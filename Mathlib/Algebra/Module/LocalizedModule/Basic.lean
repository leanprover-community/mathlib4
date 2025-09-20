/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.RingTheory.Localization.Defs

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definitions

* `LocalizedModule.r`: the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `LocalizedModule M S`: the localized module by `S`.
* `LocalizedModule.mk`: the canonical map sending `(m, s) : M × S ↦ m/s : LocalizedModule M S`
* `LocalizedModule.liftOn`: any well-defined function `f : M × S → α` respecting `r` descents to
  a function `LocalizedModule M S → α`
* `LocalizedModule.liftOn₂`: any well-defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `LocalizedModule M S → LocalizedModule M S`
* `LocalizedModule.mk_add_mk`: in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `LocalizedModule.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : Localization S` is localized ring
  by `S`.
* `LocalizedModule.isModule` : `LocalizedModule M S` is a `Localization S`-module.

## Future work

* Redefine `Localization` for monoids and rings to coincide with `LocalizedModule`.
-/


namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable (M : Type v) [AddCommMonoid M] [Module R M]
variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

/-- The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0 -/
def r (a b : M × S) : Prop :=
  ∃ u : S, u • b.2 • a.1 = u • a.2 • b.1

theorem r.isEquiv : IsEquiv _ (r S M) :=
  { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2', hu1']
    symm := fun ⟨_, _⟩ ⟨_, _⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }

instance r.setoid : Setoid (M × S) where
  r := r S M
  iseqv := ⟨(r.isEquiv S M).refl, (r.isEquiv S M).symm _ _, (r.isEquiv S M).trans _ _ _⟩

-- TODO: change `Localization` to use `r'` instead of `r` so that the two types are also defeq,
-- `Localization S = LocalizedModule S R`.
example {R} [CommSemiring R] (S : Submonoid R) : ⇑(Localization.r' S) = LocalizedModule.r S R :=
  rfl

/-- If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
def _root_.LocalizedModule : Type max u v :=
  Quotient (r.setoid S M)

section

variable {M S}

/-- The canonical map sending `(m, s) ↦ m/s` -/
def mk (m : M) (s : S) : LocalizedModule S M :=
  Quotient.mk' ⟨m, s⟩

theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ u : S, u • s' • m = u • s • m' :=
  Quotient.eq'

@[elab_as_elim, induction_eliminator, cases_eliminator]
theorem induction_on {β : LocalizedModule S M → Prop} (h : ∀ (m : M) (s : S), β (mk m s)) :
    ∀ x : LocalizedModule S M, β x := by
  rintro ⟨⟨m, s⟩⟩
  exact h m s

@[elab_as_elim]
theorem induction_on₂ {β : LocalizedModule S M → LocalizedModule S M → Prop}
    (h : ∀ (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : ∀ x y, β x y := by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'

/-- If `f : M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → α`.
-/
def liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S → α)
    (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p') : α :=
  Quotient.liftOn x f wd

theorem liftOn_mk {α : Type*} {f : M × S → α} (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p')
    (m : M) (s : S) : liftOn (mk m s) f wd = f ⟨m, s⟩ := by convert Quotient.liftOn_mk f wd ⟨m, s⟩

/-- If `f : M × S → M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → LocalizedModule M S → α`.
-/
def liftOn₂ {α : Type*} (x y : LocalizedModule S M) (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), p ≈ p' → q ≈ q' → f p q = f p' q') : α :=
  Quotient.liftOn₂ x y f wd

theorem liftOn₂_mk {α : Type*} (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), p ≈ p' → q ≈ q' → f p q = f p' q') (m m' : M)
    (s s' : S) : liftOn₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ := by
  convert Quotient.liftOn₂_mk f wd _ _

instance : Zero (LocalizedModule S M) :=
  ⟨mk 0 1⟩

/-- If `S` contains `0` then the localization at `S` is trivial. -/
theorem subsingleton (h : 0 ∈ S) : Subsingleton (LocalizedModule S M) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a,b using LocalizedModule.induction_on₂
  exact mk_eq.mpr ⟨⟨0, h⟩, by simp only [Submonoid.mk_smul, zero_smul]⟩

@[simp]
theorem zero_mk (s : S) : mk (0 : M) s = 0 :=
  mk_eq.mpr ⟨1, by rw [one_smul, smul_zero, smul_zero, one_smul]⟩

instance : Add (LocalizedModule S M) where
  add p1 p2 :=
    liftOn₂ p1 p2 (fun x y => mk (y.2 • x.1 + x.2 • y.1) (x.2 * y.2)) <|
      fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m1', s1'⟩ ⟨m2', s2'⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ =>
          mk_eq.mpr
            ⟨u1 * u2, by
              -- Put everything in the same shape, sorting the terms using `simp`
              have hu1' := congr_arg ((u2 * s2 * s2') • ·) hu1
              have hu2' := congr_arg ((u1 * s1 * s1') • ·) hu2
              simp only [smul_add, ← mul_smul, mul_comm,
                mul_left_comm] at hu1' hu2' ⊢
              rw [hu1', hu2']⟩

theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) :=
  mk_eq.mpr <| ⟨1, rfl⟩

private theorem add_assoc' (x y z : LocalizedModule S M) : x + y + z = x + (y + z) := by
  induction x with | _ mx sx
  induction y with | _ my sy
  induction z with | _ mz sz
  simp only [mk_add_mk, smul_add]
  refine mk_eq.mpr ⟨1, ?_⟩
  rw [one_smul, one_smul]
  congr 1
  · rw [mul_assoc]
  · rw [eq_comm, mul_comm, add_assoc, mul_smul, mul_smul, ← mul_smul sx sz, mul_comm, mul_smul]

private theorem add_comm' (x y : LocalizedModule S M) : x + y = y + x :=
  LocalizedModule.induction_on₂ (fun m m' s s' => by rw [mk_add_mk, mk_add_mk, add_comm, mul_comm])
    x y

private theorem zero_add' (x : LocalizedModule S M) : 0 + x = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, zero_add, mk_eq]
      exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩)
    x

private theorem add_zero' (x : LocalizedModule S M) : x + 0 = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, add_zero, mk_eq]
      exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩)
    x

instance hasNatSMul : SMul ℕ (LocalizedModule S M) where smul n := nsmulRec n

private theorem nsmul_zero' (x : LocalizedModule S M) : (0 : ℕ) • x = 0 :=
  LocalizedModule.induction_on (fun _ _ => rfl) x

private theorem nsmul_succ' (n : ℕ) (x : LocalizedModule S M) : n.succ • x = n • x + x :=
  LocalizedModule.induction_on (fun _ _ => rfl) x

instance : AddCommMonoid (LocalizedModule S M) where
  add := (· + ·)
  add_assoc := add_assoc'
  zero := 0
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := (· • ·)
  nsmul_zero := nsmul_zero'
  nsmul_succ := nsmul_succ'
  add_comm := add_comm'

instance {M : Type*} [AddCommGroup M] [Module R M] : Neg (LocalizedModule S M) where
  neg p :=
    liftOn p (fun x => LocalizedModule.mk (-x.1) x.2) fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩ => by
      rw [mk_eq]
      exact ⟨u, by simpa⟩

instance {M : Type*} [AddCommGroup M] [Module R M] : AddCommGroup (LocalizedModule S M) :=
  { show AddCommMonoid (LocalizedModule S M) by infer_instance with
    neg_add_cancel := by
      rintro ⟨m, s⟩
      change
        (liftOn (mk m s) (fun x => mk (-x.1) x.2) fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩ => by
              rw [mk_eq]
              exact ⟨u, by simpa⟩) +
            mk m s =
          0
      rw [liftOn_mk, mk_add_mk]
      simp
    -- TODO: fix the diamond
    zsmul := zsmulRec }

theorem mk_neg {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S} : mk (-m) s = -mk m s :=
  rfl

instance {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Monoid (LocalizedModule S A) :=
  { mul := fun m₁ m₂ =>
      liftOn₂ m₁ m₂ (fun x₁ x₂ => LocalizedModule.mk (x₁.1 * x₂.1) (x₁.2 * x₂.2))
        (by
          rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
          rw [mk_eq]
          use u₁ * u₂
          dsimp only at e₁ e₂ ⊢
          rw [eq_comm]
          trans (u₁ • t₁ • a₁) • u₂ • t₂ • a₂
          on_goal 1 => rw [e₁, e₂]
          on_goal 2 => rw [eq_comm]
          all_goals
            rw [smul_smul, mul_mul_mul_comm, ← smul_eq_mul, ← smul_eq_mul (α := A),
              smul_smul_smul_comm, mul_smul, mul_smul])
    one := mk 1 (1 : S)
    one_mul := by
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [one_mul, one_smul]⟩
    mul_one := by
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [mul_one, one_smul]⟩
    mul_assoc := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      apply mk_eq.mpr _
      use 1
      simp only [one_mul, smul_smul, ← mul_assoc] }

instance {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Semiring (LocalizedModule S A) :=
  { show (AddCommMonoid (LocalizedModule S A)) by infer_instance,
    show (Monoid (LocalizedModule S A)) by infer_instance with
    left_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      apply mk_eq.mpr _
      use 1
      simp only [one_mul, smul_add, mul_add, mul_smul_comm, smul_smul, ← mul_assoc,
        mul_right_comm]
    right_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      apply mk_eq.mpr _
      use 1
      simp only [one_mul, smul_add, add_mul, smul_smul, ← mul_assoc, smul_mul_assoc,
        mul_right_comm]
    zero_mul := by
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [zero_mul, smul_zero]⟩
    mul_zero := by
      rintro ⟨a, s⟩
      exact mk_eq.mpr ⟨1, by simp only [mul_zero, smul_zero]⟩ }

instance {A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R} :
    CommSemiring (LocalizedModule S A) :=
  { show Semiring (LocalizedModule S A) by infer_instance with
    mul_comm := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩
      exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩ }

instance {A : Type*} [Ring A] [Algebra R A] {S : Submonoid R} :
    Ring (LocalizedModule S A) :=
  { inferInstanceAs (AddCommGroup (LocalizedModule S A)),
    inferInstanceAs (Semiring (LocalizedModule S A)) with }

instance {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R} :
    CommRing (LocalizedModule S A) :=
  { show (Ring (LocalizedModule S A)) by infer_instance with
    mul_comm := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩
      exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩ }

theorem mk_mul_mk {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂) :=
  rfl

noncomputable instance : SMul T (LocalizedModule S M) where
  smul x p :=
    let a := IsLocalization.sec S x
    liftOn p (fun p ↦ mk (a.1 • p.1) (a.2 * p.2))
      (by
        rintro p p' ⟨s, h⟩
        refine mk_eq.mpr ⟨s, ?_⟩
        calc
          _ = a.2 • a.1 • s • p'.2 • p.1 := by
            simp_rw [Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul]; ring_nf
          _ = a.2 • a.1 • s • p.2 • p'.1 := by rw [h]
          _ = s • (a.2 * p.2) • a.1 • p'.1 := by
            simp_rw [Submonoid.smul_def, ← mul_smul, Submonoid.coe_mul]; ring_nf )

theorem smul_def (x : T) (m : M) (s : S) :
    x • mk m s = mk ((IsLocalization.sec S x).1 • m) ((IsLocalization.sec S x).2 * s) := rfl

theorem mk'_smul_mk (r : R) (m : M) (s s' : S) :
    IsLocalization.mk' T r s • mk m s' = mk (r • m) (s * s') := by
  rw [smul_def, mk_eq]
  obtain ⟨c, hc⟩ := IsLocalization.eq.mp <| IsLocalization.mk'_sec T (IsLocalization.mk' T r s)
  use c
  simp_rw [← mul_smul, Submonoid.smul_def, Submonoid.coe_mul, ← mul_smul, ← mul_assoc,
    mul_comm _ (s' : R), mul_assoc, hc]

theorem mk_smul_mk (r : R) (m : M) (s t : S) :
    Localization.mk r s • mk m t = mk (r • m) (s * t) := by
  rw [Localization.mk_eq_mk']
  exact mk'_smul_mk ..

variable {T}

private theorem one_smul_aux (p : LocalizedModule S M) : (1 : T) • p = p := by
  induction p with | _ m s
  rw [show (1 : T) = IsLocalization.mk' T (1 : R) (1 : S) by rw [IsLocalization.mk'_one, map_one]]
  rw [mk'_smul_mk, one_smul, one_mul]

private theorem mul_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x * y) • p = x • y • p := by
  induction p with | _ m s
  rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y]
  simp_rw [← IsLocalization.mk'_mul, mk'_smul_mk, ← mul_smul, mul_assoc]

private theorem smul_add_aux (x : T) (p q : LocalizedModule S M) :
    x • (p + q) = x • p + x • q := by
  induction p with | _ m s
  induction q with | _ n t
  rw [smul_def, smul_def, mk_add_mk, mk_add_mk]
  rw [show x • _ =  IsLocalization.mk' T _ _ • _ by rw [IsLocalization.mk'_sec (M := S) T]]
  rw [← IsLocalization.mk'_cancel _ _ (IsLocalization.sec S x).2, mk'_smul_mk]
  congr 1
  · simp only [Submonoid.smul_def, smul_add, ← mul_smul, Submonoid.coe_mul]; ring_nf
  · rw [mul_mul_mul_comm] -- ring does not work here

private theorem smul_zero_aux (x : T) : x • (0 : LocalizedModule S M) = 0 := by
  conv => lhs; rw [← zero_mk 1, smul_def, smul_zero, zero_mk]

private theorem add_smul_aux (x y : T) (p : LocalizedModule S M) :
    (x + y) • p = x • p + y • p := by
  induction p with | _ m s
  rw [smul_def T x, smul_def T y, mk_add_mk, show (x + y) • _ =  IsLocalization.mk' T _ _ • _ by
    rw [← IsLocalization.mk'_sec (M := S) T x, ← IsLocalization.mk'_sec (M := S) T y,
      ← IsLocalization.mk'_add, IsLocalization.mk'_cancel _ _ s], mk'_smul_mk, ← smul_assoc,
    ← smul_assoc, ← add_smul]
  congr 1
  · simp only [Submonoid.smul_def, Submonoid.coe_mul, smul_eq_mul]; ring_nf
  · rw [mul_mul_mul_comm, mul_assoc] -- ring does not work here

private theorem zero_smul_aux (p : LocalizedModule S M) : (0 : T) • p = 0 := by
  induction p with | _ m s
  rw [show (0 : T) = IsLocalization.mk' T (0 : R) (1 : S) by rw [IsLocalization.mk'_zero],
    mk'_smul_mk, zero_smul, zero_mk]

noncomputable instance isModule : Module T (LocalizedModule S M) where
  smul := (· • ·)
  one_smul := one_smul_aux
  mul_smul := mul_smul_aux
  smul_add := smul_add_aux
  smul_zero := smul_zero_aux
  add_smul := add_smul_aux
  zero_smul := zero_smul_aux

@[simp]
theorem mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s :=
  mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      rw [smul_comm]⟩

@[simp]
theorem mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1 :=
  mk_eq.mpr ⟨1, by simp⟩

@[simp]
theorem mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s :=
  mk_eq.mpr ⟨1, by simp [mul_smul]⟩

noncomputable instance isModule' : Module R (LocalizedModule S M) :=
  { Module.compHom (LocalizedModule S M) <| algebraMap R (Localization S) with }

theorem smul'_mk (r : R) (s : S) (m : M) : r • mk m s = mk (r • m) s := by
  simpa only [one_mul] using mk_smul_mk r m 1 s

lemma smul_eq_iff_of_mem
    (r : R) (hr : r ∈ S) (x y : LocalizedModule S M) :
    r • x = y ↔ x = Localization.mk 1 ⟨r, hr⟩ • y := by
  induction x using induction_on with
  | h m s =>
    induction y using induction_on with
    | h n t =>
      rw [smul'_mk, mk_smul_mk, one_smul, mk_eq, mk_eq]
      simp only [Subtype.exists, Submonoid.mk_smul, exists_prop]
      fconstructor
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [mul_smul, ← eq1, Submonoid.mk_smul, smul_comm r t]
      · rintro ⟨a, ha, eq1⟩
        refine ⟨a, ha, ?_⟩
        rw [← eq1, mul_comm, mul_smul, Submonoid.mk_smul, Submonoid.smul_def, Submonoid.mk_smul]

lemma eq_zero_of_smul_eq_zero
    (r : R) (hr : r ∈ S) (x : LocalizedModule S M) (hx : r • x = 0) : x = 0 := by
  rw [smul_eq_iff_of_mem (hr := hr)] at hx
  rw [hx, smul_zero]

theorem smul'_mul {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A) :
    x • p₁ * p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [mk_mul_mk, smul_def, smul_def, mk_mul_mk, mul_assoc, smul_mul_assoc]

theorem mul_smul' {A : Type*} [Semiring A] [Algebra R A] (x : T) (p₁ p₂ : LocalizedModule S A) :
    p₁ * x • p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [smul_def, mk_mul_mk, mk_mul_mk, smul_def, mul_left_comm, mul_smul_comm]

variable (T)

noncomputable instance {A : Type*} [Semiring A] [Algebra R A] : Algebra T (LocalizedModule S A) :=
  Algebra.ofModule smul'_mul mul_smul'

theorem algebraMap_mk' {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (IsLocalization.mk' T a s) = mk (algebraMap R A a) s := by
  rw [Algebra.algebraMap_eq_smul_one]
  change _ • mk _ _ = _
  rw [mk'_smul_mk, Algebra.algebraMap_eq_smul_one, mul_one]

theorem algebraMap_mk {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (Localization.mk a s) = mk (algebraMap R A a) s := by
  rw [Localization.mk_eq_mk']
  exact algebraMap_mk' ..

instance : IsScalarTower R T (LocalizedModule S M) where
  smul_assoc r x p := by
    induction p with | _ m s
    rw [← IsLocalization.mk'_sec (M := S) T x, IsLocalization.smul_mk', mk'_smul_mk, mk'_smul_mk,
      smul'_mk, mul_smul]

noncomputable instance algebra' {A : Type*} [Semiring A] [Algebra R A] :
    Algebra R (LocalizedModule S A) where
  algebraMap := (algebraMap (Localization S) (LocalizedModule S A)).comp
    (algebraMap R <| Localization S)
  commutes' := by
    intro r x
    induction x using induction_on with | _ a s => _
    dsimp
    rw [← Localization.mk_one_eq_algebraMap, algebraMap_mk, mk_mul_mk, mk_mul_mk, mul_comm,
      Algebra.commutes]
  smul_def' := by
    intro r x
    induction x using induction_on with | _ a s => _
    dsimp
    rw [← Localization.mk_one_eq_algebraMap, algebraMap_mk, mk_mul_mk, smul'_mk,
      Algebra.smul_def, one_mul]

section

variable (S M)

/-- The function `m ↦ m / 1` as an `R`-linear map.
-/
@[simps]
noncomputable def mkLinearMap : M →ₗ[R] LocalizedModule S M where
  toFun m := mk m 1
  map_add' x y := by simp [mk_add_mk]
  map_smul' _ _ := (smul'_mk _ _ _).symm

end

/-- For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
@[simps]
noncomputable def divBy (s : S) : LocalizedModule S M →ₗ[R] LocalizedModule S M where
  toFun p :=
    p.liftOn (fun p => mk p.1 (p.2 * s)) fun ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩ =>
      mk_eq.mpr ⟨c, by rw [mul_smul, mul_smul, smul_comm _ s, smul_comm _ s, eq1, smul_comm _ s,
        smul_comm _ s]⟩
  map_add' x y := by
    refine x.induction_on₂ ?_ y
    intro m₁ m₂ t₁ t₂
    simp_rw [mk_add_mk, LocalizedModule.liftOn_mk, mk_add_mk, mul_smul, mul_comm _ s, mul_assoc,
      smul_comm _ s, ← smul_add, mul_left_comm s t₁ t₂, mk_cancel_common_left s]
  map_smul' r x := by
    refine x.induction_on (fun _ _ ↦ ?_)
    change liftOn (mk _ _) _ _ = r • (liftOn (mk _ _) _ _)
    simp_rw [liftOn_mk, mul_assoc, ← smul_def]
    congr!

theorem divBy_mul_by (s : S) (p : LocalizedModule S M) :
    divBy s (algebraMap R (Module.End R (LocalizedModule S M)) s p) = p :=
  p.induction_on fun m t => by
    rw [Module.algebraMap_end_apply, divBy_apply, ← algebraMap_smul (Localization S) (s : R),
      smul_def, LocalizedModule.liftOn_mk, mul_assoc, ← smul_def, algebraMap_smul, smul'_mk,
      ← Submonoid.smul_def, mk_cancel_common_right _ s]

theorem mul_by_divBy (s : S) (p : LocalizedModule S M) :
    algebraMap R (Module.End R (LocalizedModule S M)) s (divBy s p) = p :=
  p.induction_on fun m t => by
    rw [divBy_apply, Module.algebraMap_end_apply, LocalizedModule.liftOn_mk, smul'_mk,
      ← Submonoid.smul_def, mk_cancel_common_right _ s]

end

end LocalizedModule

section IsLocalizedModule

universe u v

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
variable {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]
variable [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']
variable (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

/-- The characteristic predicate for localized module.
`IsLocalizedModule S f` describes that `f : M ⟶ M'` is the localization map identifying `M'` as
`LocalizedModule S M`.
-/
@[mk_iff] class IsLocalizedModule : Prop where
  map_units : ∀ x : S, IsUnit (algebraMap R (Module.End R M') x)
  surj' : ∀ y : M', ∃ x : M × S, x.2 • y = f x.1
  exists_of_eq : ∀ {x₁ x₂}, f x₁ = f x₂ → ∃ c : S, c • x₁ = c • x₂

attribute [nolint docBlame] IsLocalizedModule.map_units IsLocalizedModule.surj'
  IsLocalizedModule.exists_of_eq

lemma IsLocalizedModule.surj [IsLocalizedModule S f] (y : M') : ∃ x : M × S, x.2 • y = f x.1 :=
  surj' y

lemma IsLocalizedModule.eq_iff_exists [IsLocalizedModule S f] {x₁ x₂} :
    f x₁ = f x₂ ↔ ∃ c : S, c • x₁ = c • x₂ :=
  Iff.intro exists_of_eq fun ⟨c, h⟩ ↦ by
    apply_fun f at h
    simp_rw [f.map_smul_of_tower, Submonoid.smul_def, ← Module.algebraMap_end_apply R R] at h
    exact ((Module.End.isUnit_iff _).mp <| map_units f c).1 h

lemma IsLocalizedModule.injective_iff_isRegular [IsLocalizedModule S f] :
    Function.Injective f ↔ ∀ c : S, IsSMulRegular M c := by
  simp_rw [IsSMulRegular, Function.Injective, eq_iff_exists S, exists_imp, forall_comm (α := S)]

instance IsLocalizedModule.of_linearEquiv (e : M' ≃ₗ[R] M'') [hf : IsLocalizedModule S f] :
    IsLocalizedModule S (e ∘ₗ f : M →ₗ[R] M'') where
  map_units s := by
    rw [show algebraMap R (Module.End R M'') s = e ∘ₗ (algebraMap R (Module.End R M') s) ∘ₗ e.symm
      by ext; simp, Module.End.isUnit_iff, LinearMap.coe_comp, LinearMap.coe_comp,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, EquivLike.comp_bijective, EquivLike.bijective_comp]
    exact (Module.End.isUnit_iff _).mp <| hf.map_units s
  surj' x := by
    obtain ⟨p, h⟩ := hf.surj' (e.symm x)
    exact ⟨p, by rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ← e.congr_arg h,
      Submonoid.smul_def, Submonoid.smul_def, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq] at h
    exact hf.exists_of_eq h

instance IsLocalizedModule.of_linearEquiv_right (e : M'' ≃ₗ[R] M) [hf : IsLocalizedModule S f] :
    IsLocalizedModule S (f ∘ₗ e : M'' →ₗ[R] M') where
  map_units s := hf.map_units s
  surj' x := by
    obtain ⟨⟨p, s⟩, h⟩ := hf.surj' x
    exact ⟨⟨e.symm p, s⟩, by simpa using h⟩
  exists_of_eq h := by
    simp_rw [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h
    obtain ⟨c, hc⟩ := hf.exists_of_eq h
    exact ⟨c, by simpa only [Submonoid.smul_def, map_smul, e.symm_apply_apply]
      using congr(e.symm $hc)⟩

variable (M) in
lemma isLocalizedModule_id (R') [CommSemiring R'] [Algebra R R'] [IsLocalization S R'] [Module R' M]
    [IsScalarTower R R' M] : IsLocalizedModule S (.id : M →ₗ[R] M) where
  map_units s := by
    rw [← (Algebra.lsmul R (A := R') R M).commutes]; exact (IsLocalization.map_units R' s).map _
  surj' m := ⟨(m, 1), one_smul _ _⟩
  exists_of_eq h := ⟨1, congr_arg _ h⟩

namespace LocalizedModule

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
noncomputable def lift' (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit (algebraMap R (Module.End R M'') x)) : LocalizedModule S M → M'' :=
  fun m =>
  m.liftOn (fun p => (h p.2).unit⁻¹.val <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    dsimp only
    simp only [Submonoid.smul_def] at eq1
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← map_smul, eq_comm,
      Module.End.algebraMap_isUnit_inv_apply_eq_iff]
    have : c • s • g m' = c • s' • g m := by
      simp only [Submonoid.smul_def, ← g.map_smul, eq1]
    have : Function.Injective (h c).unit.inv := ((Module.End.isUnit_iff _).1 (by simp)).1
    apply_fun (h c).unit.inv
    rw [Units.inv_eq_val_inv, Module.End.algebraMap_isUnit_inv_apply_eq_iff, ←
      (h c).unit⁻¹.val.map_smul]
    symm
    rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← g.map_smul, ← g.map_smul, ← g.map_smul, ←
      g.map_smul, eq1]

theorem lift'_mk (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (m : M) (s : S) :
    LocalizedModule.lift' S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl

theorem lift'_add (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (x y) :
    LocalizedModule.lift' S g h (x + y) =
      LocalizedModule.lift' S g h x + LocalizedModule.lift' S g h y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      rw [mk_add_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk]
      rw [map_add, Module.End.algebraMap_isUnit_inv_apply_eq_iff, smul_add, ← map_smul,
        ← map_smul, ← map_smul]
      congr 1 <;> symm
      · rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff]
        simp only [Submonoid.coe_mul, LinearMap.map_smul_of_tower]
        rw [mul_smul, Submonoid.smul_def]
      · dsimp
        rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, mul_comm, mul_smul, ← map_smul]
        rfl)
    x y

theorem lift'_smul (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (r : R) (m) : r • LocalizedModule.lift' S g h m = LocalizedModule.lift' S g h (r • m) :=
  m.induction_on fun a b => by
    rw [LocalizedModule.lift'_mk, LocalizedModule.smul'_mk, LocalizedModule.lift'_mk,
      ← map_smul, ← g.map_smul]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    LocalizedModule S M →ₗ[R] M'' where
  toFun := LocalizedModule.lift' S g h
  map_add' := LocalizedModule.lift'_add S g h
  map_smul' r x := by rw [LocalizedModule.lift'_smul, RingHom.id_apply]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
`lift g m s = s⁻¹ • g m`.
-/
theorem lift_mk
    (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit (algebraMap R (Module.End R M'') x)) (m : M) (s : S) :
    LocalizedModule.lift S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl

@[simp]
lemma lift_mk_one (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) (m : M) :
    (LocalizedModule.lift S g h) (LocalizedModule.mk m 1) = g m := by
  simp [lift_mk]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `lift g ∘ mkLinearMap = g`.
-/
theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S g h).comp (mkLinearMap S M) = g := by
  ext x
  simp [LocalizedModule.lift_mk]

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible and
`l` is another linear map `LocalizedModule S M ⟶ M''` such that `l ∘ mkLinearMap = g` then
`l = lift g`
-/
theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : LocalizedModule S M →ₗ[R] M'') (hl : l.comp (LocalizedModule.mkLinearMap S M) = g) :
    LocalizedModule.lift S g h = l := by
  ext x; induction x with | _ m s
  rw [LocalizedModule.lift_mk]
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← hl, LinearMap.coe_comp,
    Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← l.map_smul, LocalizedModule.smul'_mk]
  congr 1; rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩; simp only [one_smul, Submonoid.smul_def]

end LocalizedModule

instance localizedModuleIsLocalizedModule :
    IsLocalizedModule S (LocalizedModule.mkLinearMap S M) where
  map_units s :=
    ⟨⟨algebraMap R (Module.End R (LocalizedModule S M)) s, LocalizedModule.divBy s,
        DFunLike.ext _ _ <| LocalizedModule.mul_by_divBy s,
        DFunLike.ext _ _ <| LocalizedModule.divBy_mul_by s⟩,
      DFunLike.ext _ _ fun p =>
        p.induction_on <| by
          intros
          rfl⟩
  surj' p :=
    p.induction_on fun m t => by
      refine ⟨⟨m, t⟩, ?_⟩
      rw [Submonoid.smul_def, LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply,
        ← Submonoid.smul_def, LocalizedModule.mk_cancel t]
  exists_of_eq eq1 := by simpa only [eq_comm, one_smul] using LocalizedModule.mk_eq.mp eq1

lemma IsLocalizedModule.of_restrictScalars (S : Submonoid R)
    {N : Type*} [AddCommMonoid N] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (f : M →ₗ[A] N) [IsLocalizedModule S (f.restrictScalars R)] :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A S) f where
  map_units x := by
    obtain ⟨_, x, hx, rfl⟩ := x
    have := IsLocalizedModule.map_units (f.restrictScalars R) ⟨x, hx⟩
    simp only [← IsScalarTower.algebraMap_apply, Module.End.isUnit_iff] at this ⊢
    exact this
  surj' y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S (f.restrictScalars R) y
    exact ⟨⟨x, ⟨_, t, t.2, rfl⟩⟩, by simpa [Submonoid.smul_def] using e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f.restrictScalars R) e
    refine ⟨⟨_, c, c.2, rfl⟩, by simpa [Submonoid.smul_def]⟩

lemma IsLocalizedModule.of_exists_mul_mem {N : Type*} [AddCommMonoid N] [Module R N]
    (S T : Submonoid R) (h : S ≤ T) (h' : ∀ x : T, ∃ m : R, m * x ∈ S)
    (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    IsLocalizedModule T f where
  map_units x := by
    obtain ⟨m, mx⟩ := h' x
    have := IsLocalizedModule.map_units f ⟨_, mx⟩
    rw [map_mul, (Algebra.commute_algebraMap_left _ _).isUnit_mul_iff] at this
    exact this.2
  surj' y := by
    obtain ⟨⟨x, t⟩, e⟩ := IsLocalizedModule.surj S f y
    exact ⟨⟨x, ⟨t, h t.2⟩⟩, e⟩
  exists_of_eq {x₁ x₂} e := by
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := f) e
    exact ⟨⟨c, h c.2⟩, hc⟩

namespace IsLocalizedModule

variable [IsLocalizedModule S f]

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule' : LocalizedModule S M → M' := fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).unit⁻¹.val (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      dsimp
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← map_smul, ← map_smul,
        Module.End.algebraMap_isUnit_inv_apply_eq_iff', ← map_smul]
      exact (IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1.symm⟩)

@[simp]
theorem fromLocalizedModule'_mk (m : M) (s : S) :
    fromLocalizedModule' S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

theorem fromLocalizedModule'_add (x y : LocalizedModule S M) :
    fromLocalizedModule' S f (x + y) = fromLocalizedModule' S f x + fromLocalizedModule' S f y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      simp only [LocalizedModule.mk_add_mk, fromLocalizedModule'_mk]
      rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, smul_add, ← map_smul, ← map_smul,
        ← map_smul, map_add]
      congr 1
      all_goals rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff']
      · simp [mul_smul, Submonoid.smul_def]
      · rw [Submonoid.coe_mul, LinearMap.map_smul_of_tower, mul_comm, mul_smul, Submonoid.smul_def])
    x y

theorem fromLocalizedModule'_smul (r : R) (x : LocalizedModule S M) :
    r • fromLocalizedModule' S f x = fromLocalizedModule' S f (r • x) :=
  LocalizedModule.induction_on
    (by
      intro a b
      rw [fromLocalizedModule'_mk, LocalizedModule.smul'_mk, fromLocalizedModule'_mk,
        f.map_smul, map_smul])
    x

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule : LocalizedModule S M →ₗ[R] M' where
  toFun := fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]

theorem fromLocalizedModule_mk (m : M) (s : S) :
    fromLocalizedModule S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

theorem fromLocalizedModule.inj : Function.Injective <| fromLocalizedModule S f := fun x y eq1 => by
  induction x with | _ a b
  induction y with | _ a' b'
  simp only [fromLocalizedModule_mk] at eq1
  rw [Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← LinearMap.map_smul,
    Module.End.algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  rw [LocalizedModule.mk_eq, ← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def,
    Submonoid.smul_def, f.map_smul, f.map_smul, eq1]

theorem fromLocalizedModule.surj : Function.Surjective <| fromLocalizedModule S f := fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff, ← eq1,
      Submonoid.smul_def]⟩

theorem fromLocalizedModule.bij : Function.Bijective <| fromLocalizedModule S f :=
  ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'` is isomorphic to
`LocalizedModule S M` as an `R`-module.
-/
noncomputable def iso : LocalizedModule S M ≃ₗ[R] M' :=
  { fromLocalizedModule S f,
    Equiv.ofBijective (fromLocalizedModule S f) <| fromLocalizedModule.bij _ _ with }

theorem iso_apply_mk (m : M) (s : S) :
    iso S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl

@[simp]
lemma iso_mk_one (x : M) : (iso S f) (LocalizedModule.mk x 1) = f x := by
  simp [iso_apply_mk]

theorem iso_symm_apply_aux (m : M') :
    (iso S f).symm m =
      LocalizedModule.mk (IsLocalizedModule.surj S f m).choose.1
        (IsLocalizedModule.surj S f m).choose.2 := by
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  rw [LinearEquiv.apply_symm_apply]
  simp [iso, fromLocalizedModule, Module.End.algebraMap_isUnit_inv_apply_eq_iff',
    ← Submonoid.smul_def, (surj' _).choose_spec]

theorem iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) :
    (iso S f).symm m = LocalizedModule.mk a b :=
  (iso_symm_apply_aux S f m).trans <|
    LocalizedModule.mk_eq.mpr <| by
      rw [← IsLocalizedModule.eq_iff_exists S f, Submonoid.smul_def, Submonoid.smul_def, f.map_smul,
        f.map_smul, ← (surj' _).choose_spec, ← Submonoid.smul_def, ← Submonoid.smul_def, ← mul_smul,
        mul_comm, mul_smul, eq1]

theorem iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M := by
  ext m
  rw [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply, LinearEquiv.coe_coe, iso_symm_apply']
  exact one_smul _ _

@[simp]
lemma iso_symm_apply (x) : (iso S f).symm (f x) = LocalizedModule.mk x 1 :=
  DFunLike.congr_fun (iso_symm_comp S f) x

/--
If `M'` is a localized module and `g` is a linear map `M → M''` such that all scalar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) : M' →ₗ[R] M'' :=
  (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap

theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S f g h).comp f = g := by
  dsimp only [IsLocalizedModule.lift]
  rw [LinearMap.comp_assoc, iso_symm_comp, LocalizedModule.lift_comp S g h]

@[simp]
lemma lift_iso (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x))
    (x : LocalizedModule S M) :
    IsLocalizedModule.lift S f g h ((iso S f) x) = LocalizedModule.lift S g h x := by
  simp [lift]

@[simp]
lemma lift_comp_iso (h : ∀ (x : S), IsUnit ((algebraMap R (Module.End R M'')) x)) :
    IsLocalizedModule.lift S f g h ∘ₗ iso S f = LocalizedModule.lift S g h :=
  LinearMap.ext fun x ↦ lift_iso S f g h x

@[simp]
theorem lift_apply (g : M →ₗ[R] M'') (h) (x) :
    lift S f g h (f x) = g x := LinearMap.congr_fun (lift_comp S f g h) x

theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : M' →ₗ[R] M'') (hl : l.comp f = g) : lift S f g h = l := by
  dsimp only [IsLocalizedModule.lift]
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap), LinearMap.comp_assoc,
    LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
    LinearMap.comp_id]
  rw [LinearMap.comp_assoc, ← hl]
  congr 1
  ext x
  simp

/-- Universal property from localized module:
If `(M', f : M ⟶ M')` is a localized module then it satisfies the following universal property:
For every `R`-module `M''` which every `s : S`-scalar multiplication is invertible and for every
`R`-linear map `g : M ⟶ M''`, there is a unique `R`-linear map `l : M' ⟶ M''` such that
`l ∘ f = g`.
```
M -----f----> M'
|           /
|g       /
|     /   l
v   /
M''
```
-/
theorem is_universal :
    ∀ (g : M →ₗ[R] M'') (_ : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)),
      ∃! l : M' →ₗ[R] M'', l.comp f = g :=
  fun g h => ⟨lift S f g h, lift_comp S f g h, fun l hl => (lift_unique S f g h l hl).symm⟩

theorem linearMap_ext {N N'} [AddCommMonoid N] [Module R N] [AddCommMonoid N'] [Module R N']
    (f' : N →ₗ[R] N') [IsLocalizedModule S f'] ⦃g g' : M' →ₗ[R] N'⦄
    (h : g ∘ₗ f = g' ∘ₗ f) : g = g' :=
  (is_universal S f _ <| map_units f').unique h rfl

theorem ext (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    ⦃j k : M' →ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k := by
  rw [← lift_unique S f (k.comp f) map_unit j h, lift_unique]
  rfl

/-- If `(M', f)` and `(M'', g)` both satisfy universal property of localized module, then `M', M''`
are isomorphic as `R`-module
-/
noncomputable def linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M'' :=
  (iso S f).symm.trans (iso S g)

@[simp]
lemma linearEquiv_apply [IsLocalizedModule S g] (x : M) :
    (linearEquiv S f g) (f x) = g x := by
  simp [linearEquiv]

@[simp]
lemma linearEquiv_symm_apply [IsLocalizedModule S g] (x : M) :
    (linearEquiv S f g).symm (g x) = f x := by
  simp [linearEquiv]

variable {S}

include f in
theorem smul_injective (s : S) : Function.Injective fun m : M' => s • m :=
  ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective

include f in
theorem smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂ :=
  (smul_injective f s).eq_iff

include f in
lemma isRegular_of_smul_left_injective {m : M'} (inj : Function.Injective fun r : R ↦ r • m)
    (s : S) : IsRegular (s : R) :=
  (Commute.isRegular_iff (Commute.all _)).mpr fun r r' eq ↦ by
    have := congr_arg (· • m) eq
    simp_rw [mul_smul, ← Submonoid.smul_def, smul_inj f] at this
    exact inj this

/-- `mk' f m s` is the fraction `m/s` with respect to the localization map `f`. -/
noncomputable def mk' (m : M) (s : S) : M' :=
  fromLocalizedModule S f (LocalizedModule.mk m s)

theorem mk'_smul (r : R) (m : M) (s : S) : mk' f (r • m) s = r • mk' f m s := by
  delta mk'
  rw [← LocalizedModule.smul'_mk, LinearMap.map_smul]

theorem mk'_add_mk' (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ + mk' f m₂ s₂ = mk' f (s₂ • m₁ + s₁ • m₂) (s₁ * s₂) := by
  delta mk'
  rw [← map_add, LocalizedModule.mk_add_mk]

@[simp]
theorem mk'_zero (s : S) : mk' f 0 s = 0 := by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]

variable (S) in
@[simp]
theorem mk'_one (m : M) : mk' f m (1 : S) = f m := by
  delta mk'
  rw [fromLocalizedModule_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff, Submonoid.coe_one,
    one_smul]

@[simp]
theorem mk'_cancel (m : M) (s : S) : mk' f (s • m) s = f m := by
  delta mk'
  rw [LocalizedModule.mk_cancel, ← mk'_one S f, fromLocalizedModule_mk,
    Module.End.algebraMap_isUnit_inv_apply_eq_iff, OneMemClass.coe_one, mk'_one, one_smul]

@[simp]
theorem mk'_cancel' (m : M) (s : S) : s • mk' f m s = f m := by
  rw [Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]

@[simp]
theorem mk'_cancel_left (m : M) (s₁ s₂ : S) : mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_left]

@[simp]
theorem mk'_cancel_right (m : M) (s₁ s₂ : S) : mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁ := by
  delta mk'
  rw [LocalizedModule.mk_cancel_common_right]

theorem mk'_add (m₁ m₂ : M) (s : S) : mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s := by
  rw [mk'_add_mk', ← smul_add, mk'_cancel_left]

theorem mk'_eq_mk'_iff (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ = mk' f m₂ s₂ ↔ ∃ s : S, s • s₁ • m₂ = s • s₂ • m₁ := by
  delta mk'
  rw [(fromLocalizedModule.inj S f).eq_iff, LocalizedModule.mk_eq]
  simp_rw [eq_comm]

theorem mk'_neg {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] (m : M) (s : S) :
    mk' f (-m) s = -mk' f m s := by
  delta mk'
  rw [LocalizedModule.mk_neg, map_neg]

theorem mk'_sub {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s : S) :
    mk' f (m₁ - m₂) s = mk' f m₁ s - mk' f m₂ s := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mk'_add, mk'_neg]

theorem mk'_sub_mk' {M M' : Type*} [AddCommGroup M] [SubtractionCommMonoid M'] [Module R M]
    [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ - mk' f m₂ s₂ = mk' f (s₂ • m₁ - s₁ • m₂) (s₁ * s₂) := by
  rw [sub_eq_add_neg, ← mk'_neg, mk'_add_mk', smul_neg, ← sub_eq_add_neg]

theorem mk'_mul_mk'_of_map_mul {M M' : Type*} [NonUnitalNonAssocSemiring M] [Semiring M']
    [Module R M] [Algebra R M'] (f : M →ₗ[R] M') (hf : ∀ m₁ m₂, f (m₁ * m₂) = f m₁ * f m₂)
    [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ * mk' f m₂ s₂ = mk' f (m₁ * m₂) (s₁ * s₂) := by
  symm
  apply (Module.End.algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  rw [smul_smul_smul_comm, ← mk'_smul, ← mk'_smul]
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]

theorem mk'_mul_mk' {M M' : Type*} [Semiring M] [Semiring M'] [Algebra R M] [Algebra R M']
    (f : M →ₐ[R] M') [IsLocalizedModule S f.toLinearMap] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f.toLinearMap m₁ s₁ * mk' f.toLinearMap m₂ s₂ = mk' f.toLinearMap (m₁ * m₂) (s₁ * s₂) :=
  mk'_mul_mk'_of_map_mul f.toLinearMap (map_mul f) m₁ m₂ s₁ s₂

variable {f}

theorem mk'_eq_iff {m : M} {s : S} {m' : M'} : mk' f m s = m' ↔ f m = s • m' := by
  rw [← smul_inj f s, Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]

@[simp]
theorem mk'_eq_zero {m : M} (s : S) : mk' f m s = 0 ↔ f m = 0 := by rw [mk'_eq_iff, smul_zero]

variable (f)

theorem mk'_eq_zero' {m : M} (s : S) : mk' f m s = 0 ↔ ∃ s' : S, s' • m = 0 := by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]

theorem mk_eq_mk' (s : S) (m : M) :
    LocalizedModule.mk m s = mk' (LocalizedModule.mkLinearMap S M) m s := by
  rw [eq_comm, mk'_eq_iff, Submonoid.smul_def, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
    LocalizedModule.mk_cancel, LocalizedModule.mkLinearMap_apply]

variable (A) in
lemma mk'_smul_mk' (x : R) (m : M) (s t : S) :
    IsLocalization.mk' A x s • mk' f m t = mk' f (x • m) (s * t) := by
  apply smul_injective f (s * t)
  conv_lhs => simp only [smul_assoc, mul_smul, smul_comm t]
  simp only [mk'_cancel', map_smul, Submonoid.smul_def s]
  rw [← smul_assoc, IsLocalization.smul_mk'_self, algebraMap_smul]

variable (S)

theorem eq_zero_iff {m : M} : f m = 0 ↔ ∃ s' : S, s' • m = 0 :=
  (mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)

theorem mk'_surjective : Function.Surjective (Function.uncurry <| mk' f : M × S → M') := by
  intro x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩

section liftOfLE

variable {M₁ M₂} [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R M₁] [Module R M₂]
variable (S₁ S₂ : Submonoid R) (h : S₁ ≤ S₂) (f₁ : M →ₗ[R] M₁) (f₂ : M →ₗ[R] M₂)
variable [IsLocalizedModule S₁ f₁] [IsLocalizedModule S₂ f₂]

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
def liftOfLE : M₁ →ₗ[R] M₂ :=
  lift S₁ f₁ f₂ fun x ↦ map_units f₂ ⟨x.1, h x.2⟩

/-- The natural map `Mₛ →ₗ[R] Mₜ` if `s ≤ t` (in `Submonoid R`). -/
noncomputable
abbrev _root_.LocalizedModule.liftOfLE : LocalizedModule S₁ M →ₗ[R] LocalizedModule S₂ M :=
  IsLocalizedModule.liftOfLE S₁ S₂ h
    (LocalizedModule.mkLinearMap S₁ M) (LocalizedModule.mkLinearMap S₂ M)

lemma liftOfLE_comp : (liftOfLE S₁ S₂ h f₁ f₂).comp f₁ = f₂ := lift_comp ..

@[simp] lemma liftOfLE_apply (x) : liftOfLE S₁ S₂ h f₁ f₂ (f₁ x) = f₂ x := lift_apply ..

/-- The image of `m/s` under `liftOfLE` is `m/s`. -/
@[simp]
lemma liftOfLE_mk' (m : M) (s : S₁) :
    liftOfLE S₁ S₂ h f₁ f₂ (mk' f₁ m s) = mk' f₂ m ⟨s.1, h s.2⟩ := by
  apply ((Module.End.isUnit_iff _).mp (map_units f₂ ⟨s, h s.2⟩)).1
  simp only [Module.algebraMap_end_apply, ← map_smul, ← Submonoid.smul_def, mk'_cancel']
  rw [liftOfLE, lift_apply]
  exact (mk'_cancel' (S := S₂) f₂ m ⟨s.1, h s.2⟩).symm

instance : IsLocalizedModule S₂ (liftOfLE S₁ S₂ h f₁ f₂) where
  map_units := map_units f₂
  surj' y := by
    obtain ⟨⟨y', s⟩, e⟩ := IsLocalizedModule.surj S₂ f₂ y
    exact ⟨⟨f₁ y', s⟩, by simpa⟩
  exists_of_eq := by
    intro x₁ x₂ e
    obtain ⟨x₁, s₁, rfl⟩ := mk'_surjective S₁ f₁ x₁
    obtain ⟨x₂, s₂, rfl⟩ := mk'_surjective S₁ f₁ x₂
    simp only [Function.uncurry, liftOfLE_mk', mk'_eq_mk'_iff,
      Submonoid.smul_def, ← mk'_smul] at e ⊢
    obtain ⟨c, e⟩ := e
    exact ⟨c, 1, by simpa [← smul_comm c.1]⟩

end liftOfLE

include S in
lemma injective_of_map_eq {N : Type*} [AddCommMonoid N] [Module R N]
    {g : M' →ₗ[R] N} (H : ∀ {x y}, g (f x) = g (f y) → f x = f y) :
    Function.Injective g := by
  intro a b hab
  obtain ⟨⟨x, m⟩, (hxm : m • a = f x)⟩ := IsLocalizedModule.surj S f a
  obtain ⟨⟨y, n⟩, (hym : n • b = f y)⟩ := IsLocalizedModule.surj S f b
  suffices h : g (f (n.val • x)) = g (f (m.val • y)) by
    apply H at h
    rw [map_smul, map_smul] at h
    rwa [← IsLocalizedModule.smul_inj f (n * m), mul_smul, mul_comm, mul_smul, hxm, hym]
  simp [← hxm, ← hym, hab, ← S.smul_def, ← mul_smul, mul_comm, ← mul_smul]

lemma injective_of_map_zero {M M' N : Type*} [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] (f : M →ₗ[R] M') [IsLocalizedModule S f]
    [AddCommGroup N] [Module R N] {g : M' →ₗ[R] N} (H : ∀ m, g (f m) = 0 → f m = 0) :
    Function.Injective g := by
  refine IsLocalizedModule.injective_of_map_eq S f (fun hxy ↦ ?_)
  rw [← sub_eq_zero, ← map_sub]
  apply H
  simpa [sub_eq_zero]

variable {N N'} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
variable (g : N →ₗ[R] N') [IsLocalizedModule S g]

/-- A linear map `M →ₗ[R] N` gives a map between localized modules `Mₛ →ₗ[R] Nₛ`. -/
noncomputable
def map : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[R] N') where
  toFun h := lift S f (g ∘ₗ h) (IsLocalizedModule.map_units g)
  map_add' h₁ h₂ := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' r h := by
    apply IsLocalizedModule.ext S f (IsLocalizedModule.map_units g)
    simp only [lift_comp, LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

lemma map_comp (h : M →ₗ[R] N) : (map S f g h) ∘ₗ f = g ∘ₗ h :=
  lift_comp S f (g ∘ₗ h) (IsLocalizedModule.map_units g)

@[simp]
lemma map_apply (h : M →ₗ[R] N) (x) : map S f g h (f x) = g (h x) :=
  lift_apply S f (g ∘ₗ h) (IsLocalizedModule.map_units g) x

@[simp]
lemma map_mk' (h : M →ₗ[R] N) (x) (s : S) :
    map S f g h (IsLocalizedModule.mk' f x s) = (IsLocalizedModule.mk' g (h x) s) := by
  simp only [map, lift, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [iso_symm_apply' S f (mk' f x s) x s (mk'_cancel' f x s), LocalizedModule.lift_mk]
  rfl

@[simp]
lemma map_id : map S f f (.id ) = .id := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  simp

@[simp]
theorem map_injective (h : M →ₗ[R] N) (h_inj : Function.Injective h) :
    Function.Injective (map S f g h) := by
  intro x y
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f x
  obtain ⟨⟨y, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f y
  simp only [Function.uncurry_apply_pair, map_mk', mk'_eq_mk'_iff, Subtype.exists,
    Submonoid.mk_smul, exists_prop, forall_exists_index, and_imp]
  intro c hc e
  exact ⟨c, hc, h_inj (by simpa)⟩

@[simp]
theorem map_surjective (h : M →ₗ[R] N) (h_surj : Function.Surjective h) :
    Function.Surjective (map S f g h) := by
  intro x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  obtain ⟨x, rfl⟩ := h_surj x
  exact ⟨mk' f x s, by simp⟩

open LocalizedModule LinearEquiv LinearMap Submonoid

variable (M)

/-- The linear map `(LocalizedModule S M) → (LocalizedModule S M)` from `iso` is the identity. -/
lemma iso_localizedModule_eq_refl : iso S (mkLinearMap S M) = refl R (LocalizedModule S M) := by
  let f := mkLinearMap S M
  obtain ⟨e, _, univ⟩ := is_universal S f f (map_units f)
  rw [← toLinearMap_inj, univ (iso S f) ((eq_toLinearMap_symm_comp f f).1 (iso_symm_comp S f).symm)]
  exact Eq.symm <| univ (refl R (LocalizedModule S M)) (by simp)

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]

/-- Formula for `IsLocalizedModule.map` when each localized module is a `LocalizedModule`. -/
lemma map_LocalizedModules (g : M₀ →ₗ[R] M₁) (m : M₀) (s : S) :
    ((map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g)
    (LocalizedModule.mk m s) = LocalizedModule.mk (g m) s := by
  have := (iso_apply_mk S (mkLinearMap S M₁) (g m) s).symm
  rw [iso_localizedModule_eq_refl, refl_apply] at this
  simpa [map, lift, iso_localizedModule_eq_refl S M₀]

lemma map_iso_commute (g : M₀ →ₗ[R] M₁) : (map S f₀ f₁) g ∘ₗ (iso S f₀) =
    (iso S f₁) ∘ₗ (map S (mkLinearMap S M₀) (mkLinearMap S M₁)) g := by
  ext x
  induction x using induction_on with | _ m s
  refine ((Module.End.isUnit_iff _).1 (map_units f₁ s)).1 ?_
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
    ← CompatibleSMul.map_smul, ← CompatibleSMul.map_smul, smul'_mk, ← mk_smul _ s.2, mk_cancel]
  simp [map, lift, iso_localizedModule_eq_refl, lift_mk]

end IsLocalizedModule

namespace IsLocalizedModule

variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]
variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']
variable (f₂ : M₂ →ₗ[R] M₂') [IsLocalizedModule S f₂]

/-- Localization of composition is the composition of localization -/
theorem map_comp' (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) :
    map S f₀ f₂ (h ∘ₗ g) = map S f₁ f₂ h ∘ₗ map S f₀ f₁ g := by
  ext x
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f₀ x
  simp

section Algebra

theorem mkOfAlgebra {R S S' : Type*} [CommSemiring R] [Ring S] [Ring S'] [Algebra R S]
    [Algebra R S'] (M : Submonoid R) (f : S →ₐ[R] S') (h₁ : ∀ x ∈ M, IsUnit (algebraMap R S' x))
    (h₂ : ∀ y, ∃ x : S × M, x.2 • y = f x.1) (h₃ : ∀ x, f x = 0 → ∃ m : M, m • x = 0) :
    IsLocalizedModule M f.toLinearMap := by
  replace h₃ := fun x =>
    Iff.intro (h₃ x) fun ⟨⟨m, hm⟩, e⟩ =>
      (h₁ m hm).mul_left_cancel <| by
        rw [← Algebra.smul_def]
        simpa [Submonoid.smul_def] using f.congr_arg e
  constructor
  · intro x
    rw [Module.End.isUnit_iff]
    constructor
    · rintro a b (e : x • a = x • b)
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      exact (h₁ x x.2).mul_left_cancel e
    · intro a
      refine ⟨((h₁ x x.2).unit⁻¹ :) * a, ?_⟩
      rw [Module.algebraMap_end_apply, Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  · exact h₂
  · intro x y
    dsimp only [AlgHom.toLinearMap_apply]
    rw [← sub_eq_zero, ← map_sub, h₃]
    simp_rw [smul_sub, sub_eq_zero]
    exact id

end Algebra

variable {R A M M' : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] (S : Submonoid R)
  [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']
  [IsLocalization S A]

/-- If `M'` is the localization of `M` at `S` and `A = S⁻¹R`, then
`M' is an `A`-module. -/
@[reducible] noncomputable def module (f : M →ₗ[R] M') [IsLocalizedModule S f] : Module A M' :=
  (IsLocalizedModule.iso S f).symm.toAddEquiv.module A

lemma isScalarTower_module (f : M →ₗ[R] M') [IsLocalizedModule S f] :
    letI : Module A M' := IsLocalizedModule.module S f
    IsScalarTower R A M' :=
  (IsLocalizedModule.iso S f).symm.isScalarTower A

section Subsingleton

lemma mem_ker_iff (S : Submonoid R) {g : M →ₗ[R] M'}
    [IsLocalizedModule S g] {m : M} :
    m ∈ LinearMap.ker g ↔ ∃ r ∈ S, r • m = 0 := by
  simpa using IsLocalizedModule.eq_zero_iff S g

lemma subsingleton_iff_ker_eq_top (S : Submonoid R) (g : M →ₗ[R] M')
    [IsLocalizedModule S g] :
    Subsingleton M' ↔ LinearMap.ker g = ⊤ := by
  rw [← top_le_iff]
  refine ⟨fun H m _ ↦ Subsingleton.elim _ _, fun H ↦ (subsingleton_iff_forall_eq 0).mpr fun x ↦ ?_⟩
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S g x
  simpa using @H x Submodule.mem_top

lemma subsingleton_iff (S : Submonoid R) (g : M →ₗ[R] M')
    [IsLocalizedModule S g] :
    Subsingleton M' ↔ ∀ m : M, ∃ r ∈ S, r • m = 0 := by
  simp_rw [subsingleton_iff_ker_eq_top S g, ← top_le_iff, SetLike.le_def,
    mem_ker_iff S, Submodule.mem_top, true_implies]

end Subsingleton

end IsLocalizedModule

end IsLocalizedModule

namespace LocalizedModule

variable {R M : Type*} [CommRing R] [AddCommMonoid M] [Module R M]

lemma mem_ker_mkLinearMap_iff {S : Submonoid R} {m : M} :
    m ∈ LinearMap.ker (mkLinearMap S M) ↔ ∃ r ∈ S, r • m = 0 :=
  IsLocalizedModule.mem_ker_iff S

lemma subsingleton_iff_ker_eq_top {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔
      LinearMap.ker (LocalizedModule.mkLinearMap S M) = ⊤ :=
  IsLocalizedModule.subsingleton_iff_ker_eq_top S _

lemma subsingleton_iff {S : Submonoid R} :
    Subsingleton (LocalizedModule S M) ↔ ∀ m : M, ∃ r ∈ S, r • m = 0 :=
  IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)

instance [Subsingleton M] (S : Submonoid R) : Subsingleton (LocalizedModule S M) := by
  rw [IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)]
  intro
  use 1, S.one_mem, Subsingleton.elim _ _

end LocalizedModule
