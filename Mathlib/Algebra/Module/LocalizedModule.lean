/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.GroupTheory.MonoidLocalization
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.RingTheory.IsTensorProduct

#align_import algebra.module.localized_module from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Localized Module

Given a commutative ring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
localize `M` by `S`. This gives us a `Localization S`-module.

## Main definitions

* `LocalizedModule.r` : the equivalence relation defining this localization, namely
  `(m, s) ≈ (m', s')` if and only if there is some `u : S` such that `u • s' • m = u • s • m'`.
* `LocalizedModule M S` : the localized module by `S`.
* `LocalizedModule.mk`  : the canonical map sending `(m, s) : M × S ↦ m/s : LocalizedModule M S`
* `LocalizedModule.liftOn` : any well defined function `f : M × S → α` respecting `r` descents to
  a function `LocalizedModule M S → α`
* `LocalizedModule.liftOn₂` : any well defined function `f : M × S → M × S → α` respecting `r`
  descents to a function `LocalizedModule M S → LocalizedModule M S`
* `LocalizedModule.mk_add_mk` : in the localized module
  `mk m s + mk m' s' = mk (s' • m + s • m') (s * s')`
* `LocalizedModule.mk_smul_mk` : in the localized module, for any `r : R`, `s t : S`, `m : M`,
  we have `mk r s • mk m t = mk (r • m) (s * t)` where `mk r s : Localization S` is localized ring
  by `S`.
* `LocalizedModule.isModule` : `LocalizedModule M S` is a `Localization S`-module.
* `IsLocalizedModule.IsBaseChange` : A localization of modules is a base change.

## Future work

 * Redefine `Localization` for monoids and rings to coincide with `LocalizedModule`.
-/


namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)

variable (M : Type v) [AddCommMonoid M] [Module R M]

/-- The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0-/
/- Porting note: We use small letter `r` since `R` is used for a ring. -/
def r (a b : M × S) : Prop :=
  ∃ u : S, u • b.2 • a.1 = u • a.2 • b.1
#align localized_module.r LocalizedModule.r

theorem r.isEquiv : IsEquiv _ (r S M) :=
  { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
                                 -- 🎉 no goals
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- ⊢ (u1 * u2 * s2) • (m3, s3).snd • (m1, s1).fst = (u1 * u2 * s2) • (m1, s1).snd …
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((· • ·) (u2 * s3)) hu1.symm
      -- ⊢ (u1 * u2 * s2) • (m3, s3).snd • (m1, s1).fst = (u1 * u2 * s2) • (m1, s1).snd …
      have hu2' := congr_arg ((· • ·) (u1 * s1)) hu2.symm
      -- ⊢ (u1 * u2 * s2) • (m3, s3).snd • (m1, s1).fst = (u1 * u2 * s2) • (m1, s1).snd …
      simp only [← mul_smul, smul_assoc, mul_assoc, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      -- ⊢ (s2 * (s3 * (u1 * u2))) • m1 = (s1 * (s2 * (u1 * u2))) • m3
      rw [hu2', hu1']
      -- 🎉 no goals
    symm := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩ => ⟨u, hu.symm⟩ }
#align localized_module.r.is_equiv LocalizedModule.r.isEquiv

instance r.setoid : Setoid (M × S) where
  r := r S M
  iseqv := ⟨(r.isEquiv S M).refl, (r.isEquiv S M).symm _ _, (r.isEquiv S M).trans _ _ _⟩
#align localized_module.r.setoid LocalizedModule.r.setoid

-- TODO: change `Localization` to use `r'` instead of `r` so that the two types are also defeq,
-- `Localization S = LocalizedModule S R`.
example {R} [CommSemiring R] (S : Submonoid R) : ⇑(Localization.r' S) = LocalizedModule.r S R :=
  rfl

/-- If `S` is a multiplicative subset of a ring `R` and `M` an `R`-module, then
we can localize `M` by `S`.
-/
-- Porting note: @[nolint has_nonempty_instance]
def _root_.LocalizedModule : Type max u v :=
  Quotient (r.setoid S M)
#align localized_module LocalizedModule

section

variable {M S}

/-- The canonical map sending `(m, s) ↦ m/s`-/
def mk (m : M) (s : S) : LocalizedModule S M :=
  Quotient.mk' ⟨m, s⟩
#align localized_module.mk LocalizedModule.mk

theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ u : S, u • s' • m = u • s • m' :=
  Quotient.eq'
#align localized_module.mk_eq LocalizedModule.mk_eq

@[elab_as_elim]
theorem induction_on {β : LocalizedModule S M → Prop} (h : ∀ (m : M) (s : S), β (mk m s)) :
    ∀ x : LocalizedModule S M, β x := by
  rintro ⟨⟨m, s⟩⟩
  -- ⊢ β (Quot.mk Setoid.r (m, s))
  exact h m s
  -- 🎉 no goals
#align localized_module.induction_on LocalizedModule.induction_on

@[elab_as_elim]
theorem induction_on₂ {β : LocalizedModule S M → LocalizedModule S M → Prop}
    (h : ∀ (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : ∀ x y, β x y := by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  -- ⊢ β (Quot.mk Setoid.r (m, s)) (Quot.mk Setoid.r (m', s'))
  exact h m m' s s'
  -- 🎉 no goals
#align localized_module.induction_on₂ LocalizedModule.induction_on₂

/-- If `f : M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → α`.
-/
def liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S → α)
    (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p') : α :=
  Quotient.liftOn x f wd
#align localized_module.lift_on LocalizedModule.liftOn

theorem liftOn_mk {α : Type*} {f : M × S → α} (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p')
    (m : M) (s : S) : liftOn (mk m s) f wd = f ⟨m, s⟩ := by convert Quotient.liftOn_mk f wd ⟨m, s⟩
                                                            -- 🎉 no goals
#align localized_module.lift_on_mk LocalizedModule.liftOn_mk

/-- If `f : M × S → M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → LocalizedModule M S → α`.
-/
def liftOn₂ {α : Type*} (x y : LocalizedModule S M) (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), p ≈ p' → q ≈ q' → f p q = f p' q') : α :=
  Quotient.liftOn₂ x y f wd
#align localized_module.lift_on₂ LocalizedModule.liftOn₂

theorem liftOn₂_mk {α : Type*} (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), p ≈ p' → q ≈ q' → f p q = f p' q') (m m' : M)
    (s s' : S) : liftOn₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ := by
  convert Quotient.liftOn₂_mk f wd _ _
  -- 🎉 no goals
#align localized_module.lift_on₂_mk LocalizedModule.liftOn₂_mk

instance : Zero (LocalizedModule S M) :=
  ⟨mk 0 1⟩

@[simp]
theorem zero_mk (s : S) : mk (0 : M) s = 0 :=
  mk_eq.mpr ⟨1, by rw [one_smul, smul_zero, smul_zero, one_smul]⟩
                   -- 🎉 no goals
#align localized_module.zero_mk LocalizedModule.zero_mk

instance : Add (LocalizedModule S M)
    where add p1 p2 :=
    liftOn₂ p1 p2 (fun x y => mk (y.2 • x.1 + x.2 • y.1) (x.2 * y.2)) <|
      fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m1', s1'⟩ ⟨m2', s2'⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ =>
          mk_eq.mpr
            ⟨u1 * u2, by
              -- Put everything in the same shape, sorting the terms using `simp`
              have hu1' := congr_arg ((· • ·) (u2 * s2 * s2')) hu1
              -- ⊢ (u1 * u2) • ((m1', s1').snd * (m2', s2').snd) • ((m2, s2).snd • (m1, s1).fst …
              have hu2' := congr_arg ((· • ·) (u1 * s1 * s1')) hu2
              -- ⊢ (u1 * u2) • ((m1', s1').snd * (m2', s2').snd) • ((m2, s2).snd • (m1, s1).fst …
              simp only [smul_add, ← mul_smul, smul_assoc, mul_assoc, mul_comm,
                mul_left_comm] at hu1' hu2' ⊢
              rw [hu1', hu2']⟩
              -- 🎉 no goals

theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) :=
  mk_eq.mpr <| ⟨1, rfl⟩
#align localized_module.mk_add_mk LocalizedModule.mk_add_mk

/-- Porting note: Some auxiliary lemmas are declared with `private` in the original mathlib3 file.
We take that policy here as well, and remove the `#align` lines accordingly. -/
private theorem add_assoc' (x y z : LocalizedModule S M) : x + y + z = x + (y + z) := by
  induction' x using LocalizedModule.induction_on with mx sx
  -- ⊢ mk mx sx + y + z = mk mx sx + (y + z)
  induction' y using LocalizedModule.induction_on with my sy
  -- ⊢ mk mx sx + mk my sy + z = mk mx sx + (mk my sy + z)
  induction' z using LocalizedModule.induction_on with mz sz
  -- ⊢ mk mx sx + mk my sy + mk mz sz = mk mx sx + (mk my sy + mk mz sz)
  simp only [mk_add_mk, smul_add]
  -- ⊢ mk (sz • sy • mx + sz • sx • my + (sx * sy) • mz) (sx * sy * sz) = mk ((sy * …
  refine' mk_eq.mpr ⟨1, _⟩
  -- ⊢ 1 • (sx * (sy * sz)) • (sz • sy • mx + sz • sx • my + (sx * sy) • mz) = 1 •  …
  rw [one_smul, one_smul]
  -- ⊢ (sx * (sy * sz)) • (sz • sy • mx + sz • sx • my + (sx * sy) • mz) = (sx * sy …
  congr 1
  -- ⊢ sx * (sy * sz) = sx * sy * sz
  · rw [mul_assoc]
    -- 🎉 no goals
  · rw [eq_comm, mul_comm, add_assoc, mul_smul, mul_smul, ← mul_smul sx sz, mul_comm, mul_smul]
    -- 🎉 no goals

private theorem add_comm' (x y : LocalizedModule S M) : x + y = y + x :=
  LocalizedModule.induction_on₂ (fun m m' s s' => by rw [mk_add_mk, mk_add_mk, add_comm, mul_comm])
                                                     -- 🎉 no goals
    x y

private theorem zero_add' (x : LocalizedModule S M) : 0 + x = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, zero_add, mk_eq];
      -- ⊢ ∃ u, u • s • s • m = u • (s * s) • m
        exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩)
        -- 🎉 no goals
    x

private theorem add_zero' (x : LocalizedModule S M) : x + 0 = x :=
  induction_on
    (fun m s => by
      rw [← zero_mk s, mk_add_mk, smul_zero, add_zero, mk_eq];
      -- ⊢ ∃ u, u • s • s • m = u • (s * s) • m
        exact ⟨1, by rw [one_smul, mul_smul, one_smul]⟩)
        -- 🎉 no goals
    x

instance hasNatSmul : SMul ℕ (LocalizedModule S M) where smul n := nsmulRec n
#align localized_module.has_nat_smul LocalizedModule.hasNatSmul

private theorem nsmul_zero' (x : LocalizedModule S M) : (0 : ℕ) • x = 0 :=
  LocalizedModule.induction_on (fun _ _ => rfl) x

private theorem nsmul_succ' (n : ℕ) (x : LocalizedModule S M) : n.succ • x = x + n • x :=
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

instance {M : Type*} [AddCommGroup M] [Module R M] : AddCommGroup (LocalizedModule S M) :=
  { show AddCommMonoid (LocalizedModule S M) by infer_instance with
                                                -- 🎉 no goals
    neg := fun p =>
      liftOn p (fun x => LocalizedModule.mk (-x.1) x.2) fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩ => by
        rw [mk_eq]
        -- ⊢ ∃ u, u • (m2, s2).snd • -(m1, s1).fst = u • (m1, s1).snd • -(m2, s2).fst
        exact ⟨u, by simpa⟩
        -- 🎉 no goals
    add_left_neg := by
      rintro ⟨m, s⟩
      -- ⊢ -Quot.mk Setoid.r (m, s) + Quot.mk Setoid.r (m, s) = 0
      change
        (liftOn (mk m s) (fun x => mk (-x.1) x.2) fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨u, hu⟩ => by
              rw [mk_eq]
              exact ⟨u, by simpa⟩) +
            mk m s =
          0
      rw [liftOn_mk, mk_add_mk]
      -- ⊢ mk (s • -(m, s).fst + (m, s).snd • m) ((m, s).snd * s) = 0
      simp }
      -- 🎉 no goals

theorem mk_neg {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S} : mk (-m) s = -mk m s :=
  rfl
#align localized_module.mk_neg LocalizedModule.mk_neg

set_option maxHeartbeats 400000 in
instance {A : Type _} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Semiring (LocalizedModule S A) :=
  { show (AddCommMonoid (LocalizedModule S A)) by infer_instance with
                                                  -- 🎉 no goals
    mul := fun m₁ m₂ =>
      liftOn₂ m₁ m₂ (fun x₁ x₂ => LocalizedModule.mk (x₁.1 * x₂.1) (x₁.2 * x₂.2))
        (by
          rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
          -- ⊢ (fun x₁ x₂ => mk (x₁.fst * x₂.fst) (x₁.snd * x₂.snd)) (a₁, s₁) (a₂, s₂) = (f …
          rw [mk_eq]
          -- ⊢ ∃ u, u • ((b₁, t₁).snd * (b₂, t₂).snd) • ((a₁, s₁).fst * (a₂, s₂).fst) = u • …
          use u₁ * u₂
          -- ⊢ (u₁ * u₂) • ((b₁, t₁).snd * (b₂, t₂).snd) • ((a₁, s₁).fst * (a₂, s₂).fst) =  …
          dsimp only at e₁ e₂ ⊢
          -- ⊢ (u₁ * u₂) • (t₁ * t₂) • (a₁ * a₂) = (u₁ * u₂) • (s₁ * s₂) • (b₁ * b₂)
          rw [eq_comm]
          -- ⊢ (u₁ * u₂) • (s₁ * s₂) • (b₁ * b₂) = (u₁ * u₂) • (t₁ * t₂) • (a₁ * a₂)
          trans (u₁ • t₁ • a₁) • u₂ • t₂ • a₂
          rw [e₁, e₂]; swap; rw [eq_comm]
          all_goals
            rw [smul_smul, mul_mul_mul_comm, ← smul_eq_mul, ← smul_eq_mul A, smul_smul_smul_comm,
              mul_smul, mul_smul])
    left_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      -- ⊢ Quot.mk Setoid.r (a₁, s₁) * (Quot.mk Setoid.r (a₂, s₂) + Quot.mk Setoid.r (a …
      apply mk_eq.mpr _
      -- ⊢ ∃ u, u • (((a₁, s₁).fst * (a₂, s₂).fst, (a₁, s₁).snd * (a₂, s₂).snd).snd * ( …
      use 1
      -- ⊢ 1 • (((a₁, s₁).fst * (a₂, s₂).fst, (a₁, s₁).snd * (a₂, s₂).snd).snd * ((a₁,  …
      simp only [one_mul, smul_add, mul_add, mul_smul_comm, smul_smul, ← mul_assoc,
        mul_right_comm]
    right_distrib := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      -- ⊢ (Quot.mk Setoid.r (a₁, s₁) + Quot.mk Setoid.r (a₂, s₂)) * Quot.mk Setoid.r ( …
      apply mk_eq.mpr _
      -- ⊢ ∃ u, u • (((a₁, s₁).fst * (a₃, s₃).fst, (a₁, s₁).snd * (a₃, s₃).snd).snd * ( …
      use 1
      -- ⊢ 1 • (((a₁, s₁).fst * (a₃, s₃).fst, (a₁, s₁).snd * (a₃, s₃).snd).snd * ((a₂,  …
      simp only [one_mul, smul_add, add_mul, smul_smul, ← mul_assoc, smul_mul_assoc,
        mul_right_comm]
    zero_mul := by
      rintro ⟨a, s⟩
      -- ⊢ 0 * Quot.mk Setoid.r (a, s) = 0
      exact mk_eq.mpr ⟨1, by simp only [zero_mul, smul_zero]⟩
      -- 🎉 no goals
    mul_zero := by
      rintro ⟨a, s⟩
      -- ⊢ Quot.mk Setoid.r (a, s) * 0 = 0
      exact mk_eq.mpr ⟨1, by simp only [mul_zero, smul_zero]⟩
      -- 🎉 no goals
    mul_assoc := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
      -- ⊢ Quot.mk Setoid.r (a₁, s₁) * Quot.mk Setoid.r (a₂, s₂) * Quot.mk Setoid.r (a₃ …
      apply mk_eq.mpr _
      -- ⊢ ∃ u, u • ((a₁, s₁).snd * ((a₂, s₂).fst * (a₃, s₃).fst, (a₂, s₂).snd * (a₃, s …
      use 1
      -- ⊢ 1 • ((a₁, s₁).snd * ((a₂, s₂).fst * (a₃, s₃).fst, (a₂, s₂).snd * (a₃, s₃).sn …
      simp only [one_mul, smul_smul, ← mul_assoc, mul_right_comm]
      -- 🎉 no goals
    one := mk 1 (1 : S)
    one_mul := by
      rintro ⟨a, s⟩
      -- ⊢ 1 * Quot.mk Setoid.r (a, s) = Quot.mk Setoid.r (a, s)
      exact mk_eq.mpr ⟨1, by simp only [one_mul, one_smul]⟩
      -- 🎉 no goals
    mul_one := by
      rintro ⟨a, s⟩
      -- ⊢ Quot.mk Setoid.r (a, s) * 1 = Quot.mk Setoid.r (a, s)
      exact mk_eq.mpr ⟨1, by simp only [mul_one, one_smul]⟩ }
      -- 🎉 no goals

instance {A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R} :
    CommSemiring (LocalizedModule S A) :=
  { show Semiring (LocalizedModule S A) by infer_instance with
                                           -- 🎉 no goals
    mul_comm := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩
      -- ⊢ Quot.mk Setoid.r (a₁, s₁) * Quot.mk Setoid.r (a₂, s₂) = Quot.mk Setoid.r (a₂ …
      exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩ }
      -- 🎉 no goals

instance {A : Type} [Ring A] [Algebra R A] {S : Submonoid R} :
    Ring (LocalizedModule S A) :=
    { inferInstanceAs (AddCommGroup (LocalizedModule S A)),
      inferInstanceAs (Semiring (LocalizedModule S A)) with }

instance {A : Type _} [CommRing A] [Algebra R A] {S : Submonoid R} :
    CommRing (LocalizedModule S A) :=
  { show (Ring (LocalizedModule S A)) by infer_instance with
                                         -- 🎉 no goals
    mul_comm := by
      rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩
      -- ⊢ Quot.mk Setoid.r (a₁, s₁) * Quot.mk Setoid.r (a₂, s₂) = Quot.mk Setoid.r (a₂ …
      exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩ }
      -- 🎉 no goals

theorem mk_mul_mk {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂) :=
  rfl
#align localized_module.mk_mul_mk LocalizedModule.mk_mul_mk

instance : SMul (Localization S) (LocalizedModule S M)
    where smul f x :=
    (Localization.liftOn f
      (fun r s =>
        (liftOn x (fun p => (mk (r • p.1) (s * p.2)))
          (by
            rintro ⟨m1, t1⟩ ⟨m2, t2⟩ ⟨u, h⟩
            -- ⊢ (fun p => mk (r • p.fst) (s * p.snd)) (m1, t1) = (fun p => mk (r • p.fst) (s …
            refine' mk_eq.mpr ⟨u, _⟩
            -- ⊢ u • (s * (m2, t2).snd) • r • (m1, t1).fst = u • (s * (m1, t1).snd) • r • (m2 …
            have h' := congr_arg ((· • ·) (s • r)) h
            -- ⊢ u • (s * (m2, t2).snd) • r • (m1, t1).fst = u • (s * (m1, t1).snd) • r • (m2 …
            simp only [← mul_smul, smul_eq_mul, mul_comm, mul_left_comm, Submonoid.smul_def,
              Submonoid.coe_mul] at h' ⊢
            rw [h'])))
            -- 🎉 no goals
      (by
        induction' x using LocalizedModule.induction_on with m t
        -- ⊢ ∀ {a c : R} {b d : { x // x ∈ S }}, ↑(Localization.r S) (a, b) (c, d) → (fun …
        rintro r r' s s' h
        -- ⊢ (fun r s => liftOn (mk m t) (fun p => mk (r • p.fst) (s * p.snd)) (_ : ∀ (p  …
        simp only [liftOn_mk, liftOn_mk, mk_eq]
        -- ⊢ ∃ u, u • (s' * t) • r • m = u • (s * t) • r' • m
        obtain ⟨u, eq1⟩ := Localization.r_iff_exists.mp h
        -- ⊢ ∃ u, u • (s' * t) • r • m = u • (s * t) • r' • m
        use u
        -- ⊢ u • (s' * t) • r • m = u • (s * t) • r' • m
        have eq1' := congr_arg (· • t • m) eq1
        -- ⊢ u • (s' * t) • r • m = u • (s * t) • r' • m
        simp only [← mul_smul, smul_assoc, Submonoid.smul_def, Submonoid.coe_mul] at eq1' ⊢
        -- ⊢ (↑u * (↑s' * ↑t * r)) • m = (↑u * (↑s * ↑t * r')) • m
        ring_nf at eq1' ⊢
        -- ⊢ (↑u * ↑s' * r * ↑t) • m = (↑u * ↑t * ↑s * r') • m
        rw [eq1']))
        -- 🎉 no goals

theorem mk_smul_mk (r : R) (m : M) (s t : S) :
    Localization.mk r s • mk m t = mk (r • m) (s * t) := by
  dsimp only [HSMul.hSMul, SMul.smul]
  -- ⊢ Localization.liftOn (Localization.mk r s) (fun r s => liftOn (mk m t) (fun p …
  rw [Localization.liftOn_mk, liftOn_mk]
  -- 🎉 no goals
#align localized_module.mk_smul_mk LocalizedModule.mk_smul_mk

private theorem one_smul' (m : LocalizedModule S M) : (1 : Localization S) • m = m := by
  induction' m using LocalizedModule.induction_on with m s
  -- ⊢ 1 • mk m s = mk m s
  rw [← Localization.mk_one, mk_smul_mk, one_smul, one_mul]
  -- 🎉 no goals

private theorem mul_smul' (x y : Localization S) (m : LocalizedModule S M) :
    (x * y) • m = x • y • m := by
  induction' x using Localization.induction_on with data
  -- ⊢ (Localization.mk data.fst data.snd * y) • m = Localization.mk data.fst data. …
  induction' y using Localization.induction_on with data'
  -- ⊢ (Localization.mk data.fst data.snd * Localization.mk data'.fst data'.snd) •  …
  rcases data, data' with ⟨⟨r, s⟩, ⟨r', s'⟩⟩
  -- ⊢ (Localization.mk (r, s).fst (r, s).snd * Localization.mk (r', s').fst (r', s …
  induction' m using LocalizedModule.induction_on with m t
  -- ⊢ (Localization.mk (r, s).fst (r, s).snd * Localization.mk (r', s').fst (r', s …
  rw [Localization.mk_mul, mk_smul_mk, mk_smul_mk, mk_smul_mk, mul_smul, mul_assoc]
  -- 🎉 no goals

private theorem smul_add' (x : Localization S) (y z : LocalizedModule S M) :
    x • (y + z) = x • y + x • z := by
  induction' x using Localization.induction_on with data
  -- ⊢ Localization.mk data.fst data.snd • (y + z) = Localization.mk data.fst data. …
  rcases data with ⟨r, u⟩
  -- ⊢ Localization.mk (r, u).fst (r, u).snd • (y + z) = Localization.mk (r, u).fst …
  induction' y using LocalizedModule.induction_on with m s
  -- ⊢ Localization.mk (r, u).fst (r, u).snd • (mk m s + z) = Localization.mk (r, u …
  induction' z using LocalizedModule.induction_on with n t
  -- ⊢ Localization.mk (r, u).fst (r, u).snd • (mk m s + mk n t) = Localization.mk  …
  rw [mk_smul_mk, mk_smul_mk, mk_add_mk, mk_smul_mk, mk_add_mk, mk_eq]
  -- ⊢ ∃ u_1, u_1 • ((r, u).snd * s * ((r, u).snd * t)) • (r, u).fst • (t • m + s • …
  use 1
  -- ⊢ 1 • ((r, u).snd * s * ((r, u).snd * t)) • (r, u).fst • (t • m + s • n) = 1 • …
  simp only [one_smul, smul_add, ← mul_smul, Submonoid.smul_def, Submonoid.coe_mul]
  -- ⊢ (↑u * ↑s * (↑u * ↑t) * (r * ↑t)) • m + (↑u * ↑s * (↑u * ↑t) * (r * ↑s)) • n  …
  ring_nf
  -- 🎉 no goals

private theorem smul_zero' (x : Localization S) : x • (0 : LocalizedModule S M) = 0 := by
  induction' x using Localization.induction_on with data
  -- ⊢ Localization.mk data.fst data.snd • 0 = 0
  rcases data with ⟨r, s⟩
  -- ⊢ Localization.mk (r, s).fst (r, s).snd • 0 = 0
  rw [← zero_mk s, mk_smul_mk, smul_zero, zero_mk, zero_mk]
  -- 🎉 no goals

private theorem add_smul' (x y : Localization S) (z : LocalizedModule S M) :
    (x + y) • z = x • z + y • z := by
  induction' x using Localization.induction_on with datax
  -- ⊢ (Localization.mk datax.fst datax.snd + y) • z = Localization.mk datax.fst da …
  induction' y using Localization.induction_on with datay
  -- ⊢ (Localization.mk datax.fst datax.snd + Localization.mk datay.fst datay.snd)  …
  induction' z using LocalizedModule.induction_on with m t
  -- ⊢ (Localization.mk datax.fst datax.snd + Localization.mk datay.fst datay.snd)  …
  rcases datax, datay with ⟨⟨r, s⟩, ⟨r', s'⟩⟩
  -- ⊢ (Localization.mk (r, s).fst (r, s).snd + Localization.mk (r', s').fst (r', s …
  rw [Localization.add_mk, mk_smul_mk, mk_smul_mk, mk_smul_mk, mk_add_mk, mk_eq]
  -- ⊢ ∃ u, u • ((r, s).snd * t * ((r', s').snd * t)) • (↑(r, s).snd * (r', s').fst …
  use 1
  -- ⊢ 1 • ((r, s).snd * t * ((r', s').snd * t)) • (↑(r, s).snd * (r', s').fst + ↑( …
  simp only [one_smul, add_smul, smul_add, ← mul_smul, Submonoid.smul_def, Submonoid.coe_mul,
    Submonoid.coe_one]
  rw [add_comm]
  -- ⊢ (↑s * ↑t * (↑s' * ↑t) * (↑s' * r)) • m + (↑s * ↑t * (↑s' * ↑t) * (↑s * r'))  …
  -- Commutativity of addition in the module is not applied by `Ring`.
  ring_nf
  -- 🎉 no goals

private theorem zero_smul' (x : LocalizedModule S M) : (0 : Localization S) • x = 0 := by
  induction' x using LocalizedModule.induction_on with m s
  -- ⊢ 0 • mk m s = 0
  rw [← Localization.mk_zero s, mk_smul_mk, zero_smul, zero_mk]
  -- 🎉 no goals

instance isModule : Module (Localization S) (LocalizedModule S M) where
  smul := (· • ·)
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_add := smul_add'
  smul_zero := smul_zero'
  add_smul := add_smul'
  zero_smul := zero_smul'
#align localized_module.is_module LocalizedModule.isModule

@[simp]
theorem mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s :=
  mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      -- ⊢ s • s' • m = s' • s • m
      rw [smul_comm]⟩
      -- 🎉 no goals
#align localized_module.mk_cancel_common_left LocalizedModule.mk_cancel_common_left

@[simp]
theorem mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1 :=
  mk_eq.mpr ⟨1, by simp⟩
                   -- 🎉 no goals
#align localized_module.mk_cancel LocalizedModule.mk_cancel

@[simp]
theorem mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s :=
  mk_eq.mpr ⟨1, by simp [mul_smul]⟩
                   -- 🎉 no goals
#align localized_module.mk_cancel_common_right LocalizedModule.mk_cancel_common_right

instance isModule' : Module R (LocalizedModule S M) :=
  { Module.compHom (LocalizedModule S M) <| algebraMap R (Localization S) with }
#align localized_module.is_module' LocalizedModule.isModule'

theorem smul'_mk (r : R) (s : S) (m : M) : r • mk m s = mk (r • m) s := by
  erw [mk_smul_mk r m 1 s, one_mul]
  -- 🎉 no goals
#align localized_module.smul'_mk LocalizedModule.smul'_mk

instance {A : Type*} [Semiring A] [Algebra R A] :
    Algebra (Localization S) (LocalizedModule S A) :=
  Algebra.ofModule
    (by
      intro r x₁ x₂
      -- ⊢ r • x₁ * x₂ = r • (x₁ * x₂)
      obtain ⟨y, s, rfl : IsLocalization.mk' _ y s = r⟩ := IsLocalization.mk'_surjective S r
      -- ⊢ IsLocalization.mk' (Localization S) y s • x₁ * x₂ = IsLocalization.mk' (Loca …
      obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := Quotient.exists_rep x₁
      -- ⊢ IsLocalization.mk' (Localization S) y s • mk a₁ s₁ * x₂ = IsLocalization.mk' …
      obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := Quotient.exists_rep x₂
      -- ⊢ IsLocalization.mk' (Localization S) y s • mk a₁ s₁ * mk a₂ s₂ = IsLocalizati …
      rw [mk_mul_mk, ← Localization.mk_eq_mk', mk_smul_mk, mk_smul_mk, mk_mul_mk, mul_assoc,
        smul_mul_assoc])
    (by
      intro r x₁ x₂
      -- ⊢ x₁ * r • x₂ = r • (x₁ * x₂)
      obtain ⟨y, s, rfl : IsLocalization.mk' _ y s = r⟩ := IsLocalization.mk'_surjective S r
      -- ⊢ x₁ * IsLocalization.mk' (Localization S) y s • x₂ = IsLocalization.mk' (Loca …
      obtain ⟨⟨a₁, s₁⟩, rfl : mk a₁ s₁ = x₁⟩ := Quotient.exists_rep x₁
      -- ⊢ mk a₁ s₁ * IsLocalization.mk' (Localization S) y s • x₂ = IsLocalization.mk' …
      obtain ⟨⟨a₂, s₂⟩, rfl : mk a₂ s₂ = x₂⟩ := Quotient.exists_rep x₂
      -- ⊢ mk a₁ s₁ * IsLocalization.mk' (Localization S) y s • mk a₂ s₂ = IsLocalizati …
      rw [mk_mul_mk, ← Localization.mk_eq_mk', mk_smul_mk, mk_smul_mk, mk_mul_mk, mul_left_comm,
        mul_smul_comm])

theorem algebraMap_mk {A : Type*} [Semiring A] [Algebra R A] (a : R) (s : S) :
    algebraMap _ _ (Localization.mk a s) = mk (algebraMap R A a) s := by
  rw [Algebra.algebraMap_eq_smul_one]
  -- ⊢ Localization.mk a s • 1 = mk (↑(algebraMap R A) a) s
  change _ • mk _ _ = _
  -- ⊢ Localization.mk a s • mk 1 1 = mk (↑(algebraMap R A) a) s
  rw [mk_smul_mk, Algebra.algebraMap_eq_smul_one, mul_one]
  -- 🎉 no goals
#align localized_module.algebra_map_mk LocalizedModule.algebraMap_mk

instance : IsScalarTower R (Localization S) (LocalizedModule S M) :=
  RestrictScalars.isScalarTower R (Localization S) (LocalizedModule S M)

instance algebra' {A : Type*} [Semiring A] [Algebra R A] : Algebra R (LocalizedModule S A) :=
  { (algebraMap (Localization S) (LocalizedModule S A)).comp (algebraMap R <| Localization S),
    show Module R (LocalizedModule S A) by
      infer_instance with
      -- 🎉 no goals
    commutes' := by
      intro r x
      -- ⊢ ↑{ toMonoidHom := ↑src✝¹, map_zero' := (_ : OneHom.toFun (↑↑src✝¹) 0 = 0), m …
      obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := Quotient.exists_rep x
      -- ⊢ ↑{ toMonoidHom := ↑src✝¹, map_zero' := (_ : OneHom.toFun (↑↑src✝¹) 0 = 0), m …
      dsimp
      -- ⊢ ↑(algebraMap (Localization S) (LocalizedModule S A)) (↑(algebraMap R (Locali …
      rw [← Localization.mk_one_eq_algebraMap, algebraMap_mk, mk_mul_mk, mk_mul_mk, mul_comm,
        Algebra.commutes]
    smul_def' := by
      intro r x
      -- ⊢ r • x = ↑{ toMonoidHom := ↑src✝¹, map_zero' := (_ : OneHom.toFun (↑↑src✝¹) 0 …
      obtain ⟨⟨a, s⟩, rfl : mk a s = x⟩ := Quotient.exists_rep x
      -- ⊢ r • mk a s = ↑{ toMonoidHom := ↑src✝¹, map_zero' := (_ : OneHom.toFun (↑↑src …
      dsimp
      -- ⊢ r • mk a s = ↑(algebraMap (Localization S) (LocalizedModule S A)) (↑(algebra …
      rw [← Localization.mk_one_eq_algebraMap, algebraMap_mk, mk_mul_mk, smul'_mk,
        Algebra.smul_def, one_mul] }
#align localized_module.algebra' LocalizedModule.algebra'

section

variable (S M)

/-- The function `m ↦ m / 1` as an `R`-linear map.
-/
@[simps]
def mkLinearMap : M →ₗ[R] LocalizedModule S M where
  toFun m := mk m 1
  map_add' x y := by simp [mk_add_mk]
                     -- 🎉 no goals
  map_smul' r x := (smul'_mk _ _ _).symm
#align localized_module.mk_linear_map LocalizedModule.mkLinearMap

end

/-- For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
@[simps]
def divBy (s : S) : LocalizedModule S M →ₗ[R] LocalizedModule S M where
  toFun p :=
    p.liftOn (fun p => mk p.1 (s * p.2)) fun ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩ =>
      mk_eq.mpr ⟨c, by rw [mul_smul, mul_smul, smul_comm c, eq1, smul_comm s]⟩
                       -- 🎉 no goals
  map_add' x y :=
    x.induction_on₂
      (by
        intro m₁ m₂ t₁ t₂
        -- ⊢ (fun p => liftOn p (fun p => mk p.fst (s * p.snd)) (_ : ∀ (x x_1 : M × { x / …
        simp only [mk_add_mk, LocalizedModule.liftOn_mk, mul_smul, ← smul_add, mul_assoc,
          mk_cancel_common_left s]
        rw [show s * (t₁ * t₂) = t₁ * (s * t₂) by
            ext
            simp only [Submonoid.coe_mul]
            ring])
      y
  map_smul' r x :=
    x.inductionOn <| by
      intro
      -- ⊢ AddHom.toFun { toFun := fun p => liftOn p (fun p => mk p.fst (s * p.snd)) (_ …
      dsimp only
      -- ⊢ liftOn (r • Quotient.mk (r.setoid S M) a✝) (fun p => mk p.fst (s * p.snd)) ( …
      change liftOn (mk _ _) _ _ = r • (liftOn (mk _ _) _ _)
      -- ⊢ liftOn (mk ((↑(algebraMap R R) r, 1).fst • a✝.fst) ((↑(algebraMap R R) r, 1) …
      simp [LocalizedModule.liftOn_mk, smul'_mk]
      -- 🎉 no goals
#align localized_module.div_by LocalizedModule.divBy

theorem divBy_mul_by (s : S) (p : LocalizedModule S M) :
    divBy s (algebraMap R (Module.End R (LocalizedModule S M)) s p) = p :=
  p.inductionOn
    (by
      intro ⟨m, t⟩
      -- ⊢ ↑(divBy s) (↑(↑(algebraMap R (Module.End R (LocalizedModule S M))) ↑s) (Quot …
      simp only [Module.algebraMap_end_apply, smul'_mk, divBy_apply]
      -- ⊢ liftOn (↑s • Quotient.mk (r.setoid S M) (m, t)) (fun p => mk p.fst (s * p.sn …
      erw [LocalizedModule.liftOn_mk]
      -- ⊢ mk ((↑(algebraMap R R) ↑s, 1).fst • (m, t).fst, (↑(algebraMap R R) ↑s, 1).sn …
      simp only [one_mul]
      -- ⊢ mk (↑(algebraMap R R) ↑s • m) (s * t) = Quotient.mk (r.setoid S M) (m, t)
      change mk (s • m) (s * t) = mk m t
      -- ⊢ mk (s • m) (s * t) = mk m t
      rw [mk_cancel_common_left s t])
      -- 🎉 no goals
#align localized_module.div_by_mul_by LocalizedModule.divBy_mul_by

theorem mul_by_divBy (s : S) (p : LocalizedModule S M) :
    algebraMap R (Module.End R (LocalizedModule S M)) s (divBy s p) = p :=
  p.inductionOn
    (by
      intro ⟨m, t⟩
      -- ⊢ ↑(↑(algebraMap R (Module.End R (LocalizedModule S M))) ↑s) (↑(divBy s) (Quot …
      simp only [LocalizedModule.liftOn_mk, divBy_apply, Module.algebraMap_end_apply, smul'_mk]
      -- ⊢ ↑s • liftOn (Quotient.mk (r.setoid S M) (m, t)) (fun p => mk p.fst (s * p.sn …
      erw [LocalizedModule.liftOn_mk, smul'_mk]
      -- ⊢ mk (↑s • (m, t).fst) (s * (m, t).snd) = Quotient.mk (r.setoid S M) (m, t)
      change mk (s • m) (s * t) = mk m t
      -- ⊢ mk (s • m) (s * t) = mk m t
      rw [mk_cancel_common_left s t])
      -- 🎉 no goals
#align localized_module.mul_by_div_by LocalizedModule.mul_by_divBy

end

end LocalizedModule

section IsLocalizedModule

universe u v

variable {R : Type*} [CommRing R] (S : Submonoid R)

variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']

variable [Module R M] [Module R M'] [Module R M''] (f : M →ₗ[R] M') (g : M →ₗ[R] M'')

/-- The characteristic predicate for localized module.
`IsLocalizedModule S f` describes that `f : M ⟶ M'` is the localization map identifying `M'` as
`LocalizedModule S M`.
-/
class IsLocalizedModule : Prop where
  map_units : ∀ x : S, IsUnit (algebraMap R (Module.End R M') x)
  surj' : ∀ y : M', ∃ x : M × S, x.2 • y = f x.1
  eq_iff_exists' : ∀ {x₁ x₂}, f x₁ = f x₂ ↔ ∃ c : S, c • x₂ = c • x₁
#align is_localized_module IsLocalizedModule

attribute [nolint docBlame] IsLocalizedModule.map_units IsLocalizedModule.surj'
  IsLocalizedModule.eq_iff_exists'

-- Porting note: Manually added to make `S` and `f` explicit.
lemma IsLocalizedModule.surj [IsLocalizedModule S f] (y : M') : ∃ x : M × S, x.2 • y = f x.1 :=
  surj' y

-- Porting note: Manually added to make `S` and `f` explicit.
lemma IsLocalizedModule.eq_iff_exists [IsLocalizedModule S f] {x₁ x₂} :
    f x₁ = f x₂ ↔ ∃ c : S, c • x₂ = c • x₁ :=
eq_iff_exists'

namespace LocalizedModule

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
noncomputable def lift' (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit (algebraMap R (Module.End R M'') x)) : LocalizedModule S M → M'' :=
  fun m =>
  m.liftOn (fun p => (h p.2).unit⁻¹.val <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    -- Porting note: We remove `generalize_proofs h1 h2`. This does nothing here.
    erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← map_smul]
    -- ⊢ ↑g (m, s).fst = ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'' …
    symm
    -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑(m', s').snd …
    erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff]
    -- ⊢ ↑(m, s).snd • ↑g (m', s').fst = ↑(m', s').snd • ↑g (m, s).fst
    dsimp
    -- ⊢ ↑s • ↑g m' = ↑s' • ↑g m
    have : c • s • g m' = c • s' • g m := by
      erw [← g.map_smul, ← g.map_smul, ← g.map_smul, ← g.map_smul, eq1]
      rfl
    have : Function.Injective (h c).unit.inv := by
      rw [Function.injective_iff_hasLeftInverse]
      refine' ⟨(h c).unit, _⟩
      intro x
      change ((h c).unit.1 * (h c).unit.inv) x = x
      simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, LinearMap.one_apply]
    apply_fun (h c).unit.inv
    -- ⊢ ↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑c))).inv (↑s  …
    erw [Units.inv_eq_val_inv, Module.End_algebraMap_isUnit_inv_apply_eq_iff, ←
      (h c).unit⁻¹.val.map_smul]
    symm
    -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑c)))⁻¹ (↑c • …
    erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← g.map_smul, ← g.map_smul, ← g.map_smul, ←
      g.map_smul, eq1]
    rfl
    -- 🎉 no goals
#align localized_module.lift' LocalizedModule.lift'

theorem lift'_mk (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (m : M) (s : S) :
    LocalizedModule.lift' S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl
#align localized_module.lift'_mk LocalizedModule.lift'_mk

theorem lift'_add (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (x y) :
    LocalizedModule.lift' S g h (x + y) =
      LocalizedModule.lift' S g h x + LocalizedModule.lift' S g h y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      -- ⊢ lift' S g h (mk a b + mk a' b') = lift' S g h (mk a b) + lift' S g h (mk a'  …
      erw [LocalizedModule.lift'_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk]
      -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑((a, b).snd  …
      -- Porting note: We remove `generalize_proofs h1 h2 h3`. This only generalize `h1`.
      erw [map_add, Module.End_algebraMap_isUnit_inv_apply_eq_iff, smul_add, ← map_smul,
        ← map_smul, ← map_smul]
      congr 1 <;> symm
      -- ⊢ ↑g ((a', b').snd • (a, b).fst) = ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R  …
                  -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑b)))⁻¹ (↑g ( …
                  -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑b')))⁻¹ (↑(( …
      · erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, mul_smul, ← map_smul]
        -- ⊢ ↑g (↑(a, b).snd • ↑(a', b').snd • a) = ↑g (↑b • (a', b').snd • (a, b).fst)
        rfl
        -- 🎉 no goals
      · dsimp
        -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑b')))⁻¹ ((↑b …
        erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, mul_comm, mul_smul, ← map_smul]
        -- ⊢ ↑b' • ↑g (↑b • a') = ↑b' • ↑g (b • a')
        rfl)
        -- 🎉 no goals
    x y
#align localized_module.lift'_add LocalizedModule.lift'_add

theorem lift'_smul (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (r : R) (m) : r • LocalizedModule.lift' S g h m = LocalizedModule.lift' S g h (r • m) :=
  m.inductionOn
    (by
      intro ⟨a, b⟩
      -- ⊢ r • lift' S g h (Quotient.mk (r.setoid S M) (a, b)) = lift' S g h (r • Quoti …
      erw [LocalizedModule.lift'_mk, LocalizedModule.smul'_mk, LocalizedModule.lift'_mk]
      -- ⊢ r • ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑b)))⁻¹ ( …
      -- Porting note: We remove `generalize_proofs h1 h2`. This does nothing here.
      erw [← map_smul, ← g.map_smul])
      -- 🎉 no goals
#align localized_module.lift'_smul LocalizedModule.lift'_smul

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) : LocalizedModule S M →ₗ[R] M''
    where
  toFun := LocalizedModule.lift' S g h
  map_add' := LocalizedModule.lift'_add S g h
  map_smul' r x := by rw [LocalizedModule.lift'_smul, RingHom.id_apply]
                      -- 🎉 no goals
#align localized_module.lift LocalizedModule.lift

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
`lift g m s = s⁻¹ • g m`.
-/
theorem lift_mk
    (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit (algebraMap R (Module.End R M'') x)) (m : M) (s : S) :
    LocalizedModule.lift S g h (LocalizedModule.mk m s) = (h s).unit⁻¹.val (g m) :=
  rfl
#align localized_module.lift_mk LocalizedModule.lift_mk

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `lift g ∘ mk_linear_map = g`.
-/
theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S g h).comp (mkLinearMap S M) = g := by
  ext x; dsimp; rw [LocalizedModule.lift_mk]
  -- ⊢ ↑(LinearMap.comp (lift S g h) (mkLinearMap S M)) x = ↑g x
         -- ⊢ ↑(lift S g h) (mk x 1) = ↑g x
                -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑1)))⁻¹ (↑g x …
  erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, one_smul]
  -- 🎉 no goals
#align localized_module.lift_comp LocalizedModule.lift_comp

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible and
`l` is another linear map `LocalizedModule S M ⟶ M''` such that `l ∘ mk_linear_map = g` then
`l = lift g`
-/
theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : LocalizedModule S M →ₗ[R] M'') (hl : l.comp (LocalizedModule.mkLinearMap S M) = g) :
    LocalizedModule.lift S g h = l := by
  ext x; induction' x using LocalizedModule.induction_on with m s
  -- ⊢ ↑(lift S g h) x = ↑l x
         -- ⊢ ↑(lift S g h) (mk m s) = ↑l (mk m s)
  rw [LocalizedModule.lift_mk]
  -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'')) ↑s)))⁻¹ (↑g m …
  erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← hl, LinearMap.coe_comp,
    Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← l.map_smul, LocalizedModule.smul'_mk]
  congr 1; rw [LocalizedModule.mk_eq]
  -- ⊢ mk m 1 = mk (↑s • m) s
           -- ⊢ ∃ u, u • s • m = u • 1 • ↑s • m
  refine' ⟨1, _⟩; simp only [one_smul]; rfl
  -- ⊢ 1 • s • m = 1 • 1 • ↑s • m
                  -- ⊢ s • m = ↑s • m
                                        -- 🎉 no goals
#align localized_module.lift_unique LocalizedModule.lift_unique

end LocalizedModule

instance localizedModuleIsLocalizedModule : IsLocalizedModule S (LocalizedModule.mkLinearMap S M)
    where
  map_units s :=
    ⟨⟨algebraMap R (Module.End R (LocalizedModule S M)) s, LocalizedModule.divBy s,
        FunLike.ext _ _ <| LocalizedModule.mul_by_divBy s,
        FunLike.ext _ _ <| LocalizedModule.divBy_mul_by s⟩,
      FunLike.ext _ _ fun p =>
        p.inductionOn <| by
          intros
          -- ⊢ ↑↑{ val := ↑(algebraMap R (Module.End R (LocalizedModule S M))) ↑s, inv := L …
          rfl⟩
          -- 🎉 no goals
  surj' p :=
    p.inductionOn
      (by
        intro ⟨m, t⟩
        -- ⊢ ∃ x, x.snd • Quotient.mk (LocalizedModule.r.setoid S M) (m, t) = ↑(Localized …
        refine' ⟨⟨m, t⟩, _⟩
        -- ⊢ (m, t).snd • Quotient.mk (LocalizedModule.r.setoid S M) (m, t) = ↑(Localized …
        erw [LocalizedModule.smul'_mk, LocalizedModule.mkLinearMap_apply, Submonoid.coe_subtype,
          LocalizedModule.mk_cancel t])
  eq_iff_exists' :=
    { mp := fun eq1 => by simpa only [eq_comm, one_smul] using LocalizedModule.mk_eq.mp eq1
                          -- 🎉 no goals
      mpr := fun ⟨c, eq1⟩ =>
        LocalizedModule.mk_eq.mpr ⟨c, by simpa only [eq_comm, one_smul] using eq1⟩ }
                                         -- 🎉 no goals
#align localized_module_is_localized_module localizedModuleIsLocalizedModule

namespace IsLocalizedModule

variable [IsLocalizedModule S f]

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule' : LocalizedModule S M → M' := fun p =>
  p.liftOn (fun x => (IsLocalizedModule.map_units f x.2).unit⁻¹.val (f x.1))
    (by
      rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨c, eq1⟩
      -- ⊢ (fun x => ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M')) ↑x.s …
      dsimp
      -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M')) ↑b)))⁻¹ (↑f a) …
      -- Porting note: We remove `generalize_proofs h1 h2`.
      erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ←map_smul, ←map_smul,
        Module.End_algebraMap_isUnit_inv_apply_eq_iff', ←map_smul]
      exact (IsLocalizedModule.eq_iff_exists S f).mpr ⟨c, eq1⟩)
      -- 🎉 no goals
#align is_localized_module.from_localized_module' IsLocalizedModule.fromLocalizedModule'

@[simp]
theorem fromLocalizedModule'_mk (m : M) (s : S) :
    fromLocalizedModule' S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
#align is_localized_module.from_localized_module'_mk IsLocalizedModule.fromLocalizedModule'_mk

theorem fromLocalizedModule'_add (x y : LocalizedModule S M) :
    fromLocalizedModule' S f (x + y) = fromLocalizedModule' S f x + fromLocalizedModule' S f y :=
  LocalizedModule.induction_on₂
    (by
      intro a a' b b'
      -- ⊢ fromLocalizedModule' S f (LocalizedModule.mk a b + LocalizedModule.mk a' b') …
      simp only [LocalizedModule.mk_add_mk, fromLocalizedModule'_mk]
      -- ⊢ ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M')) ↑(b * b'))))⁻¹ …
      -- Porting note: We remove `generalize_proofs h1 h2 h3`.
      erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, smul_add, ←map_smul, ←map_smul,
        ←map_smul, map_add]
      congr 1
      -- ⊢ ↑f (b' • a) = ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M'))  …
      all_goals erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff']
      -- ⊢ ↑f (↑(b * b') • a) = ↑b • ↑f (b' • a)
      · erw [mul_smul, f.map_smul]
        -- ⊢ ↑b • ↑f (↑b' • a) = ↑b • ↑f (b' • a)
        rfl
        -- 🎉 no goals
      · erw [mul_comm, f.map_smul, mul_smul]
        -- ⊢ ↑b' • ↑b • ↑f a' = ↑b' • ↑(Submonoid.subtype S) b • ↑f a'
        rfl)
        -- 🎉 no goals
    x y
#align is_localized_module.from_localized_module'_add IsLocalizedModule.fromLocalizedModule'_add

theorem fromLocalizedModule'_smul (r : R) (x : LocalizedModule S M) :
    r • fromLocalizedModule' S f x = fromLocalizedModule' S f (r • x) :=
  LocalizedModule.induction_on
    (by
      intro a b
      -- ⊢ r • fromLocalizedModule' S f (LocalizedModule.mk a b) = fromLocalizedModule' …
      rw [fromLocalizedModule'_mk, LocalizedModule.smul'_mk, fromLocalizedModule'_mk]
      -- ⊢ r • ↑↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R (Module.End R M')) ↑b)))⁻¹ (↑ …
      -- Porting note: We remove `generalize_proofs h1`.
      rw [f.map_smul, map_smul])
      -- 🎉 no goals
    x
#align is_localized_module.from_localized_module'_smul IsLocalizedModule.fromLocalizedModule'_smul

/-- If `(M', f : M ⟶ M')` satisfies universal property of localized module, there is a canonical
map `LocalizedModule S M ⟶ M'`.
-/
noncomputable def fromLocalizedModule : LocalizedModule S M →ₗ[R] M' where
  toFun := fromLocalizedModule' S f
  map_add' := fromLocalizedModule'_add S f
  map_smul' r x := by rw [fromLocalizedModule'_smul, RingHom.id_apply]
                      -- 🎉 no goals
#align is_localized_module.from_localized_module IsLocalizedModule.fromLocalizedModule

theorem fromLocalizedModule_mk (m : M) (s : S) :
    fromLocalizedModule S f (LocalizedModule.mk m s) =
      (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
#align is_localized_module.from_localized_module_mk IsLocalizedModule.fromLocalizedModule_mk

theorem fromLocalizedModule.inj : Function.Injective <| fromLocalizedModule S f := fun x y eq1 => by
  induction' x using LocalizedModule.induction_on with a b
  -- ⊢ LocalizedModule.mk a b = y
  induction' y using LocalizedModule.induction_on with a' b'
  -- ⊢ LocalizedModule.mk a b = LocalizedModule.mk a' b'
  simp only [fromLocalizedModule_mk] at eq1
  -- ⊢ LocalizedModule.mk a b = LocalizedModule.mk a' b'
  -- Porting note: We remove `generalize_proofs h1 h2`.
  erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← LinearMap.map_smul,
    Module.End_algebraMap_isUnit_inv_apply_eq_iff'] at eq1
  erw [LocalizedModule.mk_eq, ← IsLocalizedModule.eq_iff_exists S f,
    f.map_smul, f.map_smul, eq1]
  rfl
  -- 🎉 no goals
#align is_localized_module.from_localized_module.inj IsLocalizedModule.fromLocalizedModule.inj

theorem fromLocalizedModule.surj : Function.Surjective <| fromLocalizedModule S f := fun x =>
  let ⟨⟨m, s⟩, eq1⟩ := IsLocalizedModule.surj S f x
  ⟨LocalizedModule.mk m s, by
    rw [fromLocalizedModule_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← eq1]
    -- ⊢ (m, s).snd • x = ↑s • x
    rfl⟩
    -- 🎉 no goals
#align is_localized_module.from_localized_module.surj IsLocalizedModule.fromLocalizedModule.surj

theorem fromLocalizedModule.bij : Function.Bijective <| fromLocalizedModule S f :=
  ⟨fromLocalizedModule.inj _ _, fromLocalizedModule.surj _ _⟩
#align is_localized_module.from_localized_module.bij IsLocalizedModule.fromLocalizedModule.bij

/--
If `(M', f : M ⟶ M')` satisfies universal property of localized module, then `M'` is isomorphic to
`LocalizedModule S M` as an `R`-module.
-/
@[simps!]
noncomputable def iso : LocalizedModule S M ≃ₗ[R] M' :=
  { fromLocalizedModule S f,
    Equiv.ofBijective (fromLocalizedModule S f) <| fromLocalizedModule.bij _ _ with }
#align is_localized_module.iso IsLocalizedModule.iso

theorem iso_apply_mk (m : M) (s : S) :
    iso S f (LocalizedModule.mk m s) = (IsLocalizedModule.map_units f s).unit⁻¹.val (f m) :=
  rfl
#align is_localized_module.iso_apply_mk IsLocalizedModule.iso_apply_mk

theorem iso_symm_apply_aux (m : M') :
    (iso S f).symm m =
      LocalizedModule.mk (IsLocalizedModule.surj S f m).choose.1
        (IsLocalizedModule.surj S f m).choose.2 := by
  -- Porting note: We remove `generalize_proofs _ h2`.
  apply_fun iso S f using LinearEquiv.injective (iso S f)
  -- ⊢ ↑(iso S f) (↑(LinearEquiv.symm (iso S f)) m) = ↑(iso S f) (LocalizedModule.m …
  rw [LinearEquiv.apply_symm_apply]
  -- ⊢ m = ↑(iso S f) (LocalizedModule.mk (Exists.choose (_ : ∃ x, x.snd • m = ↑f x …
  simp only [iso_apply, LinearMap.toFun_eq_coe, fromLocalizedModule_mk]
  -- ⊢ m = fromLocalizedModule' S f (LocalizedModule.mk (Exists.choose (_ : ∃ x, x. …
  erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff', (surj' _).choose_spec]
  -- 🎉 no goals

#align is_localized_module.iso_symm_apply_aux IsLocalizedModule.iso_symm_apply_aux

theorem iso_symm_apply' (m : M') (a : M) (b : S) (eq1 : b • m = f a) :
    (iso S f).symm m = LocalizedModule.mk a b :=
  (iso_symm_apply_aux S f m).trans <|
    LocalizedModule.mk_eq.mpr <| by
      -- Porting note: We remove `generalize_proofs h1`.
      erw [← IsLocalizedModule.eq_iff_exists S f, f.map_smul, f.map_smul, ← (surj' _).choose_spec,
      ← mul_smul, mul_comm, mul_smul, eq1]
#align is_localized_module.iso_symm_apply' IsLocalizedModule.iso_symm_apply'

theorem iso_symm_comp : (iso S f).symm.toLinearMap.comp f = LocalizedModule.mkLinearMap S M := by
  ext m; rw [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  -- ⊢ ↑(LinearMap.comp (↑(LinearEquiv.symm (iso S f))) f) m = ↑(LocalizedModule.mk …
         -- ⊢ ↑↑(LinearEquiv.symm (iso S f)) (↑f m) = LocalizedModule.mk m 1
  change (iso S f).symm _ = _; rw [iso_symm_apply']; exact one_smul _ _
  -- ⊢ ↑(LinearEquiv.symm (iso S f)) (↑f m) = LocalizedModule.mk m 1
                               -- ⊢ 1 • ↑f m = ↑f m
                                                     -- 🎉 no goals
#align is_localized_module.iso_symm_comp IsLocalizedModule.iso_symm_comp

/--
If `M'` is a localized module and `g` is a linear map `M' → M''` such that all scalar multiplication
by `s : S` is invertible, then there is a linear map `M' → M''`.
-/
noncomputable def lift (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) : M' →ₗ[R] M'' :=
  (LocalizedModule.lift S g h).comp (iso S f).symm.toLinearMap
#align is_localized_module.lift IsLocalizedModule.lift

theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S f g h).comp f = g := by
  dsimp only [IsLocalizedModule.lift]
  -- ⊢ LinearMap.comp (LinearMap.comp (LocalizedModule.lift S g h) ↑(LinearEquiv.sy …
  rw [LinearMap.comp_assoc]
  -- ⊢ LinearMap.comp (LocalizedModule.lift S g h) (LinearMap.comp (↑(LinearEquiv.s …
  convert LocalizedModule.lift_comp S g h
  -- ⊢ LinearMap.comp (↑(LinearEquiv.symm (iso S f))) f = LocalizedModule.mkLinearM …
  exact iso_symm_comp _ _
  -- 🎉 no goals
#align is_localized_module.lift_comp IsLocalizedModule.lift_comp

theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : M' →ₗ[R] M'') (hl : l.comp f = g) : lift S f g h = l := by
  dsimp only [IsLocalizedModule.lift]
  -- ⊢ LinearMap.comp (LocalizedModule.lift S g h) ↑(LinearEquiv.symm (iso S f)) = l
  rw [LocalizedModule.lift_unique S g h (l.comp (iso S f).toLinearMap), LinearMap.comp_assoc,
    show (iso S f).toLinearMap.comp (iso S f).symm.toLinearMap = LinearMap.id from _,
    LinearMap.comp_id]
  · rw [LinearEquiv.comp_toLinearMap_symm_eq, LinearMap.id_comp]
    -- 🎉 no goals
  · rw [LinearMap.comp_assoc, ← hl]
    -- ⊢ LinearMap.comp l (LinearMap.comp (↑(iso S f)) (LocalizedModule.mkLinearMap S …
    congr 1
    -- ⊢ LinearMap.comp (↑(iso S f)) (LocalizedModule.mkLinearMap S M) = f
    ext x
    -- ⊢ ↑(LinearMap.comp (↑(iso S f)) (LocalizedModule.mkLinearMap S M)) x = ↑f x
    erw [fromLocalizedModule_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, one_smul]
    -- 🎉 no goals
#align is_localized_module.lift_unique IsLocalizedModule.lift_unique

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
#align is_localized_module.is_universal IsLocalizedModule.is_universal

theorem ringHom_ext (map_unit : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    ⦃j k : M' →ₗ[R] M''⦄ (h : j.comp f = k.comp f) : j = k := by
  rw [← lift_unique S f (k.comp f) map_unit j h, lift_unique]
  -- ⊢ LinearMap.comp k f = LinearMap.comp k f
  rfl
  -- 🎉 no goals
#align is_localized_module.ring_hom_ext IsLocalizedModule.ringHom_ext

/-- If `(M', f)` and `(M'', g)` both satisfy universal property of localized module, then `M', M''`
are isomorphic as `R`-module
-/
noncomputable def linearEquiv [IsLocalizedModule S g] : M' ≃ₗ[R] M'' :=
  (iso S f).symm.trans (iso S g)
#align is_localized_module.linear_equiv IsLocalizedModule.linearEquiv

variable {S}

theorem smul_injective (s : S) : Function.Injective fun m : M' => s • m :=
  ((Module.End_isUnit_iff _).mp (IsLocalizedModule.map_units f s)).injective
#align is_localized_module.smul_injective IsLocalizedModule.smul_injective

theorem smul_inj (s : S) (m₁ m₂ : M') : s • m₁ = s • m₂ ↔ m₁ = m₂ :=
  (smul_injective f s).eq_iff
#align is_localized_module.smul_inj IsLocalizedModule.smul_inj

/-- `mk' f m s` is the fraction `m/s` with respect to the localization map `f`. -/
noncomputable def mk' (m : M) (s : S) : M' :=
  fromLocalizedModule S f (LocalizedModule.mk m s)
#align is_localized_module.mk' IsLocalizedModule.mk'

theorem mk'_smul (r : R) (m : M) (s : S) : mk' f (r • m) s = r • mk' f m s := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk (r • m) s) = r • ↑(fromLocali …
  rw [← LocalizedModule.smul'_mk, LinearMap.map_smul]
  -- 🎉 no goals
#align is_localized_module.mk'_smul IsLocalizedModule.mk'_smul

theorem mk'_add_mk' (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ + mk' f m₂ s₂ = mk' f (s₂ • m₁ + s₁ • m₂) (s₁ * s₂) := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk m₁ s₁) + ↑(fromLocalizedModul …
  rw [← map_add, LocalizedModule.mk_add_mk]
  -- 🎉 no goals
#align is_localized_module.mk'_add_mk' IsLocalizedModule.mk'_add_mk'

@[simp]
theorem mk'_zero (s : S) : mk' f 0 s = 0 := by rw [← zero_smul R (0 : M), mk'_smul, zero_smul]
                                               -- 🎉 no goals
#align is_localized_module.mk'_zero IsLocalizedModule.mk'_zero

variable (S)

@[simp]
theorem mk'_one (m : M) : mk' f m (1 : S) = f m := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk m 1) = ↑f m
  rw [fromLocalizedModule_mk, Module.End_algebraMap_isUnit_inv_apply_eq_iff, Submonoid.coe_one,
    one_smul]
#align is_localized_module.mk'_one IsLocalizedModule.mk'_one

variable {S}

@[simp]
theorem mk'_cancel (m : M) (s : S) : mk' f (s • m) s = f m := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk (s • m) s) = ↑f m
  rw [LocalizedModule.mk_cancel, ← mk'_one S f]
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk m 1) = mk' f m 1
  rfl
  -- 🎉 no goals
#align is_localized_module.mk'_cancel IsLocalizedModule.mk'_cancel

@[simp]
theorem mk'_cancel' (m : M) (s : S) : s • mk' f m s = f m := by
  rw [Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]
  -- 🎉 no goals
#align is_localized_module.mk'_cancel' IsLocalizedModule.mk'_cancel'

@[simp]
theorem mk'_cancel_left (m : M) (s₁ s₂ : S) : mk' f (s₁ • m) (s₁ * s₂) = mk' f m s₂ := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk (s₁ • m) (s₁ * s₂)) = ↑(fromL …
  rw [LocalizedModule.mk_cancel_common_left]
  -- 🎉 no goals
#align is_localized_module.mk'_cancel_left IsLocalizedModule.mk'_cancel_left

@[simp]
theorem mk'_cancel_right (m : M) (s₁ s₂ : S) : mk' f (s₂ • m) (s₁ * s₂) = mk' f m s₁ := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk (s₂ • m) (s₁ * s₂)) = ↑(fromL …
  rw [LocalizedModule.mk_cancel_common_right]
  -- 🎉 no goals
#align is_localized_module.mk'_cancel_right IsLocalizedModule.mk'_cancel_right

theorem mk'_add (m₁ m₂ : M) (s : S) : mk' f (m₁ + m₂) s = mk' f m₁ s + mk' f m₂ s := by
  rw [mk'_add_mk', ← smul_add, mk'_cancel_left]
  -- 🎉 no goals
#align is_localized_module.mk'_add IsLocalizedModule.mk'_add

theorem mk'_eq_mk'_iff (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ = mk' f m₂ s₂ ↔ ∃ s : S, s • s₁ • m₂ = s • s₂ • m₁ := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk m₁ s₁) = ↑(fromLocalizedModul …
  rw [(fromLocalizedModule.inj S f).eq_iff, LocalizedModule.mk_eq]
  -- ⊢ (∃ u, u • s₂ • m₁ = u • s₁ • m₂) ↔ ∃ s, s • s₁ • m₂ = s • s₂ • m₁
  simp_rw [eq_comm]
  -- 🎉 no goals
#align is_localized_module.mk'_eq_mk'_iff IsLocalizedModule.mk'_eq_mk'_iff

theorem mk'_neg {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m : M) (s : S) : mk' f (-m) s = -mk' f m s := by
  delta mk'
  -- ⊢ ↑(fromLocalizedModule S f) (LocalizedModule.mk (-m) s) = -↑(fromLocalizedMod …
  rw [LocalizedModule.mk_neg, map_neg]
  -- 🎉 no goals
#align is_localized_module.mk'_neg IsLocalizedModule.mk'_neg

theorem mk'_sub {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s : S) :
    mk' f (m₁ - m₂) s = mk' f m₁ s - mk' f m₂ s := by
  rw [sub_eq_add_neg, sub_eq_add_neg, mk'_add, mk'_neg]
  -- 🎉 no goals
#align is_localized_module.mk'_sub IsLocalizedModule.mk'_sub

theorem mk'_sub_mk' {M M' : Type*} [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M']
    (f : M →ₗ[R] M') [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ - mk' f m₂ s₂ = mk' f (s₂ • m₁ - s₁ • m₂) (s₁ * s₂) := by
  rw [sub_eq_add_neg, ← mk'_neg, mk'_add_mk', smul_neg, ← sub_eq_add_neg]
  -- 🎉 no goals
#align is_localized_module.mk'_sub_mk' IsLocalizedModule.mk'_sub_mk'

theorem mk'_mul_mk'_of_map_mul {M M' : Type*} [Semiring M] [Semiring M'] [Module R M]
    [Algebra R M'] (f : M →ₗ[R] M') (hf : ∀ m₁ m₂, f (m₁ * m₂) = f m₁ * f m₂)
    [IsLocalizedModule S f] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f m₁ s₁ * mk' f m₂ s₂ = mk' f (m₁ * m₂) (s₁ * s₂) := by
  symm
  -- ⊢ mk' f (m₁ * m₂) (s₁ * s₂) = mk' f m₁ s₁ * mk' f m₂ s₂
  apply (Module.End_algebraMap_isUnit_inv_apply_eq_iff _ _ _ _).mpr
  -- ⊢ ↑f (m₁ * m₂, s₁ * s₂).fst = ↑(m₁ * m₂, s₁ * s₂).snd • (mk' f m₁ s₁ * mk' f m …
  simp_rw [Submonoid.coe_mul, ← smul_eq_mul]
  -- ⊢ ↑f (m₁ • m₂) = (↑s₁ • ↑s₂) • mk' f m₁ s₁ • mk' f m₂ s₂
  rw [smul_smul_smul_comm, ← mk'_smul, ← mk'_smul]
  -- ⊢ ↑f (m₁ • m₂) = mk' f (↑s₁ • m₁) s₁ • mk' f (↑s₂ • m₂) s₂
  simp_rw [← Submonoid.smul_def, mk'_cancel, smul_eq_mul, hf]
  -- 🎉 no goals
#align is_localized_module.mk'_mul_mk'_of_map_mul IsLocalizedModule.mk'_mul_mk'_of_map_mul

theorem mk'_mul_mk' {M M' : Type*} [Semiring M] [Semiring M'] [Algebra R M] [Algebra R M']
    (f : M →ₐ[R] M') [IsLocalizedModule S f.toLinearMap] (m₁ m₂ : M) (s₁ s₂ : S) :
    mk' f.toLinearMap m₁ s₁ * mk' f.toLinearMap m₂ s₂ = mk' f.toLinearMap (m₁ * m₂) (s₁ * s₂) :=
  mk'_mul_mk'_of_map_mul f.toLinearMap f.map_mul m₁ m₂ s₁ s₂
#align is_localized_module.mk'_mul_mk' IsLocalizedModule.mk'_mul_mk'

variable {f}

/-- Porting note: simp can prove this
@[simp] -/
theorem mk'_eq_iff {m : M} {s : S} {m' : M'} : mk' f m s = m' ↔ f m = s • m' := by
  rw [← smul_inj f s, Submonoid.smul_def, ← mk'_smul, ← Submonoid.smul_def, mk'_cancel]
  -- 🎉 no goals
#align is_localized_module.mk'_eq_iff IsLocalizedModule.mk'_eq_iff

@[simp]
theorem mk'_eq_zero {m : M} (s : S) : mk' f m s = 0 ↔ f m = 0 := by rw [mk'_eq_iff, smul_zero]
                                                                    -- 🎉 no goals
#align is_localized_module.mk'_eq_zero IsLocalizedModule.mk'_eq_zero

variable (f)

theorem mk'_eq_zero' {m : M} (s : S) : mk' f m s = 0 ↔ ∃ s' : S, s' • m = 0 := by
  simp_rw [← mk'_zero f (1 : S), mk'_eq_mk'_iff, smul_zero, one_smul, eq_comm]
  -- 🎉 no goals
#align is_localized_module.mk'_eq_zero' IsLocalizedModule.mk'_eq_zero'

theorem mk_eq_mk' (s : S) (m : M) :
    LocalizedModule.mk m s = mk' (LocalizedModule.mkLinearMap S M) m s := by
  rw [eq_comm, mk'_eq_iff, Submonoid.smul_def, LocalizedModule.smul'_mk, ← Submonoid.smul_def,
    LocalizedModule.mk_cancel, LocalizedModule.mkLinearMap_apply]
#align is_localized_module.mk_eq_mk' IsLocalizedModule.mk_eq_mk'

variable (S)

theorem eq_zero_iff {m : M} : f m = 0 ↔ ∃ s' : S, s' • m = 0 :=
  (mk'_eq_zero (1 : S)).symm.trans (mk'_eq_zero' f _)
#align is_localized_module.eq_zero_iff IsLocalizedModule.eq_zero_iff

theorem mk'_surjective : Function.Surjective (Function.uncurry <| mk' f : M × S → M') := by
  intro x
  -- ⊢ ∃ a, Function.uncurry (mk' f) a = x
  obtain ⟨⟨m, s⟩, e : s • x = f m⟩ := IsLocalizedModule.surj S f x
  -- ⊢ ∃ a, Function.uncurry (mk' f) a = x
  exact ⟨⟨m, s⟩, mk'_eq_iff.mpr e.symm⟩
  -- 🎉 no goals
#align is_localized_module.mk'_surjective IsLocalizedModule.mk'_surjective

section Algebra

theorem mkOfAlgebra {R S S' : Type*} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S]
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
    -- ⊢ IsUnit (↑(algebraMap R (Module.End R S')) ↑x)
    rw [Module.End_isUnit_iff]
    -- ⊢ Function.Bijective ↑(↑(algebraMap R (Module.End R S')) ↑x)
    constructor
    -- ⊢ Function.Injective ↑(↑(algebraMap R (Module.End R S')) ↑x)
    · rintro a b (e : x • a = x • b)
      -- ⊢ a = b
      simp_rw [Submonoid.smul_def, Algebra.smul_def] at e
      -- ⊢ a = b
      exact (h₁ x x.2).mul_left_cancel e
      -- 🎉 no goals
    · intro a
      -- ⊢ ∃ a_1, ↑(↑(algebraMap R (Module.End R S')) ↑x) a_1 = a
      refine' ⟨((h₁ x x.2).unit⁻¹ : _) * a, _⟩
      -- ⊢ ↑(↑(algebraMap R (Module.End R S')) ↑x) (↑(IsUnit.unit (_ : IsUnit (↑(algebr …
      change (x : R) • (_ * a) = _
      -- ⊢ ↑x • (↑(IsUnit.unit (_ : IsUnit (↑(algebraMap R S') ↑x)))⁻¹ * a) = a
      rw [Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
      -- 🎉 no goals
  · exact h₂
    -- 🎉 no goals
  · intros
    -- ⊢ ↑(AlgHom.toLinearMap f) x₁✝ = ↑(AlgHom.toLinearMap f) x₂✝ ↔ ∃ c, c • x₂✝ = c …
    dsimp only [AlgHom.toLinearMap_apply]
    -- ⊢ ↑f x₁✝ = ↑f x₂✝ ↔ ∃ c, c • x₂✝ = c • x₁✝
    rw [eq_comm, ← sub_eq_zero, ← map_sub, h₃]
    -- ⊢ (∃ m, m • (x₂✝ - x₁✝) = 0) ↔ ∃ c, c • x₂✝ = c • x₁✝
    simp_rw [smul_sub, sub_eq_zero]
    -- 🎉 no goals
#align is_localized_module.mk_of_algebra IsLocalizedModule.mkOfAlgebra

end Algebra

variable {A : Type*}
  [CommRing A] [Algebra R A] [Module A M'] [IsScalarTower R A M'] [IsLocalization S A]


/-- If `(f : M →ₗ[R] M')` is a localization of modules, then the map
`(localization S) × M → N, (s, m) ↦ s • f m` is the tensor product (insomuch as it is the universal
bilinear map).
In particular, there is an isomorphism between `LocalizedModule S M` and `(Localization S) ⊗[R] M`
given by `m/s ↦ (1/s) ⊗ₜ m`.
-/
theorem isBaseChange : IsBaseChange A f := by
  refine' IsBaseChange.of_lift_unique _ (fun Q _ _ _ _ g ↦ _)
  -- ⊢ ∃! g', LinearMap.comp (↑R g') f = g
  have := IsLocalizedModule.is_universal S f g <| by
    intro s
    simp_rw [Module.End_isUnit_iff, Function.bijective_iff_existsUnique,
      Module.algebraMap_end_apply]
    intro q
    refine' ⟨(IsLocalization.mk' _ 1 s : A) • q, _, _⟩
    · simp only [← smul_assoc, IsLocalization.smul_mk'_self, map_one, one_smul]
    · rintro q rfl
      simp only [smul_comm _ (s : R), ← smul_assoc, IsLocalization.smul_mk'_self, map_one, one_smul]
  rcases this with ⟨ℓ, rfl, h₂⟩
  -- ⊢ ∃! g', LinearMap.comp (↑R g') f = LinearMap.comp ℓ f
  refine' ⟨ℓ.extendScalarsOfIsLocalization S A, by simp, fun g'' h ↦ _⟩
  -- ⊢ g'' = LinearMap.extendScalarsOfIsLocalization S A ℓ
  ext x
  -- ⊢ ↑g'' x = ↑(LinearMap.extendScalarsOfIsLocalization S A ℓ) x
  simp [← h₂ (LinearMap.restrictScalars R g'') h]
  -- 🎉 no goals

end IsLocalizedModule

end IsLocalizedModule
