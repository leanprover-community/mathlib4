/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.OreLocalization.Ring

#align_import algebra.module.localized_module from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Localized Module

Given a commutative semiring `R`, a multiplicative subset `S ⊆ R` and an `R`-module `M`, we can
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

## Implementation Detail

`LocalizedModule M S` is by definition `OreLocalization M S`. `LocalizedModule.mk` is planned to be
replaced by `oreDiv` in the future.


-/

namespace LocalizedModule

universe u v

variable {R : Type u} [CommSemiring R] (S : Submonoid R)
variable (M : Type v) [AddCommMonoid M] [Module R M]
variable (T : Type*) [CommSemiring T] [Algebra R T] [IsLocalization S T]

/-- The equivalence relation on `M × S` where `(m1, s1) ≈ (m2, s2)` if and only if
for some (u : S), u * (s2 • m1 - s1 • m2) = 0-/
/- Porting note: We use small letter `r` since `R` is used for a ring. -/
def r (a b : M × S) : Prop :=
  ∃ u : S, u • b.2 • a.1 = u • a.2 • b.1
#align localized_module.r LocalizedModule.r

lemma oreEqv_iff_r : (OreLocalization.oreEqv S M).r = r S M := by
  ext a b
  constructor
  · rintro ⟨u, v, h₁, h₂⟩
    use u
    simp only [Submonoid.smul_def, smul_smul, h₂]
    rw [mul_comm, mul_smul, ← h₁, mul_comm, mul_smul]
    rfl
  · rintro ⟨u, hu⟩
    use u * a.2, u * b.2
    rw [mul_smul, ← hu, mul_smul, Submonoid.coe_mul, mul_assoc, mul_assoc, mul_comm (a.2 : R)]
    exact ⟨rfl, rfl⟩

theorem r.isEquiv : IsEquiv _ (r S M) :=
  { refl := fun ⟨m, s⟩ => ⟨1, by rw [one_smul]⟩
    trans := fun ⟨m1, s1⟩ ⟨m2, s2⟩ ⟨m3, s3⟩ ⟨u1, hu1⟩ ⟨u2, hu2⟩ => by
      use u1 * u2 * s2
      -- Put everything in the same shape, sorting the terms using `simp`
      have hu1' := congr_arg ((u2 * s3) • ·) hu1.symm
      have hu2' := congr_arg ((u1 * s1) • ·) hu2.symm
      simp only [← mul_smul, smul_assoc, mul_assoc, mul_comm, mul_left_comm] at hu1' hu2' ⊢
      rw [hu2', hu1']
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
-- Porting note(#5171): @[nolint has_nonempty_instance]
abbrev _root_.LocalizedModule : Type max u v :=
  OreLocalization S M
#align localized_module LocalizedModule

section

variable {M S}

/-- The canonical map sending `(m, s) ↦ m/s`-/
def mk (m : M) (s : S) : LocalizedModule S M := m /ₒ s
#align localized_module.mk LocalizedModule.mk

theorem mk_eq {m m' : M} {s s' : S} : mk m s = mk m' s' ↔ ∃ u : S, u • s' • m = u • s • m' := by
  rw [mk, mk, OreLocalization.oreDiv_eq_iff]
  show _ ↔ r S M (m, s) (m', s')
  rw [← oreEqv_iff_r]
  rfl
#align localized_module.mk_eq LocalizedModule.mk_eq

@[elab_as_elim]
theorem induction_on {β : LocalizedModule S M → Prop} (h : ∀ (m : M) (s : S), β (mk m s)) :
    ∀ x : LocalizedModule S M, β x := by
  rintro ⟨⟨m, s⟩⟩
  exact h m s
#align localized_module.induction_on LocalizedModule.induction_on

@[elab_as_elim]
theorem induction_on₂ {β : LocalizedModule S M → LocalizedModule S M → Prop}
    (h : ∀ (m m' : M) (s s' : S), β (mk m s) (mk m' s')) : ∀ x y, β x y := by
  rintro ⟨⟨m, s⟩⟩ ⟨⟨m', s'⟩⟩
  exact h m m' s s'
#align localized_module.induction_on₂ LocalizedModule.induction_on₂

/-- If `f : M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → α`.
-/
def liftOn {α : Type*} (x : LocalizedModule S M) (f : M × S → α)
    (wd : ∀ (p p' : M × S), r S M p p' → f p = f p') : α :=
  Quotient.liftOn x f (by simpa only [← oreEqv_iff_r S M] using wd)
#align localized_module.lift_on LocalizedModule.liftOn

theorem liftOn_mk {α : Type*} {f : M × S → α} (wd : ∀ (p p' : M × S), p ≈ p' → f p = f p')
    (m : M) (s : S) : liftOn (mk m s) f wd = f ⟨m, s⟩ := by convert Quotient.liftOn_mk f wd ⟨m, s⟩
#align localized_module.lift_on_mk LocalizedModule.liftOn_mk

/-- If `f : M × S → M × S → α` respects the equivalence relation `LocalizedModule.r`, then
`f` descents to a map `LocalizedModule M S → LocalizedModule M S → α`.
-/
def liftOn₂ {α : Type*} (x y : LocalizedModule S M) (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), r S M p p' → r S M q q' → f p q = f p' q') : α :=
  Quotient.liftOn₂ x y f (by simpa only [← oreEqv_iff_r S M] using wd)
#align localized_module.lift_on₂ LocalizedModule.liftOn₂

theorem liftOn₂_mk {α : Type*} (f : M × S → M × S → α)
    (wd : ∀ (p q p' q' : M × S), p ≈ p' → q ≈ q' → f p q = f p' q') (m m' : M)
    (s s' : S) : liftOn₂ (mk m s) (mk m' s') f wd = f ⟨m, s⟩ ⟨m', s'⟩ := by
  convert Quotient.liftOn₂_mk f wd _ _
#align localized_module.lift_on₂_mk LocalizedModule.liftOn₂_mk

/-- If `S` contains `0` then the localization at `S` is trivial. -/
theorem subsingleton (h : 0 ∈ S) : Subsingleton (LocalizedModule S M) := by
  refine ⟨fun a b ↦ ?_⟩
  induction a,b using LocalizedModule.induction_on₂
  exact mk_eq.mpr ⟨⟨0, h⟩, by simp only [Submonoid.mk_smul, zero_smul]⟩

@[simp]
theorem zero_mk (s : S) : mk (0 : M) s = 0 :=
  OreLocalization.zero_oreDiv _
#align localized_module.zero_mk LocalizedModule.zero_mk

theorem mk_add_mk' {m1 m2 : M} {s1 s2 : S} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s2 * s1) := by with_unfolding_all rfl

theorem mk_add_mk {m1 m2 : M} {s1 s2 : S} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) := by rw [mk_add_mk', mul_comm]
#align localized_module.mk_add_mk LocalizedModule.mk_add_mk

theorem mk_neg {M : Type*} [AddCommGroup M] [Module R M] {m : M} {s : S} : mk (-m) s = -mk m s := by
  with_unfolding_all rfl
#align localized_module.mk_neg LocalizedModule.mk_neg

/--
The multiplication on the localized module. Note that this gives a diamond with the instance on
`R[S⁻¹]` (which does not require commutativity), but is defeq to it under `with_unfolding_all`.
-/
protected def mul {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R}
    (m₁ m₂ : LocalizedModule S A) : LocalizedModule S A :=
  liftOn₂ m₁ m₂ (fun x₁ x₂ => LocalizedModule.mk (x₁.1 * x₂.1) (x₂.2 * x₁.2)) (by
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ ⟨u₁, e₁⟩ ⟨u₂, e₂⟩
    simp only [mul_comm s₂ s₁, mul_comm t₂ t₁]
    rw [mk_eq]
    use u₁ * u₂
    dsimp only at e₁ e₂ ⊢
    rw [eq_comm]
    trans (u₁ • t₁ • a₁) • u₂ • t₂ • a₂
    on_goal 1 => rw [e₁, e₂]
    on_goal 2 => rw [eq_comm]
    all_goals
      rw [smul_smul, mul_mul_mul_comm, ← smul_eq_mul, ← smul_eq_mul A, smul_smul_smul_comm,
        mul_smul, mul_smul])

instance {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Monoid (LocalizedModule S A) where
  __ := inferInstanceAs (One (LocalizedModule S A))
  mul := LocalizedModule.mul
  one_mul := by
    rintro ⟨a, s⟩
    with_unfolding_all exact mk_eq.mpr ⟨1, by simp only [one_mul, mul_one, one_smul]⟩
  mul_one := by
    rintro ⟨a, s⟩
    with_unfolding_all exact mk_eq.mpr ⟨1, by simp only [mul_one, one_smul, one_mul]⟩
  mul_assoc := by with_unfolding_all
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
    apply mk_eq.mpr _
    use 1
    simp only [one_mul, smul_smul, ← mul_assoc, mul_right_comm]

example : OreLocalization.instMonoid = LocalizedModule.instMonoid (A := R) (S := S) := rfl

theorem mk_mul_mk' {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₂ * s₁) := by
  with_unfolding_all rfl

theorem mk_mul_mk {A : Type*} [Semiring A] [Algebra R A] {a₁ a₂ : A} {s₁ s₂ : S} :
    mk a₁ s₁ * mk a₂ s₂ = mk (a₁ * a₂) (s₁ * s₂) := by rw [mk_mul_mk', mul_comm s₁ s₂]
#align localized_module.mk_mul_mk LocalizedModule.mk_mul_mk

instance {A : Type*} [Semiring A] [Algebra R A] {S : Submonoid R} :
    Semiring (LocalizedModule S A) where
  __ := inferInstanceAs (AddCommMonoid (LocalizedModule S A))
  __ := inferInstanceAs (Monoid (LocalizedModule S A))
  left_distrib := by
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
    show a₁ /ₒ s₁ * (a₂ /ₒ s₂ + a₃ /ₒ s₃) = a₁ /ₒ s₁ * (a₂ /ₒ s₂) + a₁ /ₒ s₁ * (a₃ /ₒ s₃)
    rw [← mk, ← mk, ← mk, mk_mul_mk, mk_mul_mk, mk_add_mk, mk_mul_mk, mk_add_mk]
    apply mk_eq.mpr _
    use 1
    simp only [← mul_assoc, mul_right_comm, mul_add, mul_smul_comm, smul_add, smul_smul, one_mul]
  right_distrib := by
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩ ⟨a₃, s₃⟩
    show (a₁ /ₒ s₁ + a₂ /ₒ s₂) * (a₃ /ₒ s₃) = a₁ /ₒ s₁ * (a₃ /ₒ s₃) + a₂ /ₒ s₂ * (a₃ /ₒ s₃)
    rw [← mk, ← mk, ← mk, mk_mul_mk, mk_mul_mk, mk_add_mk, mk_mul_mk, mk_add_mk]
    apply mk_eq.mpr _
    use 1
    simp only [one_mul, smul_add, add_mul, smul_smul, ← mul_assoc, smul_mul_assoc,
      mul_right_comm]
  zero_mul := by with_unfolding_all
    rintro ⟨a, s⟩
    exact mk_eq.mpr ⟨1, by simp only [zero_mul, smul_zero]⟩
  mul_zero := by with_unfolding_all
    rintro ⟨a, s⟩
    exact mk_eq.mpr ⟨1, by simp only [mul_zero, smul_zero]⟩

instance {A : Type*} [CommSemiring A] [Algebra R A] {S : Submonoid R} :
    CommSemiring (LocalizedModule S A) where
  __ := inferInstanceAs (Semiring (LocalizedModule S A))
  mul_comm := by with_unfolding_all
    rintro ⟨a₁, s₁⟩ ⟨a₂, s₂⟩
    exact mk_eq.mpr ⟨1, by simp only [one_smul, mul_comm]⟩

instance {A : Type*} [Ring A] [Algebra R A] {S : Submonoid R} :
    Ring (LocalizedModule S A) where
  __ := inferInstanceAs (AddCommGroup (LocalizedModule S A))
  __ := inferInstanceAs (Semiring (LocalizedModule S A))

instance {A : Type*} [CommRing A] [Algebra R A] {S : Submonoid R} :
    CommRing (LocalizedModule S A) where
  __ := inferInstanceAs (Ring (LocalizedModule S A))
  __ := inferInstanceAs (CommSemiring (LocalizedModule S A))

theorem mk_smul_mk (r : R) (m : M) (s t : S) :
    Localization.mk r s • mk m t = mk (r • m) (s * t) :=
  (OreLocalization.oreDiv_smul_char _ _ _ _ _ _ (mul_comm _ _)).trans (by rw [mul_comm]; rfl)
#align localized_module.mk_smul_mk LocalizedModule.mk_smul_mk

@[simp]
theorem mk_cancel_common_left (s' s : S) (m : M) : mk (s' • m) (s' * s) = mk m s :=
  mk_eq.mpr
    ⟨1, by
      simp only [mul_smul, one_smul]
      rw [smul_comm]⟩
#align localized_module.mk_cancel_common_left LocalizedModule.mk_cancel_common_left

@[simp]
theorem mk_cancel (s : S) (m : M) : mk (s • m) s = mk m 1 :=
  mk_eq.mpr ⟨1, by simp⟩
#align localized_module.mk_cancel LocalizedModule.mk_cancel

@[simp]
theorem mk_cancel_common_right (s s' : S) (m : M) : mk (s' • m) (s * s') = mk m s :=
  mk_eq.mpr ⟨1, by simp [mul_smul]⟩
#align localized_module.mk_cancel_common_right LocalizedModule.mk_cancel_common_right

variable {R₀} [SMul R₀ R] [IsScalarTower R₀ R R] [SMul R₀ M] [IsScalarTower R₀ R M]

theorem smul'_mk (r : R₀) (s : S) (m : M) : r • mk m s = mk (r • m) s := by
  refine (OreLocalization.smul_oreDiv _ _ _).trans ?_
  show (r • 1 : R) • m /ₒ s = _
  rw [smul_assoc, one_smul]
  rfl
#align localized_module.smul'_mk LocalizedModule.smul'_mk

theorem smul'_mul {A : Type*} [Semiring A] [Algebra R A]
    [SMul R₀ A] [IsScalarTower R₀ R A] [IsScalarTower R₀ A A]
    (x : R₀) (p₁ p₂ : LocalizedModule S A) :
    x • p₁ * p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [mk_mul_mk, smul'_mk, mk_mul_mk, smul'_mk, smul_mul_assoc]

theorem mul_smul' {A : Type*} [Semiring A] [Algebra R A]
    [SMul R₀ A] [IsScalarTower R₀ R A] [SMulCommClass R₀ A A]
    (x : R₀) (p₁ p₂ : LocalizedModule S A) :
    p₁ * x • p₂ = x • (p₁ * p₂) := by
  induction p₁, p₂ using induction_on₂ with | _ a₁ s₁ a₂ s₂ => _
  rw [smul'_mk, mk_mul_mk, mk_mul_mk, smul'_mk, mul_smul_comm]

instance {R₀ A : Type*} [CommSemiring R₀] [Algebra R₀ R] [Semiring A] [Algebra R A]
    [Algebra R₀ A] [IsScalarTower R₀ R A] : Algebra R₀ (LocalizedModule S A) :=
  Algebra.ofModule smul'_mul mul_smul'

section

variable (S M)

/-- The function `m ↦ m / 1` as an `R`-linear map. -/
def mkLinearMap : M →ₗ[R] LocalizedModule S M := OreLocalization.mkLinearMap S M

@[simp]
lemma mkLinearMap_apply (x) : mkLinearMap S M x = .mk x 1 := rfl

end

/-- For any `s : S`, there is an `R`-linear map given by `a/b ↦ a/(b*s)`.
-/
@[simps]
def divBy (s : S) : LocalizedModule S M →ₗ[R] LocalizedModule S M where
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
    dsimp only
    rw [smul'_mk]
    change liftOn (mk _ _) _ _ = r • (liftOn (mk _ _) _ _)
    simp_rw [liftOn_mk, smul'_mk]
#align localized_module.div_by LocalizedModule.divBy

theorem divBy_mul_by (s : S) (p : LocalizedModule S M) :
    divBy s (algebraMap R (Module.End R (LocalizedModule S M)) s p) = p :=
  p.induction_on fun m t => by
    rw [Module.algebraMap_end_apply, divBy_apply, smul'_mk]
    rw [LocalizedModule.liftOn_mk]
    exact mk_cancel_common_right _ _ _
#align localized_module.div_by_mul_by LocalizedModule.divBy_mul_by

theorem mul_by_divBy (s : S) (p : LocalizedModule S M) :
    algebraMap R (Module.End R (LocalizedModule S M)) s (divBy s p) = p :=
  p.induction_on fun m t => by
    rw [divBy_apply, Module.algebraMap_end_apply, LocalizedModule.liftOn_mk, smul'_mk,
      ← Submonoid.smul_def, mk_cancel_common_right _ s]
#align localized_module.mul_by_div_by LocalizedModule.mul_by_divBy

end

end LocalizedModule

namespace LocalizedModule

universe u v

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M M' M'' : Type*} [AddCommMonoid M] [AddCommMonoid M'] [AddCommMonoid M'']
variable {A : Type*} [CommSemiring A] [Algebra R A] [Module A M'] [IsLocalization S A]
variable [Module R M] [Module R M'] [Module R M''] [IsScalarTower R A M']
variable (f : M →ₗ[R] M') (g : M →ₗ[R] M'')


/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible, then
there is a linear map `LocalizedModule S M → M''`.
-/
noncomputable def lift' (g : M →ₗ[R] M'')
    (h : ∀ x : S, IsUnit (algebraMap R (Module.End R M'') x)) : LocalizedModule S M → M'' :=
  fun m =>
  m.liftOn (fun p => (h p.2).unit⁻¹.val <| g p.1) fun ⟨m, s⟩ ⟨m', s'⟩ ⟨c, eq1⟩ => by
    -- Porting note: We remove `generalize_proofs h1 h2`. This does nothing here.
    dsimp only
    simp only [Submonoid.smul_def] at eq1
    rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← map_smul, eq_comm,
      Module.End_algebraMap_isUnit_inv_apply_eq_iff]
    have : c • s • g m' = c • s' • g m := by
      simp only [Submonoid.smul_def, ← g.map_smul, eq1]
    have : Function.Injective (h c).unit.inv := by
      rw [Function.injective_iff_hasLeftInverse]
      refine ⟨(h c).unit, ?_⟩
      intro x
      change ((h c).unit.1 * (h c).unit.inv) x = x
      simp only [Units.inv_eq_val_inv, IsUnit.mul_val_inv, LinearMap.one_apply]
    apply_fun (h c).unit.inv
    erw [Units.inv_eq_val_inv, Module.End_algebraMap_isUnit_inv_apply_eq_iff, ←
      (h c).unit⁻¹.val.map_smul]
    symm
    rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← g.map_smul, ← g.map_smul, ← g.map_smul, ←
      g.map_smul, eq1]
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
      rw [mk_add_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk, LocalizedModule.lift'_mk]
      -- Porting note: We remove `generalize_proofs h1 h2 h3`. This only generalize `h1`.
      erw [map_add, Module.End_algebraMap_isUnit_inv_apply_eq_iff, smul_add, ← map_smul,
        ← map_smul, ← map_smul]
      congr 1 <;> symm
      · erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, mul_smul, ← map_smul]
        rfl
      · dsimp
        erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, mul_comm, mul_smul, ← map_smul]
        rfl)
    x y
#align localized_module.lift'_add LocalizedModule.lift'_add

theorem lift'_smul (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (r : R) (m) : r • LocalizedModule.lift' S g h m = LocalizedModule.lift' S g h (r • m) :=
  m.induction_on fun a b => by
    rw [LocalizedModule.lift'_mk, LocalizedModule.smul'_mk, LocalizedModule.lift'_mk]
    -- Porting note: We remove `generalize_proofs h1 h2`. This does nothing here.
    rw [← map_smul, ← g.map_smul]
#align localized_module.lift'_smul LocalizedModule.lift'_smul

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
there is a linear map `lift g ∘ mkLinearMap = g`.
-/
theorem lift_comp (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x)) :
    (lift S g h).comp (mkLinearMap S M) = g := by
  ext x; dsimp; rw [LocalizedModule.lift_mk]
  erw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, one_smul]
#align localized_module.lift_comp LocalizedModule.lift_comp

/--
If `g` is a linear map `M → M''` such that all scalar multiplication by `s : S` is invertible and
`l` is another linear map `LocalizedModule S M ⟶ M''` such that `l ∘ mkLinearMap = g` then
`l = lift g`
-/
theorem lift_unique (g : M →ₗ[R] M'') (h : ∀ x : S, IsUnit ((algebraMap R (Module.End R M'')) x))
    (l : LocalizedModule S M →ₗ[R] M'') (hl : l.comp (LocalizedModule.mkLinearMap S M) = g) :
    LocalizedModule.lift S g h = l := by
  ext x; induction' x using LocalizedModule.induction_on with m s
  rw [LocalizedModule.lift_mk]
  rw [Module.End_algebraMap_isUnit_inv_apply_eq_iff, ← hl, LinearMap.coe_comp,
    Function.comp_apply, LocalizedModule.mkLinearMap_apply, ← l.map_smul, LocalizedModule.smul'_mk]
  congr 1; rw [LocalizedModule.mk_eq]
  refine' ⟨1, _⟩; simp only [one_smul, Submonoid.smul_def]
#align localized_module.lift_unique LocalizedModule.lift_unique

end LocalizedModule
