/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import Mathlib.Topology.UniformSpace.Completion
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Ring topologised by a valuation

For a given valuation `v : Valuation R Γ₀` on a ring `R` taking values in `Γ₀`, this file
defines the type synonym `WithVal v` of `R`. By assigning a `Valued (WithVal v) Γ₀` instance,
`WithVal v` represents the ring `R` equipped with the topology coming from `v`. The type
synonym `WithVal v` is in isomorphism to `R` as rings via `WithVal.equiv v`. This
isomorphism should be used to explicitly map terms of `WithVal v` to terms of `R`.

The `WithVal` type synonym is used to define the completion of `R` with respect to `v` in
`Valuation.Completion`. An example application of this is
`IsDedekindDomain.HeightOneSpectrum.adicCompletion`, which is the completion of the field of
fractions of a Dedekind domain with respect to a height-one prime ideal of the domain.

## Main definitions
- `WithVal` : type synonym for a ring equipped with the topology coming from a valuation.
- `WithVal.equiv` : the canonical ring equivalence between `WithValuation v` and `R`.
- `Valuation.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified valuation.
-/

@[expose] public section

noncomputable section

variable {R Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Type synonym for a ring equipped with the topology coming from a valuation. -/
structure WithVal [Ring R] (v : Valuation R Γ₀) where
  /-- Converts an element of `R` to an element of `WithVal v`. -/
  toVal (v) ::
  /-- Converts an element of `WithVal v` to an element of `R`. -/
  ofVal : R

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toVal v x` being printed as `{ ofAbs := x }` by `delabStructureInstance`. -/
@[app_delab WithVal.toVal]
meta def WithVal.delabToVal : Delab := delabApp

end Notation

namespace WithVal

section Ring

variable [Ring R] (v : Valuation R Γ₀)

instance : Ring (WithVal v) := Equiv.ring {toFun := ofVal, invFun := toVal v}
instance : Inhabited (WithVal v) := ⟨0⟩
instance : Preorder (WithVal v) := letI := v.toPreorder; .lift ofVal

lemma ofVal_toVal (x : R) : ofVal (toVal v x) = x := rfl
@[simp] lemma toVal_ofVal (x : WithVal v) : toVal v (ofVal x) = x := rfl

lemma ofVal_surjective : Function.Surjective (ofVal (v := v)) :=
  Function.RightInverse.surjective <| ofVal_toVal _

lemma toVal_surjective : Function.Surjective (toVal v) :=
  Function.RightInverse.surjective <| toVal_ofVal _

lemma ofVal_injective : Function.Injective (ofVal (v := v)) :=
  Function.LeftInverse.injective <| toVal_ofVal _

lemma toVal_injective : Function.Injective (toVal v) :=
  Function.LeftInverse.injective <| ofVal_toVal _

lemma ofVal_bijective : Function.Bijective (ofVal (v := v)) :=
  ⟨ofVal_injective v, ofVal_surjective v⟩

lemma toVal_bijective : Function.Bijective (toVal v) :=
  ⟨toVal_injective v, toVal_surjective v⟩

@[simp] lemma toVal_zero : toVal v 0 = 0 := rfl
@[simp] lemma ofVal_zero : ofVal (0 : WithVal v) = 0 := rfl

@[simp] lemma toVal_one : toVal v 1 = 1 := rfl
@[simp] lemma ofVal_one : ofVal (1 : WithVal v) = 1 := rfl

@[simp] lemma toVal_add (x y : R) : toVal v (x + y) = toVal v x + toVal v y := rfl
@[simp] lemma ofVal_add (x y : WithVal v) : ofVal (x + y) = ofVal x + ofVal y := rfl

@[simp] lemma toVal_sub (x y : R) : toVal v (x - y) = toVal v x - toVal v y := rfl
@[simp] lemma ofVal_sub (x y : WithVal v) : ofVal (x - y) = ofVal x - ofVal y := rfl

@[simp] lemma toVal_mul (x y : R) : toVal v (x * y) = toVal v x * toVal v y := rfl
@[simp] lemma ofVal_mul (x y : WithVal v) : ofVal (x * y) = ofVal x * ofVal y := rfl

@[simp] lemma toVal_neg (x : R) : toVal v (-x) = -toVal v x := rfl
@[simp] lemma ofVal_neg (x : WithVal v) : ofVal (-x) = -ofVal x := rfl

@[simp] lemma toVal_pow (x : R) (n : ℕ) : toVal v (x ^ n) = (toVal v x) ^ n := rfl
@[simp] lemma ofVal_pow (x : WithVal v) (n : ℕ) : ofVal (x ^ n) = (ofVal x) ^ n := rfl

@[simp] lemma toVal_eq_zero (x : R) : toVal v x = 0 ↔ x = 0 := (toVal_injective v).eq_iff
@[simp] lemma ofVal_eq_zero (x : WithVal v) : ofVal x = 0 ↔ x = 0 := (ofVal_injective v).eq_iff

theorem le_def {v : Valuation R Γ₀} {a b : WithVal v} : a ≤ b ↔ v a.ofVal ≤ v b.ofVal := .rfl
theorem lt_def {v : Valuation R Γ₀} {a b : WithVal v} : a < b ↔ v a.ofVal < v b.ofVal := .rfl

/-- The canonical ring equivalence between `WithVal v` and `R`. -/
@[simps apply symm_apply]
def equiv : WithVal v ≃+* R where
  toFun := ofVal
  invFun := toVal v
  map_add' := ofVal_add v
  map_mul' := ofVal_mul v

variable {S : Type*} [Ring S] {Λ₀ : Type*} [LinearOrderedCommGroupWithZero Λ₀] (w : Valuation S Λ₀)

/-- Lift a ring hom to `WithVal`. -/
def map (f : R →+* S) : WithVal v →+* WithVal w := (equiv w).symm.toRingHom.comp (f.comp (equiv v))

@[simp] theorem map_id : map v v (.id R) = .id (WithVal v) := rfl
@[simp] theorem map_comp {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : S →+* T) (g : R →+* S) :
    map v u (f.comp g) = (map w u f).comp (map v w g) := rfl
@[simp] theorem map_apply (f : R →+* S) (x : WithVal v) : map v w f x = toVal w (f x.ofVal) := rfl

/-- Lft a `RingEquiv` to `WithVal`. -/
def congr (f : R ≃+* S) : WithVal v ≃+* WithVal w where
  __ := map v w f.toRingHom
  invFun := map w v f.symm.toRingHom
  left_inv _ := by simp
  right_inv _ := by simp

@[simp] theorem congr_refl : congr v v (.refl R) = .refl (WithVal v) := rfl
theorem congr_symm (f : R ≃+* S) : (congr v w f).symm = congr w v f.symm := rfl
theorem congr_trans {T : Type*} [Ring T] (u : Valuation T Γ₀) (f : R ≃+* S) (g : S ≃+* T) :
    congr v u (f.trans g) = (congr v w f).trans (congr w u g) := rfl
@[simp] theorem congr_apply (f : R ≃+* S) (x : WithVal v) :
    congr v w f x = toVal w (f x.ofVal) := rfl
@[simp] theorem congr_symm_apply (f : R ≃+* S) (x : WithVal w) :
    (congr v w f).symm x = toVal v (f.symm x.ofVal) := rfl

/-- Canonical valuation on the `WithVal v` type synonym. -/
def valuation : Valuation (WithVal v) Γ₀ := v.comap (equiv v)

@[simp] lemma valuation_equiv_symm (x : R) : valuation v (toVal v x) = v x := rfl

instance : Valued (WithVal v) Γ₀ := Valued.mk' (valuation v)

theorem apply_equiv (r : WithVal v) : v r.ofVal = Valued.v r := rfl
@[simp] theorem apply_symm_equiv (r : R) : Valued.v (toVal v r) = v r := rfl

instance [CharZero R] : CharZero (WithVal v) :=
  .of_addMonoidHom (equiv v).symm.toAddMonoidHom (by simp) (equiv v).symm.injective

end Ring

section CommRing

variable [CommRing R] (v : Valuation R Γ₀)

instance : CommRing (WithVal v) := fast_instance% (equiv v).commRing
instance : ValuativeRel (WithVal v) := .ofValuation (valuation v)
instance : (valuation v).Compatible := .ofValuation (valuation v)

end CommRing

section Module

variable [Ring R] (v : Valuation R Γ₀) {S : Type*}

instance instSMulLeft [SMul R S] : SMul (WithVal v) S where
  smul x s := ofVal x • s

theorem smul_left_def [SMul R S] (x : WithVal v) (s : S) : x • s = ofVal x • s := rfl

instance [SMul R S] [FaithfulSMul R S] : FaithfulSMul (WithVal v) S where
  eq_of_smul_eq_smul h := ofVal_injective v <| FaithfulSMul.eq_of_smul_eq_smul h

instance instSMulRight [SMul S R] : SMul S (WithVal v) := (equiv v).smul S

theorem smul_right_def [SMul S R] (s : S) (x : WithVal v) : s • x = toVal v (s • ofVal x) := rfl

instance [SMul S R] [FaithfulSMul S R] : FaithfulSMul S (WithVal v) where
  eq_of_smul_eq_smul h := by
    simp only [smul_right_def, toVal.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun r ↦ h (toVal v r)

instance instIsScalarTowerLeft {P : Type*} [Ring R] [SMul S P] [SMul R S] [SMul R P]
    [IsScalarTower R S P] (v : Valuation R Γ₀) : IsScalarTower (WithVal v) S P where
  smul_assoc := by simp [smul_left_def]

instance instIsScalarTowerRight {P : Type*} [Ring S] [SMul P S] [SMul R S] [SMul P R]
    [IsScalarTower P R S] (v : Valuation S Γ₀) : IsScalarTower P R (WithVal v) :=
  (equiv v).isScalarTower P R

instance instIsScalarTower {P : Type*} [Ring S] [SMul P R] [SMul S R] [SMul P S]
    [IsScalarTower P S R] (v : Valuation S Γ₀) : IsScalarTower P (WithVal v) R where
  smul_assoc := by simp [smul_right_def, smul_left_def]

instance instModuleLeft [AddCommMonoid S] [Module R S] : Module (WithVal v) S :=
  .compHom S (equiv v).toRingHom

instance instFiniteLeft [AddCommMonoid S] [Module R S] [Module.Finite R S] :
    Module.Finite (WithVal v) S := .of_restrictScalars_finite R (WithVal v) S

instance instModuleRight [Semiring S] [Module S R] : Module S (WithVal v) :=
  fast_instance% (equiv v).module S

@[simp] theorem toVal_smul [SMul S R] (s : S) (r : R) : toVal v (s • r) = s • toVal v r := rfl
@[simp] theorem ofVal_smul [SMul S R] (s : S) (x : WithVal v) : ofVal (s • x) = s • ofVal x := rfl

variable [Ring S] [Module R S] (v : Valuation S Γ₀)

variable (R) in
/-- The canonical `R`-linear isomorphism between `WithVal v` and `S`, when `v : Valuation S Γ₀`. -/
def linearEquiv : WithVal v ≃ₗ[R] S := (equiv v).linearEquiv R

@[simp] theorem linearEquiv_apply (x : WithVal v) : linearEquiv R v x = x.ofVal := rfl
@[simp] theorem linearEquiv_symm_apply (x : S) : (linearEquiv R v).symm x = toVal v x := rfl

instance instFiniteRight [Module R S] [Module.Finite R S] :
    Module.Finite R (WithVal v) := .equiv (linearEquiv R v).symm

end Module

section Algebra

variable {S : Type*}

section left

variable [CommRing R] (v : Valuation R Γ₀) [Semiring S] [Algebra R S]

instance instAlgebraLeft : Algebra (WithVal v) S := .compHom S (equiv v).toRingHom

theorem algebraMap_left_apply (s : WithVal v) :
    algebraMap (WithVal v) S s = algebraMap R S s.ofVal := rfl

instance {S : Type*} [CommSemiring S] [Algebra R S] [i : IsFractionRing R S] :
    IsFractionRing (WithVal v) S := .of_equiv_left (equiv v) (fun _ ↦ rfl)

theorem algebraMap_left_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap (WithVal v) S) := h.comp (ofVal_injective v)

end left

section right

variable [CommSemiring R] [Ring S] [Algebra R S] (v : Valuation S Γ₀)

instance instAlgebraRight : Algebra R (WithVal v) := (equiv v).algebra R

theorem algebraMap_right_apply (r : R) :
    algebraMap R (WithVal v) r = toVal v (algebraMap R S r) := rfl

theorem algebraMap_right_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap R (WithVal v)) := (toVal_injective v).comp h

variable {R : Type*} [CommRing R] (v : Valuation R Γ₀) (w : Valuation S Γ₀) [Algebra R S]

end right

variable [CommSemiring R] [Ring S] [Algebra R S] (v : Valuation S Γ₀)

variable (R) in
/-- The canonical `R`-algeba isomorphism between `WithVal v` and `S`, when `v : Valuation S Γ₀`. -/
def algEquiv : WithVal v ≃ₐ[R] S := (equiv v).algEquiv R

@[simp] theorem algEquiv_apply (x : WithVal v) : algEquiv R v x = x.ofVal := rfl
@[simp] theorem algEquiv_symm_apply (x : S) : (algEquiv R v).symm x = toVal v x := rfl

instance {S : Type*} [CommRing S] [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (v : Valuation S Γ₀) : IsLocalization M (WithVal v) := by
  rwa [← IsLocalization.isLocalization_iff_of_algEquiv M (algEquiv R v).symm]

end Algebra

section Field

variable [Field R] (v : Valuation R Γ₀)

instance : Field (WithVal v) := fast_instance% (equiv v).field
instance [NumberField R] : NumberField (WithVal v) where

@[simp] lemma toVal_div (x y : R) : toVal v (x / y) = toVal v x / toVal v y := rfl
@[simp] lemma ofVal_div (x y : WithVal v) : ofVal (x / y) = ofVal x / ofVal y := rfl

@[simp] lemma toVal_inv (x : R) : toVal v x⁻¹ = (toVal v x)⁻¹ := rfl
@[simp] lemma ofVal_inv (x : WithVal v) : ofVal (x⁻¹) = (ofVal x)⁻¹ := rfl

end Field

section Ring

variable [Ring R] (v : Valuation R Γ₀)

variable {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]

/-- Canonical ring equivalence between `WithVal v` and `WithVal w`. -/
@[deprecated "Use `WithVal.congr v w (.refl R)` instead" (since := "2026-01-27")]
def equivWithVal (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    WithVal v ≃+* WithVal w :=
  (equiv v).trans (equiv w).symm

@[deprecated WithVal.congr_symm (since := "2026-01-27")]
theorem equivWithVal_symm (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    (congr v w (.refl R)).symm = congr w v (.refl R) := rfl

@[deprecated "Use `WithVal.congr_apply` instead" (since := "2026-01-27")]
theorem equivWithVal_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal v} :
    congr v w (.refl R) x = (equiv w).symm (equiv v x) := by simp

@[deprecated "Use `WithVal.congr_symm_apply` instead" (since := "2026-01-27")]
theorem equivWithVal_symm_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal w} :
    (congr v w (.refl R)).symm x = (equiv v).symm (equiv w x) := by simp

end Ring

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- The completion of a field with respect to a valuation. -/
abbrev Completion := UniformSpace.Completion (WithVal v)

-- lower priority so that `Coe (WithVal v) v.Completion` uses `UniformSpace.Completion.instCoe`
instance (priority := 99) : Coe R v.Completion where
  coe r := (WithVal.equiv v).symm r

section Equivalence

/-! The uniform isomorphism between `WithVal v` and `WithVal w` when `v` and `w` are
equivalent. -/

variable {R Γ₀ Γ₀' : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'}

/-- If two valuations `v` and `w` are equivalent then `WithVal v` is order-isomorphic
to `WithVal w`. -/
def IsEquiv.orderRingIso (h : v.IsEquiv w) :
    WithVal v ≃+*o WithVal w where
  __ := WithVal.congr v w (.refl R)
  map_le_map_iff' := h.symm ..

@[simp]
theorem IsEquiv.orderRingIso_apply (h : v.IsEquiv w) (x : WithVal v) :
    h.orderRingIso x = toVal w x.ofVal := rfl

@[simp]
theorem IsEquiv.orderRingIso_symm_apply (h : v.IsEquiv w) (x : WithVal w) :
    h.orderRingIso.symm x = toVal v x.ofVal := rfl

-- TODO: remove hw when we have range bases for Valued's ValuativeRel #27314
theorem IsEquiv.uniformContinuous_congr
    (hw : ∀ γ : Γ₀'ˣ, ∃ r s, 0 < w r ∧ 0 < w s ∧ w r / w s = γ) (h : v.IsEquiv w) :
    UniformContinuous (WithVal.congr v w (.refl R)) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := hw γ
  use .mk0 (v r / v s) (by simp [h.eq_zero, hr₀.ne.symm, hs₀.ne.symm]), fun x hx ↦ ?_
  rw [← hr, congr_apply, RingEquiv.refl_apply, Set.mem_setOf_eq, apply_symm_equiv, lt_div_iff₀ hs₀,
    ← map_mul, ← lt_def, ← ofVal_mul, ← h.orderRingIso_apply, ← h.orderRingIso.lt_symm_apply]
  simpa [lt_def, lt_div_iff₀ (h.pos_iff.2 hs₀)] using hx

theorem IsEquiv.uniformContinuous_equiv [Valued R Γ₀'] (hv : Valued.v = w)
    (hw : ∀ γ : Γ₀'ˣ, ∃ r s, 0 < w r ∧ 0 < w s ∧ w r / w s = γ) (h : v.IsEquiv w) :
    UniformContinuous (WithVal.equiv v) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := hw γ
  use .mk0 (v r / v s) (by simp [h.eq_zero, hr₀.ne.symm, hs₀.ne.symm]), fun x hx ↦ ?_
  rw [← hr, equiv_apply, Set.mem_setOf_eq, lt_div_iff₀ hs₀, hv, ← map_mul, ← lt_def, ← ofVal_mul,
    ← h.orderRingIso_apply, ← h.orderRingIso.lt_symm_apply]
  simpa [lt_def, lt_div_iff₀ (h.pos_iff.2 hs₀)] using hx

theorem IsEquiv.uniformContinuous_equiv_symm [Valued R Γ₀'] (hv : Valued.v = w)
    (hw : ∀ γ : Γ₀ˣ, ∃ r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ) (h : w.IsEquiv v) :
    UniformContinuous (WithVal.equiv v).symm := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := hw γ
  use .mk0 (w r / w s) (by simp [h.eq_zero, hr₀.ne.symm, hs₀.ne.symm]), fun x hx ↦ ?_
  simp only [equiv_symm_apply, Set.mem_setOf_eq, apply_symm_equiv]
  simp [hv] at hx
  rw [← hr, lt_div_iff₀ hs₀, ← map_mul, ← lt_def,
    ← h.orderRingIso_apply, ← h.orderRingIso.lt_symm_apply]
  simpa [lt_def, lt_div_iff₀ (h.pos_iff.2 hs₀)] using hx

@[deprecated (since := "2026-01-27")]
  alias IsEquiv.uniformContinuous_equivWithVal := IsEquiv.uniformContinuous_congr

/-- If two valuations `v` and `w` are equivalent then `WithVal v` and `WithVal w` are
isomorphic as uniform spaces. -/
def IsEquiv.uniformEquiv (hv : ∀ γ : Γ₀ˣ, ∃ r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ)
    (hw : ∀ γ : Γ₀'ˣ, ∃ r s, 0 < w r ∧ 0 < w s ∧ w r / w s = γ)
    (h : v.IsEquiv w) : WithVal v ≃ᵤ WithVal w where
  __ := WithVal.congr v w (.refl R)
  uniformContinuous_toFun := h.uniformContinuous_congr hw
  uniformContinuous_invFun := h.symm.uniformContinuous_congr hv

/-- Let `v : Valuation R Γ₀`. If `R` has `Valued R Γ₀'` defined via construction through
`w : Valuation R Γ₀'`, with `v` equivalent to `w`, then `WithVal.equiv` defines a uniform
space isomorphism `WithVal v ≃ᵤ R`. -/
def _root_.WithVal.uniformEquiv [Valued R Γ₀'] (hV : Valued.v = w)
    (hv : ∀ γ : Γ₀ˣ, ∃ r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ)
    (hw : ∀ γ : Γ₀'ˣ, ∃ r s, 0 < w r ∧ 0 < w s ∧ w r / w s = γ) (h : v.IsEquiv w) :
    WithVal v ≃ᵤ R where
  __ := WithVal.equiv v
  uniformContinuous_toFun := h.uniformContinuous_equiv hV hw
  uniformContinuous_invFun := h.symm.uniformContinuous_equiv_symm hV hv

theorem exists_div_eq_of_surjective {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (hv : Function.Surjective v)
    (γ : Γ₀ˣ) : ∃ r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ := by
  obtain ⟨r, hr⟩ := hv γ
  exact ⟨r, 1, by simp [hr]⟩

open UniformSpace.Completion in
theorem IsEquiv.valuedCompletion_le_one_iff {K : Type*} [Field K] {v : Valuation K Γ₀}
    {w : Valuation K Γ₀'} (h : v.IsEquiv w) (hv : Function.Surjective v)
    (hw : Function.Surjective w) {x : v.Completion} :
    Valued.v x ≤ 1 ↔ Valued.v (mapEquiv (h.uniformEquiv (exists_div_eq_of_surjective hv)
      (exists_div_eq_of_surjective hw)) x) ≤ 1 := by
  induction x using induction_on with
  | hp =>
    exact (mapEquiv (h.uniformEquiv _ _)).toHomeomorph.isClosed_setOf_iff
      (Valued.isClopen_closedBall _ one_ne_zero) (Valued.isClopen_closedBall _ one_ne_zero)
  | ih a => simpa [Valued.valuedCompletion_apply, ← WithVal.apply_equiv] using h.le_one_iff_le_one

end Equivalence

end Valuation

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (v : Valuation K Γ₀)

instance : CoeHead (𝓞 (WithVal v)) (WithVal v) where
  coe x := RingOfIntegers.val x

instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    IsIntegralClosure R ℤ (WithVal v) where
  algebraMap_injective := WithVal.algebraMap_right_injective _
    (IsIntegralClosure.algebraMap_injective R ℤ K)
  isIntegral_iff := by
    simp [← isIntegral_algHom_iff (WithVal.algEquiv ℤ v).toAlgHom (WithVal.algEquiv ℤ v).injective,
      IsIntegralClosure.isIntegral_iff (A := R), WithVal.algebraMap_right_apply,
      (WithVal.toVal_injective v).eq_iff]

/-- The ring equivalence between `𝓞 (WithVal v)` and an integral closure of
`ℤ` in `K`. -/
@[simps!]
def withValEquiv (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    𝓞 (WithVal v) ≃+* R := NumberField.RingOfIntegers.equiv R

end NumberField.RingOfIntegers

open scoped NumberField in
/-- The ring of integers of `WithVal v`, when `v` is a valuation on `ℚ`, is
equivalent to `ℤ`. -/
@[simps! apply]
def Rat.ringOfIntegersWithValEquiv (v : Valuation ℚ Γ₀) : 𝓞 (WithVal v) ≃+* ℤ :=
  NumberField.RingOfIntegers.withValEquiv v ℤ
