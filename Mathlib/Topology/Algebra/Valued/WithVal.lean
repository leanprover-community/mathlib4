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

instance : Ring (WithVal v) := Equiv.ring { toFun := ofVal, invFun := toVal v }
instance : Inhabited (WithVal v) := ⟨0⟩
instance : Preorder (WithVal v) := .lift (v ∘ ofVal)

theorem le_def {v : Valuation R Γ₀} {a b : WithVal v} : a ≤ b ↔ v a.ofVal ≤ v b.ofVal := .rfl

theorem lt_def {v : Valuation R Γ₀} {a b : WithVal v} : a < b ↔ v a.ofVal < v b.ofVal := .rfl

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

/-- Lift a `RingEquiv` to `WithVal`. -/
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

theorem apply_ofVal (r : WithVal v) : v r.ofVal = Valued.v r := rfl

theorem val_apply_equiv (r : WithVal v) : v (equiv v r) = Valued.v r := rfl

@[simp] theorem valued_toVal (r : R) : Valued.v (toVal v r) = v r := rfl

@[deprecated (since := "2026-03-02")] alias apply_equiv := apply_ofVal
@[deprecated (since := "2026-03-02")] alias apply_symm_equiv := valued_toVal

instance [CharZero R] : CharZero (WithVal v) :=
  .of_addMonoidHom (equiv v).symm.toAddMonoidHom (by simp) (equiv v).symm.injective

end Ring

section CommRing

variable [CommRing R] (v : Valuation R Γ₀)

set_option backward.isDefEq.respectTransparency false in
instance : CommRing (WithVal v) := fast_instance% (equiv v).commRing

instance : ValuativeRel (WithVal v) := .ofValuation (valuation v)

instance : (valuation v).Compatible := .ofValuation (valuation v)

end CommRing

section Module

variable [Ring R] (v : Valuation R Γ₀) {S : Type*}

instance [SMul R S] : SMul (WithVal v) S where
  smul x s := ofVal x • s

theorem smul_left_def [SMul R S] (x : WithVal v) (s : S) : x • s = ofVal x • s := rfl

instance [SMul R S] [FaithfulSMul R S] : FaithfulSMul (WithVal v) S where
  eq_of_smul_eq_smul h := ofVal_injective v <| FaithfulSMul.eq_of_smul_eq_smul h

instance [SMul S R] : SMul S (WithVal v) := (equiv v).smul S

theorem smul_right_def [SMul S R] (s : S) (x : WithVal v) : s • x = toVal v (s • ofVal x) := rfl

instance [SMul S R] [FaithfulSMul S R] : FaithfulSMul S (WithVal v) where
  eq_of_smul_eq_smul h := by
    simp only [smul_right_def, toVal.injEq] at h
    exact FaithfulSMul.eq_of_smul_eq_smul fun r ↦ h (toVal v r)

instance {P : Type*} [Ring R] [SMul S P] [SMul R S] [SMul R P]
    [IsScalarTower R S P] (v : Valuation R Γ₀) : IsScalarTower (WithVal v) S P where
  smul_assoc := by simp [smul_left_def]

instance {P : Type*} [Ring S] [SMul P S] [SMul R S] [SMul P R]
    [IsScalarTower P R S] (v : Valuation S Γ₀) : IsScalarTower P R (WithVal v) :=
  (equiv v).isScalarTower P R

instance {P : Type*} [Ring S] [SMul P R] [SMul S R] [SMul P S]
    [IsScalarTower P S R] (v : Valuation S Γ₀) : IsScalarTower P (WithVal v) R where
  smul_assoc := by simp [smul_right_def, smul_left_def]

instance [AddCommMonoid S] [Module R S] : Module (WithVal v) S :=
  .compHom S (equiv v).toRingHom

set_option backward.isDefEq.respectTransparency false in
instance [AddCommMonoid S] [Module R S] [Module.Finite R S] :
    Module.Finite (WithVal v) S := .of_restrictScalars_finite R (WithVal v) S

instance [Semiring S] [Module S R] : Module S (WithVal v) :=
  fast_instance% (equiv v).module S

@[simp] theorem toVal_smul [SMul S R] (s : S) (r : R) : toVal v (s • r) = s • toVal v r := rfl

@[simp] theorem ofVal_smul [SMul S R] (s : S) (x : WithVal v) : ofVal (s • x) = s • ofVal x := rfl

variable [Ring S] [Module R S] (v : Valuation S Γ₀)

variable (R) in
/-- The canonical `R`-linear isomorphism between `WithVal v` and `S`, when `v : Valuation S Γ₀`. -/
def linearEquiv : WithVal v ≃ₗ[R] S := (equiv v).linearEquiv R

@[simp] theorem linearEquiv_apply (x : WithVal v) : linearEquiv R v x = x.ofVal := rfl

@[simp] theorem linearEquiv_symm_apply (x : S) : (linearEquiv R v).symm x = toVal v x := rfl

instance [Module R S] [Module.Finite R S] :
    Module.Finite R (WithVal v) := .equiv (linearEquiv R v).symm

end Module

section Algebra

variable {S : Type*}

section left

variable [CommRing R] (v : Valuation R Γ₀) [Semiring S] [Algebra R S]

instance : Algebra (WithVal v) S where
  __ := inferInstanceAs (Module (WithVal v) S)
  __ := Algebra.compHom S (equiv v).toRingHom

theorem algebraMap_left_apply (s : WithVal v) :
    algebraMap (WithVal v) S s = algebraMap R S s.ofVal := rfl

instance {S : Type*} [CommSemiring S] [Algebra R S] [i : IsFractionRing R S] :
    IsFractionRing (WithVal v) S := .of_ringEquiv_left (equiv v) (fun _ ↦ rfl)

theorem algebraMap_left_injective (h : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap (WithVal v) S) := h.comp (ofVal_injective v)

end left

section right

variable [CommSemiring R] [Ring S] [Algebra R S] (v : Valuation S Γ₀)

instance : Algebra R (WithVal v) := (equiv v).algebra R

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

set_option backward.isDefEq.respectTransparency false in
instance : Field (WithVal v) := fast_instance% (equiv v).field

set_option backward.isDefEq.respectTransparency false in
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
section ValueGroup₀

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

theorem valueGroup_eq : valueGroup (instValued v).v = valueGroup v := by
  simp [valueGroup, valueMonoid, ← (WithVal.ofVal_surjective v).range_comp]
  rfl

/-- The multiplicative equivalence between the `valueGroup` of the valuation on `WithVal v`
and the valuation `v`. -/
@[simps! apply symm_apply]
def valueGroupEquiv : valueGroup (instValued v).v ≃* valueGroup v where
  __ := Equiv.setCongr (by simp [valueGroup_eq v])
  map_mul' := by simp [Equiv.setCongr, Equiv.subtypeEquivProp]

theorem strictMono_valueGroupEquiv : StrictMono (valueGroupEquiv v) :=
  fun _ _ _ ↦ by simpa

theorem strictMono_valueGroupEquiv_symm : StrictMono (valueGroupEquiv v).symm :=
  fun _ _ _ ↦ by simpa

/-- The order-preserving, multiplicative equivalence between the `ValueGroup₀` of the valuation
on `WithVal v` and the valuation `v`. -/
@[simps!]
def valueGroupOrderIso₀ : ValueGroup₀ (instValued v).v ≃*o ValueGroup₀ v where
  toFun := WithZero.map' (valueGroupEquiv v)
  invFun := WithZero.map' (valueGroupEquiv v).symm
  left_inv x := by
    match x with
    | 0 => simp
    | .coe a => simp
  right_inv y := by
    match y with
    | 0 => simp
    | .coe b => simp
  map_mul' := by simp
  map_le_map_iff' {a b} := by
    match a, b with
    | 0, 0 => simp
    | 0, .coe _ => simp
    | .coe _, 0 => simp
    | .coe a, .coe b => simp

lemma valueGroupOrderIso₀_restrict (b : WithVal v) :
    valueGroupOrderIso₀ v (Valued.v.restrict b) = v.restrict b.ofVal := by
  simp [Valued.v.restrict_def, restrict₀_apply, ← apply_ofVal, v.restrict_def]
  by_cases hb : v b.ofVal = 0 <;> simp [hb]

lemma valueGroupOrderIso₀_symm_restrict (b : R) :
    (valueGroupOrderIso₀ v).symm (Valuation.restrict v b) = Valued.v.restrict (toVal v b) := by
  simp [Valued.v.restrict_def, restrict₀_apply, ← apply_ofVal, v.restrict_def]
  by_cases hb : v b = 0 <;> simp [hb]

lemma strictMono_valueGroupOrderIso₀ :
    StrictMono (WithVal.valueGroupOrderIso₀ v) :=
  WithZero.map'_strictMono (strictMono_valueGroupEquiv v)

lemma strictMono_valueGroupOrderIso₀_symm :
    StrictMono (WithVal.valueGroupOrderIso₀ v).symm :=
  WithZero.map'_strictMono (strictMono_valueGroupEquiv_symm v)

end ValueGroup₀

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

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀

set_option backward.isDefEq.respectTransparency false in
theorem IsEquiv.uniformContinuous_equiv [hval : Valued R Γ₀'] (hv : Valued.v = w)
    (h : v.IsEquiv w) : UniformContinuous (WithVal.equiv v) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := exists_div_eq_of_unit Valued.v γ
  use .mk0 ((instValued v).v.restrict ((WithVal.equiv v).symm r) /
    (instValued v).v.restrict ((WithVal.equiv v).symm s)) (by
    simp [Valuation.restrict_def, restrict₀_eq_zero_iff, (eq_zero h (r := r)).ne, ← hv,
      (eq_zero h (r := s)).ne, hr₀.ne', hs₀.ne'])
  intro x hx
  let y := (WithVal.equiv v) x
  have hy : toVal v y = x := rfl
  have hs0' : 0 < Valued.v.restrict (toVal v s) := by
    simp [restrict_pos_iff, h.pos_iff, ← hv, hs₀]
  have h' : v.restrict.IsEquiv w.restrict := h.restrict
  rw [← hr, equiv_apply, Set.mem_setOf_eq, lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀), hv,
    ← map_mul, ← lt_def, ← ofVal_mul,
    ← hy, ← toVal_mul, ←  h'.orderRingIso_apply, ← h'.orderRingIso.lt_symm_apply]
  simp only [toVal_mul, orderRingIso_symm_apply, lt_def, ofVal_mul, restrict_lt_iff]
  simp only [equiv_symm_apply, Units.val_mk0, Set.mem_setOf_eq, lt_div_iff₀ hs0'] at hx
  erw [← map_mul] at hx -- Why erw?
  rw [restrict_lt_iff] at hx
  exact hx

set_option backward.isDefEq.respectTransparency false in
theorem IsEquiv.uniformContinuous_equiv_symm [hval : Valued R Γ₀'] (hv : Valued.v = w)
    (h : w.IsEquiv v) : UniformContinuous (WithVal.equiv v).symm := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := exists_div_eq_of_unit Valued.v γ
  have h' : w.restrict.IsEquiv v.restrict := h.restrict
  use .mk0 ((Valued.v.restrict ((WithVal.equiv v) r)) /
    (Valued.v.restrict ((WithVal.equiv v) s))) (by
    simp only [equiv_apply, restrict_def, restrict₀_eq_zero_iff, ne_eq, div_eq_zero_iff, not_or,
      hv, (eq_zero h (r := r.ofVal)).ne, (eq_zero h (r := s.ofVal)).ne]
    exact ⟨hr₀.ne', hs₀.ne'⟩)
  intro x hx
  simp only [equiv_symm_apply, Set.mem_setOf_eq]
  simp only [equiv_apply, Units.val_mk0, Set.mem_setOf_eq] at hx
  erw [lt_div_iff₀ , ← map_mul, restrict_lt_iff, hv, h.lt_iff_lt, map_mul] at hx
  · rw [← hr, lt_div_iff₀ ((restrict_pos_iff Valued.v s).mpr hs₀), ← map_mul, ← lt_def,
      ← h.orderRingIso_apply]
    simp only [orderRingIso_apply, toVal_mul, lt_def, ofVal_mul, restrict_lt_iff]
    rw [map_mul]
    exact hx
  · rw [restrict_pos_iff, hv, h.pos_iff]
    exact hs₀

set_option backward.isDefEq.respectTransparency false in
lemma IsEquiv.uniformContinuous (h : v.IsEquiv w) :
    @UniformContinuous R R (Valued.mk' w).toUniformSpace (Valued.mk' v).toUniformSpace
      (RingHom.id R) := by
  have h_val : ((Valued.mk' v).v).IsEquiv (Valued.mk' w).v := h
  have h_res : v.restrict.IsEquiv w.restrict := h_val.restrict
  refine @uniformContinuous_of_continuousAt_zero _ _ (Valued.mk' w).toUniformSpace _ _
    _ (Valued.mk' v).toUniformSpace _ _ _ _ (RingHom.id R) ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro x
  let u := WithZero.unzero (Units.ne_zero x)
  obtain ⟨a, ha, y, hu⟩ := (mem_valueGroup_iff_of_comm _).mp u.2
  simp only [Set.mem_setOf_eq, RingHom.id_apply]
  set y₀ := h_val.orderMonoidIso x with hy₀_def
  have hy₀_ne_zero : y₀ ≠ 0 := by simp [hy₀_def]
  set y := (Units.mk0 y₀ hy₀_ne_zero) with hy_def
  use y
  intro b hb
  rwa [← h_val.orderMonoidIso_spec, hy_def, Units.val_mk0, hy₀_def,
    h_val.orderMonoidIso.strictMono.lt_iff_lt] at hb

theorem IsEquiv.uniformContinuous_congr (h : v.IsEquiv w) :
    UniformContinuous (WithVal.congr v w (.refl R)) := by
  have hcomp : WithVal.congr v w (.refl R) = _ := RingEquiv.ext_iff.mpr (congrFun rfl)
  have h1 := IsEquiv.uniformContinuous_equiv (hval := Valued.mk' w) rfl h
  have h2 := IsEquiv.uniformContinuous_equiv_symm (hval := Valued.mk' v) rfl h
  have hR : @UniformContinuous R R (Valued.mk' w).toUniformSpace (Valued.mk' v).toUniformSpace
      (RingHom.id R) := h.uniformContinuous
  apply @UniformContinuous.comp (WithVal v) R (WithVal w) _ (Valued.mk' w).toUniformSpace _
    ((RingEquiv.refl R).trans (WithVal.equiv w).symm) (WithVal.equiv v) ?_ h1
  exact @UniformContinuous.comp R R (WithVal w) (Valued.mk' w).toUniformSpace
       (Valued.mk' v).toUniformSpace _ (WithVal.equiv w).symm (RingEquiv.refl R) h2 hR

@[deprecated (since := "2026-01-27")]
  alias IsEquiv.uniformContinuous_equivWithVal := IsEquiv.uniformContinuous_congr

/-- If two valuations `v` and `w` are equivalent then `WithVal v` and `WithVal w` are
isomorphic as uniform spaces. -/
def IsEquiv.uniformEquiv (h : v.IsEquiv w) : WithVal v ≃ᵤ WithVal w where
  __ := WithVal.congr v w (.refl R)
  uniformContinuous_toFun := h.uniformContinuous_congr
  uniformContinuous_invFun := h.symm.uniformContinuous_congr

/-- Let `v : Valuation R Γ₀`. If `R` has `Valued R Γ₀'` defined via construction through
`w : Valuation R Γ₀'`, with `v` equivalent to `w`, then `WithVal.equiv` defines a uniform
space isomorphism `WithVal v ≃ᵤ R`. -/
def _root_.WithVal.uniformEquiv [Valued R Γ₀'] (hV : Valued.v = w) (h : v.IsEquiv w) :
    WithVal v ≃ᵤ R where
  __ := WithVal.equiv v
  uniformContinuous_toFun := h.uniformContinuous_equiv hV
  uniformContinuous_invFun := h.symm.uniformContinuous_equiv_symm hV

theorem exists_div_eq_of_surjective {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (hv : Function.Surjective v)
    (γ : Γ₀ˣ) : ∃ r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ := by
  obtain ⟨r, hr⟩ := hv γ
  exact ⟨r, 1, by simp [hr]⟩

theorem restrict_exists_div_eq {K : Type*} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)
    (γ : (MonoidWithZeroHom.ValueGroup₀ v)ˣ) :
    ∃ r s, 0 < v r ∧ 0 < v s ∧ v.restrict r / v.restrict s = γ.1 := by
  obtain ⟨r, hr⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective v γ
  classical
  exact ⟨r, 1, by
    simp only [map_one, zero_lt_one, restrict_def, hr, div_one, and_self, and_true]
    rw [← map_zero v, ← embedding_restrict₀,  ← embedding_restrict₀ r, hr,
      embedding_strictMono.lt_iff_lt, map_zero]
    refine WithZero.pos_iff_ne_zero.mpr (Units.ne_zero γ)⟩

set_option backward.isDefEq.respectTransparency false in
open UniformSpace.Completion in
theorem IsEquiv.valuedCompletion_le_one_iff {K : Type*} [Field K] {v : Valuation K Γ₀}
    {w : Valuation K Γ₀'} (h : v.IsEquiv w) {x : v.Completion} :
    Valued.v x ≤ 1 ↔ Valued.v (mapEquiv h.uniformEquiv x) ≤ 1 := by
  induction x using induction_on with
  | hp =>
    have h1 (x : UniformSpace.Completion (WithVal v)) :
      Valued.v x ≤ 1 ↔ Valued.v.restrict x ≤ 1 := by rw [restrict_le_one_iff]
    simp_rw [h1]
    convert (mapEquiv h.uniformEquiv).toHomeomorph.isClosed_setOf_iff
      (Valued.isClopen_closedBall _ one_ne_zero) (Valued.isClopen_closedBall _ one_ne_zero)
    rw [restrict_le_one_iff]
    rfl
  | ih a =>
    simpa [Valued.valuedCompletion_apply] using h.le_one_iff_le_one

end Equivalence

end Valuation

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (v : Valuation K Γ₀)

instance : CoeHead (𝓞 (WithVal v)) (WithVal v) where
  coe x := RingOfIntegers.val x

instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    IsIntegralClosure R ℤ (WithVal v) := .of_algEquiv _ (WithVal.algEquiv ℤ v).symm (fun _ ↦ rfl)

set_option backward.isDefEq.respectTransparency false in
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
