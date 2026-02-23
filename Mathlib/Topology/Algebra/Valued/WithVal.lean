/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

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
@[nolint unusedArguments]
def WithVal [Ring R] : Valuation R Γ₀ → Type _ := fun _ => R

namespace WithVal

section Instances

variable {P S : Type*}

instance [Ring R] (v : Valuation R Γ₀) : Ring (WithVal v) := inferInstanceAs (Ring R)

instance [CommRing R] (v : Valuation R Γ₀) : CommRing (WithVal v) := inferInstanceAs (CommRing R)

instance [Field R] (v : Valuation R Γ₀) : Field (WithVal v) := inferInstanceAs (Field R)

instance [Ring R] (v : Valuation R Γ₀) : Inhabited (WithVal v) := ⟨0⟩

instance [Ring R] (v : Valuation R Γ₀) : Preorder (WithVal v) := v.toPreorder

instance [CommSemiring S] [CommRing R] [Algebra S R] (v : Valuation R Γ₀) :
    Algebra S (WithVal v) := inferInstanceAs (Algebra S R)

instance [CommRing S] [CommRing R] [Algebra S R] [IsFractionRing S R] (v : Valuation R Γ₀) :
    IsFractionRing S (WithVal v) := inferInstanceAs (IsFractionRing S R)

instance [Ring R] [SMul S R] (v : Valuation R Γ₀) : SMul S (WithVal v) :=
  inferInstanceAs (SMul S R)

instance [Ring R] [SMul P S] [SMul S R] [SMul P R] [IsScalarTower P S R] (v : Valuation R Γ₀) :
    IsScalarTower P S (WithVal v) :=
  inferInstanceAs (IsScalarTower P S R)

variable [CommRing R] (v : Valuation R Γ₀)

instance {S : Type*} [Ring S] [Algebra R S] :
    Algebra (WithVal v) S := inferInstanceAs (Algebra R S)

instance {S : Type*} [Ring S] [Algebra R S] (w : Valuation S Γ₀) :
    Algebra R (WithVal w) := inferInstanceAs (Algebra R S)

instance {P S : Type*} [Ring S] [Semiring P] [Module P R] [Module P S]
    [Algebra R S] [IsScalarTower P R S] :
    IsScalarTower P (WithVal v) S := inferInstanceAs (IsScalarTower P R S)

end Instances

section Ring

variable [Ring R] (v : Valuation R Γ₀)

/-- Canonical ring equivalence between `WithVal v` and `R`. -/
def equiv : WithVal v ≃+* R := RingEquiv.refl _

/-- Canonical valuation on the `WithVal v` type synonym. -/
def valuation : Valuation (WithVal v) Γ₀ := v.comap (equiv v)

@[simp] lemma valuation_equiv_symm (x : R) : valuation v ((equiv v).symm x) = v x := rfl

variable {Γ'₀ : Type*} [LinearOrderedCommGroupWithZero Γ'₀]

/-- Canonical ring equivalence between `WithVal v` and `WithVal w`. -/
def equivWithVal (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    WithVal v ≃+* WithVal w :=
  (equiv v).trans (equiv w).symm

theorem equivWithVal_symm (v : Valuation R Γ₀) (w : Valuation R Γ'₀) :
    (equivWithVal v w).symm = equivWithVal w v := rfl

@[simp]
theorem equivWithVal_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal v} :
    equivWithVal v w x = (equiv w).symm (equiv v x) := rfl

@[simp]
theorem equivWithVal_symm_apply (v : Valuation R Γ₀) (w : Valuation R Γ'₀) {x : WithVal w} :
    (equivWithVal v w).symm x = (equiv v).symm (equiv w x) := rfl

instance {R} [Ring R] (v : Valuation R Γ₀) : Valued (WithVal v) Γ₀ :=
  Valued.mk' (valuation v)

theorem apply_equiv (r : WithVal v) : v (equiv v r) = Valued.v r := rfl

@[simp] theorem apply_symm_equiv (r : R) : Valued.v ((equiv v).symm r) = v r := rfl

theorem le_def {v : Valuation R Γ₀} {a b : WithVal v} :
    a ≤ b ↔ v (equiv v a) ≤ v (equiv v b) := .rfl

theorem lt_def {v : Valuation R Γ₀} {a b : WithVal v} :
    a < b ↔ v (equiv v a) < v (equiv v b) := .rfl

end Ring

section CommRing

variable [CommRing R] (v : Valuation R Γ₀)

instance : ValuativeRel (WithVal v) := .ofValuation (valuation v)
instance : (valuation v).Compatible := .ofValuation (valuation v)

end CommRing

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- The completion of a field with respect to a valuation. -/
abbrev Completion := UniformSpace.Completion (WithVal v)

instance : Coe R v.Completion :=
  inferInstanceAs <| Coe (WithVal v) (UniformSpace.Completion (WithVal v))

section Equivalence

/-! The uniform isomorphism between `WithVal v` and `WithVal w` when `v` and `w` are
equivalent. -/

variable {R Γ₀ Γ₀' : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀'] {v : Valuation R Γ₀} {w : Valuation R Γ₀'}

/-- If two valuations `v` and `w` are equivalent then `WithVal v` is order-isomorphic
to `WithVal w`. -/
def IsEquiv.orderRingIso (h : v.IsEquiv w) :
    WithVal v ≃+*o WithVal w where
  __ := equivWithVal v w
  map_le_map_iff' := h.symm ..

@[simp]
theorem IsEquiv.orderRingIso_apply (h : v.IsEquiv w) (x : WithVal v) :
    h.orderRingIso x = (equivWithVal v w) x := rfl

@[simp]
theorem IsEquiv.orderRingIso_symm_apply (h : v.IsEquiv w) (x : WithVal w) :
    h.orderRingIso.symm x = (equivWithVal v w).symm x := rfl

-- TODO: remove hw when we have range bases for Valued's ValuativeRel #27314
theorem IsEquiv.uniformContinuous_equivWithVal
    (hw : ∀ γ : Γ₀'ˣ, ∃ r s, 0 < w r ∧ 0 < w s ∧ w r / w s = γ) (h : v.IsEquiv w) :
    UniformContinuous (equivWithVal v w) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  obtain ⟨r, s, hr₀, hs₀, hr⟩ := hw γ
  use .mk0 (v r / v s) (by simp [h.eq_zero, hr₀.ne.symm, hs₀.ne.symm]), fun x hx ↦ ?_
  rw [← hr, Set.mem_setOf_eq, ← WithVal.apply_equiv, ← (equiv w).apply_symm_apply r,
    lt_div_iff₀ hs₀, ← (equiv w).apply_symm_apply s, ← map_mul, ← map_mul, ← lt_def,
    ← h.orderRingIso_apply, ← h.orderRingIso.apply_symm_apply ((equiv w).symm s), ← map_mul,
    ← h.orderRingIso.lt_symm_apply]
  simpa [lt_def, lt_div_iff₀ (h.pos_iff.2 hs₀)] using hx

/-- If two valuations `v` and `w` are equivalent then `WithVal v` and `WithVal w` are
isomorphic as uniform spaces. -/
def IsEquiv.uniformEquiv (hv : ∀ γ : Γ₀ˣ, ∃ r s, 0 < v r ∧ 0 < v s ∧ v r / v s = γ)
    (hw : ∀ γ : Γ₀'ˣ, ∃ r s, 0 < w r ∧ 0 < w s ∧ w r / w s = γ)
    (h : v.IsEquiv w) : WithVal v ≃ᵤ WithVal w where
  __ := equivWithVal v w
  uniformContinuous_toFun := h.uniformContinuous_equivWithVal hw
  uniformContinuous_invFun := h.symm.uniformContinuous_equivWithVal hv

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
  | ih a =>
    simpa [Valued.valuedCompletion_apply, ← WithVal.apply_equiv] using h.le_one_iff_le_one

end Equivalence

end Valuation

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (v : Valuation K Γ₀)

instance : CoeHead (𝓞 (WithVal v)) (WithVal v) := inferInstanceAs (CoeHead (𝓞 K) K)

instance : IsDedekindDomain (𝓞 (WithVal v)) := inferInstanceAs (IsDedekindDomain (𝓞 K))

instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    IsIntegralClosure R ℤ (WithVal v) := ‹IsIntegralClosure R ℤ K›

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
