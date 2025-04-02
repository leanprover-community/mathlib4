/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.NumberTheory.NumberField.Basic

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

noncomputable section

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

/-- Type synonym for a ring equipped with the topology coming from a valuation. -/
@[nolint unusedArguments]
def WithVal : Valuation R Γ₀ → Type _ := fun _ => R

namespace WithVal

variable (v : Valuation R Γ₀)

instance : Ring (WithVal v) := ‹Ring R›

instance [CommRing R] : CommRing (WithVal v) := ‹CommRing R›

instance [Field R] : Field (WithVal v) := ‹Field R›

instance : Inhabited (WithVal v) := ⟨0⟩

instance {S : Type*} [CommSemiring S] [CommRing R] [Algebra S R] : Algebra S (WithVal v) :=
  ‹Algebra S R›

instance {S : Type*} [CommRing S] [CommRing R] [Algebra S R] [IsFractionRing S R] :
    IsFractionRing S (WithVal v) :=
  ‹IsFractionRing S R›

instance {S : Type*} [SMul S R] : SMul S (WithVal v) :=
  ‹SMul S R›

instance {P S : Type*} [SMul P S] [SMul S R] [SMul P R] [IsScalarTower P S R] :
    IsScalarTower P S (WithVal v) :=
  ‹IsScalarTower P S R›

instance {S : Type*} [Ring S] [CommRing R] [Algebra R S] :
    Algebra (WithVal v) S := ‹Algebra R S›

instance {S : Type*} [Ring S] [CommRing R] [Algebra R S] (w : Valuation S Γ₀) :
    Algebra R (WithVal w) := ‹Algebra R S›

instance {P S : Type*} [Ring S] [CommRing R] [Semiring P] [Module P R] [Module P S]
    [Algebra R S] [IsScalarTower P R S] :
    IsScalarTower P (WithVal v) S :=
  ‹IsScalarTower P R S›

instance (v : Valuation R Γ₀) : Valued (WithVal v) Γ₀ := Valued.mk' v

/-- Canonical ring equivalence between `WithVal v` and `R`. -/
def equiv : WithVal v ≃+* R := RingEquiv.refl _

theorem apply_equiv (r : WithVal v) : v (WithVal.equiv v r) = v r := rfl

theorem equiv_symm_apply (r : R) : v ((WithVal.equiv v).symm r) = v r := rfl

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- The completion of a field with respect to a valuation. -/
def Completion := UniformSpace.Completion (WithVal v)

instance : Ring v.Completion := UniformSpace.Completion.ring

instance : Inhabited v.Completion := ⟨0⟩

instance : Coe R v.Completion :=
  inferInstanceAs <| Coe (WithVal v) (UniformSpace.Completion (WithVal v))

instance {M : Type*} [SMul M (WithVal v)] : SMul M v.Completion :=
  UniformSpace.Completion.instSMul _ _

instance (M N : Type*) [SMul M (WithVal v)] [SMul N (WithVal v)] [SMul M N]
    [UniformContinuousConstSMul M (WithVal v)] [UniformContinuousConstSMul N (WithVal v)]
    [IsScalarTower M N (WithVal v)] :
    IsScalarTower M N v.Completion :=
  UniformSpace.Completion.instIsScalarTower M N (WithVal v)

instance valuedCompletion {K : Type*} [Field K] (v : Valuation K Γ₀) :
    Valued v.Completion Γ₀ := Valued.valuedCompletion --Valued.valuedCompletion

theorem valuedCompletion_apply {K : Type*} [Field K] {v : Valuation K Γ₀}
    (x : WithVal v) : v.valuedCompletion.v x = Valued.v x := Valued.valuedCompletion_apply _

theorem valuedCompletion_apply' {K : Type*} [Field K] {v : Valuation K Γ₀}
    (x : K) : v.valuedCompletion.v x = Valued.v (WithVal.equiv v |>.symm x) :=
  Valued.valuedCompletion_apply _

theorem valuedCompletion_eq_valuation {K : Type*} [Field K] {v : Valuation K Γ₀}
    (x : WithVal v) : Valued.v (x : v.Completion) = v x :=
  valuedCompletion_apply (x : K)

instance {K : Type*} [Field K] (v : Valuation K Γ₀) [CompletableTopField (WithVal v)]  :
    Field v.Completion := UniformSpace.Completion.instField

end Valuation

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] (v : Valuation K Γ₀)

instance : CoeHead (𝓞 (WithVal v)) (WithVal v) := inferInstanceAs (CoeHead (𝓞 K) K)

instance : IsDedekindDomain (𝓞 (WithVal v)) := inferInstanceAs (IsDedekindDomain (𝓞 K))

instance (R : Type*) [CommRing R] [Algebra R K] [IsIntegralClosure R ℤ K] :
    IsIntegralClosure R ℤ (WithVal v) := ‹IsIntegralClosure R ℤ K›

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
