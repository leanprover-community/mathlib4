/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.Valued.ValuationTopology
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

variable {R Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- Type synonym for a ring equipped with the topology coming from a valuation. -/
@[nolint unusedArguments]
def WithVal [Ring R] : Valuation R Γ₀ → Type _ := fun _ => R

namespace WithVal

section Instances

variable {P S : Type*} [LinearOrderedCommGroupWithZero Γ₀]

instance [Ring R] (v : Valuation R Γ₀) : Ring (WithVal v) := inferInstanceAs (Ring R)

instance [CommRing R] (v : Valuation R Γ₀) : CommRing (WithVal v) := inferInstanceAs (CommRing R)

instance [Field R] (v : Valuation R Γ₀)  : Field (WithVal v) := inferInstanceAs (Field R)

instance [Ring R] (v : Valuation R Γ₀) : Inhabited (WithVal v) := ⟨0⟩

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

instance {R} [Ring R] (v : Valuation R Γ₀) : Valued (WithVal v) Γ₀ := Valued.mk' v

end Instances

variable [Ring R] (v : Valuation R Γ₀)

/-- Canonical ring equivalence between `WithVal v` and `R`. -/
def equiv : WithVal v ≃+* R := RingEquiv.refl _

theorem apply_equiv (r : WithVal v) : Valued.v ((WithVal.equiv v).symm r) = v r := rfl

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {R : Type*} [Ring R] (v : Valuation R Γ₀)

/-- The completion of a field with respect to a valuation. -/
abbrev Completion := UniformSpace.Completion (WithVal v)

instance : Coe R v.Completion :=
  inferInstanceAs <| Coe (WithVal v) (UniformSpace.Completion (WithVal v))

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
