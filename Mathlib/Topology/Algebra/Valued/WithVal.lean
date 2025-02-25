/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Ring topologised by a valuation

For a given valuation `v : Valuation R Γ₀` on a ring `R` taking values in `Γ₀`, this file
defines the type synonym `WithVal v` of `R`. By assigning a `Valued (WithVal v) Γ₀` instance,
`WithVal v` represents the ring `R` equipped with the topology coming from `v`. The type
synonym `WithVal v` is in isomorphism to `R` as rings via `WithVal.equiv v`. This
isomorphism should be used to explicitly map terms of `WithVal v` with terms of `R`.

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

instance [Field R] : Field (WithVal v) := ‹Field R›

instance [CommRing R] : CommRing (WithVal v) := ‹CommRing R›

--instance [Field R] : Field (WithVal v) := ‹Field R›

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

instance (v : Valuation R Γ₀) : Valued (WithVal v) Γ₀ := Valued.mk' v

/-- Canonical ring equivalence between `WithValuation v` and `R`. -/
def equiv : WithVal v ≃+* R := RingEquiv.refl _

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
