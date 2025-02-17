/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# WithValuation

`WithValuation v` is a type synonym for a ring `R` which depends on a valuation on `R`.

## Main definitions
 - `WithValuation` : type synonym for a ring which depends on a valuation.
 - `WithValuation.equiv` : The canonical ring equivalence between `WithValuation v` and `R`.
 - `Valuation.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified valuation.
-/

noncomputable section

variable {R : Type*} {Γ₀ : outParam (Type*)} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

/-- Type synonym for a ring which depends on a valuation. -/
@[nolint unusedArguments]
def WithValuation : Valuation R Γ₀ → Type _ := fun _ => R

namespace WithValuation

variable (v : Valuation R Γ₀)

instance [Nontrivial R] : Nontrivial (WithValuation v) := ‹Nontrivial R›

instance [Unique R] : Unique (WithValuation v) := ‹Unique R›

instance : Ring (WithValuation v) := ‹Ring R›

instance [CommRing R] : CommRing (WithValuation v) := ‹CommRing R›

instance [Field R] : Field (WithValuation v) := ‹Field R›

instance : Inhabited (WithValuation v) := ⟨0⟩

instance {S : Type*} [CommSemiring S] [CommRing R] [Algebra S R] : Algebra S (WithValuation v) :=
  ‹Algebra S R›

instance {S : Type*} [CommRing S] [CommRing R] [Algebra S R] [IsFractionRing S R] :
    IsFractionRing S (WithValuation v) :=
  ‹IsFractionRing S R›

instance valued (v : Valuation R Γ₀) : Valued (WithValuation v) Γ₀ := Valued.mk' v

/-- Canonical ring equivalence between `WithValuation v` and `R`. -/
def equiv : WithValuation v ≃+* R := RingEquiv.refl _

end WithValuation

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithValuation

variable {K : Type*} [Field K] (v : Valuation K Γ₀)

/-- The completion of a field with respect to a valuation. -/
abbrev Completion := UniformSpace.Completion (WithValuation v)

instance : Coe K v.Completion :=
  inferInstanceAs <| Coe (WithValuation v) (UniformSpace.Completion (WithValuation v))

end Valuation
