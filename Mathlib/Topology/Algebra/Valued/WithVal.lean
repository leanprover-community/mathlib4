/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Ring topologised by a valuation

`WithVal v` is a type synonym for a ring `R` equipped with the topology coming from
a valuation.

## Main definitions
 - `WithVal` : type synonym for a ring equipped with the topology coming from a valuation.
 - `WithVal.equiv` : The canonical ring equivalence between `WithValuation v` and `R`.
 - `Valuation.Completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified valuation.
-/

noncomputable section

variable {R : Type*} {Γ₀ : outParam (Type*)} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

/-- Type synonym for a ring equipped with the topology coming from a valuation. -/
@[nolint unusedArguments]
def WithVal : Valuation R Γ₀ → Type _ := fun _ => R

namespace WithVal

variable (v : Valuation R Γ₀)

instance [Nontrivial R] : Nontrivial (WithVal v) := ‹Nontrivial R›

instance [Unique R] : Unique (WithVal v) := ‹Unique R›

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

instance (v : Valuation R Γ₀) : Valued (WithVal v) Γ₀ := Valued.mk' v

/-- Canonical ring equivalence between `WithValuation v` and `R`. -/
def equiv : WithVal v ≃+* R := RingEquiv.refl _

end WithVal

/-! The completion of a field with respect to a valuation. -/

namespace Valuation

open WithVal

variable {K : Type*} [Field K] (v : Valuation K Γ₀)

/-- The completion of a field with respect to a valuation. -/
abbrev Completion := UniformSpace.Completion (WithVal v)

instance : Coe K v.Completion :=
  inferInstanceAs <| Coe (WithVal v) (UniformSpace.Completion (WithVal v))

end Valuation
