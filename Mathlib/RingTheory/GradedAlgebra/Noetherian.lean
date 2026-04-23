/-
Copyright (c) 2023 Fangming Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fangming Li
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The properties of a graded Noetherian ring.

This file proves that the 0-th grade of a Noetherian ring is
also a Noetherian ring.
-/

@[expose] public section

variable {ι A σ : Type*}
variable [Ring A] [IsNoetherianRing A]
variable [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ι → σ) [GradedRing 𝒜]

namespace GradedRing

/-- If the internally graded ring `A` is Noetherian, then `𝒜 0` is a Noetherian ring. -/
instance GradeZero.isNoetherianRing : IsNoetherianRing (𝒜 0) :=
  isNoetherianRing_of_surjective
    A (𝒜 0) (GradedRing.projZeroRingHom' 𝒜) (GradedRing.projZeroRingHom'_surjective 𝒜)

end GradedRing
