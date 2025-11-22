/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Analysis.Normed.Module.TransferInstance
-- XXX: for import reduction purposes, the file should be split in two, with these imports
-- going into a second file. This does not seem warrented at the moment.
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Transfer algebraic structures from `α` to `Shrink α`

-/

@[expose] public section

namespace Shrink

universe v
variable {R 𝕜 α : Type*} [Small.{v} α] [Semiring R] [NormedField 𝕜]

suppress_compilation

instance [SeminormedAddCommGroup α] : SeminormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.seminormedAddCommGroup

instance [NormedAddCommGroup α] : NormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.normedAddCommGroup

instance [SeminormedAddCommGroup α] [NormedSpace 𝕜 α] : NormedSpace 𝕜 (Shrink.{v} α) :=
  (equivShrink α).symm.normedSpace 𝕜

instance [TopologicalSpace α] : TopologicalSpace (Shrink.{v} α) :=
  (equivShrink α).symm.topologicalSpace

variable (R α) in
/-- Shrinking `α` to a smaller universe preserves the continuous module structure. -/
@[simps!]
def continuousLinearEquiv [AddCommMonoid α] [TopologicalSpace α] [Module R α] :
    Shrink.{v} α ≃L[R] α :=
  (equivShrink α).symm.continuousLinearEquiv R

end Shrink
