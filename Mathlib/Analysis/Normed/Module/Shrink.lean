/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Transfer normed algebraic structures from `α` to `Shrink α`
-/

public section

noncomputable section

namespace Shrink

universe v
variable {R 𝕜 α : Type*} [Small.{v} α] [Semiring R] [NormedField 𝕜]

instance [NormPseudoMetric α] : NormPseudoMetric (Shrink.{v} α) :=
  (equivShrink α).symm.normPseudoMetric

instance [NormMetric α] : NormMetric (Shrink.{v} α) :=
  (equivShrink α).symm.normMetric

instance [NormPseudoMetric α] [AddCommGroup α] [IsNormedAddGroup α] : IsNormedAddGroup (Shrink.{v} α) :=
  (equivShrink α).symm.isNormedAddGroup

instance [NormPseudoMetric α] [AddCommGroup α] [IsNormedAddGroup α] [NormedSpace 𝕜 α] : NormedSpace 𝕜 (Shrink.{v} α) :=
  (equivShrink α).symm.normedSpace 𝕜

end Shrink
