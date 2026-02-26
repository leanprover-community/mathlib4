/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Normed.Module.TransferInstance

/-!
# Transfer normed algebraic structures from `α` to `Shrink α`
-/

@[expose] public section

noncomputable section

namespace Shrink

universe v
variable {R 𝕜 α : Type*} [Small.{v} α] [Semiring R] [NormedField 𝕜]

instance [AddCommGroup α] [SeminormedAddCommGroup α] : SeminormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.seminormedAddCommGroup

instance [AddCommGroup α] [NormedAddCommGroup α] : NormedAddCommGroup (Shrink.{v} α) :=
  (equivShrink α).symm.normedAddCommGroup

instance [AddCommGroup α] [SeminormedAddCommGroup α] [NormedSpace 𝕜 α] : NormedSpace 𝕜 (Shrink.{v} α) :=
  (equivShrink α).symm.normedSpace 𝕜

end Shrink
