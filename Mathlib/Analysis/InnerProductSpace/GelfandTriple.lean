/-
Copyright (c) 2026 Michał Pacholski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Pacholski
-/
module

public import Mathlib.Analysis.LocallyConvex.Nuclear
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Gelfand Triple
-/

@[expose] public section

open ContinuousLinearMap InnerProductSpace

variable (𝕜 Φ H : Type*)

variable [RCLike 𝕜]
variable [TopologicalSpace Φ] [AddCommGroup Φ] [Module 𝕜 Φ] [NuclearSpace 𝕜 Φ]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

structure GelfandTriple where
  inclusion : Φ →L[𝕜] H
  injective : Function.Injective inclusion
  dense : DenseRange inclusion

namespace GelfandTriple

variable {𝕜 Φ H}

/-- Maps an element of the Hilbert space to a continuous conjugate-linear functional on `Φ`.
By mapping into the antidual, this embedding operator itself is purely linear. -/
noncomputable def toAntidual (T : GelfandTriple 𝕜 Φ H) : H →L[𝕜] (Φ →SL[starRingEnd 𝕜] 𝕜) where
  toFun x := {
    toFun := fun φ ↦ ⟪ T.inclusion φ, x⟫_𝕜
    map_add' := fun φ₁ φ₂ ↦ by simp [inner_add_left]
    map_smul' := fun c φ ↦ by simp [inner_smul_left]
    cont := Continuous.inner T.inclusion.continuous continuous_const
  }
  map_add' x y := by ext φ; simp [inner_add_right]
  map_smul' c x := by ext φ; simp [inner_smul_right]
  cont := by
    sorry

omit [NuclearSpace 𝕜 Φ] [CompleteSpace H] in
theorem toAntidual_apply (T : GelfandTriple 𝕜 Φ H) (x : H) (φ : Φ) :
    T.toAntidual x φ = ⟪T.inclusion φ, x⟫_𝕜 := rfl

end GelfandTriple
