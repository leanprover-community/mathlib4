import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Complex.Basic

variable {V₁} [SeminormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] (v₁ w₁ : V₁)
variable {V₂} [SeminormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (v₂ w₂ : V₂)
variable {V₃ 𝕜} [RCLike 𝕜] [SeminormedAddCommGroup V₃] [InnerProductSpace 𝕜 V₃] (v₃ w₃ : V₃)

open InnerProductSpace

/-- info: ⟪v₁, w₁⟫ : ℝ -/
#guard_msgs in
#check ⟪v₁, w₁⟫_ℝ

/-- info: ⟪v₂, w₂⟫ : ℂ -/
#guard_msgs in
#check ⟪v₂, w₂⟫_ℂ

/-- info: ⟪v₃, w₃⟫_𝕜 : 𝕜 -/
#guard_msgs in
#check ⟪v₃, w₃⟫_𝕜
