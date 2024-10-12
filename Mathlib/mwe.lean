import Mathlib.Analysis.Normed.Module.WeakDual

variable {𝕜 : Type*} [RCLike 𝕜] --[NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

open Metric
open WeakDual

#check NormedSpace.polar_closedBall

/-
NormedSpace.polar_closedBall.{u_3, u_4} {𝕜 : Type u_3} {E : Type u_4} [RCLike 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {r : ℝ} (hr : 0 < r) : NormedSpace.polar 𝕜 (closedBall 0 r) = closedBall 0 r⁻¹
-/



lemma test2  {r : ℝ} (hr : 0 < r) :
    toNormedDual '' (polar 𝕜 (closedBall (0 : E) r)) = (closedBall (0 ) r⁻¹) := by
  rw [polar]
  rw [Set.image_preimage_eq _ (LinearEquiv.surjective toNormedDual)]
  rw [NormedSpace.polar_closedBall (𝕜 := 𝕜) (E := E) hr]


lemma test [RCLike 𝕜] (n : ℕ) : toNormedDual '' (polar 𝕜 (closedBall 0 ((n+1)⁻¹ : ℝ))) = (closedBall (0 : NormedSpace.Dual 𝕜 E) (n+1)) := by
  rw [polar]
  rw [Set.image_preimage_eq]
  have e1 : (n+1 : ℝ)⁻¹ > 0 := by exact Nat.inv_pos_of_nat
  have e2 : (n+1 : ℝ) > 0 := by exact Nat.cast_add_one_pos n
  rw [NormedSpace.polar_closedBall (𝕜 := 𝕜) e]
