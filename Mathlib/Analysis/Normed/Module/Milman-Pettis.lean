import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.Dual


variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

open Metric NormedSpace

#check NormedSpace.polar_closedBall (𝕜 := ℝ) (E := E) (zero_lt_one)

#check StrongDual ℝ E

local notation3 "𝓤₀" => closedBall (0 : E) 1
-- local notation3 "𝓤₁" => closedBall (0 : E) 1
local notation3 "𝓤" => closedBall (0 : StrongDual ℝ (StrongDual ℝ E)) 1

-- #check inclusionInDoubleDualLi ℝ
lemma goldstine : closure (StrongDual.toWeakDual '' (inclusionInDoubleDual ℝ E '' 𝓤₀)) = 𝓤 := by
  sorry


-- theorem polar_flip_polar_eq {B : E →ₗ[ℝ] F →ₗ[ℝ] ℝ} {s : Set E} [Nonempty s] :
--     B.flip.polar (B.polar s) = closedAbsConvexHull (E := WeakBilin B) ℝ s := by
--
--
--
--
-- theorem Bourbaki_EVT_4_2_4_5 :
--     (strongDualPairing ℝ E).polar ((strongDualPairing ℝ E).flip.polar 𝓑₀) = 𝓑 := by
