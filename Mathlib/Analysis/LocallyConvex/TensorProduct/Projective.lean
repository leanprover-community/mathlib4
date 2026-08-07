module

public import Mathlib.Analysis.Normed.Module.TensorProduct.ProjectiveSeminorm
public import Mathlib.Topology.Algebra.Module.TensorProduct.Projective

import Mathlib.Analysis.Seminorm

@[expose] public section

open TensorProduct Seminorm NNReal WithSeminorms

variable {𝕜 X Y : Type*}

variable [NormedField 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X] [PolynormableSpace 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y] [TopologicalSpace Y] [PolynormableSpace 𝕜 Y]

variable {ιX ιY : Type*}

variable (p : SeminormFamily 𝕜 X ιX) (q : SeminormFamily 𝕜 Y ιY)

noncomputable def ProjectiveSeminormFamily : SeminormFamily 𝕜 (X ⊗[𝕜]π Y) (ιX × ιY) := fun ⟨i, j⟩ ↦
  letI := AddGroupSeminorm.toSeminormedAddCommGroup (p i).toAddGroupSeminorm
  letI := AddGroupSeminorm.toSeminormedAddCommGroup (q j).toAddGroupSeminorm
  letI : NormedSpace 𝕜 X := ⟨fun a b ↦ ((p i).smul' a b).le⟩
  letI : NormedSpace 𝕜 Y := ⟨fun a b ↦ ((q j).smul' a b).le⟩
  projectiveSeminorm




-- /-- The projective tensor topology is strictly induced by the projective seminorm family. -/
-- theorem withSeminorms_projectiveTensorProduct :
--     WithSeminorms (ProjectiveSeminormFamily p q) (topology := instTopologicalSpaceProjectiveTensorProduct) := by
--   sorry
