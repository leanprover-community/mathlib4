import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Group.AddTorsor

/-!
# Barycentric coordinates are smooth
-/

public section

variable {ι 𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [MetricSpace P] [NormedAddTorsor E P]
variable [FiniteDimensional 𝕜 E]

theorem smooth_barycentric_coord (b : AffineBasis ι 𝕜 E) (i : ι) : ContDiff 𝕜 ⊤ (b.coord i) :=
  (⟨b.coord i, continuous_barycentric_coord b i⟩ : E →ᴬ[𝕜] 𝕜).contDiff
