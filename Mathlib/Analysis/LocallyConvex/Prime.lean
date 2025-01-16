import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Analysis.LocallyConvex.Polar

/-!
# Prime map

-/

variable {𝕜 E F : Type*}

variable [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

namespace LinearMap

variable (C : Set E)

/-- The (absolute) polar of `s : Set E` is given by the set of all `y : F` such that `‖B x y‖ ≤ 1`
for all `x ∈ s`. -/
def prime (s : Set E) : Set F :=
  { y : F | y ∈ B.polar C ∧ ∀ x ∈ s, B x y = 1 }

end LinearMap
