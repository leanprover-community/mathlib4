import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Algebra.Order.Nonneg.Ring

variable {𝕜 : Type*} [OrderedSemiring 𝕜]

variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {F : Type*} [AddCommMonoid F] [Module 𝕜 F]

instance : Module { c : 𝕜 // 0 ≤ c } E := Module.compHom E (@Nonneg.coeRingHom 𝕜 _)
instance : IsScalarTower { c : 𝕜 // 0 ≤ c } 𝕜 E := SMul.comp.isScalarTower ↑Nonneg.coeRingHom

example (f : E →ₗ[𝕜] F) : E →ₗ[{ c : 𝕜 // 0 ≤ c }] F := LinearMap.restrictScalars { c : 𝕜 // 0 ≤ c } f
