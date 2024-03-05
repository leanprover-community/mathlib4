import Mathlib.Topology.GMetric.Basic

namespace GIsometry
open GMetric

variable {α₁ α₂ γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]
variable [CovariantClass γ γ (. + .) (. ≤ .)] {T₁ T₂:Type*} [FunLike T₁ α₁ (α₁ → γ)]
variable [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₁ α₁ γ] [GPseudoMetricClass T₂ α₂ γ]

@[ext]
structure GIsometry (gdist₁:T₁) (gdist₂:T₂) :=
  toFun : α₁ → α₂
  map_dist :∀ x y, gdist₁ x y = (gdist₂ (toFun x) (toFun y))

instance GIsometry.instFunLike (gdist₁:T₁) (gdist₂:T₂) :FunLike (GIsometry gdist₁ gdist₂) α₁ α₂ where
  coe := toFun
  coe_injective' := by
    intro φ₁ φ₂ heq
    ext z
    rw [heq]

class GIsometryClass (T₃:Type*) [FunLike T₃ α₁ α₂] (gdist₁: T₁) (gdist₂: T₂) where
  map_dist : ∀ φ:T₃,∀ x y, ⇑gdist₁ x y = ⇑gdist₂ (φ x) (φ y)

instance GIsometry.instGIsometryClass
    (gdist₁:T₁) (gdist₂:T₂): GIsometryClass (GIsometry gdist₁ gdist₂) gdist₁ gdist₂ where
      map_dist := GIsometry.map_dist
