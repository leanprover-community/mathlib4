import Mathlib.InformationTheory.Code.Basic
import Mathlib.Topology.GMetric.Isometry

namespace Code


open Set
open GMetric
open GIsometry


variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (. + .) (. ≤ .)]
variable {T:Type*} [FunLike T α (α → γ)] [GMetricClass T α γ] {gdist:T}
variable {s:Set α}
variable (hdelone:IsDelone gdist s)
variable {α₂ :Type*} {T₂:Type*} [FunLike T₂ α₂ (α₂ → γ)] [GMetricClass T₂ α₂ γ] {gdist₂:T₂}
variable {s₂ : Set α₂} (hdelone₂:IsDelone gdist₂ s₂)


@[ext]
structure CodeHom
    (hdelone:IsDelone gdist s) (hdelone₂:IsDelone gdist₂ s₂) extends GIsometry gdist gdist₂ where
  map_code : toGIsometry '' s ⊆ s₂

instance CodeHom.instFunLike : FunLike (CodeHom hdelone hdelone₂) α α₂ where
  coe := fun φ => φ.toGIsometry
  coe_injective' := fun φ₁ φ₂ h => by
    ext y
    simp at h
    rw [h]

instance CodeHom.instGIsometryClass : GIsometryClass (CodeHom hdelone hdelone₂) gdist gdist₂ where
  map_dist := fun φ => φ.map_dist

class CodeHomClass (T₃:Type*) [FunLike T₃ α α₂] (hdelone: IsDelone gdist s)
    (hdelone₂:IsDelone gdist₂ s₂) [GIsometryClass T₃ gdist gdist₂] :Prop where
  map_code : ∀ (φ:T₃), φ '' s ⊆ s₂

instance CodeHom.instCodeHomClass : CodeHomClass (CodeHom hdelone hdelone₂) hdelone hdelone₂ where
  map_code := fun φ => φ.map_code
