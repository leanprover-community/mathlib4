import Mathlib.InformationTheory.Code.Hom

namespace Code
open GMetric
open GIsometry
open Set

variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ] [CovariantClass γ γ (. + .) (. ≤ .)]


variable {T:Type*} [FunLike T α (α → γ)] [GMetricClass T α γ] {gdist:T}
variable {s:Set α}
variable (hdelone:IsDelone gdist s)
variable {α₂ :Type*} {T₂:Type*} [FunLike T₂ α₂ (α₂ → γ)] [GMetricClass T₂ α₂ γ] {gdist₂:T₂}
variable {s₂ : Set α₂} (hdelone₂:IsDelone gdist₂ s₂)

structure CodeEquiv
    (hdelone:IsDelone gdist s) (hdelone₂:IsDelone gdist₂ s₂)
    extends CodeHom hdelone hdelone₂, α ≃ α₂

class CodeEquivClass
    (T₃:Type*) [EquivLike T₃ α α₂] [GIsometryClass T₃ gdist gdist₂]
    (hdelone:IsDelone gdist s) (hdelone₂:IsDelone gdist₂ s₂)
    extends CodeHomClass T₃ hdelone hdelone₂ :Prop
