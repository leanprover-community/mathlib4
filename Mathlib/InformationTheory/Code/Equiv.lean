import Mathlib.InformationTheory.Code.Hom
import Mathlib.Topology.GMetric.IsometryEquiv
import Mathlib.Algebra.Module.Equiv

namespace Code
open GMetric
open GIsometry
open Set
section code
variable (T₃:Type*)
variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]

variable {T:Type*} (gdist:T)
variable (s:Set α)
variable--? [_Code γ gdist s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] [IsDelone gdist s]
variable {α₂ T₂ :Type*} (gdist₂:T₂)(s₂ : Set α₂)
variable--? [_Code γ gdist₂ s₂] =>
  [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂]

@[simps]
def CodeHom.inverse
    (f:CodeHom gdist s gdist₂ s₂) (g:α₂ → α)
    (h : Function.RightInverse g ⇑f) (h₃: ∀ y∈ s₂,g y ∈ s):
  CodeHom gdist₂ s₂ gdist s := {
    f.toGIsometry.inverse g h with
    map_code := by apply h₃
  }

structure CodeEquiv [_Code γ gdist s] [_Code γ gdist₂ s₂] extends CodeHom gdist s gdist₂ s₂, GIsometryEquiv gdist gdist₂ where
  invMap_code : ∀ y ∈ s₂, invFun y ∈ s

class CodeEquivClass
    [_Code γ gdist s]
    [_Code γ gdist₂ s₂] [EquivLike T₃ α α₂] [GIsometryClass T₃ gdist gdist₂]
    extends CodeHomClass T₃ gdist s gdist₂ s₂ :Prop where
  invMap_code' : ∀ (φ:T₃), ∀ y∈ s₂, Equiv.invFun φ y ∈ s

section
variable {s gdist₂ s₂}
theorem CodeEquiv.toCodeHom_injective : Function.Injective (
    CodeEquiv.toCodeHom: CodeEquiv gdist s gdist₂ s₂ → CodeHom gdist s gdist₂ s₂) :=
  fun f g h => (CodeEquiv.mk.injEq _ _ _ _ _ _ _ _ _ _).mpr
    ⟨h, (Equiv.mk.inj (@Equiv.ext α α₂ f.toGIsometryEquiv g.toGIsometryEquiv (by simp_all))).2⟩
end

instance CodeEquiv.instEquivLike : EquivLike (CodeEquiv gdist s gdist₂ s₂) α α₂ := {
  coe := fun φ => φ.toFun
  inv := fun φ => φ.invFun
  left_inv := fun φ => φ.left_inv
  right_inv := fun φ => φ.right_inv
  coe_injective' := fun φ₁ φ₂ h₁ _ => by
    apply CodeEquiv.toCodeHom_injective
    apply (DFunLike.coe_injective)
    apply h₁
}

@[ext]
lemma CodeEquiv.ext
    (φ:CodeEquiv gdist s gdist₂ s₂)
    (φ₂:CodeEquiv gdist s gdist₂ s₂)
    (h:∀ x, φ x = φ₂ x) : φ = φ₂ := by
  apply DFunLike.ext _ _ h


instance CodeEquiv.instGIsometryClass :
    GIsometryEquivClass (CodeEquiv gdist s gdist₂ s₂) gdist gdist₂ where
  map_dist' := fun φ => φ.map_dist



section
variable {gdist₂ s₂} {T₃ α₃:Type*} {gdist₃:T₃} {s₃:Set α₃}
variable--? [_Code γ gdist₃ s₃] =>
  [FunLike T₃ α₃ (α₃ → γ)] [GPseudoMetricClass T₃ α₃ γ] [IsDelone gdist₃ s₃]
end

variable [EquivLike T₃ α α₂]
  [GIsometryClass T₃ gdist gdist₂]


instance CodeEquiv.instCodeEquivClass:
    CodeEquivClass (CodeEquiv gdist s gdist₂ s₂) gdist s gdist₂ s₂ where
  map_code' := fun φ => φ.map_code
  invMap_code' := fun φ => φ.invMap_code
end code
