import Mathlib.InformationTheory.Code.Hom
import Mathlib.Topology.GMetric.IsometryEquiv
import Mathlib.Algebra.Module.Equiv

open GIsometry
open Set Code

variable {T:Type*}
variable {α₁ γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]

variable {T₁:Type*} {gdist₁:T₁}
variable {s₁:Set α₁}
variable--? [_Code γ gdist s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [FunLike T₁ α₁ (α₁ → γ)] [GPseudoMetricClass T₁ α₁ γ] [IsDelone gdist₁ s₁]
variable {α₂ T₂ :Type*} {gdist₂:T₂} {s₂ : Set α₂}
variable--? [_Code γ gdist₂ s₂] =>
  [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂]

@[simps!]
def CodeHom.inverse
    (f:CodeHom gdist₁ s₁ gdist₂ s₂) (g:α₂ → α₁)
    (h : Function.RightInverse g ⇑f) (h₃: ∀ y∈ s₂,g y ∈ s₁):
  CodeHom gdist₂ s₂ gdist₁ s₁ := {
    f.toGIsometry.inverse g h with
    map_code := by apply h₃
  }

section
variable (T gdist₁ s₁ gdist₂ s₂)

structure CodeEquiv [_Code γ gdist₁ s₁] [_Code γ gdist₂ s₂]
    extends CodeHom gdist₁ s₁ gdist₂ s₂, GIsometryEquiv gdist₁ gdist₂ where
  invMap_code : ∀ y ∈ s₂, invFun y ∈ s₁

class CodeEquivClass {γ :outParam Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]
    [CovariantClass γ γ (.+.) (.≤.)]
    {T₁ T₂ α₁ α₂:outParam Type*} [FunLike T₁ α₁ (α₁ → γ)] [GPseudoMetricClass T₁ α₁ γ]
    (gdist₁:outParam T₁) (s₁: outParam (Set α₁)) [IsDelone gdist₁ s₁] [_Code γ gdist₁ s₁]
    [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
    (gdist₂:outParam T₂) (s₂: outParam (Set α₂)) [IsDelone gdist₂ s₂] [_Code γ gdist₂ s₂]
    [EquivLike T α₁ α₂] [GIsometryClass T gdist₁ gdist₂] [_GIsometryEquivClass T gdist₁ gdist₂]
    extends CodeHomClass T gdist₁ s₁ gdist₂ s₂ :Prop where
  invMap_code' : ∀ (φ:T), ∀ y∈ s₂, (GIsometryEquiv.symm (φ:GIsometryEquiv gdist₁ gdist₂)) y ∈ s₁
end

-- theorem CodeEquivClass.invMap_code' : ∀ (φ:T), ∀ y∈ s₂, Equiv.invFun
namespace CodeEquiv

theorem toCodeHom_injective : Function.Injective (
    toCodeHom: CodeEquiv gdist₁ s₁ gdist₂ s₂ → CodeHom gdist₁ s₁ gdist₂ s₂) :=
  fun f g h => (mk.injEq _ _ _ _ _ _ _ _ _ _).mpr
    ⟨h, (Equiv.mk.inj (@Equiv.ext α₁ α₂ f.toGIsometryEquiv g.toGIsometryEquiv (by simp_all))).2⟩

instance instEquivLike : EquivLike (CodeEquiv gdist₁ s₁ gdist₂ s₂) α₁ α₂ := {
  coe := fun φ => φ.toFun
  inv := fun φ => φ.invFun
  left_inv := fun φ => φ.left_inv
  right_inv := fun φ => φ.right_inv
  coe_injective' := fun φ₁ φ₂ h₁ _ => by
    apply toCodeHom_injective
    apply (DFunLike.coe_injective)
    apply h₁
}

@[ext]
lemma ext
    (φ:CodeEquiv gdist₁ s₁ gdist₂ s₂)
    (φ₂:CodeEquiv gdist₁ s₁ gdist₂ s₂)
    (h:∀ x, φ x = φ₂ x) : φ = φ₂ := by
  apply DFunLike.ext _ _ h

instance instGIsometryClass :
    GIsometryClass (CodeEquiv gdist₁ s₁ gdist₂ s₂) gdist₁ gdist₂ where
  map_dist' := fun φ => φ.map_dist

instance instCodeEquivClass:
    CodeEquivClass (CodeEquiv gdist₁ s₁ gdist₂ s₂) gdist₁ s₁ gdist₂ s₂ where
  map_code' := fun φ => φ.map_code
  invMap_code' := fun φ => φ.invMap_code


protected def copy (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂)
  (f_inv : α₂ → α₁) (hf : f' = ↑f) (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) :
    CodeEquiv gdist₁ s₁ gdist₂ s₂ := {
      f.toCodeHom.copy f' hf, f.toGIsometryEquiv.copy f' f_inv hf hf_inv with
      invMap_code := by
        simp_rw [hf, hf_inv]
        exact f.invMap_code
    }

end CodeEquiv

variable [EquivLike T α₁ α₂] [GIsometryClass T gdist₁ gdist₂]
variable [CodeEquivClass T gdist₁ s₁ gdist₂ s₂]

@[coe]
def CodeEquivClass.toCodeEquiv [CodeEquivClass T gdist₁ s₁ gdist₂ s₂] (f : T) :
  CodeEquiv gdist₁ s₁ gdist₂ s₂:= {
    CodeHomClass.toCodeHom f, _GIsometryEquivClass.toGIsometryEquiv f with
    invMap_code := CodeEquivClass.invMap_code' f
  }

instance [GIsometryClass T gdist₁ gdist₂] [CodeEquivClass T gdist₁ s₁ gdist₂ s₂]:
  CoeTC T (CodeEquiv gdist₁ s₁ gdist₂ s₂) := ⟨CodeEquivClass.toCodeEquiv⟩


namespace CodeEquiv

@[simp]
theorem coe_copy
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂) (f_inv : α₂ → α₁) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f' := rfl

theorem coe_copy_eq
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂) (f_inv : α₂ → α₁) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f := by
  apply DFunLike.ext'
  rw [coe_copy,hf]
end CodeEquiv
