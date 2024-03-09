import Mathlib.InformationTheory.Code.Hom
import Mathlib.Topology.GMetric.IsometryEquiv
import Mathlib.Algebra.Module.Equiv

open GIsometry
open Set Code

variable (T₃:Type*)
variable {α γ :Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]

variable {T:Type*} {gdist:T}
variable {s:Set α}
variable--? [_Code γ gdist s] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1]
  [FunLike T α (α → γ)] [GPseudoMetricClass T α γ] [IsDelone gdist s]
variable {α₂ T₂ :Type*} {gdist₂:T₂} {s₂ : Set α₂}
variable--? [_Code γ gdist₂ s₂] =>
  [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
  [IsDelone gdist₂ s₂]

@[simps!]
def CodeHom.inverse
    (f:CodeHom gdist s gdist₂ s₂) (g:α₂ → α)
    (h : Function.RightInverse g ⇑f) (h₃: ∀ y∈ s₂,g y ∈ s):
  CodeHom gdist₂ s₂ gdist s := {
    f.toGIsometry.inverse g h with
    map_code := by apply h₃
  }

section
variable (gdist s gdist₂ s₂)
structure CodeEquiv [_Code γ gdist s] [_Code γ gdist₂ s₂] extends CodeHom gdist s gdist₂ s₂, GIsometryEquiv gdist gdist₂ where
  invMap_code : ∀ y ∈ s₂, invFun y ∈ s

class CodeEquivClass
    [_Code γ gdist s]
    [_Code γ gdist₂ s₂] [EquivLike T₃ α α₂] [GIsometryClass T₃ gdist gdist₂]
    extends CodeHomClass T₃ gdist s gdist₂ s₂ :Prop where
  invMap_code' : ∀ (φ:T₃), ∀ y∈ s₂, Equiv.invFun φ y ∈ s
end


namespace CodeEquiv

theorem toCodeHom_injective : Function.Injective (
    toCodeHom: CodeEquiv gdist s gdist₂ s₂ → CodeHom gdist s gdist₂ s₂) :=
  fun f g h => (mk.injEq _ _ _ _ _ _ _ _ _ _).mpr
    ⟨h, (Equiv.mk.inj (@Equiv.ext α α₂ f.toGIsometryEquiv g.toGIsometryEquiv (by simp_all))).2⟩

instance instEquivLike : EquivLike (CodeEquiv gdist s gdist₂ s₂) α α₂ := {
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
    (φ:CodeEquiv gdist s gdist₂ s₂)
    (φ₂:CodeEquiv gdist s gdist₂ s₂)
    (h:∀ x, φ x = φ₂ x) : φ = φ₂ := by
  apply DFunLike.ext _ _ h

instance instGIsometryClass :
    GIsometryEquivClass (CodeEquiv gdist s gdist₂ s₂) gdist gdist₂ where
  map_dist' := fun φ => φ.map_dist

instance instCodeEquivClass:
    CodeEquivClass (CodeEquiv gdist s gdist₂ s₂) gdist s gdist₂ s₂ where
  map_code' := fun φ => φ.map_code
  invMap_code' := fun φ => φ.invMap_code


protected def copy (f : CodeEquiv gdist s gdist₂ s₂) (f' : α → α₂)
  (f_inv : α₂ → α) (hf : f' = ↑f) (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) :
    CodeEquiv gdist s gdist₂ s₂ := {
      f.toCodeHom.copy f' hf, f.toGIsometryEquiv.copy f' f_inv hf hf_inv with
      invMap_code := by
        simp_rw [hf, hf_inv]
        exact f.invMap_code
    }

end CodeEquiv

-- not sure if this should be an abbreviation class or not.

variable {T:Type*} [EquivLike T α α₂] [GIsometryClass T gdist gdist₂]
variable [CodeEquivClass T gdist s gdist₂ s₂]

@[coe]
def CodeEquivClass.toCodeEquiv (f : T) : CodeEquiv gdist s gdist₂ s₂:={
  EquivLike.toEquiv f,  GIsometryClass.toGIsometry f with}

instance [GIsometryEquivClass T gdist₁ gdist₂] : CoeTC T (GIsometryEquiv gdist₁ gdist₂) :=
  ⟨GIsometryEquivClass.toGIsometryEquiv⟩


namespace GIsometryEquiv

@[simp]
theorem coe_copy
    (f : CodeEquiv gdist s gdist₂ s₂) (f' : α → α₂) (f_inv : α₂ → α) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f' := rfl

theorem coe_copy_eq
    (f : CodeEquiv gdist s gdist₂ s₂) (f' : α → α₂) (f_inv : α₂ → α) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f := by
  apply DFunLike.ext'
  rw [coe_copy,hf]
end CodeEquiv
