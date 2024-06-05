import Mathlib.InformationTheory.Code.Hom
import Mathlib.Topology.GMetric.IsometryEquiv
import Mathlib.Algebra.Module.Equiv

open GIsometry
open Set Code GMetric

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
    extends GIsometryEquiv gdist₁ gdist₂,CodeHom gdist₁ s₁ gdist₂ s₂ where
  invMap_code : ∀ x, toFun x ∈ s₂ → x ∈ s₁

-- preferably `extends GIsometryEquivClass ..., CodeHomClass ...` but sadly the kernel doesnt' like that.
class CodeEquivClass {γ :outParam Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]
    [CovariantClass γ γ (.+.) (.≤.)]
    {T₁ T₂ α₁ α₂:outParam Type*} [FunLike T₁ α₁ (α₁ → γ)] [GPseudoMetricClass T₁ α₁ γ]
    (gdist₁:outParam T₁) (s₁: outParam (Set α₁)) [IsDelone gdist₁ s₁] [_Code γ gdist₁ s₁]
    [FunLike T₂ α₂ (α₂ → γ)] [GPseudoMetricClass T₂ α₂ γ]
    (gdist₂:outParam T₂) (s₂: outParam (Set α₂)) [IsDelone gdist₂ s₂] [_Code γ gdist₂ s₂]
    [EquivLike T α₁ α₂]
    extends CodeHomClass T gdist₁ s₁ gdist₂ s₂ where
  invMap_code' : ∀ (φ:T), ∀ x, φ x ∈ s₂ → x ∈ s₁

instance CodeEquivClass.toGIsometryEquivClass
    {T:Type*} {γ : outParam Type*} [CompleteLinearOrder γ] [AddCommMonoid γ]
    [CovariantClass γ γ (.+.) (.≤.)] {α₁ : outParam Type*} {T₁: outParam Type*}
    {gdist₁ : outParam T₁} {s₁:outParam (Set α₁)} [FunLike T₁ α₁ (α₁ → γ)]
    [GPseudoMetricClass T₁ α₁ γ] [IsDelone gdist₁ s₁] {α₂: outParam Type*} {T₂: outParam Type*}
    {gdist₂ : outParam T₂} {s₂:outParam (Set α₂)} [FunLike T₂ α₂ (α₂ → γ)]
    [GPseudoMetricClass T₂ α₂ γ] [IsDelone gdist₂ s₂] [EquivLike T α₁ α₂]
    [CodeEquivClass T gdist₁ s₁ gdist₂ s₂]:
    GIsometryEquivClass T gdist₁ gdist₂ where
      map_dist' := fun f => GIsometryClass.map_dist' f

end

-- theorem CodeEquivClass.invMap_code' : ∀ (φ:T), ∀ y∈ s₂, Equiv.invFun
namespace CodeEquiv
instance : EquivLike (CodeEquiv gdist₁ s₁ gdist₂ s₂) α₁ α₂ where
      coe := fun φ => φ.toFun
      inv := fun φ => φ.invFun
      left_inv := fun φ => φ.left_inv
      right_inv := fun φ => φ.right_inv
      coe_injective' := fun φ₁ φ₂ h₁ _ => by cases φ₁; cases φ₂; congr; simp_all

instance instCodeEquivClass: CodeEquivClass (CodeEquiv gdist₁ s₁ gdist₂ s₂) gdist₁ s₁ gdist₂ s₂ where
    map_dist' := fun φ => φ.map_dist
    map_code' := fun φ => φ.map_code
    invMap_code' := fun φ => φ.invMap_code

@[ext]
lemma ext ⦃φ φ₂:CodeEquiv gdist₁ s₁ gdist₂ s₂⦄ (h:∀ x, φ x = φ₂ x) :
  φ = φ₂ := DFunLike.ext _ _ h

protected def copy (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂)
  (f_inv : α₂ → α₁) (hf : f' = ↑f) (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) :
    CodeEquiv gdist₁ s₁ gdist₂ s₂ := {
      f.toCodeHom.copy f' hf, f.toGIsometryEquiv.copy f' f_inv hf hf_inv with
      invMap_code := by
        simp_rw [hf]
        exact f.invMap_code
    }

end CodeEquiv

variable [EquivLike T α₁ α₂] [CodeEquivClass T gdist₁ s₁ gdist₂ s₂]

@[coe]
def CodeEquivClass.toCodeEquiv [CodeEquivClass T gdist₁ s₁ gdist₂ s₂] (f : T) :
  CodeEquiv gdist₁ s₁ gdist₂ s₂:= {
    CodeHomClass.toCodeHom f, GIsometryEquivClass.toGIsometryEquiv f with
    invMap_code := CodeEquivClass.invMap_code' f
  }

instance [CodeEquivClass T gdist₁ s₁ gdist₂ s₂]:
  CoeTC T (CodeEquiv gdist₁ s₁ gdist₂ s₂) := ⟨CodeEquivClass.toCodeEquiv⟩


namespace CodeEquiv

@[simp]
theorem toGIsometryEquiv_eq_coe (f :CodeEquiv gdist₁ s₁ gdist₂ s₂) : f.toGIsometryEquiv = f :=
  rfl

@[simp]
theorem toCodeHom_eq_coe (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : f.toCodeHom = ↑f :=
  rfl

@[simp]
theorem coe_toGIsometryEquiv (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : ⇑(f : GIsometryEquiv gdist₁ gdist₂) = f := rfl

@[simp 1100]
theorem coe_toCodeHom {f : CodeEquiv gdist₁ s₁ gdist₂ s₂} : (f.toCodeHom : α₁ → α₂) = f := rfl

def mk'
    (f : GIsometryEquiv gdist₁ gdist₂)
    (h : ∀ x, f x ∈ s₂ ↔ x ∈ s₁) :
    CodeEquiv gdist₁ s₁ gdist₂ s₂ := ⟨f,fun x => (h x).mpr,fun x => (h x).mp⟩

protected theorem bijective
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : Function.Bijective f :=
  EquivLike.bijective f

protected theorem injective
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : Function.Injective f :=
  EquivLike.injective f

protected theorem surjective
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : Function.Surjective f :=
  EquivLike.surjective f


@[refl]
def refl (gdist₁ : T₁) (s₁: Set α₁) [IsDelone gdist₁ s₁] [_Code γ gdist₁ s₁]:
  CodeEquiv gdist₁ s₁ gdist₁ s₁ := {
    GIsometryEquiv.refl gdist₁ with
    map_code := fun _ h => h
    invMap_code := fun _ h => h}

instance : Inhabited (CodeEquiv gdist₁ s₁ gdist₁ s₁) := ⟨refl gdist₁ s₁⟩

@[symm]
def symm (h : CodeEquiv gdist₁ s₁ gdist₂ s₂) : CodeEquiv gdist₂ s₂ gdist₁ s₁ := {
  h.toGIsometryEquiv.symm with
  map_code := fun x hx => h.invMap_code (h.invFun x) ((h.right_inv x).symm ▸ hx)
  invMap_code := fun x hx => (h.right_inv x) ▸ h.map_code (h.invFun x) hx
}

theorem invFun_eq_symm {f : CodeEquiv gdist₁ s₁ gdist₂ s₂} : f.invFun = f.symm := rfl

@[simp]
theorem coe_toGIsometryEquiv_symm (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) :
  ((f : GIsometryEquiv gdist₁ gdist₂).symm : α₂→ α₁) = f.symm := rfl

@[simp]
theorem equivLike_inv_eq_symm (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) :
  EquivLike.inv f = f.symm := rfl

@[simp]
theorem toGIsometryEquiv_symm (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) :
  (f.symm : GIsometryEquiv gdist₂ gdist₁) = (f : GIsometryEquiv gdist₁ gdist₂).symm := rfl

@[simp]
theorem coe_mk
    (f : GIsometryEquiv gdist₁ gdist₂) (map_code : ∀ x, x ∈ s₁ → f x ∈ s₂)
    (invMap_code : ∀ x, f x ∈ s₂ → x ∈ s₁):
    (CodeEquiv.mk f map_code invMap_code : α₁ → α₂) = f := rfl

@[simp]
theorem symm_symm (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : f.symm.symm = f := rfl

theorem symm_bijective :
    Function.Bijective
      (symm : (CodeEquiv gdist₁ s₁ gdist₂ s₂) → CodeEquiv gdist₂ s₂ gdist₁ s₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_mk
    (f : GIsometryEquiv gdist₁ gdist₂) (map_code : ∀ x, x ∈ s₁ → f x ∈ s₂)
    (invMap_code : ∀ x, f x ∈ s₂ → x ∈ s₁):
    (mk f map_code invMap_code).symm = ⟨f.symm,
      fun x hx => by
        apply (invMap_code (f.invFun x))
        apply ((f.right_inv x).symm ▸ hx),
      fun x hx => f.right_inv x ▸ map_code (f.invFun x) hx
      ⟩ := rfl

@[simp]
theorem refl_symm : (refl gdist₁ s₁).symm = refl gdist₁ s₁ := rfl

@[simp]
theorem coe_copy
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂) (f_inv : α₂ → α₁) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f' := rfl

theorem coe_copy_eq
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f' : α₁ → α₂) (f_inv : α₂ → α₁) (hf : f' = ↑f)
    (hf_inv : f_inv = ⇑f.toGIsometryEquiv.symm) : (f.copy f' f_inv hf hf_inv) = f := by
  apply DFunLike.ext'
  rw [coe_copy,hf]

variable {T₃ α₃:Type*} {gdist₃:T₃} {s₃:Set α₃} [FunLike T₃ α₃ (α₃ → γ)] [GPseudoMetricClass T₃ α₃ γ]
variable--? [_Code γ gdist₃ s₃] =>
  [IsDelone gdist₃ s₃]

@[trans]
def trans (h1 : CodeEquiv gdist₁ s₁ gdist₂ s₂) (h2 : CodeEquiv gdist₂ s₂ gdist₃ s₃) :
    CodeEquiv gdist₁ s₁ gdist₃ s₃ :=
  { h1.toGIsometryEquiv.trans h2.toGIsometryEquiv, h2.toCodeHom.comp h1.toCodeHom with
    invMap_code := fun x => h1.invMap_code x ∘ h2.invMap_code (h1 x)
  }


@[simp]
theorem apply_symm_apply (f : CodeEquiv gdist₁ s₁ gdist₂ s₂ ) (y : α₂) : f (f.symm y) = y :=
  f.toEquiv.apply_symm_apply y

@[simp]
theorem symm_apply_apply (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (x : α₁) : f.symm (f x) = x :=
  f.toEquiv.symm_apply_apply x

@[simp]
theorem symm_comp_self (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : f.symm ∘ f = _root_.id :=
  funext f.symm_apply_apply

@[simp]
theorem self_comp_symm (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) : f ∘ f.symm = _root_.id :=
  funext f.apply_symm_apply

@[simp]
theorem coe_refl : ↑(refl gdist₁ s₁) = _root_.id := rfl

@[simp]
theorem refl_apply (x : α₁) : refl gdist₁ s₁ x = x := rfl

@[simp]
theorem coe_trans
    (f₁ : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f₂ : CodeEquiv gdist₂ s₂ gdist₃ s₃) :
  ↑(f₁.trans f₂) = f₂ ∘ f₁ := rfl

@[simp]
theorem trans_apply
    (f₁ : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f₂ : CodeEquiv gdist₂ s₂ gdist₃ s₃) (x : α₁) :
    f₁.trans f₂ x = f₂ (f₁ x) := rfl

@[simp]
theorem symm_trans_apply
    (f₁ : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f₂ : CodeEquiv gdist₂ s₂ gdist₃ s₃) (y : α₃) :
    (f₁.trans f₂).symm y = f₁.symm (f₂.symm y) := rfl

-- simp can prove this
theorem apply_eq_iff_eq
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) {x y : α₁} :
  f x = f y ↔ x = y := f.injective.eq_iff

theorem apply_eq_iff_symm_apply
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) {x : α₁} {y : α₂} :
  f x = y ↔ x = f.symm y := f.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) {x y} :
  f.symm x = y ↔ x = f y := f.toEquiv.symm_apply_eq

theorem eq_symm_apply
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) {x y} :
  y = f.symm x ↔ f y = x := f.toEquiv.eq_symm_apply

theorem eq_comp_symm
    {α : Type*} (e : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f : α₂ → α) (g : α₁ → α) :
  f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

theorem comp_symm_eq
    {α : Type*} (e : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f : α₂ → α) (g : α₁ → α) :
  g ∘ e.symm = f ↔ g = f ∘ e := e.toEquiv.comp_symm_eq f g

theorem eq_symm_comp
    {α : Type*} (e : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f : α → α₁) (g : α → α₂) :
  f = e.symm ∘ g ↔ e ∘ f = g := e.toEquiv.eq_symm_comp f g

theorem symm_comp_eq
    {α : Type*} (e : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f : α → α₁) (g : α → α₂) :
  e.symm ∘ g = f ↔ g = e ∘ f := e.toEquiv.symm_comp_eq f g

@[simp]
theorem symm_trans_self
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂):
  f.symm.trans f = refl gdist₂ s₂ := DFunLike.ext _ _ f.apply_symm_apply

@[simp]
theorem self_trans_symm
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) :
  f.trans f.symm = refl gdist₁ s₁ := DFunLike.ext _ _ f.symm_apply_apply

theorem ext_iff {f g : CodeEquiv gdist₁ s₁ gdist₂ s₂} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff

@[simp]
theorem mk_coe
    (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (f' h₁ h₂ h₃ h₄ h₅) :
  (⟨⟨⟨f,f',h₁,h₂⟩,h₃⟩,h₄,h₅⟩ : CodeEquiv gdist₁ s₁ gdist₂ s₂) = f := ext fun _ => rfl

@[simp]
theorem mk_coe' (f : CodeEquiv gdist₁ s₁ gdist₂ s₂) (g h₁ h₂ h₃ h₄ h₅) :
    (CodeEquiv.mk ⟨⟨g, f, h₁, h₂⟩,h₃⟩ h₄ h₅ : CodeEquiv gdist₂ s₂ gdist₁ s₁) = f.symm :=
  symm_bijective.injective <| ext fun _ => rfl

protected theorem congr_arg
    {f : CodeEquiv gdist₁ s₁ gdist₂ s₂} {x x' : α₁} :
  x = x' → f x = f x' := DFunLike.congr_arg f

protected theorem congr_fun
    {f g : CodeEquiv gdist₁ s₁ gdist₂ s₂} (h : f = g) (x : α₁) :
  f x = g x := DFunLike.congr_fun h x

end CodeEquiv
