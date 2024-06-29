import Mathlib.Algebra.Category.ModuleCatNew.Basic

universe v u u' u''

open CategoryTheory

attribute [local instance] ConcreteCategory.instFunLike

namespace ModuleCatNew

section RestrictScalars

variable {A : Type u} {B : Type u'} {C : Type u''} [Ring A] [Ring B] [Ring C]

section

variable (φ : A →+* B)

def restrictScalars  : ModuleCatNew.{v} B ⥤ ModuleCatNew.{v} A where
  obj M :=
    { carrier := M
      module := Module.compHom M φ }
  map {M₁ M₂} f :=
    { linearMap :=
        letI := Module.compHom M₁ φ
        letI := Module.compHom M₂ φ
        { f.linearMap with map_smul' := fun r ↦ f.linearMap.map_smul (φ r) } }

@[simp]
lemma restrictScalars_obj_coe (M : ModuleCatNew.{v} B) :
    ((restrictScalars φ).obj M : Type v) = M := rfl

@[simp]
lemma restrictScalars_map {M₁ M₂ : ModuleCatNew.{v} B} (f : M₁ ⟶ M₂) (x : M₁) :
    (restrictScalars φ).map f x = f x := rfl

example (M : ModuleCatNew.{v} B) :
    (restrictScalars φ).map (𝟙 M) = 𝟙 _ := by ext; dsimp

end

section

variable {φ : A →+* A} (hφ : φ = RingHom.id A)

def restrictScalarsId : restrictScalars.{v} φ ≅ 𝟭 _ := eqToIso (by subst hφ; rfl)

@[simp]
lemma restrictScalarsId_hom_app_apply {M : ModuleCatNew.{v} A} (x : M) :
    letI α : _ ⟶ M := (restrictScalarsId hφ).hom.app M
    α x = x := by subst hφ; rfl

@[simp]
lemma restrictScalarsId_inv_app_apply {M : ModuleCatNew.{v} A} (x : M) :
    letI α : M ⟶ _ := (restrictScalarsId hφ).inv.app M
    α x = x := by subst hφ; rfl

end

section

variable {φ : A →+* B} {ψ : B →+* C} {φψ : A →+* C} (h : φψ = ψ.comp φ)

def restrictScalarsComp :
    restrictScalars.{v} φψ ≅ restrictScalars.{v} ψ ⋙ restrictScalars.{v} φ :=
  eqToIso (by subst h; rfl)

@[simp]
lemma restrictScalarsComp_hom_app_apply {M : ModuleCatNew.{v} C} (x : M) :
    letI α : _ ⟶ (restrictScalars φ).obj ((restrictScalars ψ).obj M) :=
      (restrictScalarsComp h).hom.app M
    α x = x := by subst h; rfl

@[simp]
lemma restrictScalarsComp_inv_app_apply {M : ModuleCatNew.{v} C} (x : M) :
    letI α : (restrictScalars φ).obj ((restrictScalars ψ).obj M) ⟶ _ :=
      (restrictScalarsComp h).inv.app M
    α x = x := by subst h; rfl

end

end RestrictScalars

end ModuleCatNew
