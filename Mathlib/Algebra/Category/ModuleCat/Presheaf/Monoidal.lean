/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The monoidal category structure on presheaves of modules

-/

noncomputable section

open CategoryTheory MonoidalCategory Category

universe v u v₁ u₁

-- when cleaned up, this part should be moved to `ModuleCat.Monoidal.Basic`
namespace ModuleCat

variable {R : Type u} [CommRing R] {F G H K : ModuleCat.{u} R}

section

variable (f : F → G → H) (h₁ : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (h₂ : ∀ (a : R) m n, f (a • m) n = a • f m n)
  (h₃ : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (h₄ : ∀ (a : R) m n, f m (a • n) = a • f m n)

def tensorLift : F ⊗ G ⟶ H := TensorProduct.lift (LinearMap.mk₂ R f h₁ h₂ h₃ h₄)

@[simp]
lemma tensorLift_apply (m : F) (n : G) :
    tensorLift f h₁ h₂ h₃ h₄ (m ⊗ₜ n) = f m n := rfl

end

lemma tensor_ext {f g : F ⊗ G ⟶ H} (h : ∀ m n, f (m ⊗ₜ n) = g (m ⊗ₜ n)) :
    f = g :=
  TensorProduct.ext (by ext; apply h)

@[simp]
lemma tensorHom_tmul (f : F ⟶ G) (g : H ⟶ K) (a : F) (b : H) :
    (f ⊗ g) (a ⊗ₜ b) = f a ⊗ₜ g b := rfl

lemma tensor_ext₃' {f g : (F ⊗ G) ⊗ H ⟶ K} (h : ∀ m n p, f (m ⊗ₜ n ⊗ₜ p) = g (m ⊗ₜ n ⊗ₜ p)) :
    f = g :=
  TensorProduct.ext_threefold h

end ModuleCat

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

instance (X : Cᵒᵖ) : CommRing ((R ⋙ forget₂ _ RingCat).obj X) :=
  inferInstanceAs (CommRing (R.obj X))

namespace PresheafOfModules

namespace Monoidal

variable (F G H K : PresheafOfModules (R ⋙ forget₂ _ _))

def tensorObj' :
    BundledCorePresheafOfModules (R ⋙ forget₂ _ _) where
  obj X := F.obj' X ⊗ G.obj' X
  map {X Y} f := ModuleCat.tensorLift (fun x y ↦ (F.map f x) ⊗ₜ (G.map f y))
    (by intros; dsimp; rw [map_add, TensorProduct.add_tmul])
    (by intros; dsimp; erw [F.map_smul]; rfl)
    (by intros; dsimp; rw [map_add, TensorProduct.tmul_add])
    (by intros; dsimp; simp; rfl)
  map_id X := ModuleCat.tensor_ext (by intros; dsimp; simp; rfl)
  map_comp f g := ModuleCat.tensor_ext (by intros; dsimp; simp; rfl)

def tensorObj : PresheafOfModules (R ⋙ forget₂ _ _) :=
  (tensorObj' F G).toPresheafOfModules

variable {F G H K}

@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ}
    (x : F.obj' X) (y : G.obj' X) (f : X ⟶ Y) :
    (tensorObj F G).map f (x ⊗ₜ[R.obj X] y) = (F.map f x) ⊗ₜ[R.obj Y] (G.map f y) := rfl

lemma tensorHom_aux (f : F ⟶ H) (g : G ⟶ K) {X Y : Cᵒᵖ} (φ : X ⟶ Y) :
    restrictionApp φ (tensorObj F G) ≫
      (ModuleCat.restrictScalars ((R ⋙ forget₂ _ RingCat).map φ)).map
        (Hom.app' f Y ⊗ Hom.app' g Y) =
      (Hom.app' f X ⊗ Hom.app' g X) ≫ restrictionApp φ (tensorObj H K) := by
  apply ModuleCat.tensor_ext
  intro a b
  change (Hom.app' f Y ⊗ Hom.app' g Y) (F.map φ a ⊗ₜ[R.obj Y] G.map φ b) =
    (H.map φ (Hom.app f X a)) ⊗ₜ[R.obj Y] (K.map φ (Hom.app g X b))
  erw [ModuleCat.tensorHom_tmul]
  congr 1
  all_goals apply naturality_apply

def tensorHom (f : F ⟶ H) (g : G ⟶ K) :
    tensorObj F G ⟶ tensorObj H K :=
  Hom.mk'' (fun X ↦ Hom.app' f X ⊗ Hom.app' g X)
    (by intros; apply tensorHom_aux)

variable (F)

def whiskerLeft (g : G ⟶ H) : tensorObj F G ⟶ tensorObj F H :=
  Hom.mk'' (fun X ↦ F.obj' X ◁ Hom.app' g X)
    (fun _ _ φ ↦ tensorHom_aux (𝟙 F) g φ)

variable {F}

def whiskerRight (f : F ⟶ G) (H : PresheafOfModules (R ⋙ forget₂ _ _)) :
    tensorObj F H ⟶ tensorObj G H :=
  Hom.mk'' (fun X ↦ Hom.app' f X ▷ H.obj' X )
    (fun _ _ φ ↦ tensorHom_aux f (𝟙 H) φ)

variable (F G H)

set_option maxHeartbeats 400000 in
def associator :
    tensorObj (tensorObj F G) H ≅ tensorObj F (tensorObj G H) :=
  isoMk'' (fun X ↦ α_ (F.obj' X) (G.obj' X) (H.obj' X)) (by
    intros X Y f
    dsimp only [Functor.comp_obj, Functor.comp_map, evaluation_obj, ModuleCat.of_coe]
    apply ModuleCat.tensor_ext₃'
    intro a b c
    erw [comp_apply])

def leftUnitor : tensorObj (unit _) F ≅ F :=
  isoMk'' (fun X ↦ λ_ (F.obj' X)) sorry

def rightUnitor : tensorObj F (unit _) ≅ F :=
  isoMk'' (fun X ↦ ρ_ (F.obj' X)) sorry

instance monoidalCategoryStructPresheafOfModules :
    MonoidalCategoryStruct (PresheafOfModules (R ⋙ forget₂ _ _)) where
  tensorObj F G := tensorObj F G
  whiskerLeft F _ _ g := whiskerLeft F g
  whiskerRight f H := whiskerRight f H
  tensorHom f g := tensorHom f g
  tensorUnit := unit _
  associator F G H := associator F G H
  leftUnitor F := leftUnitor F
  rightUnitor F := rightUnitor F

variable {F G H}

@[simp]
lemma evaluation_map_tensorHom (f : F ⟶ H) (g : G ⟶ K) (X : Cᵒᵖ) :
    Hom.app' (f ⊗ g) X = Hom.app' f X ⊗ Hom.app' g X := rfl

variable (F)

@[simp]
lemma evaluation_map_whiskerLeft (g : G ⟶ H) (X : Cᵒᵖ) :
    Hom.app' (F ◁ g) X = F.obj' X ◁ Hom.app' g X := rfl

variable {F}

@[simp]
lemma evaluation_map_whiskerRight
    (f : F ⟶ G) (H : PresheafOfModules (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) :
    Hom.app' (f ▷ H) X = Hom.app' f X ▷ H.obj' X := rfl

attribute [local ext] evaluation_jointly_faithful

-- what is the scope of the next two, global, or only this file?
attribute [-ext] Hom.ext
attribute [-simp] evaluation_map

@[simp]
lemma evaluation_map_associator_hom (X : Cᵒᵖ) :
    Hom.app' (α_ F G H).hom X =
      by exact (α_ (F.obj' X) (G.obj' X) (H.obj' X)).hom := by
  rfl

lemma associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃):
    ((f₁ ⊗ f₂) ⊗ f₃) ≫ (α_ Y₁ Y₂ Y₃).hom =
      (α_ X₁ X₂ X₃).hom ≫ (f₁ ⊗ f₂ ⊗ f₃) := by
  ext1 X
  simp only [Functor.map_comp, evaluation_map_tensorHom,
    evaluation_map_associator_hom]
  exact MonoidalCategory.associator_naturality
    (Hom.app' f₁ X) (Hom.app' f₂ X) (Hom.app' f₃ X)

variable (F G H K)

lemma pentagon :
    (α_ F G H).hom ▷ K ≫ (α_ F (G ⊗ H) K).hom ≫ F ◁ (α_ G H K).hom =
      (α_ (F ⊗ G) H K).hom ≫ (α_ F G (H ⊗ K)).hom := by
  ext1 X
  simp only [Functor.comp_obj, Functor.map_comp, evaluation_map_whiskerRight,
    evaluation_map_associator_hom, evaluation_map_whiskerLeft]
  apply MonoidalCategory.pentagon (F.obj' X) (G.obj' X) (H.obj' X) (K.obj' X)

lemma triangle : (α_ F (𝟙_ _) G).hom ≫ F ◁ (λ_ G).hom = (ρ_ F).hom ▷ G := by
  ext1 X
  simp only [Functor.map_comp, evaluation_map_associator_hom,
    evaluation_map_whiskerLeft, evaluation_map_whiskerRight]
  exact MonoidalCategory.triangle (F.obj' X) (G.obj' X)

set_option maxHeartbeats 400000 in
instance : MonoidalCategory (PresheafOfModules.{u} (R ⋙ forget₂ _ _)) where
  tensorHom_def _ _ := by ext1; simp [tensorHom_def]
  tensor_id _ _ := by ext1; simp; rfl
  tensor_comp f₁ f₂ g₁ g₂ := by ext1; simp
  whiskerLeft_id _ _ := by ext1; simp; rfl
  id_whiskerRight _ _ := by ext1; simp; rfl
  associator_naturality := associator_naturality
  leftUnitor_naturality := sorry
  rightUnitor_naturality := sorry
  pentagon F G H K := pentagon F G H K
  triangle F G := triangle F G

end Monoidal

end PresheafOfModules
