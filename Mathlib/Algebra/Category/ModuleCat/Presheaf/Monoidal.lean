/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson, Jack McKoen, Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# The monoidal category structure on presheaves of modules

Given a presheaf of commutative rings `R : Cᵒᵖ ⥤ CommRingCat`, we construct
the monoidal category structure on the category of presheaves of modules
`PresheafOfModulesOfCommRing R`. The tensor product `M₁ ⊗ M₂` is defined
as the presheaf of modules which sends `X : Cᵒᵖ` to `M₁.obj X ⊗ M₂.obj X`.

The universal property of this tensor product is given by
`PresheafOfModulesOfCommRing.tensorLift`: a family of bilinear maps compatible with
restriction induces a morphism from the tensor product. The lemma
`PresheafOfModulesOfCommRing.tensor_ext` gives uniqueness by testing on pure tensors.

## Notes

This contribution was created as part of the AIM workshop
"Formalizing algebraic geometry" in June 2024.

-/

@[expose] public section

open CategoryTheory MonoidalCategory BraidedCategory Category Limits

universe v u v₁ u₁

variable {C : Type*} [Category* C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace PresheafOfModulesOfCommRing

namespace Monoidal

variable (M₁ M₂ M₃ M₄ : PresheafOfModulesOfCommRing.{u} R)

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `tensorObj`. -/
noncomputable def tensorObjMap {X Y : Cᵒᵖ} (f : X ⟶ Y) : M₁.obj X ⊗ M₂.obj X ⟶
    (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y) :=
  ModuleCat.MonoidalCategory.tensorLift (fun m₁ m₂ ↦ M₁.map f m₁ ⊗ₜ M₂.map f m₂)
    (by
      intro m₁ m₁' m₂
      dsimp +instances
      rw [map_add, TensorProduct.add_tmul])
    (by intro a m₁ m₂; dsimp; erw [M₁.map_smul]; rfl)
    (by
      intro m₁ m₂ m₂'
      dsimp +instances
      rw [map_add, TensorProduct.tmul_add])
    (by intro a m₁ m₂; dsimp; erw [M₂.map_smul, TensorProduct.tmul_smul (r := R.map f a)]; rfl)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two presheaves of modules. -/
@[simps obj]
noncomputable def tensorObj : PresheafOfModulesOfCommRing R :=
  mk (fun X ↦ M₁.obj X ⊗ M₂.obj X)
    (fun f ↦ tensorObjMap M₁ M₂ f)
    (fun X ↦ ModuleCat.MonoidalCategory.tensor_ext (by
      intro m₁ m₂
      dsimp [tensorObjMap]
      simp))
    (fun f g ↦ ModuleCat.MonoidalCategory.tensor_ext (by
      intro m₁ m₂
      dsimp [tensorObjMap]
      simp +instances))

variable {M₁ M₂ M₃ M₄}

@[simp]
lemma tensorObj_map_tmul {X Y : Cᵒᵖ} (f : X ⟶ Y) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    DFunLike.coe (α := (M₁.obj X ⊗ M₂.obj X :))
      (β := fun _ ↦ (ModuleCat.restrictScalars (R.map f).hom).obj (M₁.obj Y ⊗ M₂.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((tensorObj M₁ M₂).map f)) (m₁ ⊗ₜ[R.obj X] m₂) =
    M₁.map f m₁ ⊗ₜ[R.obj Y] M₂.map f m₂ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of two morphisms of presheaves of modules. -/
@[simps]
noncomputable def tensorHom (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) :
    tensorObj M₁ M₃ ⟶ tensorObj M₂ M₄ :=
  mkHom (fun X ↦ f.app X ⊗ₘ g.app X)
    (fun φ ↦ ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₃ ↦ by
      dsimp
      rw [tensorObj_map_tmul]
      -- Need `erw` because of the type mismatch in `map` and the tensor product.
      erw [ModuleCat.MonoidalCategory.tensorHom_tmul, tensorObj_map_tmul]
      erw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
      simp))

end Monoidal

open Monoidal

noncomputable instance monoidalCategoryStruct :
    MonoidalCategoryStruct (PresheafOfModulesOfCommRing.{u} R) where
  tensorObj := tensorObj
  whiskerLeft _ _ _ g := tensorHom (𝟙 _) g
  whiskerRight f _ := tensorHom f (𝟙 _)
  tensorHom := tensorHom
  tensorUnit := unit _
  associator M₁ M₂ M₃ := isoMk (fun _ ↦ α_ _ _ _)
    (fun _ _ _ ↦ ModuleCat.MonoidalCategory.tensor_ext₃' (by intros; rfl))
  leftUnitor M := Iso.symm (isoMk (fun _ ↦ (λ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
      ModuleCat.MonoidalCategory.leftUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))
  rightUnitor M := Iso.symm (isoMk (fun _ ↦ (ρ_ _).symm) (fun X Y f ↦ by
    ext m
    dsimp [CommRingCat.forgetToRingCat_obj]
    erw [ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
      ModuleCat.MonoidalCategory.rightUnitor_inv_apply, tensorObj_map_tmul, (R.map f).hom.map_one]
    rfl))

noncomputable instance monoidalCategory :
    MonoidalCategory (PresheafOfModulesOfCommRing.{u} R) where
  tensorHom_def _ _ := by ext1; apply tensorHom_def
  id_tensorHom_id _ _ := by ext1; apply id_tensorHom_id
  tensorHom_comp_tensorHom _ _ _ _ := by ext1; apply tensorHom_comp_tensorHom
  whiskerLeft_id M₁ M₂ := by
    ext1 X
    apply MonoidalCategory.whiskerLeft_id (C := ModuleCat (R.obj X))
  id_whiskerRight _ _ := by
    ext1 X
    apply MonoidalCategory.id_whiskerRight (C := ModuleCat (R.obj X))
  associator_naturality _ _ _ := by ext1; apply associator_naturality
  leftUnitor_naturality _ := by ext1; apply leftUnitor_naturality
  rightUnitor_naturality _ := by ext1; apply rightUnitor_naturality
  pentagon _ _ _ _ := by ext1; apply pentagon
  triangle _ _ := by ext1; apply triangle

open BraidedCategory

noncomputable instance symmetricCategory :
    SymmetricCategory (PresheafOfModulesOfCommRing.{u} R) where
  braiding M₁ M₂ :=
    isoMk (fun X ↦ braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X))
      (fun _ _ f ↦ ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl))
  braiding_naturality_right _ _ _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  braiding_naturality_left _ _ := by
    ext : 1
    exact ModuleCat.MonoidalCategory.tensor_ext (fun _ _ ↦ rfl)
  hexagon_forward _ _ _ := by
    ext : 1
    apply hexagon_forward (C := ModuleCat (R.obj _))
  hexagon_reverse _ _ _ := by
    ext : 1
    apply hexagon_reverse (C := ModuleCat (R.obj _))
  symmetry _ _ := by
    ext : 1
    apply SymmetricCategory.symmetry (C := ModuleCat (R.obj _))

section

variable (M₁ M₂ M₃ M₄ : PresheafOfModulesOfCommRing.{u} R)

lemma tensorObj_obj (X : Cᵒᵖ) :
    (M₁ ⊗ M₂).obj X =
      MonoidalCategory.tensorObj (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) := rfl

attribute [local simp] tensorObj_obj

variable {M₂ M₃} in
@[simp]
lemma whiskerLeft_app (f : M₂ ⟶ M₃) (X : Cᵒᵖ) :
    dsimp% (M₁ ◁ f).app X = whiskerLeft (C := ModuleCat (R.obj X)) (M₁.obj X) (f.app X) :=
  rfl

variable {M₁ M₂} in
@[simp]
lemma whiskerRight_app (f : M₁ ⟶ M₂) (M₃ : PresheafOfModulesOfCommRing.{u} R)
    (X : Cᵒᵖ) :
    dsimp% (f ▷ M₃).app X = whiskerRight (C := ModuleCat (R.obj X)) (f.app X) (M₃.obj X) := rfl

variable {M₁ M₂ M₃ M₄} in
@[simp]
lemma tensorHom_app (f : M₁ ⟶ M₂) (g : M₃ ⟶ M₄) (X : Cᵒᵖ) :
    dsimp% (f ⊗ₘ g).app X =
      MonoidalCategory.tensorHom (C := ModuleCat (R.obj X)) (f.app X) (g.app X) := rfl

@[simp]
lemma leftUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).hom.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma leftUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (λ_ M₁).inv.app X = (leftUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv := by
  rfl

@[simp]
lemma rightUnitor_hom_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).hom.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).hom :=
  rfl

@[simp]
lemma rightUnitor_inv_app (X : Cᵒᵖ) :
    dsimp% (ρ_ M₁).inv.app X = (rightUnitor (C := ModuleCat (R.obj X)) (M₁.obj X)).inv :=
  rfl

@[simp]
lemma associator_hom_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).hom.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).hom :=
  rfl

@[simp]
lemma associator_inv_app (X : Cᵒᵖ) :
    (α_ M₁ M₂ M₃).inv.app X =
      (associator (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X) (M₃.obj X)).inv :=
  rfl

@[simp]
lemma braiding_hom_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).hom.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).hom := by
  rfl

@[simp]
lemma braiding_inv_app (X : Cᵒᵖ) :
    dsimp% (braiding M₁ M₂).inv.app X =
      (braiding (C := ModuleCat (R.obj X)) (M₁.obj X) (M₂.obj X)).inv := rfl

end

section TensorLift

variable {M₁ M₂ M₃ : PresheafOfModulesOfCommRing.{u} R}

/-- Morphisms out of a tensor product of presheaves of modules are determined by their
values on pure tensors. -/
lemma tensor_ext {f g : M₁ ⊗ M₂ ⟶ M₃}
    (h : ∀ (X : Cᵒᵖ) (m₁ : M₁.obj X) (m₂ : M₂.obj X),
      f.app X (m₁ ⊗ₜ[R.obj X] m₂) = g.app X (m₁ ⊗ₜ[R.obj X] m₂)) : f = g := by
  ext1 X
  exact ModuleCat.MonoidalCategory.tensor_ext (h X)

variable (f : ∀ (X : Cᵒᵖ), M₁.obj X → M₂.obj X → M₃.obj X)
  (hadd₁ : ∀ X m₁ m₁' m₂, f X (m₁ + m₁') m₂ = f X m₁ m₂ + f X m₁' m₂)
  (hsmul₁ : ∀ X (a : R.obj X) m₁ m₂, f X (a • m₁) m₂ = a • f X m₁ m₂)
  (hadd₂ : ∀ X m₁ m₂ m₂', f X m₁ (m₂ + m₂') = f X m₁ m₂ + f X m₁ m₂')
  (hsmul₂ : ∀ X (a : R.obj X) m₁ m₂, f X m₁ (a • m₂) = a • f X m₁ m₂)
  (hnat : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) m₁ m₂,
    f Y (M₁.map g m₁) (M₂.map g m₂) = M₃.map g (f X m₁ m₂))

/-- A family of bilinear maps compatible with restriction induces a morphism out of the
tensor product of two presheaves of modules. -/
noncomputable def tensorLift : M₁ ⊗ M₂ ⟶ M₃ :=
  mkHom (fun X ↦ ModuleCat.MonoidalCategory.tensorLift (f X)
    (hadd₁ X) (hsmul₁ X) (hadd₂ X) (hsmul₂ X)) (fun g ↦
      ModuleCat.MonoidalCategory.tensor_ext (fun m₁ m₂ ↦ hnat g m₁ m₂))

@[simp]
lemma tensorLift_app_tmul (X : Cᵒᵖ) (m₁ : M₁.obj X) (m₂ : M₂.obj X) :
    (tensorLift f hadd₁ hsmul₁ hadd₂ hsmul₂ hnat).app X (m₁ ⊗ₜ[R.obj X] m₂) =
      f X m₁ m₂ := rfl

/-- The morphism induced by a compatible family of bilinear maps is unique. -/
lemma tensorLift_unique (g : M₁ ⊗ M₂ ⟶ M₃)
    (h : ∀ (X : Cᵒᵖ) (m₁ : M₁.obj X) (m₂ : M₂.obj X),
      g.app X (m₁ ⊗ₜ[R.obj X] m₂) = f X m₁ m₂) :
    g = tensorLift f hadd₁ hsmul₁ hadd₂ hsmul₂ hnat :=
  tensor_ext h

end TensorLift

instance (F : PresheafOfModulesOfCommRing.{u} R) :
    PreservesColimitsOfSize.{u, u} (tensorLeft F) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _
      (fun X ↦ isColimitOfPreserves (tensorLeft (show ModuleCat (R.obj X) from F.obj X))
        (isColimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩⟩⟩

instance (F : PresheafOfModulesOfCommRing.{u} R) :
    PreservesColimitsOfSize.{u, u} (tensorRight F) :=
  preservesColimits_of_natIso (tensorLeftIsoTensorRight F)

end PresheafOfModulesOfCommRing
