/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

#align_import category_theory.monoidal.transport from "leanprover-community/mathlib"@"31529827d0f68d1fbd429edc393a928f677f4aba"

/-!
# Transport a monoidal structure along an equivalence.

When `C` and `D` are equivalent as categories,
we can transport a monoidal structure on `C` along the equivalence,
obtaining a monoidal structure on `D`.

We then upgrade the original functor and its inverse to monoidal functors
with respect to the new monoidal structure on `D`.
-/


universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.MonoidalCategory

namespace CategoryTheory.Monoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {D : Type u₂} [Category.{v₂} D]

-- porting note: it was @[simps {attrs := [`_refl_lemma]}]
/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps]
def transport (e : C ≌ D) : MonoidalCategory.{v₂} D where
  tensorObj X Y := e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
  whiskerLeft := fun X _ _ f ↦ e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight := fun f X ↦ e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
  tensorHom_def := by simp [tensorHom_def]
                      -- 🎉 no goals
  tensorHom f g := e.functor.map (e.inverse.map f ⊗ e.inverse.map g)
  tensorUnit' := e.functor.obj (𝟙_ C)
  associator X Y Z :=
    e.functor.mapIso
      (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫ (Iso.refl _ ⊗ e.unitIso.app _))
  leftUnitor X :=
    e.functor.mapIso (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫ λ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _
  rightUnitor X :=
    e.functor.mapIso ((Iso.refl _ ⊗ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _
  triangle X Y := by
    dsimp
    -- ⊢ e.functor.map ((NatTrans.app e.unitIso.inv (e.inverse.obj X ⊗ e.inverse.obj  …
    simp only [Iso.hom_inv_id_app_assoc, comp_tensor_id, Equivalence.unit_inverse_comp, assoc,
      Equivalence.inv_fun_map, comp_id, Functor.map_comp, id_tensor_comp, e.inverse.map_id]
    simp only [← e.functor.map_comp]
    -- ⊢ e.functor.map ((NatTrans.app e.unitIso.inv (e.inverse.obj X ⊗ e.inverse.obj  …
    congr 2
    -- ⊢ (α_ (e.inverse.obj X) (e.inverse.obj (e.functor.obj (𝟙_ C))) (e.inverse.obj  …
    slice_lhs 2 3 =>
      rw [← id_tensor_comp]
      simp
    -- ⊢ e.functor.map (e.inverse.map (e.functor.map ((NatTrans.app e.unitIso.inv (e. …
    rw [Category.id_comp, ← associator_naturality_assoc, triangle]
    -- 🎉 no goals
  pentagon W X Y Z := by
    -- ⊢ e.functor.map ((NatTrans.app (Equivalence.unitInv e) (e.inverse.obj (e.funct …
    dsimp
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
    simp only [Iso.hom_inv_id_app_assoc, comp_tensor_id, assoc, Equivalence.inv_fun_map,
      Functor.map_comp, id_tensor_comp, e.inverse.map_id]
    simp only [← e.functor.map_comp]
    congr 2
    slice_lhs 4 5 =>
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
      rw [← comp_tensor_id, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 5 6 =>
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
      rw [← id_tensor_comp, Iso.hom_inv_id_app]
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
      dsimp
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
      rw [tensor_id]
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
    simp only [Category.id_comp, Category.assoc]
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
    slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    -- ⊢ ((NatTrans.app e.unitIso.inv (e.inverse.obj W ⊗ e.inverse.obj X) ⊗ 𝟙 (e.inve …
    slice_rhs 1 2 => rw [← tensor_id, ← associator_naturality]
    -- ⊢ e.functor.map (e.inverse.map (𝟙 (e.functor.obj (𝟙_ C))) ⊗ e.inverse.map f) ≫ …
    -- ⊢ ((𝟙 (e.inverse.obj W) ⊗ NatTrans.app e.unitIso.hom (e.inverse.obj X ⊗ e.inve …
    -- ⊢ e.functor.map (𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C))) ⊗ e.inverse.map f) ≫ …
    slice_rhs 3 4 => rw [← tensor_id, associator_naturality]
    -- ⊢ e.functor.map (𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C))) ⊗ e.inverse.map f) ≫ …
    -- ⊢ (((((α_ (e.inverse.obj W) (e.inverse.obj X ⊗ e.inverse.obj Y) (e.inverse.obj …
    -- ⊢ e.functor.map ((𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C))) ⊗ e.inverse.map f)  …
    slice_rhs 2 3 => rw [← pentagon]
    -- ⊢ (𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C))) ⊗ e.inverse.map f) ≫ (NatTrans.app …
    -- ⊢ (α_ (e.inverse.obj W) (e.inverse.obj X ⊗ e.inverse.obj Y) (e.inverse.obj Z)) …
    simp only [Category.assoc]
    -- ⊢ (𝟙 (e.inverse.obj W) ⊗ NatTrans.app e.unitIso.hom (e.inverse.obj X ⊗ e.inver …
    congr 2
    -- ⊢ e.functor.map (e.inverse.map f ⊗ e.inverse.map (𝟙 (e.functor.obj (𝟙_ C)))) ≫ …
    slice_lhs 1 2 => rw [associator_naturality]
    -- ⊢ e.functor.map (e.inverse.map f ⊗ 𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C)))) ≫ …
    -- ⊢ e.functor.map (e.inverse.map (e.functor.map (e.inverse.map f₁ ⊗ e.inverse.ma …
    simp only [Category.assoc]
    -- ⊢ e.functor.map (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.i …
    -- ⊢ e.functor.map (e.inverse.map f ⊗ 𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C)))) ≫ …
    -- ⊢ e.functor.map ((NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e. …
    congr 1
    -- ⊢ (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂✝ …
    -- ⊢ e.functor.map ((e.inverse.map f ⊗ 𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C))))  …
    -- ⊢ ((NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂ …
    slice_lhs 1 2 =>
    -- ⊢ (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂✝ …
    -- ⊢ (e.inverse.map f ⊗ 𝟙 (e.inverse.obj (e.functor.obj (𝟙_ C)))) ≫ (𝟙 (e.inverse …
    -- ⊢ (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂✝ …
    -- 🎉 no goals
    -- ⊢ (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂✝ …
      rw [← id_tensor_comp, ← comp_tensor_id, Iso.hom_inv_id_app]
    -- ⊢ ((NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂ …
      dsimp
      rw [tensor_id, tensor_id]
    simp only [Category.id_comp, Category.assoc]
  leftUnitor_naturality f := by
    dsimp
    -- ⊢ (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂✝ …
    simp only [Functor.map_comp, Functor.map_id, Category.assoc]
    -- ⊢ (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂✝ …
    erw [← e.counitIso.hom.naturality]
    -- ⊢ (NatTrans.app (Equivalence.unitInv e) (e.inverse.obj X₁✝ ⊗ e.inverse.obj X₂✝ …
    simp only [Functor.comp_map, ← e.functor.map_comp_assoc]
    -- ⊢ (e.inverse.map f₁ ⊗ e.inverse.map f₂ ⊗ 𝟙 (e.inverse.obj X₃✝)) ≫ (𝟙 (e.invers …
    congr 2
    -- ⊢ (((e.inverse.map f₁ ⊗ 𝟙 (e.inverse.obj X₂✝ ⊗ e.inverse.obj X₃✝)) ≫ (𝟙 (e.inv …
    rw [id_tensor_comp_tensor_id_assoc, ← tensor_id_comp_id_tensor_assoc,
    -- ⊢ (e.inverse.map f₁ ⊗ 𝟙 (e.inverse.obj X₂✝ ⊗ e.inverse.obj X₃✝)) ≫ (𝟙 (e.inver …
      leftUnitor_naturality]
    -- ⊢ (e.inverse.map f₁ ⊗ e.inverse.map f₂ ⊗ e.inverse.map f₃) ≫ (𝟙 (e.inverse.obj …
  rightUnitor_naturality f := by
    dsimp
    simp only [Functor.map_comp, Functor.map_id, Category.assoc]
    erw [← e.counitIso.hom.naturality]
    simp only [Functor.comp_map, ← e.functor.map_comp_assoc]
    -- ⊢ (e.inverse.map f₁ ⊗ e.inverse.map f₂ ⊗ e.inverse.map f₃) ≫ (𝟙 (e.inverse.obj …
    congr 2
    erw [tensor_id_comp_id_tensor_assoc, ← id_tensor_comp_tensor_id_assoc,
      rightUnitor_naturality]
  associator_naturality f₁ f₂ f₃ := by
    dsimp
    -- ⊢ (e.inverse.map f₁ ⊗ e.inverse.map f₂ ⊗ e.inverse.map f₃) ≫ (𝟙 (e.inverse.obj …
    simp only [Equivalence.inv_fun_map, Functor.map_comp, Category.assoc]
    -- ⊢ (e.inverse.map f₁ ⊗ e.inverse.map f₂ ⊗ e.inverse.map f₃) ≫ (𝟙 (e.inverse.obj …
    simp only [← e.functor.map_comp]
    -- ⊢ (e.inverse.map f₁ ⊗ e.inverse.map f₂ ⊗ e.inverse.map f₃) ≫ (𝟙 (e.inverse.obj …
    congr 1
    -- 🎉 no goals
    conv_lhs => rw [← tensor_id_comp_id_tensor]
    slice_lhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor, ← tensor_id]
    simp only [Category.assoc]
    slice_lhs 3 4 => rw [associator_naturality]
    conv_lhs => simp only [comp_tensor_id]
    slice_lhs 3 4 =>
      rw [← comp_tensor_id, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 2 3 => rw [associator_naturality]
    simp only [Category.assoc]
    congr 2
    slice_lhs 1 1 => rw [← tensor_id_comp_id_tensor]
    slice_lhs 2 3 => rw [← id_tensor_comp, tensor_id_comp_id_tensor]
    slice_lhs 1 2 => rw [tensor_id_comp_id_tensor]
    conv_rhs =>
      congr
      · skip
      · rw [← id_tensor_comp_tensor_id, id_tensor_comp]
    simp only [Category.assoc]
    slice_rhs 1 2 =>
      rw [← id_tensor_comp, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    simp only [Category.id_comp, Category.assoc]
    conv_rhs => rw [id_tensor_comp]
    slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_rhs 1 2 => rw [id_tensor_comp_tensor_id]
#align category_theory.monoidal.transport CategoryTheory.Monoidal.transport

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[nolint unusedArguments]
def Transported (_ : C ≌ D) := D
#align category_theory.monoidal.transported CategoryTheory.Monoidal.Transported

instance (e : C ≌ D) : Category (Transported e) := (inferInstance : Category D)

instance (e : C ≌ D) : MonoidalCategory (Transported e) :=
  transport e

instance (e : C ≌ D) : Inhabited (Transported e) :=
  ⟨𝟙_ _⟩

section

attribute [local simp] transport_tensorUnit'

section

attribute [local simp]
  transport_tensorHom transport_associator transport_leftUnitor transport_rightUnitor

/--
We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def laxToTransported (e : C ≌ D) : LaxMonoidalFunctor C (Transported e) where
  toFunctor := e.functor
  ε := 𝟙 (e.functor.obj (𝟙_ C))
  μ X Y := e.functor.map (e.unitInv.app X ⊗ e.unitInv.app Y)
  μ_natural f g := by
    dsimp
    -- ⊢ e.functor.map (e.inverse.map (e.functor.map f) ⊗ e.inverse.map (e.functor.ma …
    rw [Equivalence.inv_fun_map, Equivalence.inv_fun_map, tensor_comp, Functor.map_comp,
      tensor_comp, ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp,
      assoc, assoc, ← tensor_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app, ← tensor_comp]
    dsimp
    -- ⊢ e.functor.map ((NatTrans.app (Equivalence.unitInv e) X✝ ⊗ NatTrans.app (Equi …
    rw [comp_id, comp_id]
    -- 🎉 no goals
  associativity X Y Z := by
    dsimp
    -- ⊢ e.functor.map (e.inverse.map (e.functor.map (NatTrans.app (Equivalence.unitI …
    rw [Equivalence.inv_fun_map, Equivalence.inv_fun_map, Functor.map_comp,
      Functor.map_comp, assoc, assoc, e.inverse.map_id, e.inverse.map_id,
      comp_tensor_id, id_tensor_comp, Functor.map_comp, assoc, id_tensor_comp,
      comp_tensor_id, ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp]
    congr 2
    -- ⊢ (((NatTrans.app (Equivalence.unitInv e) X ⊗ NatTrans.app (Equivalence.unitIn …
    slice_lhs 3 3 => rw [← tensor_id_comp_id_tensor]
    -- ⊢ ((NatTrans.app (Equivalence.unitInv e) X ⊗ NatTrans.app (Equivalence.unitInv …
    slice_lhs 2 3 =>
      rw [← comp_tensor_id, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    rw [id_comp]
    -- ⊢ ((NatTrans.app (Equivalence.unitInv e) X ⊗ NatTrans.app (Equivalence.unitInv …
    slice_rhs 2 3 =>
      rw [←id_tensor_comp, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    rw [id_comp]
    -- ⊢ ((NatTrans.app (Equivalence.unitInv e) X ⊗ NatTrans.app (Equivalence.unitInv …
    conv_rhs => rw [← id_tensor_comp_tensor_id _ (e.unitInv.app X)]
    -- ⊢ ((NatTrans.app (Equivalence.unitInv e) X ⊗ NatTrans.app (Equivalence.unitInv …
    dsimp only [Functor.comp_obj]
    -- ⊢ ((NatTrans.app (Equivalence.unitInv e) X ⊗ NatTrans.app (Equivalence.unitInv …
    slice_rhs 3 4 =>
      rw [← id_tensor_comp, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    simp only [associator_conjugation, ←tensor_id, ←tensor_comp, Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, assoc, id_comp, comp_id]
  left_unitality X := by
    dsimp
    -- ⊢ e.functor.map ((NatTrans.app e.unitIso.inv (𝟙_ C) ⊗ 𝟙 (e.inverse.obj (e.func …
    rw [e.inverse.map_id, e.inverse.map_id, tensor_id, Functor.map_comp, assoc,
      Equivalence.counit_app_functor, ← e.functor.map_comp, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← leftUnitor_naturality,
      ← tensor_comp_assoc, comp_id, id_comp, id_comp]
    rfl
    -- 🎉 no goals
  right_unitality X := by
    dsimp
    -- ⊢ e.functor.map ((𝟙 (e.inverse.obj (e.functor.obj X)) ⊗ NatTrans.app e.unitIso …
    rw [Functor.map_comp, assoc, e.inverse.map_id, e.inverse.map_id, tensor_id,
      Functor.map_id, id_comp, Equivalence.counit_app_functor, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← rightUnitor_naturality,
      ← tensor_comp_assoc, id_comp, comp_id]
    rfl
    -- 🎉 no goals
#align category_theory.monoidal.lax_to_transported CategoryTheory.Monoidal.laxToTransported

end

/-- We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def toTransported (e : C ≌ D) : MonoidalFunctor C (Transported e) where
  toLaxMonoidalFunctor := laxToTransported e
  ε_isIso := by
    dsimp
    -- ⊢ IsIso (𝟙 (e.functor.obj (𝟙_ C)))
    infer_instance
    -- 🎉 no goals
  μ_isIso X Y := by
    dsimp
    -- ⊢ IsIso (e.functor.map (NatTrans.app (Equivalence.unitInv e) X ⊗ NatTrans.app  …
    infer_instance
    -- 🎉 no goals
#align category_theory.monoidal.to_transported CategoryTheory.Monoidal.toTransported

end

instance (e : C ≌ D) : IsEquivalence (toTransported e).toFunctor := by
  dsimp
  -- ⊢ IsEquivalence e.functor
  infer_instance
  -- 🎉 no goals

/-- We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps!]
def fromTransported (e : C ≌ D) : MonoidalFunctor (Transported e) C :=
  monoidalInverse (toTransported e)
#align category_theory.monoidal.from_transported CategoryTheory.Monoidal.fromTransported

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps! hom inv]
def transportedMonoidalUnitIso (e : C ≌ D) :
    LaxMonoidalFunctor.id C ≅ laxToTransported e ⊗⋙ (fromTransported e).toLaxMonoidalFunctor :=
  asIso (monoidalUnit (toTransported e))
#align category_theory.monoidal.transported_monoidal_unit_iso CategoryTheory.Monoidal.transportedMonoidalUnitIso

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps! hom inv]
def transportedMonoidalCounitIso (e : C ≌ D) :
    (fromTransported e).toLaxMonoidalFunctor ⊗⋙ laxToTransported e ≅
      LaxMonoidalFunctor.id (Transported e) :=
  asIso (monoidalCounit (toTransported e))
#align category_theory.monoidal.transported_monoidal_counit_iso CategoryTheory.Monoidal.transportedMonoidalCounitIso

end CategoryTheory.Monoidal
