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
we can transport a monoidal structure on `C` along the equivalence as
`CategoryTheory.Monoidal.transport`, obtaining a monoidal structure on `D`.

More generally, we can transport the lawfulness of a monoidal structure along a suitable faithful
functor, as `CategoryTheory.Monoidal.induced`.
The comparison is analogous to the difference between `Equiv.monoid` and
`Function.Injective.Monoid`.

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

/-- The data needed to induce a `MonoidalCategory` via the functor `F`; namely, pre-existing
definitions of `⊗`, `𝟙_`, `▷`, `◁` that are preserved by `F`.
-/
structure InducingFunctorData [MonoidalCategoryStruct D] (F : D ⥤ C) where
  /-- Analogous to `CategoryTheory.LaxMonoidalFunctor.μIso` -/
  μIso : ∀ X Y,
    F.obj X ⊗ F.obj Y ≅ F.obj (X ⊗ Y)
  whiskerLeft_eq : ∀ (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂),
    F.map (X ◁ f) = (μIso _ _).inv ≫ (F.obj X ◁ F.map f) ≫ (μIso _ _).hom :=
    by aesop_cat
  whiskerRight_eq : ∀ {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D),
    F.map (f ▷ Y) = (μIso _ _).inv ≫ (F.map f ▷ F.obj Y) ≫ (μIso _ _).hom :=
    by aesop_cat
  tensorHom_eq : ∀ {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
    F.map (f ⊗ g) = (μIso _ _).inv ≫ (F.map f ⊗ F.map g) ≫ (μIso _ _).hom :=
    by aesop_cat
  /-- Analogous to `CategoryTheory.LaxMonoidalFunctor.εIso` -/
  εIso : 𝟙_ _ ≅ F.obj (𝟙_ _)
  associator_eq : ∀ X Y Z : D,
    F.map (α_ X Y Z).hom =
      (((μIso _ _).symm ≪≫ ((μIso _ _).symm ⊗ .refl _))
        ≪≫ α_ (F.obj X) (F.obj Y) (F.obj Z)
        ≪≫ ((.refl _ ⊗ μIso _ _) ≪≫ μIso _ _)).hom :=
    by aesop_cat
  leftUnitor_eq : ∀ X : D,
    F.map (λ_ X).hom =
      (((μIso _ _).symm ≪≫ (εIso.symm ⊗ .refl _)) ≪≫ λ_ (F.obj X)).hom :=
    by aesop_cat
  rightUnitor_eq : ∀ X : D,
    F.map (ρ_ X).hom =
      (((μIso _ _).symm ≪≫ (.refl _ ⊗ εIso.symm)) ≪≫ ρ_ (F.obj X)).hom :=
    by aesop_cat

-- these are theorems so don't need docstrings (std4#217)
attribute [nolint docBlame]
  InducingFunctorData.whiskerLeft_eq
  InducingFunctorData.whiskerRight_eq
  InducingFunctorData.tensorHom_eq
  InducingFunctorData.associator_eq
  InducingFunctorData.leftUnitor_eq
  InducingFunctorData.rightUnitor_eq

/--
Induce the lawfulness of the monoidal structure along an faithful functor of (plain) categories,
where the operations are already defined on the destination type `D`.

The functor `F` must preserve all the data parts of the monoidal structure between the two
categories.

-/
abbrev induced [MonoidalCategoryStruct D] (F : D ⥤ C) [Faithful F]
    (fData : InducingFunctorData F) :
    MonoidalCategory.{v₂} D where
  tensorHom_def {X₁ Y₁ X₂ Y₂} f g := F.map_injective <| by
    rw [fData.tensorHom_eq, Functor.map_comp, fData.whiskerRight_eq, fData.whiskerLeft_eq]
    simp only [tensorHom_def, assoc, Iso.hom_inv_id_assoc]
  tensor_id X₁ X₂ := F.map_injective <| by cases fData; aesop_cat
  tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ := F.map_injective <| by cases fData; aesop_cat
  whiskerLeft_id X Y := F.map_injective <| by simp [fData.whiskerLeft_eq]
  id_whiskerRight X Y := F.map_injective <| by simp [fData.whiskerRight_eq]
  triangle X Y := F.map_injective <| by cases fData; aesop_cat
  pentagon W X Y Z := F.map_injective <| by
    simp only [Functor.map_comp, fData.tensorHom_eq, fData.associator_eq, Iso.trans_assoc,
      Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, Functor.map_id, comp_tensor_id,
      associator_conjugation, tensor_id, assoc, id_tensor_comp, Iso.hom_inv_id_assoc,
      tensor_hom_inv_id_assoc, id_comp, hom_inv_id_tensor_assoc, Iso.inv_hom_id_assoc,
      id_tensor_comp_tensor_id_assoc, Iso.cancel_iso_inv_left]
    slice_lhs 6 8 =>
      rw [← id_tensor_comp, hom_inv_id_tensor, tensor_id, comp_id,
        tensor_id]
    simp only [comp_id, assoc, pentagon_assoc, Iso.inv_hom_id_assoc,
      ← associator_naturality_assoc, tensor_id, tensor_id_comp_id_tensor_assoc]
  leftUnitor_naturality {X Y : D} f := F.map_injective <| by
    have := leftUnitor_naturality (F.map f)
    simp only [Functor.map_comp, fData.tensorHom_eq, Functor.map_id, fData.leftUnitor_eq,
      Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, assoc,
      Iso.hom_inv_id_assoc, id_tensor_comp_tensor_id_assoc, Iso.cancel_iso_inv_left]
    rw [←this, ←assoc, ←tensor_comp, id_comp, comp_id]
  rightUnitor_naturality {X Y : D} f := F.map_injective <| by
    have := rightUnitor_naturality (F.map f)
    simp only [Functor.map_comp, fData.tensorHom_eq, Functor.map_id, fData.rightUnitor_eq,
      Iso.trans_assoc, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, assoc,
      Iso.hom_inv_id_assoc, tensor_id_comp_id_tensor_assoc, Iso.cancel_iso_inv_left]
    rw [←this, ←assoc, ←tensor_comp, id_comp, comp_id]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := F.map_injective <| by
    have := associator_naturality (F.map f₁) (F.map f₂) (F.map f₃)
    simp [fData.associator_eq, fData.tensorHom_eq]
    simp_rw [←assoc, ←tensor_comp, assoc, Iso.hom_inv_id, ←assoc]
    congr 1
    conv_rhs => rw [←comp_id (F.map f₁), ←id_comp (F.map f₁)]
    simp only [tensor_comp]
    simp only [tensor_id, comp_id, assoc, tensor_hom_inv_id_assoc, id_comp]
    slice_rhs 2 3 => rw [←this]
    simp only [← assoc, Iso.inv_hom_id, comp_id]
    congr 2
    simp_rw [←tensor_comp, id_comp]


/--
We can upgrade `F` to a monoidal functor from `D` to `E` with the induced structure.
-/
@[simps]
def fromInduced [MonoidalCategoryStruct D] (F : D ⥤ C) [Faithful F]
    (fData : InducingFunctorData F) :
    letI := induced F fData
    MonoidalFunctor D C :=
  letI := induced F fData
  { toFunctor := F
    ε := fData.εIso.hom
    μ := fun X Y => (fData.μIso X Y).hom
    μ_natural := by cases fData; aesop_cat
    associativity := by cases fData; aesop_cat
    left_unitality := by cases fData; aesop_cat
    right_unitality := by cases fData; aesop_cat }

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps (config := {rhsMd := .default})
  tensorObj tensorHom tensorUnit' associator leftUnitor rightUnitor]
def transport (e : C ≌ D) : MonoidalCategory.{v₂} D := .ofTensorHom
  (tensorObj := fun X Y ↦ e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y))
  (tensorHom := fun f g ↦ e.functor.map (e.inverse.map f ⊗ e.inverse.map g))
  (whiskerLeft := fun X _ _ f ↦ e.functor.map (e.inverse.obj X ◁ e.inverse.map f))
  (whiskerRight := fun f X ↦ e.functor.map (e.inverse.map f ▷ e.inverse.obj X))
  (tensorUnit' := e.functor.obj (𝟙_ C))
  (associator := fun X Y Z ↦
    e.functor.mapIso
      ((whiskerRightIso (e.unitIso.app _).symm _) ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫
          (whiskerLeftIso _ (e.unitIso.app _))))
  (leftUnitor := fun X ↦
    e.functor.mapIso ((whiskerRightIso (e.unitIso.app _).symm _) ≪≫ λ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _)
  (rightUnitor := fun X ↦
    e.functor.mapIso ((whiskerLeftIso _ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _)
  (triangle := fun X Y ↦ by
    dsimp
    simp only [Functor.map_comp, Functor.map_id, assoc, Equivalence.inv_fun_map,
      Functor.comp_obj, Functor.id_obj,
      Equivalence.unit_inverse_comp, comp_id, Iso.hom_inv_id_app_assoc,
      id_tensorHom, MonoidalCategory.whiskerLeft_comp,
      tensorHom_id, comp_whiskerRight, whisker_assoc, triangle_assoc_comp_right]
    simp only [← e.functor.map_comp]
    congr 2
    slice_lhs 2 3 =>
      rw [← MonoidalCategory.whiskerLeft_comp]
      simp
    simp)
  (pentagon := fun W X Y Z ↦ by
    dsimp
    simp only [Functor.map_comp, Equivalence.inv_fun_map, Functor.comp_obj, Functor.id_obj, assoc,
      Iso.hom_inv_id_app_assoc, Functor.map_id, tensorHom_id, comp_whiskerRight, whisker_assoc,
      id_tensorHom, MonoidalCategory.whiskerLeft_comp]
    simp only [← e.functor.map_comp]
    congr 2
    slice_lhs 6 7 =>
      rw [← comp_whiskerRight, Iso.hom_inv_id_app]
      dsimp
      rw [id_whiskerRight]
    simp only [id_comp, assoc, Iso.inv_hom_id_assoc]
    slice_lhs 5 6 =>
      rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id_app]
      dsimp
      rw [MonoidalCategory.whiskerLeft_id]
    simp only [Category.id_comp, Category.assoc]
    slice_rhs 2 3 => rw [whisker_exchange]
    slice_lhs 4 5 =>
      rw [← MonoidalCategory.whiskerLeft_comp, ← comp_whiskerRight, Iso.hom_inv_id_app]
      dsimp
      rw [id_whiskerRight, MonoidalCategory.whiskerLeft_id]
    simp)
  (leftUnitor_naturality := fun f ↦ by
    dsimp
    simp only [Functor.map_comp, Functor.map_id, Category.assoc]
    erw [← e.counitIso.hom.naturality]
    simp only [Functor.comp_map, ← e.functor.map_comp_assoc]
    congr 2
    simp only [id_tensorHom]
    rw [whisker_exchange_assoc, leftUnitor_naturality])
  (rightUnitor_naturality := fun f ↦ by
    dsimp
    simp only [Functor.map_comp, Functor.map_id, Category.assoc]
    erw [← e.counitIso.hom.naturality]
    simp only [Functor.comp_map, ← e.functor.map_comp_assoc]
    congr 2
    simp only [tensorHom_id]
    erw [← whisker_exchange_assoc, rightUnitor_naturality])
  (associator_naturality := fun f₁ f₂ f₃ ↦ by
    dsimp
    simp only [Equivalence.inv_fun_map, Functor.map_comp, Category.assoc]
    simp only [← e.functor.map_comp]
    congr 1
    conv_lhs => rw [← tensor_id_comp_id_tensor]
    simp only [← id_tensorHom, ← tensorHom_id]
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
    slice_rhs 1 2 => rw [id_tensor_comp_tensor_id])
@[simps]
def transportStruct (e : C ≌ D) : MonoidalCategoryStruct.{v₂} D where
  tensorObj X Y := e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
  whiskerLeft X _ _ f := e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight f X := e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
  tensorHom f g := e.functor.map (e.inverse.map f ⊗ e.inverse.map g)
  tensorUnit := e.functor.obj (𝟙_ C)
  associator X Y Z :=
    e.functor.mapIso
      (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫
        α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫
        (Iso.refl _ ⊗ e.unitIso.app _))
  leftUnitor X :=
    e.functor.mapIso (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫ λ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _
  rightUnitor X :=
    e.functor.mapIso ((Iso.refl _ ⊗ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
      e.counitIso.app _

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
def transport (e : C ≌ D) : MonoidalCategory.{v₂} D :=
  letI : MonoidalCategoryStruct.{v₂} D := transportStruct e
  induced e.inverse
    { μIso := fun X Y => e.unitIso.app _
      εIso := e.unitIso.app _ }
#align category_theory.monoidal.transport CategoryTheory.Monoidal.transport

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[nolint unusedArguments]
def Transported (_ : C ≌ D) := D
#align category_theory.monoidal.transported CategoryTheory.Monoidal.Transported

instance (e : C ≌ D) : Category (Transported e) := (inferInstance : Category D)

instance Transported.instMonoidalCategoryStruct (e : C ≌ D) :
    MonoidalCategoryStruct (Transported e) :=
  transportStruct e

instance Transported.instMonoidalCategory (e : C ≌ D) : MonoidalCategory (Transported e) :=
  transport e

instance (e : C ≌ D) : Inhabited (Transported e) :=
  ⟨𝟙_ _⟩

section

attribute [local simp] transport_tensorUnit'

section

/--
We can upgrade `e.functor` to a lax monoidal functor from `C` to `D` with the transported structure.
-/
@[simps!]
def laxToTransported (e : C ≌ D) : LaxMonoidalFunctor C (Transported e) := .ofTensorHom
  (F := e.functor)
  (ε := 𝟙 (e.functor.obj (𝟙_ C)))
  (μ := fun X Y ↦ e.functor.map (e.unitInv.app X ⊗ e.unitInv.app Y))
  (μ_natural := fun f g ↦ by
    dsimp
    rw [Equivalence.inv_fun_map, Equivalence.inv_fun_map, tensor_comp, Functor.map_comp,
      tensor_comp, ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp,
      assoc, assoc, ← tensor_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app, ← tensor_comp]
    dsimp
    rw [comp_id, comp_id])
  (associativity := fun X Y Z ↦ by
    dsimp
    simp only [← id_tensorHom, ← tensorHom_id]
    rw [Equivalence.inv_fun_map, Equivalence.inv_fun_map, Functor.map_comp,
      Functor.map_comp, assoc, assoc, e.inverse.map_id, e.inverse.map_id,
      comp_tensor_id, id_tensor_comp, Functor.map_comp, assoc, id_tensor_comp,
      comp_tensor_id, ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp]
    congr 2
    slice_lhs 3 3 => rw [← tensor_id_comp_id_tensor]
    slice_lhs 2 3 =>
      rw [← comp_tensor_id, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    rw [id_comp]
    slice_rhs 2 3 =>
      rw [←id_tensor_comp, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    rw [id_comp]
    conv_rhs => rw [← id_tensor_comp_tensor_id _ (e.unitInv.app X)]
    dsimp only [Functor.comp_obj]
    slice_rhs 3 4 =>
      rw [← id_tensor_comp, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    simp only [associator_conjugation, ←tensor_id, ←tensor_comp, Iso.inv_hom_id,
      Iso.inv_hom_id_assoc, assoc, id_comp, comp_id])
  (left_unitality := fun X ↦ by
    dsimp
    simp only [← id_tensorHom, ← tensorHom_id]
    rw [e.inverse.map_id, e.inverse.map_id, tensor_id, Functor.map_comp, assoc,
      Equivalence.counit_app_functor, ← e.functor.map_comp, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← leftUnitor_naturality',
      ← tensor_comp_assoc, comp_id, id_comp, id_comp]
    rfl)
  (right_unitality := fun X ↦ by
    dsimp
    simp only [← id_tensorHom, ← tensorHom_id]
    rw [Functor.map_comp, assoc, e.inverse.map_id, e.inverse.map_id, tensor_id,
      Functor.map_id, id_comp, Equivalence.counit_app_functor, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← rightUnitor_naturality',
      ← tensor_comp_assoc, id_comp, comp_id]
    rfl)
#align category_theory.monoidal.lax_to_transported CategoryTheory.Monoidal.laxToTransported

end

/-- We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps]
def toTransported (e : C ≌ D) : MonoidalFunctor C (Transported e) where
  toLaxMonoidalFunctor := laxToTransported e
  ε_isIso := by
    dsimp
    infer_instance
  μ_isIso X Y := by
    dsimp
    infer_instance
#align category_theory.monoidal.to_transported CategoryTheory.Monoidal.toTransported

end

instance (e : C ≌ D) : IsEquivalence (toTransported e).toFunctor :=
  inferInstanceAs (IsEquivalence e.functor)

/-- We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps!]
def fromTransported (e : C ≌ D) : MonoidalFunctor (Transported e) C := by
  dsimp only [transport, Transported.instMonoidalCategory]
  exact fromInduced (D := Transported e) e.inverse _
#align category_theory.monoidal.from_transported CategoryTheory.Monoidal.fromTransported

instance instIsEquivalence_fromTransported (e : C ≌ D) :
    IsEquivalence (fromTransported e).toFunctor :=
  inferInstanceAs <| IsEquivalence <| (e.functor.asEquivalence).inverse

#noalign category_theory.monoidal.lax_to_transported

/-- We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
@[simps!]
def toTransported (e : C ≌ D) : MonoidalFunctor C (Transported e) :=
  monoidalInverse (fromTransported e)
#align category_theory.monoidal.to_transported CategoryTheory.Monoidal.toTransported

instance (e : C ≌ D) : IsEquivalence (toTransported e).toFunctor := by
  dsimp [toTransported]
  infer_instance

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps! hom inv]
def transportedMonoidalUnitIso (e : C ≌ D) :
    LaxMonoidalFunctor.id C ≅
      (toTransported e).toLaxMonoidalFunctor ⊗⋙ (fromTransported e).toLaxMonoidalFunctor :=
  asIso (monoidalCounit (fromTransported e)) |>.symm
#align category_theory.monoidal.transported_monoidal_unit_iso CategoryTheory.Monoidal.transportedMonoidalUnitIso

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps! hom inv]
def transportedMonoidalCounitIso (e : C ≌ D) :
    (fromTransported e).toLaxMonoidalFunctor ⊗⋙ (toTransported e).toLaxMonoidalFunctor ≅
      LaxMonoidalFunctor.id (Transported e) :=
  asIso (monoidalUnit (fromTransported e)) |>.symm
#align category_theory.monoidal.transported_monoidal_counit_iso CategoryTheory.Monoidal.transportedMonoidalCounitIso

end CategoryTheory.Monoidal
