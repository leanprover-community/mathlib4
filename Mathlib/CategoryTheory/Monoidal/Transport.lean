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
`Function.Injective.monoid`.

We then upgrade the original functor and its inverse to monoidal functors
with respect to the new monoidal structure on `D`.
-/


universe v₁ v₂ u₁ u₂

section

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
      Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom,
      Functor.map_id, comp_whiskerRight, whisker_assoc, assoc, MonoidalCategory.whiskerLeft_comp,
      Iso.hom_inv_id_assoc, whiskerLeft_hom_inv_assoc, hom_inv_whiskerRight_assoc,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_left]
    slice_lhs 5 6 =>
      rw [← MonoidalCategory.whiskerLeft_comp, hom_inv_whiskerRight]
    rw [whisker_exchange_assoc]
    simp
  leftUnitor_naturality {X Y : D} f := F.map_injective <| by
    simp [fData.leftUnitor_eq, fData.tensorHom_eq, whisker_exchange_assoc,
      id_tensorHom, tensorHom_id]
  rightUnitor_naturality {X Y : D} f := F.map_injective <| by
    simp [fData.rightUnitor_eq, fData.tensorHom_eq, ← whisker_exchange_assoc,
      id_tensorHom, tensorHom_id]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := F.map_injective <| by
    simp [fData.tensorHom_eq, fData.associator_eq, tensorHom_def, whisker_exchange_assoc]

/--
We can upgrade `F` to a monoidal functor from `D` to `E` with the induced structure.
-/
def fromInduced [MonoidalCategoryStruct D] (F : D ⥤ C) [Faithful F]
    (fData : InducingFunctorData F) :
    letI := induced F fData
    MonoidalFunctor D C := by
  letI := induced F fData
  apply MonoidalFunctor.mk'
  case F => exact F
  case εIso => exact fData.εIso
  case μIso => exact fData.μIso
  all_goals cases fData; aesop_cat

section

variable [MonoidalCategoryStruct D] (F : D ⥤ C) [Faithful F]
         (fData : InducingFunctorData F)

@[simp] lemma fromInduced_obj (X : D) :
    letI := induced F fData
    (fromInduced F fData).obj X = F.obj X := rfl

@[simp] lemma fromInduced_map {X Y} (f : X ⟶ Y) :
    letI := induced F fData
    (fromInduced F fData).map f = F.map f := rfl

@[simp] lemma fromInduced_μIso (X Y : D) :
    letI := induced F fData
    (fromInduced F fData).μIso X Y = fData.μIso X Y := rfl

@[simp] lemma fromInduced_εIso :
    letI := induced F fData
    (fromInduced F fData).εIso = fData.εIso := rfl

end

variable (e : C ≌ D)

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps]
def transportStruct : MonoidalCategoryStruct.{v₂} D where
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

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[nolint unusedArguments]
def Transported (_ : C ≌ D) := D
#align category_theory.monoidal.transported CategoryTheory.Monoidal.Transported

instance : Category (Transported e) := inferInstanceAs (Category D)

instance Transported.instMonoidalCategoryStruct :
    MonoidalCategoryStruct (Transported e) :=
  transportStruct e

private abbrev fromTransportedFunctor : Transported e ⥤ C := e.inverse

private abbrev transportInducingData :
    InducingFunctorData (fromTransportedFunctor e) :=
  { μIso := fun X Y => e.unitIso.app (e.inverse.obj X ⊗ e.inverse.obj Y)
    εIso := e.unitIso.app (𝟙_ C) }

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
instance transport : MonoidalCategory (Transported e) :=
  induced (fromTransportedFunctor e) (transportInducingData e)
#align category_theory.monoidal.transport CategoryTheory.Monoidal.transport

instance : Inhabited (Transported e) := ⟨𝟙_ _⟩

/-- We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
def fromTransported : MonoidalFunctor (Transported e) C :=
  fromInduced (fromTransportedFunctor e) (transportInducingData e)
#align category_theory.monoidal.from_transported CategoryTheory.Monoidal.fromTransported

variable {e}

@[simp] lemma fromTransported_obj (X : Transported e) :
    (fromTransported e).obj X = e.inverse.obj X := rfl

@[simp] lemma fromTransported_map {X Y} (f : X ⟶ Y) :
    (fromTransported e).map f = e.inverse.map f := rfl

@[simp] lemma fromTransported_μIso (X Y : Transported e) :
    (fromTransported e).μIso X Y =
      e.unitIso.app (e.inverse.obj X ⊗ e.inverse.obj Y) := rfl

variable (e)

@[simp] lemma fromTransported_εIso :
    (fromTransported e).εIso = e.unitIso.app (𝟙_ C) := rfl

instance instIsEquivalence_fromTransported (e : C ≌ D) :
    IsEquivalence (fromTransported e).toFunctor :=
  inferInstanceAs (IsEquivalence e.inverse)

#noalign category_theory.monoidal.lax_to_transported

/-- We can upgrade `e.functor` to a monoidal functor from `C` to `D` with the transported structure.
-/
def toTransported : MonoidalFunctor C (Transported e) :=
  monoidalInverse (fromTransported e)
#align category_theory.monoidal.to_transported CategoryTheory.Monoidal.toTransported

variable {e}

@[simp] lemma toTransported_obj (X : C) :
    (toTransported e).obj X = e.functor.obj X := rfl

@[simp] lemma toTransported_map {X Y} (f : X ⟶ Y) :
    (toTransported e).map f = e.functor.map f := rfl

@[simp] lemma toTransported_μIso (X Y : C) :
    (toTransported e).μIso X Y =
      (monoidalInverse (fromTransported e)).μIso X Y := rfl

variable (e)

@[simp] lemma toTransported_εIso :
    (toTransported e).εIso = (monoidalInverse (fromTransported e)).εIso := rfl

instance : IsEquivalence (toTransported e).toFunctor :=
  inferInstanceAs (IsEquivalence e.functor)

/-- The unit isomorphism upgrades to a monoidal isomorphism. -/
@[simps! hom inv]
def transportedMonoidalUnitIso :
    MonoidalFunctor.id C ≅ (toTransported e) ⊗⋙ (fromTransported e) :=
  (Equivalence.monoidalCounitIso (fromTransported e)).symm
#align category_theory.monoidal.transported_monoidal_unit_iso CategoryTheory.Monoidal.transportedMonoidalUnitIso

/-- The counit isomorphism upgrades to a monoidal isomorphism. -/
@[simps! hom inv]
def transportedMonoidalCounitIso :
    fromTransported e ⊗⋙ toTransported e ≅ MonoidalFunctor.id (Transported e) :=
  (Equivalence.monoidalUnitIso (fromTransported e)).symm
#align category_theory.monoidal.transported_monoidal_counit_iso CategoryTheory.Monoidal.transportedMonoidalCounitIso

end CategoryTheory.Monoidal
