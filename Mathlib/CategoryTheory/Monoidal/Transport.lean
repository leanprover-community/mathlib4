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
structure InducingFunctorData (F : D ⥤ C) where
  tensorObj : D → D → D
  /-- Analogous to the reversed version of `CategoryTheory.LaxMonoidalFunctor.μIso` -/
  μIsoSymm : ∀ X Y,
    F.obj (tensorObj X Y) ≅ F.obj X ⊗ F.obj Y
  whiskerLeft : ∀ (X : D) {Y₁ Y₂ : D} (_f : Y₁ ⟶ Y₂), tensorObj X Y₁ ⟶ tensorObj X Y₂
  whiskerLeft_eq : ∀ (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂),
    F.map (whiskerLeft X f)
      = (μIsoSymm _ _).hom ≫ (F.obj X ◁ F.map f) ≫ (μIsoSymm _ _).inv :=
    by aesop_cat
  whiskerRight : ∀ {X₁ X₂ : D} (_f : X₁ ⟶ X₂) (Y : D), tensorObj X₁ Y ⟶ tensorObj X₂ Y
  whiskerRight_eq : ∀ {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D),
    F.map (whiskerRight f Y)
      = (μIsoSymm _ _).hom ≫ (F.map f ▷ F.obj Y) ≫ (μIsoSymm _ _).inv :=
    by aesop_cat
  tensorHom :
    ∀ {X₁ Y₁ X₂ Y₂ : D} (_f : X₁ ⟶ Y₁) (_g : X₂ ⟶ Y₂), tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂
  tensorHom_eq :
    ∀ {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂),
      F.map (tensorHom f g)
        = (μIsoSymm _ _).hom ≫ (F.map f ⊗ F.map g) ≫ (μIsoSymm _ _).inv :=
    by aesop_cat
  tensorUnit' : D
  /-- Analogous to the reversed version of `CategoryTheory.LaxMonoidalFunctor.εIso` -/
  εIsoSymm : F.obj tensorUnit' ≅ 𝟙_ _
  associator : ∀ X Y Z : D, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z)
  associator_eq : ∀ X Y Z : D,
    F.map (associator X Y Z).hom =
      ((μIsoSymm _ _ ≪≫ (μIsoSymm _ _ ⊗ .refl _))
        ≪≫ α_ (F.obj X) (F.obj Y) (F.obj Z)
        ≪≫ ((.refl _ ⊗ (μIsoSymm _ _).symm) ≪≫ (μIsoSymm _ _).symm)).hom :=
    by aesop_cat
  leftUnitor : ∀ X : D, tensorObj tensorUnit' X ≅ X
  leftUnitor_eq : ∀ X : D,
    F.map (leftUnitor X).hom =
      ((μIsoSymm _ _ ≪≫ (εIsoSymm ⊗ .refl _)) ≪≫ λ_ (F.obj X)).hom :=
    by aesop_cat
  rightUnitor : ∀ X : D, tensorObj X tensorUnit' ≅ X
  rightUnitor_eq : ∀ X : D,
    F.map (rightUnitor X).hom =
      ((μIsoSymm _ _ ≪≫ (.refl _ ⊗ εIsoSymm)) ≪≫ ρ_ (F.obj X)).hom :=
    by aesop_cat

attribute [inherit_doc MonoidalCategory.tensorObj] InducingFunctorData.tensorObj
attribute [inherit_doc MonoidalCategory.whiskerLeft] InducingFunctorData.whiskerLeft
attribute [inherit_doc MonoidalCategory.whiskerRight] InducingFunctorData.whiskerRight
attribute [inherit_doc MonoidalCategory.tensorHom] InducingFunctorData.tensorHom
attribute [inherit_doc MonoidalCategory.tensorUnit'] InducingFunctorData.tensorUnit'
attribute [inherit_doc MonoidalCategory.associator] InducingFunctorData.associator
attribute [inherit_doc MonoidalCategory.leftUnitor] InducingFunctorData.leftUnitor
attribute [inherit_doc MonoidalCategory.rightUnitor] InducingFunctorData.rightUnitor

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
@[simps]
abbrev induced (F : D ⥤ C) [Faithful F] (fData : InducingFunctorData F):
    MonoidalCategory.{v₂} D where
  -- the data fields are exactly as provided
  tensorObj := fData.tensorObj
  whiskerLeft := fData.whiskerLeft
  whiskerRight := fData.whiskerRight
  tensorHom := fData.tensorHom
  tensorUnit' := fData.tensorUnit'
  associator := fData.associator
  leftUnitor := fData.leftUnitor
  rightUnitor := fData.rightUnitor
  tensorHom_def {X₁ Y₁ X₂ Y₂} f g := F.map_injective <| by
    dsimp
    rw [fData.tensorHom_eq, Functor.map_comp, fData.whiskerRight_eq, fData.whiskerLeft_eq]
    simp only [tensorHom_def, assoc, Iso.inv_hom_id_assoc]
  tensor_id X₁ X₂ := F.map_injective <| by cases fData; aesop_cat
  tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ := F.map_injective <| by cases fData; aesop_cat
  whiskerLeft_id X Y := F.map_injective <| by simp [fData.whiskerLeft_eq]
  id_whiskerRight X Y := F.map_injective <| by simp [fData.whiskerRight_eq]
  triangle X Y := F.map_injective <| by cases fData; aesop_cat
  pentagon W X Y Z := F.map_injective <| by
    have := MonoidalCategory.pentagon (F.obj W) (F.obj X) (F.obj Y) (F.obj Z)
    dsimp
    simp only [Functor.map_comp, fData.tensorHom_eq, fData.associator_eq, Iso.trans_assoc,
      Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom, Functor.map_id, comp_tensor_id,
      associator_conjugation, tensor_id, assoc, id_tensor_comp, Iso.inv_hom_id_assoc,
      tensor_inv_hom_id_assoc, id_comp, inv_hom_id_tensor_assoc, id_tensor_comp_tensor_id_assoc,
      Iso.cancel_iso_hom_left]
    congr 1
    simp only [←assoc]
    congr 2
    simp only [assoc, ←tensor_comp, id_comp, Iso.inv_hom_id, tensor_id]
    congr 1
    conv_rhs => rw [←tensor_id_comp_id_tensor]
    simp only [assoc]
    congr 1
    rw [Iso.inv_comp_eq]
    conv_lhs => rw [←id_comp (𝟙 (F.obj W)), tensor_comp]
    slice_lhs 0 2 => rw [this]
    rw [assoc]
    congr 1
    rw [←associator_naturality, tensor_id]
  leftUnitor_naturality {X Y : D} f := F.map_injective <| by
    have := leftUnitor_naturality (F.map f)
    dsimp
    simp only [Functor.map_comp, fData.tensorHom_eq, Functor.map_id, fData.leftUnitor_eq,
      Iso.trans_assoc, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, assoc, Iso.inv_hom_id_assoc,
      id_tensor_comp_tensor_id_assoc, Iso.cancel_iso_hom_left]
    rw [←this, ←assoc, ←tensor_comp, id_comp, comp_id]
  rightUnitor_naturality {X Y : D} f := F.map_injective <| by
    have := rightUnitor_naturality (F.map f)
    dsimp
    simp only [Functor.map_comp, fData.tensorHom_eq, Functor.map_id, fData.rightUnitor_eq,
      Iso.trans_assoc, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, assoc, Iso.inv_hom_id_assoc,
      tensor_id_comp_id_tensor_assoc, Iso.cancel_iso_hom_left]
    rw [←this, ←assoc, ←tensor_comp, id_comp, comp_id]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := F.map_injective <| by
    have := associator_naturality (F.map f₁) (F.map f₂) (F.map f₃)
    dsimp
    simp [fData.associator_eq, fData.tensorHom_eq]
    simp_rw [←assoc, ←tensor_comp, assoc, Iso.inv_hom_id, ←assoc]
    congr 1
    conv_rhs => rw [←comp_id (F.map f₁), ←id_comp (F.map f₁)]
    simp only [tensor_comp]
    simp only [tensor_id, comp_id, assoc, tensor_inv_hom_id_assoc, id_comp]
    slice_rhs 2 3 => rw [←this]
    simp only [← assoc, Iso.inv_hom_id, comp_id]
    congr 2
    simp_rw [←tensor_comp, id_comp]


/--
We can upgrade `F` to a monoidal functor from `D` to `E` with the induced structure.
-/
@[simps]
def fromInduced (F : D ⥤ C) [Faithful F] (fData : InducingFunctorData F):
    letI := induced F fData
    MonoidalFunctor D C :=
  letI := induced F fData
  { toFunctor := F
    ε := fData.εIsoSymm.inv
    μ := fun X Y => (fData.μIsoSymm X Y).inv
    μ_natural := by cases fData; aesop_cat
    associativity := by cases fData; aesop_cat
    left_unitality := by cases fData; aesop_cat
    right_unitality := by cases fData; aesop_cat }

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
def transport (e : C ≌ D) : MonoidalCategory.{v₂} D :=
  induced e.inverse
    { tensorObj := fun X Y => e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
      μIsoSymm := fun X Y => (e.unitIso.app _).symm
      whiskerLeft := fun X _ _ f ↦ e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
      whiskerRight := fun f X ↦ e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
      tensorHom := fun f g => e.functor.map (e.inverse.map f ⊗ e.inverse.map g)
      tensorUnit' := e.functor.obj (𝟙_ C)
      εIsoSymm := (e.unitIso.app _).symm
      associator := fun X Y Z =>
        e.functor.mapIso
          (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫
            α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫
            (Iso.refl _ ⊗ e.unitIso.app _))
      leftUnitor := fun X =>
        e.functor.mapIso (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫ λ_ (e.inverse.obj X)) ≪≫
          e.counitIso.app _
      rightUnitor := fun X =>
        e.functor.mapIso ((Iso.refl _ ⊗ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
          e.counitIso.app _ }
#align category_theory.monoidal.transport CategoryTheory.Monoidal.transport

/-- A type synonym for `D`, which will carry the transported monoidal structure. -/
@[nolint unusedArguments]
def Transported (_ : C ≌ D) := D
#align category_theory.monoidal.transported CategoryTheory.Monoidal.Transported

instance (e : C ≌ D) : Category (Transported e) := (inferInstance : Category D)

instance Transported.instMonoidalCategory (e : C ≌ D): MonoidalCategory (Transported e) :=
  transport e

instance (e : C ≌ D) : Inhabited (Transported e) :=
  ⟨𝟙_ _⟩

/-- We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps!]
def fromTransported (e : C ≌ D) : MonoidalFunctor (Transported e) C := fromInduced e.inverse _
#align category_theory.monoidal.from_transported CategoryTheory.Monoidal.fromTransported

instance instIsEquivalence_fromTransported (e : C ≌ D) :
    IsEquivalence (fromTransported e).toFunctor := by
  dsimp [fromTransported]
  infer_instance

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
