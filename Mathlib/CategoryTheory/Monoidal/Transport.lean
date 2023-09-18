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

/-- Induce a monoidal structure along an faithful functor of (plain) categories,
-/
@[simps]
abbrev induced (e : D ⥤ C) [Faithful e]
    (tensorObj : D → D → D)
    (μIsoSymm : ∀ X Y,
      e.obj (tensorObj X Y) ≅ e.obj X ⊗ e.obj Y)
    (whiskerLeft : ∀ (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂), tensorObj X Y₁ ⟶ tensorObj X Y₂)
    (whiskerLeft_eq : ∀ (X : D) {Y₁ Y₂ : D} (f : Y₁ ⟶ Y₂),
      e.map (whiskerLeft X f)
        = (μIsoSymm _ _).hom ≫ (e.obj X ◁ e.map f) ≫ (μIsoSymm _ _).inv :=
      by aesop_cat)
    (whiskerRight : ∀ {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D), tensorObj X₁ Y ⟶ tensorObj X₂ Y)
    (whiskerRight_eq : ∀ {X₁ X₂ : D} (f : X₁ ⟶ X₂) (Y : D),
      e.map (whiskerRight f Y)
        = (μIsoSymm _ _).hom ≫ (e.map f ▷ e.obj Y) ≫ (μIsoSymm _ _).inv :=
      by aesop_cat)
    (tensorHom :
      ∀ {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂), tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂)
    (tensorHom_eq :
      ∀ {X₁ Y₁ X₂ Y₂ : D} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂),
        e.map (tensorHom f g)
          = (μIsoSymm _ _).hom ≫ (e.map f ⊗ e.map g) ≫ (μIsoSymm _ _).inv :=
      by aesop_cat)
    (tensorUnit' : D)
    (εIsoSymm : e.obj tensorUnit' ≅ 𝟙_ _)
    (associator : ∀ X Y Z : D, tensorObj (tensorObj X Y) Z ≅ tensorObj X (tensorObj Y Z))
    (associator_eq : ∀ X Y Z : D,
      e.map (associator X Y Z).hom =
        ((μIsoSymm _ _ ≪≫ (μIsoSymm _ _ ⊗ .refl _))
          ≪≫ α_ (e.obj X) (e.obj Y) (e.obj Z)
          ≪≫ ((.refl _ ⊗ (μIsoSymm _ _).symm) ≪≫ (μIsoSymm _ _).symm)).hom :=
      by aesop_cat)
    (leftUnitor : ∀ X : D, tensorObj tensorUnit' X ≅ X)
    (leftUnitor_eq : ∀ X : D,
      e.map (leftUnitor X).hom =
        ((μIsoSymm _ _ ≪≫ (εIsoSymm ⊗ .refl _)) ≪≫ λ_ (e.obj X)).hom :=
      by aesop_cat)
    (rightUnitor : ∀ X : D, tensorObj X tensorUnit' ≅ X)
    (rightUnitor_eq : ∀ X : D,
      e.map (rightUnitor X).hom =
        ((μIsoSymm _ _ ≪≫ (.refl _ ⊗ εIsoSymm)) ≪≫ ρ_ (e.obj X)).hom :=
      by aesop_cat) :
    MonoidalCategory.{v₂} D where
      tensorObj := tensorObj
      whiskerLeft := whiskerLeft
      whiskerRight := whiskerRight
      tensorHom := tensorHom
      tensorUnit' := tensorUnit'
      associator := associator
      leftUnitor := leftUnitor
      rightUnitor := rightUnitor
      tensorHom_def {X₁ Y₁ X₂ Y₂} f g := e.map_injective <| by
        dsimp
        rw [tensorHom_eq, Functor.map_comp, whiskerRight_eq, whiskerLeft_eq]
        sorry
      tensor_id X₁ X₂ := e.map_injective <| by
        dsimp
        sorry
      tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ := e.map_injective <| by
        dsimp
        sorry
      whiskerLeft_id X Y := e.map_injective <| by simp [whiskerLeft_eq]
      id_whiskerRight X Y := e.map_injective <| by simp [whiskerRight_eq]
      associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := e.map_injective <| by
        simp [associator_eq, tensorHom_eq]
        sorry
      leftUnitor_naturality {X Y : D} f := e.map_injective <| by
        simp [leftUnitor_eq, tensorHom_eq]
        sorry
      rightUnitor_naturality {X Y : D} f := e.map_injective <| by
        simp [rightUnitor_eq, tensorHom_eq]
        sorry
      pentagon W X Y Z := e.map_injective <| by
        have := MonoidalCategory.pentagon (e.obj W) (e.obj X) (e.obj Y) (e.obj Z)
        simp [associator_eq, tensorHom_eq]
        congr 2
        simp only [←assoc]
        congr 2
        simp
        sorry
      triangle X Y :=  e.map_injective <| by aesop_cat

/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
@[simps!
  tensorObj whiskerLeft whiskerRight tensorHom tensorUnit' associator leftUnitor rightUnitor]
def transport (e : C ≌ D) : MonoidalCategory.{v₂} D :=
  induced
    (e := e.inverse)
    (tensorObj := fun X Y => e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y))
    (μIsoSymm := fun X Y => (e.unitIso.app _).symm)
    (whiskerLeft := fun X _ _ f ↦ e.functor.map (e.inverse.obj X ◁ e.inverse.map f))
    (whiskerRight := fun f X ↦ e.functor.map (e.inverse.map f ▷ e.inverse.obj X))
    (tensorHom := fun f g => e.functor.map (e.inverse.map f ⊗ e.inverse.map g))
    (tensorUnit' := e.functor.obj (𝟙_ C))
    (εIsoSymm := (e.unitIso.app _).symm)
    (associator := fun X Y Z =>
      e.functor.mapIso
        (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫
          α_ (e.inverse.obj X) (e.inverse.obj Y) (e.inverse.obj Z) ≪≫ (Iso.refl _ ⊗ e.unitIso.app _)))
    (leftUnitor := fun X =>
      e.functor.mapIso (((e.unitIso.app _).symm ⊗ Iso.refl _) ≪≫ λ_ (e.inverse.obj X)) ≪≫
        e.counitIso.app _)
    (rightUnitor := fun X =>
      e.functor.mapIso ((Iso.refl _ ⊗ (e.unitIso.app _).symm) ≪≫ ρ_ (e.inverse.obj X)) ≪≫
        e.counitIso.app _)

-- porting note: it was @[simps {attrs := [`_refl_lemma]}]
/-- Transport a monoidal structure along an equivalence of (plain) categories.
-/
-- TODO: delete this once the `sorry`s above are filled
@[simps]
def transport' (e : C ≌ D) : MonoidalCategory.{v₂} D where
  tensorObj X Y := e.functor.obj (e.inverse.obj X ⊗ e.inverse.obj Y)
  whiskerLeft := fun X _ _ f ↦ e.functor.map (e.inverse.obj X ◁ e.inverse.map f)
  whiskerRight := fun f X ↦ e.functor.map (e.inverse.map f ▷ e.inverse.obj X)
  tensorHom_def := by simp [tensorHom_def]
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
    simp only [Iso.hom_inv_id_app_assoc, comp_tensor_id, Equivalence.unit_inverse_comp, assoc,
      Equivalence.inv_fun_map, comp_id, Functor.map_comp, id_tensor_comp, e.inverse.map_id]
    simp only [← e.functor.map_comp]
    congr 2
    slice_lhs 2 3 =>
      rw [← id_tensor_comp]
      simp
    rw [Category.id_comp, ← associator_naturality_assoc, triangle]
  pentagon W X Y Z := by
    dsimp
    simp only [Iso.hom_inv_id_app_assoc, comp_tensor_id, assoc, Equivalence.inv_fun_map,
      Functor.map_comp, id_tensor_comp, e.inverse.map_id]
    simp only [← e.functor.map_comp]
    congr 2
    slice_lhs 4 5 =>
      rw [← comp_tensor_id, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 5 6 =>
      rw [← id_tensor_comp, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id]
    simp only [Category.id_comp, Category.assoc]
    slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
    slice_rhs 1 2 => rw [← tensor_id, ← associator_naturality]
    slice_rhs 3 4 => rw [← tensor_id, associator_naturality]
    slice_rhs 2 3 => rw [← pentagon]
    simp only [Category.assoc]
    congr 2
    slice_lhs 1 2 => rw [associator_naturality]
    simp only [Category.assoc]
    congr 1
    slice_lhs 1 2 =>
      rw [← id_tensor_comp, ← comp_tensor_id, Iso.hom_inv_id_app]
      dsimp
      rw [tensor_id, tensor_id]
    simp only [Category.id_comp, Category.assoc]
  leftUnitor_naturality f := by
    dsimp
    simp only [Functor.map_comp, Functor.map_id, Category.assoc]
    erw [← e.counitIso.hom.naturality]
    simp only [Functor.comp_map, ← e.functor.map_comp_assoc]
    congr 2
    rw [id_tensor_comp_tensor_id_assoc, ← tensor_id_comp_id_tensor_assoc,
      leftUnitor_naturality]
  rightUnitor_naturality f := by
    dsimp
    simp only [Functor.map_comp, Functor.map_id, Category.assoc]
    erw [← e.counitIso.hom.naturality]
    simp only [Functor.comp_map, ← e.functor.map_comp_assoc]
    congr 2
    erw [tensor_id_comp_id_tensor_assoc, ← id_tensor_comp_tensor_id_assoc,
      rightUnitor_naturality]
  associator_naturality f₁ f₂ f₃ := by
    dsimp
    simp only [Equivalence.inv_fun_map, Functor.map_comp, Category.assoc]
    simp only [← e.functor.map_comp]
    congr 1
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
    rw [Equivalence.inv_fun_map, Equivalence.inv_fun_map, tensor_comp, Functor.map_comp,
      tensor_comp, ← e.functor.map_comp, ← e.functor.map_comp, ← e.functor.map_comp,
      assoc, assoc, ← tensor_comp, Iso.hom_inv_id_app, Iso.hom_inv_id_app, ← tensor_comp]
    dsimp
    rw [comp_id, comp_id]
  associativity X Y Z := by
    dsimp
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
      Iso.inv_hom_id_assoc, assoc, id_comp, comp_id]
  left_unitality X := by
    dsimp
    rw [e.inverse.map_id, e.inverse.map_id, tensor_id, Functor.map_comp, assoc,
      Equivalence.counit_app_functor, ← e.functor.map_comp, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← leftUnitor_naturality,
      ← tensor_comp_assoc, comp_id, id_comp, id_comp]
    rfl
  right_unitality X := by
    dsimp
    rw [Functor.map_comp, assoc, e.inverse.map_id, e.inverse.map_id, tensor_id,
      Functor.map_id, id_comp, Equivalence.counit_app_functor, ← e.functor.map_comp,
      ← e.functor.map_comp, ← e.functor.map_comp, ← rightUnitor_naturality,
      ← tensor_comp_assoc, id_comp, comp_id]
    rfl
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

instance (e : C ≌ D) : IsEquivalence (toTransported e).toFunctor := by
  dsimp
  infer_instance

/-- We can upgrade `e.inverse` to a monoidal functor from `D` with the transported structure to `C`.
-/
@[simps!]
def fromTransported (e : C ≌ D) : MonoidalFunctor (Transported e) C :=
  monoidalInverse (toTransported e)
#align category_theory.monoidal.from_transported CategoryTheory.Monoidal.fromTransported

instance instIsEquivalence_fromTransported (e : C ≌ D) :
    IsEquivalence (fromTransported e).toFunctor := by
  dsimp [fromTransported]
  infer_instance

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
