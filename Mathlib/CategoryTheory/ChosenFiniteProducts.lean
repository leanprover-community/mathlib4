/-
Copyright (c) 2024 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Robin Carlier
-/
import Mathlib.CategoryTheory.Monoidal.OfChosenFiniteProducts.Symmetric
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Categories with chosen finite products

We introduce a class, `ChosenFiniteProducts`, which bundles explicit choices
for a terminal object and binary products in a category `C`.
This is primarily useful for categories which have finite products with good
definitional properties, such as the category of types.

Given a category with such an instance, we also provide the associated
symmetric monoidal structure so that one can write `X ⊗ Y` for the explicit
binary product and `𝟙_ C` for the explicit terminal object.

# Projects

- Construct an instance of chosen finite products in the category of affine scheme, using
  the tensor product.
- Construct chosen finite products in other categories appearing "in nature".

-/

namespace CategoryTheory

universe v v₁ u u₁

/--
An instance of `ChosenFiniteProducts C` bundles an explicit choice of a binary
product of two objects of `C`, and a terminal object in `C`.

Users should use the monoidal notation: `X ⊗ Y` for the product and `𝟙_ C` for
the terminal object.
-/
class ChosenFiniteProducts (C : Type u) [Category.{v} C] where
  /-- A choice of a limit binary fan for any two objects of the category. -/
  product : (X Y : C) → Limits.LimitCone (Limits.pair X Y)
  /-- A choice of a terminal object. -/
  terminal : Limits.LimitCone (Functor.empty.{0} C)

namespace ChosenFiniteProducts

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    MonoidalCategory C :=
  monoidalOfChosenFiniteProducts terminal product

instance (priority := 100) (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] :
    SymmetricCategory C :=
  symmetricOfChosenFiniteProducts _ _

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]

open MonoidalCategory

/--
The unique map to the terminal object.
-/
def toUnit (X : C) : X ⟶ 𝟙_ C :=
  terminal.isLimit.lift <| .mk _ <| .mk (fun x => x.as.elim) fun x => x.as.elim

instance (X : C) : Unique (X ⟶ 𝟙_ C) where
  default := toUnit _
  uniq _ := terminal.isLimit.hom_ext fun ⟨j⟩ => j.elim

/--
This lemma follows from the preexisting `Unique` instance, but
it is often convenient to use it directly as `apply toUnit_unique` forcing
lean to do the necessary elaboration.
-/
lemma toUnit_unique {X : C} (f g : X ⟶ 𝟙_ _) : f = g :=
  Subsingleton.elim _ _

/--
Construct a morphism to the product given its two components.
-/
def lift {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : T ⟶ X ⊗ Y :=
  (product X Y).isLimit.lift <| Limits.BinaryFan.mk f g

/--
The first projection from the product.
-/
def fst (X Y : C) : X ⊗ Y ⟶ X :=
  letI F : Limits.BinaryFan X Y := (product X Y).cone
  F.fst

/--
The second projection from the product.
-/
def snd (X Y : C) : X ⊗ Y ⟶ Y :=
  letI F : Limits.BinaryFan X Y := (product X Y).cone
  F.snd

@[reassoc (attr := simp)]
lemma lift_fst {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ fst _ _ = f := by
  simp [lift, fst]

@[reassoc (attr := simp)]
lemma lift_snd {T X Y : C} (f : T ⟶ X) (g : T ⟶ Y) : lift f g ≫ snd _ _ = g := by
  simp [lift, snd]

instance mono_lift_of_mono_left {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_fst _ _

instance mono_lift_of_mono_right {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (lift f g) :=
  mono_of_mono_fac <| lift_snd _ _

@[ext 1050]
lemma hom_ext {T X Y : C} (f g : T ⟶ X ⊗ Y)
    (h_fst : f ≫ fst _ _ = g ≫ fst _ _)
    (h_snd : f ≫ snd _ _ = g ≫ snd _ _) :
    f = g :=
  (product X Y).isLimit.hom_ext fun ⟨j⟩ => j.recOn h_fst h_snd

@[reassoc (attr := simp)]
lemma tensorHom_fst {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ g) ≫ fst _ _ = fst _ _ ≫ f := lift_fst _ _

@[reassoc (attr := simp)]
lemma tensorHom_snd {X₁ X₂ Y₁ Y₂ : C} (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) :
    (f ⊗ g) ≫ snd _ _ = snd _ _ ≫ g := lift_snd _ _

@[reassoc (attr := simp)]
lemma whiskerLeft_fst (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (X ◁ g) ≫ fst _ _ = fst _ _ :=
  (tensorHom_fst _ _).trans (by simp)

@[reassoc (attr := simp)]
lemma whiskerLeft_snd (X : C) {Y₁ Y₂ : C} (g : Y₁ ⟶ Y₂) :
    (X ◁ g) ≫ snd _ _ = snd _ _ ≫ g :=
  tensorHom_snd _ _

@[reassoc (attr := simp)]
lemma whiskerRight_fst {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (f ▷ Y) ≫ fst _ _ = fst _ _ ≫ f :=
  tensorHom_fst _ _

@[reassoc (attr := simp)]
lemma whiskerRight_snd {X₁ X₂ : C} (f : X₁ ⟶ X₂) (Y : C) :
    (f ▷ Y) ≫ snd _ _ = snd _ _ :=
  (tensorHom_snd _ _).trans (by simp)

@[reassoc (attr := simp)]
lemma associator_hom_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ fst _ _ = fst _ _ ≫ fst _ _ := lift_fst _ _

@[reassoc (attr := simp)]
lemma associator_hom_snd_fst (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ fst _ _ = fst _ _ ≫ snd _ _  := by
  erw [lift_snd_assoc, lift_fst]
  rfl

@[reassoc (attr := simp)]
lemma associator_hom_snd_snd (X Y Z : C) :
    (α_ X Y Z).hom ≫ snd _ _ ≫ snd _ _ = snd _ _  := by
  erw [lift_snd_assoc, lift_snd]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_fst (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ fst _ _ = fst _ _ := by
  erw [lift_fst_assoc, lift_fst]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_fst_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ fst _ _ ≫ snd _ _ = snd _ _ ≫ fst _ _ := by
  erw [lift_fst_assoc, lift_snd]
  rfl

@[reassoc (attr := simp)]
lemma associator_inv_snd (X Y Z : C) :
    (α_ X Y Z).inv ≫ snd _ _ = snd _ _ ≫ snd _ _ := lift_snd _ _

/--
Construct an instance of `ChosenFiniteProducts C` given an instance of `HasFiniteProducts C`.
-/
noncomputable
def ofFiniteProducts
    (C : Type u) [Category.{v} C] [Limits.HasFiniteProducts C] :
    ChosenFiniteProducts C where
  product X Y := Limits.getLimitCone (Limits.pair X Y)
  terminal := Limits.getLimitCone (Functor.empty C)

instance (priority := 100) : Limits.HasFiniteProducts C :=
  letI : ∀ (X Y : C), Limits.HasLimit (Limits.pair X Y) := fun _ _ =>
    .mk <| ChosenFiniteProducts.product _ _
  letI : Limits.HasBinaryProducts C := Limits.hasBinaryProducts_of_hasLimit_pair _
  letI : Limits.HasTerminal C := Limits.hasTerminal_of_unique (𝟙_ _)
  hasFiniteProducts_of_has_binary_and_terminal

end ChosenFiniteProducts

open Limits MonoidalCategory ChosenFiniteProducts

variable {C : Type u} [Category.{v} C] [ChosenFiniteProducts C]
  {D : Type u₁} [Category.{v₁} D] (F : C ⥤ D)
  [ChosenFiniteProducts D]
  [h₀ : PreservesLimit (Functor.empty.{0} C) F]
  [h₁ : PreservesLimitsOfShape (Discrete WalkingPair) F]

/-- Promote a finite products preserving functor to a monoidal functor between
categories equipped with the monoidal category structure given by chosen finite products. -/
@[simps]
def Functor.toMonoidalFunctorOfChosenFiniteProducts : MonoidalFunctor C D where
  toFunctor := F
  ε := IsLimit.conePointsIsoOfNatIso
    (h₀.preserves terminal.isLimit) terminal.isLimit (Functor.isEmptyExt _ _)|>.inv
  μ x y := IsLimit.conePointsIsoOfNatIso
    (h₁.preservesLimit.preserves (ChosenFiniteProducts.product _ _).isLimit)
    (ChosenFiniteProducts.product _ _).isLimit (pairComp _ _ _)|>.inv
  μ_natural_left {X Y} f X' := by
    dsimp only [mapCone_pt, IsLimit.conePointsIsoOfNatIso_inv]
    apply h₁.preservesLimit.preserves (ChosenFiniteProducts.product _ _).isLimit|>.hom_ext
    dsimp only [comp_obj, pair_obj_left, mapCone_pt, IsLimit.conePointsIsoOfNatIso_inv,
      mapCone_π_app, BinaryFan.π_app_left]
    simp only [Category.assoc]
    rintro ⟨⟨_⟩⟩
    · simp only [pairComp, diagramIsoPair_inv_app, comp_obj, pair_obj_left, pair_obj_right,
        Iso.refl_inv, BinaryFan.π_app_left, Category.comp_id, Category.id_comp]
      rw [← Functor.map_comp, ← fst, whiskerRight_fst, Functor.map_comp, fst,
        ← F.mapCone_π_app, IsLimit.map_π]
      simp only [const_obj_obj, pair_obj_left, comp_obj, BinaryFan.π_app_left,
        diagramIsoPair_inv_app, pair_obj_right, Iso.refl_inv, Category.comp_id]
      rw [← fst, whiskerRight_fst]
      conv_rhs => rw [fst, ← F.mapCone_π_app, IsLimit.map_π_assoc]
      simp only [diagramIsoPair_inv_app, comp_obj, pair_obj_left, pair_obj_right, Iso.refl_inv,
        Category.comp_id, BinaryFan.π_app_left, Category.id_comp]
      rfl
    · rw [← Functor.map_comp]
      conv_rhs => arg 2; congr; (conv => arg 2; change snd _ _); rw [whiskerRight_snd f X', snd]
      rw [← F.mapCone_π_app, IsLimit.map_π, ← F.mapCone_π_app, IsLimit.map_π]
      simp only [pair_obj_right, const_obj_obj, comp_obj, BinaryFan.π_app_right]
      rw [← snd, whiskerRight_snd_assoc]
      rfl
  μ_natural_right {X Y} X' g := by
    dsimp only [mapCone_pt, IsLimit.conePointsIsoOfNatIso_inv]
    apply h₁.preservesLimit.preserves (ChosenFiniteProducts.product _ _).isLimit|>.hom_ext
    dsimp only [comp_obj, pair_obj_left, mapCone_pt, IsLimit.conePointsIsoOfNatIso_inv,
      mapCone_π_app, BinaryFan.π_app_left]
    simp only [Category.assoc]
    rintro ⟨⟨_⟩⟩
    · rw [← Functor.map_comp]
      conv_rhs => arg 2; congr; (conv => arg 2; change fst _ _); rw [whiskerLeft_fst X' g, fst]
      rw [← F.mapCone_π_app, IsLimit.map_π, ← F.mapCone_π_app, IsLimit.map_π]
      simp only [pair_obj_left, const_obj_obj, comp_obj, BinaryFan.π_app_left]
      rw [← fst, whiskerLeft_fst_assoc]
      rfl
    · simp only [pairComp, diagramIsoPair_inv_app, comp_obj, pair_obj_right, pair_obj_left,
        Iso.refl_inv, BinaryFan.π_app_right, Category.comp_id, Category.id_comp]
      rw [← Functor.map_comp, ← snd, whiskerLeft_snd, Functor.map_comp, snd,
        ← F.mapCone_π_app, IsLimit.map_π]
      simp only [const_obj_obj, pair_obj_right, comp_obj, BinaryFan.π_app_right,
        diagramIsoPair_inv_app, pair_obj_left, Iso.refl_inv, Category.comp_id]
      rw [← snd, whiskerLeft_snd]
      conv_rhs => rw [snd, ← F.mapCone_π_app, IsLimit.map_π_assoc]
      simp only [diagramIsoPair_inv_app, comp_obj, pair_obj_left, pair_obj_right, Iso.refl_inv,
        Category.comp_id, BinaryFan.π_app_left, Category.id_comp]
      rfl
  associativity X Y Z := by
    dsimp only [mapCone_pt, IsLimit.conePointsIsoOfNatIso_inv]
    apply h₁.preservesLimit.preserves (ChosenFiniteProducts.product _ _).isLimit|>.hom_ext
    simp only [comp_obj, mapCone_pt, mapCone_π_app, Category.assoc]
    rintro ⟨⟨_⟩⟩
    · rw [← Functor.map_comp]
      slice_lhs 3 4 => congr; (conv => arg 2; change fst _ _); rw [associator_hom_fst X]
      rw [← F.mapCone_π_app, IsLimit.map_π]
      slice_rhs 3 4 => arg 1; change fst _ _
      simp only [whiskerLeft_fst_assoc, associator_hom_fst_assoc, pair_obj_left, map_comp]
      rw [fst, ← F.mapCone_π_app, IsLimit.map_π_assoc]
      slice_lhs 2 2 => change fst _ _
      rw [Category.assoc, whiskerRight_fst_assoc]
      simp only [pair_obj_left, BinaryFan.π_app_left, comp_obj]
      congr 1
      simp only [pairComp, diagramIsoPair_inv_app, comp_obj, pair_obj_left, pair_obj_right,
        Iso.refl_inv, Category.id_comp, Category.comp_id]
      rw [fst, ← F.mapCone_π_app, IsLimit.map_π]
      simp only [const_obj_obj, pair_obj_left, comp_obj, BinaryFan.π_app_left,
        diagramIsoPair_inv_app, pair_obj_right, Iso.refl_inv, Category.comp_id]
      rfl
    · apply h₁.preservesLimit.preserves (ChosenFiniteProducts.product _ _).isLimit|>.hom_ext
      rintro ⟨⟨_⟩⟩ <;> simp only [Category.assoc]
      · slice_rhs 3 4 => rw [← F.mapCone_π_app, IsLimit.map_π]
        simp only [comp_obj, pair_obj_left, mapCone_pt, pair_obj_right, BinaryFan.π_app_right,
          mapCone_π_app, BinaryFan.π_app_left, Category.assoc]
        rw [← Functor.map_comp, ← Functor.map_comp]
        rw [← snd, ← fst, associator_hom_snd_fst]
        simp only [map_comp, pairComp, diagramIsoPair_inv_app, comp_obj, pair_obj_left,
          pair_obj_right, Iso.refl_inv, Category.id_comp, Category.comp_id]
        slice_lhs 2 3 => rw [fst, ← F.mapCone_π_app, IsLimit.map_π]
        simp only [const_obj_obj, pair_obj_left, comp_obj, BinaryFan.π_app_left,
          diagramIsoPair_inv_app, pair_obj_right, Iso.refl_inv, Category.comp_id]
        rw [← snd, whiskerLeft_snd_assoc]
        slice_rhs 3 4 =>
          equals fst _ _ =>
            rw [fst, ← F.mapCone_π_app, IsLimit.map_π,
              diagramIsoPair_inv_app, Iso.refl_inv]
            simp only [const_obj_obj, comp_obj, pair_obj_left,
              BinaryFan.π_app_left, Category.comp_id]
            rfl
        rw [associator_hom_snd_fst, ← fst, whiskerRight_fst_assoc]
        congr 1
        rw [snd, ← F.mapCone_π_app, IsLimit.map_π]
        simp only [const_obj_obj, pair_obj_left, comp_obj, BinaryFan.π_app_left,
          diagramIsoPair_inv_app, pair_obj_right, Iso.refl_inv, Category.comp_id]
        rfl
      · slice_rhs 3 4 => rw [← F.mapCone_π_app, IsLimit.map_π]
        simp only [comp_obj, pair_obj_left, mapCone_pt, pair_obj_right, BinaryFan.π_app_right,
          mapCone_π_app, BinaryFan.π_app_left, Category.assoc]
        rw [← Functor.map_comp, ← Functor.map_comp]
        rw [← snd, ← snd, associator_hom_snd_snd]
        simp only [map_comp, pairComp, diagramIsoPair_inv_app, comp_obj, pair_obj_left,
          pair_obj_right, Iso.refl_inv, Category.id_comp, Category.comp_id]
        slice_lhs 2 3 =>
          equals snd _ _ =>
            rw [snd, ← F.mapCone_π_app, IsLimit.map_π,
              diagramIsoPair_inv_app, Iso.refl_inv]
            simp only [const_obj_obj, comp_obj, pair_obj_right,
              BinaryFan.π_app_right, Category.comp_id]
            rfl
        rw [whiskerRight_snd]
        slice_rhs 2 4 =>
          rw [← snd, whiskerLeft_snd_assoc]
          arg 2; equals snd _ _ =>
            rw [snd, ← F.mapCone_π_app, IsLimit.map_π,
              diagramIsoPair_inv_app, Iso.refl_inv]
            simp only [const_obj_obj, comp_obj, pair_obj_right,
              BinaryFan.π_app_right, Category.comp_id]
            rfl
        rw [associator_hom_snd_snd]
  left_unitality X := by
    slice_rhs 2 3 =>
      conv => enter [2, 2]; change BinaryFan.snd _
      equals snd _ _ =>
        simp only [mapCone_pt, pairComp, IsLimit.conePointsIsoOfNatIso_inv]
        rw [← F.mapCone_π_app, IsLimit.map_π,
          diagramIsoPair_inv_app, Iso.refl_inv]
        simp only [const_obj_obj, comp_obj, pair_obj_right,
          BinaryFan.π_app_right, Category.comp_id]
        rfl
    rw [whiskerRight_snd]
    rfl
  right_unitality X := by
    slice_rhs 2 3 =>
      conv => enter [2, 2]; change BinaryFan.fst _
      equals fst _ _ =>
        simp only [mapCone_pt, pairComp, IsLimit.conePointsIsoOfNatIso_inv]
        rw [← F.mapCone_π_app, IsLimit.map_π,
          diagramIsoPair_inv_app, Iso.refl_inv]
        simp only [const_obj_obj, comp_obj, pair_obj_left,
          BinaryFan.π_app_left, Category.comp_id]
        rfl
    rw [whiskerLeft_fst]
    rfl

instance [F.IsEquivalence] : F.toMonoidalFunctorOfChosenFiniteProducts.IsEquivalence := by
  assumption

end CategoryTheory
