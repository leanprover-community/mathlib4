/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Simon Hudon
-/
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.PEmpty

#align_import category_theory.monoidal.of_chosen_finite_products.basic from "leanprover-community/mathlib"@"95a87616d63b3cb49d3fe678d416fbe9c4217bf4"

/-!
# The monoidal structure on a category with chosen finite products.

This is a variant of the development in `CategoryTheory.Monoidal.OfHasFiniteProducts`,
which uses specified choices of the terminal object and binary product,
enabling the construction of a cartesian category with specific definitions of the tensor unit
and tensor product.

(Because the construction in `CategoryTheory.Monoidal.OfHasFiniteProducts` uses `HasLimit`
classes, the actual definitions there are opaque behind `Classical.choice`.)

We use this in `CategoryTheory.Monoidal.TypeCat` to construct the monoidal category of types
so that the tensor product is the usual cartesian product of types.

For now we only do the construction from products, and not from coproducts,
which seems less often useful.
-/


universe v u


namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {X Y : C}

namespace Limits

section

variable {C}

/-- Swap the two sides of a `BinaryFan`. -/
def BinaryFan.swap {P Q : C} (t : BinaryFan P Q) : BinaryFan Q P :=
  BinaryFan.mk t.snd t.fst
#align category_theory.limits.binary_fan.swap CategoryTheory.Limits.BinaryFan.swap

@[simp]
theorem BinaryFan.swap_fst {P Q : C} (t : BinaryFan P Q) : t.swap.fst = t.snd :=
  rfl
#align category_theory.limits.binary_fan.swap_fst CategoryTheory.Limits.BinaryFan.swap_fst

@[simp]
theorem BinaryFan.swap_snd {P Q : C} (t : BinaryFan P Q) : t.swap.snd = t.fst :=
  rfl
#align category_theory.limits.binary_fan.swap_snd CategoryTheory.Limits.BinaryFan.swap_snd

/-- If a binary fan `t` over `P Q` is a limit cone, then `t.swap` is a limit cone over `Q P`.
-/
@[simps]
def IsLimit.swapBinaryFan {P Q : C} {t : BinaryFan P Q} (I : IsLimit t) : IsLimit t.swap where
  lift s := I.lift (BinaryFan.swap s)
  fac s := by rintro ⟨⟨⟩⟩ <;> simp
  uniq s m w := by
    have h := I.uniq (BinaryFan.swap s) m
    rw [h]
    rintro ⟨j⟩
    specialize w ⟨WalkingPair.swap j⟩
    cases j <;> exact w
#align category_theory.limits.is_limit.swap_binary_fan CategoryTheory.Limits.IsLimit.swapBinaryFan

/-- Construct `HasBinaryProduct Q P` from `HasBinaryProduct P Q`.
This can't be an instance, as it would cause a loop in typeclass search.
-/
theorem HasBinaryProduct.swap (P Q : C) [HasBinaryProduct P Q] : HasBinaryProduct Q P :=
  HasLimit.mk ⟨BinaryFan.swap (limit.cone (pair P Q)), (limit.isLimit (pair P Q)).swapBinaryFan⟩
#align category_theory.limits.has_binary_product.swap CategoryTheory.Limits.HasBinaryProduct.swap

/-- Given a limit cone over `X` and `Y`, and another limit cone over `Y` and `X`, we can construct
an isomorphism between the cone points. Relative to some fixed choice of limits cones for every
pair, these isomorphisms constitute a braiding.
-/
def BinaryFan.braiding {X Y : C} {s : BinaryFan X Y} (P : IsLimit s) {t : BinaryFan Y X}
    (Q : IsLimit t) : s.pt ≅ t.pt :=
  IsLimit.conePointUniqueUpToIso P Q.swapBinaryFan
#align category_theory.limits.binary_fan.braiding CategoryTheory.Limits.BinaryFan.braiding

/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `sXY.X Z`,
if `sYZ` is a limit cone we can construct a binary fan over `X sYZ.X`.

This is an ingredient of building the associator for a cartesian category.
-/
def BinaryFan.assoc {X Y Z : C} {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z} (Q : IsLimit sYZ)
    (s : BinaryFan sXY.pt Z) : BinaryFan X sYZ.pt :=
  BinaryFan.mk (s.fst ≫ sXY.fst) (Q.lift (BinaryFan.mk (s.fst ≫ sXY.snd) s.snd))
#align category_theory.limits.binary_fan.assoc CategoryTheory.Limits.BinaryFan.assoc

@[simp]
theorem BinaryFan.assoc_fst {X Y Z : C} {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z}
    (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) : (BinaryFan.assoc Q s).fst = s.fst ≫ sXY.fst :=
  rfl
#align category_theory.limits.binary_fan.assoc_fst CategoryTheory.Limits.BinaryFan.assoc_fst

@[simp]
theorem BinaryFan.assoc_snd {X Y Z : C} {sXY : BinaryFan X Y} {sYZ : BinaryFan Y Z}
    (Q : IsLimit sYZ) (s : BinaryFan sXY.pt Z) :
    (BinaryFan.assoc Q s).snd = Q.lift (BinaryFan.mk (s.fst ≫ sXY.snd) s.snd) :=
  rfl
#align category_theory.limits.binary_fan.assoc_snd CategoryTheory.Limits.BinaryFan.assoc_snd

/-- Given binary fans `sXY` over `X Y`, and `sYZ` over `Y Z`, and `s` over `X sYZ.X`,
if `sYZ` is a limit cone we can construct a binary fan over `sXY.X Z`.

This is an ingredient of building the associator for a cartesian category.
-/
def BinaryFan.assocInv {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY) {sYZ : BinaryFan Y Z}
    (s : BinaryFan X sYZ.pt) : BinaryFan sXY.pt Z :=
  BinaryFan.mk (P.lift (BinaryFan.mk s.fst (s.snd ≫ sYZ.fst))) (s.snd ≫ sYZ.snd)
#align category_theory.limits.binary_fan.assoc_inv CategoryTheory.Limits.BinaryFan.assocInv

@[simp]
theorem BinaryFan.assocInv_fst {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY)
    {sYZ : BinaryFan Y Z} (s : BinaryFan X sYZ.pt) :
    (BinaryFan.assocInv P s).fst = P.lift (BinaryFan.mk s.fst (s.snd ≫ sYZ.fst)) :=
  rfl
#align category_theory.limits.binary_fan.assoc_inv_fst CategoryTheory.Limits.BinaryFan.assocInv_fst

@[simp]
theorem BinaryFan.assocInv_snd {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY)
    {sYZ : BinaryFan Y Z} (s : BinaryFan X sYZ.pt) :
    (BinaryFan.assocInv P s).snd = s.snd ≫ sYZ.snd :=
  rfl
#align category_theory.limits.binary_fan.assoc_inv_snd CategoryTheory.Limits.BinaryFan.assocInv_snd

/-- If all the binary fans involved a limit cones, `BinaryFan.assoc` produces another limit cone.
-/
@[simps]
def IsLimit.assoc {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY) {sYZ : BinaryFan Y Z}
    (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z} (R : IsLimit s) : IsLimit (BinaryFan.assoc Q s) where
  lift t := R.lift (BinaryFan.assocInv P t)
  fac t := by
    rintro ⟨⟨⟩⟩ <;> simp
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩ <;> simp
  uniq t m w := by
    have h := R.uniq (BinaryFan.assocInv P t) m
    rw [h]
    rintro ⟨⟨⟩⟩ <;> simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩ <;> simp
      · exact w ⟨WalkingPair.left⟩
      · specialize w ⟨WalkingPair.right⟩
        simp? at w says
          simp only [pair_obj_right, BinaryFan.π_app_right, BinaryFan.assoc_snd,
            Functor.const_obj_obj, pair_obj_left] at w
        rw [← w]
        simp
    · specialize w ⟨WalkingPair.right⟩
      simp? at w says
        simp only [pair_obj_right, BinaryFan.π_app_right, BinaryFan.assoc_snd,
          Functor.const_obj_obj, pair_obj_left] at w
      rw [← w]
      simp
#align category_theory.limits.is_limit.assoc CategoryTheory.Limits.IsLimit.assoc

/-- Given two pairs of limit cones corresponding to the parenthesisations of `X × Y × Z`,
we obtain an isomorphism between the cone points.
-/
abbrev BinaryFan.associator {X Y Z : C} {sXY : BinaryFan X Y} (P : IsLimit sXY)
    {sYZ : BinaryFan Y Z} (Q : IsLimit sYZ) {s : BinaryFan sXY.pt Z} (R : IsLimit s)
    {t : BinaryFan X sYZ.pt} (S : IsLimit t) : s.pt ≅ t.pt :=
  IsLimit.conePointUniqueUpToIso (IsLimit.assoc P Q R) S
#align category_theory.limits.binary_fan.associator CategoryTheory.Limits.BinaryFan.associator

/-- Given a fixed family of limit data for every pair `X Y`, we obtain an associator.
-/
abbrev BinaryFan.associatorOfLimitCone (L : ∀ X Y : C, LimitCone (pair X Y)) (X Y Z : C) :
    (L (L X Y).cone.pt Z).cone.pt ≅ (L X (L Y Z).cone.pt).cone.pt :=
  BinaryFan.associator (L X Y).isLimit (L Y Z).isLimit (L (L X Y).cone.pt Z).isLimit
    (L X (L Y Z).cone.pt).isLimit
#align category_theory.limits.binary_fan.associator_of_limit_cone CategoryTheory.Limits.BinaryFan.associatorOfLimitCone

/-- Construct a left unitor from specified limit cones.
-/
@[simps]
def BinaryFan.leftUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan s.pt X} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.snd
  inv := Q.lift <| BinaryFan.mk (P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩) (𝟙 _)
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
    · simp
#align category_theory.limits.binary_fan.left_unitor CategoryTheory.Limits.BinaryFan.leftUnitor

/-- Construct a right unitor from specified limit cones.
-/
@[simps]
def BinaryFan.rightUnitor {X : C} {s : Cone (Functor.empty.{0} C)} (P : IsLimit s)
    {t : BinaryFan X s.pt} (Q : IsLimit t) : t.pt ≅ X where
  hom := t.fst
  inv := Q.lift <| BinaryFan.mk (𝟙 _) <| P.lift ⟨_, fun x => x.as.elim, fun {x} => x.as.elim⟩
  hom_inv_id := by
    apply Q.hom_ext
    rintro ⟨⟨⟩⟩
    · simp
    · apply P.hom_ext
      rintro ⟨⟨⟩⟩
#align category_theory.limits.binary_fan.right_unitor CategoryTheory.Limits.BinaryFan.rightUnitor

end

end Limits

open CategoryTheory.Limits

section

-- Porting note: no tidy
-- attribute [local tidy] tactic.case_bash

variable {C}
variable (𝒯 : LimitCone (Functor.empty.{0} C))
variable (ℬ : ∀ X Y : C, LimitCone (pair X Y))

namespace MonoidalOfChosenFiniteProducts

/-- Implementation of the tensor product for `MonoidalOfChosenFiniteProducts`. -/
abbrev tensorObj (X Y : C) : C :=
  (ℬ X Y).cone.pt
#align category_theory.monoidal_of_chosen_finite_products.tensor_obj CategoryTheory.MonoidalOfChosenFiniteProducts.tensorObj

/-- Implementation of the tensor product of morphisms for `MonoidalOfChosenFiniteProducts`. -/
abbrev tensorHom {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) : tensorObj ℬ W Y ⟶ tensorObj ℬ X Z :=
  (BinaryFan.IsLimit.lift' (ℬ X Z).isLimit ((ℬ W Y).cone.π.app ⟨WalkingPair.left⟩ ≫ f)
      (((ℬ W Y).cone.π.app ⟨WalkingPair.right⟩ : (ℬ W Y).cone.pt ⟶ Y) ≫ g)).val
#align category_theory.monoidal_of_chosen_finite_products.tensor_hom CategoryTheory.MonoidalOfChosenFiniteProducts.tensorHom

theorem tensor_id (X₁ X₂ : C) : tensorHom ℬ (𝟙 X₁) (𝟙 X₂) = 𝟙 (tensorObj ℬ X₁ X₂) := by
  apply IsLimit.hom_ext (ℬ _ _).isLimit;
  rintro ⟨⟨⟩⟩ <;>
    · dsimp [tensorHom]
      simp
#align category_theory.monoidal_of_chosen_finite_products.tensor_id CategoryTheory.MonoidalOfChosenFiniteProducts.tensor_id

theorem tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) : tensorHom ℬ (f₁ ≫ g₁) (f₂ ≫ g₂) = tensorHom ℬ f₁ f₂ ≫ tensorHom ℬ g₁ g₂ := by
  apply IsLimit.hom_ext (ℬ _ _).isLimit;
  rintro ⟨⟨⟩⟩ <;>
    · dsimp [tensorHom]
      simp
#align category_theory.monoidal_of_chosen_finite_products.tensor_comp CategoryTheory.MonoidalOfChosenFiniteProducts.tensor_comp

theorem pentagon (W X Y Z : C) :
    tensorHom ℬ (BinaryFan.associatorOfLimitCone ℬ W X Y).hom (𝟙 Z) ≫
        (BinaryFan.associatorOfLimitCone ℬ W (tensorObj ℬ X Y) Z).hom ≫
          tensorHom ℬ (𝟙 W) (BinaryFan.associatorOfLimitCone ℬ X Y Z).hom =
      (BinaryFan.associatorOfLimitCone ℬ (tensorObj ℬ W X) Y Z).hom ≫
        (BinaryFan.associatorOfLimitCone ℬ W X (tensorObj ℬ Y Z)).hom := by
  dsimp [tensorHom]
  apply IsLimit.hom_ext (ℬ _ _).isLimit; rintro ⟨⟨⟩⟩
  · simp
  · apply IsLimit.hom_ext (ℬ _ _).isLimit
    rintro ⟨⟨⟩⟩
    · simp
    apply IsLimit.hom_ext (ℬ _ _).isLimit
    rintro ⟨⟨⟩⟩
    · simp
    · simp
#align category_theory.monoidal_of_chosen_finite_products.pentagon CategoryTheory.MonoidalOfChosenFiniteProducts.pentagon

theorem triangle (X Y : C) :
    (BinaryFan.associatorOfLimitCone ℬ X 𝒯.cone.pt Y).hom ≫
        tensorHom ℬ (𝟙 X) (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt Y).isLimit).hom =
      tensorHom ℬ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit).hom (𝟙 Y) := by
  dsimp [tensorHom]
  apply IsLimit.hom_ext (ℬ _ _).isLimit; rintro ⟨⟨⟩⟩ <;> simp
#align category_theory.monoidal_of_chosen_finite_products.triangle CategoryTheory.MonoidalOfChosenFiniteProducts.triangle

theorem leftUnitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
    tensorHom ℬ (𝟙 𝒯.cone.pt) f ≫ (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₂).isLimit).hom =
      (BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X₁).isLimit).hom ≫ f := by
  dsimp [tensorHom]
  simp
#align category_theory.monoidal_of_chosen_finite_products.left_unitor_naturality CategoryTheory.MonoidalOfChosenFiniteProducts.leftUnitor_naturality

theorem rightUnitor_naturality {X₁ X₂ : C} (f : X₁ ⟶ X₂) :
    tensorHom ℬ f (𝟙 𝒯.cone.pt) ≫ (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₂ 𝒯.cone.pt).isLimit).hom =
      (BinaryFan.rightUnitor 𝒯.isLimit (ℬ X₁ 𝒯.cone.pt).isLimit).hom ≫ f := by
  dsimp [tensorHom]
  simp
#align category_theory.monoidal_of_chosen_finite_products.right_unitor_naturality CategoryTheory.MonoidalOfChosenFiniteProducts.rightUnitor_naturality

theorem associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) :
    tensorHom ℬ (tensorHom ℬ f₁ f₂) f₃ ≫ (BinaryFan.associatorOfLimitCone ℬ Y₁ Y₂ Y₃).hom =
      (BinaryFan.associatorOfLimitCone ℬ X₁ X₂ X₃).hom ≫ tensorHom ℬ f₁ (tensorHom ℬ f₂ f₃) := by
  dsimp [tensorHom]
  apply IsLimit.hom_ext (ℬ _ _).isLimit; rintro ⟨⟨⟩⟩
  · simp
  · apply IsLimit.hom_ext (ℬ _ _).isLimit
    rintro ⟨⟨⟩⟩
    · simp
    · simp
#align category_theory.monoidal_of_chosen_finite_products.associator_naturality CategoryTheory.MonoidalOfChosenFiniteProducts.associator_naturality

end MonoidalOfChosenFiniteProducts

open MonoidalOfChosenFiniteProducts

/-- A category with a terminal object and binary products has a natural monoidal structure. -/
def monoidalOfChosenFiniteProducts : MonoidalCategory C :=
  letI : MonoidalCategoryStruct C :=
    { tensorUnit := 𝒯.cone.pt
      tensorObj := tensorObj ℬ
      tensorHom := tensorHom ℬ
      whiskerLeft := @fun X {_ _} g ↦ tensorHom ℬ (𝟙 X) g
      whiskerRight := @fun{_ _} f Y ↦ tensorHom ℬ f (𝟙 Y)
      associator := BinaryFan.associatorOfLimitCone ℬ
      leftUnitor := fun X ↦ BinaryFan.leftUnitor 𝒯.isLimit (ℬ 𝒯.cone.pt X).isLimit
      rightUnitor := fun X ↦ BinaryFan.rightUnitor 𝒯.isLimit (ℬ X 𝒯.cone.pt).isLimit}
  .ofTensorHom
    (tensor_id := tensor_id ℬ)
    (tensor_comp := tensor_comp ℬ)
    (pentagon := pentagon ℬ)
    (triangle := triangle 𝒯 ℬ)
    (leftUnitor_naturality := leftUnitor_naturality 𝒯 ℬ)
    (rightUnitor_naturality := rightUnitor_naturality 𝒯 ℬ)
    (associator_naturality := associator_naturality ℬ)
#align category_theory.monoidal_of_chosen_finite_products CategoryTheory.monoidalOfChosenFiniteProducts

namespace MonoidalOfChosenFiniteProducts

open MonoidalCategory

/-- A type synonym for `C` carrying a monoidal category structure corresponding to
a fixed choice of limit data for the empty functor, and for `pair X Y` for every `X Y : C`.

This is an implementation detail for `SymmetricOfChosenFiniteProducts`.
-/
-- Porting note(#5171): linter `has_nonempty_instance` not ported yet
-- @[nolint has_nonempty_instance]
@[nolint unusedArguments]
def MonoidalOfChosenFiniteProductsSynonym (_𝒯 : LimitCone (Functor.empty.{0} C))
    (_ℬ : ∀ X Y : C, LimitCone (pair X Y)) :=
  C
#align category_theory.monoidal_of_chosen_finite_products.monoidal_of_chosen_finite_products_synonym CategoryTheory.MonoidalOfChosenFiniteProducts.MonoidalOfChosenFiniteProductsSynonym

instance : Category (MonoidalOfChosenFiniteProductsSynonym 𝒯 ℬ) := by
  dsimp [MonoidalOfChosenFiniteProductsSynonym]
  infer_instance

instance : MonoidalCategory (MonoidalOfChosenFiniteProductsSynonym 𝒯 ℬ) :=
  monoidalOfChosenFiniteProducts 𝒯 ℬ

end MonoidalOfChosenFiniteProducts

end

end CategoryTheory
