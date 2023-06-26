/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oleksandr Manzyuk

! This file was ported from Lean 3 source module category_theory.monoidal.Bimod
! leanprover-community/mathlib commit 4698e35ca56a0d4fa53aa5639c3364e0a77f4eba
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# The category of bimodule objects over a pair of monoid objects.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

section

open CategoryTheory.Limits

variable [HasCoequalizers C]

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem id_tensor_π_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Z ⊗ Y ⟶ W)
    (wh : (𝟙 Z ⊗ f) ≫ h = (𝟙 Z ⊗ g) ≫ h) :
    (𝟙 Z ⊗ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh
#align id_tensor_π_preserves_coequalizer_inv_desc id_tensor_π_preserves_coequalizer_inv_desc

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem id_tensor_π_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : Z ⊗ X ⟶ X') (q : Z ⊗ Y ⟶ Y') (wf : (𝟙 Z ⊗ f) ≫ q = p ≫ f')
    (wg : (𝟙 Z ⊗ g) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (𝟙 Z ⊗ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫
          colimMap (parallelPairHom (𝟙 Z ⊗ f) (𝟙 Z ⊗ g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorLeft Z) f g f' g' p q wf wg h wh
#align id_tensor_π_preserves_coequalizer_inv_colim_map_desc id_tensor_π_preserves_coequalizer_inv_colimMap_desc

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem π_tensor_id_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Y ⊗ Z ⟶ W)
    (wh : (f ⊗ 𝟙 Z) ≫ h = (g ⊗ 𝟙 Z) ≫ h) :
    (coequalizer.π f g ⊗ 𝟙 Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorRight Z) f g h wh
#align π_tensor_id_preserves_coequalizer_inv_desc π_tensor_id_preserves_coequalizer_inv_desc

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem π_tensor_id_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : X ⊗ Z ⟶ X') (q : Y ⊗ Z ⟶ Y') (wf : (f ⊗ 𝟙 Z) ≫ q = p ≫ f')
    (wg : (g ⊗ 𝟙 Z) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (coequalizer.π f g ⊗ 𝟙 Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫
          colimMap (parallelPairHom (f ⊗ 𝟙 Z) (g ⊗ 𝟙 Z) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorRight Z) f g f' g' p q wf wg h wh
#align π_tensor_id_preserves_coequalizer_inv_colim_map_desc π_tensor_id_preserves_coequalizer_inv_colimMap_desc

end

end

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A bimodule object for a pair of monoid objects, all internal to some monoidal category. -/
structure Bimod (A B : Mon_ C) where
  pt : C
  actLeft : A.pt ⊗ X ⟶ X
  one_act_left' : (A.one ⊗ 𝟙 X) ≫ act_left = (λ_ X).Hom := by obviously
  left_assoc' :
    (A.mul ⊗ 𝟙 X) ≫ act_left = (α_ A.pt A.pt X).Hom ≫ (𝟙 A.pt ⊗ act_left) ≫ act_left := by obviously
  actRight : X ⊗ B.pt ⟶ X
  actRight_one' : (𝟙 X ⊗ B.one) ≫ act_right = (ρ_ X).Hom := by obviously
  right_assoc' :
    (𝟙 X ⊗ B.mul) ≫ act_right = (α_ X B.pt B.pt).inv ≫ (act_right ⊗ 𝟙 B.pt) ≫ act_right := by
    obviously
  middle_assoc' :
    (act_left ⊗ 𝟙 B.pt) ≫ act_right = (α_ A.pt X B.pt).Hom ≫ (𝟙 A.pt ⊗ act_right) ≫ act_left := by
    obviously
#align Bimod Bimod

restate_axiom Bimod.one_act_left'

restate_axiom Bimod.actRight_one'

restate_axiom Bimod.left_assoc'

restate_axiom Bimod.right_assoc'

restate_axiom Bimod.middle_assoc'

attribute [simp, reassoc] Bimod.one_actLeft Bimod.actRight_one Bimod.left_assoc Bimod.right_assoc
  Bimod.middle_assoc

namespace Bimod

variable {A B : Mon_ C} (M : Bimod A B)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism of bimodule objects. -/
@[ext]
structure Hom (M N : Bimod A B) where
  Hom : M.pt ⟶ N.pt
  left_act_hom' : M.actLeft ≫ hom = (𝟙 A.pt ⊗ hom) ≫ N.actLeft := by obviously
  right_act_hom' : M.actRight ≫ hom = (hom ⊗ 𝟙 B.pt) ≫ N.actRight := by obviously
#align Bimod.hom Bimod.Hom

restate_axiom hom.left_act_hom'

restate_axiom hom.right_act_hom'

attribute [simp, reassoc] hom.left_act_hom hom.right_act_hom

/-- The identity morphism on a bimodule object. -/
@[simps]
def id' (M : Bimod A B) : Hom M M where Hom := 𝟙 M.pt
#align Bimod.id' Bimod.id'

instance homInhabited (M : Bimod A B) : Inhabited (Hom M M) :=
  ⟨id' M⟩
#align Bimod.hom_inhabited Bimod.homInhabited

/-- Composition of bimodule object morphisms. -/
@[simps]
def comp {M N O : Bimod A B} (f : Hom M N) (g : Hom N O) : Hom M O where Hom := f.Hom ≫ g.Hom
#align Bimod.comp Bimod.comp

instance : Category (Bimod A B) where
  Hom M N := Hom M N
  id := id'
  comp M N O f g := comp f g

@[simp]
theorem id_hom' (M : Bimod A B) : (𝟙 M : Hom M M).Hom = 𝟙 M.pt :=
  rfl
#align Bimod.id_hom' Bimod.id_hom'

@[simp]
theorem comp_hom' {M N K : Bimod A B} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl
#align Bimod.comp_hom' Bimod.comp_hom'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Construct an isomorphism of bimodules by giving an isomorphism between the underlying objects
and checking compatibility with left and right actions only in the forward direction.
-/
@[simps]
def isoOfIso {X Y : Mon_ C} {P Q : Bimod X Y} (f : P.pt ≅ Q.pt)
    (f_left_act_hom : P.actLeft ≫ f.Hom = (𝟙 X.pt ⊗ f.Hom) ≫ Q.actLeft)
    (f_right_act_hom : P.actRight ≫ f.Hom = (f.Hom ⊗ 𝟙 Y.pt) ≫ Q.actRight) : P ≅ Q where
  Hom := ⟨f.Hom⟩
  inv :=
    { Hom := f.inv
      left_act_hom' := by
        rw [← cancel_mono f.hom, category.assoc, category.assoc, iso.inv_hom_id, category.comp_id,
          f_left_act_hom, ← category.assoc, ← id_tensor_comp, iso.inv_hom_id,
          monoidal_category.tensor_id, category.id_comp]
      right_act_hom' := by
        rw [← cancel_mono f.hom, category.assoc, category.assoc, iso.inv_hom_id, category.comp_id,
          f_right_act_hom, ← category.assoc, ← comp_tensor_id, iso.inv_hom_id,
          monoidal_category.tensor_id, category.id_comp] }
  hom_inv_id' := by ext; dsimp; rw [iso.hom_inv_id]
  inv_hom_id' := by ext; dsimp; rw [iso.inv_hom_id]
#align Bimod.iso_of_iso Bimod.isoOfIso

variable (A)

/-- A monoid object as a bimodule over itself. -/
@[simps]
def regular : Bimod A A where
  pt := A.pt
  actLeft := A.mul
  actRight := A.mul
#align Bimod.regular Bimod.regular

instance : Inhabited (Bimod A A) :=
  ⟨regular A⟩

/-- The forgetful functor from bimodule objects to the ambient category. -/
def forget : Bimod A B ⥤ C where
  obj A := A.pt
  map A B f := f.Hom
#align Bimod.forget Bimod.forget

open CategoryTheory.Limits

variable [HasCoequalizers C]

namespace TensorBimod

variable {R S T : Mon_ C} (P : Bimod R S) (Q : Bimod S T)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The underlying object of the tensor product of two bimodules. -/
noncomputable def x : C :=
  coequalizer (P.actRight ⊗ 𝟙 Q.pt) ((α_ _ _ _).Hom ≫ (𝟙 P.pt ⊗ Q.actLeft))
#align Bimod.tensor_Bimod.X Bimod.TensorBimod.x

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Left action for the tensor product of two bimodules. -/
noncomputable def actLeft : R.pt ⊗ x P Q ⟶ x P Q :=
  (PreservesCoequalizer.iso (tensorLeft R.pt) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((𝟙 _ ⊗ (α_ _ _ _).Hom) ≫ (α_ _ _ _).inv ≫ (P.actLeft ⊗ 𝟙 S.pt ⊗ 𝟙 Q.pt) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).inv ≫ (P.actLeft ⊗ 𝟙 Q.pt))
        (by
          dsimp
          slice_lhs 1 2 => rw [associator_inv_naturality]
          slice_rhs 3 4 => rw [associator_inv_naturality]
          slice_rhs 4 5 => rw [← tensor_comp, middle_assoc, tensor_comp, comp_tensor_id]
          coherence)
        (by
          dsimp
          slice_lhs 1 1 => rw [id_tensor_comp]
          slice_lhs 2 3 => rw [associator_inv_naturality]
          slice_lhs 3 4 => rw [tensor_id, id_tensor_comp_tensor_id]
          slice_rhs 4 6 => rw [iso.inv_hom_id_assoc]
          slice_rhs 3 4 => rw [tensor_id, tensor_id_comp_id_tensor]))
#align Bimod.tensor_Bimod.act_left Bimod.TensorBimod.actLeft

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem id_tensor_π_actLeft :
    (𝟙 R.pt ⊗ coequalizer.π _ _) ≫ actLeft P Q =
      (α_ _ _ _).inv ≫ (P.actLeft ⊗ 𝟙 Q.pt) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colim_map (tensor_left _)]
  simp only [category.assoc]
#align Bimod.tensor_Bimod.id_tensor_π_act_left Bimod.TensorBimod.id_tensor_π_actLeft

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem one_act_left' : (R.one ⊗ 𝟙 _) ≫ actLeft P Q = (λ_ _).Hom := by
  refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
  dsimp [X]
  slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  slice_lhs 2 3 => rw [id_tensor_π_act_left]
  slice_lhs 1 2 => rw [← monoidal_category.tensor_id, associator_inv_naturality]
  slice_lhs 2 3 => rw [← comp_tensor_id, one_act_left]
  slice_rhs 1 2 => rw [left_unitor_naturality]
  coherence
#align Bimod.tensor_Bimod.one_act_left' Bimod.TensorBimod.one_act_left'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem left_assoc' :
    (R.mul ⊗ 𝟙 _) ≫ actLeft P Q = (α_ R.pt R.pt _).Hom ≫ (𝟙 R.pt ⊗ actLeft P Q) ≫ actLeft P Q := by
  refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
  dsimp [X]
  slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  slice_lhs 2 3 => rw [id_tensor_π_act_left]
  slice_lhs 1 2 => rw [← monoidal_category.tensor_id, associator_inv_naturality]
  slice_lhs 2 3 => rw [← comp_tensor_id, left_assoc, comp_tensor_id, comp_tensor_id]
  slice_rhs 1 2 => rw [← monoidal_category.tensor_id, associator_naturality]
  slice_rhs 2 3 => rw [← id_tensor_comp, id_tensor_π_act_left, id_tensor_comp, id_tensor_comp]
  slice_rhs 4 5 => rw [id_tensor_π_act_left]
  slice_rhs 3 4 => rw [associator_inv_naturality]
  coherence
#align Bimod.tensor_Bimod.left_assoc' Bimod.TensorBimod.left_assoc'

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Right action for the tensor product of two bimodules. -/
noncomputable def actRight : x P Q ⊗ T.pt ⟶ x P Q :=
  (PreservesCoequalizer.iso (tensorRight T.pt) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).Hom ≫ (α_ _ _ _).Hom ≫ (𝟙 P.pt ⊗ 𝟙 S.pt ⊗ Q.actRight) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).Hom ≫ (𝟙 P.pt ⊗ Q.actRight))
        (by
          dsimp
          slice_lhs 1 2 => rw [associator_naturality]
          slice_lhs 2 3 => rw [tensor_id, tensor_id_comp_id_tensor]
          slice_rhs 3 4 => rw [associator_inv_naturality]
          slice_rhs 2 4 => rw [iso.hom_inv_id_assoc]
          slice_rhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id])
        (by
          dsimp
          slice_lhs 1 1 => rw [comp_tensor_id]
          slice_lhs 2 3 => rw [associator_naturality]
          slice_lhs 3 4 => rw [← id_tensor_comp, middle_assoc, id_tensor_comp]
          slice_rhs 4 6 => rw [iso.inv_hom_id_assoc]
          slice_rhs 3 4 => rw [← id_tensor_comp]
          coherence))
#align Bimod.tensor_Bimod.act_right Bimod.TensorBimod.actRight

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem π_tensor_id_actRight :
    (coequalizer.π _ _ ⊗ 𝟙 T.pt) ≫ actRight P Q =
      (α_ _ _ _).Hom ≫ (𝟙 P.pt ⊗ Q.actRight) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colim_map (tensor_right _)]
  simp only [category.assoc]
#align Bimod.tensor_Bimod.π_tensor_id_act_right Bimod.TensorBimod.π_tensor_id_actRight

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem actRight_one' : (𝟙 _ ⊗ T.one) ≫ actRight P Q = (ρ_ _).Hom := by
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp [X]
  slice_lhs 1 2 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_lhs 2 3 => rw [π_tensor_id_act_right]
  slice_lhs 1 2 => rw [← monoidal_category.tensor_id, associator_naturality]
  slice_lhs 2 3 => rw [← id_tensor_comp, act_right_one]
  slice_rhs 1 2 => rw [right_unitor_naturality]
  coherence
#align Bimod.tensor_Bimod.act_right_one' Bimod.TensorBimod.actRight_one'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem right_assoc' :
    (𝟙 _ ⊗ T.mul) ≫ actRight P Q = (α_ _ T.pt T.pt).inv ≫ (actRight P Q ⊗ 𝟙 T.pt) ≫ actRight P Q :=
  by
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp [X]
  slice_lhs 1 2 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_lhs 2 3 => rw [π_tensor_id_act_right]
  slice_lhs 1 2 => rw [← monoidal_category.tensor_id, associator_naturality]
  slice_lhs 2 3 => rw [← id_tensor_comp, right_assoc, id_tensor_comp, id_tensor_comp]
  slice_rhs 1 2 => rw [← monoidal_category.tensor_id, associator_inv_naturality]
  slice_rhs 2 3 => rw [← comp_tensor_id, π_tensor_id_act_right, comp_tensor_id, comp_tensor_id]
  slice_rhs 4 5 => rw [π_tensor_id_act_right]
  slice_rhs 3 4 => rw [associator_naturality]
  coherence
#align Bimod.tensor_Bimod.right_assoc' Bimod.TensorBimod.right_assoc'

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem middle_assoc' :
    (actLeft P Q ⊗ 𝟙 T.pt) ≫ actRight P Q =
      (α_ R.pt _ T.pt).Hom ≫ (𝟙 R.pt ⊗ actRight P Q) ≫ actLeft P Q := by
  refine' (cancel_epi ((tensor_left _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp [X]
  slice_lhs 1 2 => rw [← comp_tensor_id, id_tensor_π_act_left, comp_tensor_id, comp_tensor_id]
  slice_lhs 3 4 => rw [π_tensor_id_act_right]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_lhs 3 4 => rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor]
  slice_rhs 1 2 => rw [associator_naturality]
  slice_rhs 2 3 => rw [← id_tensor_comp, π_tensor_id_act_right, id_tensor_comp, id_tensor_comp]
  slice_rhs 4 5 => rw [id_tensor_π_act_left]
  slice_rhs 3 4 => rw [associator_inv_naturality]
  slice_rhs 4 5 => rw [monoidal_category.tensor_id, id_tensor_comp_tensor_id]
  coherence
#align Bimod.tensor_Bimod.middle_assoc' Bimod.TensorBimod.middle_assoc'

end

end TensorBimod

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Tensor product of two bimodule objects as a bimodule object. -/
@[simps]
noncomputable def tensorBimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) : Bimod X Z where
  pt := TensorBimod.x M N
  actLeft := TensorBimod.actLeft M N
  actRight := TensorBimod.actRight M N
  one_act_left' := TensorBimod.one_act_left' M N
  actRight_one' := TensorBimod.actRight_one' M N
  left_assoc' := TensorBimod.left_assoc' M N
  right_assoc' := TensorBimod.right_assoc' M N
  middle_assoc' := TensorBimod.middle_assoc' M N
#align Bimod.tensor_Bimod Bimod.tensorBimod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Tensor product of two morphisms of bimodule objects. -/
@[simps]
noncomputable def tensorHom {X Y Z : Mon_ C} {M₁ M₂ : Bimod X Y} {N₁ N₂ : Bimod Y Z} (f : M₁ ⟶ M₂)
    (g : N₁ ⟶ N₂) : M₁.tensorBimod N₁ ⟶ M₂.tensorBimod N₂ where
  Hom :=
    colimMap
      (parallelPairHom _ _ _ _ ((f.Hom ⊗ 𝟙 Y.pt) ⊗ g.Hom) (f.Hom ⊗ g.Hom)
        (by
          rw [← tensor_comp, ← tensor_comp, hom.right_act_hom, category.id_comp, category.comp_id])
        (by
          slice_lhs 2 3 => rw [← tensor_comp, hom.left_act_hom, category.id_comp]
          slice_rhs 1 2 => rw [associator_naturality]
          slice_rhs 2 3 => rw [← tensor_comp, category.comp_id]))
  left_act_hom' := by
    refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
    dsimp
    slice_lhs 1 2 => rw [tensor_Bimod.id_tensor_π_act_left]
    slice_lhs 3 4 => rw [ι_colim_map, parallel_pair_hom_app_one]
    slice_lhs 2 3 => rw [← tensor_comp, hom.left_act_hom, category.id_comp]
    slice_rhs 1 2 => rw [← id_tensor_comp, ι_colim_map, parallel_pair_hom_app_one, id_tensor_comp]
    slice_rhs 2 3 => rw [tensor_Bimod.id_tensor_π_act_left]
    slice_rhs 1 2 => rw [associator_inv_naturality]
    slice_rhs 2 3 => rw [← tensor_comp, category.comp_id]
  right_act_hom' := by
    refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
    dsimp
    slice_lhs 1 2 => rw [tensor_Bimod.π_tensor_id_act_right]
    slice_lhs 3 4 => rw [ι_colim_map, parallel_pair_hom_app_one]
    slice_lhs 2 3 => rw [← tensor_comp, category.id_comp, hom.right_act_hom]
    slice_rhs 1 2 => rw [← comp_tensor_id, ι_colim_map, parallel_pair_hom_app_one, comp_tensor_id]
    slice_rhs 2 3 => rw [tensor_Bimod.π_tensor_id_act_right]
    slice_rhs 1 2 => rw [associator_naturality]
    slice_rhs 2 3 => rw [← tensor_comp, category.comp_id]
#align Bimod.tensor_hom Bimod.tensorHom

theorem tensor_id {X Y Z : Mon_ C} {M : Bimod X Y} {N : Bimod Y Z} :
    tensorHom (𝟙 M) (𝟙 N) = 𝟙 (M.tensorBimod N) := by
  ext
  simp only [id_hom', tensor_id, tensor_hom_hom, ι_colim_map, parallel_pair_hom_app_one]
  dsimp; dsimp only [tensor_Bimod.X]
  simp only [category.id_comp, category.comp_id]
#align Bimod.tensor_id Bimod.tensor_id

theorem tensor_comp {X Y Z : Mon_ C} {M₁ M₂ M₃ : Bimod X Y} {N₁ N₂ N₃ : Bimod Y Z} (f₁ : M₁ ⟶ M₂)
    (f₂ : M₂ ⟶ M₃) (g₁ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  ext
  simp only [comp_hom', tensor_comp, tensor_hom_hom, ι_colim_map, parallel_pair_hom_app_one,
    category.assoc, ι_colim_map_assoc]
#align Bimod.tensor_comp Bimod.tensor_comp

end

namespace AssociatorBimod

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

variable {R S T U : Mon_ C} (P : Bimod R S) (Q : Bimod S T) (L : Bimod T U)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An auxiliary morphism for the definition of the underlying morphism of the forward component of
the associator isomorphism. -/
noncomputable def homAux : (P.tensorBimod Q).pt ⊗ L.pt ⟶ (P.tensorBimod (Q.tensorBimod L)).pt :=
  (PreservesCoequalizer.iso (tensorRight L.pt) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).Hom ≫ (𝟙 P.pt ⊗ coequalizer.π _ _) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [tensor_Bimod.X]
        slice_lhs 1 2 => rw [associator_naturality]
        slice_lhs 2 3 =>
          rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
        slice_lhs 3 4 => rw [coequalizer.condition]
        slice_lhs 2 3 => rw [← monoidal_category.tensor_id, associator_naturality]
        slice_lhs 3 4 => rw [← id_tensor_comp, tensor_Bimod.id_tensor_π_act_left, id_tensor_comp]
        slice_rhs 1 1 => rw [comp_tensor_id]
        slice_rhs 2 3 => rw [associator_naturality]
        slice_rhs 3 4 => rw [← id_tensor_comp]
        coherence)
#align Bimod.associator_Bimod.hom_aux Bimod.AssociatorBimod.homAux

/-- The underlying morphism of the forward component of the associator isomorphism. -/
noncomputable def hom :
    ((P.tensorBimod Q).tensorBimod L).pt ⟶ (P.tensorBimod (Q.tensorBimod L)).pt :=
  coequalizer.desc (homAux P Q L)
    (by
      dsimp [hom_aux]
      refine' (cancel_epi ((tensor_right _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _
      dsimp [tensor_Bimod.X]
      slice_lhs 1 2 =>
        rw [← comp_tensor_id, tensor_Bimod.π_tensor_id_act_right, comp_tensor_id, comp_tensor_id]
      slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      slice_lhs 2 3 => rw [associator_naturality]
      slice_lhs 3 4 => rw [← id_tensor_comp, coequalizer.condition, id_tensor_comp, id_tensor_comp]
      slice_rhs 1 2 => rw [associator_naturality]
      slice_rhs 2 3 =>
        rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
      slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      slice_rhs 2 3 => rw [← monoidal_category.tensor_id, associator_naturality]
      coherence)
#align Bimod.associator_Bimod.hom Bimod.AssociatorBimod.hom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem hom_left_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actLeft ≫ hom P Q L =
      (𝟙 R.pt ⊗ hom P Q L) ≫ (P.tensorBimod (Q.tensorBimod L)).actLeft := by
  dsimp; dsimp [hom, hom_aux]
  refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
  rw [tensor_left_map]
  slice_lhs 1 2 => rw [tensor_Bimod.id_tensor_π_act_left]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← id_tensor_comp, coequalizer.π_desc, id_tensor_comp]
  refine' (cancel_epi ((tensor_right _ ⋙ tensor_left _).map (coequalizer.π _ _))).1 _
  dsimp; dsimp [tensor_Bimod.X]
  slice_lhs 1 2 => rw [associator_inv_naturality]
  slice_lhs 2 3 =>
    rw [← comp_tensor_id, tensor_Bimod.id_tensor_π_act_left, comp_tensor_id, comp_tensor_id]
  slice_lhs 4 6 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [associator_naturality]
  slice_lhs 4 5 => rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor]
  slice_rhs 1 3 =>
    rw [← id_tensor_comp, ← id_tensor_comp, π_tensor_id_preserves_coequalizer_inv_desc,
      id_tensor_comp, id_tensor_comp]
  slice_rhs 3 4 => erw [tensor_Bimod.id_tensor_π_act_left P (Q.tensor_Bimod L)]
  slice_rhs 2 3 => erw [associator_inv_naturality]
  slice_rhs 3 4 => erw [monoidal_category.tensor_id, id_tensor_comp_tensor_id]
  coherence
#align Bimod.associator_Bimod.hom_left_act_hom' Bimod.AssociatorBimod.hom_left_act_hom'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem hom_right_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actRight ≫ hom P Q L =
      (hom P Q L ⊗ 𝟙 U.pt) ≫ (P.tensorBimod (Q.tensorBimod L)).actRight := by
  dsimp; dsimp [hom, hom_aux]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  rw [tensor_right_map]
  slice_lhs 1 2 => rw [tensor_Bimod.π_tensor_id_act_right]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc, comp_tensor_id]
  refine' (cancel_epi ((tensor_right _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp; dsimp [tensor_Bimod.X]
  slice_lhs 1 2 => rw [associator_naturality]
  slice_lhs 2 3 =>
    rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 2 3 => rw [← monoidal_category.tensor_id, associator_naturality]
  slice_rhs 1 3 =>
    rw [← comp_tensor_id, ← comp_tensor_id, π_tensor_id_preserves_coequalizer_inv_desc,
      comp_tensor_id, comp_tensor_id]
  slice_rhs 3 4 => erw [tensor_Bimod.π_tensor_id_act_right P (Q.tensor_Bimod L)]
  slice_rhs 2 3 => erw [associator_naturality]
  dsimp
  slice_rhs 3 4 =>
    rw [← id_tensor_comp, tensor_Bimod.π_tensor_id_act_right, id_tensor_comp, id_tensor_comp]
  coherence
#align Bimod.associator_Bimod.hom_right_act_hom' Bimod.AssociatorBimod.hom_right_act_hom'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- An auxiliary morphism for the definition of the underlying morphism of the inverse component of
the associator isomorphism. -/
noncomputable def invAux : P.pt ⊗ (Q.tensorBimod L).pt ⟶ ((P.tensorBimod Q).tensorBimod L).pt :=
  (PreservesCoequalizer.iso (tensorLeft P.pt) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).inv ≫ (coequalizer.π _ _ ⊗ 𝟙 L.pt) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [tensor_Bimod.X]
        slice_lhs 1 2 => rw [associator_inv_naturality]
        rw [← iso.inv_hom_id_assoc (α_ _ _ _) (𝟙 P.X ⊗ Q.act_right), comp_tensor_id]
        slice_lhs 3 4 =>
          rw [← comp_tensor_id, category.assoc, ← tensor_Bimod.π_tensor_id_act_right,
            comp_tensor_id]
        slice_lhs 4 5 => rw [coequalizer.condition]
        slice_lhs 3 4 => rw [associator_naturality]
        slice_lhs 4 5 => rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor]
        slice_rhs 1 2 => rw [id_tensor_comp]
        slice_rhs 2 3 => rw [associator_inv_naturality]
        slice_rhs 3 4 => rw [monoidal_category.tensor_id, id_tensor_comp_tensor_id]
        coherence)
#align Bimod.associator_Bimod.inv_aux Bimod.AssociatorBimod.invAux

/-- The underlying morphism of the inverse component of the associator isomorphism. -/
noncomputable def inv :
    (P.tensorBimod (Q.tensorBimod L)).pt ⟶ ((P.tensorBimod Q).tensorBimod L).pt :=
  coequalizer.desc (invAux P Q L)
    (by
      dsimp [inv_aux]
      refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
      dsimp [tensor_Bimod.X]
      slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
      slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_lhs 1 2 => rw [← monoidal_category.tensor_id, associator_inv_naturality]
      slice_lhs 2 3 => rw [← comp_tensor_id, coequalizer.condition, comp_tensor_id, comp_tensor_id]
      slice_rhs 1 2 => rw [← monoidal_category.tensor_id, associator_naturality]
      slice_rhs 2 3 =>
        rw [← id_tensor_comp, tensor_Bimod.id_tensor_π_act_left, id_tensor_comp, id_tensor_comp]
      slice_rhs 4 6 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_rhs 3 4 => rw [associator_inv_naturality]
      coherence)
#align Bimod.associator_Bimod.inv Bimod.AssociatorBimod.inv

theorem hom_inv_id : hom P Q L ≫ inv P Q L = 𝟙 _ := by
  dsimp [hom, hom_aux, inv, inv_aux]
  ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  rw [tensor_right_map]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [iso.hom_inv_id_assoc]
  dsimp only [tensor_Bimod.X]
  slice_rhs 2 3 => rw [category.comp_id]
  rfl
#align Bimod.associator_Bimod.hom_inv_id Bimod.AssociatorBimod.hom_inv_id

theorem inv_hom_id : inv P Q L ≫ hom P Q L = 𝟙 _ := by
  dsimp [hom, hom_aux, inv, inv_aux]
  ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
  rw [tensor_left_map]
  slice_lhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [iso.inv_hom_id_assoc]
  dsimp only [tensor_Bimod.X]
  slice_rhs 2 3 => rw [category.comp_id]
  rfl
#align Bimod.associator_Bimod.inv_hom_id Bimod.AssociatorBimod.inv_hom_id

end AssociatorBimod

namespace LeftUnitorBimod

variable {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the left unitor isomorphism. -/
noncomputable def hom : TensorBimod.x (regular R) P ⟶ P.pt :=
  coequalizer.desc P.actLeft (by dsimp; rw [category.assoc, left_assoc])
#align Bimod.left_unitor_Bimod.hom Bimod.LeftUnitorBimod.hom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The underlying morphism of the inverse component of the left unitor isomorphism. -/
noncomputable def inv : P.pt ⟶ TensorBimod.x (regular R) P :=
  (λ_ P.pt).inv ≫ (R.one ⊗ 𝟙 _) ≫ coequalizer.π _ _
#align Bimod.left_unitor_Bimod.inv Bimod.LeftUnitorBimod.inv

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, tensor_Bimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [left_unitor_inv_naturality]
  slice_lhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  slice_lhs 3 3 => rw [← iso.inv_hom_id_assoc (α_ R.X R.X P.X) (𝟙 R.X ⊗ P.act_left)]
  slice_lhs 4 6 => rw [← category.assoc, ← coequalizer.condition]
  slice_lhs 2 3 => rw [← monoidal_category.tensor_id, associator_inv_naturality]
  slice_lhs 3 4 => rw [← comp_tensor_id, Mon_.one_mul]
  slice_rhs 1 2 => rw [category.comp_id]
  coherence
#align Bimod.left_unitor_Bimod.hom_inv_id Bimod.LeftUnitorBimod.hom_inv_id

theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [one_act_left, iso.inv_hom_id]
#align Bimod.left_unitor_Bimod.inv_hom_id Bimod.LeftUnitorBimod.inv_hom_id

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem hom_left_act_hom' :
    ((regular R).tensorBimod P).actLeft ≫ hom P = (𝟙 R.pt ⊗ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, tensor_Bimod.act_left, regular]
  refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [left_assoc]
  slice_rhs 1 2 => rw [← id_tensor_comp, coequalizer.π_desc]
  rw [iso.inv_hom_id_assoc]
#align Bimod.left_unitor_Bimod.hom_left_act_hom' Bimod.LeftUnitorBimod.hom_left_act_hom'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem hom_right_act_hom' :
    ((regular R).tensorBimod P).actRight ≫ hom P = (hom P ⊗ 𝟙 S.pt) ≫ P.actRight := by
  dsimp; dsimp [hom, tensor_Bimod.act_right, regular]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  slice_rhs 1 2 => rw [middle_assoc]
  simp only [category.assoc]
#align Bimod.left_unitor_Bimod.hom_right_act_hom' Bimod.LeftUnitorBimod.hom_right_act_hom'

end LeftUnitorBimod

namespace RightUnitorBimod

variable {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the right unitor isomorphism. -/
noncomputable def hom : TensorBimod.x P (regular S) ⟶ P.pt :=
  coequalizer.desc P.actRight (by dsimp; rw [category.assoc, right_assoc, iso.hom_inv_id_assoc])
#align Bimod.right_unitor_Bimod.hom Bimod.RightUnitorBimod.hom

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The underlying morphism of the inverse component of the right unitor isomorphism. -/
noncomputable def inv : P.pt ⟶ TensorBimod.x P (regular S) :=
  (ρ_ P.pt).inv ≫ (𝟙 _ ⊗ S.one) ≫ coequalizer.π _ _
#align Bimod.right_unitor_Bimod.inv Bimod.RightUnitorBimod.inv

theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, tensor_Bimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [right_unitor_inv_naturality]
  slice_lhs 2 3 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_lhs 3 4 => rw [coequalizer.condition]
  slice_lhs 2 3 => rw [← monoidal_category.tensor_id, associator_naturality]
  slice_lhs 3 4 => rw [← id_tensor_comp, Mon_.mul_one]
  slice_rhs 1 2 => rw [category.comp_id]
  coherence
#align Bimod.right_unitor_Bimod.hom_inv_id Bimod.RightUnitorBimod.hom_inv_id

theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [act_right_one, iso.inv_hom_id]
#align Bimod.right_unitor_Bimod.inv_hom_id Bimod.RightUnitorBimod.inv_hom_id

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem hom_left_act_hom' :
    (P.tensorBimod (regular S)).actLeft ≫ hom P = (𝟙 R.pt ⊗ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, tensor_Bimod.act_left, regular]
  refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [middle_assoc]
  slice_rhs 1 2 => rw [← id_tensor_comp, coequalizer.π_desc]
  rw [iso.inv_hom_id_assoc]
#align Bimod.right_unitor_Bimod.hom_left_act_hom' Bimod.RightUnitorBimod.hom_left_act_hom'

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem hom_right_act_hom' :
    (P.tensorBimod (regular S)).actRight ≫ hom P = (hom P ⊗ 𝟙 S.pt) ≫ P.actRight := by
  dsimp; dsimp [hom, tensor_Bimod.act_right, regular]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [right_assoc]
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  rw [iso.hom_inv_id_assoc]
#align Bimod.right_unitor_Bimod.hom_right_act_hom' Bimod.RightUnitorBimod.hom_right_act_hom'

end RightUnitorBimod

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The associator as a bimodule isomorphism. -/
noncomputable def associatorBimod {W X Y Z : Mon_ C} (L : Bimod W X) (M : Bimod X Y)
    (N : Bimod Y Z) : (L.tensorBimod M).tensorBimod N ≅ L.tensorBimod (M.tensorBimod N) :=
  isoOfIso
    { Hom := AssociatorBimod.hom L M N
      inv := AssociatorBimod.inv L M N
      hom_inv_id' := AssociatorBimod.hom_inv_id L M N
      inv_hom_id' := AssociatorBimod.inv_hom_id L M N } (AssociatorBimod.hom_left_act_hom' L M N)
    (AssociatorBimod.hom_right_act_hom' L M N)
#align Bimod.associator_Bimod Bimod.associatorBimod

/-- The left unitor as a bimodule isomorphism. -/
noncomputable def leftUnitorBimod {X Y : Mon_ C} (M : Bimod X Y) : (regular X).tensorBimod M ≅ M :=
  isoOfIso
    { Hom := LeftUnitorBimod.hom M
      inv := LeftUnitorBimod.inv M
      hom_inv_id' := LeftUnitorBimod.hom_inv_id M
      inv_hom_id' := LeftUnitorBimod.inv_hom_id M } (LeftUnitorBimod.hom_left_act_hom' M)
    (LeftUnitorBimod.hom_right_act_hom' M)
#align Bimod.left_unitor_Bimod Bimod.leftUnitorBimod

/-- The right unitor as a bimodule isomorphism. -/
noncomputable def rightUnitorBimod {X Y : Mon_ C} (M : Bimod X Y) : M.tensorBimod (regular Y) ≅ M :=
  isoOfIso
    { Hom := RightUnitorBimod.hom M
      inv := RightUnitorBimod.inv M
      hom_inv_id' := RightUnitorBimod.hom_inv_id M
      inv_hom_id' := RightUnitorBimod.inv_hom_id M } (RightUnitorBimod.hom_left_act_hom' M)
    (RightUnitorBimod.hom_right_act_hom' M)
#align Bimod.right_unitor_Bimod Bimod.rightUnitorBimod

theorem whisker_left_comp_bimod {X Y Z : Mon_ C} (M : Bimod X Y) {N P Q : Bimod Y Z} (f : N ⟶ P)
    (g : P ⟶ Q) : tensorHom (𝟙 M) (f ≫ g) = tensorHom (𝟙 M) f ≫ tensorHom (𝟙 M) g := by
  rw [← tensor_comp, category.comp_id]
#align Bimod.whisker_left_comp_Bimod Bimod.whisker_left_comp_bimod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem id_whisker_left_bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
    tensorHom (𝟙 (regular X)) f = (leftUnitorBimod M).Hom ≫ f ≫ (leftUnitorBimod N).inv := by
  dsimp [tensor_hom, regular, left_unitor_Bimod]
  ext; dsimp
  slice_lhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  dsimp [left_unitor_Bimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [left_unitor_Bimod.inv]
  slice_rhs 1 2 => rw [hom.left_act_hom]
  slice_rhs 2 3 => rw [left_unitor_inv_naturality]
  slice_rhs 3 4 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  slice_rhs 4 4 => rw [← iso.inv_hom_id_assoc (α_ X.X X.X N.X) (𝟙 X.X ⊗ N.act_left)]
  slice_rhs 5 7 => rw [← category.assoc, ← coequalizer.condition]
  slice_rhs 3 4 => rw [← monoidal_category.tensor_id, associator_inv_naturality]
  slice_rhs 4 5 => rw [← comp_tensor_id, Mon_.one_mul]
  have : (λ_ (X.X ⊗ N.X)).inv ≫ (α_ (𝟙_ C) X.X N.X).inv ≫ ((λ_ X.X).Hom ⊗ 𝟙 N.X) = 𝟙 _ := by
    pure_coherence
  slice_rhs 2 4 => rw [this]
  slice_rhs 1 2 => rw [category.comp_id]
#align Bimod.id_whisker_left_Bimod Bimod.id_whisker_left_bimod

theorem comp_whisker_left_bimod {W X Y Z : Mon_ C} (M : Bimod W X) (N : Bimod X Y)
    {P P' : Bimod Y Z} (f : P ⟶ P') :
    tensorHom (𝟙 (M.tensorBimod N)) f =
      (associatorBimod M N P).Hom ≫
        tensorHom (𝟙 M) (tensorHom (𝟙 N) f) ≫ (associatorBimod M N P').inv := by
  dsimp [tensor_hom, tensor_Bimod, associator_Bimod]
  ext; dsimp
  slice_lhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  dsimp [tensor_Bimod.X, associator_Bimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.hom_aux, associator_Bimod.inv]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  rw [tensor_right_map]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 2 3 => rw [← id_tensor_comp, ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.inv_aux]
  slice_rhs 2 2 => rw [id_tensor_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_inv_naturality]
  slice_rhs 1 3 => rw [iso.hom_inv_id_assoc, monoidal_category.tensor_id]
  slice_lhs 1 2 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  dsimp only [tensor_Bimod.X]
  simp only [category.assoc]
#align Bimod.comp_whisker_left_Bimod Bimod.comp_whisker_left_bimod

theorem comp_whisker_right_bimod {X Y Z : Mon_ C} {M N P : Bimod X Y} (f : M ⟶ N) (g : N ⟶ P)
    (Q : Bimod Y Z) : tensorHom (f ≫ g) (𝟙 Q) = tensorHom f (𝟙 Q) ≫ tensorHom g (𝟙 Q) := by
  rw [← tensor_comp, category.comp_id]
#align Bimod.comp_whisker_right_Bimod Bimod.comp_whisker_right_bimod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem whisker_right_id_bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
    tensorHom f (𝟙 (regular Y)) = (rightUnitorBimod M).Hom ≫ f ≫ (rightUnitorBimod N).inv := by
  dsimp [tensor_hom, regular, right_unitor_Bimod]
  ext; dsimp
  slice_lhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  dsimp [right_unitor_Bimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [right_unitor_Bimod.inv]
  slice_rhs 1 2 => rw [hom.right_act_hom]
  slice_rhs 2 3 => rw [right_unitor_inv_naturality]
  slice_rhs 3 4 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_rhs 4 5 => rw [coequalizer.condition]
  slice_rhs 3 4 => rw [← monoidal_category.tensor_id, associator_naturality]
  slice_rhs 4 5 => rw [← id_tensor_comp, Mon_.mul_one]
  have : (ρ_ (N.X ⊗ Y.X)).inv ≫ (α_ N.X Y.X (𝟙_ C)).Hom ≫ (𝟙 N.X ⊗ (ρ_ Y.X).Hom) = 𝟙 _ := by
    pure_coherence
  slice_rhs 2 4 => rw [this]
  slice_rhs 1 2 => rw [category.comp_id]
#align Bimod.whisker_right_id_Bimod Bimod.whisker_right_id_bimod

theorem whisker_right_comp_bimod {W X Y Z : Mon_ C} {M M' : Bimod W X} (f : M ⟶ M') (N : Bimod X Y)
    (P : Bimod Y Z) :
    tensorHom f (𝟙 (N.tensorBimod P)) =
      (associatorBimod M N P).inv ≫
        tensorHom (tensorHom f (𝟙 N)) (𝟙 P) ≫ (associatorBimod M' N P).Hom := by
  dsimp [tensor_hom, tensor_Bimod, associator_Bimod]
  ext; dsimp
  slice_lhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  dsimp [tensor_Bimod.X, associator_Bimod.inv]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.inv_aux, associator_Bimod.hom]
  refine' (cancel_epi ((tensor_left _).map (coequalizer.π _ _))).1 _
  rw [tensor_left_map]
  slice_rhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 2 3 => rw [← comp_tensor_id, ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.hom_aux]
  slice_rhs 2 2 => rw [comp_tensor_id]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_naturality]
  slice_rhs 1 3 => rw [iso.inv_hom_id_assoc, monoidal_category.tensor_id]
  slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  dsimp only [tensor_Bimod.X]
  simp only [category.assoc]
#align Bimod.whisker_right_comp_Bimod Bimod.whisker_right_comp_bimod

theorem whisker_assoc_bimod {W X Y Z : Mon_ C} (M : Bimod W X) {N N' : Bimod X Y} (f : N ⟶ N')
    (P : Bimod Y Z) :
    tensorHom (tensorHom (𝟙 M) f) (𝟙 P) =
      (associatorBimod M N P).Hom ≫
        tensorHom (𝟙 M) (tensorHom f (𝟙 P)) ≫ (associatorBimod M N' P).inv := by
  dsimp [tensor_hom, tensor_Bimod, associator_Bimod]
  ext; dsimp
  slice_lhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  dsimp [associator_Bimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.hom_aux]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  rw [tensor_right_map]
  slice_lhs 1 2 => rw [← comp_tensor_id, ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 2 3 => rw [← id_tensor_comp, ι_colim_map, parallel_pair_hom_app_one]
  dsimp [associator_Bimod.inv]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.inv_aux]
  slice_rhs 2 2 => rw [id_tensor_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_inv_naturality]
  slice_rhs 1 3 => rw [iso.hom_inv_id_assoc]
  slice_lhs 1 1 => rw [comp_tensor_id]
#align Bimod.whisker_assoc_Bimod Bimod.whisker_assoc_bimod

theorem whisker_exchange_bimod {X Y Z : Mon_ C} {M N : Bimod X Y} {P Q : Bimod Y Z} (f : M ⟶ N)
    (g : P ⟶ Q) : tensorHom (𝟙 M) g ≫ tensorHom f (𝟙 Q) = tensorHom f (𝟙 P) ≫ tensorHom (𝟙 N) g :=
  by
  dsimp [tensor_hom]
  ext; dsimp
  slice_lhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_lhs 2 3 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_lhs 1 2 => rw [id_tensor_comp_tensor_id]
  slice_rhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 2 3 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_rhs 1 2 => rw [tensor_id_comp_id_tensor]
#align Bimod.whisker_exchange_Bimod Bimod.whisker_exchange_bimod

theorem pentagon_bimod {V W X Y Z : Mon_ C} (M : Bimod V W) (N : Bimod W X) (P : Bimod X Y)
    (Q : Bimod Y Z) :
    tensorHom (associatorBimod M N P).Hom (𝟙 Q) ≫
        (associatorBimod M (N.tensorBimod P) Q).Hom ≫ tensorHom (𝟙 M) (associatorBimod N P Q).Hom =
      (associatorBimod (M.tensorBimod N) P Q).Hom ≫ (associatorBimod M N (P.tensorBimod Q)).Hom :=
  by
  dsimp [tensor_hom, associator_Bimod]; ext; dsimp
  dsimp only [associator_Bimod.hom]
  slice_lhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.hom_aux]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp
  slice_lhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  refine' (cancel_epi ((tensor_right _ ⋙ tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp
  slice_lhs 1 2 =>
    rw [← comp_tensor_id, π_tensor_id_preserves_coequalizer_inv_desc, comp_tensor_id,
      comp_tensor_id]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  dsimp only [tensor_Bimod.X]
  slice_lhs 2 3 => rw [associator_naturality]
  slice_lhs 5 6 => rw [ι_colim_map, parallel_pair_hom_app_one]
  slice_lhs 4 5 => rw [← id_tensor_comp, coequalizer.π_desc]
  slice_lhs 3 4 =>
    rw [← id_tensor_comp, π_tensor_id_preserves_coequalizer_inv_desc, id_tensor_comp,
      id_tensor_comp]
  slice_rhs 1 2 => rw [associator_naturality]
  slice_rhs 2 3 =>
    rw [monoidal_category.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [← monoidal_category.tensor_id, associator_naturality]
  coherence
#align Bimod.pentagon_Bimod Bimod.pentagon_bimod

theorem triangle_bimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) :
    (associatorBimod M (regular Y) N).Hom ≫ tensorHom (𝟙 M) (leftUnitorBimod N).Hom =
      tensorHom (rightUnitorBimod M).Hom (𝟙 N) := by
  dsimp [tensor_hom, associator_Bimod, left_unitor_Bimod, right_unitor_Bimod]
  ext; dsimp
  dsimp [associator_Bimod.hom]
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  dsimp [associator_Bimod.hom_aux]
  slice_rhs 1 2 => rw [ι_colim_map, parallel_pair_hom_app_one]
  dsimp [right_unitor_Bimod.hom]
  refine' (cancel_epi ((tensor_right _).map (coequalizer.π _ _))).1 _
  dsimp [regular]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [ι_colim_map, parallel_pair_hom_app_one]
  dsimp [left_unitor_Bimod.hom]
  slice_lhs 2 3 => rw [← id_tensor_comp, coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.condition]
  simp only [category.assoc]
#align Bimod.triangle_Bimod Bimod.triangle_bimod

/-- The bicategory of algebras (monoids) and bimodules, all internal to some monoidal category. -/
noncomputable def monBicategory : Bicategory (Mon_ C) where
  Hom X Y := Bimod X Y
  id X := regular X
  comp _ _ _ M N := tensorBimod M N
  whiskerLeft _ _ _ L _ _ f := tensorHom (𝟙 L) f
  whiskerRight _ _ _ _ _ f N := tensorHom f (𝟙 N)
  associator _ _ _ _ L M N := associatorBimod L M N
  leftUnitor _ _ M := leftUnitorBimod M
  rightUnitor _ _ M := rightUnitorBimod M
  whiskerLeft_id _ _ _ _ _ := tensor_id
  whiskerLeft_comp _ _ _ M _ _ _ f g := whisker_left_comp_bimod M f g
  id_whiskerLeft _ _ _ _ f := id_whisker_left_bimod f
  comp_whiskerLeft _ _ _ _ M N _ _ f := comp_whisker_left_bimod M N f
  id_whiskerRight _ _ _ _ _ := tensor_id
  comp_whiskerRight _ _ _ _ _ _ f g Q := comp_whisker_right_bimod f g Q
  whiskerRight_id _ _ _ _ f := whisker_right_id_bimod f
  whiskerRight_comp _ _ _ _ _ _ f N P := whisker_right_comp_bimod f N P
  whisker_assoc _ _ _ _ M _ _ f P := whisker_assoc_bimod M f P
  whisker_exchange _ _ _ _ _ _ _ f g := whisker_exchange_bimod f g
  pentagon _ _ _ _ _ M N P Q := pentagon_bimod M N P Q
  triangle _ _ _ M N := triangle_bimod M N
#align Bimod.Mon_bicategory Bimod.monBicategory

end Bimod

