/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oleksandr Manzyuk
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

#align_import category_theory.monoidal.Bimod from "leanprover-community/mathlib"@"4698e35ca56a0d4fa53aa5639c3364e0a77f4eba"

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

theorem id_tensor_π_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Z ⊗ Y ⟶ W)
    (wh : (𝟙 Z ⊗ f) ≫ h = (𝟙 Z ⊗ g) ≫ h) :
    (𝟙 Z ⊗ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh
#align id_tensor_π_preserves_coequalizer_inv_desc id_tensor_π_preserves_coequalizer_inv_desc

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

theorem π_tensor_id_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Y ⊗ Z ⟶ W)
    (wh : (f ⊗ 𝟙 Z) ≫ h = (g ⊗ 𝟙 Z) ≫ h) :
    (coequalizer.π f g ⊗ 𝟙 Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorRight Z) f g h wh
#align π_tensor_id_preserves_coequalizer_inv_desc π_tensor_id_preserves_coequalizer_inv_desc

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

/-- A bimodule object for a pair of monoid objects, all internal to some monoidal category. -/
structure Bimod (A B : Mon_ C) where
  X : C
  actLeft : A.X ⊗ X ⟶ X
  one_actLeft : (A.one ⊗ 𝟙 X) ≫ actLeft = (λ_ X).hom := by aesop_cat
  left_assoc :
    (A.mul ⊗ 𝟙 X) ≫ actLeft = (α_ A.X A.X X).hom ≫ (𝟙 A.X ⊗ actLeft) ≫ actLeft := by aesop_cat
  actRight : X ⊗ B.X ⟶ X
  actRight_one : (𝟙 X ⊗ B.one) ≫ actRight = (ρ_ X).hom := by aesop_cat
  right_assoc :
    (𝟙 X ⊗ B.mul) ≫ actRight = (α_ X B.X B.X).inv ≫ (actRight ⊗ 𝟙 B.X) ≫ actRight := by
    aesop_cat
  middle_assoc :
    (actLeft ⊗ 𝟙 B.X) ≫ actRight = (α_ A.X X B.X).hom ≫ (𝟙 A.X ⊗ actRight) ≫ actLeft := by
    aesop_cat
set_option linter.uppercaseLean3 false in
#align Bimod Bimod

attribute [reassoc (attr := simp)] Bimod.one_actLeft Bimod.actRight_one Bimod.left_assoc
  Bimod.right_assoc Bimod.middle_assoc

namespace Bimod

variable {A B : Mon_ C} (M : Bimod A B)

/-- A morphism of bimodule objects. -/
@[ext]
structure Hom (M N : Bimod A B) where
  hom : M.X ⟶ N.X
  left_act_hom : M.actLeft ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.actLeft := by aesop_cat
  right_act_hom : M.actRight ≫ hom = (hom ⊗ 𝟙 B.X) ≫ N.actRight := by aesop_cat
set_option linter.uppercaseLean3 false in
#align Bimod.hom Bimod.Hom

attribute [reassoc (attr := simp)] Hom.left_act_hom Hom.right_act_hom

/-- The identity morphism on a bimodule object. -/
@[simps]
def id' (M : Bimod A B) : Hom M M where hom := 𝟙 M.X
set_option linter.uppercaseLean3 false in
#align Bimod.id' Bimod.id'

instance homInhabited (M : Bimod A B) : Inhabited (Hom M M) :=
  ⟨id' M⟩
set_option linter.uppercaseLean3 false in
#align Bimod.hom_inhabited Bimod.homInhabited

/-- Composition of bimodule object morphisms. -/
@[simps]
def comp {M N O : Bimod A B} (f : Hom M N) (g : Hom N O) : Hom M O where hom := f.hom ≫ g.hom
set_option linter.uppercaseLean3 false in
#align Bimod.comp Bimod.comp

instance : Category (Bimod A B) where
  Hom M N := Hom M N
  id := id'
  comp f g := comp f g

-- porting note: added because `Hom.ext` is not triggered automatically
@[ext]
lemma hom_ext {M N : Bimod A B} (f g : M ⟶ N) (h : f.hom = g.hom) : f = g :=
  Hom.ext _ _ h

@[simp]
theorem id_hom' (M : Bimod A B) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl
set_option linter.uppercaseLean3 false in
#align Bimod.id_hom' Bimod.id_hom'

@[simp]
theorem comp_hom' {M N K : Bimod A B} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl
set_option linter.uppercaseLean3 false in
#align Bimod.comp_hom' Bimod.comp_hom'

/-- Construct an isomorphism of bimodules by giving an isomorphism between the underlying objects
and checking compatibility with left and right actions only in the forward direction.
-/
@[simps]
def isoOfIso {X Y : Mon_ C} {P Q : Bimod X Y} (f : P.X ≅ Q.X)
    (f_left_act_hom : P.actLeft ≫ f.hom = (𝟙 X.X ⊗ f.hom) ≫ Q.actLeft)
    (f_right_act_hom : P.actRight ≫ f.hom = (f.hom ⊗ 𝟙 Y.X) ≫ Q.actRight) : P ≅ Q where
  hom :=
    { hom := f.hom }
  inv :=
    { hom := f.inv
      left_act_hom := by
        rw [← cancel_mono f.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          f_left_act_hom, ← Category.assoc, ← id_tensor_comp, Iso.inv_hom_id,
          MonoidalCategory.tensor_id, Category.id_comp]
      right_act_hom := by
        rw [← cancel_mono f.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          f_right_act_hom, ← Category.assoc, ← comp_tensor_id, Iso.inv_hom_id,
          MonoidalCategory.tensor_id, Category.id_comp] }
  hom_inv_id := by ext; dsimp; rw [Iso.hom_inv_id]
                   -- ⊢ (Hom.mk f.hom ≫ Hom.mk f.inv).hom = (𝟙 P).hom
                        -- ⊢ f.hom ≫ f.inv = 𝟙 P.X
                               -- 🎉 no goals
  inv_hom_id := by ext; dsimp; rw [Iso.inv_hom_id]
                   -- ⊢ (Hom.mk f.inv ≫ Hom.mk f.hom).hom = (𝟙 Q).hom
                        -- ⊢ f.inv ≫ f.hom = 𝟙 Q.X
                               -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.iso_of_iso Bimod.isoOfIso

variable (A)

/-- A monoid object as a bimodule over itself. -/
@[simps]
def regular : Bimod A A where
  X := A.X
  actLeft := A.mul
  actRight := A.mul
set_option linter.uppercaseLean3 false in
#align Bimod.regular Bimod.regular

instance : Inhabited (Bimod A A) :=
  ⟨regular A⟩

/-- The forgetful functor from bimodule objects to the ambient category. -/
def forget : Bimod A B ⥤ C where
  obj A := A.X
  map f := f.hom
set_option linter.uppercaseLean3 false in
#align Bimod.forget Bimod.forget

open CategoryTheory.Limits

variable [HasCoequalizers C]

namespace TensorBimod

variable {R S T : Mon_ C} (P : Bimod R S) (Q : Bimod S T)

/-- The underlying object of the tensor product of two bimodules. -/
noncomputable def X : C :=
  coequalizer (P.actRight ⊗ 𝟙 Q.X) ((α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.actLeft))
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.X Bimod.TensorBimod.X

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- Left action for the tensor product of two bimodules. -/
noncomputable def actLeft : R.X ⊗ X P Q ⟶ X P Q :=
  (PreservesCoequalizer.iso (tensorLeft R.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((𝟙 _ ⊗ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫ (P.actLeft ⊗ 𝟙 S.X ⊗ 𝟙 Q.X) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).inv ≫ (P.actLeft ⊗ 𝟙 Q.X))
        (by
          dsimp
          -- ⊢ (𝟙 R.X ⊗ P.actRight ⊗ 𝟙 Q.X) ≫ (α_ R.X P.X Q.X).inv ≫ (P.actLeft ⊗ 𝟙 Q.X) =  …
          slice_lhs 1 2 => rw [associator_inv_naturality]
          -- ⊢ ((α_ R.X (P.X ⊗ S.X) Q.X).inv ≫ ((𝟙 R.X ⊗ P.actRight) ⊗ 𝟙 Q.X)) ≫ (P.actLeft …
          slice_rhs 3 4 => rw [associator_inv_naturality]
          -- ⊢ ((α_ R.X (P.X ⊗ S.X) Q.X).inv ≫ ((𝟙 R.X ⊗ P.actRight) ⊗ 𝟙 Q.X)) ≫ (P.actLeft …
          slice_rhs 4 5 => rw [← tensor_comp, middle_assoc, tensor_comp, comp_tensor_id]
          -- ⊢ ((α_ R.X (P.X ⊗ S.X) Q.X).inv ≫ ((𝟙 R.X ⊗ P.actRight) ⊗ 𝟙 Q.X)) ≫ (P.actLeft …
          coherence)
          -- 🎉 no goals
        (by
          dsimp
          -- ⊢ (𝟙 R.X ⊗ (α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actLeft)) ≫ (α_ R.X P.X Q.X).inv  …
          slice_lhs 1 1 => rw [id_tensor_comp]
          -- ⊢ (((𝟙 R.X ⊗ (α_ P.X S.X Q.X).hom) ≫ (𝟙 R.X ⊗ 𝟙 P.X ⊗ Q.actLeft)) ≫ (α_ R.X P. …
          slice_lhs 2 3 => rw [associator_inv_naturality]
          -- ⊢ (𝟙 R.X ⊗ (α_ P.X S.X Q.X).hom) ≫ ((α_ R.X P.X (S.X ⊗ Q.X)).inv ≫ ((𝟙 R.X ⊗ 𝟙 …
          slice_lhs 3 4 => rw [tensor_id, id_tensor_comp_tensor_id]
          -- ⊢ (𝟙 R.X ⊗ (α_ P.X S.X Q.X).hom) ≫ (α_ R.X P.X (S.X ⊗ Q.X)).inv ≫ (P.actLeft ⊗ …
          slice_rhs 4 6 => rw [Iso.inv_hom_id_assoc]
          -- ⊢ (𝟙 R.X ⊗ (α_ P.X S.X Q.X).hom) ≫ (α_ R.X P.X (S.X ⊗ Q.X)).inv ≫ (P.actLeft ⊗ …
          slice_rhs 3 4 => rw [tensor_id, tensor_id_comp_id_tensor]))
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.act_left Bimod.TensorBimod.actLeft

theorem id_tensor_π_actLeft :
    (𝟙 R.X ⊗ coequalizer.π _ _) ≫ actLeft P Q =
      (α_ _ _ _).inv ≫ (P.actLeft ⊗ 𝟙 Q.X) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorLeft _)]
  -- ⊢ ((α_ R.X P.X Q.X).inv ≫ (P.actLeft ⊗ 𝟙 Q.X)) ≫ coequalizer.π (P.actRight ⊗ 𝟙 …
  simp only [Category.assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.id_tensor_π_act_left Bimod.TensorBimod.id_tensor_π_actLeft

theorem one_act_left' : (R.one ⊗ 𝟙 _) ≫ actLeft P Q = (λ_ _).hom := by
  refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft (𝟙_ C)).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X …
  dsimp [X]
  -- ⊢ (𝟙 (𝟙_ C) ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P. …
  -- porting note: had to replace `rw` by `erw`
  slice_lhs 1 2 => erw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  -- ⊢ ((R.one ⊗ 𝟙 (P.X ⊗ Q.X)) ≫ (𝟙 R.X ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_  …
  slice_lhs 2 3 => rw [id_tensor_π_actLeft]
  -- ⊢ (R.one ⊗ 𝟙 (P.X ⊗ Q.X)) ≫ (α_ R.X P.X Q.X).inv ≫ (P.actLeft ⊗ 𝟙 Q.X) ≫ coequ …
  slice_lhs 1 2 => rw [← MonoidalCategory.tensor_id, associator_inv_naturality]
  -- ⊢ (((α_ (𝟙_ C) P.X Q.X).inv ≫ ((R.one ⊗ 𝟙 P.X) ⊗ 𝟙 Q.X)) ≫ (P.actLeft ⊗ 𝟙 Q.X) …
  slice_lhs 2 3 => rw [← comp_tensor_id, one_actLeft]
  -- ⊢ (α_ (𝟙_ C) P.X Q.X).inv ≫ ((λ_ P.X).hom ⊗ 𝟙 Q.X) ≫ coequalizer.π (P.actRight …
  slice_rhs 1 2 => rw [leftUnitor_naturality]
  -- ⊢ (α_ (𝟙_ C) P.X Q.X).inv ≫ ((λ_ P.X).hom ⊗ 𝟙 Q.X) ≫ coequalizer.π (P.actRight …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.one_act_left' Bimod.TensorBimod.one_act_left'

theorem left_assoc' :
    (R.mul ⊗ 𝟙 _) ≫ actLeft P Q = (α_ R.X R.X _).hom ≫ (𝟙 R.X ⊗ actLeft P Q) ≫ actLeft P Q := by
  refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft (R.X ⊗ R.X)).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S. …
  dsimp [X]
  -- ⊢ (𝟙 (R.X ⊗ R.X) ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫  …
  -- porting note: had to replace some `rw` by `erw`
  slice_lhs 1 2 => erw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  -- ⊢ ((R.mul ⊗ 𝟙 (P.X ⊗ Q.X)) ≫ (𝟙 R.X ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_  …
  slice_lhs 2 3 => rw [id_tensor_π_actLeft]
  -- ⊢ (R.mul ⊗ 𝟙 (P.X ⊗ Q.X)) ≫ (α_ R.X P.X Q.X).inv ≫ (P.actLeft ⊗ 𝟙 Q.X) ≫ coequ …
  slice_lhs 1 2 => rw [← MonoidalCategory.tensor_id, associator_inv_naturality]
  -- ⊢ (((α_ (R.X ⊗ R.X) P.X Q.X).inv ≫ ((R.mul ⊗ 𝟙 P.X) ⊗ 𝟙 Q.X)) ≫ (P.actLeft ⊗ 𝟙 …
  slice_lhs 2 3 => rw [← comp_tensor_id, left_assoc, comp_tensor_id, comp_tensor_id]
  -- ⊢ (α_ (R.X ⊗ R.X) P.X Q.X).inv ≫ (((α_ R.X R.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((𝟙 R.X ⊗ P …
  slice_rhs 1 2 => erw [← MonoidalCategory.tensor_id, associator_naturality]
  -- ⊢ (α_ (R.X ⊗ R.X) P.X Q.X).inv ≫ (((α_ R.X R.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((𝟙 R.X ⊗ P …
  slice_rhs 2 3 => rw [← id_tensor_comp, id_tensor_π_actLeft, id_tensor_comp, id_tensor_comp]
  -- ⊢ (α_ (R.X ⊗ R.X) P.X Q.X).inv ≫ (((α_ R.X R.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((𝟙 R.X ⊗ P …
  slice_rhs 4 5 => rw [id_tensor_π_actLeft]
  -- ⊢ (α_ (R.X ⊗ R.X) P.X Q.X).inv ≫ (((α_ R.X R.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((𝟙 R.X ⊗ P …
  slice_rhs 3 4 => rw [associator_inv_naturality]
  -- ⊢ (α_ (R.X ⊗ R.X) P.X Q.X).inv ≫ (((α_ R.X R.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((𝟙 R.X ⊗ P …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.left_assoc' Bimod.TensorBimod.left_assoc'

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Right action for the tensor product of two bimodules. -/
noncomputable def actRight : X P Q ⊗ T.X ⟶ X P Q :=
  (PreservesCoequalizer.iso (tensorRight T.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ 𝟙 S.X ⊗ Q.actRight) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.actRight))
        (by
          dsimp
          -- ⊢ ((P.actRight ⊗ 𝟙 Q.X) ⊗ 𝟙 T.X) ≫ (α_ P.X Q.X T.X).hom ≫ (𝟙 P.X ⊗ Q.actRight) …
          slice_lhs 1 2 => rw [associator_naturality]
          -- ⊢ ((α_ (P.X ⊗ S.X) Q.X T.X).hom ≫ (P.actRight ⊗ 𝟙 Q.X ⊗ 𝟙 T.X)) ≫ (𝟙 P.X ⊗ Q.a …
          slice_lhs 2 3 => rw [tensor_id, tensor_id_comp_id_tensor]
          -- ⊢ (α_ (P.X ⊗ S.X) Q.X T.X).hom ≫ (P.actRight ⊗ Q.actRight) = ((α_ (P.X ⊗ S.X)  …
          slice_rhs 3 4 => rw [associator_inv_naturality]
          -- ⊢ (α_ (P.X ⊗ S.X) Q.X T.X).hom ≫ (P.actRight ⊗ Q.actRight) = (α_ (P.X ⊗ S.X) Q …
          slice_rhs 2 4 => rw [Iso.hom_inv_id_assoc]
          -- ⊢ (α_ (P.X ⊗ S.X) Q.X T.X).hom ≫ (P.actRight ⊗ Q.actRight) = (α_ (P.X ⊗ S.X) Q …
          slice_rhs 2 3 => rw [tensor_id, id_tensor_comp_tensor_id])
          -- 🎉 no goals
        (by
          dsimp
          -- ⊢ ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actLeft) ⊗ 𝟙 T.X) ≫ (α_ P.X Q.X T.X).hom  …
          slice_lhs 1 1 => rw [comp_tensor_id]
          -- ⊢ ((((α_ P.X S.X Q.X).hom ⊗ 𝟙 T.X) ≫ ((𝟙 P.X ⊗ Q.actLeft) ⊗ 𝟙 T.X)) ≫ (α_ P.X  …
          slice_lhs 2 3 => rw [associator_naturality]
          -- ⊢ ((α_ P.X S.X Q.X).hom ⊗ 𝟙 T.X) ≫ ((α_ P.X (S.X ⊗ Q.X) T.X).hom ≫ (𝟙 P.X ⊗ Q. …
          slice_lhs 3 4 => rw [← id_tensor_comp, middle_assoc, id_tensor_comp]
          -- ⊢ ((α_ P.X S.X Q.X).hom ⊗ 𝟙 T.X) ≫ (α_ P.X (S.X ⊗ Q.X) T.X).hom ≫ (𝟙 P.X ⊗ (α_ …
          slice_rhs 4 6 => rw [Iso.inv_hom_id_assoc]
          -- ⊢ ((α_ P.X S.X Q.X).hom ⊗ 𝟙 T.X) ≫ (α_ P.X (S.X ⊗ Q.X) T.X).hom ≫ (𝟙 P.X ⊗ (α_ …
          slice_rhs 3 4 => rw [← id_tensor_comp]
          -- ⊢ ((α_ P.X S.X Q.X).hom ⊗ 𝟙 T.X) ≫ (α_ P.X (S.X ⊗ Q.X) T.X).hom ≫ (𝟙 P.X ⊗ (α_ …
          coherence))
          -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.act_right Bimod.TensorBimod.actRight

theorem π_tensor_id_actRight :
    (coequalizer.π _ _ ⊗ 𝟙 T.X) ≫ actRight P Q =
      (α_ _ _ _).hom ≫ (𝟙 P.X ⊗ Q.actRight) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorRight _)]
  -- ⊢ ((α_ P.X Q.X T.X).hom ≫ (𝟙 P.X ⊗ Q.actRight)) ≫ coequalizer.π (P.actRight ⊗  …
  simp only [Category.assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.π_tensor_id_act_right Bimod.TensorBimod.π_tensor_id_actRight

theorem actRight_one' : (𝟙 _ ⊗ T.one) ≫ actRight P Q = (ρ_ _).hom := by
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight (𝟙_ C)).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q. …
  dsimp [X]
  -- ⊢ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actLe …
  -- porting note: had to replace `rw` by `erw`
  slice_lhs 1 2 => erw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  -- ⊢ ((𝟙 (P.X ⊗ Q.X) ⊗ T.one) ≫ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X  …
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  -- ⊢ (𝟙 (P.X ⊗ Q.X) ⊗ T.one) ≫ (α_ P.X Q.X T.X).hom ≫ (𝟙 P.X ⊗ Q.actRight) ≫ coeq …
  slice_lhs 1 2 => rw [← MonoidalCategory.tensor_id, associator_naturality]
  -- ⊢ (((α_ P.X Q.X (𝟙_ C)).hom ≫ (𝟙 P.X ⊗ 𝟙 Q.X ⊗ T.one)) ≫ (𝟙 P.X ⊗ Q.actRight)) …
  slice_lhs 2 3 => rw [← id_tensor_comp, actRight_one]
  -- ⊢ (α_ P.X Q.X (𝟙_ C)).hom ≫ (𝟙 P.X ⊗ (ρ_ Q.X).hom) ≫ coequalizer.π (P.actRight …
  slice_rhs 1 2 => rw [rightUnitor_naturality]
  -- ⊢ (α_ P.X Q.X (𝟙_ C)).hom ≫ (𝟙 P.X ⊗ (ρ_ Q.X).hom) ≫ coequalizer.π (P.actRight …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.act_right_one' Bimod.TensorBimod.actRight_one'

theorem right_assoc' :
    (𝟙 _ ⊗ T.mul) ≫ actRight P Q =
      (α_ _ T.X T.X).inv ≫ (actRight P Q ⊗ 𝟙 T.X) ≫ actRight P Q := by
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight (T.X ⊗ T.X)).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S …
  dsimp [X]
  -- ⊢ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actLe …
  -- porting note: had to replace some `rw` by `erw`
  slice_lhs 1 2 => erw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  -- ⊢ ((𝟙 (P.X ⊗ Q.X) ⊗ T.mul) ≫ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X  …
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  -- ⊢ (𝟙 (P.X ⊗ Q.X) ⊗ T.mul) ≫ (α_ P.X Q.X T.X).hom ≫ (𝟙 P.X ⊗ Q.actRight) ≫ coeq …
  slice_lhs 1 2 => rw [← MonoidalCategory.tensor_id, associator_naturality]
  -- ⊢ (((α_ P.X Q.X (T.X ⊗ T.X)).hom ≫ (𝟙 P.X ⊗ 𝟙 Q.X ⊗ T.mul)) ≫ (𝟙 P.X ⊗ Q.actRi …
  slice_lhs 2 3 => rw [← id_tensor_comp, right_assoc, id_tensor_comp, id_tensor_comp]
  -- ⊢ (α_ P.X Q.X (T.X ⊗ T.X)).hom ≫ ((𝟙 P.X ⊗ (α_ Q.X T.X T.X).inv) ≫ (𝟙 P.X ⊗ Q. …
  slice_rhs 1 2 => erw [← MonoidalCategory.tensor_id, associator_inv_naturality]
  -- ⊢ (α_ P.X Q.X (T.X ⊗ T.X)).hom ≫ ((𝟙 P.X ⊗ (α_ Q.X T.X T.X).inv) ≫ (𝟙 P.X ⊗ Q. …
  slice_rhs 2 3 => rw [← comp_tensor_id, π_tensor_id_actRight, comp_tensor_id, comp_tensor_id]
  -- ⊢ (α_ P.X Q.X (T.X ⊗ T.X)).hom ≫ ((𝟙 P.X ⊗ (α_ Q.X T.X T.X).inv) ≫ (𝟙 P.X ⊗ Q. …
  slice_rhs 4 5 => rw [π_tensor_id_actRight]
  -- ⊢ (α_ P.X Q.X (T.X ⊗ T.X)).hom ≫ ((𝟙 P.X ⊗ (α_ Q.X T.X T.X).inv) ≫ (𝟙 P.X ⊗ Q. …
  slice_rhs 3 4 => rw [associator_naturality]
  -- ⊢ (α_ P.X Q.X (T.X ⊗ T.X)).hom ≫ ((𝟙 P.X ⊗ (α_ Q.X T.X T.X).inv) ≫ (𝟙 P.X ⊗ Q. …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.right_assoc' Bimod.TensorBimod.right_assoc'

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem middle_assoc' :
    (actLeft P Q ⊗ 𝟙 T.X) ≫ actRight P Q =
      (α_ R.X _ T.X).hom ≫ (𝟙 R.X ⊗ actRight P Q) ≫ actLeft P Q := by
  refine' (cancel_epi ((tensorLeft _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft R.X ⋙ tensorRight T.X).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ( …
  dsimp [X]
  -- ⊢ ((𝟙 R.X ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X  …
  slice_lhs 1 2 => rw [← comp_tensor_id, id_tensor_π_actLeft, comp_tensor_id, comp_tensor_id]
  -- ⊢ (((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ ((P.actLeft ⊗ 𝟙 Q.X) ⊗ 𝟙 T.X) ≫ (coequaliz …
  slice_lhs 3 4 => rw [π_tensor_id_actRight]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ ((P.actLeft ⊗ 𝟙 Q.X) ⊗ 𝟙 T.X) ≫ (α_ P.X Q.X …
  slice_lhs 2 3 => rw [associator_naturality]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ (((α_ (R.X ⊗ P.X) Q.X T.X).hom ≫ (P.actLeft …
  slice_lhs 3 4 => rw [MonoidalCategory.tensor_id, tensor_id_comp_id_tensor]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ (α_ (R.X ⊗ P.X) Q.X T.X).hom ≫ (P.actLeft ⊗ …
  -- porting note: had to replace `rw` by `erw`
  slice_rhs 1 2 => erw [associator_naturality]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ (α_ (R.X ⊗ P.X) Q.X T.X).hom ≫ (P.actLeft ⊗ …
  slice_rhs 2 3 => rw [← id_tensor_comp, π_tensor_id_actRight, id_tensor_comp, id_tensor_comp]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ (α_ (R.X ⊗ P.X) Q.X T.X).hom ≫ (P.actLeft ⊗ …
  slice_rhs 4 5 => rw [id_tensor_π_actLeft]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ (α_ (R.X ⊗ P.X) Q.X T.X).hom ≫ (P.actLeft ⊗ …
  slice_rhs 3 4 => rw [associator_inv_naturality]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ (α_ (R.X ⊗ P.X) Q.X T.X).hom ≫ (P.actLeft ⊗ …
  slice_rhs 4 5 => rw [MonoidalCategory.tensor_id, id_tensor_comp_tensor_id]
  -- ⊢ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 T.X) ≫ (α_ (R.X ⊗ P.X) Q.X T.X).hom ≫ (P.actLeft ⊗ …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod.middle_assoc' Bimod.TensorBimod.middle_assoc'

end

end TensorBimod

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Tensor product of two bimodule objects as a bimodule object. -/
@[simps]
noncomputable def tensorBimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) : Bimod X Z where
  X := TensorBimod.X M N
  actLeft := TensorBimod.actLeft M N
  actRight := TensorBimod.actRight M N
  one_actLeft := TensorBimod.one_act_left' M N
  actRight_one := TensorBimod.actRight_one' M N
  left_assoc := TensorBimod.left_assoc' M N
  right_assoc := TensorBimod.right_assoc' M N
  middle_assoc := TensorBimod.middle_assoc' M N
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_Bimod Bimod.tensorBimod

/-- Tensor product of two morphisms of bimodule objects. -/
@[simps]
noncomputable def tensorHom {X Y Z : Mon_ C} {M₁ M₂ : Bimod X Y} {N₁ N₂ : Bimod Y Z} (f : M₁ ⟶ M₂)
    (g : N₁ ⟶ N₂) : M₁.tensorBimod N₁ ⟶ M₂.tensorBimod N₂ where
  hom :=
    colimMap
      (parallelPairHom _ _ _ _ ((f.hom ⊗ 𝟙 Y.X) ⊗ g.hom) (f.hom ⊗ g.hom)
        (by
          rw [← tensor_comp, ← tensor_comp, Hom.right_act_hom, Category.id_comp, Category.comp_id])
          -- 🎉 no goals
        (by
          slice_lhs 2 3 => rw [← tensor_comp, Hom.left_act_hom, Category.id_comp]
          -- ⊢ (α_ M₁.X Y.X N₁.X).hom ≫ (f.hom ⊗ (𝟙 Y.X ⊗ g.hom) ≫ N₂.actLeft) = ((f.hom ⊗  …
          slice_rhs 1 2 => rw [associator_naturality]
          -- ⊢ (α_ M₁.X Y.X N₁.X).hom ≫ (f.hom ⊗ (𝟙 Y.X ⊗ g.hom) ≫ N₂.actLeft) = ((α_ M₁.X  …
          slice_rhs 2 3 => rw [← tensor_comp, Category.comp_id]))
          -- 🎉 no goals
  left_act_hom := by
    refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
    -- ⊢ (tensorLeft X.X).map (coequalizer.π (M₁.actRight ⊗ 𝟙 N₁.X) ((α_ M₁.X Y.X N₁. …
    dsimp
    -- ⊢ (𝟙 X.X ⊗ coequalizer.π (M₁.actRight ⊗ 𝟙 N₁.X) ((α_ M₁.X Y.X N₁.X).hom ≫ (𝟙 M …
    slice_lhs 1 2 => rw [TensorBimod.id_tensor_π_actLeft]
    -- ⊢ ((α_ X.X M₁.X N₁.X).inv ≫ (M₁.actLeft ⊗ 𝟙 N₁.X) ≫ coequalizer.π (M₁.actRight …
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    -- ⊢ (α_ X.X M₁.X N₁.X).inv ≫ (M₁.actLeft ⊗ 𝟙 N₁.X) ≫ (f.hom ⊗ g.hom) ≫ colimit.ι …
    slice_lhs 2 3 => rw [← tensor_comp, Hom.left_act_hom, Category.id_comp]
    -- ⊢ (α_ X.X M₁.X N₁.X).inv ≫ ((𝟙 X.X ⊗ f.hom) ≫ M₂.actLeft ⊗ g.hom) ≫ colimit.ι  …
    slice_rhs 1 2 => rw [← id_tensor_comp, ι_colimMap, parallelPairHom_app_one, id_tensor_comp]
    -- ⊢ (α_ X.X M₁.X N₁.X).inv ≫ ((𝟙 X.X ⊗ f.hom) ≫ M₂.actLeft ⊗ g.hom) ≫ colimit.ι  …
    slice_rhs 2 3 => rw [TensorBimod.id_tensor_π_actLeft]
    -- ⊢ (α_ X.X M₁.X N₁.X).inv ≫ ((𝟙 X.X ⊗ f.hom) ≫ M₂.actLeft ⊗ g.hom) ≫ colimit.ι  …
    slice_rhs 1 2 => rw [associator_inv_naturality]
    -- ⊢ (α_ X.X M₁.X N₁.X).inv ≫ ((𝟙 X.X ⊗ f.hom) ≫ M₂.actLeft ⊗ g.hom) ≫ colimit.ι  …
    slice_rhs 2 3 => rw [← tensor_comp, Category.comp_id]
    -- 🎉 no goals
  right_act_hom := by
    refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
    -- ⊢ (tensorRight Z.X).map (coequalizer.π (M₁.actRight ⊗ 𝟙 N₁.X) ((α_ M₁.X Y.X N₁ …
    dsimp
    -- ⊢ (coequalizer.π (M₁.actRight ⊗ 𝟙 N₁.X) ((α_ M₁.X Y.X N₁.X).hom ≫ (𝟙 M₁.X ⊗ N₁ …
    slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
    -- ⊢ ((α_ M₁.X N₁.X Z.X).hom ≫ (𝟙 M₁.X ⊗ N₁.actRight) ≫ coequalizer.π (M₁.actRigh …
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    -- ⊢ (α_ M₁.X N₁.X Z.X).hom ≫ (𝟙 M₁.X ⊗ N₁.actRight) ≫ (f.hom ⊗ g.hom) ≫ colimit. …
    slice_lhs 2 3 => rw [← tensor_comp, Category.id_comp, Hom.right_act_hom]
    -- ⊢ (α_ M₁.X N₁.X Z.X).hom ≫ (f.hom ⊗ (g.hom ⊗ 𝟙 Z.X) ≫ N₂.actRight) ≫ colimit.ι …
    slice_rhs 1 2 => rw [← comp_tensor_id, ι_colimMap, parallelPairHom_app_one, comp_tensor_id]
    -- ⊢ (α_ M₁.X N₁.X Z.X).hom ≫ (f.hom ⊗ (g.hom ⊗ 𝟙 Z.X) ≫ N₂.actRight) ≫ colimit.ι …
    slice_rhs 2 3 => rw [TensorBimod.π_tensor_id_actRight]
    -- ⊢ (α_ M₁.X N₁.X Z.X).hom ≫ (f.hom ⊗ (g.hom ⊗ 𝟙 Z.X) ≫ N₂.actRight) ≫ colimit.ι …
    slice_rhs 1 2 => rw [associator_naturality]
    -- ⊢ (α_ M₁.X N₁.X Z.X).hom ≫ (f.hom ⊗ (g.hom ⊗ 𝟙 Z.X) ≫ N₂.actRight) ≫ colimit.ι …
    slice_rhs 2 3 => rw [← tensor_comp, Category.comp_id]
    -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_hom Bimod.tensorHom

theorem tensor_id {X Y Z : Mon_ C} {M : Bimod X Y} {N : Bimod Y Z} :
    tensorHom (𝟙 M) (𝟙 N) = 𝟙 (M.tensorBimod N) := by
  ext
  -- ⊢ (tensorHom (𝟙 M) (𝟙 N)).hom = (𝟙 (tensorBimod M N)).hom
  apply Limits.coequalizer.hom_ext
  -- ⊢ coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X Y.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLef …
  simp only [id_hom', MonoidalCategory.tensor_id, tensorHom_hom, ι_colimMap,
    parallelPairHom_app_one]
  dsimp; dsimp only [TensorBimod.X]
  -- ⊢ 𝟙 (M.X ⊗ N.X) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N.X) ((α_ M.X Y.X N. …
         -- ⊢ 𝟙 (M.X ⊗ N.X) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N.X) ((α_ M.X Y.X N. …
  simp only [Category.id_comp, Category.comp_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_id Bimod.tensor_id

theorem tensor_comp {X Y Z : Mon_ C} {M₁ M₂ M₃ : Bimod X Y} {N₁ N₂ N₃ : Bimod Y Z} (f₁ : M₁ ⟶ M₂)
    (f₂ : M₂ ⟶ M₃) (g₁ : N₁ ⟶ N₂) (g₂ : N₂ ⟶ N₃) :
    tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂) = tensorHom f₁ g₁ ≫ tensorHom f₂ g₂ := by
  ext
  -- ⊢ (tensorHom (f₁ ≫ f₂) (g₁ ≫ g₂)).hom = (tensorHom f₁ g₁ ≫ tensorHom f₂ g₂).hom
  apply Limits.coequalizer.hom_ext
  -- ⊢ coequalizer.π (M₁.actRight ⊗ 𝟙 N₁.X) ((α_ M₁.X Y.X N₁.X).hom ≫ (𝟙 M₁.X ⊗ N₁. …
  simp only [comp_hom', MonoidalCategory.tensor_comp, tensorHom_hom,
    ι_colimMap, parallelPairHom_app_one, Category.assoc, ι_colimMap_assoc]
set_option linter.uppercaseLean3 false in
#align Bimod.tensor_comp Bimod.tensor_comp

end

namespace AssociatorBimod

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

variable {R S T U : Mon_ C} (P : Bimod R S) (Q : Bimod S T) (L : Bimod T U)

/-- An auxiliary morphism for the definition of the underlying morphism of the forward component of
the associator isomorphism. -/
noncomputable def homAux : (P.tensorBimod Q).X ⊗ L.X ⟶ (P.tensorBimod (Q.tensorBimod L)).X :=
  (PreservesCoequalizer.iso (tensorRight L.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).hom ≫ (𝟙 P.X ⊗ coequalizer.π _ _) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        -- ⊢ ((P.actRight ⊗ 𝟙 Q.X) ⊗ 𝟙 L.X) ≫ (α_ P.X Q.X L.X).hom ≫ (𝟙 P.X ⊗ coequalizer …
               -- ⊢ ((P.actRight ⊗ 𝟙 Q.X) ⊗ 𝟙 L.X) ≫ (α_ P.X Q.X L.X).hom ≫ (𝟙 P.X ⊗ coequalizer …
        slice_lhs 1 2 => rw [associator_naturality]
        -- ⊢ (((α_ (P.X ⊗ S.X) Q.X L.X).hom ≫ (P.actRight ⊗ 𝟙 Q.X ⊗ 𝟙 L.X)) ≫ (𝟙 P.X ⊗ co …
        slice_lhs 2 3 =>
          rw [MonoidalCategory.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
        slice_lhs 3 4 => rw [coequalizer.condition]
        -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).hom ≫ (𝟙 (P.X ⊗ S.X) ⊗ coequalizer.π (Q.actRight ⊗  …
        slice_lhs 2 3 => rw [← MonoidalCategory.tensor_id, associator_naturality]
        -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).hom ≫ (((α_ P.X S.X (Q.X ⊗ L.X)).hom ≫ (𝟙 P.X ⊗ 𝟙 S …
        slice_lhs 3 4 => rw [← id_tensor_comp, TensorBimod.id_tensor_π_actLeft, id_tensor_comp]
        -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).hom ≫ (α_ P.X S.X (Q.X ⊗ L.X)).hom ≫ ((𝟙 P.X ⊗ (α_  …
        slice_rhs 1 1 => rw [comp_tensor_id]
        -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).hom ≫ (α_ P.X S.X (Q.X ⊗ L.X)).hom ≫ ((𝟙 P.X ⊗ (α_  …
        slice_rhs 2 3 => rw [associator_naturality]
        -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).hom ≫ (α_ P.X S.X (Q.X ⊗ L.X)).hom ≫ ((𝟙 P.X ⊗ (α_  …
        slice_rhs 3 4 => rw [← id_tensor_comp]
        -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).hom ≫ (α_ P.X S.X (Q.X ⊗ L.X)).hom ≫ ((𝟙 P.X ⊗ (α_  …
        coherence)
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.hom_aux Bimod.AssociatorBimod.homAux

/-- The underlying morphism of the forward component of the associator isomorphism. -/
noncomputable def hom :
    ((P.tensorBimod Q).tensorBimod L).X ⟶ (P.tensorBimod (Q.tensorBimod L)).X :=
  coequalizer.desc (homAux P Q L)
    (by
      dsimp [homAux]
      -- ⊢ (TensorBimod.actRight P Q ⊗ 𝟙 L.X) ≫ (PreservesCoequalizer.iso (tensorRight  …
      refine' (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 _
      -- ⊢ (tensorRight T.X ⋙ tensorRight L.X).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X)  …
      dsimp [TensorBimod.X]
      -- ⊢ ((coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actL …
      slice_lhs 1 2 =>
        rw [← comp_tensor_id, TensorBimod.π_tensor_id_actRight, comp_tensor_id, comp_tensor_id]
      slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      -- ⊢ ((α_ P.X Q.X T.X).hom ⊗ 𝟙 L.X) ≫ ((𝟙 P.X ⊗ Q.actRight) ⊗ 𝟙 L.X) ≫ (α_ P.X Q. …
      slice_lhs 2 3 => rw [associator_naturality]
      -- ⊢ ((α_ P.X Q.X T.X).hom ⊗ 𝟙 L.X) ≫ (((α_ P.X (Q.X ⊗ T.X) L.X).hom ≫ (𝟙 P.X ⊗ Q …
      slice_lhs 3 4 => rw [← id_tensor_comp, coequalizer.condition, id_tensor_comp, id_tensor_comp]
      -- ⊢ ((α_ P.X Q.X T.X).hom ⊗ 𝟙 L.X) ≫ (α_ P.X (Q.X ⊗ T.X) L.X).hom ≫ (((𝟙 P.X ⊗ ( …
      slice_rhs 1 2 => rw [associator_naturality]
      -- ⊢ ((α_ P.X Q.X T.X).hom ⊗ 𝟙 L.X) ≫ (α_ P.X (Q.X ⊗ T.X) L.X).hom ≫ (((𝟙 P.X ⊗ ( …
      slice_rhs 2 3 =>
        rw [MonoidalCategory.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
      slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      -- ⊢ ((α_ P.X Q.X T.X).hom ⊗ 𝟙 L.X) ≫ (α_ P.X (Q.X ⊗ T.X) L.X).hom ≫ (((𝟙 P.X ⊗ ( …
      slice_rhs 2 3 => rw [← MonoidalCategory.tensor_id, associator_naturality]
      -- ⊢ ((α_ P.X Q.X T.X).hom ⊗ 𝟙 L.X) ≫ (α_ P.X (Q.X ⊗ T.X) L.X).hom ≫ (((𝟙 P.X ⊗ ( …
      coherence)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.hom Bimod.AssociatorBimod.hom

theorem hom_left_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actLeft ≫ hom P Q L =
      (𝟙 R.X ⊗ hom P Q L) ≫ (P.tensorBimod (Q.tensorBimod L)).actLeft := by
  dsimp; dsimp [hom, homAux]
  -- ⊢ TensorBimod.actLeft (tensorBimod P Q) L ≫ hom P Q L = (𝟙 R.X ⊗ hom P Q L) ≫  …
         -- ⊢ TensorBimod.actLeft (tensorBimod P Q) L ≫ coequalizer.desc ((PreservesCoequa …
  refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft R.X).map (coequalizer.π ((tensorBimod P Q).actRight ⊗ 𝟙 L.X) ((α …
  rw [tensorLeft_map]
  -- ⊢ (𝟙 R.X ⊗ coequalizer.π ((tensorBimod P Q).actRight ⊗ 𝟙 L.X) ((α_ (tensorBimo …
  slice_lhs 1 2 => rw [TensorBimod.id_tensor_π_actLeft]
  -- ⊢ ((α_ R.X (tensorBimod P Q).X L.X).inv ≫ ((tensorBimod P Q).actLeft ⊗ 𝟙 L.X)  …
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (α_ R.X (tensorBimod P Q).X L.X).inv ≫ ((tensorBimod P Q).actLeft ⊗ 𝟙 L.X) ≫ …
  slice_rhs 1 2 => rw [← id_tensor_comp, coequalizer.π_desc, id_tensor_comp]
  -- ⊢ (α_ R.X (tensorBimod P Q).X L.X).inv ≫ ((tensorBimod P Q).actLeft ⊗ 𝟙 L.X) ≫ …
  refine' (cancel_epi ((tensorRight _ ⋙ tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight L.X ⋙ tensorLeft R.X).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ( …
  dsimp; dsimp [TensorBimod.X]
  -- ⊢ (𝟙 R.X ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ …
         -- ⊢ (𝟙 R.X ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ …
  slice_lhs 1 2 => rw [associator_inv_naturality]
  -- ⊢ ((((α_ R.X (P.X ⊗ Q.X) L.X).inv ≫ ((𝟙 R.X ⊗ coequalizer.π (P.actRight ⊗ 𝟙 Q. …
  slice_lhs 2 3 =>
    rw [← comp_tensor_id, TensorBimod.id_tensor_π_actLeft, comp_tensor_id, comp_tensor_id]
  slice_lhs 4 6 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ (α_ R.X (P.X ⊗ Q.X) L.X).inv ≫ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 L.X) ≫ ((P.actLeft  …
  slice_lhs 3 4 => rw [associator_naturality]
  -- ⊢ (α_ R.X (P.X ⊗ Q.X) L.X).inv ≫ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 L.X) ≫ (((α_ (R.X ⊗ …
  slice_lhs 4 5 => rw [MonoidalCategory.tensor_id, tensor_id_comp_id_tensor]
  -- ⊢ (α_ R.X (P.X ⊗ Q.X) L.X).inv ≫ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 L.X) ≫ (α_ (R.X ⊗ P …
  slice_rhs 1 3 =>
    rw [← id_tensor_comp, ← id_tensor_comp, π_tensor_id_preserves_coequalizer_inv_desc,
      id_tensor_comp, id_tensor_comp]
  slice_rhs 3 4 => erw [TensorBimod.id_tensor_π_actLeft P (Q.tensorBimod L)]
  -- ⊢ (α_ R.X (P.X ⊗ Q.X) L.X).inv ≫ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 L.X) ≫ (α_ (R.X ⊗ P …
  slice_rhs 2 3 => erw [associator_inv_naturality]
  -- ⊢ (α_ R.X (P.X ⊗ Q.X) L.X).inv ≫ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 L.X) ≫ (α_ (R.X ⊗ P …
  slice_rhs 3 4 => erw [MonoidalCategory.tensor_id, id_tensor_comp_tensor_id]
  -- ⊢ (α_ R.X (P.X ⊗ Q.X) L.X).inv ≫ ((α_ R.X P.X Q.X).inv ⊗ 𝟙 L.X) ≫ (α_ (R.X ⊗ P …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.hom_left_act_hom' Bimod.AssociatorBimod.hom_left_act_hom'

theorem hom_right_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actRight ≫ hom P Q L =
      (hom P Q L ⊗ 𝟙 U.X) ≫ (P.tensorBimod (Q.tensorBimod L)).actRight := by
  dsimp; dsimp [hom, homAux]
  -- ⊢ TensorBimod.actRight (tensorBimod P Q) L ≫ hom P Q L = (hom P Q L ⊗ 𝟙 U.X) ≫ …
         -- ⊢ TensorBimod.actRight (tensorBimod P Q) L ≫ coequalizer.desc ((PreservesCoequ …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight U.X).map (coequalizer.π ((tensorBimod P Q).actRight ⊗ 𝟙 L.X) (( …
  rw [tensorRight_map]
  -- ⊢ (coequalizer.π ((tensorBimod P Q).actRight ⊗ 𝟙 L.X) ((α_ (tensorBimod P Q).X …
  slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
  -- ⊢ ((α_ (tensorBimod P Q).X L.X U.X).hom ≫ (𝟙 (tensorBimod P Q).X ⊗ L.actRight) …
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (α_ (tensorBimod P Q).X L.X U.X).hom ≫ (𝟙 (tensorBimod P Q).X ⊗ L.actRight)  …
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc, comp_tensor_id]
  -- ⊢ (α_ (tensorBimod P Q).X L.X U.X).hom ≫ (𝟙 (tensorBimod P Q).X ⊗ L.actRight)  …
  refine' (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight L.X ⋙ tensorRight U.X).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X)  …
  dsimp; dsimp [TensorBimod.X]
  -- ⊢ ((coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actL …
         -- ⊢ ((coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actL …
  slice_lhs 1 2 => rw [associator_naturality]
  -- ⊢ ((((α_ (P.X ⊗ Q.X) L.X U.X).hom ≫ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P …
  slice_lhs 2 3 =>
    rw [MonoidalCategory.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ (α_ (P.X ⊗ Q.X) L.X U.X).hom ≫ (𝟙 (P.X ⊗ Q.X) ⊗ L.actRight) ≫ (α_ P.X Q.X L. …
  slice_lhs 2 3 => rw [← MonoidalCategory.tensor_id, associator_naturality]
  -- ⊢ (α_ (P.X ⊗ Q.X) L.X U.X).hom ≫ (((α_ P.X Q.X (L.X ⊗ U.X)).hom ≫ (𝟙 P.X ⊗ 𝟙 Q …
  slice_rhs 1 3 =>
    rw [← comp_tensor_id, ← comp_tensor_id, π_tensor_id_preserves_coequalizer_inv_desc,
      comp_tensor_id, comp_tensor_id]
  slice_rhs 3 4 => erw [TensorBimod.π_tensor_id_actRight P (Q.tensorBimod L)]
  -- ⊢ (α_ (P.X ⊗ Q.X) L.X U.X).hom ≫ (((α_ P.X Q.X (L.X ⊗ U.X)).hom ≫ (𝟙 P.X ⊗ 𝟙 Q …
  slice_rhs 2 3 => erw [associator_naturality]
  -- ⊢ (α_ (P.X ⊗ Q.X) L.X U.X).hom ≫ (((α_ P.X Q.X (L.X ⊗ U.X)).hom ≫ (𝟙 P.X ⊗ 𝟙 Q …
  dsimp
  -- ⊢ (α_ (P.X ⊗ Q.X) L.X U.X).hom ≫ (((α_ P.X Q.X (L.X ⊗ U.X)).hom ≫ (𝟙 P.X ⊗ 𝟙 Q …
  slice_rhs 3 4 =>
    rw [← id_tensor_comp, TensorBimod.π_tensor_id_actRight, id_tensor_comp, id_tensor_comp]
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.hom_right_act_hom' Bimod.AssociatorBimod.hom_right_act_hom'

/-- An auxiliary morphism for the definition of the underlying morphism of the inverse component of
the associator isomorphism. -/
noncomputable def invAux : P.X ⊗ (Q.tensorBimod L).X ⟶ ((P.tensorBimod Q).tensorBimod L).X :=
  (PreservesCoequalizer.iso (tensorLeft P.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).inv ≫ (coequalizer.π _ _ ⊗ 𝟙 L.X) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        -- ⊢ (𝟙 P.X ⊗ Q.actRight ⊗ 𝟙 L.X) ≫ (α_ P.X Q.X L.X).inv ≫ (coequalizer.π (P.actR …
               -- ⊢ (𝟙 P.X ⊗ Q.actRight ⊗ 𝟙 L.X) ≫ (α_ P.X Q.X L.X).inv ≫ (coequalizer.π (P.actR …
        slice_lhs 1 2 => rw [associator_inv_naturality]
        -- ⊢ (((α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((𝟙 P.X ⊗ Q.actRight) ⊗ 𝟙 L.X)) ≫ (coequali …
        rw [← Iso.inv_hom_id_assoc (α_ _ _ _) (𝟙 P.X ⊗ Q.actRight), comp_tensor_id]
        -- ⊢ (((α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((α_ P.X Q.X T.X).inv ⊗ 𝟙 L.X) ≫ ((α_ P.X Q …
        slice_lhs 3 4 =>
          rw [← comp_tensor_id, Category.assoc, ← TensorBimod.π_tensor_id_actRight,
            comp_tensor_id]
        slice_lhs 4 5 => rw [coequalizer.condition]
        -- ⊢ (α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((α_ P.X Q.X T.X).inv ⊗ 𝟙 L.X) ≫ ((coequalize …
        slice_lhs 3 4 => rw [associator_naturality]
        -- ⊢ (α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((α_ P.X Q.X T.X).inv ⊗ 𝟙 L.X) ≫ (((α_ (P.X ⊗ …
        slice_lhs 4 5 => rw [MonoidalCategory.tensor_id, tensor_id_comp_id_tensor]
        -- ⊢ (α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((α_ P.X Q.X T.X).inv ⊗ 𝟙 L.X) ≫ (α_ (P.X ⊗ Q …
        slice_rhs 1 2 => rw [id_tensor_comp]
        -- ⊢ (α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((α_ P.X Q.X T.X).inv ⊗ 𝟙 L.X) ≫ (α_ (P.X ⊗ Q …
        slice_rhs 2 3 => rw [associator_inv_naturality]
        -- ⊢ (α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((α_ P.X Q.X T.X).inv ⊗ 𝟙 L.X) ≫ (α_ (P.X ⊗ Q …
        slice_rhs 3 4 => rw [MonoidalCategory.tensor_id, id_tensor_comp_tensor_id]
        -- ⊢ (α_ P.X (Q.X ⊗ T.X) L.X).inv ≫ ((α_ P.X Q.X T.X).inv ⊗ 𝟙 L.X) ≫ (α_ (P.X ⊗ Q …
        coherence)
        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.inv_aux Bimod.AssociatorBimod.invAux

/-- The underlying morphism of the inverse component of the associator isomorphism. -/
noncomputable def inv :
    (P.tensorBimod (Q.tensorBimod L)).X ⟶ ((P.tensorBimod Q).tensorBimod L).X :=
  coequalizer.desc (invAux P Q L)
    (by
      dsimp [invAux]
      -- ⊢ (P.actRight ⊗ 𝟙 (TensorBimod.X Q L)) ≫ (PreservesCoequalizer.iso (tensorLeft …
      refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
      -- ⊢ (tensorLeft (P.X ⊗ S.X)).map (coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X T. …
      dsimp [TensorBimod.X]
      -- ⊢ (𝟙 (P.X ⊗ S.X) ⊗ coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫  …
      slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
      -- ⊢ (((P.actRight ⊗ 𝟙 (Q.X ⊗ L.X)) ≫ (𝟙 P.X ⊗ coequalizer.π (Q.actRight ⊗ 𝟙 L.X) …
      slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      -- ⊢ (P.actRight ⊗ 𝟙 (Q.X ⊗ L.X)) ≫ (α_ P.X Q.X L.X).inv ≫ (coequalizer.π (P.actR …
      slice_lhs 1 2 => rw [← MonoidalCategory.tensor_id, associator_inv_naturality]
      -- ⊢ (((α_ (P.X ⊗ S.X) Q.X L.X).inv ≫ ((P.actRight ⊗ 𝟙 Q.X) ⊗ 𝟙 L.X)) ≫ (coequali …
      slice_lhs 2 3 => rw [← comp_tensor_id, coequalizer.condition, comp_tensor_id, comp_tensor_id]
      -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).inv ≫ ((((α_ P.X S.X Q.X).hom ⊗ 𝟙 L.X) ≫ ((𝟙 P.X ⊗  …
      slice_rhs 1 2 => rw [← MonoidalCategory.tensor_id, associator_naturality]
      -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).inv ≫ ((((α_ P.X S.X Q.X).hom ⊗ 𝟙 L.X) ≫ ((𝟙 P.X ⊗  …
      slice_rhs 2 3 =>
        rw [← id_tensor_comp, TensorBimod.id_tensor_π_actLeft, id_tensor_comp, id_tensor_comp]
      slice_rhs 4 6 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).inv ≫ ((((α_ P.X S.X Q.X).hom ⊗ 𝟙 L.X) ≫ ((𝟙 P.X ⊗  …
      slice_rhs 3 4 => rw [associator_inv_naturality]
      -- ⊢ (α_ (P.X ⊗ S.X) Q.X L.X).inv ≫ ((((α_ P.X S.X Q.X).hom ⊗ 𝟙 L.X) ≫ ((𝟙 P.X ⊗  …
      coherence)
      -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.inv Bimod.AssociatorBimod.inv

theorem hom_inv_id : hom P Q L ≫ inv P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  -- ⊢ coequalizer.desc ((PreservesCoequalizer.iso (tensorRight L.X) (P.actRight ⊗  …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π ((tensorBimod P Q).actRight ⊗ 𝟙 L.X) ((α_ (tensorBimod P Q).X  …
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ ((PreservesCoequalizer.iso (tensorRight L.X) (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight L.X).map (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X). …
  rw [tensorRight_map]
  -- ⊢ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actLe …
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ ((α_ P.X Q.X L.X).hom ≫ (𝟙 P.X ⊗ coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X …
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (α_ P.X Q.X L.X).hom ≫ (𝟙 P.X ⊗ coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X  …
  slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  -- ⊢ (α_ P.X Q.X L.X).hom ≫ (α_ P.X Q.X L.X).inv ≫ (coequalizer.π (P.actRight ⊗ 𝟙 …
  slice_lhs 1 3 => rw [Iso.hom_inv_id_assoc]
  -- ⊢ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actLe …
  dsimp only [TensorBimod.X]
  -- ⊢ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X).hom ≫ (𝟙 P.X ⊗ Q.actLe …
  slice_rhs 2 3 => rw [Category.comp_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.hom_inv_id Bimod.AssociatorBimod.hom_inv_id

theorem inv_hom_id : inv P Q L ≫ hom P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  -- ⊢ coequalizer.desc ((PreservesCoequalizer.iso (tensorLeft P.X) (Q.actRight ⊗ 𝟙 …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π (P.actRight ⊗ 𝟙 (tensorBimod Q L).X) ((α_ P.X S.X (tensorBimod …
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ ((PreservesCoequalizer.iso (tensorLeft P.X) (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X T. …
  refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft P.X).map (coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).h …
  rw [tensorLeft_map]
  -- ⊢ (𝟙 P.X ⊗ coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫ (𝟙 Q.X ⊗ …
  slice_lhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  -- ⊢ ((α_ P.X Q.X L.X).inv ≫ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X …
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (α_ P.X Q.X L.X).inv ≫ (coequalizer.π (P.actRight ⊗ 𝟙 Q.X) ((α_ P.X S.X Q.X) …
  slice_lhs 2 4 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ (α_ P.X Q.X L.X).inv ≫ (α_ P.X Q.X L.X).hom ≫ (𝟙 P.X ⊗ coequalizer.π (Q.actR …
  slice_lhs 1 3 => rw [Iso.inv_hom_id_assoc]
  -- ⊢ (𝟙 P.X ⊗ coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫ (𝟙 Q.X ⊗ …
  dsimp only [TensorBimod.X]
  -- ⊢ (𝟙 P.X ⊗ coequalizer.π (Q.actRight ⊗ 𝟙 L.X) ((α_ Q.X T.X L.X).hom ≫ (𝟙 Q.X ⊗ …
  slice_rhs 2 3 => rw [Category.comp_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod.inv_hom_id Bimod.AssociatorBimod.inv_hom_id

end AssociatorBimod

namespace LeftUnitorBimod

variable {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the left unitor isomorphism. -/
noncomputable def hom : TensorBimod.X (regular R) P ⟶ P.X :=
  coequalizer.desc P.actLeft (by dsimp; rw [Category.assoc, left_assoc])
                                 -- ⊢ (R.mul ⊗ 𝟙 P.X) ≫ P.actLeft = ((α_ R.X R.X P.X).hom ≫ (𝟙 R.X ⊗ P.actLeft)) ≫ …
                                        -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.left_unitor_Bimod.hom Bimod.LeftUnitorBimod.hom

/-- The underlying morphism of the inverse component of the left unitor isomorphism. -/
noncomputable def inv : P.X ⟶ TensorBimod.X (regular R) P :=
  (λ_ P.X).inv ≫ (R.one ⊗ 𝟙 _) ≫ coequalizer.π _ _
set_option linter.uppercaseLean3 false in
#align Bimod.left_unitor_Bimod.inv Bimod.LeftUnitorBimod.inv

theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, TensorBimod.X]
  -- ⊢ coequalizer.desc P.actLeft (_ : ((regular R).actRight ⊗ 𝟙 P.X) ≫ P.actLeft = …
  ext; dsimp
  -- ⊢ coequalizer.π ((regular R).actRight ⊗ 𝟙 P.X) ((α_ (regular R).X R.X P.X).hom …
       -- ⊢ coequalizer.π (R.mul ⊗ 𝟙 P.X) ((α_ R.X R.X P.X).hom ≫ (𝟙 R.X ⊗ P.actLeft)) ≫ …
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ ((P.actLeft ≫ (λ_ P.X).inv) ≫ (R.one ⊗ 𝟙 P.X)) ≫ coequalizer.π (R.mul ⊗ 𝟙 P. …
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  -- ⊢ (((λ_ (R.X ⊗ P.X)).inv ≫ (𝟙 tensorUnit' ⊗ P.actLeft)) ≫ (R.one ⊗ 𝟙 P.X)) ≫ c …
  slice_lhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  -- ⊢ (λ_ (R.X ⊗ P.X)).inv ≫ ((R.one ⊗ 𝟙 (R.X ⊗ P.X)) ≫ (𝟙 R.X ⊗ P.actLeft)) ≫ coe …
  slice_lhs 3 3 => rw [← Iso.inv_hom_id_assoc (α_ R.X R.X P.X) (𝟙 R.X ⊗ P.actLeft)]
  -- ⊢ (λ_ (R.X ⊗ P.X)).inv ≫ (R.one ⊗ 𝟙 (R.X ⊗ P.X)) ≫ ((α_ R.X R.X P.X).inv ≫ (α_ …
  slice_lhs 4 6 => rw [← Category.assoc, ← coequalizer.condition]
  -- ⊢ (λ_ (R.X ⊗ P.X)).inv ≫ (R.one ⊗ 𝟙 (R.X ⊗ P.X)) ≫ (α_ R.X R.X P.X).inv ≫ (R.m …
  slice_lhs 2 3 => rw [← MonoidalCategory.tensor_id, associator_inv_naturality]
  -- ⊢ (λ_ (R.X ⊗ P.X)).inv ≫ (((α_ tensorUnit' R.X P.X).inv ≫ ((R.one ⊗ 𝟙 R.X) ⊗ 𝟙 …
  slice_lhs 3 4 => rw [← comp_tensor_id, Mon_.one_mul]
  -- ⊢ (λ_ (R.X ⊗ P.X)).inv ≫ (α_ tensorUnit' R.X P.X).inv ≫ ((λ_ R.X).hom ⊗ 𝟙 P.X) …
  slice_rhs 1 2 => rw [Category.comp_id]
  -- ⊢ (λ_ (R.X ⊗ P.X)).inv ≫ (α_ tensorUnit' R.X P.X).inv ≫ ((λ_ R.X).hom ⊗ 𝟙 P.X) …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.left_unitor_Bimod.hom_inv_id Bimod.LeftUnitorBimod.hom_inv_id

theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  -- ⊢ ((λ_ P.X).inv ≫ (R.one ⊗ 𝟙 P.X) ≫ coequalizer.π (R.mul ⊗ 𝟙 P.X) ((α_ R.X R.X …
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (λ_ P.X).inv ≫ (R.one ⊗ 𝟙 P.X) ≫ P.actLeft = 𝟙 P.X
  rw [one_actLeft, Iso.inv_hom_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.left_unitor_Bimod.inv_hom_id Bimod.LeftUnitorBimod.inv_hom_id

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem hom_left_act_hom' :
    ((regular R).tensorBimod P).actLeft ≫ hom P = (𝟙 R.X ⊗ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  -- ⊢ TensorBimod.actLeft (regular R) P ≫ hom P = (𝟙 R.X ⊗ hom P) ≫ P.actLeft
         -- ⊢ ((PreservesCoequalizer.iso (tensorLeft R.X) (R.mul ⊗ 𝟙 P.X) ((α_ R.X R.X P.X …
  refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft R.X).map (coequalizer.π ((mk R.X R.mul R.mul).actRight ⊗ 𝟙 P.X)  …
  dsimp
  -- ⊢ (𝟙 R.X ⊗ coequalizer.π (R.mul ⊗ 𝟙 P.X) ((α_ R.X R.X P.X).hom ≫ (𝟙 R.X ⊗ P.ac …
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  -- ⊢ ((α_ R.X R.X P.X).inv ≫ (R.mul ⊗ 𝟙 P.X)) ≫ P.actLeft = (𝟙 R.X ⊗ coequalizer. …
  slice_lhs 2 3 => rw [left_assoc]
  -- ⊢ (α_ R.X R.X P.X).inv ≫ (α_ R.X R.X P.X).hom ≫ (𝟙 R.X ⊗ P.actLeft) ≫ P.actLef …
  slice_rhs 1 2 => rw [← id_tensor_comp, coequalizer.π_desc]
  -- ⊢ (α_ R.X R.X P.X).inv ≫ (α_ R.X R.X P.X).hom ≫ (𝟙 R.X ⊗ P.actLeft) ≫ P.actLef …
  rw [Iso.inv_hom_id_assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.left_unitor_Bimod.hom_left_act_hom' Bimod.LeftUnitorBimod.hom_left_act_hom'

theorem hom_right_act_hom' :
    ((regular R).tensorBimod P).actRight ≫ hom P = (hom P ⊗ 𝟙 S.X) ≫ P.actRight := by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  -- ⊢ TensorBimod.actRight (regular R) P ≫ hom P = (hom P ⊗ 𝟙 S.X) ≫ P.actRight
         -- ⊢ ((PreservesCoequalizer.iso (tensorRight S.X) (R.mul ⊗ 𝟙 P.X) ((α_ R.X R.X P. …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight S.X).map (coequalizer.π ((mk R.X R.mul R.mul).actRight ⊗ 𝟙 P.X) …
  dsimp
  -- ⊢ (coequalizer.π (R.mul ⊗ 𝟙 P.X) ((α_ R.X R.X P.X).hom ≫ (𝟙 R.X ⊗ P.actLeft))  …
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  -- ⊢ ((α_ R.X P.X S.X).hom ≫ (𝟙 R.X ⊗ P.actRight)) ≫ P.actLeft = (coequalizer.π ( …
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  -- ⊢ ((α_ R.X P.X S.X).hom ≫ (𝟙 R.X ⊗ P.actRight)) ≫ P.actLeft = (P.actLeft ⊗ 𝟙 S …
  slice_rhs 1 2 => rw [middle_assoc]
  -- ⊢ ((α_ R.X P.X S.X).hom ≫ (𝟙 R.X ⊗ P.actRight)) ≫ P.actLeft = (α_ R.X P.X S.X) …
  simp only [Category.assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.left_unitor_Bimod.hom_right_act_hom' Bimod.LeftUnitorBimod.hom_right_act_hom'

end LeftUnitorBimod

namespace RightUnitorBimod

variable {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the right unitor isomorphism. -/
noncomputable def hom : TensorBimod.X P (regular S) ⟶ P.X :=
  coequalizer.desc P.actRight (by dsimp; rw [Category.assoc, right_assoc, Iso.hom_inv_id_assoc])
                                  -- ⊢ (P.actRight ⊗ 𝟙 S.X) ≫ P.actRight = ((α_ P.X S.X S.X).hom ≫ (𝟙 P.X ⊗ S.mul)) …
                                         -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.right_unitor_Bimod.hom Bimod.RightUnitorBimod.hom

/-- The underlying morphism of the inverse component of the right unitor isomorphism. -/
noncomputable def inv : P.X ⟶ TensorBimod.X P (regular S) :=
  (ρ_ P.X).inv ≫ (𝟙 _ ⊗ S.one) ≫ coequalizer.π _ _
set_option linter.uppercaseLean3 false in
#align Bimod.right_unitor_Bimod.inv Bimod.RightUnitorBimod.inv

theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, TensorBimod.X]
  -- ⊢ coequalizer.desc P.actRight (_ : (P.actRight ⊗ 𝟙 (regular S).X) ≫ P.actRight …
  ext; dsimp
  -- ⊢ coequalizer.π (P.actRight ⊗ 𝟙 (regular S).X) ((α_ P.X S.X (regular S).X).hom …
       -- ⊢ coequalizer.π (P.actRight ⊗ 𝟙 S.X) ((α_ P.X S.X S.X).hom ≫ (𝟙 P.X ⊗ S.mul))  …
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ ((P.actRight ≫ (ρ_ P.X).inv) ≫ (𝟙 P.X ⊗ S.one)) ≫ coequalizer.π (P.actRight  …
  slice_lhs 1 2 => rw [rightUnitor_inv_naturality]
  -- ⊢ (((ρ_ (P.X ⊗ S.X)).inv ≫ (P.actRight ⊗ 𝟙 tensorUnit')) ≫ (𝟙 P.X ⊗ S.one)) ≫  …
  slice_lhs 2 3 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  -- ⊢ (ρ_ (P.X ⊗ S.X)).inv ≫ ((𝟙 (P.X ⊗ S.X) ⊗ S.one) ≫ (P.actRight ⊗ 𝟙 S.X)) ≫ co …
  slice_lhs 3 4 => rw [coequalizer.condition]
  -- ⊢ (ρ_ (P.X ⊗ S.X)).inv ≫ (𝟙 (P.X ⊗ S.X) ⊗ S.one) ≫ ((α_ P.X S.X S.X).hom ≫ (𝟙  …
  slice_lhs 2 3 => rw [← MonoidalCategory.tensor_id, associator_naturality]
  -- ⊢ (ρ_ (P.X ⊗ S.X)).inv ≫ (((α_ P.X S.X tensorUnit').hom ≫ (𝟙 P.X ⊗ 𝟙 S.X ⊗ S.o …
  slice_lhs 3 4 => rw [← id_tensor_comp, Mon_.mul_one]
  -- ⊢ (ρ_ (P.X ⊗ S.X)).inv ≫ (α_ P.X S.X tensorUnit').hom ≫ (𝟙 P.X ⊗ (ρ_ S.X).hom) …
  slice_rhs 1 2 => rw [Category.comp_id]
  -- ⊢ (ρ_ (P.X ⊗ S.X)).inv ≫ (α_ P.X S.X tensorUnit').hom ≫ (𝟙 P.X ⊗ (ρ_ S.X).hom) …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.right_unitor_Bimod.hom_inv_id Bimod.RightUnitorBimod.hom_inv_id

theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  -- ⊢ ((ρ_ P.X).inv ≫ (𝟙 P.X ⊗ S.one) ≫ coequalizer.π (P.actRight ⊗ 𝟙 S.X) ((α_ P. …
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (ρ_ P.X).inv ≫ (𝟙 P.X ⊗ S.one) ≫ P.actRight = 𝟙 P.X
  rw [actRight_one, Iso.inv_hom_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.right_unitor_Bimod.inv_hom_id Bimod.RightUnitorBimod.inv_hom_id

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem hom_left_act_hom' :
    (P.tensorBimod (regular S)).actLeft ≫ hom P = (𝟙 R.X ⊗ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  -- ⊢ TensorBimod.actLeft P (regular S) ≫ hom P = (𝟙 R.X ⊗ hom P) ≫ P.actLeft
         -- ⊢ ((PreservesCoequalizer.iso (tensorLeft R.X) (P.actRight ⊗ 𝟙 S.X) ((α_ P.X S. …
  refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft R.X).map (coequalizer.π (P.actRight ⊗ 𝟙 (mk S.X S.mul S.mul).X)  …
  dsimp
  -- ⊢ (𝟙 R.X ⊗ coequalizer.π (P.actRight ⊗ 𝟙 S.X) ((α_ P.X S.X S.X).hom ≫ (𝟙 P.X ⊗ …
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  -- ⊢ ((α_ R.X P.X S.X).inv ≫ (P.actLeft ⊗ 𝟙 S.X)) ≫ P.actRight = (𝟙 R.X ⊗ coequal …
  slice_lhs 2 3 => rw [middle_assoc]
  -- ⊢ (α_ R.X P.X S.X).inv ≫ (α_ R.X P.X S.X).hom ≫ (𝟙 R.X ⊗ P.actRight) ≫ P.actLe …
  slice_rhs 1 2 => rw [← id_tensor_comp, coequalizer.π_desc]
  -- ⊢ (α_ R.X P.X S.X).inv ≫ (α_ R.X P.X S.X).hom ≫ (𝟙 R.X ⊗ P.actRight) ≫ P.actLe …
  rw [Iso.inv_hom_id_assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.right_unitor_Bimod.hom_left_act_hom' Bimod.RightUnitorBimod.hom_left_act_hom'

theorem hom_right_act_hom' :
    (P.tensorBimod (regular S)).actRight ≫ hom P = (hom P ⊗ 𝟙 S.X) ≫ P.actRight := by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  -- ⊢ TensorBimod.actRight P (regular S) ≫ hom P = (hom P ⊗ 𝟙 S.X) ≫ P.actRight
         -- ⊢ ((PreservesCoequalizer.iso (tensorRight S.X) (P.actRight ⊗ 𝟙 S.X) ((α_ P.X S …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight S.X).map (coequalizer.π (P.actRight ⊗ 𝟙 (mk S.X S.mul S.mul).X) …
  dsimp
  -- ⊢ (coequalizer.π (P.actRight ⊗ 𝟙 S.X) ((α_ P.X S.X S.X).hom ≫ (𝟙 P.X ⊗ S.mul)) …
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  -- ⊢ ((α_ P.X S.X S.X).hom ≫ (𝟙 P.X ⊗ S.mul)) ≫ P.actRight = (coequalizer.π (P.ac …
  slice_lhs 2 3 => rw [right_assoc]
  -- ⊢ (α_ P.X S.X S.X).hom ≫ (α_ P.X S.X S.X).inv ≫ (P.actRight ⊗ 𝟙 S.X) ≫ P.actRi …
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  -- ⊢ (α_ P.X S.X S.X).hom ≫ (α_ P.X S.X S.X).inv ≫ (P.actRight ⊗ 𝟙 S.X) ≫ P.actRi …
  rw [Iso.hom_inv_id_assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.right_unitor_Bimod.hom_right_act_hom' Bimod.RightUnitorBimod.hom_right_act_hom'

end RightUnitorBimod

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The associator as a bimodule isomorphism. -/
noncomputable def associatorBimod {W X Y Z : Mon_ C} (L : Bimod W X) (M : Bimod X Y)
    (N : Bimod Y Z) : (L.tensorBimod M).tensorBimod N ≅ L.tensorBimod (M.tensorBimod N) :=
  isoOfIso
    { hom := AssociatorBimod.hom L M N
      inv := AssociatorBimod.inv L M N
      hom_inv_id := AssociatorBimod.hom_inv_id L M N
      inv_hom_id := AssociatorBimod.inv_hom_id L M N } (AssociatorBimod.hom_left_act_hom' L M N)
    (AssociatorBimod.hom_right_act_hom' L M N)
set_option linter.uppercaseLean3 false in
#align Bimod.associator_Bimod Bimod.associatorBimod

/-- The left unitor as a bimodule isomorphism. -/
noncomputable def leftUnitorBimod {X Y : Mon_ C} (M : Bimod X Y) : (regular X).tensorBimod M ≅ M :=
  isoOfIso
    { hom := LeftUnitorBimod.hom M
      inv := LeftUnitorBimod.inv M
      hom_inv_id := LeftUnitorBimod.hom_inv_id M
      inv_hom_id := LeftUnitorBimod.inv_hom_id M } (LeftUnitorBimod.hom_left_act_hom' M)
    (LeftUnitorBimod.hom_right_act_hom' M)
set_option linter.uppercaseLean3 false in
#align Bimod.left_unitor_Bimod Bimod.leftUnitorBimod

/-- The right unitor as a bimodule isomorphism. -/
noncomputable def rightUnitorBimod {X Y : Mon_ C} (M : Bimod X Y) : M.tensorBimod (regular Y) ≅ M :=
  isoOfIso
    { hom := RightUnitorBimod.hom M
      inv := RightUnitorBimod.inv M
      hom_inv_id := RightUnitorBimod.hom_inv_id M
      inv_hom_id := RightUnitorBimod.inv_hom_id M } (RightUnitorBimod.hom_left_act_hom' M)
    (RightUnitorBimod.hom_right_act_hom' M)
set_option linter.uppercaseLean3 false in
#align Bimod.right_unitor_Bimod Bimod.rightUnitorBimod

theorem whisker_left_comp_bimod {X Y Z : Mon_ C} (M : Bimod X Y) {N P Q : Bimod Y Z} (f : N ⟶ P)
    (g : P ⟶ Q) : tensorHom (𝟙 M) (f ≫ g) = tensorHom (𝟙 M) f ≫ tensorHom (𝟙 M) g := by
  rw [← tensor_comp, Category.comp_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.whisker_left_comp_Bimod Bimod.whisker_left_comp_bimod

theorem id_whisker_left_bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
    tensorHom (𝟙 (regular X)) f = (leftUnitorBimod M).hom ≫ f ≫ (leftUnitorBimod N).inv := by
  dsimp [tensorHom, regular, leftUnitorBimod]
  -- ⊢ Hom.mk (colimMap (parallelPairHom (X.mul ⊗ 𝟙 M.X) ((α_ X.X X.X M.X).hom ≫ (𝟙 …
  ext
  -- ⊢ (Hom.mk (colimMap (parallelPairHom (X.mul ⊗ 𝟙 M.X) ((α_ X.X X.X M.X).hom ≫ ( …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π ((mk X.X X.mul X.mul).actRight ⊗ 𝟙 M.X) ((α_ (mk X.X X.mul X.m …
  dsimp
  -- ⊢ coequalizer.π (X.mul ⊗ 𝟙 M.X) ((α_ X.X X.X M.X).hom ≫ (𝟙 X.X ⊗ M.actLeft)) ≫ …
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  dsimp [LeftUnitorBimod.hom]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  dsimp [LeftUnitorBimod.inv]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 1 2 => rw [Hom.left_act_hom]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 2 3 => rw [leftUnitor_inv_naturality]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 3 4 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 4 4 => rw [← Iso.inv_hom_id_assoc (α_ X.X X.X N.X) (𝟙 X.X ⊗ N.actLeft)]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 5 7 => rw [← Category.assoc, ← coequalizer.condition]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 3 4 => rw [← MonoidalCategory.tensor_id, associator_inv_naturality]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 4 5 => rw [← comp_tensor_id, Mon_.one_mul]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  have : (λ_ (X.X ⊗ N.X)).inv ≫ (α_ (𝟙_ C) X.X N.X).inv ≫ ((λ_ X.X).hom ⊗ 𝟙 N.X) = 𝟙 _ := by
    pure_coherence
  slice_rhs 2 4 => rw [this]
  -- ⊢ (𝟙 X.X ⊗ f.hom) ≫ colimit.ι (parallelPair (X.mul ⊗ 𝟙 N.X) ((α_ X.X X.X N.X). …
  slice_rhs 1 2 => rw [Category.comp_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.id_whisker_left_Bimod Bimod.id_whisker_left_bimod

theorem comp_whisker_left_bimod {W X Y Z : Mon_ C} (M : Bimod W X) (N : Bimod X Y)
    {P P' : Bimod Y Z} (f : P ⟶ P') :
    tensorHom (𝟙 (M.tensorBimod N)) f =
      (associatorBimod M N P).hom ≫
        tensorHom (𝟙 M) (tensorHom (𝟙 N) f) ≫ (associatorBimod M N P').inv := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  -- ⊢ Hom.mk (colimMap (parallelPairHom (TensorBimod.actRight M N ⊗ 𝟙 P.X) ((α_ (T …
  ext
  -- ⊢ (Hom.mk (colimMap (parallelPairHom (TensorBimod.actRight M N ⊗ 𝟙 P.X) ((α_ ( …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π ((mk (TensorBimod.X M N) (TensorBimod.actLeft M N) (TensorBimo …
  dsimp
  -- ⊢ coequalizer.π (TensorBimod.actRight M N ⊗ 𝟙 P.X) ((α_ (TensorBimod.X M N) Y. …
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (𝟙 (TensorBimod.X M N) ⊗ f.hom) ≫ colimit.ι (parallelPair (TensorBimod.actRi …
  dsimp [TensorBimod.X, AssociatorBimod.hom]
  -- ⊢ (𝟙 (coequalizer (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actL …
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ (𝟙 (coequalizer (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actL …
  dsimp [AssociatorBimod.homAux, AssociatorBimod.inv]
  -- ⊢ (𝟙 (coequalizer (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actL …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight P.X).map (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X). …
  rw [tensorRight_map]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 2 3 => rw [← id_tensor_comp, ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  dsimp [AssociatorBimod.invAux]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 2 2 => rw [id_tensor_comp]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 2 3 => rw [associator_inv_naturality]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_rhs 1 3 => rw [Iso.hom_inv_id_assoc, MonoidalCategory.tensor_id]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_lhs 1 2 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.comp_whisker_left_Bimod Bimod.comp_whisker_left_bimod

theorem comp_whisker_right_bimod {X Y Z : Mon_ C} {M N P : Bimod X Y} (f : M ⟶ N) (g : N ⟶ P)
    (Q : Bimod Y Z) : tensorHom (f ≫ g) (𝟙 Q) = tensorHom f (𝟙 Q) ≫ tensorHom g (𝟙 Q) := by
  rw [← tensor_comp, Category.comp_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.comp_whisker_right_Bimod Bimod.comp_whisker_right_bimod

theorem whisker_right_id_bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
    tensorHom f (𝟙 (regular Y)) = (rightUnitorBimod M).hom ≫ f ≫ (rightUnitorBimod N).inv := by
  dsimp [tensorHom, regular, rightUnitorBimod]
  -- ⊢ Hom.mk (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 Y.X) ((α_ M.X Y.X Y.X).hom …
  ext
  -- ⊢ (Hom.mk (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 Y.X) ((α_ M.X Y.X Y.X).ho …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π (M.actRight ⊗ 𝟙 (mk Y.X Y.mul Y.mul).X) ((α_ M.X Y.X (mk Y.X Y …
  dsimp
  -- ⊢ coequalizer.π (M.actRight ⊗ 𝟙 Y.X) ((α_ M.X Y.X Y.X).hom ≫ (𝟙 M.X ⊗ Y.mul))  …
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  dsimp [RightUnitorBimod.hom]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  dsimp [RightUnitorBimod.inv]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 1 2 => rw [Hom.right_act_hom]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 2 3 => rw [rightUnitor_inv_naturality]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 3 4 => rw [tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 4 5 => rw [coequalizer.condition]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 3 4 => rw [← MonoidalCategory.tensor_id, associator_naturality]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 4 5 => rw [← id_tensor_comp, Mon_.mul_one]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  have : (ρ_ (N.X ⊗ Y.X)).inv ≫ (α_ N.X Y.X (𝟙_ C)).hom ≫ (𝟙 N.X ⊗ (ρ_ Y.X).hom) = 𝟙 _ := by
    pure_coherence
  slice_rhs 2 4 => rw [this]
  -- ⊢ (f.hom ⊗ 𝟙 Y.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Y.X) ((α_ N.X Y.X  …
  slice_rhs 1 2 => rw [Category.comp_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.whisker_right_id_Bimod Bimod.whisker_right_id_bimod

theorem whisker_right_comp_bimod {W X Y Z : Mon_ C} {M M' : Bimod W X} (f : M ⟶ M') (N : Bimod X Y)
    (P : Bimod Y Z) :
    tensorHom f (𝟙 (N.tensorBimod P)) =
      (associatorBimod M N P).inv ≫
        tensorHom (tensorHom f (𝟙 N)) (𝟙 P) ≫ (associatorBimod M' N P).hom := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  -- ⊢ Hom.mk (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 (TensorBimod.X N P)) ((α_  …
  ext
  -- ⊢ (Hom.mk (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 (TensorBimod.X N P)) ((α_ …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π (M.actRight ⊗ 𝟙 (mk (TensorBimod.X N P) (TensorBimod.actLeft N …
  dsimp
  -- ⊢ coequalizer.π (M.actRight ⊗ 𝟙 (TensorBimod.X N P)) ((α_ M.X X.X (TensorBimod …
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (f.hom ⊗ 𝟙 (TensorBimod.X N P)) ≫ colimit.ι (parallelPair (M'.actRight ⊗ 𝟙 ( …
  dsimp [TensorBimod.X, AssociatorBimod.inv]
  -- ⊢ (f.hom ⊗ 𝟙 (coequalizer (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X  …
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ (f.hom ⊗ 𝟙 (coequalizer (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X  …
  dsimp [AssociatorBimod.invAux, AssociatorBimod.hom]
  -- ⊢ (f.hom ⊗ 𝟙 (coequalizer (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X  …
  refine' (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorLeft M.X).map (coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).h …
  rw [tensorLeft_map]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 2 3 => rw [← comp_tensor_id, ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  dsimp [AssociatorBimod.homAux]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 2 2 => rw [comp_tensor_id]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 2 3 => rw [associator_naturality]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_rhs 1 3 => rw [Iso.inv_hom_id_assoc, MonoidalCategory.tensor_id]
  -- ⊢ (𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X) ((α_ N.X Y.X P.X).hom ≫ (𝟙 N.X ⊗ …
  slice_lhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.whisker_right_comp_Bimod Bimod.whisker_right_comp_bimod

theorem whisker_assoc_bimod {W X Y Z : Mon_ C} (M : Bimod W X) {N N' : Bimod X Y} (f : N ⟶ N')
    (P : Bimod Y Z) :
    tensorHom (tensorHom (𝟙 M) f) (𝟙 P) =
      (associatorBimod M N P).hom ≫
        tensorHom (𝟙 M) (tensorHom f (𝟙 P)) ≫ (associatorBimod M N' P).inv := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  -- ⊢ Hom.mk (colimMap (parallelPairHom (TensorBimod.actRight M N ⊗ 𝟙 P.X) ((α_ (T …
  ext
  -- ⊢ (Hom.mk (colimMap (parallelPairHom (TensorBimod.actRight M N ⊗ 𝟙 P.X) ((α_ ( …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π ((mk (TensorBimod.X M N) (TensorBimod.actLeft M N) (TensorBimo …
  dsimp
  -- ⊢ coequalizer.π (TensorBimod.actRight M N ⊗ 𝟙 P.X) ((α_ (TensorBimod.X M N) Y. …
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M …
  dsimp [AssociatorBimod.hom]
  -- ⊢ (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M …
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M …
  dsimp [AssociatorBimod.homAux]
  -- ⊢ (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight P.X).map (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X). …
  rw [tensorRight_map]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X X.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLe …
  slice_lhs 1 2 => rw [← comp_tensor_id, ι_colimMap, parallelPairHom_app_one]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 2 3 => rw [← id_tensor_comp, ι_colimMap, parallelPairHom_app_one]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  dsimp [AssociatorBimod.inv]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  dsimp [AssociatorBimod.invAux]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 2 2 => rw [id_tensor_comp]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 2 3 => rw [associator_inv_naturality]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_rhs 1 3 => rw [Iso.hom_inv_id_assoc]
  -- ⊢ ((𝟙 M.X ⊗ f.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 N'.X) ((α_ M.X X. …
  slice_lhs 1 1 => rw [comp_tensor_id]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.whisker_assoc_Bimod Bimod.whisker_assoc_bimod

theorem whisker_exchange_bimod {X Y Z : Mon_ C} {M N : Bimod X Y} {P Q : Bimod Y Z} (f : M ⟶ N)
    (g : P ⟶ Q) : tensorHom (𝟙 M) g ≫ tensorHom f (𝟙 Q) =
      tensorHom f (𝟙 P) ≫ tensorHom (𝟙 N) g := by
  dsimp [tensorHom]
  -- ⊢ Hom.mk (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 P.X) ((α_ M.X Y.X P.X).hom …
  ext
  -- ⊢ (Hom.mk (colimMap (parallelPairHom (M.actRight ⊗ 𝟙 P.X) ((α_ M.X Y.X P.X).ho …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π (M.actRight ⊗ 𝟙 P.X) ((α_ M.X Y.X P.X).hom ≫ (𝟙 M.X ⊗ P.actLef …
  dsimp
  -- ⊢ coequalizer.π (M.actRight ⊗ 𝟙 P.X) ((α_ M.X Y.X P.X).hom ≫ (𝟙 M.X ⊗ P.actLef …
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ ((𝟙 M.X ⊗ g.hom) ≫ colimit.ι (parallelPair (M.actRight ⊗ 𝟙 Q.X) ((α_ M.X Y.X …
  slice_lhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (𝟙 M.X ⊗ g.hom) ≫ (f.hom ⊗ 𝟙 Q.X) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙  …
  slice_lhs 1 2 => rw [id_tensor_comp_tensor_id]
  -- ⊢ (f.hom ⊗ g.hom) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Q.X) ((α_ N.X Y.X  …
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (f.hom ⊗ g.hom) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Q.X) ((α_ N.X Y.X  …
  slice_rhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (f.hom ⊗ g.hom) ≫ colimit.ι (parallelPair (N.actRight ⊗ 𝟙 Q.X) ((α_ N.X Y.X  …
  slice_rhs 1 2 => rw [tensor_id_comp_id_tensor]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.whisker_exchange_Bimod Bimod.whisker_exchange_bimod

set_option maxHeartbeats 400000 in
theorem pentagon_bimod {V W X Y Z : Mon_ C} (M : Bimod V W) (N : Bimod W X) (P : Bimod X Y)
    (Q : Bimod Y Z) :
    tensorHom (associatorBimod M N P).hom (𝟙 Q) ≫
      (associatorBimod M (N.tensorBimod P) Q).hom ≫
        tensorHom (𝟙 M) (associatorBimod N P Q).hom =
      (associatorBimod (M.tensorBimod N) P Q).hom ≫
        (associatorBimod M N (P.tensorBimod Q)).hom := by
  dsimp [tensorHom, associatorBimod]
  -- ⊢ Hom.mk (colimMap (parallelPairHom (TensorBimod.actRight (tensorBimod M N) P  …
  ext
  -- ⊢ (Hom.mk (colimMap (parallelPairHom (TensorBimod.actRight (tensorBimod M N) P …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π ((tensorBimod (tensorBimod M N) P).actRight ⊗ 𝟙 Q.X) ((α_ (ten …
  dsimp
  -- ⊢ coequalizer.π (TensorBimod.actRight (tensorBimod M N) P ⊗ 𝟙 Q.X) ((α_ (Tenso …
  dsimp only [AssociatorBimod.hom]
  -- ⊢ coequalizer.π (TensorBimod.actRight (tensorBimod M N) P ⊗ 𝟙 Q.X) ((α_ (Tenso …
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (((coequalizer.desc (AssociatorBimod.homAux M N P) (_ : ((tensorBimod M N).a …
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  -- ⊢ (coequalizer.desc (AssociatorBimod.homAux M N P) (_ : ((tensorBimod M N).act …
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ (coequalizer.desc (AssociatorBimod.homAux M N P) (_ : ((tensorBimod M N).act …
  dsimp [AssociatorBimod.homAux]
  -- ⊢ (coequalizer.desc ((PreservesCoequalizer.iso (tensorRight P.X) (M.actRight ⊗ …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight Q.X).map (coequalizer.π ((tensorBimod M N).actRight ⊗ 𝟙 P.X) (( …
  dsimp
  -- ⊢ (coequalizer.π (TensorBimod.actRight M N ⊗ 𝟙 P.X) ((α_ (TensorBimod.X M N) X …
  slice_lhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  -- ⊢ ((((PreservesCoequalizer.iso (tensorRight P.X) (M.actRight ⊗ 𝟙 N.X) ((α_ M.X …
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ ((((PreservesCoequalizer.iso (tensorRight P.X) (M.actRight ⊗ 𝟙 N.X) ((α_ M.X …
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  -- ⊢ ((((PreservesCoequalizer.iso (tensorRight P.X) (M.actRight ⊗ 𝟙 N.X) ((α_ M.X …
  refine' (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight P.X ⋙ tensorRight Q.X).map (coequalizer.π (M.actRight ⊗ 𝟙 N.X)  …
  dsimp
  -- ⊢ ((coequalizer.π (M.actRight ⊗ 𝟙 N.X) ((α_ M.X W.X N.X).hom ≫ (𝟙 M.X ⊗ N.actL …
  slice_lhs 1 2 =>
    rw [← comp_tensor_id, π_tensor_id_preserves_coequalizer_inv_desc, comp_tensor_id,
      comp_tensor_id]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X …
  dsimp only [TensorBimod.X]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((𝟙 M.X ⊗ coequalizer.π (N.actRight ⊗ 𝟙 P.X …
  slice_lhs 2 3 => rw [associator_naturality]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ ((((α_ M.X (N.X ⊗ P.X) Q.X).hom ≫ (𝟙 M.X ⊗  …
  slice_lhs 5 6 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ (α_ M.X (N.X ⊗ P.X) Q.X).hom ≫ (𝟙 M.X ⊗ coe …
  slice_lhs 4 5 => rw [← id_tensor_comp, coequalizer.π_desc]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ (α_ M.X (N.X ⊗ P.X) Q.X).hom ≫ (𝟙 M.X ⊗ coe …
  slice_lhs 3 4 =>
    rw [← id_tensor_comp, π_tensor_id_preserves_coequalizer_inv_desc, id_tensor_comp,
      id_tensor_comp]
  slice_rhs 1 2 => rw [associator_naturality]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ (α_ M.X (N.X ⊗ P.X) Q.X).hom ≫ ((𝟙 M.X ⊗ (α …
  slice_rhs 2 3 =>
    rw [MonoidalCategory.tensor_id, tensor_id_comp_id_tensor, ← id_tensor_comp_tensor_id]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ (α_ M.X (N.X ⊗ P.X) Q.X).hom ≫ ((𝟙 M.X ⊗ (α …
  slice_rhs 2 3 => rw [← MonoidalCategory.tensor_id, associator_naturality]
  -- ⊢ ((α_ M.X N.X P.X).hom ⊗ 𝟙 Q.X) ≫ (α_ M.X (N.X ⊗ P.X) Q.X).hom ≫ ((𝟙 M.X ⊗ (α …
  coherence
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.pentagon_Bimod Bimod.pentagon_bimod

theorem triangle_bimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) :
    (associatorBimod M (regular Y) N).hom ≫ tensorHom (𝟙 M) (leftUnitorBimod N).hom =
      tensorHom (rightUnitorBimod M).hom (𝟙 N) := by
  dsimp [tensorHom, associatorBimod, leftUnitorBimod, rightUnitorBimod]
  -- ⊢ (isoOfIso (Iso.mk (AssociatorBimod.hom M (regular Y) N) (AssociatorBimod.inv …
  ext
  -- ⊢ ((isoOfIso (Iso.mk (AssociatorBimod.hom M (regular Y) N) (AssociatorBimod.in …
  apply coequalizer.hom_ext
  -- ⊢ coequalizer.π ((tensorBimod M (regular Y)).actRight ⊗ 𝟙 N.X) ((α_ (tensorBim …
  dsimp
  -- ⊢ coequalizer.π (TensorBimod.actRight M (regular Y) ⊗ 𝟙 N.X) ((α_ (TensorBimod …
  dsimp [AssociatorBimod.hom]
  -- ⊢ coequalizer.π (TensorBimod.actRight M (regular Y) ⊗ 𝟙 N.X) ((α_ (TensorBimod …
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  -- ⊢ AssociatorBimod.homAux M (regular Y) N ≫ colimMap (parallelPairHom (M.actRig …
  dsimp [AssociatorBimod.homAux]
  -- ⊢ ((PreservesCoequalizer.iso (tensorRight N.X) (M.actRight ⊗ 𝟙 Y.X) ((α_ M.X Y …
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ ((PreservesCoequalizer.iso (tensorRight N.X) (M.actRight ⊗ 𝟙 Y.X) ((α_ M.X Y …
  dsimp [RightUnitorBimod.hom]
  -- ⊢ ((PreservesCoequalizer.iso (tensorRight N.X) (M.actRight ⊗ 𝟙 Y.X) ((α_ M.X Y …
  refine' (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 _
  -- ⊢ (tensorRight N.X).map (coequalizer.π (M.actRight ⊗ 𝟙 (regular Y).X) ((α_ M.X …
  dsimp [regular]
  -- ⊢ (coequalizer.π (M.actRight ⊗ 𝟙 Y.X) ((α_ M.X Y.X Y.X).hom ≫ (𝟙 M.X ⊗ Y.mul)) …
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  -- ⊢ ((α_ M.X Y.X N.X).hom ≫ (𝟙 M.X ⊗ coequalizer.π (Y.mul ⊗ 𝟙 N.X) ((α_ Y.X Y.X  …
  slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  -- ⊢ (α_ M.X Y.X N.X).hom ≫ (𝟙 M.X ⊗ coequalizer.π (Y.mul ⊗ 𝟙 N.X) ((α_ Y.X Y.X N …
  dsimp [LeftUnitorBimod.hom]
  -- ⊢ (α_ M.X Y.X N.X).hom ≫ (𝟙 M.X ⊗ coequalizer.π (Y.mul ⊗ 𝟙 N.X) ((α_ Y.X Y.X N …
  slice_lhs 2 3 => rw [← id_tensor_comp, coequalizer.π_desc]
  -- ⊢ (α_ M.X Y.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLeft) ≫ colimit.ι (parallelPair (M.actR …
  slice_rhs 1 2 => rw [← comp_tensor_id, coequalizer.π_desc]
  -- ⊢ (α_ M.X Y.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLeft) ≫ colimit.ι (parallelPair (M.actR …
  slice_rhs 1 2 => rw [coequalizer.condition]
  -- ⊢ (α_ M.X Y.X N.X).hom ≫ (𝟙 M.X ⊗ N.actLeft) ≫ colimit.ι (parallelPair (M.actR …
  simp only [Category.assoc]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align Bimod.triangle_Bimod Bimod.triangle_bimod

/-- The bicategory of algebras (monoids) and bimodules, all internal to some monoidal category. -/
noncomputable def monBicategory : Bicategory (Mon_ C) where
  Hom X Y := Bimod X Y
  homCategory X Y := (inferInstance : Category (Bimod X Y))
  id X := regular X
  comp M N := tensorBimod M N
  whiskerLeft L _ _ f := tensorHom (Bimod.id' L) f
  whiskerRight f N := tensorHom f (Bimod.id' N)
  associator := associatorBimod
  leftUnitor := leftUnitorBimod
  rightUnitor := rightUnitorBimod
  whiskerLeft_id _ _ := tensor_id
  whiskerLeft_comp M _ _ _ f g := whisker_left_comp_bimod M f g
  id_whiskerLeft := id_whisker_left_bimod
  comp_whiskerLeft M N _ _ f := comp_whisker_left_bimod M N f
  id_whiskerRight _ _ := tensor_id
  comp_whiskerRight f g Q := comp_whisker_right_bimod f g Q
  whiskerRight_id := whisker_right_id_bimod
  whiskerRight_comp := whisker_right_comp_bimod
  whisker_assoc M _ _ f P := whisker_assoc_bimod M f P
  whisker_exchange := whisker_exchange_bimod
  pentagon := pentagon_bimod
  triangle := triangle_bimod
set_option linter.uppercaseLean3 false in
#align Bimod.Mon_bicategory Bimod.monBicategory

end Bimod
