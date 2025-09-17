/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Oleksandr Manzyuk
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-!
# The category of bimodule objects over a pair of monoid objects.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory MonObj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

section

open CategoryTheory.Limits

variable [HasCoequalizers C]

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

theorem id_tensor_π_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Z ⊗ Y ⟶ W)
    (wh : (Z ◁ f) ≫ h = (Z ◁ g) ≫ h) :
    (Z ◁ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh

theorem id_tensor_π_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : Z ⊗ X ⟶ X') (q : Z ⊗ Y ⟶ Y') (wf : (Z ◁ f) ≫ q = p ≫ f')
    (wg : (Z ◁ g) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (Z ◁ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫
          colimMap (parallelPairHom (Z ◁ f) (Z ◁ g) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorLeft Z) f g f' g' p q wf wg h wh

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem π_tensor_id_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Y ⊗ Z ⟶ W)
    (wh : (f ▷ Z) ≫ h = (g ▷ Z) ≫ h) :
    (coequalizer.π f g ▷ Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorRight Z) f g h wh

theorem π_tensor_id_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : X ⊗ Z ⟶ X') (q : Y ⊗ Z ⟶ Y') (wf : (f ▷ Z) ≫ q = p ≫ f')
    (wg : (g ▷ Z) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (coequalizer.π f g ▷ Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫
          colimMap (parallelPairHom (f ▷ Z) (g ▷ Z) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorRight Z) f g f' g' p q wf wg h wh

end

end

/-- A bimodule object for a pair of monoid objects, all internal to some monoidal category. -/
structure Bimod (A B : Mon_ C) where
  /-- The underlying monoidal category -/
  X : C
  /-- The left action of this bimodule object -/
  actLeft : A.X ⊗ X ⟶ X
  one_actLeft : η ▷ X ≫ actLeft = (λ_ X).hom := by cat_disch
  left_assoc :
    μ ▷ X ≫ actLeft = (α_ A.X A.X X).hom ≫ A.X ◁ actLeft ≫ actLeft := by cat_disch
  /-- The right action of this bimodule object -/
  actRight : X ⊗ B.X ⟶ X
  actRight_one : X ◁ η ≫ actRight = (ρ_ X).hom := by cat_disch
  right_assoc :
    X ◁ μ ≫ actRight = (α_ X B.X B.X).inv ≫ actRight ▷ B.X ≫ actRight := by
    cat_disch
  middle_assoc :
    actLeft ▷ B.X ≫ actRight = (α_ A.X X B.X).hom ≫ A.X ◁ actRight ≫ actLeft := by
    cat_disch

attribute [reassoc (attr := simp)] Bimod.one_actLeft Bimod.actRight_one Bimod.left_assoc
  Bimod.right_assoc Bimod.middle_assoc

namespace Bimod

variable {A B : Mon_ C} (M : Bimod A B)

/-- A morphism of bimodule objects. -/
@[ext]
structure Hom (M N : Bimod A B) where
  /-- The morphism between `M`'s monoidal category and `N`'s monoidal category -/
  hom : M.X ⟶ N.X
  left_act_hom : M.actLeft ≫ hom = (A.X ◁ hom) ≫ N.actLeft := by cat_disch
  right_act_hom : M.actRight ≫ hom = (hom ▷ B.X) ≫ N.actRight := by cat_disch

attribute [reassoc (attr := simp)] Hom.left_act_hom Hom.right_act_hom

/-- The identity morphism on a bimodule object. -/
@[simps]
def id' (M : Bimod A B) : Hom M M where hom := 𝟙 M.X

instance homInhabited (M : Bimod A B) : Inhabited (Hom M M) :=
  ⟨id' M⟩

/-- Composition of bimodule object morphisms. -/
@[simps]
def comp {M N O : Bimod A B} (f : Hom M N) (g : Hom N O) : Hom M O where hom := f.hom ≫ g.hom

instance : Category (Bimod A B) where
  Hom M N := Hom M N
  id := id'
  comp f g := comp f g

@[ext]
lemma hom_ext {M N : Bimod A B} (f g : M ⟶ N) (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
theorem id_hom' (M : Bimod A B) : (𝟙 M : Hom M M).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Bimod A B} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).hom = f.hom ≫ g.hom :=
  rfl

/-- Construct an isomorphism of bimodules by giving an isomorphism between the underlying objects
and checking compatibility with left and right actions only in the forward direction.
-/
@[simps]
def isoOfIso {X Y : Mon_ C} {P Q : Bimod X Y} (f : P.X ≅ Q.X)
    (f_left_act_hom : P.actLeft ≫ f.hom = (X.X ◁ f.hom) ≫ Q.actLeft)
    (f_right_act_hom : P.actRight ≫ f.hom = (f.hom ▷ Y.X) ≫ Q.actRight) : P ≅ Q where
  hom :=
    { hom := f.hom }
  inv :=
    { hom := f.inv
      left_act_hom := by
        rw [← cancel_mono f.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          f_left_act_hom, ← Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
          whiskerLeft_id, Category.id_comp]
      right_act_hom := by
        rw [← cancel_mono f.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
          f_right_act_hom, ← Category.assoc, ← comp_whiskerRight, Iso.inv_hom_id,
          id_whiskerRight, Category.id_comp] }
  hom_inv_id := by ext; dsimp; rw [Iso.hom_inv_id]
  inv_hom_id := by ext; dsimp; rw [Iso.inv_hom_id]

variable (A)

/-- A monoid object as a bimodule over itself. -/
@[simps]
def regular : Bimod A A where
  X := A.X
  actLeft := μ
  actRight := μ

instance : Inhabited (Bimod A A) :=
  ⟨regular A⟩

/-- The forgetful functor from bimodule objects to the ambient category. -/
def forget : Bimod A B ⥤ C where
  obj A := A.X
  map f := f.hom

open CategoryTheory.Limits

variable [HasCoequalizers C]

namespace TensorBimod

variable {R S T : Mon_ C} (P : Bimod R S) (Q : Bimod S T)

/-- The underlying object of the tensor product of two bimodules. -/
noncomputable def X : C :=
  coequalizer (P.actRight ▷ Q.X) ((α_ _ _ _).hom ≫ (P.X ◁ Q.actLeft))

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- Left action for the tensor product of two bimodules. -/
noncomputable def actLeft : R.X ⊗ X P Q ⟶ X P Q :=
  (PreservesCoequalizer.iso (tensorLeft R.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).inv ≫ ((α_ _ _ _).inv ▷ _) ≫ (P.actLeft ▷ S.X ▷ Q.X))
        ((α_ _ _ _).inv ≫ (P.actLeft ▷ Q.X))
        (by
          dsimp
          simp only [Category.assoc]
          slice_lhs 1 2 => rw [associator_inv_naturality_middle]
          slice_rhs 3 4 => rw [← comp_whiskerRight, middle_assoc, comp_whiskerRight]
          simp)
        (by
          dsimp
          slice_lhs 1 1 => rw [whiskerLeft_comp]
          slice_lhs 2 3 => rw [associator_inv_naturality_right]
          slice_lhs 3 4 => rw [whisker_exchange]
          simp))

theorem whiskerLeft_π_actLeft :
    (R.X ◁ coequalizer.π _ _) ≫ actLeft P Q =
      (α_ _ _ _).inv ≫ (P.actLeft ▷ Q.X) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorLeft _)]
  simp only [Category.assoc]

theorem one_act_left' : (η ▷ _) ≫ actLeft P Q = (λ_ _).hom := by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, one_actLeft]
  slice_rhs 1 2 => rw [leftUnitor_naturality]
  monoidal

theorem left_assoc' :
    (μ ▷ _) ≫ actLeft P Q = (α_ R.X R.X _).hom ≫ (R.X ◁ actLeft P Q) ≫ actLeft P Q := by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, left_assoc, comp_whiskerRight, comp_whiskerRight]
  slice_rhs 1 2 => rw [associator_naturality_right]
  slice_rhs 2 3 =>
    rw [← whiskerLeft_comp, whiskerLeft_π_actLeft,
      whiskerLeft_comp, whiskerLeft_comp]
  slice_rhs 4 5 => rw [whiskerLeft_π_actLeft]
  slice_rhs 3 4 => rw [associator_inv_naturality_middle]
  monoidal

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Right action for the tensor product of two bimodules. -/
noncomputable def actRight : X P Q ⊗ T.X ⟶ X P Q :=
  (PreservesCoequalizer.iso (tensorRight T.X) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (P.X ◁ S.X ◁ Q.actRight) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).hom ≫ (P.X ◁ Q.actRight))
        (by
          dsimp
          slice_lhs 1 2 => rw [associator_naturality_left]
          slice_lhs 2 3 => rw [← whisker_exchange]
          simp)
        (by
          dsimp
          simp only [comp_whiskerRight, whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc]
          slice_lhs 3 4 =>
            rw [← whiskerLeft_comp, middle_assoc, whiskerLeft_comp]
          simp))

theorem π_tensor_id_actRight :
    (coequalizer.π _ _ ▷ T.X) ≫ actRight P Q =
      (α_ _ _ _).hom ≫ (P.X ◁ Q.actRight) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorRight _)]
  simp only [Category.assoc]

theorem actRight_one' : (_ ◁ η) ≫ actRight P Q = (ρ_ _).hom := by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, actRight_one]
  simp

theorem right_assoc' :
    (_ ◁ μ) ≫ actRight P Q =
      (α_ _ T.X T.X).inv ≫ (actRight P Q ▷ T.X) ≫ actRight P Q := by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, right_assoc,
    whiskerLeft_comp, whiskerLeft_comp]
  slice_rhs 1 2 => rw [associator_inv_naturality_left]
  slice_rhs 2 3 => rw [← comp_whiskerRight, π_tensor_id_actRight, comp_whiskerRight,
    comp_whiskerRight]
  slice_rhs 4 5 => rw [π_tensor_id_actRight]
  simp

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem middle_assoc' :
    (actLeft P Q ▷ T.X) ≫ actRight P Q =
      (α_ R.X _ T.X).hom ≫ (R.X ◁ actRight P Q) ≫ actLeft P Q := by
  refine (cancel_epi ((tensorLeft _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [X]
  slice_lhs 1 2 => rw [← comp_whiskerRight, whiskerLeft_π_actLeft, comp_whiskerRight,
    comp_whiskerRight]
  slice_lhs 3 4 => rw [π_tensor_id_actRight]
  slice_lhs 2 3 => rw [associator_naturality_left]
  slice_rhs 1 2 => rw [associator_naturality_middle]
  slice_rhs 2 3 => rw [← whiskerLeft_comp, π_tensor_id_actRight,
    whiskerLeft_comp, whiskerLeft_comp]
  slice_rhs 4 5 => rw [whiskerLeft_π_actLeft]
  slice_rhs 3 4 => rw [associator_inv_naturality_right]
  slice_rhs 4 5 => rw [whisker_exchange]
  simp

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

/-- Left whiskering for morphisms of bimodule objects. -/
@[simps]
noncomputable def whiskerLeft {X Y Z : Mon_ C} (M : Bimod X Y) {N₁ N₂ : Bimod Y Z} (f : N₁ ⟶ N₂) :
    M.tensorBimod N₁ ⟶ M.tensorBimod N₂ where
  hom :=
    colimMap
      (parallelPairHom _ _ _ _ (_ ◁ f.hom) (_ ◁ f.hom)
        (by rw [whisker_exchange])
        (by
          simp only [Category.assoc, tensor_whiskerLeft, Iso.inv_hom_id_assoc,
            Iso.cancel_iso_hom_left]
          slice_lhs 1 2 => rw [← whiskerLeft_comp, Hom.left_act_hom]
          simp))
  left_act_hom := by
    refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_rhs 1 2 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one,
      whiskerLeft_comp]
    slice_rhs 2 3 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_rhs 1 2 => rw [associator_inv_naturality_right]
    slice_rhs 2 3 => rw [whisker_exchange]
    simp
  right_act_hom := by
    refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [← whiskerLeft_comp, Hom.right_act_hom]
    slice_rhs 1 2 =>
      rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one, comp_whiskerRight]
    slice_rhs 2 3 => rw [TensorBimod.π_tensor_id_actRight]
    simp

/-- Right whiskering for morphisms of bimodule objects. -/
@[simps]
noncomputable def whiskerRight {X Y Z : Mon_ C} {M₁ M₂ : Bimod X Y} (f : M₁ ⟶ M₂) (N : Bimod Y Z) :
    M₁.tensorBimod N ⟶ M₂.tensorBimod N where
  hom :=
    colimMap
      (parallelPairHom _ _ _ _ (f.hom ▷ _ ▷ _) (f.hom ▷ _)
        (by rw [← comp_whiskerRight, Hom.right_act_hom, comp_whiskerRight])
        (by
          slice_lhs 2 3 => rw [whisker_exchange]
          simp))
  left_act_hom := by
    refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [← comp_whiskerRight, Hom.left_act_hom]
    slice_rhs 1 2 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one, whiskerLeft_comp]
    slice_rhs 2 3 => rw [TensorBimod.whiskerLeft_π_actLeft]
    slice_rhs 1 2 => rw [associator_inv_naturality_middle]
    simp
  right_act_hom := by
    refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [whisker_exchange]
    slice_rhs 1 2 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one,
      comp_whiskerRight]
    slice_rhs 2 3 => rw [TensorBimod.π_tensor_id_actRight]
    simp

end

namespace AssociatorBimod

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
variable {R S T U : Mon_ C} (P : Bimod R S) (Q : Bimod S T) (L : Bimod T U)

/-- An auxiliary morphism for the definition of the underlying morphism of the forward component of
the associator isomorphism. -/
noncomputable def homAux : (P.tensorBimod Q).X ⊗ L.X ⟶ (P.tensorBimod (Q.tensorBimod L)).X :=
  (PreservesCoequalizer.iso (tensorRight L.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).hom ≫ (P.X ◁ coequalizer.π _ _) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_naturality_left]
        slice_lhs 2 3 => rw [← whisker_exchange]
        slice_lhs 3 4 => rw [coequalizer.condition]
        slice_lhs 2 3 => rw [associator_naturality_right]
        slice_lhs 3 4 =>
          rw [← whiskerLeft_comp, TensorBimod.whiskerLeft_π_actLeft, whiskerLeft_comp]
        simp)

/-- The underlying morphism of the forward component of the associator isomorphism. -/
noncomputable def hom :
    ((P.tensorBimod Q).tensorBimod L).X ⟶ (P.tensorBimod (Q.tensorBimod L)).X :=
  coequalizer.desc (homAux P Q L)
    (by
      dsimp [homAux]
      refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [← comp_whiskerRight, TensorBimod.π_tensor_id_actRight,
        comp_whiskerRight, comp_whiskerRight]
      slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      slice_lhs 2 3 => rw [associator_naturality_middle]
      slice_lhs 3 4 =>
        rw [← whiskerLeft_comp, coequalizer.condition,
          whiskerLeft_comp, whiskerLeft_comp]
      slice_rhs 1 2 => rw [associator_naturality_left]
      slice_rhs 2 3 => rw [← whisker_exchange]
      slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      simp)

theorem hom_left_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actLeft ≫ hom P Q L =
      (R.X ◁ hom P Q L) ≫ (P.tensorBimod (Q.tensorBimod L)).actLeft := by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 2 => rw [TensorBimod.whiskerLeft_π_actLeft]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc, whiskerLeft_comp]
  refine (cancel_epi ((tensorRight _ ⋙ tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp; dsimp [TensorBimod.X]
  slice_lhs 1 2 => rw [associator_inv_naturality_middle]
  slice_lhs 2 3 =>
    rw [← comp_whiskerRight, TensorBimod.whiskerLeft_π_actLeft,
      comp_whiskerRight, comp_whiskerRight]
  slice_lhs 4 6 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [associator_naturality_left]
  slice_rhs 1 3 =>
    rw [← whiskerLeft_comp, ← whiskerLeft_comp, π_tensor_id_preserves_coequalizer_inv_desc,
      whiskerLeft_comp, whiskerLeft_comp]
  slice_rhs 3 4 => erw [TensorBimod.whiskerLeft_π_actLeft P (Q.tensorBimod L)]
  slice_rhs 2 3 => erw [associator_inv_naturality_right]
  slice_rhs 3 4 => erw [whisker_exchange]
  monoidal

theorem hom_right_act_hom' :
    ((P.tensorBimod Q).tensorBimod L).actRight ≫ hom P Q L =
      (hom P Q L ▷ U.X) ≫ (P.tensorBimod (Q.tensorBimod L)).actRight := by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 2 => rw [TensorBimod.π_tensor_id_actRight]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc, comp_whiskerRight]
  refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp; dsimp [TensorBimod.X]
  slice_lhs 1 2 => rw [associator_naturality_left]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_rhs 1 3 =>
    rw [← comp_whiskerRight, ← comp_whiskerRight, π_tensor_id_preserves_coequalizer_inv_desc,
      comp_whiskerRight, comp_whiskerRight]
  slice_rhs 3 4 => erw [TensorBimod.π_tensor_id_actRight P (Q.tensorBimod L)]
  slice_rhs 2 3 => erw [associator_naturality_middle]
  dsimp
  slice_rhs 3 4 =>
    rw [← whiskerLeft_comp, TensorBimod.π_tensor_id_actRight, whiskerLeft_comp, whiskerLeft_comp]
  monoidal

/-- An auxiliary morphism for the definition of the underlying morphism of the inverse component of
the associator isomorphism. -/
noncomputable def invAux : P.X ⊗ (Q.tensorBimod L).X ⟶ ((P.tensorBimod Q).tensorBimod L).X :=
  (PreservesCoequalizer.iso (tensorLeft P.X) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).inv ≫ (coequalizer.π _ _ ▷ L.X) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [TensorBimod.X]
        slice_lhs 1 2 => rw [associator_inv_naturality_middle]
        rw [← Iso.inv_hom_id_assoc (α_ _ _ _) (P.X ◁ Q.actRight), comp_whiskerRight]
        slice_lhs 3 4 =>
          rw [← comp_whiskerRight, Category.assoc, ← TensorBimod.π_tensor_id_actRight,
            comp_whiskerRight]
        slice_lhs 4 5 => rw [coequalizer.condition]
        slice_lhs 3 4 => rw [associator_naturality_left]
        slice_rhs 1 2 => rw [whiskerLeft_comp]
        slice_rhs 2 3 => rw [associator_inv_naturality_right]
        slice_rhs 3 4 => rw [whisker_exchange]
        simp)

/-- The underlying morphism of the inverse component of the associator isomorphism. -/
noncomputable def inv :
    (P.tensorBimod (Q.tensorBimod L)).X ⟶ ((P.tensorBimod Q).tensorBimod L).X :=
  coequalizer.desc (invAux P Q L)
    (by
      dsimp [invAux]
      refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
      dsimp [TensorBimod.X]
      slice_lhs 1 2 => rw [whisker_exchange]
      slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_lhs 1 2 => rw [associator_inv_naturality_left]
      slice_lhs 2 3 =>
        rw [← comp_whiskerRight, coequalizer.condition, comp_whiskerRight, comp_whiskerRight]
      slice_rhs 1 2 => rw [associator_naturality_right]
      slice_rhs 2 3 =>
        rw [← whiskerLeft_comp, TensorBimod.whiskerLeft_π_actLeft,
          whiskerLeft_comp, whiskerLeft_comp]
      slice_rhs 4 6 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_rhs 3 4 => rw [associator_inv_naturality_middle]
      monoidal)

theorem hom_inv_id : hom P Q L ≫ inv P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [Iso.hom_inv_id_assoc]
  dsimp only [TensorBimod.X]
  slice_rhs 2 3 => rw [Category.comp_id]
  rfl

theorem inv_hom_id : inv P Q L ≫ hom P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_lhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [Iso.inv_hom_id_assoc]
  dsimp only [TensorBimod.X]
  slice_rhs 2 3 => rw [Category.comp_id]
  rfl

end AssociatorBimod

namespace LeftUnitorBimod

variable {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the left unitor isomorphism. -/
noncomputable def hom : TensorBimod.X (regular R) P ⟶ P.X :=
  coequalizer.desc P.actLeft (by dsimp; rw [Category.assoc, left_assoc])

/-- The underlying morphism of the inverse component of the left unitor isomorphism. -/
noncomputable def inv : P.X ⟶ TensorBimod.X (regular R) P :=
  (λ_ P.X).inv ≫ (η[R.X] ▷ _) ≫ coequalizer.π _ _

theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 3 3 => rw [← Iso.inv_hom_id_assoc (α_ R.X R.X P.X) (R.X ◁ P.actLeft)]
  slice_lhs 4 6 => rw [← Category.assoc, ← coequalizer.condition]
  slice_lhs 2 3 => rw [associator_inv_naturality_left]
  slice_lhs 3 4 => rw [← comp_whiskerRight, MonObj.one_mul]
  slice_rhs 1 2 => rw [Category.comp_id]
  monoidal

theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [one_actLeft, Iso.inv_hom_id]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem hom_left_act_hom' :
    ((regular R).tensorBimod P).actLeft ≫ hom P = (R.X ◁ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [left_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  rw [Iso.inv_hom_id_assoc]

theorem hom_right_act_hom' :
    ((regular R).tensorBimod P).actRight ≫ hom P = (hom P ▷ S.X) ≫ P.actRight := by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [middle_assoc]
  simp only [Category.assoc]

end LeftUnitorBimod

namespace RightUnitorBimod

variable {R S : Mon_ C} (P : Bimod R S)

/-- The underlying morphism of the forward component of the right unitor isomorphism. -/
noncomputable def hom : TensorBimod.X P (regular S) ⟶ P.X :=
  coequalizer.desc P.actRight (by dsimp; rw [Category.assoc, right_assoc, Iso.hom_inv_id_assoc])

/-- The underlying morphism of the inverse component of the right unitor isomorphism. -/
noncomputable def inv : P.X ⟶ TensorBimod.X P (regular S) :=
  (ρ_ P.X).inv ≫ (_ ◁ η[S.X]) ≫ coequalizer.π _ _

theorem hom_inv_id : hom P ≫ inv P = 𝟙 _ := by
  dsimp only [hom, inv, TensorBimod.X]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [rightUnitor_inv_naturality]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [coequalizer.condition]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_lhs 3 4 => rw [← whiskerLeft_comp, MonObj.mul_one]
  slice_rhs 1 2 => rw [Category.comp_id]
  monoidal

theorem inv_hom_id : inv P ≫ hom P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [actRight_one, Iso.inv_hom_id]

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem hom_left_act_hom' :
    (P.tensorBimod (regular S)).actLeft ≫ hom P = (R.X ◁ hom P) ≫ P.actLeft := by
  dsimp; dsimp [hom, TensorBimod.actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [middle_assoc]
  slice_rhs 1 2 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  rw [Iso.inv_hom_id_assoc]

theorem hom_right_act_hom' :
    (P.tensorBimod (regular S)).actRight ≫ hom P = (hom P ▷ S.X) ≫ P.actRight := by
  dsimp; dsimp [hom, TensorBimod.actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [right_assoc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  rw [Iso.hom_inv_id_assoc]

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

/-- The left unitor as a bimodule isomorphism. -/
noncomputable def leftUnitorBimod {X Y : Mon_ C} (M : Bimod X Y) : (regular X).tensorBimod M ≅ M :=
  isoOfIso
    { hom := LeftUnitorBimod.hom M
      inv := LeftUnitorBimod.inv M
      hom_inv_id := LeftUnitorBimod.hom_inv_id M
      inv_hom_id := LeftUnitorBimod.inv_hom_id M } (LeftUnitorBimod.hom_left_act_hom' M)
    (LeftUnitorBimod.hom_right_act_hom' M)

/-- The right unitor as a bimodule isomorphism. -/
noncomputable def rightUnitorBimod {X Y : Mon_ C} (M : Bimod X Y) : M.tensorBimod (regular Y) ≅ M :=
  isoOfIso
    { hom := RightUnitorBimod.hom M
      inv := RightUnitorBimod.inv M
      hom_inv_id := RightUnitorBimod.hom_inv_id M
      inv_hom_id := RightUnitorBimod.inv_hom_id M } (RightUnitorBimod.hom_left_act_hom' M)
    (RightUnitorBimod.hom_right_act_hom' M)

theorem whiskerLeft_id_bimod {X Y Z : Mon_ C} {M : Bimod X Y} {N : Bimod Y Z} :
    whiskerLeft M (𝟙 N) = 𝟙 (M.tensorBimod N) := by
  ext
  apply Limits.coequalizer.hom_ext
  dsimp only [tensorBimod_X, whiskerLeft_hom, id_hom']
  simp only [whiskerLeft_id, ι_colimMap, parallelPair_obj_one,
    parallelPairHom_app_one, Category.id_comp]
  erw [Category.comp_id]

theorem id_whiskerRight_bimod {X Y Z : Mon_ C} {M : Bimod X Y} {N : Bimod Y Z} :
    whiskerRight (𝟙 M) N = 𝟙 (M.tensorBimod N) := by
  ext
  apply Limits.coequalizer.hom_ext
  dsimp only [tensorBimod_X, whiskerRight_hom, id_hom']
  simp only [id_whiskerRight, ι_colimMap, parallelPair_obj_one,
    parallelPairHom_app_one, Category.id_comp]
  erw [Category.comp_id]

theorem whiskerLeft_comp_bimod {X Y Z : Mon_ C} (M : Bimod X Y) {N P Q : Bimod Y Z} (f : N ⟶ P)
    (g : P ⟶ Q) : whiskerLeft M (f ≫ g) = whiskerLeft M f ≫ whiskerLeft M g := by
  ext
  apply Limits.coequalizer.hom_ext
  simp

theorem id_whiskerLeft_bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
    whiskerLeft (regular X) f = (leftUnitorBimod M).hom ≫ f ≫ (leftUnitorBimod N).inv := by
  dsimp [tensorHom, regular, leftUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [LeftUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.left_act_hom]
  slice_rhs 2 3 => rw [leftUnitor_inv_naturality]
  slice_rhs 3 4 => rw [whisker_exchange]
  slice_rhs 4 4 => rw [← Iso.inv_hom_id_assoc (α_ X.X X.X N.X) (X.X ◁ N.actLeft)]
  slice_rhs 5 7 => rw [← Category.assoc, ← coequalizer.condition]
  slice_rhs 3 4 => rw [associator_inv_naturality_left]
  slice_rhs 4 5 => rw [← comp_whiskerRight, MonObj.one_mul]
  have : (λ_ (X.X ⊗ N.X)).inv ≫ (α_ (𝟙_ C) X.X N.X).inv ≫ ((λ_ X.X).hom ▷ N.X) = 𝟙 _ := by
    monoidal
  grind

theorem comp_whiskerLeft_bimod {W X Y Z : Mon_ C} (M : Bimod W X) (N : Bimod X Y)
    {P P' : Bimod Y Z} (f : P ⟶ P') :
    whiskerLeft (M.tensorBimod N) f =
      (associatorBimod M N P).hom ≫
        whiskerLeft M (whiskerLeft N f) ≫ (associatorBimod M N P').inv := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux, AssociatorBimod.inv]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux]
  slice_rhs 2 2 => rw [whiskerLeft_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_inv_naturality_right]
  slice_rhs 1 3 => rw [Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [← whisker_exchange]
  rfl

theorem comp_whiskerRight_bimod {X Y Z : Mon_ C} {M N P : Bimod X Y} (f : M ⟶ N) (g : N ⟶ P)
    (Q : Bimod Y Z) : whiskerRight (f ≫ g) Q = whiskerRight f Q ≫ whiskerRight g Q := by
  ext
  apply Limits.coequalizer.hom_ext
  simp

theorem whiskerRight_id_bimod {X Y : Mon_ C} {M N : Bimod X Y} (f : M ⟶ N) :
    whiskerRight f (regular Y) = (rightUnitorBimod M).hom ≫ f ≫ (rightUnitorBimod N).inv := by
  dsimp [tensorHom, regular, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [RightUnitorBimod.inv]
  slice_rhs 1 2 => rw [Hom.right_act_hom]
  slice_rhs 2 3 => rw [rightUnitor_inv_naturality]
  slice_rhs 3 4 => rw [← whisker_exchange]
  slice_rhs 4 5 => rw [coequalizer.condition]
  slice_rhs 3 4 => rw [associator_naturality_right]
  slice_rhs 4 5 => rw [← whiskerLeft_comp, MonObj.mul_one]
  simp

theorem whiskerRight_comp_bimod {W X Y Z : Mon_ C} {M M' : Bimod W X} (f : M ⟶ M') (N : Bimod X Y)
    (P : Bimod Y Z) :
    whiskerRight f (N.tensorBimod P) =
      (associatorBimod M N P).inv ≫
        whiskerRight (whiskerRight f N) P ≫ (associatorBimod M' N P).hom := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [TensorBimod.X, AssociatorBimod.inv]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux, AssociatorBimod.hom]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  simp only [curriedTensor_obj_map]
  slice_rhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  slice_rhs 2 2 => rw [comp_whiskerRight]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_naturality_left]
  slice_rhs 1 3 => rw [Iso.inv_hom_id_assoc]
  slice_lhs 1 2 => rw [whisker_exchange]
  rfl

theorem whisker_assoc_bimod {W X Y Z : Mon_ C} (M : Bimod W X) {N N' : Bimod X Y} (f : N ⟶ N')
    (P : Bimod Y Z) :
    whiskerRight (whiskerLeft M f) P =
      (associatorBimod M N P).hom ≫
        whiskerLeft M (whiskerRight f P) ≫ (associatorBimod M N' P).inv := by
  dsimp [tensorHom, tensorBimod, associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  simp only [Functor.flip_obj_map, curriedTensor_map_app]
  slice_lhs 1 2 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod.inv]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.invAux]
  slice_rhs 2 2 => rw [whiskerLeft_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  simp

theorem whisker_exchange_bimod {X Y Z : Mon_ C} {M N : Bimod X Y} {P Q : Bimod Y Z} (f : M ⟶ N)
    (g : P ⟶ Q) : whiskerLeft M g ≫ whiskerRight f Q =
      whiskerRight f P ≫ whiskerLeft N g := by
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 1 2 => rw [whisker_exchange]
  simp

theorem pentagon_bimod {V W X Y Z : Mon_ C} (M : Bimod V W) (N : Bimod W X) (P : Bimod X Y)
    (Q : Bimod Y Z) :
    whiskerRight (associatorBimod M N P).hom Q ≫
      (associatorBimod M (N.tensorBimod P) Q).hom ≫
        whiskerLeft M (associatorBimod N P Q).hom =
      (associatorBimod (M.tensorBimod N) P Q).hom ≫
        (associatorBimod M N (P.tensorBimod Q)).hom := by
  dsimp [associatorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp only [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight, π_tensor_id_preserves_coequalizer_inv_desc, comp_whiskerRight,
      comp_whiskerRight]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  dsimp only [TensorBimod.X]
  slice_lhs 2 3 => rw [associator_naturality_middle]
  slice_lhs 5 6 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 4 5 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  slice_lhs 3 4 =>
    rw [← whiskerLeft_comp, π_tensor_id_preserves_coequalizer_inv_desc,
      whiskerLeft_comp, whiskerLeft_comp]
  slice_rhs 1 2 => rw [associator_naturality_left]
  slice_rhs 2 3 => rw [← whisker_exchange]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_naturality_right]
  monoidal

theorem triangle_bimod {X Y Z : Mon_ C} (M : Bimod X Y) (N : Bimod Y Z) :
    (associatorBimod M (regular Y) N).hom ≫ whiskerLeft M (leftUnitorBimod N).hom =
      whiskerRight (rightUnitorBimod M).hom N := by
  dsimp [associatorBimod, leftUnitorBimod, rightUnitorBimod]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp [AssociatorBimod.hom]
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod.homAux]
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod.hom]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [regular]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod.hom]
  slice_lhs 2 3 => rw [← whiskerLeft_comp, coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.condition]
  simp only [Category.assoc]

/-- The bicategory of algebras (monoids) and bimodules, all internal to some monoidal category. -/
noncomputable def monBicategory : Bicategory (Mon_ C) where
  Hom X Y := Bimod X Y
  homCategory X Y := (inferInstance : Category (Bimod X Y))
  id X := regular X
  comp M N := tensorBimod M N
  whiskerLeft L _ _ f := whiskerLeft L f
  whiskerRight f N := whiskerRight f N
  associator := associatorBimod
  leftUnitor := leftUnitorBimod
  rightUnitor := rightUnitorBimod
  whiskerLeft_id _ _ := whiskerLeft_id_bimod
  whiskerLeft_comp M _ _ _ f g := whiskerLeft_comp_bimod M f g
  id_whiskerLeft := id_whiskerLeft_bimod
  comp_whiskerLeft M N _ _ f := comp_whiskerLeft_bimod M N f
  id_whiskerRight _ _ := id_whiskerRight_bimod
  comp_whiskerRight f g Q := comp_whiskerRight_bimod f g Q
  whiskerRight_id := whiskerRight_id_bimod
  whiskerRight_comp := whiskerRight_comp_bimod
  whisker_assoc M _ _ f P := whisker_assoc_bimod M f P
  whisker_exchange := whisker_exchange_bimod
  pentagon := pentagon_bimod
  triangle := triangle_bimod

end Bimod
