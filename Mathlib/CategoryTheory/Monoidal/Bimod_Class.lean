/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Oleksandr Manzyuk
-/
import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Monoidal.Mod_Class
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

theorem id_tensor_π_preserves_coequalizer_inv_desc {W X Y Z : C} (f g : X ⟶ Y) (h : Z ⊗ Y ⟶ W)
    (wh : (Z ◁ f) ≫ h = (Z ◁ g) ≫ h) :
    (Z ◁ coequalizer.π f g) ≫
        (PreservesCoequalizer.iso (tensorLeft Z) f g).inv ≫ coequalizer.desc h wh =
      h :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft Z) f g h wh

theorem id_tensor_π_preserves_coequalizer_inv_colimMap_desc {X Y Z X' Y' Z' : C} (f g : X ⟶ Y)
    (f' g' : X' ⟶ Y') (p : Z ⊗ X ⟶ X') (q : (Z ⊗ Y : C) ⟶ Y') (wf : (Z ◁ f) ≫ q = p ≫ f')
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
    (f' g' : X' ⟶ Y') (p : (X ⊗ Z : C) ⟶ X') (q : Y ⊗ Z ⟶ Y') (wf : (f ▷ Z) ≫ q = p ≫ f')
    (wg : (g ▷ Z) ≫ q = p ≫ g') (h : Y' ⟶ Z') (wh : f' ≫ h = g' ≫ h) :
    (coequalizer.π f g ▷ Z) ≫
        (PreservesCoequalizer.iso (tensorRight Z) f g).inv ≫
          colimMap (parallelPairHom (f ▷ Z) (g ▷ Z) f' g' p q wf wg) ≫ coequalizer.desc h wh =
      q ≫ h :=
  map_π_preserves_coequalizer_inv_colimMap_desc (tensorRight Z) f g f' g' p q wf wg h wh

end

end

open scoped Mon_Class

class RightMod_Class (B : C) [Mon_Class B] (X : C) where
  actRight : X ⊗ B ⟶ X
  actRight_one : (X ◁ η) ≫ actRight = (ρ_ X).hom := by aesop_cat
  right_assoc : (X ◁ μ) ≫ actRight = (α_ X B B).inv ≫ (actRight ▷ B) ≫ actRight := by aesop_cat

namespace RightMod_Class

scoped notation "↶" => RightMod_Class.actRight

variable {B M : C} [Mon_Class B] [RightMod_Class B M]

@[simps]
instance regular : RightMod_Class B B where
  actRight := μ

end RightMod_Class

/-- A bimodule object for a pair of monoid objects, all internal to some monoidal category. -/
class MiddleAssocClass (A B M : C)
    [Mon_Class A] [Mon_Class B] [Mod_Class A M] [RightMod_Class B M] : Prop where
  middle_assoc :
    (Mod_Class.act ▷ B) ≫ RightMod_Class.actRight =
      (α_ A M B).hom ≫ (A ◁ RightMod_Class.actRight) ≫ Mod_Class.act := by aesop_cat

namespace Bimod_Class

variable {A B M : C} [Mon_Class A] [Mon_Class B]

open scoped Mod_Class RightMod_Class

/-- A morphism of bimodule objects. -/
@[ext]
structure Hom (A B : C)
    [Mon_Class A] [Mon_Class B] (M N : C)
    [Mod_Class A M] [RightMod_Class B M] [Mod_Class A N] [RightMod_Class B N] where
  hom : M ⟶ N
  left_act_hom : ↷ ≫ hom = (A ◁ hom) ≫ ↷:= by aesop_cat
  right_act_hom : ↶ ≫ hom = (hom ▷ B) ≫ ↶ := by aesop_cat

attribute [reassoc (attr := simp)] Hom.left_act_hom Hom.right_act_hom

@[ext]
structure Iso (A B : C)
    [Mon_Class A] [Mon_Class B] (M N : C)
    [Mod_Class A M] [RightMod_Class B M] [Mod_Class A N] [RightMod_Class B N] where
  iso : M ≅ N
  left_act_hom : ↷ ≫ iso.hom = A ◁ iso.hom ≫ ↷ := by aesop_cat
  right_act_hom : ↶ ≫ iso.hom = iso.hom ▷ B ≫ ↶ := by aesop_cat

attribute [reassoc (attr := simp)] Iso.left_act_hom Iso.right_act_hom

@[simps]
def Iso.hom {A B : C}
    [Mon_Class A] [Mon_Class B] {M N : C}
    [Mod_Class A M] [RightMod_Class B M] [Mod_Class A N] [RightMod_Class B N]
    (f : Iso A B M N) : Hom A B M N where hom := f.iso.hom

@[simp]
theorem Iso.left_act_inv {A B : C} [Mon_Class A] [Mon_Class B]
  {M N : C} [Mod_Class A M] [RightMod_Class B M]
  [Mod_Class A N] [RightMod_Class B N] (self : Iso A B M N) :
    ↷ ≫ self.iso.inv = A ◁ self.iso.inv ≫ ↷ := by
  simp [Iso.comp_inv_eq]

@[simp]
theorem Iso.right_act_inv {A B : C} [Mon_Class A] [Mon_Class B]
  {M N : C} [Mod_Class A M] [RightMod_Class B M] [Mod_Class A N] [RightMod_Class B N]
  (self : Iso A B M N) :
    ↶ ≫ self.iso.inv = self.iso.inv ▷ B ≫ ↶ := by
  simp [Iso.comp_inv_eq]

@[simps]
def Iso.inv {A B : C}
    [Mon_Class A] [Mon_Class B] {M N : C}
    [Mod_Class A M] [RightMod_Class B M] [Mod_Class A N] [RightMod_Class B N]
    (f : Iso A B M N) : Hom A B N M where
  hom := f.iso.inv

/-- The identity morphism on a bimodule object. -/
@[simps]
def id (A B M : C) [Mon_Class A] [Mon_Class B] [Mod_Class A M] [RightMod_Class B M] :
    Hom A B M M where
  hom := 𝟙 M

instance homInhabited (M : C) [Mod_Class A M] [RightMod_Class B M] : Inhabited (Hom A B M M) :=
  ⟨id A B M⟩

/-- Composition of bimodule object morphisms. -/
@[simps]
def Hom.comp {M N O : C}
  [Mod_Class A M] [RightMod_Class B M] [Mod_Class A N] [RightMod_Class B N]
  [Mod_Class A O] [RightMod_Class B O]
  (f : Hom A B M N) (g : Hom A B N O) : Hom A B M O where hom := f.hom ≫ g.hom

end Bimod_Class

structure Bimod_Cat (A B : C) [Mon_Class A] [Mon_Class B] where
  X : C
  [isMod : Mod_Class A X]
  [isRightMod : RightMod_Class B X]
  [isMiddleAssoc : MiddleAssocClass A B X]

attribute [instance] Bimod_Cat.isMod Bimod_Cat.isRightMod Bimod_Cat.isMiddleAssoc

variable {A B : C} [Mon_Class A] [Mon_Class B]

instance : Category (Bimod_Cat A B) where
  Hom M N := Bimod_Class.Hom A B M.X N.X
  id M := Bimod_Class.id A B M.X
  comp f g := f.comp g

namespace Bimod_Cat

open Bimod_Class

abbrev of (A : C) [Mon_Class A] (B : C) [Mon_Class B]
  (M : C) [Mod_Class A M] [RightMod_Class B M] [MiddleAssocClass A B M] : Bimod_Cat A B where
  X := M

-- Porting note: added because `Hom.ext` is not triggered automatically
@[ext]
lemma hom_ext {M N : Bimod_Cat A B} (f g : M ⟶ N) (h : f.hom = g.hom) : f = g :=
  Hom.ext h

@[simp]
theorem id_hom' (M : Bimod_Cat A B) : (𝟙 M : Hom A B M.X M.X).hom = 𝟙 M.X :=
  rfl

@[simp]
theorem comp_hom' {M N K : Bimod_Cat A B} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom A B M.X K.X).hom = f.hom ≫ g.hom :=
  rfl

variable {M N : C} [Mod_Class A M] [RightMod_Class B M] [Mod_Class A N] [RightMod_Class B N]
variable [MiddleAssocClass A B M] [MiddleAssocClass A B N]

def ofHom (f : Hom A B M N) : Bimod_Cat.of A B M ⟶ Bimod_Cat.of A B N where
  hom := f.hom

def ofIso (f : Iso A B M N) : Bimod_Cat.of A B M ≅ Bimod_Cat.of A B N where
  hom := { hom := f.iso.hom }
  inv := { hom := f.iso.inv }

/-- The forgetful functor from bimodule objects to the ambient category. -/
def forget : Bimod_Cat A B ⥤ C where
  obj A := A.X
  map f := f.hom

end Bimod_Cat

namespace Bimod_Class

open Mod_Class RightMod_Class MiddleAssocClass

/-- Construct an isomorphism of bimodules by giving an isomorphism between the underlying objects
and checking compatibility with left and right actions only in the forward direction.
-/
@[simps]
def isoOfIso {X Y P Q : C}
    [Mon_Class X] [Mon_Class Y] [Mod_Class X P] [RightMod_Class Y P]
    [Mod_Class X Q] [RightMod_Class Y Q]
    (f : P ≅ Q)
    (f_left_act_hom : ↷ ≫ f.hom = (X ◁ f.hom) ≫ ↷)
    (f_right_act_hom : ↶ ≫ f.hom = (f.hom ▷ Y) ≫ ↶) : Iso X Y P Q where
  iso := f

/-- A monoid object as a bimodule over itself. -/
@[simps]
instance regular : MiddleAssocClass A A A where

instance : Inhabited (MiddleAssocClass A A A) :=
  ⟨regular⟩

open CategoryTheory.Limits

variable [HasCoequalizers C]

variable (R S T P Q : C) [Mon_Class R] [Mon_Class S] [Mon_Class T]
variable [Mod_Class R P] [RightMod_Class S P] [MiddleAssocClass R S P]
variable [Mod_Class S Q] [RightMod_Class T Q] [MiddleAssocClass S T Q]

/-- The underlying object of the tensor product of two bimodules. -/
noncomputable def tensor : C :=
  coequalizer (actRight ▷ Q) ((α_ P S Q).hom ≫ P ◁ act)

scoped notation:71 P " ⊗[" S "] " Q:70 => tensor S P Q

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]

/-- Left action for the tensor product of two bimodules. -/
noncomputable def actLeft : R ⊗ P ⊗[S] Q ⟶ P ⊗[S] Q :=
  (PreservesCoequalizer.iso (tensorLeft R) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).inv ≫ (α_ _ _ _).inv ▷ _ ≫ ↷ ▷ S ▷ Q)
        ((α_ _ _ _).inv ≫ ↷ ▷ Q)
        (by
          dsimp
          simp only [Category.assoc]
          slice_lhs 1 2 => rw [associator_inv_naturality_middle]
          slice_rhs 3 4 => rw [← comp_whiskerRight, middle_assoc, comp_whiskerRight]
          monoidal)
        (by
          dsimp
          slice_lhs 1 1 => rw [MonoidalCategory.whiskerLeft_comp]
          slice_lhs 2 3 => rw [associator_inv_naturality_right]
          slice_lhs 3 4 => rw [whisker_exchange]
          monoidal))

theorem whiskerLeft_π_actLeft :
    (R ◁ coequalizer.π _ _) ≫ actLeft _ S P Q =
      (α_ _ _ _).inv ≫ (↷ ▷ Q) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorLeft _)]
  simp only [Category.assoc]

theorem one_act_left' : η ▷ _ ≫ actLeft R S P Q = (λ_ _).hom := by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [tensor]
  -- Porting note: had to replace `rw` by `erw`
  slice_lhs 1 2 => erw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, one_act]
  slice_rhs 1 2 => rw [leftUnitor_naturality]
  monoidal

theorem left_assoc' :
    μ ▷ _ ≫ actLeft R S P Q = (α_ R R _).hom ≫ (R ◁ actLeft R S P Q) ≫ actLeft R S P Q := by
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp [tensor]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 => rw [whiskerLeft_π_actLeft]
  slice_lhs 1 2 => rw [associator_inv_naturality_left]
  slice_lhs 2 3 => rw [← comp_whiskerRight, assoc, comp_whiskerRight, comp_whiskerRight]
  slice_rhs 1 2 => rw [associator_naturality_right]
  slice_rhs 2 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp, whiskerLeft_π_actLeft,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  slice_rhs 4 5 => rw [whiskerLeft_π_actLeft]
  slice_rhs 3 4 => rw [associator_inv_naturality_middle]
  monoidal

@[simps]
noncomputable instance : Mod_Class R (P ⊗[S] Q) where
  act := actLeft R S P Q
  one_act := one_act_left' R S P Q
  assoc := left_assoc' R S P Q

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Right action for the tensor product of two bimodules. -/
noncomputable def actRight : (P ⊗[S] Q) ⊗ T ⟶ P ⊗[S] Q :=
  (PreservesCoequalizer.iso (tensorRight T) _ _).inv ≫
    colimMap
      (parallelPairHom _ _ _ _
        ((α_ _ _ _).hom ≫ (α_ _ _ _).hom ≫ (P ◁ S ◁ ↶) ≫ (α_ _ _ _).inv)
        ((α_ _ _ _).hom ≫ (P ◁ ↶))
        (by
          dsimp
          slice_lhs 1 2 => rw [associator_naturality_left]
          slice_lhs 2 3 => rw [← whisker_exchange]
          simp)
        (by
          dsimp
          simp only [comp_whiskerRight, whisker_assoc, Category.assoc, Iso.inv_hom_id_assoc]
          slice_lhs 3 4 =>
            rw [← MonoidalCategory.whiskerLeft_comp, middle_assoc,
              MonoidalCategory.whiskerLeft_comp]
          simp))

theorem π_tensor_id_actRight :
    (coequalizer.π _ _ ▷ T) ≫ actRight S T P Q =
      (α_ _ _ _).hom ≫ (P ◁ ↶) ≫ coequalizer.π _ _ := by
  erw [map_π_preserves_coequalizer_inv_colimMap (tensorRight _)]
  simp only [Category.assoc]

theorem actRight_one' : _ ◁ η ≫ actRight S T P Q = (ρ_ _).hom := by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [tensor]
  -- Porting note: had to replace `rw` by `erw`
  slice_lhs 1 2 =>erw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, actRight_one]
  simp

theorem right_assoc' :
    _ ◁ μ ≫ actRight S T P Q =
      (α_ _ T T).inv ≫ (actRight S T P Q ▷ T) ≫ actRight S T P Q := by
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [tensor]
  -- Porting note: had to replace some `rw` by `erw`
  slice_lhs 1 2 => rw [← whisker_exchange]
  slice_lhs 2 3 => rw [π_tensor_id_actRight]
  slice_lhs 1 2 => rw [associator_naturality_right]
  slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, right_assoc,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  slice_rhs 1 2 => rw [associator_inv_naturality_left]
  slice_rhs 2 3 => rw [← comp_whiskerRight, π_tensor_id_actRight, comp_whiskerRight,
    comp_whiskerRight]
  slice_rhs 4 5 => rw [π_tensor_id_actRight]
  simp

@[simps]
noncomputable instance : RightMod_Class T (P ⊗[S] Q) where
  actRight := actRight S T P Q
  actRight_one := actRight_one' S T P Q
  right_assoc := right_assoc' S T P Q

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem middle_assoc' :
    (actLeft R S P Q ▷ T) ≫ actRight S T P Q =
      (α_ R _ T).hom ≫ (R ◁ actRight S T P Q) ≫ actLeft R S P Q := by
  refine (cancel_epi ((tensorLeft _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [tensor]
  slice_lhs 1 2 => rw [← comp_whiskerRight, whiskerLeft_π_actLeft, comp_whiskerRight,
    comp_whiskerRight]
  slice_lhs 3 4 => rw [π_tensor_id_actRight]
  slice_lhs 2 3 => rw [associator_naturality_left]
  -- Porting note: had to replace `rw` by `erw`
  slice_rhs 1 2 => rw [associator_naturality_middle]
  slice_rhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, π_tensor_id_actRight,
    MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  slice_rhs 4 5 => rw [whiskerLeft_π_actLeft]
  slice_rhs 3 4 => rw [associator_inv_naturality_right]
  slice_rhs 4 5 => rw [whisker_exchange]
  simp

@[simp]
noncomputable instance : MiddleAssocClass R T (P ⊗[S] Q) where
  middle_assoc := middle_assoc' R S T P Q

end

section

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- Left whiskering for morphisms of bimodule objects. -/
@[simps]
noncomputable def whiskerLeft (X : C) {Y Z : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
    (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
    {N₁ N₂ : C} [Mod_Class Y N₁] [RightMod_Class Z N₁] [MiddleAssocClass Y Z N₁]
    [Mod_Class Y N₂] [RightMod_Class Z N₂] [MiddleAssocClass Y Z N₂]
    (f : Hom Y Z N₁ N₂) :
    Hom X Z (M ⊗[Y] N₁) (M ⊗[Y] N₂) where
  hom :=
    colimMap
      (parallelPairHom _ _ _ _ (_ ◁ f.hom) (_ ◁ f.hom)
        (by rw [whisker_exchange])
        (by
          simp only [Category.assoc, tensor_whiskerLeft, Iso.inv_hom_id_assoc,
            Iso.cancel_iso_hom_left]
          slice_lhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp, Hom.left_act_hom]
          simp))
  left_act_hom := by
    refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [whiskerLeft_π_actLeft]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one,
      MonoidalCategory.whiskerLeft_comp]
    slice_rhs 2 3 => rw [whiskerLeft_π_actLeft]
    slice_rhs 1 2 => rw [associator_inv_naturality_right]
    slice_rhs 2 3 => rw [whisker_exchange]
    simp
  right_act_hom := by
    refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [π_tensor_id_actRight]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, Hom.right_act_hom]
    slice_rhs 1 2 =>
      rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one, comp_whiskerRight]
    slice_rhs 2 3 => rw [π_tensor_id_actRight]
    simp

/-- Right whiskering for morphisms of bimodule objects. -/
@[simps]
noncomputable def whiskerRight {X Y : C} (Z : C) [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
    {M₁ M₂ : C} [Mod_Class X M₁] [RightMod_Class Y M₁] [MiddleAssocClass X Y M₁]
    [Mod_Class X M₂] [RightMod_Class Y M₂] [MiddleAssocClass X Y M₂]
    (f : Hom X Y M₁ M₂)
    (N : C) [Mod_Class Y N] [RightMod_Class Z N] [MiddleAssocClass Y Z N] :
    Hom X Z (M₁ ⊗[Y] N) (M₂ ⊗[Y] N) where
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
    slice_lhs 1 2 => rw [whiskerLeft_π_actLeft]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [← comp_whiskerRight, Hom.left_act_hom]
    slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one,
      MonoidalCategory.whiskerLeft_comp]
    slice_rhs 2 3 => rw [whiskerLeft_π_actLeft]
    slice_rhs 1 2 => rw [associator_inv_naturality_middle]
    simp
  right_act_hom := by
    refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
    dsimp
    slice_lhs 1 2 => rw [π_tensor_id_actRight]
    slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
    slice_lhs 2 3 => rw [whisker_exchange]
    slice_rhs 1 2 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one,
      comp_whiskerRight]
    slice_rhs 2 3 => rw [π_tensor_id_actRight]
    simp

end

namespace AssociatorBimod_Class

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
variable (R S T U : C) [Mon_Class R] [Mon_Class S] [Mon_Class T] [Mon_Class U]
  (P : C) [Mod_Class R P] [RightMod_Class S P] [MiddleAssocClass R S P]
  (Q : C) [Mod_Class S Q] [RightMod_Class T Q] [MiddleAssocClass S T Q]
  (L : C) [Mod_Class T L] [RightMod_Class U L] [MiddleAssocClass T U L]

/-- An auxiliary morphism for the definition of the underlying morphism of the forward component of
the associator isomorphism. -/
noncomputable def homAux : (P ⊗[S] Q) ⊗ L ⟶ P ⊗[S] (Q ⊗[T] L) :=
  (PreservesCoequalizer.iso (tensorRight L) _ _).inv ≫
    coequalizer.desc ((α_ P Q L).hom ≫ (P ◁ coequalizer.π _ _) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [tensor]
        slice_lhs 1 2 => rw [associator_naturality_left]
        slice_lhs 2 3 => rw [← whisker_exchange]
        slice_lhs 3 4 => rw [coequalizer.condition]
        slice_lhs 2 3 => rw [associator_naturality_right]
        slice_lhs 3 4 =>
          rw [← MonoidalCategory.whiskerLeft_comp,
            whiskerLeft_π_actLeft, MonoidalCategory.whiskerLeft_comp]
        simp)

/-- The underlying morphism of the forward component of the associator isomorphism. -/
noncomputable def hom : (P ⊗[S] Q) ⊗[T] L ⟶ P ⊗[S] (Q ⊗[T] L) :=
  coequalizer.desc (homAux S T P Q L)
    (by
      dsimp [homAux]
      refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
      dsimp [tensor]
      slice_lhs 1 2 => rw [← comp_whiskerRight, π_tensor_id_actRight,
        comp_whiskerRight, comp_whiskerRight]
      slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      slice_lhs 2 3 => rw [associator_naturality_middle]
      slice_lhs 3 4 =>
        rw [← MonoidalCategory.whiskerLeft_comp, coequalizer.condition,
          MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
      slice_rhs 1 2 => rw [associator_naturality_left]
      slice_rhs 2 3 => rw [← whisker_exchange]
      slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
      simp)

theorem hom_left_act_hom' :
    ↷ ≫ hom S T P Q L = R ◁ hom S T P Q L ≫ ↷ := by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  rw [tensorLeft_map]
  slice_lhs 1 2 => rw [whiskerLeft_π_actLeft]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp, coequalizer.π_desc,
    MonoidalCategory.whiskerLeft_comp]
  refine (cancel_epi ((tensorRight _ ⋙ tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp; dsimp [tensor]
  slice_lhs 1 2 => rw [associator_inv_naturality_middle]
  slice_lhs 2 3 =>
    rw [← comp_whiskerRight, whiskerLeft_π_actLeft,
      comp_whiskerRight, comp_whiskerRight]
  slice_lhs 4 6 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [associator_naturality_left]
  slice_rhs 1 3 =>
    rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp,
      π_tensor_id_preserves_coequalizer_inv_desc, MonoidalCategory.whiskerLeft_comp,
      MonoidalCategory.whiskerLeft_comp]
  slice_rhs 3 4 => erw [whiskerLeft_π_actLeft _ _ P (tensor T Q L)]
  slice_rhs 2 3 => erw [associator_inv_naturality_right]
  slice_rhs 3 4 => erw [whisker_exchange]
  monoidal

theorem hom_right_act_hom' :
    ↶ ≫ hom S T P Q L = hom S T P Q L ▷ U ≫ ↶ := by
  dsimp; dsimp [hom, homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  rw [tensorRight_map]
  slice_lhs 1 2 => rw [π_tensor_id_actRight]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc, comp_whiskerRight]
  refine (cancel_epi ((tensorRight _ ⋙ tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp; dsimp [tensor]
  slice_lhs 1 2 => rw [associator_naturality_left]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_rhs 1 3 =>
    rw [← comp_whiskerRight, ← comp_whiskerRight, π_tensor_id_preserves_coequalizer_inv_desc,
      comp_whiskerRight, comp_whiskerRight]
  slice_rhs 3 4 => erw [π_tensor_id_actRight _ _ P (Q ⊗[T] L)]
  slice_rhs 2 3 => erw [associator_naturality_middle]
  dsimp
  slice_rhs 3 4 =>
    rw [← MonoidalCategory.whiskerLeft_comp, π_tensor_id_actRight,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  monoidal

/-- An auxiliary morphism for the definition of the underlying morphism of the inverse component of
the associator isomorphism. -/
noncomputable def invAux : P ⊗ (Q ⊗[T] L) ⟶ (P ⊗[S] Q) ⊗[T] L :=
  (PreservesCoequalizer.iso (tensorLeft P) _ _).inv ≫
    coequalizer.desc ((α_ _ _ _).inv ≫ (coequalizer.π _ _ ▷ L) ≫ coequalizer.π _ _)
      (by
        dsimp; dsimp [tensor]
        slice_lhs 1 2 => rw [associator_inv_naturality_middle]
        rw [← Iso.inv_hom_id_assoc (α_ _ _ _) (P ◁ ↶), comp_whiskerRight]
        slice_lhs 3 4 =>
          rw [← comp_whiskerRight, Category.assoc, ← π_tensor_id_actRight,
            comp_whiskerRight]
        slice_lhs 4 5 => rw [coequalizer.condition]
        slice_lhs 3 4 => rw [associator_naturality_left]
        slice_rhs 1 2 => rw [MonoidalCategory.whiskerLeft_comp]
        slice_rhs 2 3 => rw [associator_inv_naturality_right]
        slice_rhs 3 4 => rw [whisker_exchange]
        monoidal)

/-- The underlying morphism of the inverse component of the associator isomorphism. -/
noncomputable def inv : P ⊗[S] (Q ⊗[T] L) ⟶ (P ⊗[S] Q) ⊗[T] L :=
  coequalizer.desc (invAux S T P Q L)
    (by
      dsimp [invAux]
      refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
      dsimp [tensor]
      slice_lhs 1 2 => rw [whisker_exchange]
      slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_lhs 1 2 => rw [associator_inv_naturality_left]
      slice_lhs 2 3 =>
        rw [← comp_whiskerRight, coequalizer.condition, comp_whiskerRight, comp_whiskerRight]
      slice_rhs 1 2 => rw [associator_naturality_right]
      slice_rhs 2 3 =>
        rw [← MonoidalCategory.whiskerLeft_comp, whiskerLeft_π_actLeft,
          MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
      slice_rhs 4 6 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
      slice_rhs 3 4 => rw [associator_inv_naturality_middle]
      monoidal)

theorem hom_inv_id : hom S T P Q L ≫ inv S T P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  rw [tensorRight_map]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [Iso.hom_inv_id_assoc]
  dsimp only [tensor]
  slice_rhs 2 3 => rw [Category.comp_id]
  rfl

theorem inv_hom_id : inv S T P Q L ≫ hom S T P Q L = 𝟙 _ := by
  dsimp [hom, homAux, inv, invAux]
  apply coequalizer.hom_ext
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  rw [tensorLeft_map]
  slice_lhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  slice_lhs 2 4 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 1 3 => rw [Iso.inv_hom_id_assoc]
  dsimp only [tensor]
  slice_rhs 2 3 => rw [Category.comp_id]
  rfl

end AssociatorBimod_Class

namespace LeftUnitorBimod_Class

variable (R S : C) [Mon_Class R] [Mon_Class S]
variable (P : C) [Mod_Class R P] [RightMod_Class S P] [MiddleAssocClass R S P]

/-- The underlying morphism of the forward component of the left unitor isomorphism. -/
noncomputable def hom : R ⊗[R] P ⟶ P :=
  coequalizer.desc ↷ (by dsimp; rw [Category.assoc, assoc])

/-- The underlying morphism of the inverse component of the left unitor isomorphism. -/
noncomputable def inv : P ⟶ R ⊗[R] P :=
  (λ_ P).inv ≫ (η ▷ _) ≫ coequalizer.π _ _

theorem hom_inv_id : hom R P ≫ inv R P = 𝟙 _ := by
  dsimp only [hom, inv, tensor]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
  slice_lhs 2 3 => rw [whisker_exchange]
  slice_lhs 3 3 => rw [← Iso.inv_hom_id_assoc (α_ R R P) (R ◁ ↷)]
  slice_lhs 4 6 => rw [← Category.assoc, ← coequalizer.condition]
  slice_lhs 2 3 => rw [associator_inv_naturality_left]
  slice_lhs 3 4 => rw [← comp_whiskerRight, Mon_Class.one_mul]
  slice_rhs 1 2 => rw [Category.comp_id]
  monoidal

theorem inv_hom_id : inv R P ≫ hom R P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [one_act, Iso.inv_hom_id]

-- variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
-- variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem hom_left_act_hom' [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] :
    ↷ ≫ hom R P = R ◁ hom R P ≫ ↷ := by
  dsimp; dsimp [hom, actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [assoc]
  slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp, coequalizer.π_desc]
  rw [Iso.inv_hom_id_assoc]

theorem hom_right_act_hom' [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] :
    ↶ ≫ hom R P = hom R P ▷ S ≫ ↶ := by
  dsimp; dsimp [hom, actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [middle_assoc]
  simp only [Category.assoc]

end LeftUnitorBimod_Class

namespace RightUnitorBimod_Class

variable (R S : C) [Mon_Class R] [Mon_Class S]
variable (P : C) [Mod_Class R P] [RightMod_Class S P] [MiddleAssocClass R S P]

/-- The underlying morphism of the forward component of the right unitor isomorphism. -/
noncomputable def hom : P ⊗[S] S ⟶ P :=
  coequalizer.desc ↶ (by dsimp; rw [Category.assoc, right_assoc, Iso.hom_inv_id_assoc])

/-- The underlying morphism of the inverse component of the right unitor isomorphism. -/
noncomputable def inv : P ⟶ P ⊗[S] S :=
  (ρ_ P).inv ≫ _ ◁ η ≫ coequalizer.π _ _

theorem hom_inv_id : hom S P ≫ inv S P = 𝟙 _ := by
  dsimp only [hom, inv, tensor]
  ext; dsimp
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  slice_lhs 1 2 => rw [rightUnitor_inv_naturality]
  slice_lhs 2 3 => rw [← whisker_exchange]
  slice_lhs 3 4 => rw [coequalizer.condition]
  slice_lhs 2 3 => rw [associator_naturality_right]
  slice_lhs 3 4 => rw [← MonoidalCategory.whiskerLeft_comp, Mon_Class.mul_one]
  slice_rhs 1 2 => rw [Category.comp_id]
  monoidal

theorem inv_hom_id : inv S P ≫ hom S P = 𝟙 _ := by
  dsimp [hom, inv]
  slice_lhs 3 4 => rw [coequalizer.π_desc]
  rw [actRight_one, Iso.inv_hom_id]

-- variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
-- variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

theorem hom_left_act_hom'  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)] :
    ↷ ≫ hom S P = (R ◁ hom S P) ≫ ↷ := by
  dsimp; dsimp [hom, actLeft, regular]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [id_tensor_π_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [middle_assoc]
  slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp, coequalizer.π_desc]
  rw [Iso.inv_hom_id_assoc]

theorem hom_right_act_hom' [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] :
    ↶ ≫ hom S P = (hom S P ▷ S) ≫ ↶ := by
  dsimp; dsimp [hom, actRight, regular]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp
  slice_lhs 1 4 => rw [π_tensor_id_preserves_coequalizer_inv_colimMap_desc]
  slice_lhs 2 3 => rw [right_assoc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  rw [Iso.hom_inv_id_assoc]

end RightUnitorBimod_Class

variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The associator as a bimodule isomorphism. -/
noncomputable def associatorBimod_Class {W X Y Z : C}
    [Mon_Class W] [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
    (L : C) [Mod_Class W L] [RightMod_Class X L] [MiddleAssocClass W X L]
    (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
    (N : C) [Mod_Class Y N] [RightMod_Class Z N] [MiddleAssocClass Y Z N] :
    Iso W Z ((L ⊗[X] M) ⊗[Y] N) (L ⊗[X] (M ⊗[Y] N)) :=
  isoOfIso
    { hom := AssociatorBimod_Class.hom _ _ L M N
      inv := AssociatorBimod_Class.inv _ _ L M N
      hom_inv_id := AssociatorBimod_Class.hom_inv_id _ _ L M N
      inv_hom_id := AssociatorBimod_Class.inv_hom_id _ _ L M N }
    (AssociatorBimod_Class.hom_left_act_hom' _ _ _ L M N)
    (AssociatorBimod_Class.hom_right_act_hom' _ _ _ L M N)

/-- The left unitor as a bimodule isomorphism. -/
noncomputable def leftUnitorBimod_Class {X Y : C} [Mon_Class X] [Mon_Class Y]
    (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M] :
    Iso X Y (X ⊗[X] M) M :=
  isoOfIso
    { hom := LeftUnitorBimod_Class.hom _ M
      inv := LeftUnitorBimod_Class.inv _ M
      hom_inv_id := LeftUnitorBimod_Class.hom_inv_id _ M
      inv_hom_id := LeftUnitorBimod_Class.inv_hom_id _ M }
    (LeftUnitorBimod_Class.hom_left_act_hom' _ M)
    (LeftUnitorBimod_Class.hom_right_act_hom' _ _ M)

/-- The right unitor as a bimodule isomorphism. -/
noncomputable def rightUnitorBimod_Class {X Y : C} [Mon_Class X] [Mon_Class Y]
    (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M] :
    Iso X Y (M ⊗[Y] Y) M :=
  isoOfIso
    { hom := RightUnitorBimod_Class.hom _ M
      inv := RightUnitorBimod_Class.inv _ M
      hom_inv_id := RightUnitorBimod_Class.hom_inv_id _ M
      inv_hom_id := RightUnitorBimod_Class.inv_hom_id _ M }
    (RightUnitorBimod_Class.hom_left_act_hom' _ _ M)
    (RightUnitorBimod_Class.hom_right_act_hom' _ M)

theorem whiskerLeft_id_bimod {X Y Z : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  (N : C) [Mod_Class Y N] [RightMod_Class Z N] [MiddleAssocClass Y Z N] :
    whiskerLeft X M (Bimod_Class.id Y Z N) = Bimod_Class.id X Z (M ⊗[Y] N) := by
  ext
  apply Limits.coequalizer.hom_ext
  dsimp only [tensor, whiskerLeft_hom, id_hom]
  simp only [MonoidalCategory.whiskerLeft_id, ι_colimMap, parallelPair_obj_one,
    parallelPairHom_app_one, Category.id_comp]
  erw [Category.comp_id]

theorem id_whiskerRight_bimod {X Y Z : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  (N : C) [Mod_Class Y N] [RightMod_Class Z N] [MiddleAssocClass Y Z N] :
    whiskerRight Z (Bimod_Class.id X Y M) N = Bimod_Class.id X Z (M ⊗[Y] N) := by
  ext
  apply Limits.coequalizer.hom_ext
  dsimp only [tensor, whiskerRight_hom, id_hom]
  simp only [MonoidalCategory.id_whiskerRight, ι_colimMap, parallelPair_obj_one,
    parallelPairHom_app_one, Category.id_comp]
  erw [Category.comp_id]

theorem whiskerLeft_comp_bimod (X : C) {Y Z : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  {N P Q : C} [Mod_Class Y N] [RightMod_Class Z N] [MiddleAssocClass Y Z N]
  [Mod_Class Y P] [RightMod_Class Z P] [MiddleAssocClass Y Z P]
  [Mod_Class Y Q] [RightMod_Class Z Q] [MiddleAssocClass Y Z Q]
  (f : Hom Y Z N P) (g : Hom Y Z P Q) :
    whiskerLeft X M (f.comp g) = (whiskerLeft X M f).comp (whiskerLeft X M g) := by
  ext
  apply Limits.coequalizer.hom_ext
  simp

theorem id_whiskerLeft_bimod {X Y : C} [Mon_Class X] [Mon_Class Y]
  {M N : C} [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  [Mod_Class X N] [RightMod_Class Y N] [MiddleAssocClass X Y N] (f : Hom X Y M N) :
    whiskerLeft X X f =
      (leftUnitorBimod_Class M).hom.comp (f.comp (leftUnitorBimod_Class N).inv) := by
  dsimp [tensor, leftUnitorBimod_Class]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod_Class.hom]
  slice_rhs 1 2 => erw [coequalizer.π_desc]
  dsimp [LeftUnitorBimod_Class.inv]
  slice_rhs 1 2 => rw [Hom.left_act_hom]
  slice_rhs 2 3 => rw [leftUnitor_inv_naturality]
  slice_rhs 3 4 => rw [whisker_exchange]
  slice_rhs 4 4 => rw [← Iso.inv_hom_id_assoc (α_ X X N) (X ◁ ↷)]
  slice_rhs 5 7 => rw [← Category.assoc, ← coequalizer.condition]
  slice_rhs 3 4 => rw [associator_inv_naturality_left]
  slice_rhs 4 5 => rw [← comp_whiskerRight, Mon_Class.one_mul]
  have : (λ_ (X ⊗ N)).inv ≫ (α_ (𝟙_ C) X N).inv ≫ ((λ_ X).hom ▷ N) = 𝟙 _ := by
    monoidal
  slice_rhs 2 4 => rw [this]
  slice_rhs 1 2 => rw [Category.comp_id]

theorem comp_whiskerLeft_bimod {W X Y Z : C} [Mon_Class W] [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  (M : C) [Mod_Class W M] [RightMod_Class X M] [MiddleAssocClass W X M]
  (N : C) [Mod_Class X N] [RightMod_Class Y N] [MiddleAssocClass X Y N]
  {P P' : C} [Mod_Class Y P] [RightMod_Class Z P] [MiddleAssocClass Y Z P]
  [Mod_Class Y P'] [RightMod_Class Z P'] [MiddleAssocClass Y Z P']
  (f : Hom Y Z P P') :
    whiskerLeft W (M ⊗[X] N) f =
      (associatorBimod_Class M N P).hom.comp
        ((whiskerLeft _ M (whiskerLeft _ N f)).comp (associatorBimod_Class M N P').inv) := by
  dsimp [tensor, associatorBimod_Class]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [tensor, AssociatorBimod_Class.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.homAux, AssociatorBimod_Class.inv]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  rw [tensorRight_map]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.invAux]
  slice_rhs 2 2 => rw [MonoidalCategory.whiskerLeft_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_inv_naturality_right]
  slice_rhs 1 3 => rw [Iso.hom_inv_id_assoc]
  slice_lhs 1 2 => rw [← whisker_exchange]
  rfl

theorem comp_whiskerRight_bimod {X Y Z : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  {M N P : C} [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  [Mod_Class X N] [RightMod_Class Y N] [MiddleAssocClass X Y N]
  [Mod_Class X P] [RightMod_Class Y P] [MiddleAssocClass X Y P]
  (f : Hom X Y M N) (g : Hom X Y N P)
  (Q : C) [Mod_Class Y Q] [RightMod_Class Z Q] [MiddleAssocClass Y Z Q] :
    whiskerRight Z (f.comp g) Q = (whiskerRight _ f Q).comp (whiskerRight _ g Q) := by
  ext
  apply Limits.coequalizer.hom_ext
  simp

theorem whiskerRight_id_bimod {X Y : C} [Mon_Class X] [Mon_Class Y]
  {M N : C} [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  [Mod_Class X N] [RightMod_Class Y N] [MiddleAssocClass X Y N] (f : Hom X Y M N) :
    whiskerRight Y f Y =
      (rightUnitorBimod_Class M).hom.comp (f.comp (rightUnitorBimod_Class N).inv) := by
  dsimp [tensor, regular, rightUnitorBimod_Class]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod_Class.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [RightUnitorBimod_Class.inv]
  slice_rhs 1 2 => rw [Hom.right_act_hom]
  slice_rhs 2 3 => rw [rightUnitor_inv_naturality]
  slice_rhs 3 4 => rw [← whisker_exchange]
  slice_rhs 4 5 => rw [coequalizer.condition]
  slice_rhs 3 4 => rw [associator_naturality_right]
  slice_rhs 4 5 => rw [← MonoidalCategory.whiskerLeft_comp, Mon_Class.mul_one]
  simp

theorem whiskerRight_comp_bimod {W X Y Z : C}
  [Mon_Class W] [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  {M M' : C} [Mod_Class W M] [RightMod_Class X M] [MiddleAssocClass W X M]
  [Mod_Class W M'] [RightMod_Class X M'] [MiddleAssocClass W X M']
  (f : Hom W X M M') (N : C) [Mod_Class X N] [RightMod_Class Y N] [MiddleAssocClass X Y N]
  (P : C) [Mod_Class Y P] [RightMod_Class Z P] [MiddleAssocClass Y Z P] :
    whiskerRight Z f (N ⊗[Y] P) =
      (associatorBimod_Class M N P).inv.comp
        ((whiskerRight _ (whiskerRight _ f N) P).comp (associatorBimod_Class M' N P).hom) := by
  dsimp [tensor, associatorBimod_Class]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [tensor, AssociatorBimod_Class.inv]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.invAux, AssociatorBimod_Class.hom]
  refine (cancel_epi ((tensorLeft _).map (coequalizer.π _ _))).1 ?_
  rw [tensorLeft_map]
  slice_rhs 1 3 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.homAux]
  slice_rhs 2 2 => rw [comp_whiskerRight]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_naturality_left]
  slice_rhs 1 3 => rw [Iso.inv_hom_id_assoc]
  slice_lhs 1 2 => rw [whisker_exchange]
  rfl

theorem whisker_assoc_bimod {W X Y Z : C} [Mon_Class W] [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  (M : C) [Mod_Class W M] [RightMod_Class X M] [MiddleAssocClass W X M]
  {N N' : C} [Mod_Class X N] [RightMod_Class Y N] [MiddleAssocClass X Y N]
  [Mod_Class X N'] [RightMod_Class Y N'] [MiddleAssocClass X Y N']
  (f : Hom X Y N N') (P : C) [Mod_Class Y P] [RightMod_Class Z P] [MiddleAssocClass Y Z P] :
    whiskerRight Z (whiskerLeft W M f) P =
      (associatorBimod_Class M N P).hom.comp
        ((whiskerLeft _ M (whiskerRight _ f P)).comp (associatorBimod_Class M N' P).inv) := by
  dsimp [tensor, associatorBimod_Class]
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod_Class.hom]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.homAux]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  rw [tensorRight_map]
  slice_lhs 1 2 => rw [← comp_whiskerRight, ι_colimMap, parallelPairHom_app_one]
  slice_rhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, ι_colimMap, parallelPairHom_app_one]
  dsimp [AssociatorBimod_Class.inv]
  slice_rhs 3 4 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.invAux]
  slice_rhs 2 2 => rw [MonoidalCategory.whiskerLeft_comp]
  slice_rhs 3 5 => rw [id_tensor_π_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_inv_naturality_middle]
  slice_rhs 1 3 => rw [Iso.hom_inv_id_assoc]
  slice_lhs 1 1 => rw [comp_whiskerRight]
  rfl

theorem whisker_exchange_bimod {X Y Z : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  {M N : C} [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  [Mod_Class X N] [RightMod_Class Y N] [MiddleAssocClass X Y N]
  {P Q : C} [Mod_Class Y P] [RightMod_Class Z P] [MiddleAssocClass Y Z P]
  [Mod_Class Y Q] [RightMod_Class Z Q] [MiddleAssocClass Y Z Q]
  (f : Hom X Y M N) (g : Hom Y Z P Q) :
    (whiskerLeft _ M g).comp (whiskerRight _ f Q) =
      (whiskerRight _ f P).comp (whiskerLeft _ N g) := by
  ext
  apply coequalizer.hom_ext
  dsimp
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_rhs 2 3 => rw [ι_colimMap, parallelPairHom_app_one]
  simp only [Category.assoc]

set_option maxHeartbeats 400000 in
theorem pentagon_bimod {V W X Y Z : C}
  [Mon_Class V] [Mon_Class W] [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  (M : C) [Mod_Class V M] [RightMod_Class W M] [MiddleAssocClass V W M]
  (N : C) [Mod_Class W N] [RightMod_Class X N] [MiddleAssocClass W X N]
  (P : C) [Mod_Class X P] [RightMod_Class Y P] [MiddleAssocClass X Y P]
  (Q : C) [Mod_Class Y Q] [RightMod_Class Z Q] [MiddleAssocClass Y Z Q] :
    (whiskerRight Z (associatorBimod_Class M N P).hom Q).comp
      ((associatorBimod_Class M (N ⊗[X] P) Q).hom.comp
        (whiskerLeft V M (associatorBimod_Class N P Q).hom)) =
      (associatorBimod_Class (M ⊗[W] N) P Q).hom.comp
        (associatorBimod_Class M N (P ⊗[Y] Q)).hom := by
  dsimp [associatorBimod_Class]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp only [AssociatorBimod_Class.hom]
  slice_lhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 2 3 => rw [coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.homAux]
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
  dsimp only [tensor]
  slice_lhs 2 3 => rw [associator_naturality_middle]
  slice_lhs 5 6 => rw [ι_colimMap, parallelPairHom_app_one]
  slice_lhs 4 5 => rw [← MonoidalCategory.whiskerLeft_comp, coequalizer.π_desc]
  slice_lhs 3 4 =>
    rw [← MonoidalCategory.whiskerLeft_comp, π_tensor_id_preserves_coequalizer_inv_desc,
      MonoidalCategory.whiskerLeft_comp, MonoidalCategory.whiskerLeft_comp]
  slice_rhs 1 2 => rw [associator_naturality_left]
  slice_rhs 2 3 =>
    rw [← whisker_exchange]
  slice_rhs 3 5 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_rhs 2 3 => rw [associator_naturality_right]
  monoidal

theorem triangle_bimod {X Y Z : C} [Mon_Class X] [Mon_Class Y] [Mon_Class Z]
  (M : C) [Mod_Class X M] [RightMod_Class Y M] [MiddleAssocClass X Y M]
  (N : C) [Mod_Class Y N] [RightMod_Class Z N] [MiddleAssocClass Y Z N] :
    (associatorBimod_Class M Y N).hom.comp (whiskerLeft X M (leftUnitorBimod_Class N).hom) =
      whiskerRight Z (rightUnitorBimod_Class M).hom N := by
  dsimp [associatorBimod_Class, leftUnitorBimod_Class, rightUnitorBimod_Class]
  ext
  apply coequalizer.hom_ext
  dsimp
  dsimp [AssociatorBimod_Class.hom]
  slice_lhs 1 2 => rw [coequalizer.π_desc]
  dsimp [AssociatorBimod_Class.homAux]
  slice_rhs 1 2 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [RightUnitorBimod_Class.hom]
  refine (cancel_epi ((tensorRight _).map (coequalizer.π _ _))).1 ?_
  dsimp [regular]
  slice_lhs 1 3 => rw [π_tensor_id_preserves_coequalizer_inv_desc]
  slice_lhs 3 4 => rw [ι_colimMap, parallelPairHom_app_one]
  dsimp [LeftUnitorBimod_Class.hom]
  slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp, coequalizer.π_desc]
  slice_rhs 1 2 => rw [← comp_whiskerRight, coequalizer.π_desc]
  slice_rhs 1 2 => rw [coequalizer.condition]
  simp only [Category.assoc]

/-- The bicategory of algebras (monoids) and bimodules, all internal to some monoidal category. -/
noncomputable def monBicategory : Bicategory (Mon_Cat C) where
  Hom X Y := Bimod_Cat X.X Y.X
  homCategory X Y := (inferInstance : Category (Bimod_Cat X.X Y.X))
  id X := Bimod_Cat.mk X.X
  comp {_ B _} M N := Bimod_Cat.mk (M.X ⊗[B.X] N.X)
  whiskerLeft {A _ _ } L _ _ f := whiskerLeft A.X L.X f
  whiskerRight {_ _ C} _ _ f N := whiskerRight C.X f N.X
  associator _ _ _ := Bimod_Cat.ofIso (associatorBimod_Class _ _ _)
  leftUnitor _ := Bimod_Cat.ofIso (leftUnitorBimod_Class _)
  rightUnitor _ := Bimod_Cat.ofIso (rightUnitorBimod_Class _)
  whiskerLeft_id _ _ := whiskerLeft_id_bimod _ _
  whiskerLeft_comp M _ _ _ f g := whiskerLeft_comp_bimod _ M.X f g
  id_whiskerLeft := id_whiskerLeft_bimod
  comp_whiskerLeft M N _ _ f := comp_whiskerLeft_bimod M.X N.X f
  id_whiskerRight _ _ := id_whiskerRight_bimod _ _
  comp_whiskerRight f g Q := comp_whiskerRight_bimod f g Q.X
  whiskerRight_id := whiskerRight_id_bimod
  whiskerRight_comp _ _ _ := whiskerRight_comp_bimod _ _ _
  whisker_assoc M _ _ f P := whisker_assoc_bimod M.X f P.X
  whisker_exchange := whisker_exchange_bimod
  pentagon _ _ _ _ := pentagon_bimod _ _ _ _
  triangle _ _ := triangle_bimod _ _

end Bimod_Class
