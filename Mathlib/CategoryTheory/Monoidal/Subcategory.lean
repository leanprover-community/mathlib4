/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-!
# Full monoidal subcategories

Given a monoidal category `C` and a property of objects `P : ObjectProperty C`
that is monoidal (i.e. it holds for the unit and is stable by `⊗`),
we can put a monoidal structure on `P.FullSubcategory` (the category
structure is defined in `Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.

## TODO
* Add monoidal/braided versions of `ObjectProperty.Lift`
-/

@[expose] public section


universe u v

namespace CategoryTheory

open MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

namespace ObjectProperty

/-- Given three properties of objects `P₁`, `P₂`, and `Q` in a monoidal
category `C`, we say `TensorLE P₁ P₂ Q` holds if the tensor product
of an object in `P₁` and an object `P₂` is necessary in `Q`,
see also `ObjectProperty.IsMonoidal`. -/
class TensorLE (P₁ P₂ Q : ObjectProperty C) : Prop where
  prop_tensor (X₁ X₂ : C) (h₁ : P₁ X₁) (h₂ : P₂ X₂) : Q (X₁ ⊗ X₂)

lemma prop_tensor {P₁ P₂ Q : ObjectProperty C} [TensorLE P₁ P₂ Q]
    {X₁ X₂ : C} (h₁ : P₁ X₁) (h₂ : P₂ X₂) : Q (X₁ ⊗ X₂) :=
  TensorLE.prop_tensor _ _ h₁ h₂

/-- This is the property that `P : ObjectProperty C` holds
for the unit of the monoidal category structure. -/
class ContainsUnit (P : ObjectProperty C) : Prop where
  prop_unit : P (𝟙_ C)

lemma prop_unit (P : ObjectProperty C) [ContainsUnit P] : P (𝟙_ C) :=
  ContainsUnit.prop_unit

/-- If `C` is a monoidal category, we say that `P : ObjectProperty C`
is monoidal if it is stable by tensor product and holds for the unit. -/
class IsMonoidal (P : ObjectProperty C) : Prop extends
  ContainsUnit P, TensorLE P P P where

/-- A property of objects is a monoidal closed if it is closed under taking internal homs
-/
class IsMonoidalClosed (P : ObjectProperty C) [MonoidalClosed C] : Prop where
  prop_ihom (X Y : C) : P X → P Y → P ((ihom X).obj Y) := by cat_disch

lemma prop_ihom (P : ObjectProperty C) [MonoidalClosed C] [P.IsMonoidalClosed]
    {X Y : C} (hX : P X) (hY : P Y) : P ((ihom X).obj Y) :=
  IsMonoidalClosed.prop_ihom _ _ hX hY

variable (P : ObjectProperty C) [P.IsMonoidal]

@[simps]
instance : MonoidalCategoryStruct P.FullSubcategory where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, prop_tensor X.2 Y.2⟩
  whiskerLeft X _ _ f := ObjectProperty.homMk (X.1 ◁ f.hom)
  whiskerRight f Y := ObjectProperty.homMk (f.hom ▷ Y.1)
  tensorHom f g := ObjectProperty.homMk (f.hom ⊗ₘ g.hom)
  tensorUnit := ⟨𝟙_ C, P.prop_unit⟩
  associator X Y Z := P.isoMk (α_ X.1 Y.1 Z.1)
  leftUnitor X := P.isoMk (λ_ X.1)
  rightUnitor X := P.isoMk (ρ_ X.1)

/--
When `P : ObjectProperty C` is monoidal, the full subcategory for `P` inherits the
monoidal structure of `C`.
-/
instance fullMonoidalSubcategory : MonoidalCategory (FullSubcategory P) :=
  Monoidal.induced P.ι
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _ }

/-- The forgetful monoidal functor from a full monoidal subcategory into the original category
("forgetting" the condition).
-/
instance monoidalι : P.ι.Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

open Functor.LaxMonoidal Functor.OplaxMonoidal

@[simp] lemma ι_ε : ε P.ι = 𝟙 _ := rfl
@[simp] lemma ι_η : ε P.ι = 𝟙 _ := rfl
@[simp] lemma ι_μ (X Y : FullSubcategory P) : μ P.ι X Y = 𝟙 _ := rfl
@[simp] lemma ι_δ (X Y : FullSubcategory P) : δ P.ι X Y = 𝟙 _ := rfl

section

variable [Preadditive C]

instance [MonoidalPreadditive C] : MonoidalPreadditive P.FullSubcategory :=
  monoidalPreadditive_of_faithful P.ι

variable (R : Type*) [Ring R] [Linear R C]

instance [MonoidalPreadditive C] [MonoidalLinear R C] : MonoidalLinear R P.FullSubcategory :=
  .ofFaithful R P.ι

end

section

variable {P} {P' : ObjectProperty C} [P'.IsMonoidal] (h : P ≤ P')

/-- An inequality `P ≤ P'` between monoidal properties of objects induces
a monoidal functor between full monoidal subcategories. -/
instance : (ιOfLE h).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _ }

@[simp] lemma ιOfLE_ε : ε (ιOfLE h) = 𝟙 _ := rfl
@[simp] lemma ιOfLE_η : η (ιOfLE h) = 𝟙 _ := rfl
@[simp] lemma ιOfLE_μ (X Y : P.FullSubcategory) : μ (ιOfLE h) X Y = 𝟙 _ := rfl
@[simp] lemma ιOfLE_δ (X Y : FullSubcategory P) : δ (ιOfLE h) X Y = 𝟙 _ := rfl

end

section Braided

variable [BraidedCategory C]

/-- The braided structure on a full subcategory inherited by the braided structure on `C`.
-/
instance fullBraidedSubcategory : BraidedCategory (FullSubcategory P) :=
  .ofFaithful P.ι fun X Y ↦ P.isoMk (β_ X.1 Y.1)

/-- The forgetful braided functor from a full braided subcategory into the original category
("forgetting" the condition).
-/
instance : P.ι.Braided where

variable {P}

/-- An inequality `P ≤ P'` between monoidal properties of objects induces
a braided functor between full braided subcategories. -/
instance {P' : ObjectProperty C} [P'.IsMonoidal] (h : P ≤ P') :
    (ιOfLE h).Braided where

end Braided

section Symmetric

variable [SymmetricCategory C]

instance fullSymmetricSubcategory : SymmetricCategory P.FullSubcategory :=
  .ofFaithful P.ι

end Symmetric

section Closed

variable [MonoidalClosed C] [P.IsMonoidalClosed]

set_option backward.isDefEq.respectTransparency false in
instance fullMonoidalClosedSubcategory : MonoidalClosed (FullSubcategory P) where
  closed X :=
    { rightAdj := P.lift (P.ι ⋙ ihom X.1) (fun Y => P.prop_ihom X.2 Y.2)
      adj :=
        { unit := { app Y := ObjectProperty.homMk ((ihom.coev X.1).app Y.1) }
          counit := { app Y := ObjectProperty.homMk ((ihom.ev X.1).app Y.1) } } }

@[simp]
theorem ihom_obj (X Y : P.FullSubcategory) :
    ((ihom X).obj Y).obj = (ihom X.obj).obj Y.obj :=
  rfl

@[simp]
theorem ihom_map_hom (X : P.FullSubcategory) {Y Z : P.FullSubcategory}
    (f : Y ⟶ Z) : ((ihom X).map f).hom = (ihom X.obj).map f.hom :=
  rfl

@[deprecated (since := "2025-12-18")] alias ihom_map := ihom_map_hom

end Closed

end ObjectProperty

end CategoryTheory
