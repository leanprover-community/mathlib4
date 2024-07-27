/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Monoidal.Transport
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Closed.Monoidal

/-!
# Full monoidal subcategories

Given a monoidal category `C` and a monoidal predicate on `C`, that is a function `P : C → Prop`
closed under `𝟙_` and `⊗`, we can put a monoidal structure on `{X : C // P X}` (the category
structure is defined in `Mathlib.CategoryTheory.FullSubcategory`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.

## TODO
* Add monoidal/braided versions of `CategoryTheory.FullSubcategory.Lift`
-/


universe u v

namespace CategoryTheory

namespace MonoidalCategory

open Iso

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (P : C → Prop)

/-- A property `C → Prop` is a monoidal predicate if it is closed under `𝟙_` and `⊗`.
-/
class MonoidalPredicate : Prop where
  prop_id : P (𝟙_ C) := by aesop_cat
  prop_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y) := by aesop_cat

open MonoidalPredicate

variable [MonoidalPredicate P]

@[simps]
instance : MonoidalCategoryStruct (FullSubcategory P) where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, prop_tensor X.2 Y.2⟩
  whiskerLeft X _ _ f := { hom := X.1 ◁ f.hom }
  whiskerRight f Y := { hom := f.hom ▷ Y.1 }
  tensorHom f g := { hom := f.hom ⊗ g.hom }
  tensorUnit := ⟨𝟙_ C, prop_id⟩
  associator _ _ _ := FullSubcategory.isoMk (α_ _ _ _)
  leftUnitor _ := FullSubcategory.isoMk (λ_ _)
  rightUnitor _ := FullSubcategory.isoMk (ρ_ _)

/--
When `P` is a monoidal predicate, the full subcategory for `P` inherits the monoidal structure of
  `C`.
-/
instance fullMonoidalSubcategory : MonoidalCategory (FullSubcategory P) :=
  Monoidal.induced (fullSubcategoryInclusion P)
    { μIso := fun X Y => Iso.refl _
      εIso := Iso.refl _ }

/-- The forgetful monoidal functor from a full monoidal subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def fullMonoidalSubcategoryInclusion : MonoidalFunctor (FullSubcategory P) C where
  toFunctor := fullSubcategoryInclusion P
  ε := 𝟙 _
  μ X Y := 𝟙 _

instance fullMonoidalSubcategory.full : (fullMonoidalSubcategoryInclusion P).Full :=
  FullSubcategory.full P

instance fullMonoidalSubcategory.faithful :
    (fullMonoidalSubcategoryInclusion P).Faithful :=
  FullSubcategory.faithful P

section

variable [Preadditive C]

instance fullMonoidalSubcategoryInclusion_additive :
    (fullMonoidalSubcategoryInclusion P).toFunctor.Additive :=
  Functor.fullSubcategoryInclusion_additive _

instance [MonoidalPreadditive C] : MonoidalPreadditive (FullSubcategory P) :=
  monoidalPreadditive_of_faithful (fullMonoidalSubcategoryInclusion P)

variable (R : Type*) [Ring R] [Linear R C]

instance fullMonoidalSubcategoryInclusion_linear :
    (fullMonoidalSubcategoryInclusion P).toFunctor.Linear R :=
  Functor.fullSubcategoryInclusionLinear R _

instance [MonoidalPreadditive C] [MonoidalLinear R C] : MonoidalLinear R (FullSubcategory P) :=
  monoidalLinearOfFaithful R (fullMonoidalSubcategoryInclusion P)

end

variable {P} {P' : C → Prop} [MonoidalPredicate P']

/-- An implication of predicates `P → P'` induces a monoidal functor between full monoidal
subcategories. -/
@[simps]
def fullMonoidalSubcategory.map (h : ∀ ⦃X⦄, P X → P' X) :
    MonoidalFunctor (FullSubcategory P) (FullSubcategory P') where
  toFunctor := FullSubcategory.map h
  ε := 𝟙 _
  μ X Y := 𝟙 _

/-- The inclusion functor between two full monoidal subcategories is fully faithful. -/
def fullMonoidalSubcategory.fullyFaithfulMap (h : ∀ ⦃X⦄, P X → P' X) :
    (fullMonoidalSubcategory.map h).FullyFaithful :=
  FullSubcategory.fullyFaithfulMap _

instance fullMonoidalSubcategory.map_full (h : ∀ ⦃X⦄, P X → P' X) :
    (fullMonoidalSubcategory.map h).Full :=
  (fullyFaithfulMap h).full

instance fullMonoidalSubcategory.map_faithful (h : ∀ ⦃X⦄, P X → P' X) :
    (fullMonoidalSubcategory.map h).Faithful :=
  (fullyFaithfulMap h).faithful

section Braided

variable (P) [BraidedCategory C]

/-- The braided structure on a full subcategory inherited by the braided structure on `C`.
-/
instance fullBraidedSubcategory : BraidedCategory (FullSubcategory P) :=
  braidedCategoryOfFaithful (fullMonoidalSubcategoryInclusion P)
    (fun X Y ↦ FullSubcategory.isoMk (β_ _ _)) (by aesop_cat)

/-- The forgetful braided functor from a full braided subcategory into the original category
("forgetting" the condition).
-/
@[simps!]
def fullBraidedSubcategoryInclusion : BraidedFunctor (FullSubcategory P) C where
  toMonoidalFunctor := fullMonoidalSubcategoryInclusion P
  braided X Y := by rw [IsIso.eq_inv_comp]; aesop_cat

instance fullBraidedSubcategory.full : (fullBraidedSubcategoryInclusion P).Full :=
  fullMonoidalSubcategory.full P

instance fullBraidedSubcategory.faithful : (fullBraidedSubcategoryInclusion P).Faithful :=
  fullMonoidalSubcategory.faithful P

variable {P}

/-- An implication of predicates `P → P'` induces a braided functor between full braided
subcategories. -/
@[simps!]
def fullBraidedSubcategory.map (h : ∀ ⦃X⦄, P X → P' X) :
    BraidedFunctor (FullSubcategory P) (FullSubcategory P') where
  toMonoidalFunctor := fullMonoidalSubcategory.map h
  braided X Y := by rw [IsIso.eq_inv_comp]; aesop_cat

instance fullBraidedSubcategory.mapFull (h : ∀ ⦃X⦄, P X → P' X) :
    (fullBraidedSubcategory.map h).Full :=
  fullMonoidalSubcategory.map_full h

instance fullBraidedSubcategory.map_faithful (h : ∀ ⦃X⦄, P X → P' X) :
    (fullBraidedSubcategory.map h).Faithful :=
  fullMonoidalSubcategory.map_faithful h

end Braided

section Symmetric

variable (P) [SymmetricCategory C]

instance fullSymmetricSubcategory : SymmetricCategory (FullSubcategory P) :=
  symmetricCategoryOfFaithful (fullBraidedSubcategoryInclusion P)

end Symmetric

section Closed

variable (P) [MonoidalClosed C]

/-- A property `C → Prop` is a closed predicate if it is closed under taking internal homs
-/
class ClosedPredicate : Prop where
  prop_ihom : ∀ {X Y}, P X → P Y → P ((ihom X).obj Y) := by aesop_cat

open ClosedPredicate

variable [ClosedPredicate P]

instance fullMonoidalClosedSubcategory : MonoidalClosed (FullSubcategory P) where
  closed X :=
    { rightAdj := FullSubcategory.lift P (fullSubcategoryInclusion P ⋙ ihom X.1)
        fun Y => prop_ihom X.2 Y.2
      adj :=
        Adjunction.mkOfUnitCounit
        { unit :=
          { app := fun Y => { hom := (ihom.coev X.1).app Y.1 }
            naturality := fun Y Z f => by ext; exact ihom.coev_naturality X.1 f.hom }
          counit :=
          { app := fun Y => { hom := (ihom.ev X.1).app Y.1 }
            naturality := fun Y Z f => by ext; exact ihom.ev_naturality X.1 f.hom } } }

@[simp]
theorem fullMonoidalClosedSubcategory_ihom_obj (X Y : FullSubcategory P) :
    ((ihom X).obj Y).obj = (ihom X.obj).obj Y.obj :=
  rfl

@[simp]
theorem fullMonoidalClosedSubcategory_ihom_map_hom
    (X : FullSubcategory P) {Y Z : FullSubcategory P} (f : Y ⟶ Z) :
    ((ihom X).map f).hom = (ihom X.obj).map f.hom :=
  rfl

end Closed

end MonoidalCategory

end CategoryTheory
