/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import Mathlib.CategoryTheory.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Closed.Monoidal

#align_import category_theory.monoidal.subcategory from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

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
#align category_theory.monoidal_category.monoidal_predicate CategoryTheory.MonoidalCategory.MonoidalPredicate

open MonoidalPredicate

variable [MonoidalPredicate P]

/--
When `P` is a monoidal predicate, the full subcategory for `P` inherits the monoidal structure of
  `C`.
-/
instance fullMonoidalSubcategory : MonoidalCategory (FullSubcategory P) where
  tensorObj X Y := ⟨X.1 ⊗ Y.1, prop_tensor X.2 Y.2⟩
  tensorHom f g := ⟨f.hom ⊗ g.hom⟩
  tensorHom_def _f _g := FullSubcategory.hom_ext <| tensorHom_def _ _
  whiskerLeft := fun X _ _ f ↦ ⟨X.1 ◁ f.hom⟩
  whiskerRight := fun f Y ↦ ⟨f.hom ▷ Y.1⟩
  tensorUnit' := ⟨𝟙_ C, prop_id⟩
  associator X Y Z := (fullSubcategoryInclusion P).preimageIso (α_ X.1 Y.1 Z.1)
  whiskerLeft_id X Y := FullSubcategory.hom_ext <| whiskerLeft_id X.1 Y.1
  id_whiskerRight X Y := FullSubcategory.hom_ext <| id_whiskerRight X.1 Y.1
  leftUnitor X := (fullSubcategoryInclusion P).preimageIso (λ_ X.1)
  rightUnitor X := (fullSubcategoryInclusion P).preimageIso (ρ_ X.1)
  tensor_id X Y := FullSubcategory.hom_ext <| tensor_id X.1 Y.1
  tensor_comp _f₁ _f₂ _g₁ _g₂ := FullSubcategory.hom_ext <| tensor_comp _ _ _ _
  associator_naturality _f₁ _f₂ _f₃ := FullSubcategory.hom_ext <| associator_naturality _ _ _
  leftUnitor_naturality _f := FullSubcategory.hom_ext <| leftUnitor_naturality _
  rightUnitor_naturality _f := FullSubcategory.hom_ext <| rightUnitor_naturality _
  pentagon W X Y Z := FullSubcategory.hom_ext <| pentagon W.1 X.1 Y.1 Z.1
  triangle X Y := FullSubcategory.hom_ext <| triangle X.1 Y.1
#align category_theory.monoidal_category.full_monoidal_subcategory CategoryTheory.MonoidalCategory.fullMonoidalSubcategory

/-- The forgetful monoidal functor from a full monoidal subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def fullMonoidalSubcategoryInclusion : MonoidalFunctor (FullSubcategory P) C where
  toFunctor := fullSubcategoryInclusion P
  ε := 𝟙 _
  μ X Y := 𝟙 _
#align category_theory.monoidal_category.full_monoidal_subcategory_inclusion CategoryTheory.MonoidalCategory.fullMonoidalSubcategoryInclusion

instance fullMonoidalSubcategory.full : Full (fullMonoidalSubcategoryInclusion P).toFunctor :=
  FullSubcategory.full P
#align category_theory.monoidal_category.full_monoidal_subcategory.full CategoryTheory.MonoidalCategory.fullMonoidalSubcategory.full

instance fullMonoidalSubcategory.faithful :
    Faithful (fullMonoidalSubcategoryInclusion P).toFunctor :=
  FullSubcategory.faithful P
#align category_theory.monoidal_category.full_monoidal_subcategory.faithful CategoryTheory.MonoidalCategory.fullMonoidalSubcategory.faithful

section

variable [Preadditive C]

instance fullMonoidalSubcategoryInclusion_additive :
    (fullMonoidalSubcategoryInclusion P).toFunctor.Additive :=
  Functor.fullSubcategoryInclusion_additive _
#align category_theory.monoidal_category.full_monoidal_subcategory_inclusion_additive CategoryTheory.MonoidalCategory.fullMonoidalSubcategoryInclusion_additive

instance [MonoidalPreadditive C] : MonoidalPreadditive (FullSubcategory P) :=
  monoidalPreadditive_of_faithful (fullMonoidalSubcategoryInclusion P)

variable (R : Type*) [Ring R] [Linear R C]

instance fullMonoidalSubcategoryInclusion_linear :
    (fullMonoidalSubcategoryInclusion P).toFunctor.Linear R :=
  Functor.fullSubcategoryInclusionLinear R _
#align category_theory.monoidal_category.full_monoidal_subcategory_inclusion_linear CategoryTheory.MonoidalCategory.fullMonoidalSubcategoryInclusion_linear

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
#align category_theory.monoidal_category.full_monoidal_subcategory.map CategoryTheory.MonoidalCategory.fullMonoidalSubcategory.map

instance fullMonoidalSubcategory.mapFull (h : ∀ ⦃X⦄, P X → P' X) :
    Full (fullMonoidalSubcategory.map h).toFunctor :=
  inferInstanceAs <| Full (FullSubcategory.map h)
#align category_theory.monoidal_category.full_monoidal_subcategory.map_full CategoryTheory.MonoidalCategory.fullMonoidalSubcategory.mapFull

instance fullMonoidalSubcategory.map_faithful (h : ∀ ⦃X⦄, P X → P' X) :
    Faithful (fullMonoidalSubcategory.map h).toFunctor :=
  inferInstanceAs <| Faithful (FullSubcategory.map h)
#align category_theory.monoidal_category.full_monoidal_subcategory.map_faithful CategoryTheory.MonoidalCategory.fullMonoidalSubcategory.map_faithful

section Braided

variable (P) [BraidedCategory C]

/-- The braided structure on a full subcategory inherited by the braided structure on `C`.
-/
instance fullBraidedSubcategory : BraidedCategory (FullSubcategory P) :=
  braidedCategoryOfFaithful (fullMonoidalSubcategoryInclusion P)
    (fun X Y => (fullSubcategoryInclusion P).preimageIso (β_ X.1 Y.1))
    fun X Y => by aesop_cat
#align category_theory.monoidal_category.full_braided_subcategory CategoryTheory.MonoidalCategory.fullBraidedSubcategory

/-- The forgetful braided functor from a full braided subcategory into the original category
("forgetting" the condition).
-/
@[simps!]
def fullBraidedSubcategoryInclusion : BraidedFunctor (FullSubcategory P) C where
  toMonoidalFunctor := fullMonoidalSubcategoryInclusion P
  braided X Y := by rw [IsIso.eq_inv_comp]; aesop_cat
#align category_theory.monoidal_category.full_braided_subcategory_inclusion CategoryTheory.MonoidalCategory.fullBraidedSubcategoryInclusion

instance fullBraidedSubcategory.full : Full (fullBraidedSubcategoryInclusion P).toFunctor :=
  fullMonoidalSubcategory.full P
#align category_theory.monoidal_category.full_braided_subcategory.full CategoryTheory.MonoidalCategory.fullBraidedSubcategory.full

instance fullBraidedSubcategory.faithful : Faithful (fullBraidedSubcategoryInclusion P).toFunctor :=
  fullMonoidalSubcategory.faithful P
#align category_theory.monoidal_category.full_braided_subcategory.faithful CategoryTheory.MonoidalCategory.fullBraidedSubcategory.faithful

variable {P}

/-- An implication of predicates `P → P'` induces a braided functor between full braided
subcategories. -/
@[simps!]
def fullBraidedSubcategory.map (h : ∀ ⦃X⦄, P X → P' X) :
    BraidedFunctor (FullSubcategory P) (FullSubcategory P') where
  toMonoidalFunctor := fullMonoidalSubcategory.map h
  braided X Y := by rw [IsIso.eq_inv_comp]; aesop_cat
#align category_theory.monoidal_category.full_braided_subcategory.map CategoryTheory.MonoidalCategory.fullBraidedSubcategory.map

instance fullBraidedSubcategory.mapFull (h : ∀ ⦃X⦄, P X → P' X) :
    Full (fullBraidedSubcategory.map h).toFunctor :=
  fullMonoidalSubcategory.mapFull h
#align category_theory.monoidal_category.full_braided_subcategory.map_full CategoryTheory.MonoidalCategory.fullBraidedSubcategory.mapFull

instance fullBraidedSubcategory.map_faithful (h : ∀ ⦃X⦄, P X → P' X) :
    Faithful (fullBraidedSubcategory.map h).toFunctor :=
  fullMonoidalSubcategory.map_faithful h
#align category_theory.monoidal_category.full_braided_subcategory.map_faithful CategoryTheory.MonoidalCategory.fullBraidedSubcategory.map_faithful

end Braided

section Symmetric

variable (P) [SymmetricCategory C]

instance fullSymmetricSubcategory : SymmetricCategory (FullSubcategory P) :=
  symmetricCategoryOfFaithful (fullBraidedSubcategoryInclusion P)
#align category_theory.monoidal_category.full_symmetric_subcategory CategoryTheory.MonoidalCategory.fullSymmetricSubcategory

end Symmetric

section Closed

variable (P) [MonoidalClosed C]

/-- A property `C → Prop` is a closed predicate if it is closed under taking internal homs
-/
class ClosedPredicate : Prop where
  prop_ihom : ∀ {X Y}, P X → P Y → P ((ihom X).obj Y) := by aesop_cat
#align category_theory.monoidal_category.closed_predicate CategoryTheory.MonoidalCategory.ClosedPredicate

open ClosedPredicate

variable [ClosedPredicate P]

instance fullMonoidalClosedSubcategory : MonoidalClosed (FullSubcategory P) where
  closed X :=
  { isAdj :=
    { right :=
        FullSubcategory.lift P (fullSubcategoryInclusion P ⋙ ihom X.1) fun Y => prop_ihom X.2 Y.2
      adj :=
        Adjunction.mkOfUnitCounit
        { unit :=
          { app := fun Y => ⟨(ihom.coev X.1).app Y.1⟩
            naturality := fun Y Z f => FullSubcategory.hom_ext <| ihom.coev_naturality X.1 f.1 }
          counit :=
          { app := fun Y => ⟨(ihom.ev X.1).app Y.1⟩
            naturality := fun Y Z f => FullSubcategory.hom_ext <| ihom.ev_naturality X.1 f.1 }
          left_triangle := by ext Y; simp; exact ihom.ev_coev X.1 Y.1
          right_triangle := by ext Y; simp } } }
#align category_theory.monoidal_category.full_monoidal_closed_subcategory CategoryTheory.MonoidalCategory.fullMonoidalClosedSubcategory

@[simp]
theorem fullMonoidalClosedSubcategory_ihom_obj (X Y : FullSubcategory P) :
    ((ihom X).obj Y).obj = (ihom X.obj).obj Y.obj :=
  rfl
#align category_theory.monoidal_category.full_monoidal_closed_subcategory_ihom_obj CategoryTheory.MonoidalCategory.fullMonoidalClosedSubcategory_ihom_obj

@[simp]
theorem fullMonoidalClosedSubcategory_ihom_map (X : FullSubcategory P) {Y Z : FullSubcategory P}
    (f : Y ⟶ Z) : ((ihom X).map f).hom = (ihom X.obj).map f.hom :=
  rfl
#align category_theory.monoidal_category.full_monoidal_closed_subcategory_ihom_map CategoryTheory.MonoidalCategory.fullMonoidalClosedSubcategory_ihom_map

end Closed

end MonoidalCategory

end CategoryTheory
