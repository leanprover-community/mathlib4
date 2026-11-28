/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.CategoryTheory.Yoneda

/-!
# Chosen (co)representations of functors to `Type`

This file defines typeclasses for chosen (co)representations of functors to `Type*`.

In **Type**, every element `x : X` of every type `X` can be uniquely represented as a morphism
`homOfElement x : PUnit ⟶ X`. This can be thought of as a canonical choice of corepresenting object
for the forgetful functor, which in the case of `Type*` is just the identity. Generalizing, we can
define such a `homOfElement` any time we have a `ChosenCorepresentation` of a functor, and dually,
we can define a `homFromElement` any time we have a `ChosenRepresentation` of a functor.

This file provides typeclasses and convenience API for working with chosen (co)representations of
arbitrary functors. See `Mathlib.CategoryTheory.ConcreteCategory.Representable` for a
specialization to the important case where the category is concrete and the functor is the
canonical forgetful functor to `Type*`.

### Main definitions:
* `Chosen(Co)Representation`: a data-carrying typeclass holding a canonical choice of
(co)-representing object and its corresponding canonical assignment of elements to morphisms.
* `F.(co)reprObj` and `F.(co)univ` : the chosen (co)-representing object and the corresponding
universal element.
* `F.homFromElement` and `F.homOfElement` : the canonical morphisms induced by elements via the
chosen (co)representation.

### Future work
* Reimplement `CategoryTheory.homOfElement` using `(𝟭 TypeCat).homOfElement`.
  * Provide instances for common categories, such as `Type*`, `TopCat`, `Cat`.
* Refactor `Mathlib.Algebra.Category.Grp.ForgetCorepresentable` and the work that depends on it
  to use `ChosenCorepresentation`.
* Once the upstream `CategoryTheory` files have been `to_dual`-ified, we can refactor this file
  to use `to_dual` as well.

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Functor
open Opposite

variable {C : Type*} [Category* C]

/-- Data typeclass for a chosen representation of a functor. -/
class ChosenRepresentation (F : Cᵒᵖ ⥤ Type*) where
  /-- The representing object of the chosen representation. -/
  obj : C
  /-- The natural equivalence of hom-types witnessing that `F` is representable by `obj`. -/
  reprBy : F.RepresentableBy obj

@[inherit_doc ChosenRepresentation.obj]
abbrev reprObj (F : Cᵒᵖ ⥤ Type*) [c : ChosenRepresentation F] : C := c.obj

@[inherit_doc ChosenRepresentation.obj]
def ChosenRepresentation.Simps.reprObj (F : Cᵒᵖ ⥤ Type*) [c : ChosenRepresentation F] : C :=
  F.reprObj

initialize_simps_projections ChosenRepresentation (obj → reprObj)

section
variable (F : Cᵒᵖ ⥤ Type*) [c : ChosenRepresentation F] {Z : C} (z z₁ z₂ : F.obj (op Z))

/-- The chosen universal element, that represents `𝟙 F.reprObj`. -/
def univ : F.obj (op F.reprObj) := c.reprBy.homEquiv (𝟙 _)

/-- The unique morphism `F.obj (op Z) ⟶ F.reprObj` induced by an `z : F.obj (op Z)`. -/
def homFromElement {Z : C} (z : F.obj (op Z)) : Z ⟶ F.reprObj := c.reprBy.homEquiv.symm z

@[reassoc (attr := simp), elementwise (attr := simp)]
lemma homFromElement_comp {X Y : C} (y : F.obj (op Y)) (f : X ⟶ Y) :
    f ≫ F.homFromElement y = F.homFromElement (F.map (op f) y) :=
  c.reprBy.comp_homEquiv_symm ..

lemma homFromElement_injective :
    Function.Injective (F.homFromElement : F.obj (op Z) → (Z ⟶ F.reprObj)) :=
  c.reprBy.homEquiv.symm.injective

lemma homFromElement_inj : F.homFromElement z₁ = F.homFromElement z₂ ↔ z₁ = z₂ :=
  c.reprBy.homEquiv.symm.injective.eq_iff

@[simp] lemma homFromElement_univ : F.homFromElement F.univ = 𝟙 _ := by
  simp [homFromElement, univ]

@[simp]
lemma map_homFromElement_apply : F.map (op (F.homFromElement z)) F.univ = z := by
  apply homFromElement_injective
  rw [← homFromElement_comp, homFromElement_univ, Category.comp_id]

/-- Convenience version of `map_homFromElement_apply` in the case when `F.reprObj` is
a unique type. -/
@[simp]
lemma map_homFromElement_apply' [Unique (F.obj (op F.reprObj))]
    (a : F.obj (op F.reprObj)) : F.map (op (F.homFromElement z)) a = z := by
  rw [Unique.eq_default a, Unique.default_eq F.univ, map_homFromElement_apply]

end

/-- Data typeclass for a chosen corepresentation of a functor. -/
class ChosenCorepresentation (F : C ⥤ Type*) where
  /-- The corepresenting object of the chosen corepresentation. -/
  obj : C
  /-- The natural equivalence of hom-types witnessing that `F` is corepresentable by `obj`. -/
  coreprBy : F.CorepresentableBy obj

@[inherit_doc ChosenCorepresentation.obj]
abbrev coreprObj (F : C ⥤ Type*) [c : ChosenCorepresentation F] : C := c.obj

@[inherit_doc ChosenCorepresentation.obj]
def ChosenCorepresentation.Simps.coreprObj (F : C ⥤ Type*) [c : ChosenCorepresentation F] : C :=
  F.coreprObj

initialize_simps_projections ChosenCorepresentation (obj → coreprObj)

section
variable (F : C ⥤ Type*) [c : ChosenCorepresentation F] {Z : C} (z z₁ z₂ : F.obj Z)

/-- The chosen universal element, that co-represents `𝟙 F.coreprObj`. -/
def couniv : F.obj F.coreprObj := c.coreprBy.homEquiv (𝟙 _)

/-- The unique morphism `F.coreprObj ⟶ Z` induced by an element `z : F.obj Z`. -/
def homOfElement {Z : C} (z : F.obj Z) : F.coreprObj ⟶ Z := c.coreprBy.homEquiv.symm z

@[simp, reassoc, elementwise (attr := simp)]
lemma homOfElement_comp {X Y : C} (x : F.obj X) (f : X ⟶ Y) :
    F.homOfElement x ≫ f = F.homOfElement (F.map f x) :=
  c.coreprBy.homEquiv_symm_comp ..

lemma homOfElement_injective :
    Function.Injective (F.homOfElement : F.obj Z → (F.coreprObj ⟶ Z)) :=
  c.coreprBy.homEquiv.symm.injective

lemma homOfElement_inj : F.homOfElement z₁ = F.homOfElement z₂ ↔ z₁ = z₂ :=
  c.coreprBy.homEquiv.symm.injective.eq_iff

@[simp] lemma homOfElement_univ : F.homOfElement F.couniv = 𝟙 _ := by
  simp [homOfElement, couniv]

@[simp]
lemma map_homOfElement_apply : F.map (F.homOfElement z) F.couniv = z := by
  apply homOfElement_injective
  rw [← homOfElement_comp, homOfElement_univ, Category.id_comp]

/-- Convenience version of `map_homOfElement_apply` in the common case when `F.coreprObj` is
a unique type. In particular, this is true of `forget C` for many concrete categories `C`,
including `Type` itself. -/
@[simp]
lemma map_homOfElement_apply' [Unique (F.obj F.coreprObj)]
    (a : F.obj F.coreprObj) : F.map (F.homOfElement z) a = z := by
  rw [Unique.eq_default a, Unique.default_eq F.couniv, map_homOfElement_apply]

end

end CategoryTheory.Functor
