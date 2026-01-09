/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Stacks: effectiveness of descent

Let `C` be a category with a Grothendieck topology `J` and `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`.
In this file, we define the typeclass `F.IsStack J` saying that `F` is a stack for `J`.
(See the terminological note in the file `Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean`:
we do not require that the categories `F.obj (.mk (op S))` are groupoids.)

The typeclass `IsStack` extends `IsPrestack`. The effectiveness of descent that
is required for stacks is expressed by saying that the functors `toDescentData`
attached to covering sieves are essentially surjective. Together with the
`IsPrestack` assumption, we get that these functors are actually equivalences of
categories (see `isEquivalence_toDescentData`). Conversely, we provide a
constructor `IsStack.of_isStackFor` which assumes that these functors are
equivalences of categories.

## References
* [Jean Giraud, *Cohomologie non abélienne*][giraud1971]
* [Gérard Laumon and Laurent Moret-Bailly, *Champs algébriques*][laumon-morel-bailly-2000]

-/

@[expose] public section

universe t t' v' v u' u

namespace CategoryTheory

open Bicategory

namespace Pseudofunctor

variable {C : Type u} [Category.{v} C]

/-- The property that a pseudofunctor `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat`
has effective descent for a Grothendieck topology, i.e. is a stack.
(See the terminological note in the introduction of the file
`Mathlib/CategoryTheory/Sites/Descent/IsPrestack.lean`.) -/
@[stacks 026F]
class IsStack (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : GrothendieckTopology C) : Prop
    extends F.IsPrestack J where
  essSurj_of_sieve (F) {S : C} (R : Sieve S) (hR : R ∈ J S) :
    (F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)).EssSurj

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {J : GrothendieckTopology C}

/-- Version of `isStackFor` for a sieve instead of a presieve. -/
lemma isStackFor' [F.IsStack J] {S : C} (R : Sieve S) (hR : R ∈ J S) :
    F.IsStackFor R.arrows := by
  rw [isStackFor_iff]
  have hF := (F.isPrestackFor' _ hR).fullyFaithful
  have := hF.full
  have := hF.faithful
  have := IsStack.essSurj_of_sieve F _ hR
  exact { }

lemma isStackFor [F.IsStack J] {S : C} (R : Presieve S) (hR : Sieve.generate R ∈ J S) :
    F.IsStackFor R := by
  simpa using F.isStackFor' _ hR

lemma isEquivalence_toDescentData [F.IsStack J]
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) :
    (F.toDescentData f).IsEquivalence := by
  rw [← isStackFor_ofArrows_iff, ← IsStackFor_generate_iff]
  exact F.isStackFor _ (by simpa)

variable {F} in
lemma IsStack.of_isStackFor
    (hF : ∀ (S : C) (R : Sieve S) (_ : R ∈ J S), F.IsStackFor R.arrows) :
    F.IsStack J where
  toIsPrestack := .of_isPrestackFor (fun _ _ hR ↦ (hF _ _ hR).isPrestackFor)
  essSurj_of_sieve R hR := by
    have := (isStackFor_iff _ _).1 (hF _ _ hR)
    infer_instance

end Pseudofunctor

end CategoryTheory
