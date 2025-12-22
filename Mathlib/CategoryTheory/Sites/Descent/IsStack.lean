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
In this file, we define the typeclass `F.IsStack J` saying that `F` is a stack
for `J`. (See the terminological note in the file `Sites.Descent.IsPrestack`: we
do not require that the categories `F.obj (.mk (op S))` are groupoids.)

The typeclass `IsStack` extends `IsPrestack`. The effectiveness of descent that
is required for stacks is expressed by saying that the functors `toDescentData`
attached to covering sieves are essentially surjective. Together with the
`IsPrestack` assumption, we get that these functors are actually equivalences of
categories (see `isEquivalence_toDescentData`). Conversely, we provide a
constructor `IsStack.of_isEquivalence` which assumes that these functors are
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
(See the terminological note in the introduction of the file `Sites.Descent.IsPrestack`.) -/
@[stacks 026F]
class IsStack (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) (J : GrothendieckTopology C) : Prop
    extends F.IsPrestack J where
  essSurj_of_sieve (F) {S : C} (R : Sieve S) (hR : R ∈ J S) :
    (F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)).EssSurj

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {J : GrothendieckTopology C}

lemma IsStack.isEquivalence_of_sieve [F.IsStack J] {S : C} (R : Sieve S) (hR : R ∈ J S) :
    (F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)).IsEquivalence := by
  let hF : (F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)).FullyFaithful :=
    F.fullyFaithfulToDescentData _ (by convert hR; apply Sieve.ofArrows_category)
  have := hF.full
  have := hF.faithful
  have := essSurj_of_sieve F R hR
  exact { }

lemma isEquivalence_toDescentData_iff_of_sieve_eq
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {ι' : Type t'} {X' : ι' → C} (f' : ∀ i', X' i' ⟶ S)
    (h : Sieve.ofArrows _ f = Sieve.ofArrows _ f') :
    (F.toDescentData f).IsEquivalence ↔ (F.toDescentData f').IsEquivalence := by
  obtain ⟨e, ⟨iso⟩⟩ := DescentData.exists_equivalence_of_sieve_eq F f f' h
  rw [← Functor.isEquivalence_iff_of_iso iso]
  exact ⟨fun _ ↦ inferInstance,
    fun _ ↦ Functor.isEquivalence_of_comp_right _ e.functor⟩

lemma isEquivalence_toDescentData [F.IsStack J]
    {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S) (hf : Sieve.ofArrows _ f ∈ J S) :
    (F.toDescentData f).IsEquivalence := by
  rw [← isEquivalence_toDescentData_iff_of_sieve_eq _ _ _
    (Sieve.ofArrows_category (Sieve.ofArrows _ f))]
  exact IsStack.isEquivalence_of_sieve F _ hf

variable {F} in
lemma IsStack.of_isEquivalence
    (hF : ∀ (S : C) (R : Sieve S) (_ : R ∈ J S),
      (F.toDescentData (fun (f : R.arrows.category) ↦ f.obj.hom)).IsEquivalence) :
    F.IsStack J where
  toIsPrestack := .of_fullyFaithful (fun _ _ hR ↦ by
    have := hF _ _ hR
    exact Functor.FullyFaithful.ofFullyFaithful _)
  essSurj_of_sieve _ hR := by have := hF _ _ hR; infer_instance

end Pseudofunctor

end CategoryTheory
