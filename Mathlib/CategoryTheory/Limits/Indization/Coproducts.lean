/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.CategoryTheory.Limits.Indization.Category
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Constructions.Filtered

/-!
# Coproducts in the category of Ind-objects

We show that if `C` has finite coproducts, then `Ind C` has small coproducts. It is shown in
`CategoryTheory.Limits.Indization.Category` that the functor `C ⥤ Ind C` preserves finite
coproducts.

It is not true that the functors `C ⥤ Ind C` or `Ind C ⥤ Cᵒᵖ ⥤ Type v` preserve coproducts in
general.

We deduce that if `C` has finite coproducts, and `Ind C` has small coproducts.

## Implementation notes

Our proof is inspired by the one in [Kashiwara2006], but instead of arguing via
`Limits.Cones.isColimitYonedaEquiv` as is done in the book, we invoke the already-established fact
that `Ind.yoneda` preserves finite colimits, which shortens the proof considerably.

## References
* [M. Kashiwara, P. Schapira, *Categories and Sheaves*][Kashiwara2006], Prop. 6.1.18
-/

universe w v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section

variable {α : Type v} [Finite α]

instance [HasColimitsOfShape (Discrete α) C] : HasColimitsOfShape (Discrete α) (Ind C) := by
  refine ⟨fun F => ?_⟩
  let I : α → Type v := fun s => (F.obj ⟨s⟩).presentation.I
  let G : ∀ s, I s ⥤ C := fun s => (F.obj ⟨s⟩).presentation.F
  let iso : Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
      (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim ≅ F := by
    refine Discrete.natIso (fun s => ?_)
    refine (Functor.Final.colimitIso (Pi.eval I s.as) (G s.as ⋙ Ind.yoneda)) ≪≫ ?_
    exact Ind.colimitPresentationCompYoneda _
  -- The actual proof happens during typeclass resolution in the following line, which deduces
  -- ```
  -- HasColimit Discrete.functor (fun s => Pi.eval I s ⋙ G s) ⋙
  --    (whiskeringRight _ _ _).obj Ind.yoneda ⋙ colim
  -- ```
  -- from the fact that finite limits commute with filtered colimits and from the fact that
  -- `Ind.yoneda` preserves finite colimits.
  apply hasColimitOfIso iso.symm

end

instance [HasFiniteCoproducts C] : HasCoproducts.{v} (Ind C) :=
  have : HasFiniteCoproducts (Ind C) :=
    ⟨fun _ => hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)⟩
  hasCoproducts_of_finite_and_filtered

end CategoryTheory.Limits
