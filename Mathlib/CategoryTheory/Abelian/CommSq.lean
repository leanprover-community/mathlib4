/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Preadditive.CommSq

/-!
# The exact sequence attached to a pushout square

Given a pushout square in an abelian category
```
   t
W --> X
|     |
|l    |r
v     v
Y --> Z
   b
```
we consider the associated exact sequence `W ⟶ Y ⊞ X ⟶ Z ⟶ 0`.

-/

universe v u

namespace CategoryTheory

open Category Limits

namespace IsPushout

variable {C : Type u} [Category.{v} C] [Abelian C] {W X Y Z : C}
  {t : W ⟶ X} {l : W ⟶ Y} {r : X ⟶ Z} {b : Y ⟶ Z}

/-- Given a pushout square in an abelian category
```
   t
W --> X
|     |
|l    |r
v     v
Y --> Z
   b
```
there is an exact short complex `W ⟶ Y ⊞ X ⟶ Z`,
where the left map is a difference and the right map a sum. -/
lemma shortComplex_exact (h : IsPushout t l r b) : h.shortComplex.Exact :=
  h.shortComplex.exact_of_g_is_cokernel
    h.isColimitCokernelCofork

/-- Given a pushout square in an abelian category
```
   t
W --> X
|     |
|l    |r
v     v
Y --> Z
   b
```
the morphism `Y ⊞ X ⟶ Z` is an epimorphism. This lemma translates this
as the existence of liftings up to refinements: a morphism `z : T ⟶ Z`
can be written as a sum of a morphism to `Y` and a morphism to `X`,
at least if we allow a precomposition with an epimorphism `π : T' ⟶ T`. -/
lemma hom_eq_add_up_to_refinements (h : IsPushout t l r b) {T : C} (z : T ⟶ Z) :
    ∃ (T' : C) (π : T' ⟶ T) (_ : Epi π) (y : T' ⟶ Y) (x : T' ⟶ X),
      π ≫ z = y ≫ b + x ≫ r := by
  have := h.epi_shortComplex_g
  obtain ⟨T', π, _, u, hu⟩ := surjective_up_to_refinements_of_epi h.shortComplex.g z
  refine ⟨T', π, inferInstance, u ≫ biprod.fst, u ≫ biprod.snd, ?_⟩
  simp only [hu, assoc, ← Preadditive.comp_add]
  congr
  aesop_cat

end IsPushout

end CategoryTheory
