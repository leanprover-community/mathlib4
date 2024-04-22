/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Refinements

In order to prove injectivity/surjectivity/exactness properties for diagrams
in the category of abelian groups, we often need to do diagram chases.
Some of these can be carried out in more general abelian categories:
for example, a morphism `X ⟶ Y` in an abelian category `C` is a
monomorphism if and only if for all `A : C`, the induced map
`(A ⟶ X) → (A ⟶ Y)` of abelian groups is a monomorphism, i.e. injective.
Alternatively, the yoneda presheaf functor which sends `X` to the
presheaf of maps `A ⟶ X` for all `A : C` preserves and reflects
monomorphisms.

However, if `p : X ⟶ Y` is an epimorphism in `C` and `A : C`,
`(A ⟶ X) → (A ⟶ Y)` may fail to be surjective (unless `p` is a split
epimorphism).

In this file, the basic result is `epi_iff_surjective_up_to_refinements`
which states that `f : X ⟶ Y` is a morphism in an abelian category,
then it is an epimorphism if and only if for all `y : A ⟶ Y`,
there exists an epimorphism `π : A' ⟶ A` and `x : A' ⟶ X` such
that `π ≫ y = x ≫ f`. In order words, if we allow a precomposition
with an epimorphism, we may lift a morphism to `Y` to a morphism to `X`.
Following unpublished notes by George Bergman, we shall say that the
precomposition by an epimorphism `π ≫ y` is a refinement of `y`. Then,
we get that an epimorphism is a morphism that is "surjective up to refinements".
(This result is similar to the fact that a morphism of sheaves on
a topological space or a site is epi iff sections can be lifted
locally. Then, arguing "up to refinements" is very similar to
arguing locally for a Grothendieck topology (TODO: indeed,
show that it corresponds to the "refinements" topology on an
abelian category `C` that is defined by saying that
a sieve is covering if it contains an epimorphism).

Similarly, it is possible to show that a short complex in an abelian
category is exact if and only if it is exact up to refinements
(see `ShortComplex.exact_iff_exact_up_to_refinements`).

As it is outlined in the documentation of the file
`CategoryTheory.Abelian.Pseudoelements`, the Freyd-Mitchell
embedding theorem implies the existence of a faithful and exact functor `ι`
from an abelian category `C` to the category of abelian groups. If we
define a pseudo-element of `X : C` to be an element in `ι.obj X`, one
may do diagram chases in any abelian category using these pseudo-elements.
However, using this approach would require proving this embedding theorem!
Currently, mathlib contains a weaker notion of pseudo-elements
`CategoryTheory.Abelian.Pseudoelements`. Some theorems can be obtained
using this notion, but there is the issue that for this notion
of pseudo-elements a morphism `X ⟶ Y` in `C` is not determined by
its action on pseudo-elements (see also `Counterexamples/Pseudoelement`).
On the contrary, the approach consisting of working up to refinements
does not require the introduction of other types: we only need to work
with morphisms `A ⟶ X` in `C` which we may consider as being
"sort of elements of `X`". One may carry diagram-chasing by tracking
these morphisms and sometimes introducing an auxiliary epimorphism `A' ⟶ A`.

## References
* George Bergman, A note on abelian categories – translating element-chasing proofs,
and exact embedding in abelian groups (1974)
http://math.berkeley.edu/~gbergman/papers/unpub/elem-chase.pdf

-/

namespace CategoryTheory

open Category Limits

variable {C : Type _} [Category C] [Abelian C] {X Y : C} (S : ShortComplex C)
  {S₁ S₂ : ShortComplex C}

lemma epi_iff_surjective_up_to_refinements (f : X ⟶ Y) :
    Epi f ↔ ∀ ⦃A : C⦄ (y : A ⟶ Y),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f := by
  constructor
  · intro _ A a
    exact ⟨pullback a f, pullback.fst, inferInstance, pullback.snd, pullback.condition⟩
  · intro hf
    obtain ⟨A, π, hπ, a', fac⟩ := hf (𝟙 Y)
    rw [comp_id] at fac
    exact epi_of_epi_fac fac.symm

lemma surjective_up_to_refinements_of_epi (f : X ⟶ Y) [Epi f] {A : C} (y : A ⟶ Y) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x : A' ⟶ X), π ≫ y = x ≫ f :=
  (epi_iff_surjective_up_to_refinements f).1 inferInstance y

lemma ShortComplex.exact_iff_exact_up_to_refinements :
    S.Exact ↔ ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
      ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  rw [S.exact_iff_epi_toCycles, epi_iff_surjective_up_to_refinements]
  constructor
  · intro hS A a ha
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (S.liftCycles a ha)
    exact ⟨A', π, hπ, x₁, by simpa only [assoc, liftCycles_i, toCycles_i] using fac =≫ S.iCycles⟩
  · intro hS A a
    obtain ⟨A', π, hπ, x₁, fac⟩ := hS (a ≫ S.iCycles) (by simp)
    exact ⟨A', π, hπ, x₁, by simp only [← cancel_mono S.iCycles, assoc, toCycles_i, fac]⟩

variable {S}

lemma ShortComplex.Exact.exact_up_to_refinements
    (hS : S.Exact) {A : C} (x₂ : A ⟶ S.X₂) (hx₂ : x₂ ≫ S.g = 0) :
    ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements] at hS
  exact hS x₂ hx₂

end CategoryTheory
