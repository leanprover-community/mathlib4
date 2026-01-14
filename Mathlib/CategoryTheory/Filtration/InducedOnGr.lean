/-
Copyright (c) 2026 Matteo Cipollina,Jonathan Washburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Jonathan Washburn
-/

module

public import Mathlib.CategoryTheory.Filtration.Opposed

/-!
## Induced filtrations on graded pieces (Deligne, *Théorie de Hodge II*, §1.2.1).

This PR introduces the *iterated graded* objects attached to a pair of decreasing filtrations.

Given decreasing filtrations `F, G` on an object `A` in an abelian category, for each `q : ℤ` we
construct a decreasing filtration on the graded piece `Gr_G^q(A)` induced by `F` (Deligne 1.2.1).

From this we define the iterated graded object
  `Gr_F^p(Gr_G^q(A))`.

This file is deliberately scoped: it provides the definitions and the basic structural lemmas
needed for the Zassenhaus isomorphisms and splitting lemma that follow in later PRs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

namespace DecFiltration

variable {A : C}

section Abelian

variable [Abelian C]

/-- The filtration on `Gr_G^q(A)` induced by a filtration `F` on `A`.

Here we take the induced filtration of `F` on the subobject `G^q(A)`, and then push it
forward to the quotient `G^q(A)/G^{q+1}(A)` along `grπ G q`.

This aims to model Deligne's `F`-filtration on `Gr_G^q(A)` in §1.2.1.
-/
noncomputable def inducedOnGr (F G : DecFiltration A) (q : ℤ) : DecFiltration (G.gr q) where
  F p := FilteredObject.imageSubobject (grπ G q) ((F.induced (G q)) p)
  antitone' := by
    intro m n hmn
    -- The induced filtration on `G q` is decreasing, and images are monotone in the subobject.
    have hle : (F.induced (G q)) n ≤ (F.induced (G q)) m := (F.induced (G q)).antitone hmn
    exact (FilteredObject.imageSubobject_mono (grπ G q)) hle

@[simp] lemma inducedOnGr_apply (F G : DecFiltration A) (q p : ℤ) :
    (inducedOnGr (A := A) F G q) p
      = FilteredObject.imageSubobject (grπ (A := A) G q) ((F.induced (G q)) p) :=
  rfl

/-- The *iterated graded* piece `Gr_F^p(Gr_G^q(A))`. -/
noncomputable def grGr (F G : DecFiltration A) (p q : ℤ) : C :=
  (inducedOnGr (A := A) F G q).gr p

/-- Notation-friendly lemma unfolding `grGr`. -/
@[simp] lemma grGr_def (F G : DecFiltration A) (p q : ℤ) :
    grGr (A := A) F G p q = (inducedOnGr (A := A) F G q).gr p := rfl

end Abelian

end DecFiltration

end CategoryTheory
