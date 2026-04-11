/-
Copyright (c) 2026 Arnoud van der Leer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arnoud van der Leer
-/
module

public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# The Nerve of a Codiscrete Category
In the codiscrete category on a type `X`, every hom-type is given by `Unit`.
When we take the nerve of such a category, the `n`-simplices become equivalent to
`X`-vectors of length `n + 1`.
Therefore, if `X` has decidable equality, so does the type of `n`-simplices in this nerve.
-/

@[expose] public section

universe u

namespace CategoryTheory.Codiscrete

open Simplicial

variable {X : Type u} {n : ℕ}

/-- Since the morphisms in a codiscrete category do not carry information, an n-simplex of
coherentIso is equivalent to an X-vector of length (n + 1). -/
def equivFun : nerve (Codiscrete X) _⦋n⦌ ≃ (Fin (n + 1) → X) where
  toFun f n := (f.obj n).as
  invFun f := .mk (fun n ↦ .mk (f n)) (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)

/-- If a type `X` has decidable equality, the nerve of the codiscrete category on `X`
has decidable equality as well. -/
instance [DecidableEq X] : DecidableEq (nerve (Codiscrete X) _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq equivFun)

end CategoryTheory.Codiscrete
