/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices

/-!
# The type of non degenerate simplices not in a subcomplex

In this file, given a subcomplex `A` of a simplicial set `X`,
we introduce the type `A.N` of nondegenerate simplices of `X`
that are not in `A`.

-/

universe u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} (A : X.Subcomplex)

/-- The type of nondegenerate simplices which do not belong to
a given subcomplex of a simplicial set. -/
structure N extends X.N where mk' ::
  notMem : simplex ∉ A.obj _

namespace N

variable {A}

lemma mk'_surjective (s : A.N) :
    ∃ (t : X.N) (ht : t.simplex ∉ A.obj _), s = mk' t ht :=
  ⟨s.toN, s.notMem, rfl⟩

/-- Constructor for the type of nondegenerate simplices which
do not belong to a given subcomplex of a simplicial set. -/
@[simps!]
def mk {n : ℕ} (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
    (hx' : x ∉ A.obj _) : A.N where
  simplex := x
  nonDegenerate := hx
  notMem := hx'

lemma mk_surjective (s : A.N) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (hx : x ∈ X.nonDegenerate n)
      (hx' : x ∉ A.obj _), s = mk x hx hx' :=
  ⟨s.dim, s.simplex, s.nonDegenerate, s.notMem, rfl⟩

lemma ext_iff (x y : A.N) :
    x = y ↔ x.toN = y.toN := by
  cases x
  cases y
  aesop

section

variable (s : A.N) {d : ℕ} (hd : s.dim = d)

/-- When `A` is a subcomplex of a simplicial set `X`,
and `s : A.N` is such that `s.dim = d`, this is a term
that is equal to `s`, but whose dimension if definitionally equal to `d`. -/
abbrev cast : A.N where
  toN := s.toN.cast hd
  notMem := hd ▸ s.notMem

lemma cast_eq_self : s.cast hd = s := by
  subst hd
  rfl

end

end N

end SSet.Subcomplex
