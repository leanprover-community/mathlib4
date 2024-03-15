/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.StandardGeometricRepresentation

/-!
# The exchange properties, deletion property, and Matsumoto's theorem
Throughout this file, `B` is a type and `M : Matrix B B ℕ` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* Matrix.CoxeterGroup M`, where `Matrix.CoxeterGroup M` refers to
the quotient of the free group on `B` by the Coxeter relations given by the matrix `M`. See
`Mathlib.GroupTheory.Coxeter.Basic` for more details.

The goal of this file is to prove the (strong) right exchange property, the (strong) left exchange
property, the deletion property, and Matsumoto's theorem. No new definitions are included. See
the documentation below for the informal statements of each of these theorems.

We also prove some auxiliary results, such as that a word is reduced if and only if its right
inversion sequence has no duplicates if and only if its left inversion sequence has no duplicates.
(One direction of this implication was proved in `Mathlib.GroupTheory.Coxeter.Length`.)

## References
* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*][bjorner2005]
-/

noncomputable section

namespace CoxeterSystem

open List Matrix Function Real

variable {B : Type*} [DecidableEq B]
variable {M : Matrix B B ℕ}
variable {W : Type*} [Group W]
variable (cs : CoxeterSystem M W)

local prefix:100 "s" => cs.simpleReflection
local prefix:100 "π" => cs.wordProd
local prefix:100 "ℓ" => cs.length
local prefix:100 "ris" => cs.rightInvSeq
local prefix:100 "lis" => cs.leftInvSeq


/-! ### The (strong) exchange properties and deletion property -/

/-- The (strong) right exchange property:
Let $w = s_{i_1} \cdots s_{i_\ell}$ be a reduced expression for an element $w \in W$
and let $t \in W$.
The following are equivalent:

* $t$ is a right inversion of $w$.
* $t$ appears in the right inversion sequence of the word $s_{i_1} \cdots s_{i_\ell}$.
* There exists $j$ with $1 \leq j \leq \ell$ such that
  $$wt = s_{i_1} \cdots \widehat{s_{i_j}} \cdots s_{i_\ell}$$
  (i.e. the result of multiplying all of the simple reflections $s_{i_1}, \ldots, s_{i_\ell}$
  except $s_{i_j}$).
-/
theorem right_exchange_property {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsRightInversion (π ω) t,
      t ∈ ris ω,
      ∃ j < ω.length, (π ω) * t = π (ω.eraseIdx j)
    ] := by
  sorry

/-- The (strong) left exchange property:
Let $w = s_{i_1} \cdots s_{i_\ell}$ be a reduced expression for an element $w \in W$
and let $t \in W$.
The following are equivalent:

* $t$ is a left inversion of $w$.
* $t$ appears in the left inversion sequence of the word $s_{i_1} \cdots s_{i_\ell}$.
* There exists $j$ with $1 \leq j \leq \ell$ such that
  $$tw = s_{i_1} \cdots \widehat{s_{i_j}} \cdots s_{i_\ell}$$
  (i.e. the result of multiplying all of the simple reflections $s_{i_1}, \ldots, s_{i_\ell}$
  except $s_{i_j}$).
-/
theorem left_exchange_property {ω : List B} (t : W) (rω : cs.IsReduced ω) :
    List.TFAE [
      cs.IsLeftInversion (π ω) t,
      t ∈ lis ω,
      ∃ j < ω.length, t * (π ω) = π (ω.eraseIdx j)
    ] := by
  sorry

theorem nodup_rightInvSeq_iff (ω : List B) :
    List.Nodup (ris ω) ↔ cs.IsReduced ω := by
  sorry

theorem nodup_leftInvSeq_iff (ω : List B) :
    List.Nodup (lis ω) ↔ cs.IsReduced ω := by
  sorry

/-- The deletion property:
If $s_{i_1} \cdots s_{i_\ell}$ is not a reduced expression, then there are $i, j$ with
$1 \leq j < j' \leq \ell$ such that
$$s_{i_1} \cdots s_{i_\ell} =
s_{i_1} \cdots \widehat{s_{i_j}} \cdots \widehat{s_{i_{j'}}} \cdots s_{i_\ell}.$$
-/
theorem deletion_property (ω : List B) (nrω : ¬ cs.IsReduced ω) :
    ∃ j' < ω.length, ∃ j < j', π ((ω.eraseIdx j').eraseIdx j) = π ω := by
  sorry

end CoxeterSystem

end
/-
TODO: Inversion set is finite. Size of inversion set = length.
Matsumoto's theorem.
Simple reflections are distinct.
Order of s_i s_j is exactly M i j.

Eₙ for n > 8.

Irreducibility. Irreducible components.
Parabolic subgroups.
Poincare series.

The standard geometric representation. It is faithful.
Height of a root.
Standard geometric representation is orthogonal if and only if W is finite.
Classification of irreducible finite Coxeter groups.
Classification of irreducible affine Coxeter groups.

Small roots.
Coxeter groups are automatic.

Long element has all reflections as inversions. Long element is an involution.
Properties of Coxeter number.

The weak order. Ungar moves. Ungar's problem.

Bruhat order.

Combinatorially describe finite and affine Coxeter groups of types A, B, C, D.
Interpret inversions, descents, length, convex sets, parabolic subgroups, Bruhat order.

Schubert polynomials.

Associated hyperplane arrangements and partition lattices and their characteristic polynomials.
Folding.
Convex sets.
Coxeter elements, c-sorting words.
Powers of Coxeter elements in infinite groups are reduced.
Futuristic Coxeter groups.
-/
