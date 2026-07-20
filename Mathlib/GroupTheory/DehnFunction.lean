/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Presentation

/-!
# Dehn functions

For a presentation `P = ⟨α | rel⟩` of a group `G` and a word `w : FreeGroup α` that dies in `G`,
the *area* of `w` is the least number of conjugates of relators (and of inverse relators) whose
product is `w`. The *Dehn function* of `P` is `n ↦ max {area w | w = 1 in G, ‖w‖ ≤ n}`.

This is the combinatorial definition; the area of `w` is equally the least number of `2`-cells in a
van Kampen diagram with boundary word `w`.

## Main definitions

* `Group.Presentation.conjRelSet`: the conjugates of relators and of inverse relators.
* `Group.Presentation.IsAreaAtMost P w n`: `w` is a product of at most `n` such conjugates.
* `Group.Presentation.area`: the least such `n`.
* `Group.Presentation.kerBall`: the words of length at most `n` that die in `G`.
* `Group.Presentation.dehn`: the Dehn function.

The theory of these definitions — that `area` is finite exactly on the words that die in `G`, that
the Dehn function is monotone, and that its growth type is an invariant of the finitely presented
group — is developed downstream of this file.

## Design notes

* `area` is defined by `sInf`, so `area w = 0` is a junk value when `w` does not die in `G`.
* `dehn` is defined by `sSup`, and is junk unless `[Finite α]` makes the relevant set of words
  finite.
* `FreeGroup.norm` needs `[DecidableEq α]`, so `kerBall` and `dehn` do too.

## Tags

Dehn function
-/

@[expose] public section

variable {G α ρ : Type*} [Group G]

namespace Group.Presentation

variable (P : Group.Presentation G α ρ)

/-- The conjugates of relators and of inverse relators: the words `u * r * u⁻¹` and `u * r⁻¹ * u⁻¹`
with `r` a relator. These are the elementary pieces out of which every word that dies in `G` is
built; see `Group.Presentation.mem_ker_iff_exists_isAreaAtMost`. -/
def conjRelSet : Set (FreeGroup α) :=
  {x | ∃ u r, r ∈ P.relSet ∧ (x = u * r * u⁻¹ ∨ x = u * r⁻¹ * u⁻¹)}

/-! ### Area -/

/-- `P.IsAreaAtMost w n` means that `w` is a product of at most `n` conjugates of relators and
inverse relators. Equivalently, `w` bounds a van Kampen diagram over `P` with at most `n` faces. -/
def IsAreaAtMost (w : FreeGroup α) (n : ℕ) : Prop :=
  ∃ l : List (FreeGroup α), l.length ≤ n ∧ (∀ x ∈ l, x ∈ P.conjRelSet) ∧ l.prod = w

/-- The area of a word `w` over the presentation `P`: the least number of conjugates of relators
and inverse relators whose product is `w`.

This is the junk value `0` when `w` does not die in `G`. -/
noncomputable def area (w : FreeGroup α) : ℕ := sInf {n | P.IsAreaAtMost w n}

/-! ### The Dehn function -/

section Dehn

variable [DecidableEq α]

/-- The words of length at most `n` that die in `G`. -/
def kerBall (n : ℕ) : Set (FreeGroup α) := {w | w ∈ P.lift.ker ∧ FreeGroup.norm w ≤ n}

/-- The Dehn function of a presentation: `P.dehn n` is the largest area of a word of length at most
`n` that dies in `G`. Equivalently, it is the least isoperimetric function of `P`.

This is junk unless the generating set is finite; the relevant lemmas assume `[Finite α]`. -/
noncomputable def dehn (n : ℕ) : ℕ := sSup (P.area '' P.kerBall n)

end Dehn

end Group.Presentation
