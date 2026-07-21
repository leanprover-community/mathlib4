/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Presentation

/-!
# Dehn functions

For a presentation `P = ⟨α | rel⟩` of a group `G` and a word `w : FreeGroup α` that dies in `G`,
the *area* of `w` is the least number of conjugates of relators (and of inverse relators) whose
product is `w`. The *Dehn function* of `P` is `n ↦ max {area w | w = 1 in G, ‖w‖ ≤ n}`.

This is the combinatorial definition; the area of `w` is equally the least number of `2`-cells in a
van Kampen diagram with boundary word `w`. Expressing `w` as a product of conjugates of relators and
inverse relators is the algebraic shadow of such a diagram — a *filling* of the loop `w`.

## Main definitions

* `Group.Presentation.symmRelSet`: the relators of `P` together with their inverses.
* `Group.Presentation.IsConjProduct P w l`: the list `l` exhibits `w` as a product of
  conjugates of relators and inverse relators.
* `Group.Presentation.area`: the least length of such a product, valued in `ℕ∞` (`⊤` when there is
  none).
* `Group.Presentation.kerBall`: the words of length at most `n` that die in `G`.
* `Group.Presentation.dehn`: the Dehn function.

The theory of these definitions — that `area` is finite exactly on the words that die in `G`, that
the Dehn function is monotone, and that its growth type is an invariant of the finitely presented
group — is developed downstream of this file.

## Design notes

* The factors of the product range over `Group.conjugatesOfSet P.symmRelSet`, the conjugates of
  relators *and* of inverse relators. Both signs are needed: the conjugates of `P.relSet` alone
  generate only a submonoid, whereas the products must realise every element of the kernel
  `Subgroup.normalClosure P.relSet`, a subgroup.
* `area` takes values in `ℕ∞`; it is `⊤` exactly when `w` does not die in `G` (there is then no
  product of conjugates equal to `w`), and finite otherwise. This mirrors `SimpleGraph.edist`, and
  keeps `area w = 0 ↔ w = 1` rather than colliding with the junk value.
* `dehn` is defined by `sSup`, and is junk unless `[Finite α]` makes the relevant set of words
  finite.
* `FreeGroup.norm` needs `[DecidableEq α]`, so `kerBall` and `dehn` do too.

## Tags

Dehn function
-/

@[expose] public section

open scoped Pointwise

variable {G α ρ : Type*} [Group G]

namespace Group.Presentation

variable (P : Group.Presentation G α ρ)

/-- The relators of `P` together with their inverses. -/
def symmRelSet : Set (FreeGroup α) := P.relSet ∪ P.relSet⁻¹

/-- `P.IsConjProduct w l` means that the list `l` exhibits `w` as a product of conjugates of
relators and inverse relators: every entry lies in `Group.conjugatesOfSet P.symmRelSet`, and
`l.prod = w`. Its length counts the relator applications used to trivialise `w`, so `l` is the
algebraic shadow of a van Kampen diagram with boundary word `w` (a *filling* of the loop). Such a
list exists exactly when `w` dies in `G`. -/
def IsConjProduct (w : FreeGroup α) (l : List (FreeGroup α)) : Prop :=
  (∀ x ∈ l, x ∈ Group.conjugatesOfSet P.symmRelSet) ∧ l.prod = w

/-- The area of a word `w` over the presentation `P`: the least length of a product of conjugates of
relators and inverse relators equal to `w`, valued in `ℕ∞`.

This is `⊤` exactly when `w` is not the identity of `G` (there is then no such product), and finite
otherwise; in particular `area w = 0 ↔ w = 1`. -/
noncomputable def area (w : FreeGroup α) : ℕ∞ :=
  sInf ((fun l : List (FreeGroup α) => (l.length : ℕ∞)) '' {l | P.IsConjProduct w l})

variable {w : FreeGroup α} {n : ℕ}

/-- Writing `w` as a product of conjugates witnesses that its area is at most that product's
length. -/
theorem IsConjProduct.area_le {l : List (FreeGroup α)}
    (h : P.IsConjProduct w l) : P.area w ≤ l.length :=
  sInf_le ⟨l, h, rfl⟩

/-- The area of `w` is `⊤` exactly when `w` is not a product of conjugates of any length, i.e. when
`w` does not die in `G`. -/
theorem area_eq_top_iff : P.area w = ⊤ ↔ ¬ ∃ l, P.IsConjProduct w l := by
  simp [area, sInf_eq_top]

/-- `n ≤ area w` exactly when every expression of `w` as a product of conjugates uses at least `n`
of them. -/
theorem coe_le_area_iff :
    (n : ℕ∞) ≤ P.area w ↔ ∀ l, P.IsConjProduct w l → n ≤ l.length := by
  simp [area, le_sInf_iff]

/-- The Galois connection between `area` and products of conjugates: `area w ≤ n` exactly when `w`
is a product of at most `n` conjugates of relators and inverse relators. This is the workhorse for
reasoning about `area`. -/
theorem area_le_iff : P.area w ≤ n ↔ ∃ l, P.IsConjProduct w l ∧ l.length ≤ n := by
  refine ⟨fun h => ?_, fun ⟨l, hpc, hl⟩ => hpc.area_le.trans (by exact_mod_cast hl)⟩
  by_contra hn
  have hle : (↑(n + 1) : ℕ∞) ≤ P.area w :=
    P.coe_le_area_iff.mpr fun l hpc => by
      have : n + 1 ≤ l.length := by
        by_contra hlen
        exact hn ⟨l, hpc, by omega⟩
      exact_mod_cast this
  exact absurd h (not_le.mpr (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hle))

/-! ### The Dehn function -/

section Dehn

variable [DecidableEq α]

/-- The words of length at most `n` that die in `G`. -/
def kerBall (n : ℕ) : Set (FreeGroup α) := {w | w ∈ P.lift.ker ∧ FreeGroup.norm w ≤ n}

/-- The Dehn function of a presentation: `P.dehn n` is the largest area of a word of length at most
`n` that dies in `G`. Equivalently, it is the least isoperimetric function of `P`.

This is junk unless the generating set is finite; the relevant lemmas assume `[Finite α]`. The
areas involved are all finite (the words die in `G`), so truncating the `ℕ∞`-valued supremum back
to `ℕ` with `ENat.toNat` loses nothing. -/
noncomputable def dehn (n : ℕ) : ℕ := (sSup (P.area '' P.kerBall n)).toNat

end Dehn

end Group.Presentation
