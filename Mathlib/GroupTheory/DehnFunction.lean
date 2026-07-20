/-
Copyright (c) 2026 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su
-/
module

public import Mathlib.Data.ENat.Lattice
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
* `Group.Presentation.area`: the least such `n`, valued in `ℕ∞` (`⊤` when there is none).
* `Group.Presentation.kerBall`: the words of length at most `n` that die in `G`.
* `Group.Presentation.dehn`: the Dehn function.

The theory of these definitions — that `area` is finite exactly on the words that die in `G`, that
the Dehn function is monotone, and that its growth type is an invariant of the finitely presented
group — is developed downstream of this file.

## Design notes

* `area` takes values in `ℕ∞`; it is `⊤` exactly when `w` does not die in `G` (there is then no
  product of conjugate relators equal to `w`), and finite otherwise. This mirrors
  `SimpleGraph.edist`, and keeps `area w = 0 ↔ w = 1` rather than colliding with the junk value.
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
with `r` a relator. -/
def conjRelSet : Set (FreeGroup α) :=
  {x | ∃ u r, r ∈ P.relSet ∧ (x = u * r * u⁻¹ ∨ x = u * r⁻¹ * u⁻¹)}

/-! ### Area -/

/-- `P.IsAreaAtMost w n` means that `w` is a product of at most `n` conjugates of relators and
inverse relators. Equivalently, `w` bounds a van Kampen diagram over `P` with at most `n` faces. -/
def IsAreaAtMost (w : FreeGroup α) (n : ℕ) : Prop :=
  ∃ l : List (FreeGroup α), l.length ≤ n ∧ (∀ x ∈ l, x ∈ P.conjRelSet) ∧ l.prod = w

/-- The area of a word `w` over the presentation `P`: the least number of conjugates of relators
and inverse relators whose product is `w`, valued in `ℕ∞`.

This is `⊤` exactly when `w` does not die in `G` (there is then no such product), and finite
otherwise; in particular `area w = 0 ↔ w = 1`. -/
noncomputable def area (w : FreeGroup α) : ℕ∞ :=
  sInf (((↑) : ℕ → ℕ∞) '' {n | P.IsAreaAtMost w n})

variable {w : FreeGroup α} {n : ℕ}

/-- If `w` is a product of at most `n` conjugate relators, then its area is at most `n`. -/
theorem area_le (h : P.IsAreaAtMost w n) : P.area w ≤ n :=
  sInf_le ⟨n, h, rfl⟩

/-- The area of `w` is `⊤` exactly when `w` is not a product of any number of conjugate relators,
i.e. when `w` does not die in `G`. -/
theorem area_eq_top_iff : P.area w = ⊤ ↔ ¬ ∃ n, P.IsAreaAtMost w n := by
  simp [area, sInf_eq_top]

/-- `n ≤ area w` exactly when every expression of `w` as a product of conjugate relators uses at
least `n` of them. -/
theorem coe_le_area_iff : (n : ℕ∞) ≤ P.area w ↔ ∀ m, P.IsAreaAtMost w m → n ≤ m := by
  simp [area, le_sInf_iff]

/-- The Galois connection between `area` and `IsAreaAtMost`: `area w ≤ n` exactly when `w` is a
product of at most `n` conjugate relators. This is the workhorse for reasoning about `area`. -/
theorem area_le_iff : P.area w ≤ n ↔ P.IsAreaAtMost w n := by
  refine ⟨fun h => ?_, P.area_le⟩
  by_contra hn
  have hle : (↑(n + 1) : ℕ∞) ≤ P.area w :=
    P.coe_le_area_iff.mpr fun m hm => by
      by_contra hmn
      obtain ⟨l, hl, hmem, hprod⟩ := hm
      exact hn ⟨l, hl.trans (by omega), hmem, hprod⟩
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
