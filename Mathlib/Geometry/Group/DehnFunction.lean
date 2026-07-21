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

For a presentation `P = ⟨α | rel⟩` of a group `G` and a word `w : FreeGroup α` that evaluates to
the identity in `G`, the *area* of `w` is the least number of conjugates of relators (and of
inverse relators) whose product is `w`. The *Dehn function* of `P` is
`n ↦ max {area w | w = 1 in G, ‖w‖ ≤ n}`.

This is the combinatorial definition; the area of `w` is equally the least number of `2`-cells in a
van Kampen diagram with boundary word `w`. Expressing `w` as a product of conjugates of relators and
inverse relators is the algebraic shadow of such a diagram — a *filling* of the loop `w`.

## Main definitions

* `Group.Presentation.IsConjRelDecomp P w l`: the list `l` exhibits `w` as a product of
  conjugates of relators and inverse relators.
* `Group.Presentation.IsConjRelProduct P w`: `w` is a product of conjugates of relators and inverse
  relators, i.e. it admits such a decomposition.
* `Group.Presentation.area`: the least length of such a decomposition, valued in `ℕ∞` (`⊤` when
  there is none).
* `Group.Presentation.IsMinimalConjRelDecomp P w l`: `l` is a decomposition of `w` of least
  possible length, i.e. of length `P.area w`.
* `Group.Presentation.kerBall`: the words of length at most `n` that evaluate to the identity
  in `G`.
* `Group.Presentation.dehn`: the Dehn function.

The theory of these definitions — that `area` is finite exactly on the words that evaluate to the
identity in `G`, that the Dehn function is monotone, and that its growth type is an invariant of
the finitely presented group — is developed downstream of this file.

## Design notes

* The factors of the product range over `Group.conjugatesOfSet P.symmRelSet`, the conjugates of
  relators *and* of inverse relators. Both signs are needed: the conjugates of `P.relSet` alone
  generate only a submonoid, whereas the products must realise every element of the kernel
  `Subgroup.normalClosure P.relSet`, a subgroup.
* `area` takes values in `ℕ∞`; it is `⊤` exactly when `w` does not evaluate to the identity in `G`
  (there is then no product of conjugates equal to `w`), and finite otherwise. This mirrors
  `SimpleGraph.edist`, and keeps `area w = 0 ↔ w = 1` rather than colliding with the junk value.
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

/-- A list `l` of elements of the free group is a decomposition of `w` into conjugates of relators
of `P` if every entry of `l` is a conjugate of a relator or of an inverse relator, and the product
of `l` is `w`. -/
def IsConjRelDecomp (w : FreeGroup α) (l : List (FreeGroup α)) : Prop :=
  (∀ x ∈ l, x ∈ Group.conjugatesOfSet P.symmRelSet) ∧ l.prod = w

/-- The area of a word `w` over the presentation `P` is the least length of a decomposition
`l` of `w` into conjugates of elements of the symmetric relator set.
It is valued in `ℕ∞`: it is finite when a decomposition `l` exists, and `⊤` when `w` is not the
identity of `G`, since then no such decomposition exists and the infimum is taken over the empty
set. -/
noncomputable def area (w : FreeGroup α) : ℕ∞ :=
  sInf ((fun l : List (FreeGroup α) => (l.length : ℕ∞)) '' {l | P.IsConjRelDecomp w l})

variable {w : FreeGroup α} {l : List (FreeGroup α)} {n : ℕ}

/-- Writing `w` as a product of conjugates witnesses that its area is at most that product's
length. -/
lemma IsConjRelDecomp.area_le (h : P.IsConjRelDecomp w l) : P.area w ≤ l.length :=
  sInf_le ⟨l, h, rfl⟩

/-- A word admitting a decomposition into conjugates of relators evaluates to the identity in
`G`. -/
lemma IsConjRelDecomp.lift_eq_one (h : P.IsConjRelDecomp w l) : P.lift w = 1 := by
  obtain ⟨hmem, rfl⟩ := h
  rw [← List.prod_hom l P.lift]
  refine List.prod_eq_one fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact P.lift_eq_one_of_mem_conjugatesOfSet_symmRelSet (hmem y hy)

/-- A word is a product of conjugates of relators and inverse relators exactly when it evaluates to
the identity in `G`. -/
lemma exists_isConjRelDecomp_iff_mem_ker :
    (∃ l, P.IsConjRelDecomp w l) ↔ w ∈ P.lift.ker := by
  refine ⟨fun ⟨l, hl⟩ => hl.lift_eq_one, fun hw => ?_⟩
  rw [P.ker_lift, Subgroup.normalClosure, ← Subgroup.mem_toSubmonoid,
    Subgroup.closure_toSubmonoid] at hw
  obtain ⟨l, hmem, rfl⟩ := Submonoid.exists_list_of_mem_closure hw
  refine ⟨l, fun x hx => ?_, rfl⟩
  have hsub := Group.conjugatesOfSet_mono P.relSet_subset_symmRelSet
  rcases hmem x hx with h | h
  · exact hsub h
  · simpa using P.inv_mem_conjugatesOfSet_symmRelSet (hsub (Set.mem_inv.mp h))

/-- A word has finite area exactly when it evaluates to the identity in `G`. -/
theorem area_ne_top_iff : P.area w ≠ ⊤ ↔ w ∈ P.lift.ker := by
  rw [← P.exists_isConjRelDecomp_iff_mem_ker]
  refine ⟨fun h => ?_, fun ⟨l, hl⟩ => (hl.area_le.trans_lt (by simp)).ne⟩
  by_contra hw
  have hempty : {l : List (FreeGroup α) | P.IsConjRelDecomp w l} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun l hl => hw ⟨l, hl⟩
  exact h (by rw [area, hempty, Set.image_empty, sInf_empty])

/-- A word has area `⊤` exactly when it does not evaluate to the identity of `G`: there is then no
product of conjugates of relators equal to it, so the infimum defining `area` is over the empty
set. -/
theorem area_eq_top_iff : P.area w = ⊤ ↔ w ∉ P.lift.ker := by
  rw [← P.area_ne_top_iff, not_ne_iff]

/-- A word has area `⊤` exactly when it does not evaluate to the identity of `G`. -/
theorem area_eq_top_iff_lift_ne_one : P.area w = ⊤ ↔ P.lift w ≠ 1 := by
  rw [P.area_eq_top_iff, MonoidHom.mem_ker]

/-- A word has finite area exactly when it evaluates to the identity of `G`. -/
theorem area_lt_top_iff : P.area w < ⊤ ↔ w ∈ P.lift.ker := by
  rw [lt_top_iff_ne_top, P.area_ne_top_iff]

section Dehn

variable [DecidableEq α]

/-- The set of words of length at most `n` that evaluate to the identity in `G`. -/
def kerBall (n : ℕ) : Set (FreeGroup α) := {w | w ∈ P.lift.ker ∧ FreeGroup.norm w ≤ n}

/-- The Dehn function of a presentation: `P.dehn n` is the largest area of a word of length at most
`n` that evaluates to the identity in `G`. Equivalently, it is the least isoperimetric function
of `P`.

This is junk unless the generating set is finite; the relevant lemmas assume `[Finite α]`. The
areas involved are all finite (the words evaluate to the identity in `G`), so truncating the
`ℕ∞`-valued supremum back to `ℕ` with `ENat.toNat` loses nothing. -/
noncomputable def dehn (n : ℕ) : ℕ := (sSup (P.area '' P.kerBall n)).toNat

end Dehn

end Group.Presentation
