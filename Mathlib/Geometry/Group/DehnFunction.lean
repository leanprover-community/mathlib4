/-
Copyright (c) 2026 Hang Lu Su, Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hang Lu Su, Justus Springer
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Data.ENat.Lattice
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Presentation

/-!
# Dehn functions

For a presentation `P` of a group `G` and a word `w : FreeGroup α` that evaluates to
the identity in `G`, the *area* of `w` is the least number of conjugates of relators and of
inverse relators whose product is `w`. The *Dehn function* of `P` is given by
`n ↦ max {area w | w = 1 in G, ‖w‖ ≤ n}`, where `‖w‖` is the length of `w`.

## Main definitions

* `Group.Presentation.IsConjRelDecomp P w l`:
* `Group.Presentation.area`:
* `Group.Presentation.kerBall`:
* `Group.Presentation.dehn`:

## Design notes

* The factors of the product range over `Group.conjugatesOfSet P.symmRelSet`, the conjugates of
  relators *and* of inverse relators. Both signs are needed: the conjugates of `P.relSet` alone
  generate only a submonoid, whereas the products must realise every element of the kernel
  `Subgroup.normalClosure P.relSet`, a subgroup.
* `area` takes values in `ℕ∞`; it is `⊤` exactly when `w` does not evaluate to the identity in `G`
  (there is then no product of conjugates equal to `w`), and finite otherwise. This mirrors
  `SimpleGraph.edist`, and keeps `area w = 0 ↔ w = 1` rather than colliding with the junk value.
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
structure IsConjRelDecomp (w : FreeGroup α) (l : List (FreeGroup α)) : Prop where
  mem_conjugatesOfSet : ∀ x ∈ l, x ∈ Group.conjugatesOfSet P.symmRelSet
  prod_eq : l.prod = w

attribute [simp] IsConjRelDecomp.prod_eq

lemma isConjRelDecomp_one_nil : P.IsConjRelDecomp (1 : FreeGroup α) [] where
  mem_conjugatesOfSet := by simp
  prod_eq := by simp

/-- The area of a word `w` over the presentation `P` is the least length of a decomposition
`l` of `w` into conjugates of elements of the symmetric relator set. It is valued in `ℕ∞`
so that it returns a finite number when `l` exists, and the junk value `⊤` when
`w` is not the identity of `G`, since then no such decomposition exists and
the infimum is taken over the empty set. -/
noncomputable def area (w : FreeGroup α) : ℕ∞ :=
  sInf ((fun l : List (FreeGroup α) ↦ (l.length : ℕ∞)) '' {l | P.IsConjRelDecomp w l})

variable {w : FreeGroup α} {l : List (FreeGroup α)} {n : ℕ}

/-- The area  of `w` is less or equal than the length of a conjugate decomposition. -/
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

lemma area_eq_foo : P.area w = n → ∃ (l : List (FreeGroup α)), P.IsConjRelDecomp w l := by
  sorry

@[simp]
lemma area_one_eq_zero : P.area (1 : FreeGroup α) = 0 := by
  simpa using IsConjRelDecomp.area_le P (isConjRelDecomp_one_nil P)

lemma area_eq_zero_iff : P.area w = 0 ↔ w = (1 : FreeGroup α) := by
  constructor
  · intro h
    contrapose h
    sorry
  · intro h ; simp [h]

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

-- TODO add little lemmas about Dehn functions.

end Dehn

end Group.Presentation
