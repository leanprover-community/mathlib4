/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Rank and Orderings on polynomials

This file defines rank structures on multivariate polynomials,
which are essential for the Characteristic Set Method (Wu-Ritt Method).

## Main definitions

* `MvPolynomial.rank`: The rank of a polynomial `p` is the pair `(max_vars p, mainDegree p)`,
  ordered lexicographically. This defines a well-ordering on polynomials when the variable type
  is well-founded.

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]

-/

public section

variable {R σ : Type*} [CommSemiring R] [LinearOrder σ] {p q : MvPolynomial σ R}

namespace MvPolynomial

/-- The rank of a polynomial `p` is the pair `(p.vars.max, p.mainDegree.card)`,
which is ordered lexicographically. -/
noncomputable def rank (p : MvPolynomial σ R) : WithBot σ ×ₗ ℕ := (p.vars.max, p.mainDegree.card)

namespace Rank

theorem rank_eq_iff : p.rank = q.rank ↔
    p.vars.max = q.vars.max ∧ p.mainDegree.card = q.mainDegree.card := Prod.mk_inj

scoped instance : Preorder (MvPolynomial σ R) where
  le := InvImage (· ≤ ·) rank
  le_refl := fun _ ↦ by rw [InvImage]
  le_trans := fun _ _ _ ↦ le_trans

theorem le_def' : p ≤ q ↔ p.rank ≤ q.rank := Iff.rfl

noncomputable scoped instance : DecidableLE (MvPolynomial σ R) := fun _ _ ↦
  decidable_of_iff _ le_def'.symm

noncomputable scoped instance : DecidableLT (MvPolynomial σ R) := decidableLTOfDecidableLE

scoped instance instIsTotalLe : Std.Total (@LE.le (MvPolynomial σ R) _) where
  total p q := le_total p.rank q.rank

theorem le_def : p ≤ q ↔ p.vars.max < q.vars.max ∨
    p.vars.max = q.vars.max ∧ p.mainDegree.card ≤ q.mainDegree.card := Prod.lex_def

theorem le_iff_not_imp : p ≤ q ↔ ¬p.vars.max < q.vars.max →
    p.vars.max = q.vars.max ∧ p.mainDegree.card ≤ q.mainDegree.card :=
  Iff.trans le_def <| Decidable.or_iff_not_imp_left

theorem max_vars_le_of_le : p ≤ q → p.vars.max ≤ q.vars.max :=
  fun h ↦ Or.elim (le_def.mp h) le_of_lt (fun h ↦ le_of_eq h.1)

theorem lt_def' : p < q ↔ p.rank < q.rank := Iff.trans lt_iff_le_not_ge (by
  rw [le_def', le_def', not_le, and_iff_right_iff_imp]
  exact le_of_lt)

theorem lt_def : p < q ↔ p.vars.max < q.vars.max ∨
    p.vars.max = q.vars.max ∧ p.mainDegree.card < q.mainDegree.card :=
  Iff.trans lt_def' Prod.lex_def

theorem lt_iff_not_imp : p < q ↔ ¬p.vars.max < q.vars.max
    → p.vars.max = q.vars.max ∧ p.mainDegree.card < q.mainDegree.card :=
  Iff.trans lt_def <| Decidable.or_iff_not_imp_left

theorem lt_of_max_vars_lt : p.vars.max < q.vars.max → p < q :=
  fun h ↦ lt_def.mpr <| Or.inl h

@[simp] theorem not_lt_iff_ge : ¬(p < q) ↔ q ≤ p := by rw [le_def', lt_def', not_lt]

@[simp] theorem not_le_iff_gt : ¬(p ≤ q) ↔ q < p := by rw [le_def', lt_def', not_le]

theorem X_lt_of_lt [Nontrivial R] {i j : σ} : i < j → (X i : MvPolynomial σ R) < X j := fun h ↦ by
  apply lt_of_max_vars_lt; simpa only [vars_X, Finset.max_singleton, WithBot.coe_lt_coe] using h

scoped instance : Setoid (MvPolynomial σ R) := AntisymmRel.setoid (MvPolynomial σ R) (· ≤ ·)

noncomputable scoped instance : @DecidableRel (MvPolynomial σ R) _ (· ≈ ·) :=
  fun _ _ ↦ instDecidableAnd

theorem equiv_def'' : p ≈ q ↔ p ≤ q ∧ q ≤ p := Iff.rfl

theorem equiv_def' : p ≈ q ↔ p.rank = q.rank := Iff.trans equiv_def''
  (by rw [le_def', le_def']; exact Std.le_antisymm_iff)

theorem equiv_def : p ≈ q ↔ ¬p < q ∧ ¬q < p := Iff.trans equiv_def''
  (by rw [not_lt_iff_ge, not_lt_iff_ge, and_comm])

theorem equiv_iff : p ≈ q ↔ p.vars.max = q.vars.max ∧ p.mainDegree.card = q.mainDegree.card :=
  Iff.trans equiv_def' rank_eq_iff

theorem le_iff_lt_or_equiv : p ≤ q ↔ p < q ∨ p ≈ q := le_iff_lt_or_antisymmRel

theorem lt_of_equiv_of_lt {r : MvPolynomial σ R} : p ≈ q → q < r → p < r := lt_of_antisymmRel_of_lt

theorem lt_of_lt_of_equiv {r : MvPolynomial σ R} : p < q → q ≈ r → p < r := lt_of_lt_of_antisymmRel

theorem equiv_of_le_of_ge : p ≤ q → q ≤ p → p ≈ q := And.intro

protected theorem zero_le : 0 ≤ p :=
  le_def'.mpr <| StrictMono.minimal_preimage_bot (fun ⦃_ _⦄ a ↦ a) rfl p.rank

section WellFounded

theorem wellFoundedLT_variables_of_wellFoundedLT [Nontrivial R] :
    WellFoundedLT (MvPolynomial σ R) → WellFoundedLT σ := fun h ↦ by
  rw [WellFoundedLT, isWellFounded_iff, wellFounded_iff_isEmpty_descending_chain] at h ⊢
  contrapose! h
  rcases nonempty_subtype.mp h with ⟨f, hf⟩
  exact ⟨X ∘ f, fun n ↦ X_lt_of_lt <| hf n⟩

scoped instance [WellFoundedLT σ] : WellFoundedLT (MvPolynomial σ R) :=
  Subrelation.isWellFounded (InvImage _ _) lt_def'.mp

theorem wellFoundedLT_iff [Nontrivial R] : WellFoundedLT (MvPolynomial σ R) ↔ WellFoundedLT σ :=
  ⟨wellFoundedLT_variables_of_wellFoundedLT, @instWellFoundedLT _ _ _ _⟩

variable [WellFoundedLT (MvPolynomial σ R)] (PS : Set (MvPolynomial σ R))

theorem Set.has_min (h : PS.Nonempty) : ∃ p ∈ PS, ∀ q ∈ PS, ¬q < p :=
  haveI : WellFounded (· < ·) := @wellFounded_lt (MvPolynomial σ R) _ _
  WellFounded.has_min this PS h

/-- The minimal element of a nonempty set of multivariate polynomials. -/
noncomputable def Set.min (h : PS.Nonempty) : MvPolynomial σ R := Exists.choose (has_min PS h)

theorem Set.min_mem (h : PS.Nonempty) : (min PS h) ∈ PS := (Exists.choose_spec (has_min PS h)).1

end WellFounded

end Rank

end MvPolynomial
