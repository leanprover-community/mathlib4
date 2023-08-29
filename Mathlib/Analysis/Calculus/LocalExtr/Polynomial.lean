/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

#align_import analysis.calculus.local_extr from "leanprover-community/mathlib"@"3bce8d800a6f2b8f63fe1e588fd76a9ff4adcebe"

/-!
# Rolle's Theorem for polynomials

In this file we use Rolle's Theorem
to relate the number of real roots of a real polynomial and its derivative.
Namely, we prove the following facts.

* `Polynomial.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ`:
  the number of roots of a real polynomial `p` is at most the number of roots of its derivative
  that are not roots of `p` plus one.
* `Polynomial.card_roots_toFinset_le_derivative`, `Polynomial.card_rootSet_le_derivative`:
  the number of roots of a real polynomial
  is at most the number of roots of its derivative plus one.
* `Polynomial.card_roots_le_derivative`: same, but the roots are counted with multiplicities.

## Keywords

polynomial, Rolle's Theorem, root
-/

namespace Polynomial

open scoped BigOperators

/-- The number of roots of a real polynomial `p` is at most the number of roots of its derivative
that are not roots of `p` plus one. -/
theorem card_roots_toFinset_le_card_roots_derivative_diff_roots_succ (p : ℝ[X]) :
    p.roots.toFinset.card ≤ (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 := by
  cases' eq_or_ne (derivative p) 0 with hp' hp'
  -- ⊢ Finset.card (Multiset.toFinset (roots p)) ≤ Finset.card (Multiset.toFinset ( …
  · rw [eq_C_of_derivative_eq_zero hp', roots_C, Multiset.toFinset_zero, Finset.card_empty]
    -- ⊢ 0 ≤ Finset.card (Multiset.toFinset (roots (↑derivative (↑C (coeff p 0)))) \  …
    exact zero_le _
    -- 🎉 no goals
  have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  -- ⊢ Finset.card (Multiset.toFinset (roots p)) ≤ Finset.card (Multiset.toFinset ( …
  refine' Finset.card_le_diff_of_interleaved fun x hx y hy hxy hxy' => _
  -- ⊢ ∃ z, z ∈ Multiset.toFinset (roots (↑derivative p)) ∧ x < z ∧ z < y
  rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
  -- ⊢ ∃ z, z ∈ Multiset.toFinset (roots (↑derivative p)) ∧ x < z ∧ z < y
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuousOn (hx.trans hy.symm)
  -- ⊢ ∃ z, z ∈ Multiset.toFinset (roots (↑derivative p)) ∧ x < z ∧ z < y
  refine' ⟨z, _, hz1⟩
  -- ⊢ z ∈ Multiset.toFinset (roots (↑derivative p))
  rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]
  -- 🎉 no goals
#align polynomial.card_roots_to_finset_le_card_roots_derivative_diff_roots_succ Polynomial.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ

/-- The number of roots of a real polynomial is at most the number of roots of its derivative plus
one. -/
theorem card_roots_toFinset_le_derivative (p : ℝ[X]) :
    p.roots.toFinset.card ≤ p.derivative.roots.toFinset.card + 1 :=
  p.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ.trans <|
    add_le_add_right (Finset.card_mono <| Finset.sdiff_subset _ _) _
#align polynomial.card_roots_to_finset_le_derivative Polynomial.card_roots_toFinset_le_derivative

/-- The number of roots of a real polynomial (counted with multiplicities) is at most the number of
roots of its derivative (counted with multiplicities) plus one. -/
theorem card_roots_le_derivative (p : ℝ[X]) :
    Multiset.card p.roots ≤ Multiset.card (derivative p).roots + 1 :=
  calc
    Multiset.card p.roots = ∑ x in p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x in p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun x hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x in p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
      -- 🎉 no goals
    _ ≤ (∑ x in p.roots.toFinset, p.derivative.rootMultiplicity x) +
          ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
      (add_le_add
        (Finset.sum_le_sum fun x _ => rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
        p.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ)
    _ ≤ (∑ x in p.roots.toFinset, p.derivative.roots.count x) +
          ((∑ x in p.derivative.roots.toFinset \ p.roots.toFinset,
            p.derivative.roots.count x) + 1) := by
      simp only [← count_roots]
      -- ⊢ ∑ x in Multiset.toFinset (roots p), Multiset.count x (roots (↑derivative p)) …
      refine' add_le_add_left (add_le_add_right ((Finset.card_eq_sum_ones _).trans_le _) _) _
      -- ⊢ ∑ x in Multiset.toFinset (roots (↑derivative p)) \ Multiset.toFinset (roots  …
      refine' Finset.sum_le_sum fun x hx => Nat.succ_le_iff.2 <| _
      -- ⊢ 0 < Multiset.count x (roots (↑derivative p))
      rw [Multiset.count_pos, ← Multiset.mem_toFinset]
      -- ⊢ x ∈ Multiset.toFinset (roots (↑derivative p))
      exact (Finset.mem_sdiff.1 hx).1
      -- 🎉 no goals
    _ = Multiset.card (derivative p).roots + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union, ←
        Multiset.toFinset_sum_count_eq, ← Finset.sum_subset (Finset.subset_union_right _ _)]
      intro x _ hx₂
      -- ⊢ Multiset.count x (roots (↑derivative p)) = 0
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂
      -- 🎉 no goals
#align polynomial.card_roots_le_derivative Polynomial.card_roots_le_derivative

/-- The number of real roots of a polynomial is at most the number of roots of its derivative plus
one. -/
theorem card_rootSet_le_derivative {F : Type*} [CommRing F] [Algebra F ℝ] (p : F[X]) :
    Fintype.card (p.rootSet ℝ) ≤ Fintype.card (p.derivative.rootSet ℝ) + 1 := by
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    card_roots_toFinset_le_derivative (p.map (algebraMap F ℝ))
#align polynomial.card_root_set_le_derivative Polynomial.card_rootSet_le_derivative

end Polynomial
