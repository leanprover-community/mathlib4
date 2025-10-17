/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

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

/-- The number of roots of a real polynomial `p` is at most the number of roots of its derivative
that are not roots of `p` plus one. -/
theorem card_roots_toFinset_le_card_roots_derivative_diff_roots_succ (p : ℝ[X]) :
    p.roots.toFinset.card ≤ (p.derivative.roots.toFinset \ p.roots.toFinset).card + 1 := by
  rcases eq_or_ne (derivative p) 0 with hp' | hp'
  · rw [eq_C_of_derivative_eq_zero hp', roots_C, Multiset.toFinset_zero, Finset.card_empty]
    exact zero_le _
  have hp : p ≠ 0 := ne_of_apply_ne derivative (by rwa [derivative_zero])
  refine Finset.card_le_diff_of_interleaved fun x hx y hy hxy hxy' => ?_
  rw [Multiset.mem_toFinset, mem_roots hp] at hx hy
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuousOn (hx.trans hy.symm)
  refine ⟨z, ?_, hz1⟩
  rwa [Multiset.mem_toFinset, mem_roots hp', IsRoot, ← p.deriv]

/-- The number of roots of a real polynomial is at most the number of roots of its derivative plus
one. -/
theorem card_roots_toFinset_le_derivative (p : ℝ[X]) :
    p.roots.toFinset.card ≤ p.derivative.roots.toFinset.card + 1 :=
  p.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ.trans <| by
    grw [Finset.sdiff_subset]

/-- The number of roots of a real polynomial (counted with multiplicities) is at most the number of
roots of its derivative (counted with multiplicities) plus one. -/
theorem card_roots_le_derivative (p : ℝ[X]) :
    Multiset.card p.roots ≤ Multiset.card (derivative p).roots + 1 :=
  calc
    Multiset.card p.roots = ∑ x ∈ p.roots.toFinset, p.roots.count x :=
      (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ p.roots.toFinset, (p.roots.count x - 1 + 1) :=
      (Eq.symm <| Finset.sum_congr rfl fun _ hx => tsub_add_cancel_of_le <|
        Nat.succ_le_iff.2 <| Multiset.count_pos.2 <| Multiset.mem_toFinset.1 hx)
    _ = (∑ x ∈ p.roots.toFinset, (p.rootMultiplicity x - 1)) + p.roots.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones, count_roots]
    _ ≤ (∑ x ∈ p.roots.toFinset, p.derivative.rootMultiplicity x) +
          ((p.derivative.roots.toFinset \ p.roots.toFinset).card + 1) :=
      (add_le_add
        (Finset.sum_le_sum fun _ _ => rootMultiplicity_sub_one_le_derivative_rootMultiplicity _ _)
        p.card_roots_toFinset_le_card_roots_derivative_diff_roots_succ)
    _ ≤ (∑ x ∈ p.roots.toFinset, p.derivative.roots.count x) +
          ((∑ x ∈ p.derivative.roots.toFinset \ p.roots.toFinset,
            p.derivative.roots.count x) + 1) := by
      simp only [← count_roots, Finset.card_eq_sum_ones]
      gcongr with x hx
      rw [Nat.succ_le_iff, Multiset.count_pos, ← Multiset.mem_toFinset]
      exact (Finset.mem_sdiff.1 hx).1
    _ = Multiset.card (derivative p).roots + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_self_eq_union, ←
        Multiset.toFinset_sum_count_eq, ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx₂
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx₂

/-- The number of real roots of a polynomial is at most the number of roots of its derivative plus
one. -/
theorem card_rootSet_le_derivative {F : Type*} [CommRing F] [Algebra F ℝ] (p : F[X]) :
    Fintype.card (p.rootSet ℝ) ≤ Fintype.card (p.derivative.rootSet ℝ) + 1 := by
  simpa only [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe, derivative_map] using
    card_roots_toFinset_le_derivative (p.map (algebraMap F ℝ))

end Polynomial
