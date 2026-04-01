/-
Copyright (c) 2026 Huanyu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Discreteness of the zeros of the Riemann zeta function

We show that the zeros of the Riemann zeta function form a discrete subset of `ℂ`,
so that in particular any compact subset of `ℂ` contains only finitely many zeros.

## Main results

* `isClosed_riemannZeta_zeros`: `riemannZeta ⁻¹' {0}` is closed.

* `isDiscrete_riemannZeta_zeros`: `riemannZeta ⁻¹' {0}` is discrete.

* `riemannZeta_zeros_on_Compact_finite`: for any compact set `S : Set ℂ`, the intersection
  `S ∩ riemannZeta ⁻¹' {0}` is finite.
-/

public section

/-- The complement of the zero set of `riemannZeta` is codiscrete within `{1}ᶜ`. -/
private lemma riemannZeta_zeros_codiscreteWithin_compl_one :
    (riemannZeta ⁻¹' {0})ᶜ ∈ Filter.codiscreteWithin {1}ᶜ := by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin (x := 2) ?_ (by grind) ?_
  · exact riemannZeta_ne_zero_of_one_le_re (by aesop)
  · exact isConnected_compl_singleton_of_one_lt_rank (by aesop) 1

/-- The complement of the zero set of `riemannZeta` is codiscrete. -/
private lemma compl_riemannZeta_zeros_mem_codiscrete :
    (riemannZeta ⁻¹' {0})ᶜ ∈ Filter.codiscrete ℂ := by
  have := riemannZeta_zeros_codiscreteWithin_compl_one
  simp only [mem_codiscreteWithin, Set.mem_compl_iff, Set.mem_singleton_iff, sdiff_compl,
    Set.inf_eq_inter, Filter.disjoint_principal_right, mem_codiscrete, compl_compl] at this ⊢
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds
  · exact Filter.mem_of_superset (this x hx) (by grind [riemannZeta_one_ne_zero])

lemma isClosed_riemannZeta_zeros : IsClosed (riemannZeta ⁻¹' {0}) :=
  by simpa using (mem_codiscrete'.mp compl_riemannZeta_zeros_mem_codiscrete).1

lemma isDiscrete_riemannZeta_zeros : IsDiscrete (riemannZeta ⁻¹' {0}) :=
  by simpa using (mem_codiscrete'.mp compl_riemannZeta_zeros_mem_codiscrete).2

/-- Any compact subset of `ℂ` contains only finitely many zeros of the Riemann zeta function. -/
lemma riemannZeta_zeros_on_compact_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZeta ⁻¹' {0}).Finite := by
  apply (hS.inter_right isClosed_riemannZeta_zeros).finite
  exact isDiscrete_riemannZeta_zeros.mono (by grind)

end
