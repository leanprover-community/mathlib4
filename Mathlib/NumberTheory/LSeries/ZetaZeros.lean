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

## Main declarations

* `riemannZetaZeros`: The zeros of Riemann zeta function.

* `riemannZetaTrivialZeros`: The trivial zeros `{-2, -4, -6, …}`.

* `riemannZetaNontrivialZeros`: The zeros that are neither trivial zeros nor the point `s = 1`.

## Main results

* `isClosed_riemannZetaZeros`: `riemannZetaZeros` is closed.

* `isDiscrete_riemannZetaZeros`: `riemannZetaZeros` is discrete.

* `IsCompact.inter_riemannZetaZeros_finite`: for any compact set `S : Set ℂ`, the intersection
  `S ∩ riemannZetaZeros` is finite.

* `riemannHypothesis_iff_nontrivialZeros`: the Riemann hypothesis is equivalent to the statement
  that every nontrivial zero has real part `1 / 2`.
-/

@[expose] public section

/-- The zeros of Riemann's ζ-function. -/
def riemannZetaZeros : Set ℂ := riemannZeta ⁻¹' {0}

lemma mem_riemannZetaZeros {z : ℂ} :
    z ∈ riemannZetaZeros ↔ riemannZeta z = 0 := .rfl

/-- The complement of the zero set of `riemannZeta` is codiscrete within `{1}ᶜ`. -/
private lemma riemannZetaZeros_codiscreteWithin_compl_one :
    riemannZetaZerosᶜ ∈ Filter.codiscreteWithin {1}ᶜ := by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin (x := 2) ?_ (by simp) ?_
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1

/-- The complement of the zero set of `riemannZeta` is codiscrete. -/
private lemma compl_riemannZetaZeros_mem_codiscrete :
    riemannZetaZerosᶜ ∈ Filter.codiscrete ℂ := by
  have := riemannZetaZeros_codiscreteWithin_compl_one
  simp only [mem_codiscreteWithin, Set.mem_compl_iff, Set.mem_singleton_iff, sdiff_compl,
    Set.inf_eq_inter, Filter.disjoint_principal_right, mem_codiscrete, compl_compl] at this ⊢
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds
  · exact Filter.mem_of_superset (this x hx)
      (by grind [riemannZeta_one_ne_zero, mem_riemannZetaZeros])

lemma isClosed_riemannZetaZeros : IsClosed riemannZetaZeros :=
  by simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).1

lemma isDiscrete_riemannZetaZeros : IsDiscrete riemannZetaZeros :=
  by simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).2

/-- Any compact subset of `ℂ` contains only finitely many zeros of the Riemann zeta function. -/
lemma IsCompact.inter_riemannZetaZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZetaZeros).Finite := by
  apply (hS.inter_right isClosed_riemannZetaZeros).finite
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_right

open Filter in
lemma tendsto_riemannZeta_cofinite_cocompact :
    Tendsto ((↑) : riemannZetaZeros → ℂ) cofinite (cocompact ℂ) :=
  isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannZetaZeros

/-! ### Trivial and nontrivial zeros -/

/-- The trivial zeros of the Riemann zeta function: `{-2(n+1) | n : ℕ} = {-2, -4, -6, …}`.
These are indeed zeros by `riemannZeta_neg_two_mul_nat_add_one`. -/
def riemannZetaTrivialZeros : Set ℂ :=
  {s | ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)}

lemma mem_riemannZetaTrivialZeros {s : ℂ} :
    s ∈ riemannZetaTrivialZeros ↔ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := .rfl

/-- The nontrivial zeros of the Riemann zeta function: zeros that are neither trivial zeros
nor the point `s = 1` (where `riemannZeta` has its pole removed by a junk value). -/
def riemannZetaNontrivialZeros : Set ℂ :=
  riemannZetaZeros \ (riemannZetaTrivialZeros ∪ {1})

lemma mem_riemannZetaNontrivialZeros {s : ℂ} :
    s ∈ riemannZetaNontrivialZeros ↔
      riemannZeta s = 0 ∧ s ∉ riemannZetaTrivialZeros ∧ s ≠ 1 := by
  simp only [riemannZetaNontrivialZeros, Set.mem_sdiff, Set.mem_union, Set.mem_singleton_iff,
    mem_riemannZetaZeros, not_or]

/-- Trivial zeros are indeed zeros of `ζ`. -/
lemma riemannZetaTrivialZeros_subset_zeros :
    riemannZetaTrivialZeros ⊆ riemannZetaZeros := by
  intro s ⟨n, hs⟩
  rw [mem_riemannZetaZeros, hs]
  exact riemannZeta_neg_two_mul_nat_add_one n

lemma riemannZetaNontrivialZeros_subset_zeros :
    riemannZetaNontrivialZeros ⊆ riemannZetaZeros :=
  Set.sdiff_subset

/-- The Riemann hypothesis is equivalent to the statement that every nontrivial zero of the
Riemann zeta function has real part `1 / 2`. -/
theorem riemannHypothesis_iff_nontrivialZeros :
    RiemannHypothesis ↔ ∀ s ∈ riemannZetaNontrivialZeros, s.re = 1 / 2 := by
  constructor
  · intro hRH s hs
    rw [mem_riemannZetaNontrivialZeros] at hs
    obtain ⟨hzero, hnottriv, hne1⟩ := hs
    exact hRH s hzero (fun ⟨n, hn⟩ => hnottriv ⟨n, hn⟩) hne1
  · intro h s hzero hnottriv hne1
    refine h s (mem_riemannZetaNontrivialZeros.mpr ⟨hzero, fun ⟨n, hn⟩ => hnottriv ⟨n, hn⟩, hne1⟩)

end
