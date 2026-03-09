/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# tendsto_antidiagonal

`tendsto_antidiagonal` : Given two functions `f g` from a monoid to a non-archimedean Normed ring,
  and a function `C` from the monoid to ℝ, if `Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))`
  and `Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0))` holds, then we also have
  `Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0)`.

-/

@[expose] public section

open Filter
open scoped Topology Pointwise

open IsUltrametricDist

lemma tendsto_antidiagonal {M S : Type*} [AddMonoid M] [Finset.HasAntidiagonal M] [NormedRing S]
    [IsUltrametricDist S] {C : M → ℝ} (hC : ∀ a b, C (a + b) = C a * C b) {f g : M → S}
    (hf : Tendsto (fun i ↦ ‖f i‖ * C i) cofinite (𝓝 0))
    (hg : Tendsto (fun i ↦ ‖g i‖ * C i) cofinite (𝓝 0)) :
    Tendsto (fun a ↦ ‖∑ p ∈ Finset.antidiagonal a, (f p.1 * g p.2)‖ * C a) cofinite (𝓝 0) := by
  obtain ⟨F, Fpos, hF⟩ := (bddAbove_iff_exists_ge 1).mp
    (Tendsto.bddAbove_range_of_cofinite (Filter.Tendsto.norm hf))
  obtain ⟨G, Gpos, hG⟩ := (bddAbove_iff_exists_ge 1).mp
    (Tendsto.bddAbove_range_of_cofinite (Filter.Tendsto.norm hg))
  simp only [norm_mul, Real.norm_eq_abs, Set.mem_range, forall_exists_index,
    forall_apply_eq_imp_iff] at hF hG
  simp only [NormedAddGroup.tendsto_nhds_zero, gt_iff_lt, Real.norm_eq_abs, eventually_cofinite,
    not_lt] at *
  intro ε hε
  let I := {x | ε / G ≤ |‖f x‖ * C x|}
  let J := {x | ε / F ≤ |‖g x‖ * C x|}
  specialize hf (ε / G) (by positivity)
  specialize hg (ε / F) (by positivity)
  refine Set.Finite.subset (s := I + J) (Set.Finite.add (by aesop) (by aesop)) ?_
  by_contra h
  obtain ⟨t, ht, ht'⟩ := Set.not_subset.mp h
  simp only [abs_mul, abs_norm] at *
  have hh (i j : M) (ht_eq : t = i + j) : i ∉ I ∨ j ∉ J := by
    simp_rw [ht_eq] at ht'
    contrapose ht'
    simp only [not_or, not_not] at *
    use i; use ht'.1; use j; use ht'.2
  have hij (i j : M) (ht_eq : t = i + j) : ‖f i * g j‖ * |C t| < ε := by
      calc
      _ ≤ ‖f i‖ * ‖g j‖ * |C t| :=
        mul_le_mul_of_nonneg (norm_mul_le _ _) (le_refl _) (norm_nonneg _) (abs_nonneg _)
      _ ≤ ‖f i‖ * ‖g j‖ * (|C i| * |C j|) :=
        mul_le_mul_of_nonneg (le_refl _) (by simp [ht_eq, hC]) (by positivity) (by positivity)
      _ = (‖f i‖ * |C i|) * (‖g j‖ * |C j|) := by
        ring
      _ < ε := by
        rcases hh i j ht_eq with hi | hj
        · rw [← div_mul_cancel₀ ε (show G ≠ 0 by grind)]
          exact mul_lt_mul_of_nonneg_of_pos (by aesop) (hG j)
            (mul_nonneg (by positivity) (by positivity)) (by positivity)
        · rw [← div_mul_cancel₀ ε (show F ≠ 0 by grind), mul_comm]
          exact mul_lt_mul_of_nonneg_of_pos (by aesop) (hF i)
            (mul_nonneg (by positivity) (by positivity)) (by positivity)
  have Final : ‖∑ p ∈ Finset.antidiagonal t, f p.1 * g p.2‖ * |C t| < ε := by
    obtain ⟨k, hk, leq⟩ := exists_norm_finset_sum_le (Finset.antidiagonal t) (fun a ↦ f a.1 * g a.2)
    calc
    _ ≤ ‖f k.1 * g k.2‖ * |C t| := mul_le_mul_of_nonneg (leq) (le_refl _)
        (by positivity) (by positivity)
    _ < ε := hij k.1 k.2 (Eq.symm (by simpa using hk (Finset.nonempty_def.mpr
      (Exists.intro (t, 0) (by simp)))))
  grind
