/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.NumberTheory.MahlerMeasure
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Asymptotics of Reducible Polynomials

This file states and proves a key result of van der Waerden that the number of reducible monic
polynomials with `supNorm` bounded by `H` and degree `n + 1` is big O of `H ^ n` when `n + 1` is at
least `3`.

## Definitions

- `monicBoxPolyReducible`: The collection of monic, reducible polynomials of bounded `supNorm`
- `monicBoxPolyReducibleₘ`: The collection of monic, reducible polynomials of bounded
    `mahlerMeasure`

## Main results

- `isBigO_monicBoxPolyReducible_2`: Asymptotically, the number of monic, reducible polynomials
    of degree `n + 1` is `H ^ n` when `n + 1` is at least `3`.
-/

public section

variable (n : ℕ) (H : ℝ)

namespace Polynomial

open Asymptotics Filter

/-- The collection of monic, reducible polynomials of bounded `supNorm` -/
def monicBoxPolyReducible : Set ℤ[X] :=
  {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧ p.supNorm ≤ H ∧ ¬ Irreducible p}

/-- The collection of monic, reducible polynomials of bounded `mahlerMeasure` -/
def monicBoxPolyReducibleₘ : Set ℤ[X] :=
  {p : ℤ[X] | p.natDegree = n + 1 ∧ p.Monic ∧ (p.map (Int.castRingHom ℂ)).mahlerMeasure ≤ H ∧
    ¬ Irreducible p}

lemma monicBoxPolyReducible_subset_monicBoxPoly : monicBoxPolyReducible n H ⊆ monicBoxPoly n H := by
  intro p ⟨hdeg, hmon, hsup, _⟩
  exact (mem_monicBoxPoly ..).mpr ⟨hdeg, hmon, hsup⟩

lemma monicBoxPolyReducibleₘ_subset_monicBoxPolyₘ :
    monicBoxPolyReducibleₘ n H ⊆ monicBoxPolyₘ n H := by
  intro p ⟨hdeg, hmon, hM, _⟩
  exact (mem_monicBoxPolyₘ ..).mpr ⟨hdeg, hmon, hM⟩

lemma monicBoxPolyReducibleₘ_subset_monicBoxPolyReducible :
    monicBoxPolyReducibleₘ n H ⊆ monicBoxPolyReducible n ((n + 1).choose ((n + 1) / 2) * H) := by
  intro p ⟨hdeg, hmon, hM, hirr⟩
  refine ⟨hdeg, hmon, ?_, hirr⟩
  have hmem : p ∈ monicBoxPolyₘ n H := (mem_monicBoxPolyₘ ..).mpr ⟨hdeg, hmon, hM⟩
  obtain ⟨_, _, hsup⟩ :=
    (Polynomial.mem_monicBoxPoly ..).mp (monicBoxPolyₘ_subset_monicBoxPoly n H hmem)
  exact hsup

lemma monicBoxPolyReducible_subset_monicBoxPolyReducibleₘ :
    monicBoxPolyReducible n H ⊆ monicBoxPolyReducibleₘ n (√(n + 2) * H) := by
  intro p ⟨hdeg, hmon, hsup, hirr⟩
  have hmem : p ∈ monicBoxPoly n H := (Polynomial.mem_monicBoxPoly ..).mpr ⟨hdeg, hmon, hsup⟩
  obtain ⟨_, _, hM⟩ := (mem_monicBoxPolyₘ ..).mp (monicBoxPoly_subset_monicBoxPolyₘ n H hmem)
  exact ⟨hdeg, hmon, hM, hirr⟩

theorem finite_monicBoxPolyReducible : Set.Finite (monicBoxPolyReducible n H) :=
  (finite_monicBoxPoly n H).subset (monicBoxPolyReducible_subset_monicBoxPoly n H)

theorem finite_monicBoxPolyReducibleₘ : Set.Finite (monicBoxPolyReducibleₘ n H) :=
  (finite_monicBoxPolyₘ n H).subset (monicBoxPolyReducibleₘ_subset_monicBoxPolyₘ n H)

/-- A wrapper around `irreducible_of_monic` that provides some extra facts -/
private lemma exists_monic_factors_of_not_irreducible {p : ℤ[X]}
    (hmon : p.Monic) (hdeg : p.natDegree = n + 1) (hirr : ¬ Irreducible p) :
  ∃ f g : ℤ[X], p = f * g ∧ f.Monic ∧ g.Monic ∧ 1 ≤ f.natDegree ∧ 1 ≤ g.natDegree ∧
    f.natDegree + g.natDegree = n + 1 ∧ f.natDegree ≤ g.natDegree := by
  have hp1 : p ≠ 1 := by intro h; simp [h] at hdeg
  rw [irreducible_of_monic hmon hp1] at hirr
  push Not at hirr
  obtain ⟨f, g, hfmon, hgmon, hfg, hf1, hg1⟩ := hirr
  have hfdeg : 1 ≤ f.natDegree := by by_contra! h; exact hf1 (hfmon.natDegree_eq_zero.mp (by omega))
  have hgdeg : 1 ≤ g.natDegree := by by_contra! h; exact hg1 (hgmon.natDegree_eq_zero.mp (by omega))
  by_cases! h : f.natDegree ≤ g.natDegree
  · refine ⟨f, g, hfg.symm, hfmon, hgmon, hfdeg, hgdeg, ?_, h⟩
    rwa [← natDegree_mul hfmon.ne_zero hgmon.ne_zero, hfg]
  · refine ⟨g, f, ?_, hgmon, hfmon, hgdeg, hfdeg, ?_, h.le⟩
    · rw [mul_comm, hfg.symm]
    · rwa [← natDegree_mul hgmon.ne_zero hfmon.ne_zero, mul_comm, hfg]

private theorem monicBoxPolyReducible_subset_biUnion (hn : 2 ≤ n) (hH : 1 ≤ H) :
  monicBoxPolyReducible n H ⊆
    ⋃ k ∈ Finset.range ((n + 1) / 2), ⋃ l ∈ Finset.range (⌊((2 : ℝ) ^ n * (n + 2)) * H⌋₊ + 1),
      Set.image2 (· * ·)
        (monicBoxPoly k ((k + 1).choose ((k + 1) / 2) * (2 * 2 ^ l)))
        (monicBoxPoly (n - k - 1)
          ((n - k).choose ((n - k) / 2) * (√(n + 2) * H / 2 ^ l))) := by
  apply (monicBoxPolyReducible_subset_monicBoxPolyReducibleₘ n H).trans
  intro p ⟨hdeg, hmon, hM, hirr⟩
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_image2]
  obtain ⟨f, g, hpfg, hfmon, hgmon, hfdeg, hgdeg, hdegsum, hfgdeg_le⟩ :=
    exists_monic_factors_of_not_irreducible n hmon hdeg hirr
  have hMf_pos := one_le_mahlerMeasure_of_ne_zero hfmon.ne_zero
  have hMg_pos := one_le_mahlerMeasure_of_ne_zero hgmon.ne_zero
  obtain ⟨l, hl_le, hl_lt⟩ := exists_nat_pow_near hMf_pos (by norm_num : (1 : ℝ) < 2)
  refine ⟨f.natDegree - 1, by omega, l, Nat.lt_add_one_iff.mpr (Nat.le_floor ?_),
    f, ?_, g, ?_, hpfg.symm⟩
  · grw [show (l : ℝ) ≤ 2 ^ l by exact_mod_cast Nat.lt_two_pow_self.le, hl_le]
    rw [← mul_one ((f.map (Int.castRingHom ℂ)).mahlerMeasure)]
    grw [hMg_pos]
    rw [← mahlerMeasure_mul, ← Polynomial.map_mul, ← hpfg]
    grw [hM]
    gcongr
    rw [← one_mul √(n + 2)]
    gcongr
    · exact_mod_cast Nat.one_le_pow _ _ (by positivity)
    · rw [Real.sqrt_le_left (by positivity)]
      nlinarith
  · refine monicBoxPolyₘ_subset_monicBoxPoly _ _ ((mem_monicBoxPolyₘ ..).mpr ?_)
    refine ⟨by omega, hfmon, ?_⟩
    grw [hl_lt, mul_comm, pow_add, pow_one]
  · rw [show n - (f.natDegree - 1) = n - (f.natDegree - 1) - 1 + 1 by omega]
    refine monicBoxPolyₘ_subset_monicBoxPoly _ _ ((mem_monicBoxPolyₘ ..).mpr ?_)
    refine ⟨by omega, hgmon, ?_⟩
    rw [le_div_iff₀ (by positivity)]
    grw [hl_le]
    rwa [← mahlerMeasure_mul, ← Polynomial.map_mul, mul_comm g f, ← hpfg]

theorem isBigO_monicBoxPolyReducible_2 (hn : 2 ≤ n) :
    (fun H ↦ ((monicBoxPolyReducible n H).ncard : ℝ)) =O[atTop] (· ^ n) := by
  set K := (n + 1) / 2
  set D := (2 : ℝ) ^ n * (n + 2)
  have hD : 1 ≤ D := by
    rw [← mul_one 1]; simp only [D]; gcongr
    · exact_mod_cast Nat.one_le_pow _ _ (by omega)
    · norm_cast; omega
  -- A simple bound to get rid of the floor
  have hncard : ∀ m : ℕ, ∀ R : ℝ,
      ((monicBoxPoly m R).ncard : ℝ) ≤ (3 * |R|) ^ (m + 1) := by
    intro m R
    by_cases! hR : 1 ≤ R
    · rw [abs_of_nonneg (by positivity)]
      calc ((monicBoxPoly m R).ncard : ℝ)
          ≤ ((2 * ⌊R⌋₊ + 1) ^ (m + 1) : ℕ) := by exact_mod_cast ncard_monicBoxPoly_le m R
        _ ≤ (3 * R) ^ (m + 1) := by
            push_cast; gcongr
            linarith [Nat.floor_le (show 0 ≤ R by linarith)]
    · rw [ncard_monicBoxPoly_lt_one _ _ hR]
      norm_cast
      positivity
  calc
    (fun H ↦ ((monicBoxPolyReducible n H).ncard : ℝ))
      =O[atTop] fun H ↦ ((∑ k ∈ Finset.range K, ∑ l ∈ Finset.range (⌊D * H⌋₊ + 1),
        (monicBoxPoly k (((k + 1).choose ((k + 1) / 2) : ℝ) * (2 * 2 ^ l))).ncard *
        (monicBoxPoly (n - k - 1)
          ((n - k).choose ((n - k) / 2) * (√(n + 2) * H / 2 ^ l))).ncard) : ℝ) := by
      apply IsBigO.of_norm_eventuallyLE
      filter_upwards [eventually_ge_atTop 1] with H hH
      norm_cast
      apply (Set.ncard_le_ncard (monicBoxPolyReducible_subset_biUnion n H hn hH) ?_).trans
      · apply (Finset.set_ncard_biUnion_le _ _).trans
        apply Finset.sum_le_sum; intros
        apply (Finset.set_ncard_biUnion_le _ _).trans
        apply Finset.sum_le_sum; intros
        exact_mod_cast Set.ncard_image2_le (finite_monicBoxPoly _ _) (finite_monicBoxPoly _ _)
      · apply Set.Finite.biUnion (Finset.finite_toSet _)
        intros; apply Set.Finite.biUnion (Finset.finite_toSet _)
        intros; exact (finite_monicBoxPoly _ _).image2 _ (finite_monicBoxPoly _ _)
    _ =O[atTop] fun H ↦ ∑ k ∈ Finset.range K, ‖∑ l ∈ Finset.range (⌊D * H⌋₊ + 1),
        ‖((2 ^ l) ^ (k + 1)) * (H / 2 ^ l) ^ (n - k)‖‖ := by
      apply IsBigO.sum_congr
      intro k hk
      apply IsBigO.sum_congr'
      refine IsBigO.mul
        (IsBigO.of_bound ((3 * (k + 1).choose ((k + 1) / 2) * 2) ^ (k + 1)) ?_)
        (IsBigO.of_bound ((3 * (n - k).choose ((n - k) / 2) * √(n + 2)) ^ (n - k)) ?_)
      all_goals
      simp_rw [← principal_univ]
      rw [eventually_swap_iff, eventually_prod_principal_iff]
      filter_upwards [eventually_ge_atTop 1] with _ _ _ _
      rw [Prod.swap_prod_mk, Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (by positivity)]
      apply (hncard ..).trans_eq
      have : n - k - 1 + 1 = n - k := by
        apply Nat.sub_one_add_one
        rw [Nat.sub_ne_zero_iff_lt]
        calc k < K := Finset.mem_range.mp hk
          _ ≤ n := by omega
      try rw [this]
      simp only [abs_mul, Nat.abs_cast, Nat.abs_ofNat, abs_pow]
      try rw [abs_of_nonneg (by positivity)]
      ring
    _ =O[atTop] fun H ↦ ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range (⌊D * H⌋₊ + 1),
        ((2 ^ l) ^ (k + 1)) * (H / 2 ^ l) ^ (n - k) := by
        apply EventuallyEq.isBigO
        filter_upwards [eventually_ge_atTop 1] with a ha
        repeat first
        | rw [Real.norm_of_nonneg (by positivity)]
        | refine Finset.sum_congr rfl ?_
        | intros
    _ =O[atTop] fun H ↦ ∑ k ∈ Finset.range K, ∑ l ∈ Finset.range (⌊D * H⌋₊ + 1),
        H ^ (n - k) / 2 ^ (l * (n - 2 * k - 1)) := by
        apply EventuallyEq.isBigO
        filter_upwards [eventually_ge_atTop 1] with a ha
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        have h2kn : 2 * k + 1 ≤ n := by have := Finset.mem_range.mp hk; omega
        have hkn : k + 1 ≤ n - k := by omega
        have hexp : l * (k + 1) + l * (n - 2 * k - 1) = l * (n - k) := by
          rw [← mul_add]; congr 1; omega
        rw [div_pow, ← pow_mul (2 : ℝ), ← pow_mul (2 : ℝ), ← mul_div_assoc,
            div_eq_div_iff (by positivity) (by positivity),
            mul_comm (2 ^ (l * (k + 1))) (a ^ (n - k)), mul_assoc, ← pow_add, hexp]
    _ =O[atTop] (· ^ n) := by
      apply IsBigO.sum
      intro k hk
      by_cases! hcase : 2 * k + 2 ≤ n
      · have : (fun (x : ℝ) ↦ 1 * x ^ n) =O[atTop] (· ^ n) := by
          simpa [one_mul _] using isBigO_refl ..
        refine IsBigO.trans ?_ this
        simp_rw [div_eq_inv_mul, ← Finset.sum_mul]
        apply IsBigO.mul
        · rw [isBigO_one_iff]
          apply isBoundedUnder_of_eventually_le (a := ∑' (i : ℕ), ((2⁻¹ ^ (n - 2 * k - 1))) ^ i)
          filter_upwards with x
          rw [Real.norm_of_nonneg (by positivity)]
          simp_rw [← inv_pow, mul_comm _ (n - 2 * k - 1), pow_mul]
          refine (summable_geometric_of_lt_one (by positivity) ?_).sum_le_tsum _ ?_ |>.trans_eq rfl
          · exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
          · intros; positivity
        · exact Asymptotics.isBigO_pow_pow_atTop_of_le (by omega)
      · -- In this case n = 2 * k + 1, so n - 2 * k - 1 = 0 and so the sum is just a constant
        have hn2k1 : n = 2 * k + 1 := by have := Finset.mem_range.mp hk; omega
        simp only [show n - 2 * k - 1 = 0 by omega, mul_zero, pow_zero, div_one, Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
        have : (· ^ n) = fun (x : ℝ) ↦ x * x ^ (n - 1) := by
          funext x; rw [mul_comm, ← pow_succ]; congr; omega
        rw [this]
        apply IsBigO.mul
        · apply IsBigO.of_bound (2 * D)
          filter_upwards [eventually_ge_atTop 1] with H hH
          rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
          grw [Nat.floor_le (by positivity)]
          nlinarith
        · exact Asymptotics.isBigO_pow_pow_atTop_of_le (by omega)

end Polynomial

end
