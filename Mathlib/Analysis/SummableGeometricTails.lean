/-
Copyright (c) 2026 Jan Bernlöhr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Bernlöhr
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weighted summability and geometric tails

For nonnegative coefficients indexed by a type with a natural-valued size function, positive
power-weighted summability is equivalent to summability of geometrically weighted tails,
together with summability of the original coefficients.

The base-summability assumption controls the central region and ensures that the real-valued
tail sums are sums of summable families. The reverse implication requires positive order:
at order zero, summable coefficients can have nonsummable geometric tails.

The proof interchanges nonnegative double sums and estimates a finite geometric sum.
-/

public section

variable {ι : Type*} {f : ι → ℝ} (ν : ι → ℕ) {b M : ℕ} {t : ℝ}

/-- Summability of geometrically weighted tails implies power-weighted summability.
The unweighted coefficients must also be summable. -/
theorem summable_rpow_mul_of_summable_geometric_tails
    (hf : ∀ i, 0 ≤ f i) (hs : Summable f) (hb : 1 < b) (hM : 0 < M) (ht : 0 ≤ t)
    (h : Summable (fun k : ℕ ↦ ((b : ℝ) ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then f i else 0))) :
    Summable (fun i ↦ (1 + (ν i : ℝ)) ^ t * f i) := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  let r := (b : ℝ) ^ t
  let a (k : ℕ) (i : ι) := r ^ k * (if b ^ k * M ≤ ν i then f i else 0)
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have ha (k : ℕ) (i : ι) : 0 ≤ a k i := by
    dsimp only [a]
    split
    · exact mul_nonneg (pow_nonneg hr _) (hf _)
    · simp
  have htail (k : ℕ) : Summable (fun i ↦ if b ^ k * M ≤ ν i then f i else 0) :=
    hs.of_nonneg_of_le (fun i ↦ by
      split
      · exact hf i
      · exact le_rfl) (fun i ↦ by split <;> simp [hf])
  have hrow (k : ℕ) : Summable (a k) := (htail k).mul_left _
  have hrows : Summable (fun k ↦ ∑' i, a k i) := by
    simpa only [a, tsum_mul_left] using h
  have hprod : Summable (fun ki : ℕ × ι ↦ a ki.1 ki.2) :=
    (summable_prod_of_nonneg (fun ki ↦ ha ki.1 ki.2)).mpr ⟨hrow, hrows⟩
  have hcols := (summable_prod_of_nonneg (fun ik : ι × ℕ ↦ ha ik.2 ik.1)).mp
    hprod.prod_symm
  let D := (1 + (b : ℝ) * M) ^ t
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply ((hs.mul_left D).add (hcols.2.mul_left D)).of_nonneg_of_le
    (fun i ↦ mul_nonneg (Real.rpow_nonneg (by positivity) _) (hf i))
  intro i
  have hsum : 0 ≤ ∑' k, a k i := tsum_nonneg (fun k ↦ ha k i)
  by_cases hi : ν i < M
  · have hiR : (ν i : ℝ) < M := by exact_mod_cast hi
    have hMR : (0 : ℝ) ≤ M := by positivity
    have hbase : 1 + (ν i : ℝ) ≤ 1 + (b : ℝ) * M := by nlinarith
    have hweight := Real.rpow_le_rpow (by positivity) hbase ht
    have hle := mul_le_mul_of_nonneg_right hweight (hf i)
    exact hle.trans (le_add_of_nonneg_right (mul_nonneg hD hsum))
  · have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hiR : (M : ℝ) ≤ ν i := by exact_mod_cast (Nat.le_of_not_gt hi)
    obtain ⟨k, hlo, hhi⟩ := exists_nat_pow_near (x := (ν i : ℝ) / M)
      ((le_div_iff₀ hMR).mpr (by simpa using hiR)) hbR
    have hcut : b ^ k * M ≤ ν i := by
      have hle := (le_div_iff₀ hMR).mp hlo
      exact_mod_cast hle
    have hbase : 1 + (ν i : ℝ) ≤ (1 + (b : ℝ) * M) * (b : ℝ) ^ k := by
      have hlt := (div_lt_iff₀ hMR).mp hhi
      have hk : (1 : ℝ) ≤ (b : ℝ) ^ k := one_le_pow₀ hbR.le
      rw [pow_succ] at hlt
      nlinarith
    have hweight : (1 + (ν i : ℝ)) ^ t ≤ D * r ^ k := by
      calc
        _ ≤ ((1 + (b : ℝ) * M) * (b : ℝ) ^ k) ^ t :=
          Real.rpow_le_rpow (by positivity) hbase ht
        _ = D * r ^ k := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_pow_comm (by positivity)]
    have hterm : r ^ k * f i ≤ ∑' j, a j i := by
      simpa only [a, ite_eq_left hcut] using (hcols.1 i).le_tsum k (fun j _ ↦ ha j i)
    calc
      _ ≤ D * (r ^ k * f i) := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hweight (hf i)
      _ ≤ D * (∑' j, a j i) := mul_le_mul_of_nonneg_left hterm hD
      _ ≤ D * f i + D * (∑' j, a j i) :=
        le_add_of_nonneg_left (mul_nonneg hD (hf i))

/-- Positive power-weighted summability implies summability of the tails at the same
geometric rate. The positivity of the order is essential. -/
theorem summable_geometric_tails_of_summable_rpow_mul
    (hf : ∀ i, 0 ≤ f i) (hb : 1 < b) (hM : 0 < M) (ht : 0 < t)
    (hw : Summable (fun i ↦ (1 + (ν i : ℝ)) ^ t * f i)) :
    Summable (fun k : ℕ ↦ ((b : ℝ) ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then f i else 0)) := by
  have hbR : (1 : ℝ) < b := by exact_mod_cast hb
  let r := (b : ℝ) ^ t
  have hr : 1 < r := Real.one_lt_rpow hbR ht
  let a (k : ℕ) (i : ι) := r ^ k * (if b ^ k * M ≤ ν i then f i else 0)
  have ha (k : ℕ) (i : ι) : 0 ≤ a k i := by
    dsimp only [a]
    split
    · exact mul_nonneg (pow_nonneg (zero_lt_one.trans hr).le _) (hf _)
    · simp
  have hcol (i : ι) : Summable (fun k ↦ a k i) ∧
      (∑' k, a k i) ≤ (r / (r - 1)) * ((1 + (ν i : ℝ)) ^ t * f i) := by
    obtain ⟨K, hlo, hhi⟩ := exists_nat_pow_near
      (x := 1 + (ν i : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg _)) hbR
    have hsupp (k : ℕ) (hk : k ∉ Finset.range (K + 1)) : a k i = 0 := by
      have hkK : K + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
      have hnot : ¬b ^ k * M ≤ ν i := by
        intro hcut
        have hpow : b ^ k ≤ ν i := (Nat.le_mul_of_pos_right _ hM).trans hcut
        have hpowR : (b : ℝ) ^ k ≤ (ν i : ℝ) := by exact_mod_cast hpow
        have hpowK : (b : ℝ) ^ (K + 1) ≤ (b : ℝ) ^ k :=
          pow_le_pow_right₀ hbR.le hkK
        linarith
      simp only [a, ite_eq_right hnot, mul_zero]
    have hsum : Summable (fun k ↦ a k i) := summable_of_ne_finset_zero hsupp
    refine ⟨hsum, ?_⟩
    rw [tsum_eq_sum hsupp]
    have hgeo : (∑ k ∈ Finset.range (K + 1), r ^ k) ≤
        (r / (r - 1)) * (1 + (ν i : ℝ)) ^ t := by
      rw [geom_sum_eq hr.ne' (K + 1)]
      apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
      have hpow : r ^ K ≤ (1 + (ν i : ℝ)) ^ t := by
        dsimp only [r]
        rw [Real.rpow_pow_comm (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hlo ht.le
      have hmul := mul_le_mul_of_nonneg_left hpow (zero_lt_one.trans hr).le
      have he : r / (r - 1) * (1 + (ν i : ℝ)) ^ t * (r - 1) =
          r * (1 + (ν i : ℝ)) ^ t := by
        field_simp [sub_ne_zero.mpr hr.ne']
      rw [he, pow_succ]
      nlinarith
    calc
      _ ≤ ∑ k ∈ Finset.range (K + 1), r ^ k * f i :=
        Finset.sum_le_sum (fun k _ ↦ by
          dsimp only [a]
          split
          · exact le_rfl
          · simp only [mul_zero]
            exact mul_nonneg (pow_nonneg (zero_lt_one.trans hr).le _) (hf i))
      _ = (∑ k ∈ Finset.range (K + 1), r ^ k) * f i := (Finset.sum_mul _ _ _).symm
      _ ≤ ((r / (r - 1)) * (1 + (ν i : ℝ)) ^ t) * f i :=
        mul_le_mul_of_nonneg_right hgeo (hf i)
      _ = _ := by ring
  have hcols : Summable (fun i ↦ ∑' k, a k i) :=
    (hw.mul_left (r / (r - 1))).of_nonneg_of_le
      (fun i ↦ tsum_nonneg (fun k ↦ ha k i)) (fun i ↦ (hcol i).2)
  have hprod : Summable (fun ik : ι × ℕ ↦ a ik.2 ik.1) :=
    (summable_prod_of_nonneg (fun ik ↦ ha ik.2 ik.1)).mpr ⟨fun i ↦ (hcol i).1, hcols⟩
  have hrows := ((summable_prod_of_nonneg (fun ki : ℕ × ι ↦ ha ki.1 ki.2)).mp
    hprod.prod_symm).2
  simpa only [a, tsum_mul_left] using hrows

/-- Positive power-weighted summability is equivalent to base summability and summability
of geometrically weighted tails, for any natural-valued size function. -/
theorem summable_rpow_mul_iff_summable_geometric_tails
    (hf : ∀ i, 0 ≤ f i) (hb : 1 < b) (hM : 0 < M) (ht : 0 < t) :
    Summable (fun i ↦ (1 + (ν i : ℝ)) ^ t * f i) ↔
      Summable f ∧ Summable (fun k : ℕ ↦ ((b : ℝ) ^ t) ^ k *
        (∑' i, if b ^ k * M ≤ ν i then f i else 0)) := by
  constructor
  · intro hw
    refine ⟨hw.of_nonneg_of_le hf (fun i ↦ ?_),
      summable_geometric_tails_of_summable_rpow_mul ν hf hb hM ht hw⟩
    exact le_mul_of_one_le_left (hf i)
      (Real.one_le_rpow (le_add_of_nonneg_right (Nat.cast_nonneg _)) ht.le)
  · rintro ⟨hs, h⟩
    exact summable_rpow_mul_of_summable_geometric_tails ν hf hs hb hM ht.le h
