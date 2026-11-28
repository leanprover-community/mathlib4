/-
Copyright (c) 2026 Jan Bernlöhr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Bernlöhr
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Weighted sums and geometric tails

For extended nonnegative coefficients and a natural-valued size function, two quantitative
bounds compare a power-weighted sum with a geometrically weighted sum of tails. These bounds
hold without finiteness assumptions, for any real geometric base greater than one and any
positive natural cutoff. At positive order they give an equivalence of finiteness, with the
unweighted sum controlling the central region.

The real-valued summability results follow by applying these bounds to `ENNReal.ofReal`.
The reverse bound requires positive order: at order zero, summable coefficients can have
nonsummable geometric tails.
-/

public section

open scoped ENNReal

variable {b : ℝ}

private theorem ofReal_rpow_one_add_natCast (n : ℕ) (t : ℝ) :
    ENNReal.ofReal ((1 + (n : ℝ)) ^ t) = (1 + (n : ℝ≥0∞)) ^ t := by
  rw [← ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < 1 + (n : ℝ)),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast]

private theorem ofReal_geometric_weight (hb : 1 < b) (t : ℝ) (k : ℕ) :
    ENNReal.ofReal ((b ^ t) ^ k) = (ENNReal.ofReal b ^ t) ^ k := by
  rw [ENNReal.ofReal_pow (Real.rpow_nonneg (by positivity) _) _,
    ← ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < b)]

namespace ENNReal

variable {ι : Type*} {f : ι → ℝ≥0∞} (ν : ι → ℕ) {M : ℕ} {b t : ℝ}

/-- A power-weighted sum is bounded by the mass and geometrically weighted tails.
This bound also holds at order zero and for infinite sums. -/
theorem tsum_rpow_mul_le_geometric_tails (hb : 1 < b) (hM : 0 < M) (ht : 0 ≤ t) :
    (∑' i, (1 + (ν i : ℝ≥0∞)) ^ t * f i) ≤
      (1 + ENNReal.ofReal b * M) ^ t * ((∑' i, f i) +
        ∑' k : ℕ, (ENNReal.ofReal b ^ t) ^ k *
          (∑' i, if b ^ k * M ≤ ν i then f i else 0)) := by
  let a (k : ℕ) (i : ι) := (ENNReal.ofReal b ^ t) ^ k *
    (if b ^ k * M ≤ ν i then f i else 0)
  let D := (1 + ENNReal.ofReal b * M) ^ t
  have hpoint (i : ι) : (1 + (ν i : ℝ≥0∞)) ^ t * f i ≤
      D * f i + D * (∑' k, a k i) := by
    by_cases hi : ν i < M
    · have hbase : 1 + (ν i : ℝ≥0∞) ≤ 1 + ENNReal.ofReal b * M := by
        have hiE : (ν i : ℝ≥0∞) ≤ M := by exact_mod_cast hi.le
        have hbE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal b := by
          simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hb.le
        exact add_le_add le_rfl (hiE.trans (le_mul_of_one_le_left' hbE))
      exact (mul_le_mul_left (rpow_le_rpow hbase ht) _).trans le_self_add
    · have hMR : (0 : ℝ) < M := by exact_mod_cast hM
      have hiR : (M : ℝ) ≤ ν i := by exact_mod_cast (Nat.le_of_not_gt hi)
      obtain ⟨k, hlo, hhi⟩ := exists_nat_pow_near (x := (ν i : ℝ) / M)
        ((le_div_iff₀ hMR).mpr (by simpa using hiR)) hb
      have hcut : b ^ k * M ≤ ν i := (le_div_iff₀ hMR).mp hlo
      have hbase : 1 + (ν i : ℝ) ≤ (1 + b * M) * b ^ k := by
        have hlt := (div_lt_iff₀ hMR).mp hhi
        have hk : (1 : ℝ) ≤ b ^ k := one_le_pow₀ hb.le
        rw [pow_succ] at hlt
        nlinarith
      have hbaseE : 1 + (ν i : ℝ≥0∞) ≤
          (1 + ENNReal.ofReal b * M) * ENNReal.ofReal b ^ k := by
        have h := ENNReal.ofReal_le_ofReal hbase
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_one, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast] at h
        exact h
      have hweight : (1 + (ν i : ℝ≥0∞)) ^ t ≤ D * (ENNReal.ofReal b ^ t) ^ k := by
        calc
          _ ≤ ((1 + ENNReal.ofReal b * M) * ENNReal.ofReal b ^ k) ^ t :=
            rpow_le_rpow hbaseE ht
          _ = _ := by
            rw [mul_rpow_of_nonneg _ _ ht, ← rpow_natCast_mul,
              mul_comm (k : ℝ) t, rpow_mul, rpow_natCast]
      have hterm : (ENNReal.ofReal b ^ t) ^ k * f i ≤ ∑' j, a j i := by
        simpa only [a, ite_eq_left hcut] using (le_tsum (f := fun j ↦ a j i) k)
      calc
        _ ≤ D * ((ENNReal.ofReal b ^ t) ^ k * f i) := by
          simpa only [mul_assoc] using mul_le_mul_left hweight (f i)
        _ ≤ D * (∑' j, a j i) := mul_le_mul_right hterm D
        _ ≤ D * f i + D * (∑' j, a j i) := le_add_self
  calc
    _ ≤ ∑' i, (D * f i + D * (∑' k, a k i)) := tsum_le_tsum hpoint
    _ = D * ((∑' i, f i) + ∑' k, ∑' i, a k i) := by
      rw [tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ← mul_add, tsum_comm]
    _ = _ := by simp only [a, ENNReal.tsum_mul_left, D]

/-- Geometrically weighted tails are bounded by a power-weighted sum at positive order.
No finiteness assumption is needed. -/
theorem tsum_geometric_tails_le_rpow_mul (hb : 1 < b) (hM : 0 < M) (ht : 0 < t) :
    (∑' k : ℕ, (ENNReal.ofReal b ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then f i else 0)) ≤
      ENNReal.ofReal (b ^ t / (b ^ t - 1)) *
        ∑' i, (1 + (ν i : ℝ≥0∞)) ^ t * f i := by
  let r := b ^ t
  have hr : 1 < r := Real.one_lt_rpow hb ht
  let a (k : ℕ) (i : ι) := (ENNReal.ofReal b ^ t) ^ k *
    (if b ^ k * M ≤ ν i then f i else 0)
  have hcol (i : ι) : (∑' k, a k i) ≤
      ENNReal.ofReal (r / (r - 1)) * ((1 + (ν i : ℝ≥0∞)) ^ t * f i) := by
    obtain ⟨K, hlo, hhi⟩ := exists_nat_pow_near
      (x := 1 + (ν i : ℝ)) (le_add_of_nonneg_right (Nat.cast_nonneg _)) hb
    have hsupp (k : ℕ) (hk : k ∉ Finset.range (K + 1)) : a k i = 0 := by
      have hkK : K + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
      have hnot : ¬b ^ k * M ≤ ν i := by
        intro hcut
        have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM
        have hpowR : b ^ k ≤ (ν i : ℝ) :=
          (le_mul_of_one_le_right (pow_nonneg (by positivity) _) hMR).trans hcut
        have hpowK : b ^ (K + 1) ≤ b ^ k :=
          pow_le_pow_right₀ hb.le hkK
        linarith
      simp only [a, ite_eq_right hnot, mul_zero]
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
    have hgeoE : (∑ k ∈ Finset.range (K + 1), (ENNReal.ofReal b ^ t) ^ k) ≤
        ENNReal.ofReal (r / (r - 1)) * (1 + (ν i : ℝ≥0∞)) ^ t := by
      have h := ofReal_le_ofReal hgeo
      rw [ofReal_sum_of_nonneg (fun _ _ ↦ pow_nonneg (zero_lt_one.trans hr).le _),
        ofReal_mul (div_nonneg (zero_lt_one.trans hr).le (sub_pos.mpr hr).le)] at h
      change (∑ k ∈ Finset.range (K + 1), ENNReal.ofReal ((b ^ t) ^ k)) ≤
        ENNReal.ofReal (r / (r - 1)) * ENNReal.ofReal ((1 + (ν i : ℝ)) ^ t) at h
      simpa only [ofReal_geometric_weight hb, ofReal_rpow_one_add_natCast] using h
    calc
      _ ≤ ∑ k ∈ Finset.range (K + 1), (ENNReal.ofReal b ^ t) ^ k * f i :=
        Finset.sum_le_sum (fun k _ ↦ by dsimp only [a]; split <;> simp)
      _ = (∑ k ∈ Finset.range (K + 1), (ENNReal.ofReal b ^ t) ^ k) * f i :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ (ENNReal.ofReal (r / (r - 1)) * (1 + (ν i : ℝ≥0∞)) ^ t) * f i :=
        mul_le_mul_left hgeoE _
      _ = _ := mul_assoc _ _ _
  calc
    _ = ∑' i, ∑' k, a k i := by simp only [a, ENNReal.tsum_mul_left, tsum_comm]
    _ ≤ ∑' i, ENNReal.ofReal (r / (r - 1)) * ((1 + (ν i : ℝ≥0∞)) ^ t * f i) :=
      tsum_le_tsum hcol
    _ = _ := ENNReal.tsum_mul_left

/-- Finiteness of a positive power-weighted sum is equivalent to finiteness of the mass
and of its geometrically weighted tails. -/
theorem tsum_rpow_mul_lt_top_iff_geometric_tails (hb : 1 < b) (hM : 0 < M) (ht : 0 < t) :
    (∑' i, (1 + (ν i : ℝ≥0∞)) ^ t * f i) < ∞ ↔
      (∑' i, f i) < ∞ ∧ (∑' k : ℕ, (ENNReal.ofReal b ^ t) ^ k *
        (∑' i, if b ^ k * M ≤ ν i then f i else 0)) < ∞ := by
  constructor
  · intro hw
    refine ⟨lt_of_le_of_lt (tsum_le_tsum (fun i ↦ ?_)) hw,
      lt_of_le_of_lt (tsum_geometric_tails_le_rpow_mul ν hb hM ht)
        (ENNReal.mul_lt_top ofReal_lt_top hw)⟩
    exact le_mul_of_one_le_left' (one_le_rpow le_self_add ht)
  · rintro ⟨hs, h⟩
    exact lt_of_le_of_lt (tsum_rpow_mul_le_geometric_tails ν hb hM ht.le)
      (ENNReal.mul_lt_top (rpow_lt_top_of_nonneg ht.le
        (ENNReal.add_lt_top.mpr ⟨by simp, ENNReal.mul_lt_top (by simp) (by simp)⟩).ne)
        (ENNReal.add_lt_top.mpr ⟨hs, h⟩))

end ENNReal

variable {ι : Type*} {f : ι → ℝ} (ν : ι → ℕ) {M : ℕ} {b t : ℝ}

private theorem ofReal_geometric_tail (hf : ∀ i, 0 ≤ f i) (hs : Summable f)
    (hb : 1 < b) (k : ℕ) :
    ENNReal.ofReal ((b ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then f i else 0)) =
      (ENNReal.ofReal b ^ t) ^ k *
        (∑' i, if b ^ k * M ≤ ν i then ENNReal.ofReal (f i) else 0) := by
  have hnonneg (i : ι) : 0 ≤ if b ^ k * M ≤ ν i then f i else 0 := by
    split <;> simp [hf]
  have htail : Summable (fun i ↦ if b ^ k * M ≤ ν i then f i else 0) :=
    hs.of_nonneg_of_le hnonneg (fun i ↦ by split <;> simp [hf])
  rw [ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg (by positivity) _) _),
    ofReal_geometric_weight hb, ENNReal.ofReal_tsum_of_nonneg hnonneg htail]
  congr 1
  apply tsum_congr
  intro i
  split <;> simp

/-- Summability of geometrically weighted tails implies power-weighted summability.
The unweighted coefficients must also be summable. -/
theorem summable_rpow_mul_of_summable_geometric_tails
    (hf : ∀ i, 0 ≤ f i) (hs : Summable f) (hb : 1 < b) (hM : 0 < M) (ht : 0 ≤ t)
    (h : Summable (fun k : ℕ ↦ (b ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then f i else 0))) :
    Summable (fun i ↦ (1 + (ν i : ℝ)) ^ t * f i) := by
  have htail : (∑' k : ℕ, (ENNReal.ofReal b ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then ENNReal.ofReal (f i) else 0)) < ∞ := by
    simpa only [ofReal_geometric_tail ν hf hs hb] using h.tsum_ofReal_lt_top
  have hfinite := lt_of_le_of_lt
    (ENNReal.tsum_rpow_mul_le_geometric_tails (f := fun i ↦ ENNReal.ofReal (f i))
      ν hb hM ht)
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ht
      (ENNReal.add_lt_top.mpr ⟨by simp, ENNReal.mul_lt_top (by simp) (by simp)⟩).ne)
      (ENNReal.add_lt_top.mpr ⟨hs.tsum_ofReal_lt_top, htail⟩))
  have heq (i : ι) : ENNReal.ofReal ((1 + (ν i : ℝ)) ^ t * f i) =
      (1 + (ν i : ℝ≥0∞)) ^ t * ENNReal.ofReal (f i) := by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
      ofReal_rpow_one_add_natCast]
  rw [← tsum_congr heq] at hfinite
  exact (ENNReal.summable_toReal hfinite.ne).congr (fun i ↦
    ENNReal.toReal_ofReal (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hf i)))

/-- Positive power-weighted summability implies summability of the tails at the same
geometric rate. The positivity of the order is essential. -/
theorem summable_geometric_tails_of_summable_rpow_mul
    (hf : ∀ i, 0 ≤ f i) (hb : 1 < b) (hM : 0 < M) (ht : 0 < t)
    (hw : Summable (fun i ↦ (1 + (ν i : ℝ)) ^ t * f i)) :
    Summable (fun k : ℕ ↦ (b ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then f i else 0)) := by
  have hs : Summable f := hw.of_nonneg_of_le hf (fun i ↦
    le_mul_of_one_le_left (hf i)
      (Real.one_le_rpow (le_add_of_nonneg_right (Nat.cast_nonneg _)) ht.le))
  have hfinite : (∑' i, (1 + (ν i : ℝ≥0∞)) ^ t * ENNReal.ofReal (f i)) < ∞ := by
    have heq (i : ι) : ENNReal.ofReal ((1 + (ν i : ℝ)) ^ t * f i) =
        (1 + (ν i : ℝ≥0∞)) ^ t * ENNReal.ofReal (f i) := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
        ofReal_rpow_one_add_natCast]
    simpa only [heq] using hw.tsum_ofReal_lt_top
  have htail := ((ENNReal.tsum_rpow_mul_lt_top_iff_geometric_tails ν hb hM ht).mp hfinite).2
  simp_rw [← ofReal_geometric_tail ν hf hs hb] at htail
  have hnonneg (k : ℕ) : 0 ≤ (b ^ t) ^ k *
      (∑' i, if b ^ k * M ≤ ν i then f i else 0) := by
    apply mul_nonneg (pow_nonneg (Real.rpow_nonneg (by positivity) _) _)
    exact tsum_nonneg (fun i ↦ by split <;> simp [hf])
  exact (ENNReal.summable_toReal htail.ne).congr (fun k ↦ ENNReal.toReal_ofReal (hnonneg k))

/-- Positive power-weighted summability is equivalent to base summability and summability
of geometrically weighted tails, for any natural-valued size function. -/
theorem summable_rpow_mul_iff_summable_geometric_tails
    (hf : ∀ i, 0 ≤ f i) (hb : 1 < b) (hM : 0 < M) (ht : 0 < t) :
    Summable (fun i ↦ (1 + (ν i : ℝ)) ^ t * f i) ↔
      Summable f ∧ Summable (fun k : ℕ ↦ (b ^ t) ^ k *
        (∑' i, if b ^ k * M ≤ ν i then f i else 0)) := by
  constructor
  · intro hw
    refine ⟨hw.of_nonneg_of_le hf (fun i ↦ ?_),
      summable_geometric_tails_of_summable_rpow_mul ν hf hb hM ht hw⟩
    exact le_mul_of_one_le_left (hf i)
      (Real.one_le_rpow (le_add_of_nonneg_right (Nat.cast_nonneg _)) ht.le)
  · rintro ⟨hs, h⟩
    exact summable_rpow_mul_of_summable_geometric_tails ν hf hs hb hM ht.le h
