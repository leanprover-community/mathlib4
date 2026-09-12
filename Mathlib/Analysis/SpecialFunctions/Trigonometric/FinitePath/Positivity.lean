/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.Coherence

/-!
# Strict positivity of finite path coherence

The squared coherence equals one in sizes two and three, and exceeds one from size four.
-/

@[expose] public section

noncomputable section
open Real Filter
open scoped Topology
namespace Real.FinitePath
theorem coherenceSq_two : coherenceSq 2 = 1 := by
  simp only [coherenceSq, size, angle, Nat.cast_ofNat]
  rw [show (2 : ℝ)+1 = 3 by norm_num, show (2 : ℝ)-1 = 1 by norm_num]
  rw [cos_pi_div_three, sin_pi_div_three]
  have h3 : (√3)^2 = (3 : ℝ) := sq_sqrt (by norm_num)
  have hs : (√3 / 2)^2 = (3 : ℝ)/4 := by rw [div_pow, h3]; norm_num
  simp [hs]; norm_num

theorem coherenceSq_three : coherenceSq 3 = 1 := by
  simp only [coherenceSq, size, angle, Nat.cast_ofNat]
  rw [show (3 : ℝ)+1 = 4 by norm_num, show (3 : ℝ)-1 = 2 by norm_num]
  rw [cos_pi_div_four, sin_pi_div_four]
  have h2 : (√2)^2 = (2 : ℝ) := sq_sqrt (by norm_num)
  have hs : (√2 / 2)^2 = (2 : ℝ)/4 := by rw [div_pow, h2]; norm_num
  simp [hs]; norm_num

theorem coherenceSq_four : coherenceSq 4 = (99 - 42 * √5) / 5 := by
  simp only [coherenceSq, size, angle, Nat.cast_ofNat]
  rw [show (4 : ℝ)+1 = 5 by norm_num, show (4 : ℝ)-1 = 3 by norm_num]
  have hc0 : cos (π / 5) = (1 + √5) / 4 := cos_pi_div_five
  have hs5 : (√5)^2 = (5 : ℝ) := sq_sqrt (by norm_num)
  have hcos2 : cos (π / 5)^2 = (3 + √5) / 8 := by
    rw [hc0]; ring_nf; simp [hs5]; ring
  have hsin2 : sin (π / 5)^2 = (5 - √5) / 8 := by
    have : sin (π / 5)^2 = 1 - cos (π / 5)^2 := by
      rw [← sin_sq_add_cos_sq (π / 5)]; ring
    rw [this, hcos2]; ring
  rw [hcos2, hsin2]
  ring_nf; field_simp; ring_nf; simp [hs5]; ring

theorem one_lt_coherenceSq_four : 1 < coherenceSq 4 := by
  rw [coherenceSq_four]
  have h5 : (0 : ℝ) < 5 := by norm_num
  rw [one_lt_div h5]
  have h : √5 < (47 : ℝ) / 21 := by
    rw [sqrt_lt (by norm_num : (0 : ℝ) ≤ 5) (by positivity)]; norm_num
  have hs : (√5)^2 = (5 : ℝ) := sq_sqrt (by norm_num)
  nlinarith [hs, h, sqrt_nonneg 5]

theorem coherenceSq_five : coherenceSq 5 = (28 : ℝ)/27 := by
  simp only [coherenceSq, size, angle, Nat.cast_ofNat]
  rw [show (5 : ℝ)+1 = 6 by norm_num, show (5 : ℝ)-1 = 4 by norm_num]
  rw [cos_pi_div_six, sin_pi_div_six]
  have h3 : (√3)^2 = (3 : ℝ) := sq_sqrt (by norm_num)
  have hc : (√3 / 2)^2 = (3 : ℝ)/4 := by rw [div_pow, h3]; norm_num
  simp [hc]; norm_num

theorem one_lt_coherenceSq_five : 1 < coherenceSq 5 := by
  rw [coherenceSq_five]; norm_num

theorem one_lt_coherenceSq_six : 1 < coherenceSq 6 := by
  simp only [coherenceSq, size, angle, Nat.cast_ofNat]
  rw [show (6 : ℝ)+1 = 7 by norm_num, show (6 : ℝ)-1 = 5 by norm_num]
  set θ := π / 7
  have h7 : (0 : ℝ) < 7 := by norm_num
  have hθpos : 0 < θ := div_pos pi_pos h7
  have hθlt : θ < π / 2 := by
    rw [div_lt_div_iff₀ h7 (by norm_num : (0 : ℝ)<2)]; nlinarith [pi_pos]
  have hπlo : (314 : ℝ)/100 < π := by have := pi_gt_d2; norm_num at this ⊢; linarith
  have hπhi : π < (315 : ℝ)/100 := by have := pi_lt_d2; norm_num at this ⊢; linarith
  have hθ_lt_one : θ < 1 := by
    have : θ < (315 : ℝ)/100 / 7 := by
      simp only [θ]; exact div_lt_div_of_pos_right hπhi h7
    exact lt_trans this (by norm_num)
  have hs0pos : 0 < θ - θ^3/6 := by
    have : θ^2 < 6 := by nlinarith [hθpos, hθ_lt_one]
    nlinarith [hθpos, this]
  have hsin : θ - θ^3/6 < sin θ := sin_gt_sub_cube hθpos
  set s0 := θ - θ^3/6
  have hcos_pos : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hθpos], hθlt⟩
  have hcos2 : cos θ ^ 2 < 1 - s0 ^ 2 := by
    have hsq : s0^2 < sin θ ^ 2 :=
      pow_lt_pow_left₀ hsin (le_of_lt hs0pos) (by norm_num)
    have : cos θ ^ 2 = 1 - sin θ ^ 2 := by rw [← sin_sq_add_cos_sq θ]; ring
    linarith
  have hs0_bound :
      s0 ≥ ((314 : ℝ)/100 / 7) * (1 - ((315 : ℝ)/100 / 7)^2 / 6) := by
    have hs0θ : s0 = θ * (1 - θ^2/6) := by ring
    have hθlo : (314 : ℝ)/100 / 7 ≤ θ := by
      simp only [θ]; exact div_le_div_of_nonneg_right hπlo.le (le_of_lt h7)
    have hθhi2 : θ ≤ (315 : ℝ)/100 / 7 := by
      simp only [θ]; exact div_le_div_of_nonneg_right hπhi.le (le_of_lt h7)
    have hfac : 1 - θ^2/6 ≥ 1 - ((315 : ℝ)/100 / 7)^2 / 6 := by
      nlinarith [hθpos, hθhi2]
    rw [hs0θ]; nlinarith [hθlo, hfac, hθpos]
  have hpos_lo :
      (0 : ℝ) ≤ ((314 : ℝ)/100 / 7) * (1 - ((315 : ℝ)/100 / 7)^2 / 6) := by
    norm_num
  have hs0sq :
      s0^2 ≥ (((314 : ℝ)/100 / 7) * (1 - ((315 : ℝ)/100 / 7)^2 / 6))^2 :=
    pow_le_pow_left₀ hpos_lo hs0_bound 2
  have h1s0 :
      1 - s0^2 ≤
        1 - (((314 : ℝ)/100 / 7) * (1 - ((315 : ℝ)/100 / 7)^2 / 6))^2 := by
    nlinarith [hs0sq]
  have hlt_thr :
      1 - (((314 : ℝ)/100 / 7) * (1 - ((315 : ℝ)/100 / 7)^2 / 6))^2 <
        (75 : ℝ)/92 := by
    norm_num
  have hcos_thr : cos θ ^ 2 < (75 : ℝ)/92 :=
    lt_of_lt_of_le hcos2 (le_trans h1s0 hlt_thr.le)
  have hs : sin θ ^ 2 = 1 - cos θ ^ 2 := by
    rw [← sin_sq_add_cos_sq θ]; ring
  rw [hs]
  set c := cos θ ^ 2
  have hcpos : 0 < c := sq_pos_of_pos hcos_pos
  have hc_thr : c < (75 : ℝ)/92 := hcos_thr
  have hsimp :
      2 * 5 / (7 * c) * (((7 : ℝ)^2 + 2) / 6 * (1 - c) - 1) =
        5 * (15 - 17 * c) / (7 * c) := by
    field_simp; ring
  rw [hsimp]
  have hden : 0 < 7 * c := by positivity
  rw [one_lt_div hden]
  nlinarith [hc_thr, hcpos]

/-- The cosine threshold equivalent to coherence squared exceeding one. -/
noncomputable def cosineThreshold (d : ℕ) : ℝ :=
  ((d : ℝ) - 1) * (((d : ℝ) + 1) ^ 2 - 4) /
    (((d : ℝ) - 1) * (((d : ℝ) + 1) ^ 2 + 2) + 3 * ((d : ℝ) + 1))

theorem coherenceSq_eq_cos (d : ℕ) (hd : 2 ≤ d)
    (hcos_ne : cos (π / ((d : ℝ) + 1)) ≠ 0) :
    coherenceSq d =
      ((d : ℝ) - 1) / (3 * ((d : ℝ) + 1) * cos (π / ((d : ℝ) + 1)) ^ 2) *
        ((((d : ℝ) + 1) ^ 2 - 4) -
          (((d : ℝ) + 1) ^ 2 + 2) * cos (π / ((d : ℝ) + 1)) ^ 2) := by
  set N := (d : ℝ) + 1
  set c := cos (π / N) ^ 2
  have hs : sin (π / N) ^ 2 = 1 - c := by
    have := sin_sq_add_cos_sq (π / N)
    simp only [c] at *; linarith
  have hcos_ne' : cos (π / N) ≠ 0 := by simpa [N] using hcos_ne
  simp only [coherenceSq, size, angle]
  change
      2 * ((d : ℝ) - 1) / (N * cos (π / N) ^ 2) *
          (((N ^ 2 + 2) / 6) * sin (π / N) ^ 2 - 1) =
        ((d : ℝ) - 1) / (3 * N * cos (π / N) ^ 2) *
          ((N ^ 2 - 4) - (N ^ 2 + 2) * cos (π / N) ^ 2)
  rw [hs]
  have hc0 : c ≠ 0 := by
    have : cos (π / N) ^ 2 ≠ 0 := pow_ne_zero 2 hcos_ne'
    simpa [c] using this
  have hN0 : N ≠ 0 := by positivity
  simp only [c] at hc0 ⊢
  field_simp [hcos_ne', hN0]
  ring

theorem one_lt_coherenceSq_of_cos_lt
    (d : ℕ) (hd : 2 ≤ d)
    (hcos_pos : 0 < cos (π / ((d : ℝ) + 1)))
    (hthr : cos (π / ((d : ℝ) + 1)) ^ 2 < cosineThreshold d) :
    1 < coherenceSq d := by
  set N := (d : ℝ) + 1
  set c := cos (π / N) ^ 2
  have hcpos : 0 < c := by
    change 0 < cos (π / N) ^ 2
    exact sq_pos_of_pos (by simpa [N] using hcos_pos)
  have hform : coherenceSq d =
      ((d : ℝ) - 1) / (3 * N * c) * ((N ^ 2 - 4) - (N ^ 2 + 2) * c) := by
    have hne : cos (π / ((d : ℝ) + 1)) ≠ 0 := hcos_pos.ne'
    simpa [N, c] using coherenceSq_eq_cos d hd hne
  have hden : 0 < 3 * N * c := by
    have : 0 < N := by positivity
    positivity
  have ha : 0 < (d : ℝ) - 1 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set e := (N ^ 2 - 4) - (N ^ 2 + 2) * c with hedef
  have hthr' : c <
      ((d : ℝ) - 1) * (N ^ 2 - 4) /
        (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) := by
    simpa [c, N, cosineThreshold] using hthr
  have hden' : 0 < ((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N := by positivity
  have hN2 : 0 < N ^ 2 - 4 := by
    have : (3 : ℝ) ≤ N := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    nlinarith
  have hthr_mul :
      c * (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) <
        ((d : ℝ) - 1) * (N ^ 2 - 4) :=
    (lt_div_iff₀ hden').mp hthr'
  have he : 0 < e := by
    have hcmp :
        ((d : ℝ) - 1) * (N ^ 2 - 4) /
            (((d : ℝ) - 1) * (N ^ 2 + 2) + 3 * N) <
          (N ^ 2 - 4) / (N ^ 2 + 2) := by
      rw [div_lt_div_iff₀ hden' (by positivity)]
      nlinarith [hN2, ha, show 0 < N by positivity]
    have hc_mid : c < (N ^ 2 - 4) / (N ^ 2 + 2) := lt_trans hthr' hcmp
    have : c * (N ^ 2 + 2) < N ^ 2 - 4 := (lt_div_iff₀ (by positivity)).mp hc_mid
    simp only [e]; linarith
  have hmul : ((d : ℝ) - 1) * e > 3 * N * c := by
    simp only [e]
    nlinarith [hthr_mul]
  have hgt : ((d : ℝ) - 1) / (3 * N * c) * e > 1 := by
    have : ((d : ℝ) - 1) * e / (3 * N * c) > 1 :=
      (one_lt_div hden).mpr hmul
    convert this using 1; ring
  rwa [hform]

theorem key_poly_nat (n : ℕ) (hn : 7 ≤ n) :
    ((314 : ℝ)/100)^2 * (1 - ((315 : ℝ)/100)^2 / (3 * (n:ℝ)^2)) *
        ((n:ℝ)^3 - 2*(n:ℝ)^2 + 5*(n:ℝ) - 4) >
      (9*(n:ℝ) - 12) * (n:ℝ)^2 := by
  by_cases hle : n ≤ 40
  · interval_cases n <;> norm_num
  · have hnR : (41 : ℝ) ≤ n := by exact_mod_cast (show 41 ≤ n by omega)
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 41) hnR
    have h314 : ((314 : ℝ)/100)^2 ≥ (985 : ℝ)/100 := by norm_num
    have hfac : 1 - ((315 : ℝ)/100)^2 / (3 * (n:ℝ)^2) ≥ (99 : ℝ)/100 := by
      have hle' : ((315 : ℝ)/100)^2 / (3 * (n:ℝ)^2) ≤
          ((315 : ℝ)/100)^2 / (3 * 41 ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        nlinarith [hnR]
      have : ((315 : ℝ)/100)^2 / (3 * 41 ^ 2) ≤ (1 : ℝ)/100 := by norm_num
      linarith
    have hden : (n:ℝ)^3 - 2*(n:ℝ)^2 + 5*(n:ℝ) - 4 ≥ (n:ℝ)^3 - 2*(n:ℝ)^2 := by
      nlinarith [hnpos]
    have hden' : (n:ℝ)^3 - 2*(n:ℝ)^2 = (n:ℝ)^2 * ((n:ℝ) - 2) := by ring
    have hmain : ((985 : ℝ)/100) * ((99 : ℝ)/100) * ((n:ℝ) - 2) >
        9 * (n:ℝ) - 12 := by
      nlinarith [hnR]
    have hfacpos : (0 : ℝ) < 1 - ((315 : ℝ)/100)^2 / (3 * (n:ℝ)^2) := by
      linarith [hfac]
    have hdenpos : (0 : ℝ) < (n:ℝ)^3 - 2*(n:ℝ)^2 + 5*(n:ℝ) - 4 := by
      nlinarith [hnR]
    nlinarith [h314, hfac, hden, hden', hmain, hfacpos, hdenpos,
      show (0 : ℝ) ≤ (n:ℝ)^2 by positivity]

theorem cos_sq_bound_of_seven_le (N : ℝ) (hN : (7 : ℝ) ≤ N) :
    cos (π / N) ^ 2 <
      1 - (((314 : ℝ)/100 / N) * (1 - ((315 : ℝ)/100 / N)^2 / 6)) ^ 2 := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 7) hN
  set θ := π / N
  have hθpos : 0 < θ := div_pos pi_pos hNpos
  have hθlt : θ < π / 2 := by
    rw [div_lt_div_iff₀ hNpos (by norm_num : (0 : ℝ)<2)]
    nlinarith [pi_pos, hN]
  have hπlo : (314 : ℝ)/100 < π := by
    have := pi_gt_d2; norm_num at this ⊢; linarith
  have hπhi : π < (315 : ℝ)/100 := by
    have := pi_lt_d2; norm_num at this ⊢; linarith
  have hθle : θ ≤ π / 7 := by
    rw [div_le_div_iff₀ hNpos (by norm_num : (0 : ℝ)<7)]
    nlinarith [pi_pos, hN]
  have hθlt1 : θ < 1 := by
    have h1 : π / 7 < (315 : ℝ)/100 / 7 :=
      div_lt_div_of_pos_right hπhi (by norm_num)
    have h2 : ((315 : ℝ)/100 / 7) < 1 := by norm_num
    exact lt_of_le_of_lt hθle (lt_trans h1 h2)
  have hs0pos : 0 < θ - θ^3/6 := by
    have : θ^2 < 6 := by nlinarith [hθpos, hθlt1]
    nlinarith [hθpos, this]
  have hsin : θ - θ^3/6 < sin θ := sin_gt_sub_cube hθpos
  set s0 := θ - θ^3/6
  set s0lo := ((314 : ℝ)/100 / N) * (1 - ((315 : ℝ)/100 / N)^2 / 6)
  have hcos2 : cos θ ^ 2 < 1 - s0 ^ 2 := by
    have hsq : s0^2 < sin θ ^ 2 :=
      pow_lt_pow_left₀ hsin hs0pos.le (by norm_num)
    have : cos θ ^ 2 = 1 - sin θ ^ 2 := by
      rw [← sin_sq_add_cos_sq θ]; ring
    linarith
  have hfac_s0lo_pos : 0 ≤ 1 - ((315 : ℝ)/100 / N)^2 / 6 := by
    have hle : ((315 : ℝ)/100 / N)^2 / 6 ≤ ((315 : ℝ)/100 / 7)^2 / 6 := by
      have : (315 : ℝ)/100 / N ≤ (315 : ℝ)/100 / 7 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) hN
      nlinarith [this, show (0 : ℝ) ≤ 315/100/N by positivity]
    have : ((315 : ℝ)/100 / 7)^2 / 6 < 1 := by norm_num
    linarith
  have hs0_ge : s0 ≥ s0lo := by
    have hs0θ : s0 = θ * (1 - θ^2/6) := by ring
    have hθlo : (314 : ℝ)/100 / N ≤ θ := by
      change (314 : ℝ)/100 / N ≤ π / N
      exact div_le_div_of_nonneg_right hπlo.le hNpos.le
    have hθhi2 : θ ≤ (315 : ℝ)/100 / N := by
      change π / N ≤ (315 : ℝ)/100 / N
      exact div_le_div_of_nonneg_right hπhi.le hNpos.le
    have hfac : 1 - θ^2/6 ≥ 1 - ((315 : ℝ)/100 / N)^2 / 6 := by
      nlinarith [hθpos, hθhi2]
    have hfacθ : 0 ≤ 1 - θ^2/6 := by
      have : θ^2 ≤ 1 := by nlinarith [hθpos, hθlt1]
      nlinarith
    have ha : (0 : ℝ) ≤ (314 : ℝ)/100 / N := by positivity
    rw [hs0θ]
    calc
      θ * (1 - θ^2/6)
          ≥ ((314 : ℝ)/100 / N) * (1 - θ^2/6) :=
            mul_le_mul_of_nonneg_right hθlo hfacθ
      _ ≥ ((314 : ℝ)/100 / N) * (1 - ((315 : ℝ)/100 / N)^2 / 6) :=
            mul_le_mul_of_nonneg_left hfac ha
  have hpos_lo : 0 ≤ s0lo := by positivity
  have hs0sq : s0 ^ 2 ≥ s0lo ^ 2 :=
    pow_le_pow_left₀ hpos_lo hs0_ge 2
  linarith [hcos2, hs0sq]

theorem one_sub_cosineThreshold (d : ℕ) (hd : 2 ≤ d) :
    1 - cosineThreshold d =
      (9 * ((d : ℝ) + 1) - 12) /
        (((d : ℝ) + 1) ^ 3 - 2 * ((d : ℝ) + 1) ^ 2 +
          5 * ((d : ℝ) + 1) - 4) := by
  set N := (d : ℝ) + 1
  have hd1 : (d : ℝ) - 1 = N - 2 := by ring
  have hden0 : (N - 2) * (N ^ 2 + 2) + 3 * N ≠ 0 := by
    have : 0 < N - 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    positivity
  have hthr : cosineThreshold d =
      (N - 2) * (N ^ 2 - 4) / ((N - 2) * (N ^ 2 + 2) + 3 * N) := by
    unfold cosineThreshold; rw [hd1]
  rw [hthr]
  have hD : (N - 2) * (N ^ 2 + 2) + 3 * N =
      N ^ 3 - 2 * N ^ 2 + 5 * N - 4 := by ring
  rw [hD]
  have hden : N ^ 3 - 2 * N ^ 2 + 5 * N - 4 ≠ 0 := by
    rw [← hD]; exact hden0
  rw [one_sub_div hden]
  congr 1
  ring

set_option maxHeartbeats 800000 in
-- The polynomial normalization in this proof exceeds the default heartbeat budget.
theorem one_lt_coherenceSq_of_six_le (d : ℕ) (hd : 6 ≤ d) : 1 < coherenceSq d := by
  have hd2 : 2 ≤ d := by omega
  set N := (d : ℝ) + 1
  have hNnat : 7 ≤ d + 1 := by omega
  have hN : (7 : ℝ) ≤ N := by
    have : (6 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hNpos : 0 < N := by positivity
  have hcos_ub := cos_sq_bound_of_seven_le N hN
  set s0lo := ((314 : ℝ)/100 / N) * (1 - ((315 : ℝ)/100 / N)^2 / 6)
  have hcos_lt : cos (π / N) ^ 2 < 1 - s0lo ^ 2 := by
    simpa [s0lo] using hcos_ub
  have hweak :
      s0lo ^ 2 ≥
        ((314 : ℝ)/100)^2 / N ^ 2 *
          (1 - ((315 : ℝ)/100)^2 / (3 * N ^ 2)) := by
    have hleft : s0lo ^ 2 =
        ((314 : ℝ)/100)^2 / N ^ 2 *
          (1 - ((315 : ℝ)/100 / N)^2 / 6) ^ 2 := by
      change
          (((314 : ℝ)/100 / N) * (1 - ((315 : ℝ)/100 / N)^2 / 6)) ^ 2 =
            ((314 : ℝ)/100)^2 / N ^ 2 *
              (1 - ((315 : ℝ)/100 / N)^2 / 6) ^ 2
      rw [mul_pow, div_pow]
    have hsq : (1 - ((315 : ℝ)/100 / N)^2 / 6) ^ 2 ≥
        1 - 2 * (((315 : ℝ)/100 / N)^2 / 6) := by
      nlinarith [sq_nonneg (((315 : ℝ)/100 / N)^2 / 6)]
    have h2u : 2 * (((315 : ℝ)/100 / N)^2 / 6) =
        ((315 : ℝ)/100)^2 / (3 * N ^ 2) := by
      field_simp [hNpos.ne']; ring
    rw [hleft]
    nlinarith [hsq, show (0 : ℝ) ≤ ((314 : ℝ)/100)^2 / N^2 by positivity, h2u]
  have h1mthr := one_sub_cosineThreshold d hd2
  have hden_pos : 0 < N ^ 3 - 2 * N ^ 2 + 5 * N - 4 := by
    nlinarith [hN, hNpos]
  have hkey := key_poly_nat (d + 1) hNnat
  have hkey' :
      ((314 : ℝ)/100)^2 * (1 - ((315 : ℝ)/100)^2 / (3 * N ^ 2)) *
          (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) >
        (9 * N - 12) * N ^ 2 := by
    simpa [N] using hkey
  have hs0_gt : s0lo ^ 2 > 1 - cosineThreshold d := by
    have h1 : 1 - cosineThreshold d =
        (9 * N - 12) / (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) := by
      simpa [N] using h1mthr
    rw [h1, gt_iff_lt]
    have hN2pos : 0 < N ^ 2 := sq_pos_of_pos hNpos
    have hlo :
        ((314 : ℝ)/100)^2 / N ^ 2 *
            (1 - ((315 : ℝ)/100)^2 / (3 * N ^ 2)) *
            (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) >
          9 * N - 12 := by
      have hN2ne : N ^ 2 ≠ 0 := hN2pos.ne'
      have hL :
          ((314 : ℝ)/100)^2 / N ^ 2 *
              (1 - ((315 : ℝ)/100)^2 / (3 * N ^ 2)) *
              (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) =
            (((314 : ℝ)/100)^2 *
                (1 - ((315 : ℝ)/100)^2 / (3 * N ^ 2)) *
                (N ^ 3 - 2 * N ^ 2 + 5 * N - 4)) / N ^ 2 := by
        field_simp [hN2ne]
      rw [hL]
      have hdiv :
          (((314 : ℝ)/100)^2 *
              (1 - ((315 : ℝ)/100)^2 / (3 * N ^ 2)) *
              (N ^ 3 - 2 * N ^ 2 + 5 * N - 4)) / N ^ 2 >
            ((9 * N - 12) * N ^ 2) / N ^ 2 :=
        div_lt_div_of_pos_right hkey' hN2pos
      have hR : ((9 * N - 12) * N ^ 2) / N ^ 2 = 9 * N - 12 := by
        field_simp [hN2ne]
      rwa [hR] at hdiv
    have hmul :
        9 * N - 12 < s0lo ^ 2 * (N ^ 3 - 2 * N ^ 2 + 5 * N - 4) := by
      nlinarith [hweak, hlo, hden_pos]
    exact (div_lt_iff₀ hden_pos).mpr hmul
  have hcos_thr : cos (π / N) ^ 2 < cosineThreshold d := by
    have : 1 - s0lo ^ 2 < cosineThreshold d := by linarith [hs0_gt]
    linarith [hcos_lt]
  have hθlt : π / N < π / 2 := by
    rw [div_lt_div_iff₀ hNpos (by norm_num : (0 : ℝ)<2)]
    nlinarith [pi_pos, hN]
  have hθpos : 0 < π / N := div_pos pi_pos hNpos
  have hcos_pos : 0 < cos (π / N) :=
    cos_pos_of_mem_Ioo ⟨by linarith [pi_pos, hθpos], hθlt⟩
  exact one_lt_coherenceSq_of_cos_lt d hd2
    (by simpa [N] using hcos_pos)
    (by simpa [N] using hcos_thr)

theorem one_lt_coherenceSq (d : ℕ) (hd : 4 ≤ d) : 1 < coherenceSq d := by
  match d with
  | 0 | 1 | 2 | 3 => omega
  | 4 => exact one_lt_coherenceSq_four
  | 5 => exact one_lt_coherenceSq_five
  | n + 6 => exact one_lt_coherenceSq_of_six_le (n + 6) (by omega)

theorem one_lt_coherence (d : ℕ) (hd : 4 ≤ d) : 1 < coherence d := by
  rw [coherence, ← sqrt_one]
  exact sqrt_lt_sqrt (by norm_num) (one_lt_coherenceSq d hd)

theorem gap_pos (d : ℕ) (hd : 4 ≤ d) : 0 < gap d := by
  unfold gap
  linarith [one_lt_coherence d hd]

end Real.FinitePath
