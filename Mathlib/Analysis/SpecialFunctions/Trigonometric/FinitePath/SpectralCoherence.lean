/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.CosecantSq
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.Coherence

/-!
# The spectral sum for finite path coherence

The interior cosecant-squared sum gives the closed expression for finite path coherence.
-/

@[expose] public section

noncomputable section
open Real
namespace Real.FinitePath



/-- The weighted interior cosecant sum for finite path coherence. -/
noncomputable def spectralCoherenceSq (d : ℕ) : ℝ :=
  ((d : ℝ) - 1) / ((d : ℝ) + 1) * Real.tan (angle d) ^ 2 *
    (1 + ∑ n ∈ Finset.Icc 2 (d - 1), (Real.sin ((n : ℝ) * angle d))⁻¹ ^ 2)

theorem sum_inv_sin_sq_interior (d : ℕ) (hd : 2 ≤ d) :
    1 + ∑ n ∈ Finset.Icc 2 (d - 1), (Real.sin ((n : ℝ) * angle d))⁻¹ ^ 2 =
      ((((d + 1) : ℝ) ^ 2 + 2) / 3) - 2 / sin (angle d) ^ 2 := by
  set Nval := (d + 1) with hNdef
  have hN : 2 ≤ Nval := by unfold Nval; omega
  have hNeq : (Nval : ℝ) = (d : ℝ) + 1 := by unfold Nval; push_cast; ring
  have ha : angle d = π / (Nval : ℝ) := by
    unfold angle size Nval; push_cast; rfl
  have hfull := Real.sum_inv_sin_sq_pi_div Nval (by omega)
  have hN' : Nval = d + 1 := by unfold Nval; rfl
  -- Reflect the endpoints of the finite sum.
  have hsym0 : (Real.sin (((Nval : ℝ) - 1) * angle d))⁻¹ ^ 2 = (Real.sin (angle d))⁻¹ ^ 2 := by
    have heq : ((Nval : ℝ) - 1) * angle d = π - angle d := by
      rw [ha]
      have hNpos : (Nval : ℝ) ≠ 0 := by exact_mod_cast (show Nval ≠ 0 by omega)
      field_simp [hNpos]
    have hπ : sin (π - angle d) = sin (angle d) := sin_pi_sub (angle d)
    rw [heq, hπ]
  have hsym : (Real.sin ((d : ℝ) * angle d))⁻¹ ^ 2 = (Real.sin (angle d))⁻¹ ^ 2 := by
    have hdval : (d : ℝ) = (Nval : ℝ) - 1 := by rw [hNeq]; ring
    rw [hdval]; exact hsym0
  -- Reflect the endpoints of the finite sum.
  have hfull' :
      ∑ k ∈ Finset.Ico 1 Nval, (Real.sin ((k : ℝ) * angle d))⁻¹ ^ 2 =
        ((Nval : ℝ) ^ 2 - 1) / 3 := by
    rw [← hfull]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hidx : (k : ℝ) * angle d = (k : ℝ) * π / (Nval : ℝ) := by rw [ha]; ring
    rw [hidx]
  -- Remove the two boundary modes.
  have hIco_eq :
      Finset.Ico 1 Nval = insert 1 (insert d (Finset.Icc 2 (d - 1))) := by
    rw [hN']
    ext k
    simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_Icc]
    omega
  have hd_notin : d ∉ Finset.Icc 2 (d - 1) := by
    simp only [Finset.mem_Icc]; omega
  have h1_notin : (1 : ℕ) ∉ insert d (Finset.Icc 2 (d - 1)) := by
    simp only [Finset.mem_insert, Finset.mem_Icc]; omega
  rw [hIco_eq, Finset.sum_insert h1_notin, Finset.sum_insert hd_notin] at hfull'
  simp only [Nat.cast_one, one_mul] at hfull'
  rw [hsym] at hfull'
  have hcsc_eq : (2 : ℝ) / sin (angle d) ^ 2 = 2 * (Real.sin (angle d))⁻¹ ^ 2 := by
    rw [inv_pow]; ring
  rw [hcsc_eq]
  rw [hNeq] at hfull'
  linarith [hfull']

theorem spectralCoherenceSq_eq_coherenceSq (d : ℕ) (hd : 2 ≤ d) :
    spectralCoherenceSq d = coherenceSq d := by
  have hint := sum_inv_sin_sq_interior d hd
  have hapos : 0 < angle d := by unfold angle size; positivity
  have halt : angle d < π / 2 := by
    unfold angle size
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pi_pos, show (2 : ℝ) ≤ d by exact_mod_cast hd]
  have hsin : sin (angle d) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi hapos (by linarith [pi_pos])).ne'
  have hcos : cos (angle d) ≠ 0 :=
    (cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], halt⟩).ne'
  unfold spectralCoherenceSq coherenceSq
  rw [hint, Real.tan_eq_sin_div_cos]
  have hv : ((d + 1) : ℝ) = size d := by
    rfl
  rw [hv]
  unfold size
  field_simp
  ring

end Real.FinitePath
