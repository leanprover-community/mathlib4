/-
Copyright (c) 2026 Jan Bernlöhr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan Bernlöhr
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Basic.ENNReal.Holder

/-!
# Conjugate norm detection on finite products

For conjugate exponents, a finite real or complex vector admits a vector in the conjugate unit
ball whose bilinear pairing with it is its norm. Consequently, bounds on all such pairings detect
the norm. The endpoint pairs `(1, ∞)` and `(∞, 1)` are included.
-/

public section

open scoped ENNReal NNReal ComplexConjugate
open WithLp

namespace PiLp

variable {ι 𝕜 : Type*} [Fintype ι] [RCLike 𝕜]

private lemma norm_phase_le_one (z : 𝕜) : ‖conj z / (‖z‖ : 𝕜)‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  · simp [norm_div, hz]

private lemma mul_phase (z : 𝕜) : z * (conj z / (‖z‖ : 𝕜)) = (‖z‖ : 𝕜) := by
  by_cases hz : z = 0
  · simp [hz]
  · rw [← mul_div_assoc, RCLike.mul_conj, pow_two,
      mul_div_cancel_right₀ _ (RCLike.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]

private lemma exists_norming_vector_of_ne_top {p q : ℝ≥0∞} [p.HolderConjugate q]
    (hp : p ≠ ⊤) (hq : q ≠ ⊤) (a : PiLp p (fun _ : ι ↦ 𝕜)) :
    ∃ b : PiLp q (fun _ : ι ↦ 𝕜), ‖b‖ ≤ 1 ∧ ∑ i, a i * b i = (‖a‖ : 𝕜) := by
  have hpR := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp
  have hqR := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq
  have hpq : p.toReal.HolderConjugate q.toReal :=
    ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  obtain ⟨g, hg, he⟩ := (NNReal.isGreatest_Lp Finset.univ (fun i ↦ ‖a i‖₊) hpq).1
  let b : PiLp q (fun _ : ι ↦ 𝕜) := toLp q fun i ↦
    ((g i : ℝ) : 𝕜) * (conj (a i) / (‖a i‖ : 𝕜))
  have hbn (i : ι) : ‖b i‖ ≤ (g i : ℝ) := by
    change ‖((g i : ℝ) : 𝕜) * (conj (a i) / (‖a i‖ : 𝕜))‖ ≤ _
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_left (norm_phase_le_one (a i)) (norm_nonneg ((g i : ℝ) : 𝕜))
  have hb : ‖b‖ ≤ 1 := by
    rw [norm_eq_sum hqR]
    apply Real.rpow_le_one (Finset.sum_nonneg fun _ _ ↦ by positivity) _ (by positivity)
    calc
      _ ≤ ∑ i, (g i : ℝ) ^ q.toReal := by
        gcongr with i
        exact hbn i
      _ ≤ 1 := by exact_mod_cast hg
  have ha : ‖a‖ = ∑ i, ‖a i‖ * (g i : ℝ) := by
    rw [norm_eq_sum hpR]
    have he' := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) he
    simpa only [NNReal.coe_sum, NNReal.coe_mul, coe_nnnorm, NNReal.coe_rpow] using he'.symm
  refine ⟨b, hb, ?_⟩
  rw [ha, RCLike.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  change a i * (((g i : ℝ) : 𝕜) * (conj (a i) / (‖a i‖ : 𝕜))) = _
  rw [mul_left_comm, mul_phase, RCLike.ofReal_mul]
  ring

/-- A finite vector has a conjugate-unit-ball test whose bilinear pairing is its norm.

This includes the endpoint conjugate pairs `(1, ∞)` and `(∞, 1)`. -/
theorem exists_norming_vector {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (a : PiLp p (fun _ : ι ↦ 𝕜)) :
    ∃ b : PiLp q (fun _ : ι ↦ 𝕜), ‖b‖ ≤ 1 ∧ ∑ i, a i * b i = (‖a‖ : 𝕜) := by
  classical
  by_cases hp : p = ⊤
  · subst p
    have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ q).mp rfl
    subst q
    cases isEmpty_or_nonempty ι with
    | inl h =>
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      exact ⟨0, by simp, by simp⟩
    | inr h =>
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ‖a i‖)
        Finset.univ_nonempty
      have ha : ‖a‖ = ‖a i‖ := by
        rw [← norm_ofLp]
        exact le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
          fun j ↦ hi j (Finset.mem_univ _)) (norm_le_pi_norm _ _)
      refine ⟨single 1 i (conj (a i) / (‖a i‖ : 𝕜)), ?_, ?_⟩
      · simpa using norm_phase_le_one (a i)
      · simp [single_apply, mul_phase, ha]
  by_cases hq : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    refine ⟨toLp ⊤ (fun i ↦ conj (a i) / (‖a i‖ : 𝕜)), ?_, ?_⟩
    · rw [norm_toLp]
      exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦ norm_phase_le_one (a i)
    · simp only [mul_phase, norm_eq_of_L1, RCLike.ofReal_sum]
  exact exists_norming_vector_of_ne_top hp hq a

private lemma norm_sum_mul_le_of_top_left
    (a : PiLp ⊤ (fun _ : ι ↦ 𝕜)) (b : PiLp 1 (fun _ : ι ↦ 𝕜)) :
    ‖∑ i, a i * b i‖ ≤ ‖a‖ * ‖b‖ := by
  calc
    _ ≤ ∑ i, ‖a i * b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖a i‖ * ‖b i‖ := by simp only [norm_mul]
    _ ≤ ∑ i, ‖a‖ * ‖b i‖ := by
      gcongr with i
      exact norm_apply_le a i
    _ = _ := by rw [← Finset.mul_sum, norm_eq_of_L1]

/-- Hölder's inequality for the bilinear pairing on finite real or complex vectors. -/
theorem norm_sum_mul_le {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (a : PiLp p (fun _ : ι ↦ 𝕜)) (b : PiLp q (fun _ : ι ↦ 𝕜)) :
    ‖∑ i, a i * b i‖ ≤ ‖a‖ * ‖b‖ := by
  by_cases hp : p = ⊤
  · subst p
    have hq : q = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ q).mp rfl
    subst q
    exact norm_sum_mul_le_of_top_left a b
  by_cases hq : q = ⊤
  · subst q
    have hp : p = 1 := (ENNReal.HolderConjugate.eq_top_iff_eq_one ⊤ p).mp rfl
    subst p
    simpa only [mul_comm] using norm_sum_mul_le_of_top_left b a
  have hpR := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero p q) hp
  have hqR := ENNReal.toReal_pos (ENNReal.HolderConjugate.ne_zero q p) hq
  calc
    _ ≤ ∑ i, ‖a i * b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖a i‖ * ‖b i‖ := by simp only [norm_mul]
    _ ≤ (∑ i, ‖a i‖ ^ p.toReal) ^ (1 / p.toReal) *
        (∑ i, ‖b i‖ ^ q.toReal) ^ (1 / q.toReal) := by
      simpa using Real.inner_le_Lp_mul_Lq Finset.univ (fun i ↦ ‖a i‖) (fun i ↦ ‖b i‖)
        (ENNReal.HolderConjugate.toReal_of_ne_top hp hq)
    _ = _ := by rw [norm_eq_sum hpR, norm_eq_sum hqR]

/-- Bounds on pairings against the conjugate unit ball detect the norm of a finite vector. -/
theorem norm_le_of_forall_sum_mul_le {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (a : PiLp p (fun _ : ι ↦ 𝕜)) {C : ℝ}
    (h : ∀ b : PiLp q (fun _ : ι ↦ 𝕜), ‖b‖ ≤ 1 → ‖∑ i, a i * b i‖ ≤ C) : ‖a‖ ≤ C := by
  obtain ⟨b, hb, hab⟩ := exists_norming_vector (q := q) a
  simpa only [hab, RCLike.norm_of_nonneg (norm_nonneg a)] using h b hb

/-- The norm of a finite vector is determined by its pairings with the conjugate unit ball. -/
theorem norm_le_iff_forall_sum_mul_le {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (a : PiLp p (fun _ : ι ↦ 𝕜)) {C : ℝ} :
    ‖a‖ ≤ C ↔ ∀ b : PiLp q (fun _ : ι ↦ 𝕜), ‖b‖ ≤ 1 → ‖∑ i, a i * b i‖ ≤ C := by
  refine ⟨?_, norm_le_of_forall_sum_mul_le a⟩
  intro ha b hb
  exact (norm_sum_mul_le a b).trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg a)).trans
    (by simpa using ha))

end PiLp
