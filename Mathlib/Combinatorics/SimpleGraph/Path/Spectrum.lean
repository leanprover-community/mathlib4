/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Path.Hermitian

/-!
# The sine eigenbasis of a finite path

Explicit sine modes form an eigenbasis for the adjacency matrix of a finite path.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate

namespace SimpleGraph.pathGraph

theorem sum_cond_succ {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if i.val + 1 = j.val then f j else 0) =
      if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0 := by
  classical
  by_cases h : i.val + 1 < d
  · let s : Fin d := ⟨i.val + 1, h⟩
    have hs (j : Fin d) : i.val + 1 = j.val ↔ s = j := by
      simp only [s]
      exact ⟨fun e => Fin.ext e, fun e => by
        have := congrArg Fin.val e
        simpa [s] using this⟩
    simp_rw [hs]
    simp [h, s]
  · have hs (j : Fin d) : i.val + 1 ≠ j.val := by omega
    simp [h, hs]

theorem sum_cond_pred {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if j.val + 1 = i.val then f j else 0) =
      if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0 := by
  classical
  by_cases h : 0 < i.val
  · let p : Fin d := ⟨i.val - 1, by omega⟩
    have hp (j : Fin d) : j.val + 1 = i.val ↔ p = j := by
      simp only [p]
      constructor
      · intro e
        apply Fin.ext
        change i.val - 1 = j.val
        omega
      · intro e
        have he := congrArg Fin.val e
        change i.val - 1 = j.val at he
        omega
    simp_rw [hp]
    simp [h, p]
  · have hp (j : Fin d) : j.val + 1 ≠ i.val := by omega
    simp [h, hp]

theorem sum_consecutive
    {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (∑ j : Fin d, if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then f j else 0) =
      (if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0) +
      (if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0) := by
  classical
  rw [show (∑ j : Fin d, if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then f j else 0) =
      (∑ j : Fin d, if i.val + 1 = j.val then f j else 0) +
      (∑ j : Fin d, if j.val + 1 = i.val then f j else 0) by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h₁ : i.val + 1 = j.val
    · have h₂ : j.val + 1 ≠ i.val := by omega
      simp [h₁, h₂]
    · by_cases h₂ : j.val + 1 = i.val <;> simp [h₁, h₂]]
  rw [sum_cond_succ, sum_cond_pred]

theorem adjacency_mulVec_apply
    {d : ℕ} (i : Fin d) (f : Fin d → ℂ) :
    (adjacency d).mulVec f i =
      (if h : i.val + 1 < d then f ⟨i.val + 1, h⟩ else 0) +
      (if h : 0 < i.val then f ⟨i.val - 1, by omega⟩ else 0) := by
  classical
  simp only [Matrix.mulVec, dotProduct, adjacency_apply]
  simp_rw [ite_mul, one_mul, zero_mul]
  exact sum_consecutive i f

/-- The angle for a sine mode indexed from zero. -/
noncomputable def modeAngle (d : ℕ) (k : Fin d) : ℝ :=
  ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1)

/-- A sine eigenmode of finite path adjacency. -/
noncomputable def sineMode (d : ℕ) (k : Fin d) : Fin d → ℂ :=
  fun j => (Real.sin (((j.val : ℝ) + 1) * modeAngle d k) : ℂ)

theorem sin_add_recurrence (a : ℝ) (n : ℕ) :
    Real.sin (((n : ℝ) + 2) * a) + Real.sin ((n : ℝ) * a) =
      2 * Real.cos a * Real.sin (((n : ℝ) + 1) * a) := by
  rw [show ((n : ℝ) + 2) * a = ((n : ℝ) + 1) * a + a by ring,
    Real.sin_add,
    show (n : ℝ) * a = ((n : ℝ) + 1) * a - a by ring,
    Real.sin_sub]
  ring

theorem sin_modeAngle_mul_card_add_one
    {d : ℕ} (k : Fin d) :
    Real.sin (((d : ℝ) + 1) * modeAngle d k) = 0 := by
  unfold modeAngle
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  rw [show ((d : ℝ) + 1) *
      (((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1)) =
      (k.val + 1 : ℕ) * Real.pi by
        push_cast
        field_simp]
  exact Real.sin_nat_mul_pi (k.val + 1)

theorem adjacency_mulVec_sineMode
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    (adjacency d).mulVec (sineMode d k) =
      fun i => (2 * Real.cos (modeAngle d k) : ℂ) * sineMode d k i := by
  funext i
  rw [adjacency_mulVec_apply]
  by_cases hs : i.val + 1 < d
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, dite_true, sineMode]
      have hpred : i.val - 1 + 1 = i.val := by omega
      have hsucc : i.val + 1 + 1 = i.val + 2 := by omega
      have hpredR : ((i.val - 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) := by
        exact_mod_cast hpred
      have hsuccR : ((i.val + 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) + 2 := by
        exact_mod_cast hsucc
      rw [hpredR, hsuccR]
      exact_mod_cast sin_add_recurrence (modeAngle d k) i.val
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, dite_true, dite_false, add_zero, sineMode]
      simp only [hi0, Nat.cast_zero, zero_add, Nat.cast_one]
      exact_mod_cast (by
        simpa using sin_add_recurrence (modeAngle d k) 0)
  · have hilast : i.val + 1 = d := by omega
    by_cases hp : 0 < i.val
    · simp only [hs, hp, dite_false, dite_true, zero_add, sineMode]
      have hrec := sin_add_recurrence (modeAngle d k) i.val
      have hzero :
          Real.sin (((i.val : ℝ) + 2) * modeAngle d k) = 0 := by
        rw [show ((i.val : ℝ) + 2) = (d : ℝ) + 1 by
          exact_mod_cast (show i.val + 2 = d + 1 by omega)]
        exact sin_modeAngle_mul_card_add_one k
      rw [hzero, zero_add] at hrec
      have hpred : i.val - 1 + 1 = i.val := by omega
      have hpredR : ((i.val - 1 : ℕ) : ℝ) + 1 = (i.val : ℝ) := by
        exact_mod_cast hpred
      rw [hpredR]
      exact_mod_cast hrec
    · have hd1 : d = 1 := by omega
      subst d
      have hk0 : k = 0 := Subsingleton.elim _ _
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst k
      subst i
      norm_num [sineMode, modeAngle]

/-- The eigenvalue of a sine adjacency mode. -/
noncomputable def adjacencyEigenvalue (d : ℕ) (k : Fin d) : ℂ :=
  (2 * Real.cos (modeAngle d k) : ℝ)

theorem modeAngle_mem_Icc {d : ℕ} (k : Fin d) :
    modeAngle d k ∈ Set.Icc (0 : ℝ) Real.pi := by
  constructor
  · unfold modeAngle
    positivity
  · unfold modeAngle
    have hk : (k.val : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      exact_mod_cast (show k.val + 1 ≤ d + 1 by omega)
    have hd : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) ≤
          ((d : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
            gcongr
      _ = Real.pi := by field_simp

theorem adjacencyEigenvalue_injective {d : ℕ} :
    Function.Injective (adjacencyEigenvalue d) := by
  intro k l hkl
  have hcos :
      Real.cos (modeAngle d k) = Real.cos (modeAngle d l) := by
    apply mul_left_cancel₀ (a := (2 : ℝ)) (by norm_num)
    apply Complex.ofReal_injective
    simpa [adjacencyEigenvalue] using hkl
  have hang : modeAngle d k = modeAngle d l :=
    Real.strictAntiOn_cos.injOn
      (modeAngle_mem_Icc k) (modeAngle_mem_Icc l) hcos
  apply Fin.ext
  unfold modeAngle at hang
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd : (d : ℝ) + 1 ≠ 0 := by positivity
  have : (k.val : ℝ) = (l.val : ℝ) := by
    field_simp at hang
    nlinarith
  exact_mod_cast this

theorem sineMode_ne_zero {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    sineMode d k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, hd⟩
  have ha0 : 0 < modeAngle d k := by
    unfold modeAngle
    positivity
  have hapi : modeAngle d k < Real.pi := by
    unfold modeAngle
    have hk : (k.val : ℝ) + 1 < (d : ℝ) + 1 := by
      exact_mod_cast Nat.add_lt_add_right k.isLt 1
    have hdR : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) <
          ((d : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
            gcongr
      _ = Real.pi := by field_simp
  have hs := (Real.sin_pos_of_pos_of_lt_pi ha0 hapi).ne'
  apply Complex.ofReal_ne_zero.mpr hs
  simpa [sineMode] using h0

theorem sineMode_hasEigenvector
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (Matrix.toLin' (adjacency d))
      (adjacencyEigenvalue d k) (sineMode d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
    ext i
    simpa [adjacencyEigenvalue] using congrFun (adjacency_mulVec_sineMode hd k) i
  · exact sineMode_ne_zero hd k

theorem sineMode_linearIndependent
    {d : ℕ} (hd : 1 ≤ d) :
    LinearIndependent ℂ (sineMode d) :=
  Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (adjacency d))
    (adjacencyEigenvalue d) adjacencyEigenvalue_injective (sineMode d)
    (sineMode_hasEigenvector hd)

/-- The basis consisting of all sine adjacency modes. -/
noncomputable def sineBasis
    {d : ℕ} (hd : 1 ≤ d) : Module.Basis (Fin d) ℂ (Fin d → ℂ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (sineMode_linearIndependent hd)

theorem sineBasis_apply
    {d : ℕ} (hd : 1 ≤ d) (k : Fin d) :
    sineBasis hd k = sineMode d k := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent
    (sineMode_linearIndependent hd)) k

theorem adjacency_mulVec_eq_sum_sineMode
    {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℂ) :
    Matrix.toLin' (adjacency d) v =
      ∑ k : Fin d,
        (sineBasis hd).repr v k •
          (adjacencyEigenvalue d k • sineMode d k) := by
  calc
    Matrix.toLin' (adjacency d) v =
        Matrix.toLin' (adjacency d)
          (∑ k, (sineBasis hd).repr v k • sineBasis hd k) := by
            rw [(sineBasis hd).sum_repr v]
    _ = ∑ k, (sineBasis hd).repr v k •
          Matrix.toLin' (adjacency d) (sineBasis hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [sineBasis_apply]
      congr 1
      rw [Matrix.toLin'_apply]
      ext i
      simpa [adjacencyEigenvalue] using congrFun (adjacency_mulVec_sineMode hd k) i

theorem sineBasis_repr_adjacency
    {d : ℕ} (hd : 1 ≤ d) (v : Fin d → ℂ) (k : Fin d) :
    (sineBasis hd).repr (Matrix.toLin' (adjacency d) v) k =
      adjacencyEigenvalue d k * (sineBasis hd).repr v k := by
  rw [adjacency_mulVec_eq_sum_sineMode hd v, map_sum]
  classical
  simp [← sineBasis_apply hd, Finsupp.single_apply, mul_comm]

theorem exists_adjacencyEigenvalue_eq
    {d : ℕ} (hd : 1 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (adjacency d)) μ) :
    ∃ k : Fin d, μ = adjacencyEigenvalue d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (sineBasis hd).repr v ≠ 0 := by
    simpa using (sineBasis hd).repr.injective.ne hv.2
  have hk : ∃ k : Fin d, (sineBasis hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  obtain ⟨k, hk⟩ := hk
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hc := congrArg (fun w => (sineBasis hd).repr w k) heig
  rw [sineBasis_repr_adjacency] at hc
  simp only [map_smul] at hc
  exact ⟨k, (mul_right_cancel₀ hk hc).symm⟩

theorem fundamentalAngle_le_modeAngle
    {d : ℕ} (k : Fin d) :
    fundamentalAngle d ≤ modeAngle d k := by
  unfold fundamentalAngle modeAngle
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hk : (1 : ℝ) ≤ (k.val : ℝ) + 1 := by
    exact_mod_cast (show 1 ≤ k.val + 1 by omega)
  calc
    Real.pi / ((d : ℝ) + 1) =
        1 * Real.pi / ((d : ℝ) + 1) := by ring
    _ ≤ ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) := by
      gcongr

theorem modeAngle_le_pi_sub_fundamentalAngle
    {d : ℕ} (k : Fin d) :
    modeAngle d k ≤ Real.pi - fundamentalAngle d := by
  unfold fundamentalAngle modeAngle
  have hd : 0 < (d : ℝ) + 1 := by positivity
  have hk : (k.val : ℝ) + 1 ≤ d := by
    exact_mod_cast (show k.val + 1 ≤ d by omega)
  calc
    ((k.val : ℝ) + 1) * Real.pi / ((d : ℝ) + 1) ≤
        (d : ℝ) * Real.pi / ((d : ℝ) + 1) := by
          gcongr
    _ = Real.pi - Real.pi / ((d : ℝ) + 1) := by
      field_simp
      ring

theorem abs_cos_modeAngle_le_cos_fundamentalAngle
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    |Real.cos (modeAngle d k)| ≤ Real.cos (fundamentalAngle d) := by
  apply abs_le.mpr
  constructor
  · rw [← Real.cos_pi_sub]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · exact (modeAngle_mem_Icc k).1
    · have hθ : 0 ≤ fundamentalAngle d := by
        unfold fundamentalAngle
        positivity
      linarith [Real.pi_pos]
    · exact modeAngle_le_pi_sub_fundamentalAngle k
  · apply Real.cos_le_cos_of_nonneg_of_le_pi
    · unfold fundamentalAngle
      positivity
    · exact (modeAngle_mem_Icc k).2
    · exact fundamentalAngle_le_modeAngle k

theorem norm_adjacencyEigenvalue_le_spectralBound
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    ‖adjacencyEigenvalue d k‖ ≤ spectralBound d := by
  rw [adjacencyEigenvalue, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [spectralBound]
  exact mul_le_mul_of_nonneg_left
    (by simpa [fundamentalAngle] using
      abs_cos_modeAngle_le_cos_fundamentalAngle hd k)
    (by norm_num)

end SimpleGraph.pathGraph
