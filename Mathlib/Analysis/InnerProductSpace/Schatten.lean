/-
Copyright (c) 2026 Tjeerd Jan Heeringa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tjeerd Jan Heeringa
-/
module

public import Mathlib.Analysis.InnerProductSpace.Polar
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Schatten operators

This file defines the Schatten operators.

## TODO:
 - generalize from `ℂ` to `𝕜`
 - determine proper junk value for `p=0`
 - expand APIs

-/

open scoped ENNReal NNReal InnerProductSpace ContinuousLinearMap

noncomputable section



namespace ContinuousLinearMap

section Trace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open scoped ComplexConjugate ENNReal

theorem trace_eq_zero {A : E →L[ℂ] E} (hA : 0 ≤ A)
    (hfin : ∑' i, ‖CFC.sqrt A (traceBasis E i)‖ₑ ^ 2 ≠ ∞) : trace A = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [trace_def, traceOfBasis_eq_tsum_enorm_sq hA.of_nonneg, Complex.ofReal_eq_zero,
    ENNReal.toReal_eq_zero_iff, or_iff_left hfin, tsum_eq_zero_iff] at h
  have hS : CFC.sqrt A = 0 := by
    refine ContinuousLinearMap.ext_on
      (Submodule.dense_iff_topologicalClosure_eq_top.mpr (traceBasis E).dense_span) ?_
    rintro _ ⟨i, rfl⟩
    simpa using h i
  rw [← CFC.sqrt_mul_sqrt_self A hA, hS, zero_mul]

end Trace

section

variable (p : ℝ≥0∞) (q : ℝ) {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def eSpNorm' (T : E →L[ℂ] F) : ℝ≥0∞ := (CFC.nnrpow T.abs q.toNNReal).trace ^ (1 / q)

@[simp]
theorem eSpNorm'_apply (T : E →L[ℂ] F) :
    eSpNorm' q T = (CFC.nnrpow T.abs q.toNNReal).trace ^ (1 / q) :=
  rfl

@[simp]
theorem eSpNorm'_zero {q} (hq : 0 < q) : eSpNorm' q (0 : E →L[ℂ] F) = 0 := by
  simp [eSpNorm', hq]

theorem eSpNorm'_one (T : E →L[ℂ] F) : eSpNorm' 1 T = T.abs.trace := by
  simp [CFC.nnrpow_one]

theorem eSpNorm'_abs (T : E →L[ℂ] F) : eSpNorm' q T.abs = eSpNorm' q T := by
  simp

theorem eSpNorm'_eq_zero {q} (hq : 0 < q) (T : E →L[ℂ] F) : eSpNorm' q T = 0 ↔ T = 0 := by
  constructor
  · rintro hT
    have hq' : ¬(q < 0) := by sorry
    have hq'' : q.toNNReal ≠ 0 := by sorry
    simp [hq, hq', trace_eq_zero] at hT
    simp [← CFC.nnrpow_inv_eq 0 T.abs hq'' (le_refl 0) T.isPositive_abs.nonneg] at hT
    exact ContinuousLinearMap.abs_eq_zero.mp hT.symm
  · rintro hT
    simp [eSpNorm', hT, hq]

def eSpNorm (T : E →L[ℂ] F) : ℝ≥0∞ :=
  if p = 0 then 0 else
    if p = ∞ then ‖T‖ₑ else
      eSpNorm' p.toReal T

@[simp]
theorem eSpNorm_apply (T : E →L[ℂ] F) :
    eSpNorm p T = if p = 0 then 0 else
    if p = ∞ then ‖T‖ₑ else
      eSpNorm' p.toReal T :=
  rfl

theorem trace_abs_eq_eSpNorm_one (T : E →L[ℂ] F) : T.abs.trace = eSpNorm 1 T := by
  simp [CFC.nnrpow_one]

theorem eSpNorm_abs (T : E →L[ℂ] F) : eSpNorm p T.abs = eSpNorm p T := by
  sorry

open Topology Filter in
theorem IsCompactOperator.exists_hilbertBasis_hasEigenvector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hTc : IsCompactOperator T) (hTa : IsSelfAdjoint T) :
    ∃ (ι : Type*) (b : HilbertBasis ι ℂ H) (μ : ι → ℝ),
      (∀ i, Module.End.HasEigenvector (T : Module.End ℂ H) (μ i : ℂ) (b i)) ∧
      Filter.Tendsto μ Filter.cofinite (𝓝 0) := by
  sorry

theorem hasEigenvalue.nonneg {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} (hT : 0 ≤ T)
    {b : HilbertBasis ι ℂ H} {μ : ι → ℝ} {i : ι}
    (he : Module.End.HasEigenvector (T : Module.End ℂ H) (μ i : ℂ) (b i)) : 0 ≤ μ i := by
  calc
    0 ≤ RCLike.re ⟪b i, T (b i)⟫_ℂ := (nonneg_iff_isPositive.mp hT).re_inner_nonneg_right (b i)
    _ = RCLike.re ⟪b i, (μ i) • (b i)⟫_ℂ := by
      rw [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff] at he
      simp at he
      rw [he.1]
    _ = RCLike.re (μ i) := by simp [inner_smul_right_eq_smul (b i) (b i) (μ i), b.orthonormal.1]

theorem hasEigenvector.rpow {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {T : H →L[ℂ] H} (hT : 0 ≤ T)
    {b : HilbertBasis ι ℂ H} {μ : ι → ℝ} {i : ι} (hq : 0 < q)
    (he : Module.End.HasEigenvector (T : Module.End ℂ H) (μ i : ℂ) (b i)) :
    Module.End.HasEigenvector ((CFC.nnrpow T q.toNNReal : H →L[ℂ] H) : Module.End ℂ H)
      (((μ i) ^ q : ℝ) : ℂ) (b i) := by sorry

theorem eSpNorm'_eq_tsum [Fact (0 < q)] (T : E →L[ℂ] F)
    {ι : Type*} (b : HilbertBasis ι ℂ E) {μ : ι → ℝ}
    (hb : ∀ i, Module.End.HasEigenvector (T.abs : Module.End ℂ E) (μ i : ℂ) (b i)) :
    eSpNorm' q T = (∑' i, ENNReal.ofReal (μ i) ^ q) ^ (1 / q) := by
  have hT : 0 ≤ (T.abs ^ q.toNNReal) := CFC.nnrpow_nonneg
  have hbq (i : ι) : (T.abs ^ q.toNNReal) (b i) = (((μ i) ^ q : ℝ) : ℂ) • (b i) := by
    simpa using (hasEigenvector.rpow q T.isPositive_abs.nonneg Fact.out (hb i)).apply_eq_smul
  simp only [eSpNorm'_apply, trace, CFC.nnrpow_eq_pow, one_div, traceOfBasis_eq hT _ b]
  simp [traceOfBasis, ENNReal.ofReal_rpow_of_nonneg
    (ContinuousLinearMap.hasEigenvalue.nonneg T.isPositive_abs.nonneg (hb _))
    (Fact.out : 0 < q).le, hbq _,
    b.orthonormal.1 _]

theorem eSpNorm_eq_tsum [Fact (0 < p)] (T : E →L[ℂ] F)
    {ι : Type*} (b : HilbertBasis ι ℂ E) {μ : ι → ℝ}
    (hb : ∀ i, Module.End.HasEigenvector (T.abs : Module.End ℂ E) (μ i : ℂ) (b i)) :
    eSpNorm p T = if p = ∞ then ⨆ i, ENNReal.ofReal (μ i)
      else (∑' i, ENNReal.ofReal (μ i) ^ p.toReal) ^ (1 / p.toReal) := by
  have hp : p ≠ 0 := (Fact.out : 0 < p).ne'
  simp only [eSpNorm_apply, hp, ↓reduceIte]
  by_cases hp : p = ∞
  · simp [hp]
    apply le_antisymm
    · -- define `opENorm_le_bound'` mirroring `opNorm_le_bound'` to get rid of the cases below.
      apply ContinuousLinearMap.opENorm_le_bound T
      intro e
      by_cases he : ‖e‖ₑ = 0
      · rw [enorm_eq_zero] at he
        simp [he]
      · -- use theorem to go to `⊢ ‖T e‖ₑ ^ 2 ≤ (⨆ i, ENNReal.ofReal (μ i)) ^ 2 * ‖e‖ₑ ^ 2`
        -- use calc to show
        --   ‖T e‖ₑ ^ 2 = ⟪T e, T e⟫
        --   __ = ⟪T.adjoint ∘ T e, e⟫
        --   __ = ∑' i, ⟪(T.adjoint ∘L T) e, b i⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ⟪e, T.abs ^ 2 (b i)⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ⟪e, (μ i) ^ 2 (b i)⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ENNReal.ofReal (μ i) ^ 2 * ⟪e, b i⟫ • ⟪b i, e⟫
        --   __ = ∑' i, ENNReal.ofReal (μ i) ^ 2 * |⟪e, b i⟫| ^ 2
        --   __ ≤ (⨆ i, ENNReal.ofReal (μ i)) ^ 2 * ∑' i, |⟪e, b i⟫| ^ 2
        --   __ = (⨆ i, ENNReal.ofReal (μ i)) ^ 2 * ‖e‖ₑ ^ 2
        sorry
      -- finish by taking the supremum over `this`
    · sorry
      -- take index that attains `⨆ i, ENNReal.ofReal (μ i)`. Call that `j : ι`
      -- use calc to show
      --   (⨆ i, ENNReal.ofReal (μ i)) ^ 2 = ENNReal.ofReal (μ j) ^ 2
      --   _ = ENNReal.ofReal ⟪b j, (μ j) ^ 2 • b j⟫_𝕜
      --   _ = ENNReal.ofReal ⟪b j, T.abs ^ 2 (b j)⟫_𝕜
      --   _ = ENNReal.ofReal ⟪b j, (T.adjoint ∘L T) (b j)⟫_𝕜
      --   _ = ENNReal.ofReal ⟪T (b j), T (b j)⟫_𝕜
      --   _ = ‖T (b j)‖ₑ
      --   _ ≤ ‖T‖ₑ
  · let : Fact (0 < p.toReal) := by sorry
    simp only [hp, ↓reduceIte]
    exact eSpNorm'_eq_tsum p.toReal T b hb

/-- Hölder's inequality for Schatten-class operators -/
theorem eSpNorm_one_comp_le_mul (A : F →L[ℂ] E) (B : E →L[ℂ] F) {q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) :
    eSpNorm 1 (A ∘L B) ≤ eSpNorm p A * eSpNorm q B := sorry

theorem trace_comp_eq_mul_right (A : F →L[ℂ] E) (B : E →L[ℂ] F) :
    (A ∘L B).trace ≤ eSpNorm 1 A * ‖B‖ₑ := by
  sorry

theorem trace_comp_eq_mul_left (A : F →L[ℂ] E) (B : E →L[ℂ] F) :
    (A ∘L B).trace ≤ ‖A‖ₑ * eSpNorm 1 B := by
  sorry

/-- Required for the `q > 1` part whilst matching the `q = 1`, so it was made a separate theorem. -/
private theorem eSpNorm'_one_add_le (A B : E →L[ℂ] F) :
    eSpNorm' 1 (A + B) ≤ eSpNorm' 1 A + eSpNorm' 1 B := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ E
  rw [eSpNorm'_one]
  rw [← polar_adjoint_comp_self_eq_abs (A + B)]
  rw [comp_add (adjoint (A + B).polar) A B]
  grw [trace_add_le, trace_comp_eq_mul_left, trace_comp_eq_mul_left]
  simp_rw [LinearIsometryEquiv.enorm_map adjoint, ← ofReal_norm]
  grw [norm_polar_le_one]
  simp

theorem eSpNorm'_add_le {q} (hq : 1 ≤ q) (A B : E →L[ℂ] F) :
    eSpNorm' q (A + B) ≤ eSpNorm' q A + eSpNorm' q B := by
  rcases hq.eq_or_lt with rfl | hq
  · exact eSpNorm'_one_add_le A B
  obtain ⟨p, hconj⟩ : ∃ p, q.HolderConjugate p := ⟨_, Real.HolderConjugate.conjExponent hq⟩
  set R := A + B with hR
  set D := CFC.nnrpow R.abs (q - 1).toNNReal ∘L R.polar.adjoint with hD
  sorry

theorem eSpNorm_add_le [Fact (1 ≤ p)] (A B : E →L[ℂ] F) :
    eSpNorm p (A + B) ≤ eSpNorm p A + eSpNorm p B := by
  have hp : p ≠ 0 := sorry
  by_cases hp' : p = ∞
  · simp [hp, hp', ESeminormedAddMonoid.enorm_add_le A B]
  have hp'' : 1 ≤ p.toNNReal := by sorry
  simp [hp, hp', eSpNorm, -eSpNorm_apply, -eSpNorm'_apply]
  exact eSpNorm'_add_le hp'' A B

theorem eSpNorm_eq_zero [Fact (0 < p)] (T : E →L[ℂ] F) : eSpNorm p T = 0 ↔ T = 0 := by
  simp [-eSpNorm'_apply]
  refine ⟨fun hT ↦ ?_,  fun hT ↦ ?_⟩
  · have hp : ¬(p=0) := by sorry
    by_cases hp' : p = ∞
    · simp_all
    · have : 0 < p.toReal := by sorry
      simp [hp, hp', this, -eSpNorm'_apply] at hT
      exact (T.eSpNorm'_eq_zero this).mp hT
  · rintro hp
    by_cases hp' : p = ∞
    · simp [hp', hT]
    · have : 0 < p.toReal := by sorry
      simp [hp', hT, this]

def spNorm (T : E →L[ℂ] F) : ℝ := (eSpNorm p T).toReal

def MemSp (T : E →L[ℂ] F) : Prop := eSpNorm p T < ∞

set_option linter.unusedVariables false in
def Sp (p : ℝ≥0∞) (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] : Type _ :=
  E →L[ℂ] F

end

namespace Sp

variable (p : ℝ≥0∞) (q : ℝ) {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

instance : FunLike (Sp p E F) E F := inferInstanceAs (FunLike (E →L[ℂ] F) E F)
instance : ContinuousLinearMapClass (Sp p E F) ℂ E F :=
  inferInstanceAs (ContinuousLinearMapClass (E →L[ℂ] F) ℂ E F)
instance : AddCommGroup (Sp p E F) := inferInstanceAs (AddCommGroup (E →L[ℂ] F))
instance : Module ℂ (Sp p E F) := inferInstanceAs (Module ℂ (E →L[ℂ] F))

def toCLM : (Sp p E F) ≃ₗ[ℂ] (E →L[ℂ] F) := LinearEquiv.refl _ _
def ofCLM : (E →L[ℂ] F) ≃ₗ[ℂ] (Sp p E F) := LinearEquiv.refl _ _

instance : ENorm (Sp p E F) where
  eNorm T := eSpNorm p (toCLM p T)

@[simp]
theorem enorm_def (T : Sp p E F) : ‖T‖ₑ = eSpNorm p (toCLM p T) := rfl

@[simp]
theorem enorm_zero : ‖(0 : Sp p E F)‖ₑ = 0 := by
  simp
  rintro hn0 hnt
  exact ENNReal.toReal_pos hn0 hnt

theorem enorm_add_le [Fact (1 ≤ p)] (T T' : Sp p E F) : ‖T + T'‖ₑ ≤ ‖T‖ₑ + ‖T'‖ₑ :=
  eSpNorm_add_le _ _ _

theorem enorm_eq_zero [Fact (0 < p)] (T : Sp p E F) : ‖T‖ₑ = 0 ↔ T = 0 :=
  eSpNorm_eq_zero _ _

local instance [Fact (1 ≤ p)] : Fact (0 < p) := sorry

instance [Fact (1 ≤ p)] : EMetricSpace (Sp p E F) where
  edist f g := ‖f - g‖ₑ
  edist_self f := by
    rw [sub_self, enorm_zero]
  edist_comm f g:= by
    simp [eSpNorm, eNorm_sub_rev, ← ContinuousLinearMap.abs_neg (toCLM p f - toCLM p g)]
  edist_triangle f g h := by
    simpa using enorm_add_le p (f-g) (g-h)
  eq_of_edist_eq_zero hfg := by
    rw [← sub_eq_zero]
    exact (enorm_eq_zero p _).mp hfg

instance [Fact (1 ≤ p)] : ENormedAddMonoid (Sp p E F) where
  continuous_eNorm := by
    refine continuous_of_le_add_edist 1 ENNReal.one_ne_top fun f g => ?_
    have := enorm_add_le p g (f - g)
    rw [add_sub_cancel g f] at this
    rw [one_mul]
    exact this
  eNorm_zero := enorm_zero p
  eNorm_add_le := enorm_add_le p
  eNorm_eq_zero := enorm_eq_zero p

end Sp

namespace MemSp

end MemSp

end ContinuousLinearMap
