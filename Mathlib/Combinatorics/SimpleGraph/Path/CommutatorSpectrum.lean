/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Path.Spectrum

/-!
# Spectrum of the path commutator

Phase-rotated sine modes diagonalize the imaginary transport-position commutator.
-/

@[expose] public section

noncomputable section
open scoped ComplexConjugate
namespace SimpleGraph.pathGraph
/-- The imaginary matrix commutator of transport and position. -/
noncomputable def commutatorMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Complex.I • ((transport d * position d) - (position d * transport d))

/-- The phase rotating adjacency modes into commutator modes. -/
noncomputable def phase (j : ℕ) : ℂ := (-Complex.I) ^ j

/-- A sine mode multiplied coordinatewise by the commutator phase. -/
noncomputable def phaseMode (d : ℕ) (k : Fin d) : Fin d → ℂ :=
  fun j => phase j.val * sineMode d k j

theorem commutatorMatrix_apply
    (d : ℕ) (i j : Fin d) :
    commutatorMatrix d i j =
      Complex.I * transport d i j *
        ((positionCoordinate d j : ℂ) - positionCoordinate d i) := by
  rw [commutatorMatrix]
  change Complex.I * (((transport d * position d) - (position d * transport d)) i j) = _
  rw [Matrix.sub_apply,
    transport_mul_position_apply, position_mul_transport_apply]
  ring

theorem phase_neighbor_term
    {d : ℕ} (hd : 2 ≤ d) {i j : Fin d}
    (hpaso : (i.val + 1 = j.val ∨ j.val + 1 = i.val)) (z : ℂ) :
    commutatorMatrix d i j * (phase j.val * z) =
      ((2 / ((d : ℝ) - 1) / spectralBound d : ℝ) : ℂ) *
        (phase i.val * z) := by
  have hrhoR : spectralBound d ≠ 0 := (spectralBound_pos d hd).ne'
  have hrhoC : (spectralBound d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrhoR
  have hdsubR : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  rw [commutatorMatrix_apply]
  have hTd : transport d i j = 1 / (spectralBound d : ℂ) := by
    simp [transport, adjacency_apply, hpaso]
  rw [hTd]
  rcases hpaso with hij | hji
  · have hpos := positionCoordinate_succ_sub d hd i j hij
    have hposC :
        (positionCoordinate d j : ℂ) - positionCoordinate d i =
          ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
      exact_mod_cast hpos
    have hpow : phase j.val = phase i.val * (-Complex.I) := by
      unfold phase
      rw [← hij, pow_succ]
    rw [hpow, hposC]
    push_cast
    field_simp [hrhoR, hdsubR]
    ring_nf
    simp [Complex.I_sq]
  · have hpos := positionCoordinate_succ_sub d hd j i hji
    have hposC :
        (positionCoordinate d j : ℂ) - positionCoordinate d i =
          -((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
      exact_mod_cast (show positionCoordinate d j - positionCoordinate d i =
        -(2 / ((d : ℝ) - 1)) by linarith)
    have hpow : phase i.val = phase j.val * (-Complex.I) := by
      unfold phase
      rw [← hji, pow_succ]
    have hI : phase j.val = phase i.val * Complex.I := by
      calc
        phase j.val = phase j.val * ((-Complex.I) * Complex.I) := by
          rw [show (-Complex.I) * Complex.I = 1 by
            apply Complex.ext <;> norm_num]
          ring
        _ = phase i.val * Complex.I := by rw [hpow]; ring
    rw [hI, hposC]
    push_cast
    field_simp [hrhoR, hdsubR]
    ring_nf
    simp [Complex.I_sq]

theorem commutatorMatrix_mulVec_phaseMode
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    (commutatorMatrix d).mulVec (phaseMode d k) =
      fun i =>
        (((2 / ((d : ℝ) - 1)) *
          (2 * Real.cos (modeAngle d k) / spectralBound d) : ℝ) : ℂ) *
          phaseMode d k i := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  rw [show (∑ j : Fin d, commutatorMatrix d i j * phaseMode d k j) =
      ∑ j : Fin d,
        if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then
          (((2 / ((d : ℝ) - 1) / spectralBound d : ℝ) : ℂ) *
            (phase i.val * sineMode d k j))
        else 0 by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hp : (i.val + 1 = j.val ∨ j.val + 1 = i.val)
      · simp only [hp, ite_eq_left, phaseMode]
        exact phase_neighbor_term hd hp (sineMode d k j)
      · have hz : commutatorMatrix d i j = 0 := by
          rw [commutatorMatrix_apply]
          simp [transport, adjacency_apply, hp]
        simp [hp, hz]]
  rw [show (∑ x : Fin d,
      if (i.val + 1 = x.val ∨ x.val + 1 = i.val) then
        (((2 / ((d : ℝ) - 1) / spectralBound d : ℝ) : ℂ) *
          (phase i.val * sineMode d k x))
      else 0) =
      (((2 / ((d : ℝ) - 1) / spectralBound d : ℝ) : ℂ) * phase i.val) *
        ∑ x : Fin d, if (i.val + 1 = x.val ∨ x.val + 1 = i.val) then sineMode d k x else 0 by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hp : (i.val + 1 = x.val ∨ x.val + 1 = i.val) <;> simp [hp]
    ring]
  rw [show (∑ j : Fin d, if (i.val + 1 = j.val ∨ j.val + 1 = i.val) then sineMode d k j else 0) =
      (adjacency d).mulVec (sineMode d k) i by
        simp only [Matrix.mulVec, dotProduct, adjacency_apply]
        simp_rw [ite_mul, one_mul, zero_mul]]
  rw [congrFun (adjacency_mulVec_sineMode (by omega) k) i]
  simp only [phaseMode]
  push_cast
  ring

/-- The eigenvalue of a phase-rotated sine mode. -/
noncomputable def commutatorEigenvalue (d : ℕ) (k : Fin d) : ℂ :=
  ((((2 / ((d : ℝ) - 1)) / spectralBound d : ℝ) : ℂ) * adjacencyEigenvalue d k)

theorem commutatorMatrix_phaseMode
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Matrix.toLin' (commutatorMatrix d) (phaseMode d k) =
      commutatorEigenvalue d k • phaseMode d k := by
  rw [Matrix.toLin'_apply]
  ext i
  change (commutatorMatrix d).mulVec (phaseMode d k) i =
    commutatorEigenvalue d k * phaseMode d k i
  rw [congrFun (commutatorMatrix_mulVec_phaseMode hd k) i]
  simp only [commutatorEigenvalue, adjacencyEigenvalue]
  push_cast
  ring

theorem phaseMode_ne_zero
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    phaseMode d k ≠ 0 := by
  intro h
  have h0 := congrFun h ⟨0, by omega⟩
  have hs := sineMode_ne_zero (by omega : 1 ≤ d) k
  apply hs
  funext j
  have hf : phase j.val ≠ 0 := by
    exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  have hj := congrFun h j
  simp only [phaseMode] at hj
  exact (mul_eq_zero.mp hj).resolve_left hf

theorem commutatorEigenvalue_injective
    {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (commutatorEigenvalue d) := by
  intro k l hkl
  apply adjacencyEigenvalue_injective
  unfold commutatorEigenvalue at hkl
  have hcR : (2 / ((d : ℝ) - 1)) / spectralBound d ≠ 0 := by
    have hdR : (d : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      linarith
    exact div_ne_zero (div_ne_zero (by norm_num) hdR) (spectralBound_pos d hd).ne'
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hcR) hkl

theorem phaseMode_hasEigenvector
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (Matrix.toLin' (commutatorMatrix d))
      (commutatorEigenvalue d k) (phaseMode d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact commutatorMatrix_phaseMode hd k
  · exact phaseMode_ne_zero hd k

theorem phaseMode_linearIndependent
    {d : ℕ} (hd : 2 ≤ d) :
    LinearIndependent ℂ (phaseMode d) :=
  Module.End.eigenvectors_linearIndependent' (Matrix.toLin' (commutatorMatrix d))
    (commutatorEigenvalue d) (commutatorEigenvalue_injective hd) (phaseMode d)
    (phaseMode_hasEigenvector hd)

/-- The eigenbasis of phase-rotated sine modes. -/
noncomputable def phaseBasis
    {d : ℕ} (hd : 2 ≤ d) : Module.Basis (Fin d) ℂ (Fin d → ℂ) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (phaseMode_linearIndependent hd)

theorem phaseBasis_apply
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    phaseBasis hd k = phaseMode d k := by
  classical
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent
    (phaseMode_linearIndependent hd)) k

theorem commutatorMatrix_mulVec_eq_sum_phaseMode
    {d : ℕ} (hd : 2 ≤ d) (v : Fin d → ℂ) :
    Matrix.toLin' (commutatorMatrix d) v =
      ∑ k : Fin d,
        (phaseBasis hd).repr v k •
          (commutatorEigenvalue d k • phaseMode d k) := by
  calc
    Matrix.toLin' (commutatorMatrix d) v =
        Matrix.toLin' (commutatorMatrix d)
          (∑ k, (phaseBasis hd).repr v k • phaseBasis hd k) := by
            rw [(phaseBasis hd).sum_repr v]
    _ = ∑ k, (phaseBasis hd).repr v k •
          Matrix.toLin' (commutatorMatrix d) (phaseBasis hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [phaseBasis_apply]
      congr 1
      exact commutatorMatrix_phaseMode hd k

theorem phaseBasis_repr_commutatorMatrix
    {d : ℕ} (hd : 2 ≤ d) (v : Fin d → ℂ) (k : Fin d) :
    (phaseBasis hd).repr (Matrix.toLin' (commutatorMatrix d) v) k =
      commutatorEigenvalue d k * (phaseBasis hd).repr v k := by
  rw [commutatorMatrix_mulVec_eq_sum_phaseMode hd v, map_sum]
  classical
  simp [← phaseBasis_apply hd, Finsupp.single_apply, mul_comm]

theorem exists_commutatorMatrix_eigenvalue_eq
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (commutatorMatrix d)) μ) :
    ∃ k : Fin d, μ = commutatorEigenvalue d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (phaseBasis hd).repr v ≠ 0 := by
    simpa using (phaseBasis hd).repr.injective.ne hv.2
  obtain ⟨k, hk⟩ :
      ∃ k : Fin d, (phaseBasis hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hcoord := congrArg (fun w => (phaseBasis hd).repr w k) heig
  rw [phaseBasis_repr_commutatorMatrix] at hcoord
  simp only [map_smul] at hcoord
  exact ⟨k, (mul_right_cancel₀ hk hcoord).symm⟩

theorem norm_commutatorEigenvalue_le
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    ‖commutatorEigenvalue d k‖ ≤ 2 / ((d : ℝ) - 1) := by
  have hδ : 0 ≤ 2 / ((d : ℝ) - 1) := by
    have hdsub : 0 < (d : ℝ) - 1 := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      linarith
    exact div_nonneg (by norm_num) hdsub.le
  have hρ := spectralBound_pos d hd
  rw [commutatorEigenvalue, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hδ hρ.le)]
  calc
    (2 / ((d : ℝ) - 1) / spectralBound d) * ‖adjacencyEigenvalue d k‖ ≤
        (2 / ((d : ℝ) - 1) / spectralBound d) * spectralBound d := by
          gcongr
          exact norm_adjacencyEigenvalue_le_spectralBound hd k
    _ = 2 / ((d : ℝ) - 1) := by
      field_simp [(spectralBound_pos d hd).ne']

theorem commutatorLin_eq_toEuclideanLin (d : ℕ) :
    commutatorLin d = Matrix.toEuclideanLin (commutatorMatrix d) := by
  unfold commutatorLin LinearMap.SymmetricSpectrum.imaginaryCommutator commutatorMatrix
  rw [commutator_transportLin_positionLin]
  exact (Matrix.toEuclideanLin :
    Matrix (Fin d) (Fin d) ℂ ≃ₗ[ℂ] (EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin
      d))).map_smul
      Complex.I ((transport d * position d) - (position d * transport d)) |>.symm

/-- The phase-rotated sine mode viewed in Euclidean space. -/
noncomputable def euclideanPhaseMode (d : ℕ) (k : Fin d) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (phaseMode d k)

theorem commutatorLin_euclideanPhaseMode
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    commutatorLin d (euclideanPhaseMode d k) =
      commutatorEigenvalue d k • euclideanPhaseMode d k := by
  rw [commutatorLin_eq_toEuclideanLin]
  change WithLp.toLp 2 ((commutatorMatrix d).mulVec (phaseMode d k)) =
    WithLp.toLp 2 (fun i => commutatorEigenvalue d k * phaseMode d k i)
  congr 1
  funext i
  simpa [smul_eq_mul] using congrFun (commutatorMatrix_phaseMode hd k) i

theorem euclideanPhaseMode_ne_zero
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    euclideanPhaseMode d k ≠ 0 := by
  exact (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.injective.ne
    (phaseMode_ne_zero hd k)

theorem euclideanPhaseMode_hasEigenvector
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    Module.End.HasEigenvector (commutatorLin d)
      (commutatorEigenvalue d k) (euclideanPhaseMode d k) := by
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    exact commutatorLin_euclideanPhaseMode hd k
  · exact euclideanPhaseMode_ne_zero hd k

theorem euclideanPhaseMode_linearIndependent
    {d : ℕ} (hd : 2 ≤ d) :
    LinearIndependent ℂ (euclideanPhaseMode d) :=
  Module.End.eigenvectors_linearIndependent' (commutatorLin d)
    (commutatorEigenvalue d) (commutatorEigenvalue_injective hd) (euclideanPhaseMode d)
    (euclideanPhaseMode_hasEigenvector hd)

/-- The phase-mode eigenbasis in Euclidean space. -/
noncomputable def euclideanPhaseBasis
    {d : ℕ} (hd : 2 ≤ d) : Module.Basis (Fin d) ℂ (EuclideanSpace ℂ (Fin d)) :=
  (phaseBasis hd).map (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm

theorem euclideanPhaseBasis_apply
    {d : ℕ} (hd : 2 ≤ d) (k : Fin d) :
    euclideanPhaseBasis hd k = euclideanPhaseMode d k := by
  simp [euclideanPhaseBasis, euclideanPhaseMode, phaseBasis_apply]

theorem commutatorLin_eq_sum_euclideanPhaseMode
    {d : ℕ} (hd : 2 ≤ d) (v : EuclideanSpace ℂ (Fin d)) :
    commutatorLin d v =
      ∑ k : Fin d,
        (euclideanPhaseBasis hd).repr v k •
          (commutatorEigenvalue d k • euclideanPhaseMode d k) := by
  calc
    commutatorLin d v =
        commutatorLin d
          (∑ k, (euclideanPhaseBasis hd).repr v k •
            euclideanPhaseBasis hd k) := by
              rw [(euclideanPhaseBasis hd).sum_repr v]
    _ = ∑ k, (euclideanPhaseBasis hd).repr v k •
          commutatorLin d (euclideanPhaseBasis hd k) := by
            simp only [map_sum, map_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      rw [euclideanPhaseBasis_apply]
      congr 1
      exact commutatorLin_euclideanPhaseMode hd k

theorem euclideanPhaseBasis_repr_commutatorLin
    {d : ℕ} (hd : 2 ≤ d) (v : EuclideanSpace ℂ (Fin d)) (k : Fin d) :
    (euclideanPhaseBasis hd).repr (commutatorLin d v) k =
      commutatorEigenvalue d k * (euclideanPhaseBasis hd).repr v k := by
  rw [commutatorLin_eq_sum_euclideanPhaseMode hd v, map_sum]
  classical
  simp [← euclideanPhaseBasis_apply hd, Finsupp.single_apply, mul_comm]

theorem exists_commutatorLin_eigenvalue_eq
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (commutatorLin d) μ) :
    ∃ k : Fin d, μ = commutatorEigenvalue d k := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hrepr : (euclideanPhaseBasis hd).repr v ≠ 0 := by
    simpa using (euclideanPhaseBasis hd).repr.injective.ne hv.2
  obtain ⟨k, hk⟩ :
      ∃ k : Fin d, (euclideanPhaseBasis hd).repr v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hrepr
    apply Finsupp.ext
    intro k
    exact h k
  have heig := Module.End.mem_eigenspace_iff.mp hv.1
  have hcoord := congrArg (fun w => (euclideanPhaseBasis hd).repr w k) heig
  rw [euclideanPhaseBasis_repr_commutatorLin] at hcoord
  simp only [map_smul] at hcoord
  exact ⟨k, (mul_right_cancel₀ hk hcoord).symm⟩

theorem abs_commutatorLin_eigenvalue_le
    {d : ℕ} (hd : 2 ≤ d) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (commutatorLin d) μ) :
    ‖μ‖ ≤ 2 / ((d : ℝ) - 1) := by
  obtain ⟨k, rfl⟩ := exists_commutatorLin_eigenvalue_eq hd hμ
  exact norm_commutatorEigenvalue_le hd k

theorem commutatorEigenvalue_zero
    (d : ℕ) (hd : 2 ≤ d) :
    commutatorEigenvalue d ⟨0, by omega⟩ =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) := by
  have hρ : spectralBound d ≠ 0 := (spectralBound_pos d hd).ne'
  have hdsub : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  simp only [commutatorEigenvalue, adjacencyEigenvalue, modeAngle,
    Nat.cast_zero, zero_add]
  rw [show (1 : ℝ) * Real.pi / ((d : ℝ) + 1) =
    Real.pi / ((d : ℝ) + 1) by ring]
  rw [show (2 * Real.cos (Real.pi / ((d : ℝ) + 1)) : ℝ) = spectralBound d by
    rfl]
  push_cast
  field_simp [hρ, hdsub]

theorem euclideanPhaseMode_zero
    (d : ℕ) (hd : 2 ≤ d) :
    euclideanPhaseMode d ⟨0, by omega⟩ = rawFundamentalVector d := by
  change WithLp.toLp 2 (fun j : Fin d =>
      (-Complex.I) ^ j.val *
        (Real.sin (((j.val : ℝ) + 1) *
          ((((⟨0, by omega⟩ : Fin d).val : ℝ) + 1) * Real.pi /
            ((d : ℝ) + 1))) : ℂ)) =
    WithLp.toLp 2 (fun j : Fin d =>
      (-Complex.I) ^ j.val *
        (Real.sin (((j.val : ℝ) + 1) *
          (Real.pi / ((d : ℝ) + 1))) : ℂ))
  congr 1
  funext j
  congr 3
  norm_num

theorem commutatorLin_rawFundamentalVector
    (d : ℕ) (hd : 2 ≤ d) :
    commutatorLin d (rawFundamentalVector d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • rawFundamentalVector d := by
  rw [← euclideanPhaseMode_zero d hd,
    commutatorLin_euclideanPhaseMode hd, commutatorEigenvalue_zero d hd]

theorem commutatorLin_fundamentalVector
    (d : ℕ) (hd : 2 ≤ d) :
    commutatorLin d (fundamentalVector d) =
      ((2 / ((d : ℝ) - 1) : ℝ) : ℂ) • fundamentalVector d := by
  rw [fundamentalVector, map_smul, commutatorLin_rawFundamentalVector d hd]
  module

theorem maxEigenvalueNorm_commutatorLin
    (d : ℕ) (hd : 2 ≤ d) :
    let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    let : Nontrivial (EuclideanSpace ℂ (Fin d)) := inferInstance
    LinearMap.SymmetricSpectrum.maxEigenvalueNorm (commutatorLin d) (isSymmetric_commutatorLin d)
      =
      2 / ((d : ℝ) - 1) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  let : Nontrivial (EuclideanSpace ℂ (Fin d)) := inferInstance
  have hdsub : 0 < (d : ℝ) - 1 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  have hδ : 0 ≤ 2 / ((d : ℝ) - 1) := by
    exact div_nonneg (by norm_num) hdsub.le
  apply le_antisymm
  · have heig :=
      (isSymmetric_commutatorLin d).hasEigenvalue_eigenvalues rfl
        (LinearMap.SymmetricSpectrum.maxAbsEigenvalueIndex (commutatorLin d)
          (isSymmetric_commutatorLin d))
    have hb := abs_commutatorLin_eigenvalue_le hd heig
    simpa [LinearMap.SymmetricSpectrum.maxEigenvalueNorm,
      LinearMap.SymmetricSpectrum.maxAbsEigenvalue,
      Complex.norm_real, Real.norm_eq_abs] using hb
  · have hb :=
      LinearMap.SymmetricSpectrum.norm_apply_le_maxEigenvalueNorm_mul
        (commutatorLin d) (isSymmetric_commutatorLin d) (fundamentalVector d)
    rw [commutatorLin_fundamentalVector d hd, norm_smul,
      norm_fundamentalVector d (by omega)] at hb
    have hb' :
        2 / ‖(((d : ℝ) : ℂ) - 1)‖ ≤
          LinearMap.SymmetricSpectrum.maxEigenvalueNorm (commutatorLin d)
            (isSymmetric_commutatorLin d) := by
      simpa [Complex.norm_real, abs_of_nonneg hδ] using hb
    rw [show (((d : ℝ) : ℂ) - 1) = (((d : ℝ) - 1 : ℝ) : ℂ) by
      push_cast
      ring, Complex.norm_real, Real.norm_of_nonneg hdsub.le] at hb'
    exact hb'

/-- The canonical operator norm of the imaginary path commutator. -/
theorem norm_commutatorLin (d : ℕ) (hd : 2 ≤ d) :
    ‖(commutatorLin d).toContinuousLinearMap‖ = 2 / ((d : ℝ) - 1) := by
  let : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [LinearMap.SymmetricSpectrum.norm_toContinuousLinearMap
    (commutatorLin d) (isSymmetric_commutatorLin d)]
  exact maxEigenvalueNorm_commutatorLin d hd

end SimpleGraph.pathGraph
