/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum.Extremal
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Combinatorics.SimpleGraph.Path.Operators
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Hermitian operators on a finite path

The transport, position and imaginary commutator are Hermitian; the commutator is nonzero.
-/

@[expose] public section

noncomputable section
namespace LinearMap.SymmetricSpectrum
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The standard Lie bracket multiplied by the imaginary unit. -/
def imaginaryCommutator (T P : H →ₗ[ℂ] H) : H →ₗ[ℂ] H :=
  Complex.I • ⁅T, P⁆

theorem isSymmetric_imaginaryCommutator
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T P : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (hP : P.IsSymmetric) :
    (imaginaryCommutator T P).IsSymmetric := by
  intro x y
  change
    @inner ℂ E _ (Complex.I • (T (P x) - P (T x))) y =
      @inner ℂ E _ x (Complex.I • (T (P y) - P (T y)))
  rw [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  rw [hT (P x) y, hP x (T y), hP (T x) y, hT x (P y)]
  simp only [Complex.conj_I]
  ring

theorem imaginaryCommutator_ne_zero
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T P : E →ₗ[ℂ] E) (hC : ⁅T, P⁆ ≠ 0) :
    imaginaryCommutator T P ≠ 0 := by
  intro hK
  apply hC
  ext v
  have hv := LinearMap.congr_fun hK v
  change Complex.I • (⁅T, P⁆) v = 0 at hv
  exact (smul_eq_zero.mp hv).resolve_left Complex.I_ne_zero

end LinearMap.SymmetricSpectrum
namespace SimpleGraph.pathGraph

open LinearMap.SymmetricSpectrum

/-- The linear map induced by normalized path adjacency. -/
noncomputable def transportLin (d : ℕ) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)
  :=
  Matrix.toEuclideanLin (transport d)

/-- The linear map induced by centered diagonal position. -/
noncomputable def positionLin (d : ℕ) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
  Matrix.toEuclideanLin (position d)

theorem consecutive_comm {d : ℕ} {i j : Fin d} :
    (i.val + 1 = j.val ∨ j.val + 1 = i.val) ↔ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
  constructor <;> rintro (h | h)
  · exact Or.inr h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inl h

theorem isHermitian_transport (d : ℕ) : Matrix.IsHermitian (transport d) := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  have hrho : star (spectralBound d : ℂ) = (spectralBound d : ℂ) := by
    exact Complex.conj_ofReal _
  by_cases h : (i.val + 1 = j.val ∨ j.val + 1 = i.val)
  · have h' : (j.val + 1 = i.val ∨ i.val + 1 = j.val) := consecutive_comm.mp h
    simp only [transport, adjacency_apply, h, h', ite_eq_left]
    rw [one_div, star_inv₀, hrho]
  · have h' : ¬(j.val + 1 = i.val ∨ i.val + 1 = j.val) := by
      intro hji
      exact h (consecutive_comm.mpr hji)
    simp [transport, adjacency_apply, h, h']

theorem isHermitian_position (d : ℕ) : Matrix.IsHermitian (position d) := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [position, positionCoordinate]
  · have hji : j ≠ i := Ne.symm hij
    simp [position, hij, hji]

theorem isSymmetric_transportLin (d : ℕ) : (transportLin d).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (isHermitian_transport d)

theorem isSymmetric_positionLin (d : ℕ) : (positionLin d).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr (isHermitian_position d)

/-- The imaginary commutator of transport and position. -/
noncomputable def commutatorLin (d : ℕ) : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)
  :=
  imaginaryCommutator (transportLin d) (positionLin d)

theorem isSymmetric_commutatorLin (d : ℕ) : (commutatorLin d).IsSymmetric :=
  isSymmetric_imaginaryCommutator (transportLin d) (positionLin d)
    (isSymmetric_transportLin d) (isSymmetric_positionLin d)

/-- A unit eigenvector attaining the largest absolute commutator eigenvalue. -/
noncomputable def extremalVector (d : ℕ) (hd : 1 ≤ d) : EuclideanSpace ℂ (Fin d) := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact maxEigenvalueVector (commutatorLin d) (isSymmetric_commutatorLin d)

theorem norm_extremalVector (d : ℕ) (hd : 1 ≤ d) :
    ‖extremalVector d hd‖ = 1 := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact norm_maxEigenvalueVector (commutatorLin d) (isSymmetric_commutatorLin d)

/-- The fundamental angle of the finite path. -/
noncomputable def fundamentalAngle (d : ℕ) : ℝ :=
  Real.pi / ((d : ℝ) + 1)

/-- The fundamental sine mode with successive powers of minus the imaginary unit. -/
noncomputable def rawFundamentalVector (d : ℕ) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun j : Fin d =>
    (-Complex.I) ^ j.val *
      (Real.sin (((j.val : ℝ) + 1) * fundamentalAngle d) : ℂ)

theorem sin_fundamentalAngle_mul_pos
    (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    0 < Real.sin (((j.val : ℝ) + 1) * fundamentalAngle d) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · unfold fundamentalAngle
    positivity
  · unfold fundamentalAngle
    have hj : (j.val : ℝ) + 1 < (d : ℝ) + 1 := by
      exact_mod_cast Nat.add_lt_add_right j.isLt 1
    have hden : 0 < (d : ℝ) + 1 := by positivity
    calc
      ((j.val : ℝ) + 1) * (Real.pi / ((d : ℝ) + 1)) =
          (((j.val : ℝ) + 1) / ((d : ℝ) + 1)) * Real.pi := by ring
      _ < 1 * Real.pi :=
        mul_lt_mul_of_pos_right ((div_lt_one hden).2 hj) Real.pi_pos
      _ = Real.pi := one_mul _

theorem rawFundamentalVector_apply_ne_zero
    (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    rawFundamentalVector d j ≠ 0 := by
  unfold rawFundamentalVector
  apply mul_ne_zero
  · exact pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)
  · exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (sin_fundamentalAngle_mul_pos d hd j))

theorem rawFundamentalVector_ne_zero
    (d : ℕ) (hd : 1 ≤ d) :
    rawFundamentalVector d ≠ 0 := by
  let j : Fin d := ⟨0, hd⟩
  intro h
  have hj := congrArg (fun v : EuclideanSpace ℂ (Fin d) => v j) h
  exact rawFundamentalVector_apply_ne_zero d hd j hj

/-- The normalized fundamental phase-rotated sine mode. -/
noncomputable def fundamentalVector (d : ℕ) : EuclideanSpace ℂ (Fin d) :=
  ((‖rawFundamentalVector d‖ : ℂ)⁻¹) • rawFundamentalVector d

theorem norm_fundamentalVector
    (d : ℕ) (hd : 1 ≤ d) :
    ‖fundamentalVector d‖ = 1 := by
  rw [fundamentalVector, norm_smul]
  have hn : ‖rawFundamentalVector d‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (rawFundamentalVector_ne_zero d hd)
  simp [hn]

theorem fundamentalVector_apply_ne_zero
    (d : ℕ) (hd : 1 ≤ d) (j : Fin d) :
    fundamentalVector d j ≠ 0 := by
  rw [fundamentalVector]
  change (↑‖rawFundamentalVector d‖ : ℂ)⁻¹ * rawFundamentalVector d j ≠ 0
  apply mul_ne_zero
  · exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (rawFundamentalVector_ne_zero d hd)))
  · exact rawFundamentalVector_apply_ne_zero d hd j

theorem transport_mul_position_apply (d : ℕ) (i j : Fin d) :
    (transport d * position d) i j = transport d i j * (positionCoordinate d j : ℂ) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [position]
  · intro k _ hkj
    simp [position, hkj]
  · simp

theorem position_mul_transport_apply (d : ℕ) (i j : Fin d) :
    (position d * transport d) i j = (positionCoordinate d i : ℂ) * transport d i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · simp [position]
  · intro k _ hki
    simp [position, Ne.symm hki]
  · simp

theorem spectralBound_pos (d : ℕ) (hd : 2 ≤ d) : 0 < spectralBound d := by
  have hden : 0 < (d : ℝ) + 1 := by positivity
  have hden3 : (3 : ℝ) ≤ (d : ℝ) + 1 := by
    exact_mod_cast (show 3 ≤ d + 1 by omega)
  have hfrac : 1 / ((d : ℝ) + 1) < (1 : ℝ) / 2 := by
    rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hangle_pos : 0 < Real.pi / ((d : ℝ) + 1) :=
    div_pos Real.pi_pos hden
  have hangle_lt :
      Real.pi / ((d : ℝ) + 1) < Real.pi / 2 := by
    have hmul := mul_lt_mul_of_pos_left hfrac Real.pi_pos
    simpa [div_eq_mul_inv] using hmul
  have hcos :
      0 < Real.cos (Real.pi / ((d : ℝ) + 1)) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hangle_lt⟩
  unfold spectralBound
  positivity

theorem positionCoordinate_succ_sub
    (d : ℕ) (hd : 2 ≤ d)
    (i j : Fin d) (hij : i.val + 1 = j.val) :
    positionCoordinate d j - positionCoordinate d i = 2 / ((d : ℝ) - 1) := by
  unfold positionCoordinate
  have hdsub : (d : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
    linarith
  have hijr : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hij.symm
  rw [hijr]
  field_simp
  ring

theorem commutator_neighbor_entry_ne_zero
    (d : ℕ) (hd : 2 ≤ d) :
    let i : Fin d := ⟨0, by omega⟩
    let j : Fin d := ⟨1, by omega⟩
    ((transport d * position d) - (position d * transport d)) i j ≠ 0 := by
  dsimp only
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i.val + 1 = j.val := rfl
  have hpaso : (i.val + 1 = j.val ∨ j.val + 1 = i.val) := Or.inl hij
  have hrho : (spectralBound d : ℂ) ≠ 0 := by
    exact_mod_cast (spectralBound_pos d hd).ne'
  have hdelta :
      (positionCoordinate d j : ℂ) - (positionCoordinate d i : ℂ) ≠ 0 := by
    have hdpos : 0 < (2 : ℝ) / ((d : ℝ) - 1) := by
      have : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
      positivity
    exact_mod_cast
      ((positionCoordinate_succ_sub d hd i j hij).trans_ne hdpos.ne')
  rw [Matrix.sub_apply, transport_mul_position_apply, position_mul_transport_apply]
  have hTd : transport d i j = 1 / (spectralBound d : ℂ) := by
    simp only [transport, adjacency_apply, ite_eq_left hpaso]
  rw [hTd]
  intro hz
  have hz0 :
      (spectralBound d : ℂ)⁻¹ * (positionCoordinate d j : ℂ) -
        (positionCoordinate d i : ℂ) * (spectralBound d : ℂ)⁻¹ = 0 := by
    simpa [i, j, one_div] using hz
  have hz' :
      (spectralBound d : ℂ)⁻¹ *
        ((positionCoordinate d j : ℂ) - (positionCoordinate d i : ℂ)) = 0 := by
    calc
      (spectralBound d : ℂ)⁻¹ *
          ((positionCoordinate d j : ℂ) - (positionCoordinate d i : ℂ)) =
        (spectralBound d : ℂ)⁻¹ * (positionCoordinate d j : ℂ) -
          (positionCoordinate d i : ℂ) * (spectralBound d : ℂ)⁻¹ := by ring
      _ = 0 := hz0
  exact hdelta ((mul_eq_zero.mp hz').resolve_left (inv_ne_zero hrho))

theorem matrix_commutator_ne_zero (d : ℕ) (hd : 2 ≤ d) :
    (transport d * position d) - (position d * transport d) ≠ 0 := by
  intro hz
  have hentry := congrFun (congrFun hz ⟨0, by omega⟩) ⟨1, by omega⟩
  exact commutator_neighbor_entry_ne_zero d hd hentry

theorem commutator_transportLin_positionLin (d : ℕ) :
    ⁅transportLin d, positionLin d⁆ =
      Matrix.toEuclideanLin ((transport d * position d) - (position d * transport d)) := by
  simp [Ring.lie_def, transportLin, positionLin, Matrix.toEuclideanLin,
    Matrix.toLpLin_mul_same, Module.End.mul_eq_comp]

theorem commutator_transportLin_positionLin_ne_zero (d : ℕ) (hd : 2 ≤ d) :
    ⁅transportLin d, positionLin d⁆ ≠ 0 := by
  rw [commutator_transportLin_positionLin]
  intro hz
  apply matrix_commutator_ne_zero d hd
  apply Matrix.toEuclideanLin.injective
  simpa using hz

theorem commutatorLin_ne_zero (d : ℕ) (hd : 2 ≤ d) : commutatorLin d ≠ 0 :=
  imaginaryCommutator_ne_zero (transportLin d) (positionLin d)
    (commutator_transportLin_positionLin_ne_zero d hd)

end SimpleGraph.pathGraph
