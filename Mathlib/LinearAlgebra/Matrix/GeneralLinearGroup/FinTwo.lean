/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# The group `GL (Fin 2) R`
-/

open Polynomial

namespace Matrix

section CommRing

variable {R : Type*} [CommRing R] [Nontrivial R] (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/-- A `2 × 2` matrix is *parabolic* if it is non-scalar and its discriminant is 0. -/
def IsParabolic : Prop := m ∉ Set.range (scalar _) ∧ m.disc = 0

section conjugation

variable {m}

-- conjugation lemmas are not flagged `simp` because `g.val⁻¹` is simp-normal form, not
-- `g⁻¹.val`, but `g⁻¹.val` is more convenient in this theory

lemma disc_conj : (g * m * g⁻¹).disc = m.disc := by
  simp only [disc_fin_two, trace_units_conj, det_units_conj]

lemma disc_conj' : (g⁻¹ * m * g).disc = m.disc := by
  simpa using disc_conj g⁻¹

lemma isParabolic_conj_iff : (g * m * g⁻¹).IsParabolic ↔ IsParabolic m := by
  simp_rw [IsParabolic, disc_conj, Set.mem_range, Units.eq_mul_inv_iff_mul_eq,
    scalar_apply, ← smul_eq_diagonal_mul, smul_eq_mul_diagonal, Units.mul_right_inj]

lemma isParabolic_conj'_iff : (g⁻¹ * m * g).IsParabolic ↔ m.IsParabolic := by
  simpa using isParabolic_conj_iff g⁻¹

end conjugation

end CommRing

section Field

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

lemma sub_scalar_sq_eq_disc [NeZero (2 : K)] :
    (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.disc / 4) := by
  simp only [scalar_apply, trace_fin_two, disc_fin_two, trace_fin_two,
    det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field_simp
    ring

variable (m) in
/-- The unique eigenvalue of a parabolic matrix (junk if `m` is not parabolic). -/
def parabolicEigenvalue : K := m.trace / 2

lemma IsParabolic.sub_eigenvalue_sq_eq_zero [NeZero (2 : K)] (hm : m.IsParabolic) :
    (m - scalar _ m.parabolicEigenvalue) ^ 2 = 0 := by
  simp [parabolicEigenvalue, -scalar_apply, sub_scalar_sq_eq_disc, hm.2]

/-- Characterization of parabolic elements: they have the form `a + m` where `a` is scalar and
`m` is nonzero and nilpotent. -/
lemma isParabolic_iff_exists [NeZero (2 : K)] :
    m.IsParabolic ↔ ∃ a n, m = scalar _ a + n ∧ n ≠ 0 ∧ n ^ 2 = 0 := by
  constructor
  · exact fun hm ↦ ⟨_, _, (add_sub_cancel ..).symm, sub_ne_zero.mpr fun h ↦ hm.1 ⟨_, h.symm⟩,
      hm.sub_eigenvalue_sq_eq_zero⟩
  · rintro ⟨a, n, hm, hn0, hnsq⟩
    constructor
    · refine fun ⟨b, hb⟩ ↦ hn0 ?_
      rw [← sub_eq_iff_eq_add'] at hm
      simpa only [← hm, ← hb, ← map_sub, ← map_pow, ← map_zero (scalar (Fin 2)), scalar_inj,
        sq_eq_zero_iff] using hnsq
    · suffices scalar (Fin 2) (m.disc / 4) = 0 by
        rw [← map_zero (scalar (Fin 2)), scalar_inj, div_eq_zero_iff] at this
        have : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using NeZero.ne _
        tauto
      rw [← sub_scalar_sq_eq_disc, hm, trace_add, scalar_apply, trace_diagonal]
      simp [mul_div_cancel_left₀ _ (NeZero.ne (2 : K)),
        (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, hnsq⟩).eq_zero , hnsq]

end Field

section LinearOrderedRing

variable {R : Type*} [CommRing R] [Nontrivial R] [Preorder R]
  (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/-- A `2 × 2` matrix is *hyperbolic* if its discriminant is strictly positive. -/
def IsHyperbolic : Prop := 0 < m.disc

/-- A `2 × 2` matrix is *elliptic* if its  discriminant is strictly negative. -/
def IsElliptic : Prop := m.disc < 0

variable {m}

lemma isHyperbolic_conj_iff : (g * m * g⁻¹).IsHyperbolic ↔ m.IsHyperbolic := by
  simp only [IsHyperbolic, disc_conj]

lemma isHyperbolic_conj'_iff : (g⁻¹ * m * g).IsHyperbolic ↔ m.IsHyperbolic := by
  simpa using isHyperbolic_conj_iff g⁻¹

lemma isElliptic_conj_iff : (g * m * g⁻¹).IsElliptic ↔ m.IsElliptic := by
  simp only [IsElliptic, disc_conj]

lemma isElliptic_conj'_iff : (g⁻¹ * m * g).IsElliptic ↔ m.IsElliptic := by
  simpa using isElliptic_conj_iff g⁻¹

end LinearOrderedRing

namespace GeneralLinearGroup

variable {R K : Type*} [CommRing R] [Field K]

/-- Synonym of `Matrix.IsParabolic`, for dot-notation. -/
abbrev IsParabolic (g : GL (Fin 2) R) : Prop := g.val.IsParabolic

/-- Synonym of `Matrix.IsElliptic`, for dot-notation. -/
abbrev IsElliptic [Preorder R] (g : GL (Fin 2) R) : Prop := g.val.IsElliptic

/-- Synonym of `Matrix.IsHyperbolic`, for dot-notation. -/
abbrev IsHyperbolic [Preorder R] (g : GL (Fin 2) R) : Prop := g.val.IsHyperbolic

/-- Polynomial whose roots are the fixed points of `g` considered as a Möbius transformation.

See `Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff`. -/
noncomputable def fixpointPolynomial (g : GL (Fin 2) R) : R[X] :=
  C (g 1 0) * X ^ 2 + C (g 1 1 - g 0 0) * X - C (g 0 1)

/-- The fixed-point polynomial is identically zero iff `g` is scalar. -/
lemma fixpointPolynomial_eq_zero_iff {g : GL (Fin 2) R} :
    g.fixpointPolynomial = 0 ↔ g.val ∈ Set.range (scalar _) := by
  rw [fixpointPolynomial]
  constructor
  · refine fun hP ↦ ⟨g 0 0, ?_⟩
    have hb : g 0 1 = 0 := by simpa using congr_arg (coeff · 0) hP
    have hc : g 1 0 = 0 := by simpa using congr_arg (coeff · 2) hP
    have hd : g 1 1 = g 0 0 := by simpa [sub_eq_zero] using congr_arg (coeff · 1) hP
    ext i j
    fin_cases i <;>
    fin_cases j <;>
    simp [hb, hc, hd]
  · rintro ⟨a, ha⟩
    simp [← ha]

lemma parabolicEigenvalue_ne_zero {g : GL (Fin 2) K} [NeZero (2 : K)] (hg : IsParabolic g) :
    g.val.parabolicEigenvalue ≠ 0 := by
  have : g.val.trace ^ 2 = 4 * g.val.det := by simpa [sub_eq_zero, disc_fin_two] using hg.2
  rw [parabolicEigenvalue, div_ne_zero_iff, eq_true_intro (two_ne_zero' K), and_true,
    Ne, ← sq_eq_zero_iff, this, show (4 : K) = 2 ^ 2 by norm_num, mul_eq_zero,
    sq_eq_zero_iff, not_or]
  exact ⟨NeZero.ne _, g.det_ne_zero⟩

/-- A non-zero power of a parabolic element is parabolic. -/
lemma IsParabolic.pow {g : GL (Fin 2) K} (hg : IsParabolic g) [CharZero K]
    {n : ℕ} (hn : n ≠ 0) : IsParabolic (g ^ n) := by
  rw [IsParabolic, isParabolic_iff_exists] at hg ⊢
  obtain ⟨a, m, hg, hm0, hmsq⟩ := hg
  refine ⟨a ^ n, (n * a ^ (n - 1)) • m, ?_, ?_, by simp [smul_pow, hmsq]⟩
  · rw [Units.val_pow_eq_pow_val, hg]
    rw [← Nat.one_le_iff_ne_zero] at hn
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn IH =>
      simp only [pow_succ, IH, add_mul, Nat.add_sub_cancel, mul_add, ← map_mul, add_assoc]
      simp only [scalar_apply, ← smul_eq_mul_diagonal, ← MulAction.mul_smul, ← smul_eq_diagonal_mul,
        smul_mul, ← sq, hmsq, smul_zero, add_zero, ← add_smul, Nat.cast_add_one, add_mul, one_mul]
      rw [(by omega : n = n - 1 + 1), pow_succ, (by omega : n - 1 + 1 = n)]
      ring_nf
  · suffices a ≠ 0 by simp [this, hm0, hn]
    refine fun ha ↦ (g ^ 2).det_ne_zero ?_
    rw [ha, map_zero, zero_add] at hg
    rw [← hg] at hmsq
    rw [Units.val_pow_eq_pow_val, hmsq, det_zero ⟨0⟩]

end GeneralLinearGroup

end Matrix
