/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.Group.AddChar
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
def IsParabolic : Prop := m ∉ Set.range (scalar _) ∧ m.discr = 0

variable {m}

section conjugation

@[simp] lemma discr_conj : (g.val * m * g.val⁻¹).discr = m.discr := by
  simp only [discr_fin_two, ← Matrix.coe_units_inv, trace_units_conj, det_units_conj]

@[simp] lemma discr_conj' : (g.val⁻¹ * m * g.val).discr = m.discr := by
  simpa using discr_conj g⁻¹

@[deprecated (since := "2025-10-20")] alias disc_conj := discr_conj
@[deprecated (since := "2025-10-20")] alias disc_conj' := discr_conj'

@[simp] lemma isParabolic_conj_iff : (g.val * m * g.val⁻¹).IsParabolic ↔ IsParabolic m := by
  simp_rw [IsParabolic, discr_conj, Set.mem_range, ← Matrix.coe_units_inv,
    Units.eq_mul_inv_iff_mul_eq, scalar_apply, ← smul_eq_diagonal_mul, smul_eq_mul_diagonal,
    Units.mul_right_inj]

@[simp] lemma isParabolic_conj'_iff : (g.val⁻¹ * m * g.val).IsParabolic ↔ m.IsParabolic := by
  simpa using isParabolic_conj_iff g⁻¹

end conjugation

lemma isParabolic_iff_of_upperTriangular [IsReduced R] (hm : m 1 0 = 0) :
    m.IsParabolic ↔ m 0 0 = m 1 1 ∧ m 0 1 ≠ 0 := by
  rw [IsParabolic]
  have aux : m.discr = 0 ↔ m 0 0 = m 1 1 := by
    suffices m.discr = (m 0 0 - m 1 1) ^ 2 by
      rw [this, IsReduced.pow_eq_zero_iff two_ne_zero, sub_eq_zero]
    grind [disc_fin_two, trace_fin_two, det_fin_two]
  have (h : m 0 0 = m 1 1) : m ∈ Set.range (scalar _) ↔ m 0 1 = 0 := by
    constructor
    · rintro ⟨a, rfl⟩
      simp
    · intro h'
      use m 1 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h, h', hm]
  tauto

end CommRing

section Field

variable {K : Type*} [Field K] {m : Matrix (Fin 2) (Fin 2) K}

lemma sub_scalar_sq_eq_discr [NeZero (2 : K)] :
    (m - scalar _ (m.trace / 2)) ^ 2 = scalar _ (m.discr / 4) := by
  simp only [scalar_apply, trace_fin_two, discr_fin_two, trace_fin_two,
    det_fin_two, sq, (by norm_num : (4 : K) = 2 * 2)]
  ext i j
  fin_cases i <;>
  fin_cases j <;>
  · simp [Matrix.mul_apply]
    field

@[deprecated (since := "2025-10-20")] alias sub_scalar_sq_eq_disc := sub_scalar_sq_eq_discr

variable (m) in
/-- The unique eigenvalue of a parabolic matrix (junk if `m` is not parabolic). -/
def parabolicEigenvalue : K := m.trace / 2

lemma IsParabolic.sub_eigenvalue_sq_eq_zero [NeZero (2 : K)] (hm : m.IsParabolic) :
    (m - scalar _ m.parabolicEigenvalue) ^ 2 = 0 := by
  simp [parabolicEigenvalue, -scalar_apply, sub_scalar_sq_eq_discr, hm.2]

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
    · suffices scalar (Fin 2) (m.discr / 4) = 0 by
        rw [← map_zero (scalar (Fin 2)), scalar_inj, div_eq_zero_iff] at this
        have : (4 : K) ≠ 0 := by simpa [show (4 : K) = 2 ^ 2 by norm_num] using NeZero.ne _
        tauto
      rw [← sub_scalar_sq_eq_discr, hm, trace_add, scalar_apply, trace_diagonal]
      simp [mul_div_cancel_left₀ _ (NeZero.ne (2 : K)),
        (Matrix.isNilpotent_trace_of_isNilpotent ⟨2, hnsq⟩).eq_zero , hnsq]

end Field

section LinearOrderedRing

variable {R : Type*} [CommRing R] [Nontrivial R] [Preorder R]
  (m : Matrix (Fin 2) (Fin 2) R) (g : GL (Fin 2) R)

/-- A `2 × 2` matrix is *hyperbolic* if its discriminant is strictly positive. -/
def IsHyperbolic : Prop := 0 < m.discr

/-- A `2 × 2` matrix is *elliptic* if its  discriminant is strictly negative. -/
def IsElliptic : Prop := m.discr < 0

variable {m}

lemma isHyperbolic_conj_iff : (g.val * m * g.val⁻¹).IsHyperbolic ↔ m.IsHyperbolic := by
  simp [IsHyperbolic]

lemma isHyperbolic_conj'_iff : (g.val⁻¹ * m * g.val).IsHyperbolic ↔ m.IsHyperbolic := by
  simpa using isHyperbolic_conj_iff g⁻¹

lemma isElliptic_conj_iff : (g.val * m * g.val⁻¹).IsElliptic ↔ m.IsElliptic := by
  simp [IsElliptic]

lemma isElliptic_conj'_iff : (g.val⁻¹ * m * g.val).IsElliptic ↔ m.IsElliptic := by
  simpa using isElliptic_conj_iff g⁻¹

end LinearOrderedRing

namespace GeneralLinearGroup

section Ring

variable {R : Type*} [Ring R]

/-- The map sending `x` to `[1, x; 0, 1]` (bundled as an `AddChar`). -/
@[simps apply]
def upperRightHom : AddChar R (GL (Fin 2) R) where
  toFun x := ⟨!![1, x; 0, 1], !![1, -x; 0, 1], by simp [one_fin_two], by simp [one_fin_two]⟩
  map_zero_eq_one' := by simp [Units.ext_iff, one_fin_two]
  map_add_eq_mul' a b := by simp [Units.ext_iff, add_comm]

lemma injective_upperRightHom : Function.Injective (upperRightHom (R := R)) := by
  refine (injective_iff_map_eq_zero (upperRightHom (R := R)).toAddMonoidHom).mpr ?_
  simp [Units.ext_iff, one_fin_two]

end Ring

variable {R K : Type*} [CommRing R] [Field K]

/-- Synonym of `Matrix.IsParabolic`, for dot-notation. -/
abbrev IsParabolic (g : GL (Fin 2) R) : Prop := g.val.IsParabolic

@[simp] lemma isParabolic_conj_iff [Nontrivial R] (g h : GL (Fin 2) R) :
    IsParabolic (g * h * g⁻¹) ↔ IsParabolic h := by
  simp [IsParabolic]

@[simp] lemma isParabolic_conj_iff' [Nontrivial R] (g h : GL (Fin 2) R) :
    IsParabolic (g⁻¹ * h * g) ↔ IsParabolic h := by
  simp [IsParabolic]

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
  have : g.val.trace ^ 2 = 4 * g.val.det := by simpa [sub_eq_zero, discr_fin_two] using hg.2
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
      rw [(by cutsat : n = n - 1 + 1), pow_succ, (by cutsat : n - 1 + 1 = n)]
      ring_nf
  · suffices a ≠ 0 by simp [this, hm0, hn]
    refine fun ha ↦ (g ^ 2).det_ne_zero ?_
    rw [ha, map_zero, zero_add] at hg
    rw [← hg] at hmsq
    rw [Units.val_pow_eq_pow_val, hmsq, det_zero ⟨0⟩]

lemma isParabolic_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) :
    g.IsParabolic ↔ g 0 0 = g 1 1 ∧ g 0 1 ≠ 0 :=
  Matrix.isParabolic_iff_of_upperTriangular hg

/-- Specialized version of `isParabolic_iff_of_upperTriangular` intended for use with
discrete subgroups of `GL(2, ℝ)`. -/
lemma isParabolic_iff_of_upperTriangular_of_det [LinearOrder K] [IsStrictOrderedRing K]
    {g : GL (Fin 2) K} (h_det : g.det = 1 ∨ g.det = -1) (hg10 : g 1 0 = 0) :
    g.IsParabolic ↔ (∃ x ≠ 0, g = upperRightHom x) ∨ (∃ x ≠ 0, g = -upperRightHom x) := by
  rw [isParabolic_iff_of_upperTriangular hg10]
  constructor
  · rintro ⟨hg00, hg01⟩
    have : g 1 1 ^ 2 = 1 := by
      have : g.det = g 1 1 ^ 2 := by rw [val_det_apply, det_fin_two, hg10, hg00]; ring
      simp only [Units.ext_iff, Units.val_one, Units.val_neg, this] at h_det
      exact h_det.resolve_right (neg_one_lt_zero.trans_le <| sq_nonneg _).ne'
    apply (sq_eq_one_iff.mp this).imp <;> intro hg11 <;> simp only [Units.ext_iff]
    · refine ⟨g 0 1, hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
    · refine ⟨-g 0 1, neg_eq_zero.not.mpr hg01, ?_⟩
      rw [g.val.eta_fin_two]
      simp_all
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;>
    simpa using hx

end GeneralLinearGroup

end Matrix
