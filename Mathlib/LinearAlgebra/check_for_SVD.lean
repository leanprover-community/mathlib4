lake exe mk_all
/-
Copyright (c) 2025 Levi Githaiga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Levi, GPT 5.1
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Tactic

@[expose] public section

open Matrix
open InnerProductSpace
open scoped ComplexOrder
open scoped ComplexInnerProductSpace

set_option linter.unnecessarySimpa false
set_option maxRecDepth 2000

noncomputable section

variable {m n : ℕ}

/-! ## Instances -/
local instance : Fintype (Fin m) := Fin.fintype _
local instance : Fintype (Fin n) := Fin.fintype _
local instance : DecidableEq (Fin m) := inferInstance
local instance : DecidableEq (Fin n) := inferInstance

namespace Matrix

/-! ## Definitions -/

/-- Left semi-unitary: `Uᴴ * U = I`. (For `U : m×n`.) -/
def IsSemiUnitary (U : Matrix (Fin m) (Fin n) ℂ) : Prop :=
  Uᴴ * U = 1

/-- Real diagonal (square `n×n`): zero off-diagonal, real entries on the diagonal. -/
def IsRealDiag (S : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j : Fin n, i ≠ j → S i j = 0) ∧
  (∀ i : Fin n, ∃ r : ℝ, S i i = Complex.ofReal r)

-- Removed @[simp] to avoid simpVarHead linter error
lemma IsRealDiag.diag_off {S} (hS : IsRealDiag S) {i j : Fin n} (hij : i ≠ j) :
    S i j = 0 := hS.1 i j hij

/-- If `S` is real diagonal then `S` is Hermitian and `Sᴴ = S`. -/
lemma IsRealDiag.isHermitian_conjTranspose_eq
    {S : Matrix (Fin n) (Fin n) ℂ} (hS : IsRealDiag S) :
    IsHermitian S ∧ Sᴴ = S := by
  classical
  have hconj : Sᴴ = S := by
    ext i j
    by_cases h : i = j
    · subst h
      rcases hS.2 i with ⟨r, hr⟩
      simp [Matrix.conjTranspose_apply, hr]
    · have hji : j ≠ i := by intro hji; exact h hji.symm
      simp [Matrix.conjTranspose_apply, hS.diag_off h, hS.diag_off hji]
  exact ⟨by simpa [Matrix.IsHermitian] using hconj, hconj⟩

/-! ## Thin SVD for full column rank matrices -/

theorem exists_thinSVD_of_posDef
    (A : Matrix (Fin m) (Fin n) ℂ) (hpos : (Aᴴ * A).PosDef) :
    ∃ (U : Matrix (Fin m) (Fin n) ℂ)
      (Sigma V : Matrix (Fin n) (Fin n) ℂ),
      IsSemiUnitary U ∧              -- Uᴴ * U = Iₙ
      ((Vᴴ * V = 1) ∧ (V * Vᴴ = 1)) ∧  -- V unitary (two identities)
      IsRealDiag Sigma ∧
      (∀ i : Fin n, 0 < (Sigma i i).re) ∧
      A = U * Sigma * Vᴴ := by
  classical
  -- Hermitian `H := Aᴴ * A`
  have hHherm : IsHermitian (Aᴴ * A) := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  -- Unitary eigenvector matrix for `H`
  let Uunit : Matrix.unitaryGroup (Fin n) ℂ := hHherm.eigenvectorUnitary
  let V : Matrix (Fin n) (Fin n) ℂ := (Uunit : _)
  have hVhV : Vᴴ * V = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have : V ∈ Matrix.unitaryGroup (Fin n) ℂ := Uunit.property
    exact (Matrix.mem_unitaryGroup_iff').1 this
  have hVVh : V * Vᴴ = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have : V ∈ Matrix.unitaryGroup (Fin n) ℂ := Uunit.property
    exact (Matrix.mem_unitaryGroup_iff).1 this
  -- Diagonal of eigenvalues of `H`
  let S : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (fun i => Complex.ofReal (hHherm.eigenvalues i))
  have hSdiag : IsRealDiag S := by
    constructor
    · intro i j hij; simp [S, Matrix.diagonal_apply_ne, hij]
    · intro i; exact ⟨hHherm.eigenvalues i, by simp [S]⟩
  -- Spectral theorem: H = V S Vᴴ
  have hH : Aᴴ * A = V * S * Vᴴ := by
    simpa [S] using hHherm.spectral_theorem
  -- All eigenvalues of H are positive (full column rank)
  have h_eval_pos :
      ∀ i : Fin n, 0 < (Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hpos.1) i :=
    Matrix.PosDef.eigenvalues_pos hpos
  -- σ := √λ  (strictly positive)
  let σ : Fin n → ℝ :=
    fun i => Real.sqrt ((Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hpos.1) i)
  have hσ_pos : ∀ i, 0 < σ i := fun i => Real.sqrt_pos.mpr (h_eval_pos i)
  -- Σ := diag(σ) (complex)
  let Sigma : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => (σ i : ℂ))
  have hSigmadiag : IsRealDiag Sigma := by
    constructor
    · intro i j hij; simp [Sigma, Matrix.diagonal_apply_ne, hij]
    · intro i; exact ⟨σ i, by simp [Sigma]⟩
  -- Σ^2 = S
  have hSigma_sq_S : Sigma * Sigma = S := by
    ext i j
    by_cases hij : i = j
    · subst hij
      have hσsqR :
          σ i * σ i =
          (Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hpos.1) i := by
        simp [σ, Real.mul_self_sqrt, le_of_lt (h_eval_pos i)]
      have hσsqC :
          ((σ i : ℂ)) * (σ i : ℂ)
            = Complex.ofReal ((Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hpos.1) i) := by
        simpa using congrArg Complex.ofReal hσsqR
      simp [Sigma, S, Matrix.diagonal_apply_eq, hσsqC]
    · simp [Sigma, S, hij]
  -- Σ⁻¹ := diag(σ⁻¹)
  let Sigmainv : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((σ i)⁻¹ : ℂ))
  -- Σ * Σ⁻¹ = 1 and Σ⁻¹ * Σ = 1
  have hSigma_mul_Sigmainv : Sigma * Sigmainv = 1 := by
    classical
    ext i j
    by_cases hij : i = j
    · subst hij
      have hzℝ : σ i ≠ 0 := ne_of_gt (hσ_pos i)
      have hzC : ((σ i : ℂ)) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hzℝ)
      have hmul : ((σ i : ℂ)) * ((σ i : ℂ))⁻¹ = (1 : ℂ) := by
        simpa using (mul_inv_cancel₀ (a := (σ i : ℂ)) hzC)
      simp [Sigma, Sigmainv, hmul]
    · simp [Sigma, Sigmainv, hij]
  have hSigmainv_mul_Sigma : Sigmainv * Sigma = 1 := by
    classical
    ext i j
    by_cases hij : i = j
    · subst hij
      have hzℝ : σ i ≠ 0 := ne_of_gt (hσ_pos i)
      have hzC : ((σ i : ℂ)) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hzℝ)
      have hzC' : ((σ i : ℂ)⁻¹) ≠ 0 := inv_ne_zero hzC
      have hmul : ((σ i : ℂ)⁻¹) * (((σ i : ℂ)⁻¹)⁻¹) = (1 : ℂ) := by
        simpa using (mul_inv_cancel₀ (a := (σ i : ℂ)⁻¹) hzC')
      have hmul' : ((σ i : ℂ)⁻¹) * (σ i : ℂ) = (1 : ℂ) := by simpa [inv_inv] using hmul
      simp [Sigma, Sigmainv, hmul']
    · simp [Sigma, Sigmainv, hij]
  -- Σ, Σ⁻¹ are self-adjoint
  have hSigma_star : Sigmaᴴ = Sigma := by
    have := (IsRealDiag.isHermitian_conjTranspose_eq hSigmadiag).2
    simpa [Sigma] using this
  have hSigmainv_star : Sigmainvᴴ = Sigmainv := by
    have hdiag : IsRealDiag Sigmainv := by
      constructor
      · intro i j hij; simp [Sigmainv, Matrix.diagonal_apply_ne, hij]
      · intro i; exact ⟨(σ i)⁻¹, by simp [Sigmainv]⟩
    simpa [Sigmainv] using (IsRealDiag.isHermitian_conjTranspose_eq hdiag).2

  -- Clean identity: Vᴴ (Aᴴ (A V)) = S
  have hVHVS : Vᴴ * (Aᴴ * (A * V)) = S := by
    calc
      Vᴴ * (Aᴴ * (A * V))
          = Vᴴ * ((Aᴴ * A) * V) := by simp [Matrix.mul_assoc]
      _ = (Vᴴ * (Aᴴ * A)) * V := by simp [Matrix.mul_assoc]
      _ = Vᴴ * (V * S * Vᴴ) * V := by simpa [hH, Matrix.mul_assoc]
      _ = (Vᴴ * V) * S * (Vᴴ * V) := by simp [Matrix.mul_assoc]
      _ = 1 * S * 1 := by simpa [hVhV, hVVh]
      _ = S := by simp

  -- Define U := A * V * Σ⁻¹  (m×n)
  let U : Matrix (Fin m) (Fin n) ℂ := A * V * Sigmainv
  -- Prove U is left semi-unitary
  have hUleft : Uᴴ * U = 1 := by
    calc
      Uᴴ * U
          = (Sigmainvᴴ * Vᴴ * Aᴴ) * (A * V * Sigmainv) := by
              simp [U, Matrix.mul_assoc, Matrix.conjTranspose_mul, hSigmainv_star]
      _ = Sigmainv * (Vᴴ * (Aᴴ * A) * V) * Sigmainv := by
              simp [Matrix.mul_assoc, hSigmainv_star]

      _ = Sigmainv * S * Sigmainv := by
        have h' : Vᴴ * (Aᴴ * A) * V = S := by
          simpa [Matrix.mul_assoc] using hVHVS   -- since Aᴴ * (A * V) = (Aᴴ * A) * V
        simpa [h']

      _ = Sigmainv * (Sigma * Sigma) * Sigmainv := by simpa [hSigma_sq_S]
      _ = (Sigmainv * Sigma) * (Sigma * Sigmainv) := by simp [Matrix.mul_assoc]
      _ = 1 := by simpa [hSigmainv_mul_Sigma, hSigma_mul_Sigmainv, Matrix.one_mul]
  -- Strict positivity of Σ diagonal
  have hSigmapos : ∀ i : Fin n, 0 < (Sigma i i).re := by
    intro i; simp [Sigma, Complex.ofReal_re, hσ_pos i]
  -- Final identity: A = U Σ Vᴴ
  have hAeq : A = U * Sigma * Vᴴ := by
    calc
      A = A * (V * Vᴴ) := by rw [hVVh, Matrix.mul_one]
      _ = (A * V) * Vᴴ := by simp [Matrix.mul_assoc]
      _ = ((A * V) * (Sigmainv * Sigma)) * Vᴴ := by
            simp [hSigmainv_mul_Sigma, Matrix.mul_assoc]
      _ = (A * V * Sigmainv) * (Sigma * Vᴴ) := by simp [Matrix.mul_assoc]
      _ = U * Sigma * Vᴴ := by simp [U, Matrix.mul_assoc]
  exact ⟨U, Sigma, V, hUleft, ⟨hVhV, hVVh⟩, hSigmadiag, hSigmapos, hAeq⟩

/-! ## Rectangular real-diagonal helper -/

/-- Rectangular real diagonal `m×n`: all entries are zero except on positions
`(Fin.castLE h j, j)` where the value is a nonnegative real (as a complex). -/
def IsRectRealDiag (Sigma : Matrix (Fin m) (Fin n) ℂ) (h : n ≤ m) : Prop :=
  (∀ (i : Fin m) (j : Fin n), i ≠ Fin.castLE h j → Sigma i j = 0) ∧
  (∀ j : Fin n, ∃ r : ℝ, 0 ≤ r ∧ Sigma (Fin.castLE h j) j = Complex.ofReal r)

-- Removed @[simp] to avoid simpVarHead linter error
lemma IsRectRealDiag.off_diag {Sigma : Matrix (Fin m) (Fin n) ℂ} {h : n ≤ m}
    (hS : IsRectRealDiag (m := m) (n := n) Sigma h)
    {i : Fin m} {j : Fin n} (hij : i ≠ Fin.castLE h j) : Sigma i j = 0 :=
  hS.1 i j hij

lemma IsRectRealDiag.diag_real_nonneg {Sigma : Matrix (Fin m) (Fin n) ℂ} {h : n ≤ m}
    (hS : IsRectRealDiag (m := m) (n := n) Sigma h) (j : Fin n) :
    ∃ r : ℝ, 0 ≤ r ∧ Sigma (Fin.castLE h j) j = Complex.ofReal r :=
  hS.2 j

/-! ### Diagonal helpers for SVD calculations -/

/-- Build a complex diagonal matrix from a real-valued diagonal `σ`. -/
def SigmaOf {n : ℕ} (σ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun i => (σ i : ℂ))

/-- Moore–Penrose-like diagonal pseudoinverse: reciprocal where `σ i > 0`, zero otherwise. -/
def SigmaPinvOf {n : ℕ} (σ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal (fun i => if 0 < σ i then ((σ i : ℂ)⁻¹) else 0)

@[simp] lemma SigmaOf_apply {n : ℕ} (σ : Fin n → ℝ) (i j : Fin n) :
    SigmaOf σ i j = if i = j then (σ i : ℂ) else 0 := by
  by_cases h : i = j
  · subst h; simp [SigmaOf]
  · simp [SigmaOf, Matrix.diagonal_apply_ne, h]

@[simp] lemma SigmaPinvOf_apply {n : ℕ} (σ : Fin n → ℝ) (i j : Fin n) :
    SigmaPinvOf σ i j = if i = j then (if 0 < σ i then ((σ i : ℂ)⁻¹) else 0) else 0 := by
  by_cases h : i = j
  · subst h; simp [SigmaPinvOf]
  · simp [SigmaPinvOf, Matrix.diagonal_apply_ne, h]

lemma Sigma_mul_SigmaPinv_diag {n : ℕ} (σ : Fin n → ℝ) :
    SigmaOf σ * SigmaPinvOf σ
      = diagonal (fun i : Fin n => if 0 < σ i then (1 : ℂ) else 0) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hpos : 0 < σ i
    · have hz : ((σ i : ℂ)) ≠ 0 := by
        exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
      simp [SigmaOf, SigmaPinvOf, hpos, hz]
    · have hσ0 : (if 0 < σ i then ((σ i : ℂ)⁻¹) else 0) = 0 := by simp [hpos]
      simp [SigmaOf, SigmaPinvOf, hpos]
  · simp [SigmaOf, SigmaPinvOf, hij]

lemma SigmaPinv_mul_Sigma_diag {n : ℕ} (σ : Fin n → ℝ) :
    SigmaPinvOf σ * SigmaOf σ
      = diagonal (fun i : Fin n => if 0 < σ i then (1 : ℂ) else 0) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hpos : 0 < σ i
    · have hz : ((σ i : ℂ)) ≠ 0 := by
        exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
      simp [SigmaOf, SigmaPinvOf, hpos, hz]
    · have hσ0 : (if 0 < σ i then ((σ i : ℂ)⁻¹) else 0) = 0 := by simp [hpos]
      simp [SigmaOf, SigmaPinvOf, hpos]
  · simp [SigmaOf, SigmaPinvOf, hij]

lemma SigmaPinv_isRealDiag {n : ℕ} (σ : Fin n → ℝ) :
    IsRealDiag (SigmaPinvOf σ) := by
  classical
  constructor
  · intro i j hij; simp [SigmaPinvOf, Matrix.diagonal_apply_ne, hij]
  · intro i
    by_cases hσ : 0 < σ i
    · refine ⟨(σ i)⁻¹, ?_⟩; simp [SigmaPinvOf, hσ, Complex.ofReal_inv]
    · refine ⟨0, ?_⟩; simp [SigmaPinvOf, hσ]

@[simp] lemma SigmaPinv_conjTranspose {n : ℕ} (σ : Fin n → ℝ) :
    (SigmaPinvOf σ)ᴴ = SigmaPinvOf σ := by
  simpa using (IsRealDiag.isHermitian_conjTranspose_eq (SigmaPinv_isRealDiag (n := n) σ)).2


open scoped Matrix

/-- Pseudoinverse factorization stage for SVD (works for any A : m×n). We produce a unitary V and
nonnegative `σ` such that, writing `S = SigmaOf σ`, we have

`A = (A * V * SigmaPinvOf σ) * S * Vᴴ`.

This avoids any inverse and works even when some `σ i = 0` because `SigmaPinvOf` uses 0 there. -/
theorem exists_pseudoSVD_factorization
    (A : Matrix (Fin m) (Fin n) ℂ) :
    ∃ (σ : Fin n → ℝ) (V : Matrix (Fin n) (Fin n) ℂ),
      ((Vᴴ * V = 1) ∧ (V * Vᴴ = 1)) ∧
      A = (A * V * SigmaPinvOf σ) * (SigmaOf σ) * Vᴴ := by
  classical
  -- Hermitian H := Aᴴ * A (positive semidefinite)
  have hHherm : IsHermitian (Aᴴ * A) := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  -- Unitary eigenvector matrix for H
  let Uunit : Matrix.unitaryGroup (Fin n) ℂ := hHherm.eigenvectorUnitary
  let V : Matrix (Fin n) (Fin n) ℂ := (Uunit : _)
  have hVhV : Vᴴ * V = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have : V ∈ Matrix.unitaryGroup (Fin n) ℂ := Uunit.property
    exact (Matrix.mem_unitaryGroup_iff').1 this
  have hVVh : V * Vᴴ = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have : V ∈ Matrix.unitaryGroup (Fin n) ℂ := Uunit.property
    exact (Matrix.mem_unitaryGroup_iff).1 this
  -- Spectral decomposition: H = V * Sev * Vᴴ with Sev diagonal of eigenvalues (real, nonneg)
  let Sev : Matrix (Fin n) (Fin n) ℂ :=
    diagonal (fun i => Complex.ofReal (hHherm.eigenvalues i))
  have hH_spec : Aᴴ * A = V * Sev * Vᴴ := by
    simpa [Sev] using hHherm.spectral_theorem
  -- Eigenvalues nonnegative
  have h_eval_nonneg : ∀ i : Fin n,
      0 ≤ (Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hHherm) i := by
    have hpsd : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
    intro i; simpa using (Matrix.PosSemidef.eigenvalues_nonneg (n := Fin n) (A := Aᴴ * A) hpsd i)
  -- Singular values σ := √λ (nonnegative)
  let σ : Fin n → ℝ := fun i => Real.sqrt ((Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hHherm) i)
  -- Sσ := Σ = diag(σ)
  let Sσ : Matrix (Fin n) (Fin n) ℂ := SigmaOf σ
  -- Sσ^2 = Sev
  have hSσ_sq_Sev : Sσ * Sσ = Sev := by
    classical
    ext i j
    by_cases hij : i = j
    · subst hij
      have : (σ i) * (σ i) = (hHherm.eigenvalues i) := by
        have := Real.sq_sqrt (h_eval_nonneg i)
        simpa [σ, pow_two] using this
      have : ((σ i : ℂ)) * (σ i : ℂ) = Complex.ofReal ((hHherm.eigenvalues i)) := by
        simpa using congrArg Complex.ofReal this
      simp [Sσ, Sev, SigmaOf, Matrix.diagonal_apply_eq, this]
    · simp [Sσ, Sev, SigmaOf, hij]
  -- Define B := A * V
  let B : Matrix (Fin m) (Fin n) ℂ := A * V
  -- Compute Bᴴ * B = Sev
  have hBHB : Bᴴ * B = Sev := by
    calc
      Bᴴ * B = (Vᴴ * Aᴴ) * (A * V) := by simp [B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Vᴴ * (Aᴴ * A) * V := by simp [Matrix.mul_assoc]
      _ = Vᴴ * (V * Sev * Vᴴ) * V := by simpa [hH_spec]
      _ = (Vᴴ * V) * Sev * (Vᴴ * V) := by simp [Matrix.mul_assoc]
      _ = 1 * Sev * 1 := by simpa [hVhV, hVVh]
      _ = Sev := by simp
  -- Columns with σ j = 0 are zero columns of B
  have hB_col_zero_of_sigma_zero : ∀ j : Fin n, σ j = 0 → (fun i => B i j) = 0 := by
    intro j hσ0
    -- From σ j = 0 and nonnegativity, the eigenvalue equals 0
    have hσsq : σ j * σ j = (hHherm.eigenvalues j) := by
      simpa [σ] using (Real.mul_self_sqrt (h_eval_nonneg j))
    have hLam0 : (hHherm.eigenvalues j) = 0 := by
      have h0 : 0 = (hHherm.eigenvalues j) := by
        simpa [hσ0] using hσsq
      simpa using h0.symm
    have hSev0 : Sev j j = 0 := by simp [Sev, hLam0]
    -- (Bᴴ * B) j j = 0, hence column j is zero by dotProduct_star_self_eq_zero
    have hBB0 : (Bᴴ * B) j j = 0 := by simpa [hBHB] using hSev0
    -- Expand the (j,j) entry of Bᴴ * B as a star-inner product
    classical
    have hsum : (Bᴴ * B) j j = dotProduct (star (fun i => B i j)) (fun i => B i j) := by
      simp [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct]
    have hz : dotProduct (star (fun i => B i j)) (fun i => B i j) = 0 := by
      simpa [hsum] using hBB0
    -- Conclude the column is zero using the iff
    exact (dotProduct_star_self_eq_zero.mp hz)
  -- Define the diagonal projector D = Σ⁺ Σ
  let D : Matrix (Fin n) (Fin n) ℂ := SigmaPinvOf σ * Sσ
  have hD_diag : D = diagonal (fun i : Fin n => if 0 < σ i then (1 : ℂ) else 0) := by
    simpa [Sσ] using SigmaPinv_mul_Sigma_diag (n := n) σ
  -- Show B = B * D (columns with σ=0 are zero, others unchanged)
  have hB_eq_BD : B = B * D := by
    classical
    ext i j
    have hMul : (B * D) i j = B i j * (if 0 < σ j then (1 : ℂ) else 0) := by
      -- Only the j-th term survives due to diagonal D
      simp [D, hD_diag, Matrix.mul_apply, Matrix.diagonal]
    by_cases hpos : 0 < σ j
    · calc
        B i j = B i j * (1 : ℂ) := by simp
        _ = B i j * (if 0 < σ j then (1 : ℂ) else 0) := by simp [hpos]
        _ = (B * D) i j := by simpa [hMul]
    · have hσ_nonneg : 0 ≤ σ j := Real.sqrt_nonneg _
      have hσ0' : σ j = 0 := le_antisymm (le_of_not_gt hpos) hσ_nonneg
      have hcol0 := hB_col_zero_of_sigma_zero j hσ0'
      calc
        B i j = 0 := by simpa using congrArg (fun f => f i) hcol0
        _ = 0 * (if 0 < σ j then (1 : ℂ) else 0) := by simp
        _ = (B * D) i j := by simpa [hMul, hσ0', hpos]
  -- Now conclude factorization A = (A V Σ⁺) Σ Vᴴ
  refine ⟨σ, V, ⟨hVhV, hVVh⟩, ?_⟩
  have hAVcalc : A * V = A * V * (SigmaPinvOf σ * Sσ) := by
    calc
      A * V = B := rfl
      _ = B * D := hB_eq_BD
      _ = A * V * (SigmaPinvOf σ * Sσ) := rfl
  calc
    A = A * (V * Vᴴ) := by rw [hVVh, Matrix.mul_one]
    _ = (A * V) * Vᴴ := by
          -- use associativity (A * V) * Vᴴ = A * (V * Vᴴ)
          simpa using (Matrix.mul_assoc A V Vᴴ).symm
    _ = (A * V * (SigmaPinvOf σ * Sσ)) * Vᴴ := by
          exact congrArg (fun X => X * Vᴴ) hAVcalc
    _ = ((A * V * SigmaPinvOf σ) * Sσ) * Vᴴ := by
          simpa [Matrix.mul_assoc]
    _ = (A * V * SigmaPinvOf σ) * (SigmaOf σ) * Vᴴ := by
          rfl

/-- Uᴴ * U = diagonal indicator for U := A * V * SigmaPinvOf σ -/
theorem UhU_diag_core {A : Matrix (Fin m) (Fin n) ℂ} (σ : Fin n → ℝ)
    (V : Matrix (Fin n) (Fin n) ℂ)
    (hBHB : (A * V)ᴴ * (A * V) = (SigmaOf σ) * (SigmaOf σ)) :
    (A * V * SigmaPinvOf σ)ᴴ * (A * V * SigmaPinvOf σ) =
      diagonal (fun i => if 0 < σ i then (1 : ℂ) else 0) := by
  have hSigmainv_star : (SigmaPinvOf σ)ᴴ = SigmaPinvOf σ := by
    simpa using (SigmaPinv_conjTranspose (n := n) σ)
  -- (A*V*SigmaPinv)ᴴ * (A*V*SigmaPinv) = SigmaPinv * (A*V)ᴴ * (A*V) * SigmaPinv
  calc
    (A * V * SigmaPinvOf σ)ᴴ * (A * V * SigmaPinvOf σ)
        = (SigmaPinvOf σ)ᴴ * (A * V)ᴴ * (A * V) * SigmaPinvOf σ := by
            simp [Matrix.mul_assoc, Matrix.conjTranspose_mul, hSigmainv_star]
    _ = SigmaPinvOf σ * (SigmaOf σ * SigmaOf σ) * SigmaPinvOf σ := by
      simpa [Matrix.mul_assoc] using congrArg (fun X => (SigmaPinvOf σ) * X * (SigmaPinvOf σ)) hBHB
    _ = (SigmaPinvOf σ * SigmaOf σ) * (SigmaOf σ * SigmaPinvOf σ) := by simp [Matrix.mul_assoc]
    _ = diagonal (fun i => if 0 < σ i then (1 : ℂ) else 0) := by
      -- reduce to the product of two identical diagonal idempotents
      have h1 := SigmaPinv_mul_Sigma_diag σ
      have h2 := Sigma_mul_SigmaPinv_diag σ
      -- compute the product entrywise
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.mul_apply, Matrix.diagonal_apply_eq, SigmaOf_apply, SigmaPinvOf_apply]
        by_cases hpos : 0 < σ i
        · have hz : ((σ i : ℂ)) ≠ 0 := by
            exact (Complex.ofReal_ne_zero.mpr (ne_of_gt hpos))
          have hmul1 : ((σ i : ℂ))⁻¹ * ((σ i : ℂ)) = (1 : ℂ) := by
            have h := mul_inv_cancel₀ (a := (σ i : ℂ)) hz
            simpa [mul_comm] using h
          have hmul2 : ((σ i : ℂ)) * ((σ i : ℂ))⁻¹ = (1 : ℂ) := by
            simpa using mul_inv_cancel₀ (a := (σ i : ℂ)) hz
          simp [hpos, hmul1, hmul2]
        · -- σ i ≤ 0 implies the pinv entry is 0, so the product is 0
          simp [hpos]
      · simp [Matrix.mul_apply, hij]


/-! ### Rectangular SVD - extend to full unitary U and rectangular Σ -/



theorem exists_rectSVD (A : Matrix (Fin m) (Fin n) ℂ) {h : n ≤ m} :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (Sigma : Matrix (Fin m) (Fin n) ℂ) (V : Matrix (Fin n) (Fin n) ℂ),
      ((Vᴴ * V = 1) ∧ (V * Vᴴ = 1)) ∧ IsRectRealDiag Sigma (m := m) (n := n) h ∧ A = U * Sigma * Vᴴ := by
  -- Recompute spectral decomposition for Aᴴ * A to get V and σ (like in pseudoSVD)
  have hHherm : IsHermitian (Aᴴ * A) := by
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  let Uunit : Matrix.unitaryGroup (Fin n) ℂ := hHherm.eigenvectorUnitary
  let V : Matrix (Fin n) (Fin n) ℂ := (Uunit : _)
  have hVhV : Vᴴ * V = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have : V ∈ Matrix.unitaryGroup (Fin n) ℂ := Uunit.property
    exact (Matrix.mem_unitaryGroup_iff').1 this
  have hVVh : V * Vᴴ = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    have : V ∈ Matrix.unitaryGroup (Fin n) ℂ := Uunit.property
    exact (Matrix.mem_unitaryGroup_iff).1 this
  let Sev : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => Complex.ofReal (hHherm.eigenvalues i))
  have hH_spec : Aᴴ * A = V * Sev * Vᴴ := by
    simpa [Sev] using hHherm.spectral_theorem
  have h_eval_nonneg : ∀ i : Fin n,
      0 ≤ (Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hHherm) i := by
    have hpsd : (Aᴴ * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
    intro i; simpa using (Matrix.PosSemidef.eigenvalues_nonneg (n := Fin n) (A := Aᴴ * A) hpsd i)
  let σ : Fin n → ℝ := fun i => Real.sqrt ((Matrix.IsHermitian.eigenvalues (A := Aᴴ * A) hHherm) i)
  let Sσ : Matrix (Fin n) (Fin n) ℂ := SigmaOf σ
  have hSσ_sq_Sev : Sσ * Sσ = Sev := by
    classical
    ext i j
    by_cases hij : i = j
    · subst hij
      have : (σ i) * (σ i) = (hHherm.eigenvalues i) := by
        have := Real.sq_sqrt (h_eval_nonneg i)
        simpa [σ, pow_two] using this
      have : ((σ i : ℂ)) * (σ i : ℂ) = Complex.ofReal ((hHherm.eigenvalues i)) := by
        simpa using congrArg Complex.ofReal this
      simp [Sσ, Sev, SigmaOf, Matrix.diagonal_apply_eq, this]
    · simp [Sσ, Sev, SigmaOf, hij]
  let B : Matrix (Fin m) (Fin n) ℂ := A * V
  have hBHB : Bᴴ * B = Sev := by
    calc
      Bᴴ * B = (Vᴴ * Aᴴ) * (A * V) := by simp [B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Vᴴ * (Aᴴ * A) * V := by simp [Matrix.mul_assoc]
      _ = Vᴴ * (V * Sev * Vᴴ) * V := by simpa [hH_spec]
      _ = (Vᴴ * V) * Sev * (Vᴴ * V) := by simp [Matrix.mul_assoc]
      _ = 1 * Sev * 1 := by simpa [hVhV, hVVh]
      _ = Sev := by simp
  -- compute the pseudofactorization A = (A V Σ⁺) Σ Vᴴ as in the thin case
  have hD_diag : (SigmaPinvOf σ * Sσ) = diagonal (fun i : Fin n => if 0 < σ i then (1 : ℂ) else 0) := by
    simpa [Sσ] using SigmaPinv_mul_Sigma_diag (n := n) σ
  have hB_eq_BD : B = B * (SigmaPinvOf σ * Sσ) := by
    classical
    ext i j
    have hMul : (B * (SigmaPinvOf σ * Sσ)) i j = B i j * (if 0 < σ j then (1 : ℂ) else 0) := by
      simp [Matrix.mul_apply, Matrix.diagonal, hD_diag]
    by_cases hpos : 0 < σ j
    · simp [hpos, hMul]
    · have hσ_nonneg : 0 ≤ σ j := Real.sqrt_nonneg _
      have hσ0' : σ j = 0 := le_antisymm (le_of_not_gt hpos) hσ_nonneg
      have hσsq : σ j * σ j = (hHherm.eigenvalues j) := by
        simpa [σ] using Real.mul_self_sqrt (h_eval_nonneg j)
      have hLam0 : (hHherm.eigenvalues j) = 0 := by
        have htmp := hσsq
        simp [hσ0'] at htmp
        exact Eq.symm htmp
      have hSev0 : Sev j j = 0 := by simp [Sev, hLam0]
      have hBB0 : (Bᴴ * B) j j = 0 := by simpa [hBHB] using hSev0
      have hsum : (Bᴴ * B) j j = dotProduct (star (fun i => B i j)) (fun i => B i j) := by
        simp [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct]
      have hz : dotProduct (star (fun i => B i j)) (fun i => B i j) = 0 := by simpa [hsum] using hBB0
      have hcol0 : (fun i => B i j) = 0 := dotProduct_star_self_eq_zero.mp hz
      have hbij : B i j = 0 := congrArg (fun f => f i) hcol0
      simp [hMul, hσ0', hbij]
  have hAVcalc : A * V = A * V * (SigmaPinvOf σ * Sσ) := by
    calc
      A * V = B := rfl
      _ = B * (SigmaPinvOf σ * Sσ) := hB_eq_BD
      _ = A * V * (SigmaPinvOf σ * Sσ) := rfl
  -- thin U (m×n)
  let Uthin : Matrix (Fin m) (Fin n) ℂ := A * V * SigmaPinvOf σ
  -- indicator set of nonzero singular values
  let s : Set (Fin n) := { j | 0 < σ j }
  -- prove orthonormality of the nonzero columns (as functions Fin m → ℂ)
  have hUdiag := UhU_diag_core σ V (hBHB.trans (Eq.symm hSσ_sq_Sev))
  have hUdiag' : Uthinᴴ * Uthin = diagonal (fun i => if 0 < σ i then (1 : ℂ) else 0) := by
    simpa [Uthin] using hUdiag
  -- define family f : Fin m → EuclideanSpace ℂ (Fin m) placing Uthin's columns at positions `Fin.castLE h j`
  let f : Fin m → EuclideanSpace ℂ (Fin m) := fun i =>
    if hmem : ∃ j : Fin n, i = Fin.castLE h j then
      (WithLp.equiv 2 (Fin m → ℂ)).symm (fun k => Uthin k (Classical.choose hmem))
    else (0 : EuclideanSpace ℂ (Fin m))
  -- show `f` is pairwise orthogonal
  have hf_pairwise : Pairwise (fun i j => ⟪f i, f j⟫ = (0 : ℂ)) := by
    intro i j hij
    dsimp [f]
    by_cases hi : ∃ a, i = Fin.castLE h a
    · by_cases hj : ∃ b, j = Fin.castLE h b
      · -- both in image of castLE: reduce to Uthin inner products
        let ai := Classical.choose hi
        let bj := Classical.choose hj
        have hais : i = Fin.castLE h ai := Classical.choose_spec hi
        have hbj : j = Fin.castLE h bj := Classical.choose_spec hj
        have hneq : ai ≠ bj := by
          intro heq; apply hij; simpa [heq, hais, hbj]
        -- both in image: compute inner product of `f i` and `f j` via dotProduct on columns
        have hdot_eq : dotProduct (fun k => Uthin k bj) (star fun k => Uthin k ai) =
            (Uthinᴴ * Uthin) ai bj := by
          classical
          simp [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, mul_comm]
        have hdiag0 : (Uthinᴴ * Uthin) ai bj = 0 := by
          have : (Uthinᴴ * Uthin) ai bj = (diagonal (fun i => if 0 < σ i then (1 : ℂ) else 0) : Matrix _ _ _) ai bj := by
            simpa using congrArg (fun M => M ai bj) hUdiag'
          simp [Matrix.diagonal_apply_ne _ hneq] at this
          exact this
        -- both vectors are nonzero, so compute their inner product
        simp [hais, hbj, EuclideanSpace.inner_eq_star_dotProduct]
        exact hdot_eq.trans hdiag0
      · -- j not in image -> f j = 0
        simp [hj, inner_zero_right]
    · -- i not in image -> f i = 0
      simp [hi, inner_zero_left]
  -- extend the orthonormal subset `f` on the image positions to a full orthonormal basis
  let s_index : Set (Fin m) := { i | ∃ j : Fin n, i = Fin.castLE h j ∧ 0 < σ j }
  -- build orthonormal basis via Gram-Schmidt (index size = finrank of EuclideanSpace)
  have hfinrank : Module.finrank ℂ (EuclideanSpace ℂ (Fin m)) = Fintype.card (Fin m) := by
    simpa [Fintype.card_fin] using (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := m))
  let b := gramSchmidtOrthonormalBasis (𝕜 := ℂ) (h := hfinrank) f
  -- for indices coming from `Fin.castLE h j` with σ j > 0, `b` equals the corresponding column
  have hb_spec' : ∀ j : Fin n, 0 < σ j → b (Fin.castLE h j) = (WithLp.equiv 2 (Fin m → ℂ)).symm (fun k => Uthin k j) := by
    intro j hj
    classical
    have hf_orth : Pairwise (fun i k => ⟪f i, f k⟫ = (0 : ℂ)) := by simpa using hf_pairwise
    -- the jth diagonal entry is 1, so the jth column is nonzero
    have hdiagjj : (Uthinᴴ * Uthin) j j = 1 := by
      have := congrArg (fun M => M j j) hUdiag'
      simpa [Matrix.diagonal_apply_eq, hj] using this
    have hsum : dotProduct (star fun k => Uthin k j) (fun k => Uthin k j) = 1 := by
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct] using hdiagjj
    have hv_ne : (fun k => Uthin k j) ≠ 0 := by
      intro hv
      have hzero : dotProduct (star fun k => Uthin k j) (fun k => Uthin k j) = 0 :=
        dotProduct_star_self_eq_zero.mpr hv
      have : (0 : ℂ) = 1 := by simpa [hzero] using hsum.symm
      exact (one_ne_zero : (1 : ℂ) ≠ 0) this.symm
    -- f(castLE h j) corresponds to that column through the WithLp equivalence, hence is nonzero
    have hfi_ne : f (Fin.castLE h j) ≠ 0 := by
      dsimp [f]
      intro h0
      have hmem : ∃ j₀, Fin.castLE h j = Fin.castLE h j₀ := ⟨j, rfl⟩
      have h_eq : (fun k => Uthin k j) = 0 := by
        have := congrArg (WithLp.equiv 2 (Fin m → ℂ)) h0
        simp at this
        exact this
      exact hv_ne h_eq
    -- Gram–Schmidt formula for b at that index
    have hb_eq :
        b (Fin.castLE h j) = (‖f (Fin.castLE h j)‖⁻¹ : ℂ) • f (Fin.castLE h j) :=
      gramSchmidtOrthonormalBasis_apply_of_orthogonal (𝕜 := ℂ)
        (h := hfinrank) (f := f) hf_orth hfi_ne
    -- compute ‖f (Fin.castLE h j)‖ = 1 from hsum
    have hnorm1 : (‖f (Fin.castLE h j)‖ : ℝ) = 1 := by
      -- Define the EuclideanSpace vector corresponding to the j-th column of Uthin
      let x : EuclideanSpace ℂ (Fin m) :=
        (WithLp.equiv 2 _).symm (fun k => Uthin k j)
      -- `f (Fin.castLE h j)` is definitionally equal to this vector
      have hx_def : f (Fin.castLE h j) = x := by
        dsimp [x, f]
        have hmem : ∃ j₀, Fin.castLE h j = Fin.castLE h j₀ := ⟨j, rfl⟩
        simp only [hmem, dif_pos]
        congr 1
        ext k
        -- identify the chosen index in `hmem` with `j`
        have h_spec : Classical.choose hmem = j := by
          have : Fin.castLE h (Classical.choose hmem) = Fin.castLE h j :=
            (Classical.choose_spec hmem).symm
          exact Fin.castLE_injective h this
        simpa [h_spec]
      -- first show the inner product of x with itself is 1
      have h_inner_x : (⟪x, x⟫ : ℂ) = 1 := by
        -- express ⟪x,x⟫ in terms of a dot product of its coordinates
        have h_eq :
            (⟪x, x⟫ : ℂ) =
            dotProduct (WithLp.equiv 2 (Fin m → ℂ) x)
              (star (WithLp.equiv 2 (Fin m → ℂ) x)) := by
          simpa using
            (EuclideanSpace.inner_eq_star_dotProduct (𝕜 := ℂ) (ι := Fin m) x x)
        -- coordinates of x are exactly the j-th column of Uthin
        have hx_fun : WithLp.equiv 2 (Fin m → ℂ) x = (fun k => Uthin k j) := by
          -- by definition of x and properties of an equivalence
          simpa [x] using
            (Equiv.apply_symm_apply (WithLp.equiv 2 (Fin m → ℂ)) (fun k => Uthin k j))
        -- use hsum and dotProduct_comm to identify the dot product as 1
        have h_dot' :
            dotProduct (WithLp.equiv 2 (Fin m → ℂ) x)
              (star (WithLp.equiv 2 (Fin m → ℂ) x)) = (1 : ℂ) := by
          have h_dot :
              dotProduct (star (fun k => Uthin k j)) (fun k => Uthin k j) = (1 : ℂ) := hsum
          have h_dot_comm :
              dotProduct (fun k => Uthin k j) (star (fun k => Uthin k j)) = (1 : ℂ) := by
            simpa [dotProduct_comm] using h_dot
          simpa [hx_fun] using h_dot_comm
        -- combine the two equalities
        rw [h_eq, h_dot']
      -- translate the inner product equality to a statement about the norm of x
      have hnorm_sqC : ((‖x‖ : ℂ) ^ 2) = (1 : ℂ) := by
        -- inner_self_eq_norm_sq_to_K : ⟪x,x⟫ = (‖x‖ : ℂ)²
        have hnorm_sq := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x
        -- combine with h_inner_x : ⟪x,x⟫ = 1
        calc
          ((‖x‖ : ℂ) ^ 2)
              = ⟪x, x⟫ := by
                  simpa [pow_two] using hnorm_sq.symm
          _ = 1 := h_inner_x
      have hnorm_sqR : ‖x‖ ^ 2 = (1 : ℝ) := by
        -- take norms on both sides and simplify
        have := congrArg (fun z : ℂ => ‖z‖) hnorm_sqC
        -- left: ‖(‖x‖ : ℂ)²‖ = ‖x‖², right: ‖1‖ = 1
        simpa [pow_two] using this
      -- From ‖x‖² = 1 and ‖x‖ ≥ 0, conclude ‖x‖ = 1
      have hx_nonneg : 0 ≤ ‖x‖ := norm_nonneg _
      have hx1 : ‖x‖ = 1 := by
        -- take square roots on both sides of hnorm_sqR
        have := congrArg Real.sqrt hnorm_sqR
        -- sqrt (‖x‖²) = ‖x‖, sqrt 1 = 1
        simpa [pow_two, Real.sqrt_mul_self, hx_nonneg, Real.sqrt_one] using this
      -- finally, rewrite in terms of f
      simpa [hx_def] using hx1
    -- finish: normalization factor is 1
    have : (‖f (Fin.castLE h j)‖⁻¹ : ℂ) = 1 := by simpa [hnorm1]
    calc
      b (Fin.castLE h j)
          = (‖f (Fin.castLE h j)‖⁻¹ : ℂ) • f (Fin.castLE h j) := hb_eq
      _ = f (Fin.castLE h j) := by simp [this]
      _ = (WithLp.equiv 2 (Fin m → ℂ)).symm (fun k => Uthin k j) := by
        dsimp [f]
        have hmem : ∃ j₀, Fin.castLE h j = Fin.castLE h j₀ := ⟨j, rfl⟩
        simp only [hmem, dif_pos]
        congr 1
        ext k
        have h_spec : Classical.choose hmem = j := by
          have : Fin.castLE h (Classical.choose hmem) = Fin.castLE h j := (Classical.choose_spec hmem).symm
          exact Fin.castLE_injective h this
        rw [h_spec]
  -- build unitary U matrix from basis `b` (columns are `b i`)
  let Umat : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => (b j) i
  -- prove Umat is unitary: Umatᴴ * Umat = 1 and Umat * Umatᴴ = 1
  have hUmat_mem : Umat ∈ Matrix.unitaryGroup (Fin m) ℂ := by
    -- change-of-basis matrix between orthonormal bases is unitary
    simpa [Umat] using
      (OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
        (a := EuclideanSpace.basisFun (Fin m) ℂ) (b := b))
  have hUmat_unit_left : Umatᴴ * Umat = 1 := (Matrix.mem_unitaryGroup_iff').1 hUmat_mem
  have hUmat_unit_right : Umat * Umatᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hUmat_mem
  -- define rectangular Sigma with embedded σ on rows `Fin.castLE h j`
  let SigmaRect : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j => if i = Fin.castLE h j then (σ j : ℂ) else 0
  -- SigmaRect is IsRectRealDiag
  have hSigmaRect_diag : IsRectRealDiag (m := m) (n := n) SigmaRect (h := h) := by
    constructor
    · intro i j hij; simp [SigmaRect]; by_cases h' : i = Fin.castLE h j
      · exact (hij h').elim
      · simp [h']
    · intro j; use (σ j); constructor
      · apply Real.sqrt_nonneg
      · simp [SigmaRect]
  -- final equality: A = Umat * SigmaRect * Vᴴ
  have hAeq : A = Umat * SigmaRect * Vᴴ := by
    calc
      A = A * (V * Vᴴ) := by rw [hVVh, Matrix.mul_one]
      _ = (A * V) * Vᴴ := by simp [Matrix.mul_assoc]
      _ = (A * V * (SigmaPinvOf σ * Sσ)) * Vᴴ := by
            exact congrArg (fun X => X * Vᴴ) hAVcalc
      _ = ((A * V * SigmaPinvOf σ) * Sσ) * Vᴴ := by simpa [Matrix.mul_assoc]
      _ = (Uthin * Sσ) * Vᴴ := by simp [Uthin, Matrix.mul_assoc]
      _ = (Umat * SigmaRect) * Vᴴ := by
        -- Show Uthin * Σ = Umat * SigmaRect by proving matrix equality
        congr 1
        ext i j
        have hL : (Uthin * Sσ) i j = Uthin i j * (σ j : ℂ) := by
          simp [Matrix.mul_apply, Sσ, SigmaOf, Matrix.diagonal]
        have hR : (Umat * SigmaRect) i j = (b (Fin.castLE h j)) i * (σ j : ℂ) := by
          simp [Matrix.mul_apply, SigmaRect, Umat]
        by_cases hpos : 0 < σ j
        · have hb_eq : b (Fin.castLE h j) = (WithLp.equiv 2 (Fin m → ℂ)).symm (fun k => Uthin k j) := by
            simpa using hb_spec' j hpos
          -- Positive singular value case: use hb_eq to identify the column and cancel σ j
          rw [hL, hR, hb_eq]
          simp
        · -- In this case σ j = 0, so both sides are 0
          have hσ_zero : σ j = 0 := by
            have := le_of_not_gt hpos
            have h_nonneg := Real.sqrt_nonneg (hHherm.eigenvalues j)
            exact le_antisymm this h_nonneg
          -- In this case the diagonal entry σ j is zero, so both matrix products vanish
          have hL' : (Uthin * Sσ) i j = 0 := by
            simp [Matrix.mul_apply, Sσ, SigmaOf, Matrix.diagonal, hσ_zero]
          have hR' : (Umat * SigmaRect) i j = 0 := by
            simp [Matrix.mul_apply, SigmaRect, Umat, hσ_zero]
          rw [hL', hR']
      _ = Umat * SigmaRect * Vᴴ := by simp [Matrix.mul_assoc]
  -- bundle unitary identities for V
  have hVunit : (Vᴴ * V = 1) ∧ (V * Vᴴ = 1) := ⟨hVhV, hVVh⟩
  exact ⟨Umat, SigmaRect, V, hVunit, hSigmaRect_diag, hAeq⟩

/-! ### Rectangular SVD for wide matrices (m ≤ n) -/

theorem exists_rectSVD_wide (A : Matrix (Fin m) (Fin n) ℂ) {h : m ≤ n} :
    ∃ (U : Matrix (Fin m) (Fin m) ℂ) (Sigma : Matrix (Fin m) (Fin n) ℂ)
      (V : Matrix (Fin n) (Fin n) ℂ),
      ((Uᴴ * U = 1) ∧ (U * Uᴴ = 1)) ∧
      IsRectRealDiag (m := n) (n := m) Sigmaᴴ h ∧
      A = U * Sigma * Vᴴ := by
  classical
  -- Apply the rectangular SVD to the conjugate transpose Aᴴ : n×m
  obtain ⟨U', Sigma', V', hVunit', hSigmaRect', hArect⟩ :=
    (exists_rectSVD (m := n) (n := m) (A := Aᴴ) (h := h))
  -- Take conjugate transpose of the factorization of Aᴴ to get one for A
  have hA : A = V' * Sigma'ᴴ * U'ᴴ := by
    have := congrArg Matrix.conjTranspose hArect
    -- (Aᴴ)ᴴ = A, (U' * Sigma' * V'ᴴ)ᴴ = V' * Sigma'ᴴ * U'ᴴ
    simpa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using this
  -- Package the result in the requested form
  refine ⟨V', Sigma'ᴴ, U', ?_, ?_, ?_⟩
  · -- U is V', so it is unitary by hVunit'
    exact hVunit'
  · -- Sigma is Sigma'ᴴ, so Sigmaᴴ = Sigma' and inherits rectangular diagonal structure
    -- Goal: IsRectRealDiag (m := n) (n := m) (Sigma'ᴴ)ᴴ h
    simpa [Matrix.conjTranspose_conjTranspose] using hSigmaRect'
  · -- Equality A = U * Sigma * Vᴴ
    simpa [Matrix.mul_assoc] using hA

end Matrix
