import Mathlib -- Main Mathlib import
import Mathlib.Data.Matrix.Block -- For block matrix operations
import Mathlib.Data.Matrix.Basic -- For basic matrix defs (provides extensionality for Matrix)
import Mathlib.LinearAlgebra.Matrix.Trace -- For trace inner product
import Mathlib.Data.Real.Basic -- For 1/2
import Mathlib.Tactic.Ring -- For ring / ring_nf / norm_num
import Mathlib.Tactic.Abel -- For abel / abel_nf
import Mathlib.Algebra.Module.Basic -- Provides smul properties (one_smul, add_smul, neg_smul)
import Mathlib.Algebra.Group.Basic -- Provides sub_eq_add_neg
import Mathlib.Tactic.Conv -- For conv mode
import Mathlib.Analysis.InnerProductSpace.Basic -- Potentially needed for frobDot properties
import Mathlib.LinearAlgebra.Matrix.Orthogonal -- Potentially relevant for Stiefel properties
import Mathlib.Tactic.NormNum -- Explicit import for norm_num
import Mathlib.Tactic.FieldSimp -- For field_simp tactic
-- import Mathlib.Tactic.Ext -- REMOVED: Incorrect import, ext should be available
import Mathlib.Tactic.Linarith -- For linarith tactic
import Mathlib.Tactic.SimpRw -- Provides simp_rw tactic if needed

open Matrix BigOperators Real Finset Function List Equiv -- Ensure List and Equiv are opened
open scoped Matrix BigOperators Nat -- Added Nat scope

-- disable 100-char-line warnings
set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

/-! # Definitions for Steepest Descent on Stiefel Manifold -/

/-- A square matrix is skew-symmetric iff Aᵀ = -A. -/
def IsSkewSymmetricDef {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop := Aᵀ = -A

/-- W lies on the Stiefel manifold Sₘ,ₙ (m ≥ n). -/
def IsStiefel {m n : ℕ} (_h_mn : n ≤ m) (W : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Wᵀ * W = 1

/-- A is tangent to Sₘ,ₙ at W. Uses explicit definition. -/
def IsTangent {m n : ℕ} (W A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  IsSkewSymmetricDef (Wᵀ * A)

/-- Frobenius inner product on m×n matrices. -/
def frobDot {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  Matrix.trace (Aᵀ * B) -- Using trace definition: sum (diag (Aᵀ * B))
notation "⟪" A ", " B "⟫_F" => frobDot A B

/-! # Assumed Components (Axioms / Opaque Definitions / Noncomputable Definitions) -/

/-- Structure to hold the result of SVD: A = U * Σ * Vᵀ -/
structure SVDResult (m n : ℕ) where
  U : Matrix (Fin m) (Fin m) ℝ
  Sigma : Matrix (Fin m) (Fin n) ℝ -- Diagonal matrix of singular values
  V : Matrix (Fin n) (Fin n) ℝ
  h_U_orth : U * Uᵀ = 1 ∧ Uᵀ * U = 1 -- U is orthogonal
  h_V_orth : V * Vᵀ = 1 ∧ Vᵀ * V = 1 -- V is orthogonal
  h_Sigma_diag : ∀ (i : Fin m) (j : Fin n), (i : ℕ) ≠ (j : ℕ) → Sigma i j = 0
  h_Sigma_nonneg : ∀ i j, Sigma i j ≥ 0 -- Singular values are non-negative

-- Axiom asserting the existence of SVD for any matrix A
axiom svdExists (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
  ∃ (res : SVDResult m n), res.U * res.Sigma * res.Vᵀ = A

-- Define a function to get the SVD result (noncomputably) using indefinite description
noncomputable def svd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
  { res : SVDResult m n // res.U * res.Sigma * res.Vᵀ = A } :=
  Classical.indefiniteDescription _ (svdExists m n A)

/-- Extract singular values from the Sigma matrix of SVD as a function. -/
noncomputable def singularValuesFn {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Fin (min m n) → ℝ :=
  let Sigma := (svd A).val.Sigma
  fun (k : Fin (min m n)) =>
    Sigma (Fin.castLE (Nat.min_le_left m n) k) (Fin.castLE (Nat.min_le_right m n) k)

/-- Operator norm (spectral norm) - largest singular value (defined via axiomatized SVD). -/
noncomputable def opNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  let k := min m n
  if h : k = 0 then
    0
  else
    let sv_fn := singularValuesFn A
    have fin_k_pos : 0 < k := Nat.pos_of_ne_zero h
    let fin_k_nonempty : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp fin_k_pos
    let univ_nonempty : (Finset.univ : Finset (Fin k)).Nonempty :=
      Finset.univ_nonempty_iff.mpr fin_k_nonempty
    Finset.sup' Finset.univ univ_nonempty sv_fn

notation "‖" A "‖₂" => opNorm A

/-- Structure for Orthogonal Complement Basis -/
structure OrthogonalComplementBasis (m n : ℕ) (h_mn : n ≤ m) (W : Matrix (Fin m) (Fin n) ℝ) where
  W_perp : Matrix (Fin m) (Fin (m - n)) ℝ
  h_orthonormal : W_perpᵀ * W_perp = 1
  h_orthogonal_to_W : Wᵀ * W_perp = 0

-- Axiom asserting existence of the orthogonal complement basis
axiom orthogonalComplementBasisExists :
  ∀ {m n : ℕ} (h_mn : n ≤ m)
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel h_mn W),
  ∃ (basis : OrthogonalComplementBasis m n h_mn W), True

-- Define a function to get the basis (noncomputably)
noncomputable def getOrthogonalComplementBasis {m n : ℕ} (h_mn : n ≤ m)
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel h_mn W) :
  OrthogonalComplementBasis m n h_mn W :=
  Classical.indefiniteDescription _ (orthogonalComplementBasisExists h_mn W hW)

/-! # Block Matrix Operations (Implemented using Mathlib) -/

def blockStackImpl {m n : ℕ} (h_mn : n ≤ m)
  (S : Matrix (Fin n) (Fin n) ℝ) (T : Matrix (Fin (m - n)) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  let Zeros_n0 : Matrix (Fin n) (Fin 0) ℝ := 0
  let Zeros_mn0 : Matrix (Fin (m - n)) (Fin 0) ℝ := 0
  let BlockedSum := Matrix.fromBlocks S Zeros_n0 T Zeros_mn0
  have h_dims_row : n + (m - n) = m := Nat.add_sub_of_le h_mn
  have h_dims_col : n + 0 = n := by simp
  let row_map := fun (x : Fin m) => (h_dims_row ▸ finSumFinEquiv.symm) x
  let col_map := fun (x : Fin n) => (h_dims_col ▸ (Equiv.sumEmpty (Fin n) (Fin 0)).symm) x
  BlockedSum.submatrix row_map col_map

def blockExtractTopImpl {m n k : ℕ} (h_k_le_m : k ≤ m)
  (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin k) (Fin n) ℝ :=
  A.submatrix (Fin.castLEEmb h_k_le_m) (Equiv.refl _)

def blockExtractBottomImpl {m n k : ℕ} (h_k_le_m : k ≤ m)
  (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin (m - k)) (Fin n) ℝ :=
  have h_dims : k + (m - k) = m := Nat.add_sub_of_le h_k_le_m
  let row_map : Fin (m - k) → Fin m := fun i => h_dims ▸ finSumFinEquiv (Sum.inr i)
  A.submatrix row_map (Equiv.refl _)

def blockExtractColumnsImpl {m n k : ℕ} (h_k_le_n : k ≤ n)
  (A : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin k) ℝ :=
  A.submatrix (Equiv.refl _) (Fin.castLEEmb h_k_le_n)

def blockExtractColumnsImpl' {m k : ℕ} (h_k_le_m : k ≤ m)
  (A : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin k) ℝ :=
  A.submatrix (Equiv.refl _) (Fin.castLEEmb h_k_le_m)

/-! # Core Algorithm Functions -/

def symmPart {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (1/2 : ℝ) • (M + Mᵀ)

def skewPart {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (1/2 : ℝ) • (M - Mᵀ)

def projectTangent {m n : ℕ} (_h_mn : n ≤ m)
  (W : Matrix (Fin m) (Fin n) ℝ)
  (Y : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  let M := Wᵀ * Y
  Y - W * (symmPart M)

def scaleToUnit {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  let norm := ‖X‖₂
  if h_norm_le_one : norm ≤ 1 then
    X
  else
    have h_norm_ne_zero : norm ≠ 0 := by linarith -- Assuming norm > 1 implies norm ≠ 0
    (1 / norm) • X

def computeSteepestDescentSpectral {m n : ℕ} (h_mn : n ≤ m)
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel h_mn W)
  (G : Matrix (Fin m) (Fin n) ℝ) :
  Matrix (Fin m) (Fin n) ℝ :=
  let P : Matrix (Fin m) (Fin n) ℝ := projectTangent h_mn W G
  if hP_zero : P = 0 then
    0
  else
    let W_perp_basis := getOrthogonalComplementBasis h_mn W hW
    let W_perp := W_perp_basis.W_perp
    let S : Matrix (Fin n) (Fin n) ℝ := Wᵀ * P
    let T : Matrix (Fin (m - n)) (Fin n) ℝ := W_perpᵀ * P
    let Z : Matrix (Fin m) (Fin n) ℝ := blockStackImpl h_mn S T
    let svdZ_prop := svd Z
    let svdZ := svdZ_prop.val
    let U_Z := svdZ.U
    let V_Z := svdZ.V
    let U_Z_thin : Matrix (Fin m) (Fin n) ℝ := blockExtractColumnsImpl' h_mn U_Z -- Corrected to use h_mn
    let Y : Matrix (Fin m) (Fin n) ℝ := - U_Z_thin * V_Zᵀ
    let Y_top : Matrix (Fin n) (Fin n) ℝ := blockExtractTopImpl h_mn Y
    let Y_bottom : Matrix (Fin (m-n)) (Fin n) ℝ := blockExtractBottomImpl h_mn Y
    let Omega_prime : Matrix (Fin n) (Fin n) ℝ := skewPart Y_top
    let K_prime : Matrix (Fin (m-n)) (Fin n) ℝ := Y_bottom
    let X_prime : Matrix (Fin m) (Fin n) ℝ := blockStackImpl h_mn Omega_prime K_prime
    let X_star : Matrix (Fin m) (Fin n) ℝ := scaleToUnit X_prime
    let Omega_star : Matrix (Fin n) (Fin n) ℝ := blockExtractTopImpl h_mn X_star
    let K_star : Matrix (Fin (m-n)) (Fin n) ℝ := blockExtractBottomImpl h_mn X_star
    let A_star := W * Omega_star + W_perp * K_star
    A_star

/-! # Proof of Tangency for Projection -/

lemma symmPart_transpose {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) : (symmPart M)ᵀ = symmPart M := by
  unfold symmPart; rw [transpose_smul, transpose_add, transpose_transpose, add_comm]

-- Helper identity: M - symmPart M = skewPart M
lemma sub_symmPart_eq_skewPart {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
  M - symmPart M = skewPart M := by
  -- Prove M - (1/2) • M = (1/2) • M using conv mode for targeted rewrite
  have h_combine : M - (1/2 : ℝ) • M = (1/2 : ℝ) • M := by
    rw [sub_eq_add_neg] -- Step 1: Goal: M + -( (1/2) • M ) = (1/2) • M
    rw [← neg_smul]    -- Step 2: Goal: M + (-1/2) • M = (1/2) • M
    conv =>           -- Step 3: Enter conv mode to target the rewrite
      lhs            -- Focus on the left side: M + (-1/2) • M
      arg 1          -- Focus on the first argument of '+': M
      rw [← one_smul ℝ M] -- Rewrite *only* this M to 1 • M
    -- Exit conv mode. Goal should now be: 1 • M + (-1/2) • M = (1/2) • M
    rw [← add_smul]    -- Step 4: Apply distributivity r • x + s • x = (r + s) • x
    norm_num           -- Step 5: Calculate 1 + (-1/2) = 1/2 numerically
  -- Now use this in the main calculation
  calc
    M - symmPart M = M - (1/2 : ℝ) • (M + Mᵀ) := by unfold symmPart; rfl
    _ = M - ((1/2 : ℝ) • M + (1/2 : ℝ) • Mᵀ) := by rw [smul_add]
    _ = M - (1/2 : ℝ) • M - (1/2 : ℝ) • Mᵀ := by rw [sub_add_eq_sub_sub]
    _ = (M - (1/2 : ℝ) • M) - (1/2 : ℝ) • Mᵀ := by rw [sub_sub] -- Group terms
    _ = (1/2 : ℝ) • M - (1/2 : ℝ) • Mᵀ := by rw [h_combine] -- Use the proven equality
    _ = (1/2 : ℝ) • (M - Mᵀ) := by rw [smul_sub] -- Factor out scalar
    _ = skewPart M := by unfold skewPart; rfl

lemma skewPart_transpose_eq_neg {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
  (skewPart M)ᵀ = -skewPart M := by
  unfold skewPart
  simp only [transpose_smul, transpose_sub, transpose_transpose, smul_sub, neg_smul]
  abel

theorem project_tangent_is_tangent {m n : ℕ} (h_mn : n ≤ m)
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel h_mn W)
  (Y : Matrix (Fin m) (Fin n) ℝ) :
  IsTangent W (projectTangent h_mn W Y) := by
  rw [IsTangent]
  let M := Wᵀ * Y
  have h_term_eq_skewPart : Wᵀ * (projectTangent h_mn W Y) = skewPart M := calc
    Wᵀ * (projectTangent h_mn W Y) = Wᵀ * (Y - W * symmPart M) := by rw [projectTangent]
    _ = Wᵀ * Y - Wᵀ * (W * symmPart M) := by rw [Matrix.mul_sub]
    _ = Wᵀ * Y - (Wᵀ * W) * symmPart M := by rw [Matrix.mul_assoc]
    _ = Wᵀ * Y - 1 * symmPart M := by rw [hW]
    _ = M - 1 * symmPart M := rfl
    _ = M - symmPart M := by rw [Matrix.one_mul]
    _ = skewPart M := by rw [sub_symmPart_eq_skewPart] -- Use the helper lemma
  rw [h_term_eq_skewPart]
  rw [IsSkewSymmetricDef]
  exact skewPart_transpose_eq_neg M

/-! # Example Axioms (Unproven Assertions about Algorithm Components) -/

axiom scaleToUnit_norm_le_one :
  ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ), ‖scaleToUnit X‖₂ ≤ 1

axiom computeSteepestDescent_IsTangent :
  ∀ {m n : ℕ} (h_mn : n ≤ m) (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel h_mn W) (G : Matrix (Fin m) (Fin n) ℝ),
  IsTangent W (computeSteepestDescentSpectral h_mn W hW G)

axiom computeSteepestDescent_Optimality
  {m n : ℕ} {h_mn : n ≤ m} {W : Matrix (Fin m) (Fin n) ℝ} {hW : IsStiefel h_mn W} {G : Matrix (Fin m) (Fin n) ℝ} :
  let A_star := computeSteepestDescentSpectral h_mn W hW G
  ∀ (A : Matrix (Fin m) (Fin n) ℝ) (hA_tangent : IsTangent W A) (hA_norm : ‖A‖₂ ≤ 1),
  ⟪G, A_star⟫_F ≤ ⟪G, A⟫_F

axiom blockStack_extract_eq_self {m n : ℕ} (h_mn : n ≤ m)
  (S : Matrix (Fin n) (Fin n) ℝ) (T : Matrix (Fin (m - n)) (Fin n) ℝ) :
  let Z := blockStackImpl h_mn S T
  let S' := blockExtractTopImpl h_mn Z
  let T' := blockExtractBottomImpl h_mn Z
  S' = S ∧ T' = T

-- Stray lines from previous error message? Removed.

end noncomputable section
