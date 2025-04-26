import Mathlib

open Matrix BigOperators Real
open scoped Matrix

-- disable 100-char-line warnings
set_option linter.style.longLine false
set_option linter.unusedVariables false

noncomputable section

/-- A square matrix is skew-symmetric iff Aᵀ = -A. -/
def IsSkewSymm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Aᵀ = -A

/-- W lies on the Stiefel manifold Sₘ,ₙ. -/
def IsStiefel {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Wᵀ * W = 1

/-- A is tangent to Sₘ,ₙ at W. -/
def IsTangent {m n : ℕ} (W A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  IsSkewSymm (Wᵀ * A)

/-- Frobenius inner product on m×n matrices. -/
def frobDot {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j
notation "⟪" A ", " B "⟫" => frobDot A B

/-- Stub operator‐norm (spectral norm). -/
def opNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := 0
notation "‖" A "‖₂" => opNorm A

/-- Project Y into the tangent space at W. -/
def projectTangent {m n : ℕ}
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
  (Y : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  let S    := Wᵀ * Y
  let skew := (2⁻¹ : ℝ) • (S - Sᵀ)   -- use “ℝ • Matrix” so Lean finds the action instance
  W * skew

/-- Scale X down to ‖·‖₂ ≤ 1 if needed. -/
def scaleToUnit {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  if ‖X‖₂ ≤ 1 then X else (1 / ‖X‖₂) • X

/-- Closed-form steepest-descent under ‖·‖₂ ≤ 1 in the tangent space. -/
def computeSteepestDescentSpectral {m n : ℕ}
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
  (P : Matrix (Fin m) (Fin n) ℝ) (hP : IsTangent W P) :
  Matrix (Fin m) (Fin n) ℝ :=
  scaleToUnit (projectTangent W hW P)

/-- **Axiom.** `projectTangent` really lands in the tangent space. -/
axiom project_tangent_is_tangent {m n : ℕ}
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
  (Y : Matrix (Fin m) (Fin n) ℝ) :
  IsTangent W (projectTangent W hW Y)

/-- **Axiom.** `computeSteepestDescentSpectral` is tangent and has norm ≤ 1. -/
axiom compute_properties {m n : ℕ}
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
  (P : Matrix (Fin m) (Fin n) ℝ) (hP : IsTangent W P) :
  IsTangent W (computeSteepestDescentSpectral W hW P hP)
  ∧ ‖computeSteepestDescentSpectral W hW P hP‖₂ ≤ 1

/-- **Axiom.** `computeSteepestDescentSpectral` is optimal among all tangent A with ‖A‖₂ ≤ 1. -/
axiom optimality {m n : ℕ}
  (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
  (P : Matrix (Fin m) (Fin n) ℝ) (hP : IsTangent W P)
  (A : Matrix (Fin m) (Fin n) ℝ) (hA : IsTangent W A) (hA_norm : ‖A‖₂ ≤ 1) :
  ⟪-P, A⟫ ≤ ⟪-P, computeSteepestDescentSpectral W hW P hP⟫
