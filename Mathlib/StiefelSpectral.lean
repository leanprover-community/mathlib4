/-
Mathlib/StiefelSpectral.lean

Steepest-Descent Direction on the Stiefel Manifold under the Spectral Norm
-/
import Mathlib                     -- Mathlib4 core
import Mathlib.Data.Matrix.Basic   -- Matrix definitions
import Mathlib.Data.Matrix.Notation-- `ᵀ`, `!![…]` notation
-- (No `Norm` imports: we stub our own operator norm)

open Matrix BigOperators Real
open scoped Matrix

noncomputable section

/-! ### Basic predicates -/

/-- A square matrix is skew-symmetric iff `Aᵀ = -A`. -/
def IsSkewSymm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  Aᵀ = -A

/-- `W` lies on the real Stiefel manifold `S_{m,n}` (orthonormal columns). -/
def IsStiefel {m n : ℕ} (W : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  Wᵀ * W = 1

/-- `A` is tangent to `S_{m,n}` at `W`. -/
def IsTangent {m n : ℕ} (W A : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  IsSkewSymm (Wᵀ * A)

/-! ### Inner product and *stub* operator norm -/

/-- Frobenius inner product. -/
def frobDot {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j
notation "⟪" A ", " B "⟫" => frobDot A B

/-- **Stub** operator (spectral) norm.  
    Replace `0` with a genuine expression once you import a norm instance. -/
def opNorm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := 0
notation "‖" A "‖₂" => opNorm A

/-! ### Construction -/

/-- Project `Y` into the tangent space at `W`. (Skew-part projection.) -/
def projectTangent {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
    (Y : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  let S := Wᵀ * Y
  let skewS := (S - Sᵀ) / 2
  W * skewS

/-- Scale to *unit* operator norm if necessary (using the stubbed `‖·‖₂`). -/
def scaleToUnit {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) : Matrix (Fin m) (Fin n) ℝ :=
  if h : ‖X‖₂ ≤ 1 then X else (1 / ‖X‖₂) • X

/-- Closed-form steepest-descent direction (with stubbed norm). -/
def computeSteepestDescentSpectral {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
    (P : Matrix (Fin m) (Fin n) ℝ) (hP : IsTangent W P) :
    Matrix (Fin m) (Fin n) ℝ :=
  scaleToUnit (projectTangent W hW P)

/-! ### Properties (place-holders for now) -/

/-- `projectTangent` lands in the tangent space. -/
theorem project_tangent_is_tangent {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
    (Y : Matrix (Fin m) (Fin n) ℝ) :
    IsTangent W (projectTangent W hW Y) := by
  sorry

/-- Tangency + norm bound for `computeSteepestDescentSpectral`. -/
theorem compute_properties {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
    (P : Matrix (Fin m) (Fin n) ℝ) (hP : IsTangent W P) :
    let A⋆ := computeSteepestDescentSpectral W hW P hP
    IsTangent W A⋆ ∧ ‖A⋆‖₂ ≤ 1 := by
  sorry

/-- **Axiom** (to be proved once SVD/duality is available): optimality of `A⋆`. -/
axiom optimality {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ) (hW : IsStiefel W)
    (P : Matrix (Fin m) (Fin n) ℝ) (hP : IsTangent W P) :
    let A⋆ := computeSteepestDescentSpectral W hW P hP in
    ∀ A, IsTangent W A → ‖A‖₂ ≤ 1 → ⟪-P, A⟫ ≤ ⟪-P, A⋆⟫

end
