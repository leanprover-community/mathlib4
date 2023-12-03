import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Cone.Dual

open Matrix Finset

variable {m n : Type*}

variable [Fintype m] [Fintype n]

theorem dotProduct_pos {v w : n → ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w := by
  sorry

/-
theorem ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) {b : H} (disj : b ∉ K) :
    ∃ y : H, (∀ x : H, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪y, b⟫_ℝ < 0 := by
-/

variable (A : Matrix m n ℝ) (b : m → ℝ)

#check smul_nonneg

-- example (x : ℝ) : 0 < x → 0 ≤ x := by exact?

noncomputable def temp : ConvexCone ℝ (n → ℝ) where
  carrier := { x : n → ℝ | 0 ≤ mulVec A x }
  smul_mem' := by
    rintro x hx v hv
    rw [Set.mem_setOf_eq, mulVec_smul]
    exact smul_nonneg (le_of_lt hx) hv
  add_mem' := fun x hx y hy => by
    rw [Set.mem_setOf_eq, mulVec_add]
    exact add_nonneg hx hy

theorem farkas  :
    Xor' (∃ x : n → ℝ, mulVec A x = b ∧ 0 ≤ x) (∃ y : m → ℝ, 0 ≤ vecMul y A ∧ b ⬝ᵥ y < 0) := by
  rw [xor_iff_iff_not]
  push_neg
  constructor
  · rintro ⟨x, hx₁, hx₂⟩ y hy
    rw [← hx₁, dotProduct_comm, dotProduct_mulVec]
    exact dotProduct_pos hy hx₂
  · rintro h

    sorry
