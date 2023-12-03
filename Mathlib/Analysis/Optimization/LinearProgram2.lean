import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Cone.Dual

variable {m n 𝕜 : Type*}

open Matrix Finset

structure LinearConstraint (m n 𝕜) where
  LHS : Matrix m n 𝕜
  RHS : m → 𝕜

structure LinearProgram (m n 𝕜) where
  obj : n → 𝕜
  constraint : LinearConstraint m n 𝕜

namespace LinearConstraint

variable [Fintype m] [Fintype n]
variable [LinearOrderedCommRing 𝕜]

def is_feasible (c : LinearConstraint m n 𝕜) (v : n → 𝕜) :=
  mulVec c.LHS v ≤ c.RHS ∧ 0 ≤ v

end LinearConstraint

namespace LinearProgram

variable [Fintype m] [Fintype n]
variable [LinearOrderedCommRing 𝕜]

variable (lp : LinearProgram m n 𝕜)

def value (v : n → 𝕜) := lp.obj ⬝ᵥ v

def is_optimal (v : n → 𝕜) :=
  lp.constraint.is_feasible v ∧ ∀ w, lp.constraint.is_feasible w → lp.value w ≤ lp.value v

noncomputable def Dual : LinearProgram n m 𝕜 where
  obj := -lp.constraint.RHS
  constraint := ⟨-lp.constraint.LHSᵀ, -lp.obj⟩

theorem dotProduct_le_dotProduct_of_nonneg_left {u v w : n → 𝕜} (hu : 0 ≤ u) (hvw : v ≤ w) :
    u ⬝ᵥ v ≤ u ⬝ᵥ w :=
  sum_le_sum $ fun i _ => mul_le_mul_of_nonneg_left (hvw i) (hu i)

theorem dotProduct_le_dotProduct_of_nonneg_right {u v w : n → 𝕜} (hu : 0 ≤ u) (hvw : v ≤ w) :
    v ⬝ᵥ u ≤ w ⬝ᵥ u :=
  sum_le_sum $ fun i _ => mul_le_mul_of_nonneg_right (hvw i) (hu i)

theorem dotProduct_pos {v w : n → 𝕜} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w := by
  sorry

theorem Pi.neg_le_neg (x y : n → 𝕜) (h : x ≤ y) : -y ≤ -x := by
  rintro i
  simpa only [Pi.neg_apply, neg_le_neg_iff] using h i

theorem Pi.neg_le_neg_iff (x y : n → 𝕜) : -x ≤ -y ↔ y ≤ x := by
  sorry

theorem weak_duality (v : n → 𝕜) (w : m → 𝕜)
    (hv : lp.constraint.is_feasible v) (hw : lp.Dual.constraint.is_feasible w) :
    lp.value v ≤ -lp.Dual.value w := by
  obtain ⟨hv₁, hv₂⟩ := hv
  obtain ⟨hw₁, hw₂⟩ := hw
  simp_rw [value, Dual, neg_dotProduct, neg_neg]
  rw [Dual, ← Pi.neg_le_neg_iff, neg_mulVec, neg_neg, neg_neg] at hw₁
  calc lp.obj ⬝ᵥ v
      ≤ (mulVec lp.constraint.LHSᵀ w) ⬝ᵥ v := dotProduct_le_dotProduct_of_nonneg_right hv₂ hw₁
    _ = v ⬝ᵥ (mulVec lp.constraint.LHSᵀ w) := dotProduct_comm _ _
    _ = (vecMul v lp.constraint.LHSᵀ) ⬝ᵥ w := dotProduct_mulVec _ _ _
    _ = (mulVec lp.constraint.LHS v) ⬝ᵥ w := by rw [vecMul_transpose]
    _ ≤ lp.constraint.RHS ⬝ᵥ w := dotProduct_le_dotProduct_of_nonneg_right hw₂ hv₁

/--

/-- This is a stronger version of the Hahn-Banach separation theorem for closed convex cones. This
is also the geometric interpretation of Farkas' lemma. -/
theorem ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem (K : ConvexCone ℝ H)
    (ne : (K : Set H).Nonempty) (hc : IsClosed (K : Set H)) {b : H} (disj : b ∉ K) :
    ∃ y : H, (∀ x : H, x ∈ K → 0 ≤ ⟪x, y⟫_ℝ) ∧ ⟪y, b⟫_ℝ < 0 := by

-/


end LinearProgram
