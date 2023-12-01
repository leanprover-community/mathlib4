import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

variable {m n 𝕜 : Type*}

open Matrix Finset

structure LinearProgram (m n 𝕜) [Fintype m] [Fintype n] [OrderedCommRing 𝕜] where
  obj : n → 𝕜
  LHS : Matrix m n 𝕜
  RHS : m → 𝕜

namespace LinearProgram

variable [Fintype m] [Fintype n]
variable [OrderedCommRing 𝕜]

variable (lp : LinearProgram m n 𝕜)

def value (v : n → 𝕜) := lp.obj ⬝ᵥ v

def is_feasible (v : n → 𝕜) :=
  mulVec lp.LHS v ≤ lp.RHS ∧ 0 ≤ v

def is_optimal (v : n → 𝕜) :=
  lp.is_feasible v ∧ ∀ w, lp.is_feasible w → lp.value w ≤ lp.value v

noncomputable def Dual : LinearProgram n m 𝕜 where
  obj := -lp.RHS
  LHS := -lp.LHSᵀ
  RHS := -lp.obj

theorem dotProduct_le_dotProduct_of_nonneg_left
    (u v w : n → 𝕜) (hu : 0 ≤ u) (hvw : v ≤ w) : u ⬝ᵥ v ≤ u ⬝ᵥ w :=
  sum_le_sum $ fun i _ => mul_le_mul_of_nonneg_left (hvw i) (hu i)


theorem Pi.neg_le_neg (x y : n → 𝕜) (h : x ≤ y) : -y ≤ -x := by
  rintro i
  simpa only [Pi.neg_apply, neg_le_neg_iff] using h i

theorem Pi.neg_le_neg_iff (x y : n → 𝕜) : -x ≤ -y ↔ y ≤ x := by
  sorry

theorem weak_duality (v : n → 𝕜) (w : m → 𝕜)
    (hv : lp.is_feasible v) (hw : lp.Dual.is_feasible w) :
    lp.value v ≤ -lp.Dual.value w := by
  simp_rw [value, Dual, neg_dotProduct, neg_neg]
  dsimp [is_feasible, value, Dual] at *
  obtain ⟨hv₁, hv₂⟩ := hv
  obtain ⟨hw₁, hw₂⟩ := hw
  rw [← Pi.neg_le_neg_iff, neg_mulVec, neg_neg, neg_neg] at hw₁
  calc lp.obj ⬝ᵥ v ≤ (mulVec lp.LHSᵀ w) ⬝ᵥ v := by sorry
    _ = v ⬝ᵥ (mulVec lp.LHSᵀ w) := dotProduct_comm _ _
    _ = (vecMul v lp.LHSᵀ) ⬝ᵥ w := by sorry
    _ = (mulVec lp.LHS v) ⬝ᵥ w := by rw [vecMul_transpose]
    _ ≤ lp.RHS ⬝ᵥ w := by sorry

end LinearProgram
