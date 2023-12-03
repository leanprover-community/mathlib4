import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix Finset

variable {m n : Type*}

variable [Fintype m] [Fintype n]

theorem dotProduct_pos {v w : n → ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w := by
  sorry

variable (A : Matrix m n ℝ) (b : m → ℝ)

noncomputable def mulVec_convexCone : PointedCone ℝ (EuclideanSpace ℝ m) where
  carrier := (mulVec A) '' Set.Ici 0
  -- { b : EuclideanSpace ℝ m | ∃ x, mulVec A x = b ∧ 0 ≤ x}
  add_mem' := by
    rintro a b ⟨x, hx₁, hx₂⟩ ⟨y, hy₁, hy₂⟩
    use x + y
    constructor
    . rw [Set.mem_Ici] at hx₁
      apply add_nonneg hx₁ hy₁
    . rw [mulVec_add, hx₂, hy₂]
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro ⟨c, hc⟩ a ⟨x, hx₁, hx₂⟩
    rw [Set.mem_Ici] at hx₁
    use c • x
    constructor
    · apply smul_nonneg hc hx₁
    · simp [mulVec_smul, hx₂]


theorem isClosed_mulVec_convexCone :
    IsClosed (mulVec_convexCone A : Set (EuclideanSpace ℝ m)) := by
  sorry

theorem farkas_aux {y : EuclideanSpace ℝ m}
    (h : ∀ x ∈ mulVec_convexCone A, 0 ≤ x ⬝ᵥ y) :
    0 ≤ vecMul y A := by
  sorry

theorem farkas :
    Xor'
      (∃ x : EuclideanSpace ℝ n, mulVec A x = b ∧ (0 : n → ℝ) ≤ x)
      (∃ y : EuclideanSpace ℝ m, 0 ≤ vecMul y A ∧ y ⬝ᵥ b < 0) := by
  rw [xor_iff_iff_not]
  push_neg
  constructor
  . rintro ⟨x, hx₁, hx₂⟩ y hy
    rw [← hx₁, dotProduct_mulVec]
    exact dotProduct_pos hy hx₂
  . contrapose!
    rintro h

    let cone := mulVec_convexCone A
    have nonempty : Set.Nonempty (cone : Set (EuclideanSpace ℝ m)) := ⟨0, by simp⟩
    have isClosed : IsClosed (cone : Set (EuclideanSpace ℝ m)) := by sorry
    have temp := @ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_nmem (EuclideanSpace ℝ m) _ _ _ cone nonempty isClosed

    have : b ∉ cone := by
      rintro ⟨z, hz₁, hz₂⟩
      rw [Set.mem_Ici] at hz₁
      exact h z hz₂ hz₁

    obtain ⟨y, hy₁, hy₂⟩ := temp this
    exact ⟨y, farkas_aux A hy₁, hy₂⟩
