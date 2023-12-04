import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.Convex.Cone.Pointed
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix Finset

variable {m n : Type*}

variable [Fintype m] [Fintype n]

theorem dotProduct_nonneg {v w : n → ℝ} (hv : 0 ≤ v) (hw : 0 ≤ w) : 0 ≤ v ⬝ᵥ w := by
  apply Finset.sum_nonneg
  simp only [mem_univ, gt_iff_lt, forall_true_left]
  exact fun _ => mul_nonneg (hv _) (hw _)

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
  have : IsClosedMap (mulVec A) := by
    /-
    theorem extracted_1.{u_1, u_2} {m : Type u_1} {n : Type u_2} [inst : Fintype m] [inst_1 : Fintype n]
      (A : Matrix m n ℝ) : IsClosedMap (mulVec A) := sorry
    -/
    extract_goal
    sorry
  exact this _ isClosed_Ici

variable [DecidableEq n]

theorem farkas_aux {y : EuclideanSpace ℝ m} (h : ∀ x ∈ mulVec_convexCone A, 0 ≤ x ⬝ᵥ y) :
    0 ≤ vecMul y A := by
  rintro i
  simp_rw [mulVec_convexCone, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_image, Set.mem_Ici, dotProduct_comm, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dotProduct_mulVec] at h
  specialize h (Pi.single i 1)
  simp_rw [dotProduct_single, Pi.single, le_update_self_iff, Pi.zero_apply, zero_le_one, mul_one,
    forall_true_left] at h
  exact h

theorem farkas : Xor'
    (∃ x : EuclideanSpace ℝ n, mulVec A x = b ∧ (0 : n → ℝ) ≤ x)
    (∃ y : EuclideanSpace ℝ m, 0 ≤ vecMul y A ∧ y ⬝ᵥ b < 0) := by
  rw [xor_iff_iff_not]
  push_neg
  constructor
  . rintro ⟨x, hx₁, hx₂⟩ y hy
    rw [← hx₁, dotProduct_mulVec]
    exact dotProduct_nonneg hy hx₂
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
