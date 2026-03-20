/-
Copyright (c) 2025 William Weishuhn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Weishuhn
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Matrix.MoorePenrose.Defs

/-!
# The Moore-Penrose Pseudo-Inverse for Matrices

Constructs the Moore-Penrose pseudo-inverse for matrices over `ℝ` or `ℂ` and proves
basic properties.

## Main definitions

* `Matrix.moorePenroseInverse`: the Moore-Penrose pseudo-inverse of a matrix.

## Main results

* `Matrix.exists_isMoorePenroseInverse`: existence of the Moore-Penrose inverse for matrices
  over `RCLike` fields, via orthogonal projection and the restricted isomorphism
  `ker(A)ᗮ ≃ₗ range(A)`.
* `Matrix.isMoorePenroseInverse_unique`: uniqueness for rectangular matrices (the semigroup
  version `IsMoorePenroseInverse.unique` only covers square matrices).
* `Matrix.moorePenroseInverse_conjTranspose`: `(Aᴴ)⁺ = (A⁺)ᴴ`.
* `Matrix.moorePenroseInverse_eq_nonsing_inv`: for invertible matrices, `A⁺ = A⁻¹`.

## References

* <https://github.com/leanprover-community/mathlib4/issues/24787>
-/
noncomputable section
namespace Matrix
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]
omit [DecidableEq m] [DecidableEq n] in
/-- Heterogeneous uniqueness for matrices. -/
lemma isMoorePenroseInverse_unique {A : Matrix m n 𝕜} {B C : Matrix n m 𝕜}
    (hB : IsMoorePenroseInverse A B) (hC : IsMoorePenroseInverse A C) : B = C := by
  have h1 : B * A = C * A := by
    have eq1 : B * A = (B * A) * (C * A) := by
      calc B * A = B * (A * C * A) := by rw [hC.mul_mul_cancel_left]
        _ = (B * A) * (C * A) := by simp only [Matrix.mul_assoc]
    have eq2 : C * A = (C * A) * (B * A) := by
      calc C * A = C * (A * B * A) := by rw [hB.mul_mul_cancel_left]
        _ = (C * A) * (B * A) := by simp only [Matrix.mul_assoc]
    have eq3 : C * A = (B * A) * (C * A) := by
      have h := congr_arg star eq2
      rw [hC.star_self_mul] at h
      rw [star_mul, hB.star_self_mul, hC.star_self_mul] at h
      exact h
    exact eq1.trans eq3.symm
  have h2 : A * B = A * C := by
    have eq1 : A * B = (A * C) * (A * B) := by
      calc A * B = (A * C * A) * B := by rw [hC.mul_mul_cancel_left]
        _ = (A * C) * (A * B) := by simp only [Matrix.mul_assoc]
    have eq2 : A * C = (A * B) * (A * C) := by
      calc A * C = (A * B * A) * C := by rw [hB.mul_mul_cancel_left]
        _ = (A * B) * (A * C) := by simp only [Matrix.mul_assoc]
    have eq3 : A * C = (A * C) * (A * B) := by
      have h := congr_arg star eq2
      rw [hC.star_mul_self] at h
      rw [star_mul, hB.star_mul_self, hC.star_mul_self] at h
      exact h
    exact eq1.trans eq3.symm
  calc B = B * A * B := hB.mul_mul_cancel_right.symm
    _ = C * A * B := by rw [h1]
    _ = C * (A * B) := Matrix.mul_assoc _ _ _
    _ = C * (A * C) := by rw [h2]
    _ = C * A * C := (Matrix.mul_assoc _ _ _).symm
    _ = C := hC.mul_mul_cancel_right

/-- Every matrix over an `RCLike` field has a Moore-Penrose inverse.
The construction uses the restricted isomorphism `ker(f)ᗮ ≃ₗ range(f)`
and orthogonal projections. -/
theorem exists_isMoorePenroseInverse (A : Matrix m n 𝕜) :
    ∃ (As : Matrix n m 𝕜), IsMoorePenroseInverse A As := by
  -- 1. Setup via toEuclideanLin (= toLpLin 2 2)
  let f := Matrix.toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n) A
  -- 2. Orthogonal decomposition
  let K := LinearMap.ker f
  let W := LinearMap.range f
  have h_compl : IsCompl (Kᗮ) K :=
    (Submodule.isCompl_orthogonal_of_hasOrthogonalProjection (K := K)).symm
  -- 3. Restricted isomorphism
  let e : Kᗮ ≃ₗ[𝕜] W := LinearMap.kerComplementEquivRange f h_compl
  -- 4. Build pseudo-inverse
  let g : EuclideanSpace 𝕜 m →ₗ[𝕜] EuclideanSpace 𝕜 n :=
    Kᗮ.subtype ∘ₗ e.symm.toLinearMap ∘ₗ
      (Submodule.orthogonalProjection W : _ →L[𝕜] _).toLinearMap
  let As : Matrix n m 𝕜 :=
    (Matrix.toEuclideanLin (𝕜 := 𝕜) (m := n) (n := m)).symm g
  use As
  -- toEuclideanLin As = g
  have hAs : Matrix.toEuclideanLin As = g := LinearEquiv.apply_symm_apply _ g
  -- ↑(e x) = f (Kᗮ.subtype x)
  have key_e : ∀ x : ↥Kᗮ,
      (e x : EuclideanSpace 𝕜 m) = f (Kᗮ.subtype x) := by
    intro x
    simp only [e, LinearMap.kerComplementEquivRange, LinearEquiv.ofBijective_apply,
      LinearMap.comp_apply, LinearMap.codRestrict_apply]
  -- 1: f ∘ g = W.starProjection
  have fg_eq : ∀ w, f (g w) = Submodule.starProjection W w := by
    intro w
    show f (Kᗮ.subtype (e.symm ((Submodule.orthogonalProjection W) w))) =
      Submodule.starProjection W w
    rw [← key_e, LinearEquiv.apply_symm_apply]
    exact (Submodule.starProjection_apply W w).symm
  -- 2: g ∘ f = Kᗮ.starProjection
  have gf_eq : ∀ v, g (f v) = Submodule.starProjection Kᗮ v := by
    intro v
    symm
    have hgfv_mem : g (f v) ∈ Kᗮ := SetLike.coe_mem _
    have hv_sub_mem : v - g (f v) ∈ (Kᗮ)ᗮ := by
      apply Submodule.le_orthogonal_orthogonal K
      rw [LinearMap.mem_ker, map_sub, fg_eq,
        Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self f v)]
      exact sub_self _
    exact Submodule.eq_starProjection_of_mem_orthogonal' hgfv_mem hv_sub_mem
      (by rw [add_comm, sub_add_cancel])
  -- Verify the 4 Penrose conditions
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Condition 1: A * As * A = A
    apply Matrix.toEuclideanLin.injective
    simp only [Matrix.toLpLin_mul_same, hAs]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    rw [fg_eq, Submodule.starProjection_eq_self_iff.mpr (LinearMap.mem_range_self f v)]
  · -- Condition 2: As * A * As = As
    apply Matrix.toEuclideanLin.injective
    simp only [Matrix.toLpLin_mul_same, hAs]
    refine LinearMap.ext fun w => ?_
    simp only [LinearMap.comp_apply]
    rw [gf_eq]
    exact Submodule.starProjection_eq_self_iff.mpr (SetLike.coe_mem _)
  · -- Condition 3: star (A * As) = A * As
    show (A * As)ᴴ = A * As
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [Matrix.toLpLin_mul_same, hAs]
    exact LinearMap.IsSymmetric.adjoint_eq (fun u v => by
      simp only [LinearMap.comp_apply]
      change @inner 𝕜 _ _ (f (g u)) v = @inner 𝕜 _ _ u (f (g v))
      rw [fg_eq, fg_eq]
      exact Submodule.inner_starProjection_left_eq_right W u v)
  · -- Condition 4: star (As * A) = As * A
    show (As * A)ᴴ = As * A
    apply Matrix.toEuclideanLin.injective
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [Matrix.toLpLin_mul_same, hAs]
    exact LinearMap.IsSymmetric.adjoint_eq (fun u v => by
      simp only [LinearMap.comp_apply]
      change @inner 𝕜 _ _ (g (f u)) v = @inner 𝕜 _ _ u (g (f v))
      rw [gf_eq, gf_eq]
      exact Submodule.inner_starProjection_left_eq_right Kᗮ u v)

/-- The Moore-Penrose pseudo-inverse of a matrix. -/
def moorePenroseInverse (A : Matrix m n 𝕜) : Matrix n m 𝕜 :=
  (exists_isMoorePenroseInverse A).choose

/-- `moorePenroseInverse A` satisfies the four Penrose conditions
with respect to `A`. -/
lemma isMoorePenroseInverse_moorePenroseInverse (A : Matrix m n 𝕜) :
    IsMoorePenroseInverse A (moorePenroseInverse A) :=
  (exists_isMoorePenroseInverse A).choose_spec

@[simp]
lemma moorePenroseInverse_zero : moorePenroseInverse (0 : Matrix m n 𝕜) = 0 := by
  have h_zero : IsMoorePenroseInverse (0 : Matrix m n 𝕜) (0 : Matrix n m 𝕜) :=
    ⟨by simp, by simp, by simp, by simp⟩
  exact isMoorePenroseInverse_unique
    (isMoorePenroseInverse_moorePenroseInverse 0) h_zero

@[simp]
lemma moorePenroseInverse_moorePenroseInverse (A : Matrix m n 𝕜) :
    moorePenroseInverse (moorePenroseInverse A) = A := by
  have h1 := isMoorePenroseInverse_moorePenroseInverse A
  have h2 := isMoorePenroseInverse_moorePenroseInverse (moorePenroseInverse A)
  exact isMoorePenroseInverse_unique h2 h1.symm

@[simp]
lemma moorePenroseInverse_conjTranspose (A : Matrix m n 𝕜) :
    moorePenroseInverse (Aᴴ) = (moorePenroseInverse A)ᴴ := by
  set B := moorePenroseInverse A
  have hB := isMoorePenroseInverse_moorePenroseInverse A
  apply isMoorePenroseInverse_unique (isMoorePenroseInverse_moorePenroseInverse Aᴴ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Aᴴ * Bᴴ * Aᴴ
        = (A * B * A)ᴴ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Aᴴ := by rw [hB.mul_mul_cancel_left]
  · calc Bᴴ * Aᴴ * Bᴴ
        = (B * A * B)ᴴ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = Bᴴ := by rw [hB.mul_mul_cancel_right]
  · calc star (Aᴴ * Bᴴ)
        = (Aᴴ * Bᴴ)ᴴ := rfl
      _ = Bᴴᴴ * Aᴴᴴ := conjTranspose_mul _ _
      _ = B * A := by simp only [conjTranspose_conjTranspose]
      _ = star (B * A) := hB.star_self_mul.symm
      _ = (B * A)ᴴ := rfl
      _ = Aᴴ * Bᴴ := conjTranspose_mul B A
  · calc star (Bᴴ * Aᴴ)
        = (Bᴴ * Aᴴ)ᴴ := rfl
      _ = Aᴴᴴ * Bᴴᴴ := conjTranspose_mul _ _
      _ = A * B := by simp only [conjTranspose_conjTranspose]
      _ = star (A * B) := hB.star_mul_self.symm
      _ = (A * B)ᴴ := rfl
      _ = Bᴴ * Aᴴ := conjTranspose_mul A B

/-- For an invertible square matrix, the Moore-Penrose inverse
equals the ordinary inverse. -/
lemma moorePenroseInverse_eq_nonsing_inv
    {n' : Type*} [Fintype n'] [DecidableEq n']
    (A : Matrix n' n' 𝕜) (hA : IsUnit A) :
    moorePenroseInverse A = A⁻¹ := by
  have hdet : IsUnit A.det := isUnit_iff_isUnit_det _ |>.mp hA
  apply isMoorePenroseInverse_unique (isMoorePenroseInverse_moorePenroseInverse A)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [mul_nonsing_inv _ hdet]
  · simp [nonsing_inv_mul _ hdet]
  · rw [mul_nonsing_inv _ hdet, star_one]
  · rw [nonsing_inv_mul _ hdet, star_one]

@[simp]
lemma moorePenroseInverse_one {n' : Type*} [Fintype n'] [DecidableEq n'] :
    moorePenroseInverse (1 : Matrix n' n' 𝕜) = 1 := by
  apply isMoorePenroseInverse_unique (isMoorePenroseInverse_moorePenroseInverse 1)
  exact ⟨by simp, by simp, by simp, by simp⟩

/-- The four Penrose conditions hold for `A` and `moorePenroseInverse A`. -/
lemma mul_moorePenroseInverse_mul (A : Matrix m n 𝕜) :
    A * moorePenroseInverse A * A = A :=
  (isMoorePenroseInverse_moorePenroseInverse A).mul_mul_cancel_left

lemma moorePenroseInverse_mul_self_mul (A : Matrix m n 𝕜) :
    moorePenroseInverse A * A * moorePenroseInverse A = moorePenroseInverse A :=
  (isMoorePenroseInverse_moorePenroseInverse A).mul_mul_cancel_right

lemma star_mul_moorePenroseInverse (A : Matrix m n 𝕜) :
    star (A * moorePenroseInverse A) = A * moorePenroseInverse A :=
  (isMoorePenroseInverse_moorePenroseInverse A).star_mul_self

lemma star_moorePenroseInverse_mul (A : Matrix m n 𝕜) :
    star (moorePenroseInverse A * A) = moorePenroseInverse A * A :=
  (isMoorePenroseInverse_moorePenroseInverse A).star_self_mul

end Matrix
