/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Basic lemmas about the general linear group $GL(n, R)$

This file lists various basic lemmas about the general linear group $GL(n, R)$. For the definitions,
see `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`.
-/

namespace Matrix

/-- The outer product of two non-zero vectors is nonzero. -/
theorem vecMulVec_ne_zero {R n : Type*} [MulZeroClass R] [NoZeroDivisors R]
    {α β : n → R} (hα : α ≠ 0) (hβ : β ≠ 0) :
    vecMulVec α β ≠ 0 := by
  obtain ⟨i, hiy⟩ := Function.ne_iff.mp hβ
  obtain ⟨j, hju⟩ := Function.ne_iff.mp hα
  simp [ne_eq, ← ext_iff, vecMulVec_apply]
  exact ⟨⟨j, hju⟩, ⟨i, hiy⟩⟩

variable {R n : Type*} [Fintype n] [DecidableEq n]

private def mat_T [Semiring R] (f : (Matrix n n R) →ₗ[R] Matrix n n R) (y z : n → R) :
    (n → R) →ₗ[R] n → R where
  toFun x := f (vecMulVec x y) *ᵥ z
  map_add' w p := by simp_rw [vecMulVec_eq (Fin 1), replicateCol_add w p,
    Matrix.add_mul, map_add, add_mulVec]
  map_smul' w r := by simp_rw [vecMulVec_eq (Fin 1), RingHom.id_apply,
    replicateCol_smul, smul_mul, LinearMap.map_smul, smul_mulVec_assoc]

private theorem mat_T_mul
    [CommSemiring R] (f : Matrix n n R →ₙₐ[R] Matrix n n R)
    (y z : n → R) (A : Matrix n n R) :
    ((mat_T f y z).toMatrix' * A) = (f A * (mat_T f y z).toMatrix') := by
  apply_fun toLin' using toLin'.injective
  rw [LinearMap.ext_iff]
  intro x
  let T := mat_T f y z
  calc
    ((LinearMap.toMatrix' T) * A) *ᵥ x = T (A *ᵥ x) :=
      by ext; rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    _ = (f (vecMulVec (A *ᵥ x) y)) *ᵥ z := by simp [T, mat_T]
    _ = (f (A * vecMulVec x y)) *ᵥ z := by
      simp_rw [vecMulVec_eq (Fin 1), replicateCol_mulVec, ← Matrix.mul_assoc]
    _ = (f A * f (vecMulVec x y)) *ᵥ z := by simp_rw [map_mul]
    _ = (f A) *ᵥ (T x) := by
      simp [← mulVec_mulVec]; rfl
    _ = (f A * (LinearMap.toMatrix' T)) *ᵥ x := by
      simp_rw [← mulVec_mulVec, ← toLin'_apply (LinearMap.toMatrix' T), toLin'_toMatrix']

theorem AlgEquiv.exists_generalLinearGroup_conj
    [Field R] (f : Matrix n n R ≃ₐ[R] Matrix n n R) :
    ∃ T : GL n R, (∀ a, f a * T = T * a) := by
  by_cases hn : IsEmpty n
  · use 1
    intro
    ext i _
    exact isEmpty_iff.mp hn i |>.elim
  rw [not_isEmpty_iff] at hn
  have : ∃ u : n → R, u ≠ 0 := ⟨1, one_ne_zero⟩
  have t1 := this
  obtain ⟨⟨u, hu⟩, ⟨y, hy⟩⟩ := this, t1
  have : ∃ z : n → R, (f (vecMulVec u y)) *ᵥ z ≠ 0 := by
    simp_rw [ne_eq, ← not_forall]
    suffices ¬f (vecMulVec u y) = 0 by
      rwa [← LinearMap.toMatrix'_toLin' (f _), EmbeddingLike.map_eq_zero_iff,
        LinearMap.ext_iff] at this
    rw [← ne_eq, EmbeddingLike.map_ne_zero_iff]
    exact vecMulVec_ne_zero hu hy
  obtain ⟨z, hz⟩ := this
  let T := mat_T f.toLinearMap y z
  let M := T.toMatrix'
  suffices hM : IsUnit M by
    use hM.unit
    intro A
    simp [M]
    exact mat_T_mul f.toAlgHom.toNonUnitalAlgHom y z A |>.symm
  rw [← isUnit_toLin'_iff]
  simp_rw [M, toLin'_toMatrix', LinearMap.isUnit_iff_range_eq_top, LinearMap.range_eq_top]
  intro w
  have hi : T u ≠ 0 := by simpa [T, mat_T]
  have this1 : ∃ d : n → R, T u ⬝ᵥ d = 1 := by
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hi
    use Pi.single q (T u q)⁻¹
    rw [dotProduct_single, mul_inv_cancel₀ hq]
  obtain ⟨B, hB⟩ : ∃ B : Matrix n n R, (f B) *ᵥ (T u) = w := by
    obtain ⟨d, hd⟩ := this1
    obtain ⟨B, hB⟩ := f.bijective.2 (vecMulVec w d)
    use B
    rw [hB, vecMulVec_eq (Fin 1), ← mulVec_mulVec]
    suffices (replicateRow (Fin 1) d) *ᵥ (T u) = 1 by
      ext; simp [this, mulVec_one]
    ext
    simp_rw [mulVec, Pi.one_apply, ← hd, dotProduct, replicateRow_apply, mul_comm]
  use (toLin' B) u
  rw [← toLin'_toMatrix' T]
  have this A : (T.toMatrix' * A) = (f A * T.toMatrix') :=
    mat_T_mul f.toAlgHom.toNonUnitalAlgHom y z A
  simp_rw [toLin'_apply, mulVec_mulVec, this, ← mulVec_mulVec,
    ← toLin'_apply (LinearMap.toMatrix' T), toLin'_toMatrix']
  exact hB

section Examples

/-- The matrix [a, -b; b, a] (inspired by multiplication by a complex number); it is an element of
$GL_2(R)$ if `a ^ 2 + b ^ 2` is nonzero. -/
@[simps! -fullyApplied val]
def planeConformalMatrix {R} [Field R] (a b : R) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    Matrix.GeneralLinearGroup (Fin 2) R :=
  GeneralLinearGroup.mkOfDetNeZero !![a, -b; b, a] (by simpa [det_fin_two, sq] using hab)

/- TODO: Add Iwasawa matrices `n_x=!![1,x; 0,1]`, `a_t=!![exp(t/2),0;0,exp(-t/2)]` and
  `k_θ=!![cos θ, sin θ; -sin θ, cos θ]`
-/
end Examples

end Matrix
