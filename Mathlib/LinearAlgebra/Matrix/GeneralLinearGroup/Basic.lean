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

open Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]

private def NonUnitalAlgHom.apply_vecMulVec_mulVec [Semiring R]
    (f : (Matrix n n R) →ₙₐ[R] Matrix n n R) (y z : n → R) :
    (n → R) →ₗ[R] n → R where
  toFun x := f (vecMulVec x y) *ᵥ z
  map_add' w p := by simp_rw [add_vecMulVec, map_add, add_mulVec]
  map_smul' w r := by simp_rw [smul_vecMulVec, map_smul, smul_mulVec_assoc, RingHom.id_apply]

private theorem NonUnitalAlgHom.apply_vecMulVec_mulVec_mul_comm [CommSemiring R]
    (f : Matrix n n R →ₙₐ[R] Matrix n n R) (y z : n → R) (A : Matrix n n R) :
    (f.apply_vecMulVec_mulVec y z).toMatrix' * A
    = f A * (f.apply_vecMulVec_mulVec y z).toMatrix' := by
  apply_fun toLin' using toLin'.injective
  rw [LinearMap.ext_iff]
  intro x
  let T := f.apply_vecMulVec_mulVec y z
  calc
    ((LinearMap.toMatrix' T) * A) *ᵥ x = T (A *ᵥ x) :=
      by ext; rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    _ = (f (vecMulVec (A *ᵥ x) y)) *ᵥ z := by simp [T, NonUnitalAlgHom.apply_vecMulVec_mulVec]
    _ = (f (A * vecMulVec x y)) *ᵥ z := by
      simp_rw [vecMulVec_eq (Fin 1), replicateCol_mulVec, ← Matrix.mul_assoc]
    _ = (f A * f (vecMulVec x y)) *ᵥ z := by simp_rw [map_mul]
    _ = (f A) *ᵥ (T x) := by
      simp [← mulVec_mulVec]; rfl
    _ = (f A * (LinearMap.toMatrix' T)) *ᵥ x := by
      simp_rw [← mulVec_mulVec, ← toLin'_apply (LinearMap.toMatrix' T), toLin'_toMatrix']

theorem AlgEquiv.exists_generalLinearGroup_eq_mulLeftRight_inv
    [Field R] (f : Matrix n n R ≃ₐ[R] Matrix n n R) :
    ∃ T : GL n R, ⇑f = (LinearMap.mulLeftRight R (↑T, ↑T⁻¹)) := by
  by_cases hn : IsEmpty n
  · use 1
    ext a i _
    exact isEmpty_iff.mp hn i |>.elim
  simp_rw [funext_iff, LinearMap.mulLeftRight_apply, @eq_comm _ (f _),
    Units.mul_inv_eq_iff_eq_mul, @eq_comm _ _ (f _ * _)]
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
    simp [← ext_iff, vecMulVec_apply]
    exact ⟨Function.ne_iff.mp hu, Function.ne_iff.mp hy⟩
  obtain ⟨z, hz⟩ := this
  let T := f.toAlgHom.toNonUnitalAlgHom.apply_vecMulVec_mulVec y z
  let M := T.toMatrix'
  suffices hM : IsUnit M by
    use hM.unit
    intro A
    simp [M]
    exact f.toAlgHom.toNonUnitalAlgHom.apply_vecMulVec_mulVec_mul_comm y z A |>.symm
  rw [← isUnit_toLin'_iff]
  simp_rw [M, toLin'_toMatrix', LinearMap.isUnit_iff_range_eq_top, LinearMap.range_eq_top]
  intro w
  have hi : T u ≠ 0 := by simpa [T, NonUnitalAlgHom.apply_vecMulVec_mulVec]
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
    f.toAlgHom.toNonUnitalAlgHom.apply_vecMulVec_mulVec_mul_comm y z A
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
