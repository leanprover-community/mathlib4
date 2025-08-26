/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Ring.Action.ConjAct

/-!
# Basic lemmas about the general linear group $GL(n, R)$

This file lists various basic lemmas about the general linear group $GL(n, R)$. For the definitions,
see `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean`.
-/

namespace Matrix

open Matrix LinearMap

variable {R n : Type*} [Fintype n]

/-- This takes in a non-unital algebra homomorphism `f` and vectors `y, z : n → R`
and constructs a linear operator on `(n → R)` such that `x ↦ f (vecMulVec x y) *ᵥ z`. -/
private def NonUnitalAlgHom.apply_vecMulVec_mulVec [Semiring R]
    (f : Matrix n n R →ₙₐ[R] Matrix n n R) (y z : n → R) :
    (n → R) →ₗ[R] (n → R) :=
  (mulVecBilin R ℕ).flip z ∘ₗ (↑f : Matrix n n R →ₗ[R] Matrix n n R) ∘ₗ (vecMulVecBilin R ℕ).flip y

@[simp]
private theorem NonUnitalAlgHom.apply_vecMulVec_mulVec_apply [Semiring R]
    (f : Matrix n n R →ₙₐ[R] Matrix n n R) (x y z : n → R) :
  f.apply_vecMulVec_mulVec y z x = f (vecMulVec x y) *ᵥ z := rfl

variable [DecidableEq n]

private theorem NonUnitalAlgHom.toMatrix'_apply_vecMulVec_mulVec_mul [CommSemiring R]
    (f : Matrix n n R →ₙₐ[R] Matrix n n R) (y z : n → R) (A : Matrix n n R) :
    (f.apply_vecMulVec_mulVec y z).toMatrix' * A = f A * (f.apply_vecMulVec_mulVec y z).toMatrix' :=
  toLin'.injective <| LinearMap.ext fun x =>
  let T := f.apply_vecMulVec_mulVec y z
  calc
    (T.toMatrix' * A) *ᵥ x = T (A *ᵥ x) := by
      ext; rw [← mulVec_mulVec, LinearMap.toMatrix'_mulVec]
    _ = f (vecMulVec (A *ᵥ x) y) *ᵥ z := by simp [T, NonUnitalAlgHom.apply_vecMulVec_mulVec_apply]
    _ = f (A * vecMulVec x y) *ᵥ z := by
      simp_rw [vecMulVec_eq Unit, replicateCol_mulVec, ← Matrix.mul_assoc]
    _ = (f A * f (vecMulVec x y)) *ᵥ z := by simp_rw [map_mul]
    _ = f A *ᵥ T x := by
      simp only [← mulVec_mulVec]; rfl
    _ = (f A * T.toMatrix') *ᵥ x := by
      simp_rw [← mulVec_mulVec, ← toLin'_apply (LinearMap.toMatrix' T), toLin'_toMatrix']

/-- Given an algebra automorphism `f` on `Matrix n n R`, there exists an invertible matrix `T`
such that `f` is given by `x ↦ T * x * T⁻¹`. -/
theorem AlgEquiv.coe_eq_generalLinearGroup_conjugate [Field R]
    (f : Matrix n n R ≃ₐ[R] Matrix n n R) :
    ∃ T : GL n R, ⇑f = fun x => T * x * ((T⁻¹ : GL n R) : Matrix n n R) := by
  obtain hn | hn := isEmpty_or_nonempty n
  · exact ⟨1, Subsingleton.elim _ _⟩
  simp_rw [funext_iff, @eq_comm _ (f _), Units.mul_inv_eq_iff_eq_mul, @eq_comm _ _ (f _ * _)]
  obtain ⟨u, v, hu, hv⟩ : ∃ u v : n → R, u ≠ 0 ∧ v ≠ 0 := ⟨1, 1, one_ne_zero, one_ne_zero⟩
  obtain ⟨z, hz⟩ : ∃ z : n → R, f (vecMulVec u v) *ᵥ z ≠ 0 := by
    simp_rw [ne_eq, ← not_forall]
    suffices ¬ f (vecMulVec u v) = 0 by
      rwa [← toMatrix'_toLin' (f _), EmbeddingLike.map_eq_zero_iff, LinearMap.ext_iff] at this
    rw [← ne_eq, EmbeddingLike.map_ne_zero_iff]
    simp only [Ne, ← ext_iff, vecMulVec_apply, zero_apply, mul_eq_zero, not_forall, not_or,
      exists_and_left, exists_and_right]
    exact ⟨Function.ne_iff.mp hu, Function.ne_iff.mp hv⟩
  let T := f.toAlgHom.toNonUnitalAlgHom.apply_vecMulVec_mulVec v z
  have this A : T.toMatrix' * A = f A * T.toMatrix' :=
    f.toAlgHom.toNonUnitalAlgHom.toMatrix'_apply_vecMulVec_mulVec_mul v z A
  suffices hM : IsUnit T.toMatrix' from ⟨hM.unit, fun A => this A |>.symm⟩
  simp_rw [← isUnit_toLin'_iff, toLin'_toMatrix', isUnit_iff_range_eq_top, range_eq_top]
  intro w
  obtain ⟨B, hB⟩ : ∃ B : Matrix n n R, f B *ᵥ T u = w := by
    obtain ⟨d, hd⟩ : ∃ d : n → R, T u ⬝ᵥ d = 1 := by
      have hi : T u ≠ 0 := by simpa [T, NonUnitalAlgHom.apply_vecMulVec_mulVec]
      obtain ⟨q, hq⟩ := Function.ne_iff.mp hi
      use Pi.single q (T u q)⁻¹
      rw [dotProduct_single, mul_inv_cancel₀ hq]
    obtain ⟨B, hB⟩ := f.surjective (vecMulVec w d)
    use B
    rw [hB, vecMulVec_mulVec, dotProduct_comm, hd, MulOpposite.op_one, one_smul]
  use B *ᵥ u
  simp_rw [← toMatrix'_mulVec, mulVec_mulVec, this, ← mulVec_mulVec, toMatrix'_mulVec, hB]

/-- Alternate statement of `coe_eq_generalLinearGroup_conjugate`. -/
theorem mulSemiringActionToAlgEquiv_conjAct_surjective [Field R] :
    Function.Surjective (MulSemiringAction.toAlgEquiv (G := ConjAct (GL n R)) R (Matrix n n R)) :=
  fun f => f.coe_eq_generalLinearGroup_conjugate.imp fun _ h => (DFunLike.coe_injective h).symm

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
