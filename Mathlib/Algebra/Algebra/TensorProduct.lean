/-
Copyright (c) 2026 Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonid Ryvkin
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Construction of the tensor product over an algebra from the tensor product over its ring

If `A` is an `R`-algebra, then the tensor product `M ⊗[A] N` of two modules `M, N` over `A`
can be constructed as a quotient of `M ⊗[R] N` by the span of
`{(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)}`.
In other words `(mapOfCompatibleSMul' A R M N) : M ⊗[A] N →ₗ[A] M ⊗[R] N` is surjective and its
kernel is the span of `{(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)}`.

-/

@[expose] public section

namespace TensorProduct

open Function Submodule TensorProduct

variable
  {R : Type*} [CommSemiring R]
  {A : Type*} [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  {N : Type*} [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

lemma surjective_mapOfCompatibleSMul' : Surjective (mapOfCompatibleSMul' A R M N) := by
  exact mapOfCompatibleSMul_surjective A R M N

lemma ker_mapOfCompatibleSMul' :
    (mapOfCompatibleSMul' A R M N).ker =
      span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)} := by
  refine Eq.symm (span_eq_of_le (mapOfCompatibleSMul' A R M N).ker ?_ ?_)
  · rintro x ⟨a, m, n, h⟩
    simp [← h, smul_tmul]
  · let S := span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)}
    let F : M ⊗[A] N →ₗ[A]  (M ⊗[R] N) ⧸ S := TensorProduct.lift ({
      toFun m := {
        toFun n :  (M ⊗[R] N) ⧸ S := S.mkQ (m⊗ₜn)
        map_add' _ _ := by simp [tmul_add]
        map_smul' (a : A) n := by
          symm
          simp_rw [Submodule.mkQ_apply, ←Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
          exact Submodule.subset_span ⟨a, m, n, rfl⟩ }
      map_add' _ _ := by ext _; simp [add_tmul]
      map_smul' _ _ := by simp; rfl })
    have h : F ∘ₗ(mapOfCompatibleSMul' A R M N) = S.mkQ := by
      ext m n
      simp [mkQ_apply, S, F]
    change (mapOfCompatibleSMul' A R M N).ker ≤ S
    rw [← ker_mkQ S, ← h]
    exact LinearMap.ker_le_ker_comp (mapOfCompatibleSMul' A R M N) F

end TensorProduct
end
