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
In other words `(mapOfCompatibleSMul A R A M N) : M ⊗[A] N →ₗ[A] M ⊗[R] N` is surjective and its
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

lemma ker_mapOfCompatibleSMul :
    (mapOfCompatibleSMul A R A M N).ker =
      span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)} := by
  refine (span_eq_of_le (mapOfCompatibleSMul A R A M N).ker ?_ ?_).symm
  · rintro - ⟨a, m, n, rfl⟩
    simp [smul_tmul]
  · let S := span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)}
    let F : M ⊗[A] N →ₗ[A] (M ⊗[R] N) ⧸ S := TensorProduct.lift ({
      toFun m := {
        toFun n := S.mkQ (m ⊗ₜ[R] n)
        map_add' _ _ := by simp [tmul_add]
        map_smul' a n := by
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, eq_comm,
            Submodule.Quotient.eq, RingHom.id_apply]
          exact Submodule.subset_span ⟨a, m, n, rfl⟩ }
      map_add' _ _ := by ext _; simp [add_tmul]
      map_smul' _ _ := by simp; rfl })
    have h : F ∘ₗ mapOfCompatibleSMul A R A M N = S.mkQ := by ext; simp [S, F]
    change (mapOfCompatibleSMul A R A M N).ker ≤ S
    rw [← ker_mkQ S, ← h]
    exact (mapOfCompatibleSMul A R A M N).ker_le_ker_comp F

end TensorProduct
end
