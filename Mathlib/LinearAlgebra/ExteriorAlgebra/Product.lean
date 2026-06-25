/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal

/-!

# Exterior algebra of product module

In this file, we proved the equivelence between exterior algebra of product module and
graded tensor product of the two exterior algebras.

-/

@[expose] public section

universe u

variable (R : Type u) [CommRing R]

variable (M N : Type*) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

open TensorProduct

namespace ExteriorAlgebra

/-- The auxiliary linear map for lifting to a morphism from `ExteriorAlgebra R (M × N)`. -/
noncomputable def prodEquivTensorForwardAux :
    (M × N) →ₗ[R] ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) :=
  (GradedTensorProduct.includeLeft _ _).toLinearMap.comp ((ι R).comp (LinearMap.fst R M N)) +
    (GradedTensorProduct.includeRight _ _).toLinearMap.comp ((ι R).comp (LinearMap.snd R M N))

variable {M N} in
lemma prodEquivTensorForwardAux_apply_mul (m : M × N) :
    (prodEquivTensorForwardAux R M N) m * (prodEquivTensorForwardAux R M N) m = 0 := by
  let a : ⋀[R]^1 M := ⟨ι R m.1, by simp⟩
  let b : ⋀[R]^1 N := ⟨ι R m.2, by simp⟩
  have h : prodEquivTensorForwardAux R M N m = a.val ᵍ⊗ₜ[R] 1 + 1 ᵍ⊗ₜ[R] b.val := rfl
  rw [h, add_mul, mul_add, mul_add, GradedTensorProduct.tmul_one_mul_coe_tmul,
    GradedTensorProduct.tmul_one_mul_one_tmul, GradedTensorProduct.tmul_coe_mul_coe_tmul,
    GradedTensorProduct.tmul_coe_mul_one_tmul]
  simp [a, b, mul_one, one_mul, uzpow_one, Units.neg_smul, one_smul, GradedTensorProduct.tmul,
    TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero]

/-- The forward function for the equivalence between `ExteriorAlgebra R (M × N)` and
graded tensor product of the two exterior algebras, lift from `(x, y) ↦ x ⊗ 1 + 1 ⊗ y`. -/
noncomputable def prodEquivTensorForward :
    ExteriorAlgebra R (M × N) →ₐ[R] ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) :=
  ExteriorAlgebra.lift R ⟨prodEquivTensorForwardAux R M N, prodEquivTensorForwardAux_apply_mul R⟩

lemma prodEquivTensorForward_ι_apply (m : M × N) :
    prodEquivTensorForward R M N (ι R m) = ι R m.1 ᵍ⊗ₜ[R] 1 + 1 ᵍ⊗ₜ[R] ι R m.2 := by
  simp [prodEquivTensorForward, lift_ι_apply, prodEquivTensorForwardAux]

variable {M N} in
lemma map_inl_inr_anticomm (i j : ℕ) (a : ⋀[R]^i M) (b : ⋀[R]^j N) :
    (map (LinearMap.inl R M N)) a * (map (LinearMap.inr R M N)) b =
      (-1) ^ (j * i) • ((map (LinearMap.inr R M N)) b * (map (LinearMap.inl R M N)) a) := by
  have amem : a.1 ∈ ⋀[R]^i M := a.2
  have bmem : b.1 ∈ ⋀[R]^j N := b.2
  rw [← (Submodule.ext_iff.mp (ιMulti_span_fixedDegree R _))] at amem bmem
  refine Submodule.span_induction₂ (p := fun x y hx hy ↦
    (map (LinearMap.inl R M N)) x * (map (LinearMap.inr R M N)) y =
      (-1) ^ (j * i) • ((map (LinearMap.inr R M N)) y * (map (LinearMap.inl R M N)) x))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ amem bmem
  · rintro x y ⟨mx, rfl⟩ ⟨my, rfl⟩
    rw [map_apply_ιMulti, map_apply_ιMulti]
    exact ιMulti_mul_ιMulti_anticomm R _ _
  all_goals simp +contextual [add_mul, mul_add]

/-- The inverse function for the equivalence between `ExteriorAlgebra R (M × N)` and
graded tensor product of the two exterior algebras, lift form universal property. -/
noncomputable def prodEquivTensorInverse :
    ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) →ₐ[R] ExteriorAlgebra R (M × N) :=
  GradedTensorProduct.lift _ _ (ExteriorAlgebra.map (LinearMap.inl R M N))
    (ExteriorAlgebra.map (LinearMap.inr R M N)) (map_inl_inr_anticomm R)

lemma prodEquivTensorInverse_ι_tmul_one (m : M) :
    prodEquivTensorInverse R M N (ι R m ᵍ⊗ₜ[R] 1) = ι R (m, 0) := by
  simp [prodEquivTensorInverse]

lemma prodEquivTensorInverse_one_tmul_ι (n : N) :
    prodEquivTensorInverse R M N (1 ᵍ⊗ₜ[R] ι R n) = ι R (0, n) := by
  simp [prodEquivTensorInverse]

attribute [local simp] prodEquivTensorForward_ι_apply
attribute [local simp] prodEquivTensorInverse_ι_tmul_one prodEquivTensorInverse_one_tmul_ι

lemma prodEquivTensor_inverse_comp_forward :
    (prodEquivTensorInverse R M N).comp (prodEquivTensorForward R M N) = AlgHom.id R _ := by
  ext m
  · simp [prodEquivTensorForward_ι_apply, GradedTensorProduct.tmul]
  · simp [prodEquivTensorForward_ι_apply, GradedTensorProduct.tmul]

lemma prodEquivTensor_forward_comp_inverse :
    (prodEquivTensorForward R M N).comp (prodEquivTensorInverse R M N) = AlgHom.id R _ := by
  ext
  · simp
  · simp

/-- The equivalence `ExteriorAlgebra R (M × N) ≃ₐ[R] ExteriorAlgebra R M ⊗ ExteriorAlgebra R N`,
with the right side given graded multiplication. -/
noncomputable def prodEquivTensor :
    ExteriorAlgebra R (M × N) ≃ₐ[R] ((fun (i : ℕ) => ⋀[R]^i M) ᵍ⊗[R] (fun (i : ℕ) => ⋀[R]^i N)) :=
  AlgEquiv.ofAlgHom (prodEquivTensorForward R M N) (prodEquivTensorInverse R M N)
    (prodEquivTensor_forward_comp_inverse R M N) (prodEquivTensor_inverse_comp_forward R M N)

lemma prodEquivTensor_symm_apply_tmul_ιMulti (i j : ℕ) (m : Fin i → M) (n : Fin j → N) :
    (prodEquivTensor R M N).symm (ιMulti R i m ᵍ⊗ₜ[R] ιMulti R j n) =
      ιMulti R (i + j) (Fin.append (LinearMap.inl R M N ∘ m) (LinearMap.inr R M N ∘ n)) := by
  simp [prodEquivTensor, prodEquivTensorInverse, ExteriorAlgebra.ιMulti_mul_ιMulti]

lemma prodEquivTensor_symm_tmul (a : ExteriorAlgebra R M) (b : ExteriorAlgebra R N) :
    (prodEquivTensor R M N).symm (a ᵍ⊗ₜ[R] b) =
      map (LinearMap.inl R M N) a * map (LinearMap.inr R M N) b :=
  rfl

end ExteriorAlgebra
