/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.LinearAlgebra.Contraction
import Mathlib.Analysis.InnerProductSpace.l2Space

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 F]

open scoped TensorProduct

instance TensorProduct.instInner : Inner 𝕜 (E ⊗[𝕜] F) :=
  ⟨fun x y =>
    LinearMap.mul' 𝕜 𝕜 ((homTensorHomMap 𝕜 _ _ _ _ ((mapₛₗ (innerₛₗ 𝕜) (innerₛₗ 𝕜)) x)) y)⟩

@[simp]
theorem inner_tmul (x x' : E) (y y' : F) :
    inner 𝕜 (x ⊗ₜ[𝕜] y) (x' ⊗ₜ[𝕜] y') = inner 𝕜 x x' * inner 𝕜 y y' := rfl

@[simp]
theorem TensorProduct.inner_add (x y z : E ⊗[𝕜] F) :
    inner 𝕜 x (y + z) = inner 𝕜 x y + inner 𝕜 x z := by
  simp [inner]

@[simp]
theorem TensorProduct.add_inner (x y z : E ⊗[𝕜] F) :
    inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z := by
  simp [inner]

@[simp]
theorem TensorProduct.smul_inner (x y : E ⊗[𝕜] F) (c : 𝕜) :
    inner 𝕜 (c • x) y = starRingEnd 𝕜 c * inner 𝕜 x y := by
  simp [inner]

@[simp]
theorem TensorProduct.inner_smul (x y : E ⊗[𝕜] F) (c : 𝕜) :
    inner 𝕜 x (c • y) = c * inner 𝕜 x y := by
  simp [inner]

theorem TensorProduct.conj_inner (x y : E ⊗[𝕜] F) :
    starRingEnd 𝕜 (inner 𝕜 x y) = inner 𝕜 y x :=
  x.induction_on (by simp only [inner, map_zero, LinearMap.zero_apply])
    (y.induction_on (by simp only [inner, mapₛₗ_tmul, homTensorHomMap_apply, map_zero,
      LinearMap.zero_apply, implies_true]) (fun x y => by simp only [inner_tmul, map_mul,
      inner_conj_symm, implies_true])
    (fun x y hx hy a b => by simp_all only [inner, mapₛₗ_tmul, homTensorHomMap_apply, map_add,
      LinearMap.add_apply]))
    (fun x y hx hy => by simp_all only [inner, map_add, LinearMap.add_apply])

variable [CompleteSpace E] [CompleteSpace F]

theorem TensorProduct.inner_definite (x : E ⊗[𝕜] F) (hx : inner 𝕜 x x = 0) : x = 0 := sorry

theorem TensorProduct.re_inner_self_nonneg (x : E ⊗[𝕜] F) :
    0 ≤ RCLike.re (inner 𝕜 x x) := sorry

noncomputable instance TensorProduct.instNormedAddCommGroup : NormedAddCommGroup (E ⊗[𝕜] F) :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 (E ⊗[𝕜] F) _ _ _
  { conj_inner_symm := fun x y => TensorProduct.conj_inner y x
    add_left := TensorProduct.add_inner
    smul_left := TensorProduct.smul_inner
    definite := TensorProduct.inner_definite
    re_inner_nonneg := TensorProduct.re_inner_self_nonneg }

noncomputable instance TensorProduct.instInnerProductSpace :
    @InnerProductSpace 𝕜 (E ⊗[𝕜] F) _ _ :=
  InnerProductSpace.ofCore _
