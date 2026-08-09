/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!

# Inner product space structure on `PiTensorProduct`

This file provides the inner product space structure on tensor products of finite families
of inner product spaces.

The inner product on `⨂[𝕜] i, E i`, where `E` is a finite indexed family of `𝕜`-inner product
spaces, is defined by `⟪⨂ₜ[𝕜] i, a i, ⨂ₜ[𝕜] i, b i⟫ = ∏ i, ⟪a i, b i⟫` for pure tensors
and extended by linearity.

## Main definitions:

## TODO:

-/

@[expose] public section

variable {ι} {𝕜 : Type*} [RCLike 𝕜] [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]
variable {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]

open scoped TensorProduct

namespace PiTensorProduct

noncomputable instance instInner : Inner 𝕜 (⨂[𝕜] i, E i) where
  inner x y := ((lift <| mapMultilinear E _ _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
    (map fun _ ↦ innerₛₗ 𝕜)) x y

lemma inner_def (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 x y = ((lift <| mapMultilinear E _ _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
      (map fun _ ↦ innerₛₗ 𝕜)) x y := rfl

variable (𝕜) in
@[simp]
theorem inner_tmul (x y : Π i, E i) :
    inner 𝕜 (⨂ₜ[𝕜] i, x i) (⨂ₜ[𝕜] i, y i) = ∏ i, inner 𝕜 (x i) (y i) := by
  simp [inner_def]

-- This is a helper lemma for showing that this inner product is positive definite
-- and is superceded by `_root_.inner_add_left`.
private lemma inner_add_left (x y z : ⨂[𝕜] i, E i) :
    inner 𝕜 (x + y) z = inner 𝕜 x z + inner 𝕜 y z := by simp [inner_def]

-- This is a helper lemma for showing that this inner product is positive definite
-- and is superceded by `_root_.inner_add_right`.
private lemma inner_add_right (x y z : ⨂[𝕜] i, E i) :
    inner 𝕜 x (y + z) = inner 𝕜 x y + inner 𝕜 x z := by simp [inner_def]

@[simp]
theorem inner_map_map (f : Π i, E i →ₗᵢ[𝕜] F i) (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 (map (fun i ↦ (f i).1) x) (map (fun i ↦ (f i).1) y) = inner 𝕜 x y :=
  x.induction_on
    (y.induction_on (by simp [inner_def]) (by simp_all [inner_add_right]))
    (by simp_all [inner_add_left])

theorem inner_mapIncl_mapIncl (p : Π i, Submodule 𝕜 (E i)) (x y : ⨂[𝕜] i, p i) :
    inner 𝕜 (mapIncl p x) (mapIncl p y) = inner 𝕜 x y :=
  inner_map_map (fun i ↦ (p i).subtypeₗᵢ) x y

@[simp]
theorem inner_of_isEmpty [IsEmpty ι] (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 x y = starRingEnd 𝕜 (isEmptyEquiv ι x) * isEmptyEquiv ι y :=
  x.induction_on
    (y.induction_on (by simp_all [inner_def, mul_comm]) (by simp_all [inner_add_right, mul_add]))
    (by simp_all [inner_add_left, add_mul])

theorem inner_of_subsingleton [Subsingleton ι] (i₀ : ι) (x y : ⨂[𝕜] i, E i) :
    inner 𝕜 x y = inner 𝕜 (subsingletonEquiv i₀ x) (subsingletonEquiv i₀ y) :=
  x.induction_on
    (y.induction_on
      (by simp [inner_def, inner_smul_left, inner_smul_right, Fintype.prod_subsingleton _ i₀])
      (by simp_all [inner_add_right, _root_.inner_add_right]))
    (by simp_all [inner_add_left, _root_.inner_add_left])

end PiTensorProduct
