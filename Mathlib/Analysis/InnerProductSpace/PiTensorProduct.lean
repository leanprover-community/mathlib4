/-
Copyright (c) 2026 Gregory J. Loges. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory J. Loges
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!

# Inner product space structure on `PiTensorProduct`

This file provides the inner product space structure on pi tensor products.

For an indexed family `E` of `𝕜`-inner product spaces, the inner product on `⨂[𝕜] i, E i` is the
unique sesquilinear map given by `⟪⨂ₜ[𝕜] i, a i, ⨂ₜ[𝕜] i, b i⟫ = ∏ i, ⟪a i, b i⟫` on pure tensors.

-/

@[expose] public section

namespace PiTensorProduct

open scoped InnerProductSpace TensorProduct

variable {𝕜} [RCLike 𝕜] {ι : Type*} [Fintype ι]
  {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace 𝕜 (E i)]

noncomputable instance instInner : Inner 𝕜 (⨂[𝕜] i, E i) where
  inner x y := ((lift <| mapMultilinear 𝕜 E _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
    (map fun _ ↦ innerₛₗ 𝕜)) x y

lemma inner_def (x y : ⨂[𝕜] i, E i) :
    ⟪x, y⟫_𝕜 = ((lift <| mapMultilinear 𝕜 E _).compr₂ (lift <| .mkPiAlgebra 𝕜 ι 𝕜) ∘ₛₗ
      (map fun _ ↦ innerₛₗ 𝕜)) x y :=
  rfl

variable (𝕜) in
@[simp]
theorem inner_tprod (x y : Π i, E i) : ⟪⨂ₜ[𝕜] i, x i, ⨂ₜ[𝕜] i, y i⟫_𝕜 = ∏ i, ⟪x i, y i⟫_𝕜 := by
  simp [inner_def]

end PiTensorProduct
