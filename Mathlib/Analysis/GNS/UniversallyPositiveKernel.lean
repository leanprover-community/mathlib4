/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Universally positive kernels and their GNS construction

-/

section MoveMe

section Bilin

variable {ι κ R S T E F G : Type*} [CommRing R] [CommRing S] [CommRing T]
  [AddCommGroup E] [AddCommGroup F] [AddCommGroup G]
  [Module R E] [Module S F] [Module T G]
  {σ : R →+* T} {τ : S →+* T}

/-- This is a temporary workaround for the fact that `Finsupp.lsum` doesn't support
seminilear maps. -/
def Finsupp.slsum (φ : ι → E →ₛₗ[σ] G) :
    (ι →₀ E) →ₛₗ[σ] G where
  toFun := fun d => d.sum fun i => φ i
  map_add' := (liftAddHom (α := ι) (M := E) (N := G) fun x => (φ x).toAddMonoidHom).map_add
  map_smul' := fun c f => by simp [sum_smul_index', smul_sum]

def Finsupp.liftBilin (φ : ι → κ → E →ₛₗ[σ] F →ₛₗ[τ] G) :
    (ι →₀ E) →ₛₗ[σ] (κ →₀ F) →ₛₗ[τ] G :=
  Finsupp.slsum fun i ↦ .flip <| Finsupp.slsum (LinearMap.flip ∘ φ i)

end Bilin

end MoveMe

variable {𝕜 X E F : Type*} [RCLike 𝕜] [TopologicalSpace X]
variable [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

section Bilin

open scoped ComplexOrder

variable (𝕜 X E)
structure UniversallyPositiveBilinKernel : Type _ where
  toFun : X → X → E →L⋆[𝕜] E →L[𝕜] 𝕜
  continuous : Continuous fun xy : X × X ↦ toFun xy.1 xy.2
  positive : ∀ c : X →₀ E, 0 ≤ Finsupp.liftBilin
    (fun x y ↦ ContinuousLinearMap.coeLM 𝕜 ∘ₛₗ (toFun x y).toLinearMap) c c
  symm : ∀ c d : X →₀ E,
    Finsupp.liftBilin (fun x y ↦ ContinuousLinearMap.coeLM 𝕜 ∘ₛₗ (toFun x y).toLinearMap) c d =
    star (Finsupp.liftBilin (fun x y ↦ ContinuousLinearMap.coeLM 𝕜 ∘ₛₗ (toFun x y).toLinearMap) c d)

end Bilin
