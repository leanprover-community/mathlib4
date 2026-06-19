/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ramabadran, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# The map from test functions to Schwartz functions

This file defines the canonical continuous linear map from test functions to Schwartz functions.
More explicitly, a smooth compactly supported function is automatically a Schwartz function, and we
show that this assignment is linear and continuous with respect to the natural locally convex
topologies.

## Main definitions

- `ContDiffMapSupportedIn.toSchwartzMapCLM`: the local map `𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F)`.
- `TestFunction.toSchwartzMapCLM`: the canonical continuous linear map
  `𝓓(Ω, F) →L[𝕜] 𝓢(E, F)`.

## Tags

distributions, test function, Schwartz space
-/

@[expose] public noncomputable section

open Set TopologicalSpace
open scoped Distributions SchwartzMap

variable {𝕜 E F : Type*}

namespace ContDiffMapSupportedIn

section ToSchwartzMap

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {K : Compacts E}

/-- Smooth compactly-supported functions are Schwartz. -/
def toSchwartzMap (f : 𝓓_{K}(E, F)) : 𝓢(E, F) :=
  f.hasCompactSupport.toSchwartzMap f.contDiff

@[simp]
theorem toSchwartzMap_apply (f : 𝓓_{K}(E, F)) (x : E) :
    toSchwartzMap f x = f x :=
  rfl

/-- A nonnegative bound for `‖x‖^k` on the compact set `K`. -/
private def powNormBound (K : Compacts E) (k : ℕ) : ℝ :=
  let A : Set ℝ := (fun x : E => ‖x‖ ^ k) '' (K : Set E)
  max (sSup A) 0

omit [NormedSpace ℝ E] in
private theorem norm_pow_le_bound_on_compact (k : ℕ) {x : E} (hx : x ∈ K) :
    ‖x‖ ^ k ≤ powNormBound K k := by
  grw [powNormBound, ← le_max_of_le_left]
  exact le_csSup (K.isCompact.image (by fun_prop)).bddAbove ⟨x, hx, rfl⟩

/-- Main continuity estimate: each Schwartz seminorm is bounded by a defining seminorm on
`𝓓_{K}`. -/
private theorem schwartzSeminorm_le_localSeminorm (k n : ℕ) (f : 𝓓_{K}(E, F)) :
    SchwartzMap.seminorm 𝕜 k n (toSchwartzMap f) ≤
      powNormBound K k * N[𝕜]_{K, n} f := by
  have hbound : 0 ≤ powNormBound K k := le_max_right ..
  refine (toSchwartzMap f).seminorm_le_bound 𝕜 k n (by positivity) fun x ↦ ?_
  by_cases hx : x ∈ K
  · calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖
      _ ≤ powNormBound K k * ‖iteratedFDeriv ℝ n f x‖ := by
        gcongr; exact norm_pow_le_bound_on_compact (K := K) k hx
      _ ≤ powNormBound K k * N[𝕜]_{K, n} f := by
        gcongr; exact norm_iteratedFDeriv_apply_le_seminorm_top 𝕜
  · have hzero : iteratedFDeriv ℝ n (toSchwartzMap f) x = 0 := by
      have hfun : (toSchwartzMap f : E → F) = f := by
        ext y
        exact toSchwartzMap_apply f y
      rw [hfun]
      exact f.iteratedFDeriv_zero_on_compl hx
    simp only [hzero, norm_zero, mul_zero, ge_iff_le]
    positivity

variable (𝕜) in
/-- Local map `𝓓_{K} → 𝓢` is continuous linear map. Continuity via `WithSeminorms`
and previous estimate. -/
noncomputable def toSchwartzMapCLM : 𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F) :=
  .mk { toFun := toSchwartzMap, map_add' _ _ := ?h₁, map_smul' _ _ := ?h₂ } ?h₃
where finally
  case h₁ | h₂ => exact SchwartzMap.ext fun _ ↦ rfl
  refine (ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K).continuous_of_isBounded
    (schwartz_withSeminorms 𝕜 E F) _ (.of_real fun ⟨k, n⟩ ↦
      ⟨{n}, powNormBound K k, fun f ↦ ?_⟩)
  simpa [Finset.sup_singleton, Seminorm.smul_apply] using
    schwartzSeminorm_le_localSeminorm (𝕜 := 𝕜) (K := K) k n f

@[simp]
theorem toSchwartzMapCLM_apply (f : 𝓓_{K}(E, F)) (x : E) :
    toSchwartzMapCLM (𝕜 := 𝕜) f x = f x :=
  rfl

end ToSchwartzMap

end ContDiffMapSupportedIn

namespace TestFunction

section ToSchwartzMap

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

/-- Map from smooth compactly-supported functions to Schwartz functions. -/
def toSchwartzMap (f : 𝓓(Ω, F)) : 𝓢(E, F) :=
  f.hasCompactSupport.toSchwartzMap f.contDiff

@[simp]
theorem toSchwartzMap_apply (f : 𝓓(Ω, F)) (x : E) : toSchwartzMap f x = f x :=
  rfl

variable (𝕜) in
/-- Canonical continuous linear map from test functions to Schwartz functions.
Uses `TestFunction.limitCLM` to glue the local maps from `ContDiffMapSupportedIn`. -/
noncomputable def toSchwartzMapCLM : 𝓓(Ω, F) →L[𝕜] 𝓢(E, F) :=
  TestFunction.limitCLM _ toSchwartzMap
    (fun _ _ => ContDiffMapSupportedIn.toSchwartzMapCLM _)
    (fun _ _ _ => rfl)

@[simp]
theorem toSchwartzMapCLM_apply (f : 𝓓(Ω, F)) (x : E) :
    toSchwartzMapCLM 𝕜 f x = f x :=
  rfl

end ToSchwartzMap

end TestFunction
