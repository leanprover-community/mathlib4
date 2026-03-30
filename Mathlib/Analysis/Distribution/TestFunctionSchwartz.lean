/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ramabadran, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Compactly supported smooth functions as Schwartz functions

This file defines the canonical continuous linear map from test functions to Schwartz functions,
and the induced (linear) restriction map from tempered distributions to distributions.
-/

@[expose] public noncomputable section

open Set TopologicalSpace
open scoped Distributions SchwartzMap

variable {𝕜 E F : Type*}

namespace ContDiffMapSupportedIn

section ToSchwartzMap

-- will need that the scalar actions on F commute
variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
  {K : Compacts E}

/-- Smooth compactly-supported functions are Schwartz. -/
def toSchwartzMap (f : ContDiffMapSupportedIn E F ⊤ K) : 𝓢(E, F) :=
  f.hasCompactSupport.toSchwartzMap f.contDiff

/-- Nonnegative bound for `‖x‖^k` on compact set `K`, will be used later. -/
private def powNormBound (K : Compacts E) (k : ℕ) : ℝ :=
  let A : Set ℝ := (fun x : E => ‖x‖ ^ k) '' (K : Set E)
  max (sSup A) 0

omit [NormedSpace ℝ E] in
private theorem norm_pow_le_powNormBound (k : ℕ) {x : E} (hx : x ∈ K) :
    ‖x‖ ^ k ≤ powNormBound K k := by
  refine (le_csSup
    (IsCompact.bddAbove <|
      K.isCompact.image_of_continuousOn ((continuous_norm.pow k).continuousOn))
    (Set.mem_image_of_mem _ hx)).trans ?_
  rw [powNormBound]
  simp

@[simp]
theorem toSchwartzMap_apply (f : ContDiffMapSupportedIn E F ⊤ K) (x : E) :
    toSchwartzMap f x = f x :=
  rfl

/-- Main continuity estimate: if you fix a Schwartz norm (indexed by k,n) and apply it to f, result is
bounded by one of the defining seminorms on `𝓓_K`.
-/
private theorem seminorm_toSchwartzMap_le (k n : ℕ) (f : ContDiffMapSupportedIn E F ⊤ K) :
    SchwartzMap.seminorm 𝕜 k n (toSchwartzMap f) ≤
      powNormBound K k * N[𝕜]_{K, n} f := by
  have hbound : 0 ≤ powNormBound K k := by
    unfold powNormBound
    simp

  refine SchwartzMap.seminorm_le_bound 𝕜 k n (toSchwartzMap f)
    (mul_nonneg hbound
      (apply_nonneg (ContDiffMapSupportedIn.seminorm 𝕜 E F ⊤ K n) f)) ?_

  intro x
  by_cases hx : x ∈ K
  · have hK : ‖x‖ ^ k ≤ powNormBound K k :=
      norm_pow_le_powNormBound (K := K) k hx
    have hderiv :
        ‖iteratedFDeriv ℝ n f x‖ ≤ N[𝕜]_{K, n} f :=
      norm_iteratedFDeriv_apply_le_seminorm_top (𝕜 := 𝕜) (f := f) (x := x) (i := n)
    calc
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (toSchwartzMap f) x‖
        = ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ := by rfl
      _ ≤ powNormBound K k * ‖iteratedFDeriv ℝ n f x‖ := by
        exact mul_le_mul_of_nonneg_right hK (norm_nonneg _)
      _ ≤ powNormBound K k * N[𝕜]_{K, n} f := by
        exact mul_le_mul_of_nonneg_left hderiv hbound
  · have hzero : iteratedFDeriv ℝ n (toSchwartzMap f) x = 0 := by
      simpa [toSchwartzMap] using f.iteratedFDeriv_zero_on_compl hx
    simpa [hzero] using
      mul_nonneg hbound (apply_nonneg (ContDiffMapSupportedIn.seminorm 𝕜 E F ⊤ K n) f)


/-- Map from smooth functions supported in `K` to Schwartz. -/
noncomputable def toSchwartzMapCLM : ContDiffMapSupportedIn E F ⊤ K →L[𝕜] 𝓢(E, F) where
  toFun := toSchwartzMap
  map_add' f g := by
    ext x
    rfl
  map_smul' c f := by
    ext x
    rfl
  cont := by
    let L : ContDiffMapSupportedIn E F ⊤ K →ₗ[𝕜] 𝓢(E, F) :=
      { toFun := toSchwartzMap
        map_add' := by
          intro f g
          ext x
          rfl
        map_smul' := by
          intro c f
          ext x
          rfl }
    change Continuous L
    refine WithSeminorms.continuous_of_isBounded
      (ContDiffMapSupportedIn.withSeminorms 𝕜 E F ⊤ K)
      (schwartz_withSeminorms 𝕜 E F) _ (.of_real fun m => ?_)
    rcases m with ⟨k, n⟩
    refine ⟨{n}, powNormBound K k, ?_⟩
    intro f
    simpa [Finset.sup_singleton, Seminorm.smul_apply] using
      seminorm_toSchwartzMap_le (𝕜 := 𝕜) (K := K) k n f

@[simp]
theorem toSchwartzMapCLM_apply (f : ContDiffMapSupportedIn E F ⊤ K) (x : E) :
    toSchwartzMapCLM (𝕜 := 𝕜) f x = f x :=
  rfl

end ToSchwartzMap

end ContDiffMapSupportedIn
