/-
Copyright (c) 2026 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Ramabadran, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.Distribution.TemperedDistribution

/-!
# Maps between test functions, Schwartz functions, tempered distributions, and distributions

This file defines the canonical continuous linear map from test functions to Schwartz functions,
and the induced (linear) restriction map from tempered distributions to distributions. More
explicitly, a smooth compactly supported function is automatically a Schwartz function, and we show
that this assignment is linear and continuous (with respect to the natural locally
convex topologies.)

Then, a tempered distribution can be restricted to a distribution by
precomposing with the above map, and we show that this assignment is linear. But we don't
show continuity since the source and target dual spaces use different topologies.

## Main definitions

- `ContDiffMapSupportedIn.toSchwartzMapCLM`: the local map `𝓓_{K}(E, F) →L[𝕜] 𝓢(E, F)`.
- `TestFunction.toSchwartzMapCLM`: the canonical continuous linear map `𝓓(Ω, F) →L[𝕜] 𝓢(E, F)`.
- `TestFunction.toComplexSchwartzMapCLM`: the canonical continuous linear map
  `𝓓(Ω, ℝ) →L[ℝ] 𝓢(E, ℂ)`, used to let tempered distributions act on real-valued test functions.
- `TemperedDistribution.toDistributionLM`: the induced linear map `𝓢'(E, F) →ₗ[ℂ] 𝓓'(Ω, F)`.

## Tags

distributions, test function, Schwartz space, tempered distributions
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

/-- Main continuity estimate: each Schwartz seminorm is bounded by a defining seminorm on `𝓓_{K}`. -/
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
      simpa [toSchwartzMap] using f.iteratedFDeriv_zero_on_compl hx
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
    (schwartz_withSeminorms 𝕜 E F) _ (.of_real fun ⟨k, n⟩ ↦ ⟨{n}, powNormBound K k, fun f ↦ ?_⟩)
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

section ToComplexSchwartzMap

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-- Map from ℝ-valued test functions on `Ω` to ℂ-valued Schwartz functions.
This allows tempered distributions to act on ℝ-valued test functions. -/
noncomputable def toComplexSchwartzMapCLM : 𝓓(Ω, ℝ) →L[ℝ] 𝓢(E, ℂ) :=
  (toSchwartzMapCLM ℝ).comp (postcompCLM Complex.ofRealCLM)

@[simp]
theorem toComplexSchwartzMapCLM_apply (f : 𝓓(Ω, ℝ)) (x : E) :
    toComplexSchwartzMapCLM f x = Complex.ofReal (f x) :=
  rfl

private theorem toComplexSchwartzMapCLM_real_smul (c : ℝ) (φ : 𝓓(Ω, ℝ)) :
    toComplexSchwartzMapCLM (c • φ) = (c : ℂ) • toComplexSchwartzMapCLM φ := by
  simp

end ToComplexSchwartzMap

end TestFunction

namespace TemperedDistribution

section ToDistribution

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

/--
A tempered distribution defines a continuous ℝ-linear map on ℝ-valued test functions.
We do this by precomposing the tempered distribution with `toComplexSchwartzMapCLM`.

Morally, this is just `T.restrictScalars ℝ ∘L TestFunction.toComplexSchwartzMapCLM`, but
since `𝓢'(E, F)` is equipped with the topology of pointwise convergence, we instead build it by
hand.
-/
@[simps]
noncomputable def restrictToTestFunctionsCLM (T : 𝓢'(E, F)) : 𝓓(Ω, ℝ) →L[ℝ] F where
  toFun := fun φ ↦ T (TestFunction.toComplexSchwartzMapCLM φ)
  map_add' := by simp
  map_smul' c φ := by
    rw [TestFunction.toComplexSchwartzMapCLM_real_smul c φ, RingHom.id_apply,
      ← algebraMap_smul (A := ℂ) c (T _)]
    exact T.map_smul (c : ℂ) _


/--
The distribution associated to a tempered distribution by restricting
to ℝ-valued test functions, repackaging `restrictToTestFunctionsCLM`.
-/
noncomputable def toDistribution (T : 𝓢'(E, F)) : 𝓓'(Ω, F) :=
  (restrictToTestFunctionsCLM T).toUniformConvergenceCLM _ _ _

@[simp]
theorem toDistribution_apply (T : 𝓢'(E, F)) (φ : 𝓓(Ω, ℝ)) :
    toDistribution T φ = T (TestFunction.toComplexSchwartzMapCLM φ) :=
  rfl

/--
Linear restriction map from tempered distributions to distributions.
We send a tempered distribution `T` to the distribution
`φ ↦ T (TestFunction.toComplexSchwartzMapCLM φ)`.
-/
def toDistributionLM : 𝓢'(E, F) →ₗ[ℂ] 𝓓'(Ω, F) where
  toFun := toDistribution
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

@[simp]
theorem toDistributionLM_apply_apply (T : 𝓢'(E, F)) (φ : 𝓓(Ω, ℝ)) :
    toDistributionLM (E := E) (Ω := Ω) T φ =
      T ((TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω)) φ) :=
  rfl

end ToDistribution

end TemperedDistribution
