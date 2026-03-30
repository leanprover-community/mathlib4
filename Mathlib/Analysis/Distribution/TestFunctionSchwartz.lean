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

- `ContDiffMapSupportedIn.toSchwartzMapCLM`: the local map `𝓓_K(E, F) →L[𝕜] 𝓢(E, F)`.
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
def toSchwartzMap (f : ContDiffMapSupportedIn E F ⊤ K) : 𝓢(E, F) :=
  f.hasCompactSupport.toSchwartzMap f.contDiff

/-- A nonnegative bound for `‖x‖^k` on the compact set `K`. -/
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

/-- Main continuity estimate: each Schwartz seminorm is bounded by a defining seminorm on `𝓓_K`. -/
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


/-- Local map `𝓓_K → 𝓢` is continuous linear map. Continuity via `WithSeminorms`
and previous estimate. -/
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

namespace TestFunction

section ToSchwartzMap

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  [Algebra ℝ 𝕜] [IsScalarTower ℝ 𝕜 F]

/-- Map from smooth compactly-supported functions to Schwartz functions. -/
def toSchwartzMap (f : TestFunction Ω F ⊤) : 𝓢(E, F) :=
  f.hasCompactSupport.toSchwartzMap f.contDiff

@[simp]
theorem toSchwartzMap_apply (f : TestFunction Ω F ⊤) (x : E) : toSchwartzMap f x = f x :=
  rfl

/-- Canonical continuous linear map from test functions to Schwartz functions.
Uses `TestFunction.limitCLM` to glue the local maps from `ContDiffMapSupportedIn`. -/
noncomputable def toSchwartzMapCLM : TestFunction Ω F ⊤ →L[𝕜] 𝓢(E, F) :=
  TestFunction.limitCLM 𝕜
    (TestFunction.toSchwartzMap (E := E) (Ω := Ω) (F := F))
    (fun K _ =>
      ContDiffMapSupportedIn.toSchwartzMapCLM
        (𝕜 := 𝕜) (E := E) (F := F) (K := K))
    (fun _ _ _ => rfl)

@[simp]
theorem toSchwartzMapCLM_apply (f : TestFunction Ω F ⊤) (x : E) :
    toSchwartzMapCLM (𝕜 := 𝕜) f x = f x :=
  rfl

end ToSchwartzMap

section ToComplexSchwartzMap

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

/-- Map from ℝ-valued test functions on `Ω` to ℂ-valued Schwartz functions.
This allows tempered distributions to act on ℝ-valued test functions. -/
noncomputable def toComplexSchwartzMapCLM : TestFunction Ω ℝ ⊤ →L[ℝ] 𝓢(E, ℂ) :=
  (TestFunction.toSchwartzMapCLM (𝕜 := ℝ) (E := E) (Ω := Ω) (F := ℂ)).comp
    (TestFunction.postcompCLM (Ω := Ω) (n := (⊤ : ℕ∞)) (𝕜 := ℝ) Complex.ofRealCLM)

@[simp]
theorem toComplexSchwartzMapCLM_apply (f : TestFunction Ω ℝ ⊤) (x : E) :
    toComplexSchwartzMapCLM (E := E) (Ω := Ω) f x = Complex.ofReal (f x) :=
  rfl

end ToComplexSchwartzMap

end TestFunction

namespace TemperedDistribution

section ToDistribution

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

private theorem toComplexSchwartzMapCLM_real_smul (c : ℝ) (φ : TestFunction Ω ℝ ⊤) :
    TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω) (c • φ) =
      (c : ℂ) • TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω) φ := by
  simp

/--
A tempered distribution defines a continuous ℝ-linear map on ℝ-valued test functions.
We do this by precomposing the tempered distribution with `toComplexSchwartzMapCLM`.
-/
noncomputable def toDistributionCLM (T : 𝓢'(E, F)) : TestFunction Ω ℝ ⊤ →L[ℝ] F :=
  { toFun := fun φ ↦ T (TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω) φ)
    map_add' := by
      simp
    map_smul' := by
      intro c φ
      let ψ := TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω) φ
      rw [toComplexSchwartzMapCLM_real_smul (E := E) (Ω := Ω) c φ]
      change T (c • ψ) = c • T ψ
      rw [← algebraMap_smul (A := ℂ) c (T ψ)]
      exact T.map_smul (c : ℂ) ψ
    cont := by
      exact T.continuous.comp
        (TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω)).continuous
        }

@[simp]
theorem toDistributionCLM_apply (T : 𝓢'(E, F)) (φ : TestFunction Ω ℝ ⊤) :
    toDistributionCLM (E := E) (Ω := Ω) T φ =
      T ((TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω)) φ) :=
  rfl

noncomputable def toDistribution (T : 𝓢'(E, F)) : Distribution Ω F ⊤ :=
  (ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) F
      {s : Set (TestFunction Ω ℝ ⊤) | IsCompact s})
    (toDistributionCLM (E := E) (Ω := Ω) T)

@[simp]
theorem toDistribution_apply (T : 𝓢'(E, F)) (φ : TestFunction Ω ℝ ⊤) :
    toDistribution (E := E) (Ω := Ω) T φ =
      T ((TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω)) φ) :=
  rfl

/--
Linear restriction map from tempered distributions to distributions.
We send a tempered distribution `T` to the distribution
`φ ↦ T (TestFunction.toComplexSchwartzMapCLM φ)`.
-/
def toDistributionLM : 𝓢'(E, F) →ₗ[ℂ] Distribution Ω F ⊤ where
  toFun := toDistribution (E := E) (Ω := Ω)
  map_add' T S := by
    ext φ
    rw [UniformConvergenceCLM.add_apply, toDistribution_apply, toDistribution_apply,
      toDistribution_apply]
    rfl
  map_smul' c T := by
    ext φ
    rw [UniformConvergenceCLM.smul_apply, toDistribution_apply, toDistribution_apply]
    rfl

@[simp]
theorem toDistributionLM_apply_apply (T : 𝓢'(E, F)) (φ : TestFunction Ω ℝ ⊤) :
    toDistributionLM (E := E) (Ω := Ω) T φ =
      T ((TestFunction.toComplexSchwartzMapCLM (E := E) (Ω := Ω)) φ) :=
  rfl

end ToDistribution

end TemperedDistribution
