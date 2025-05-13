/-
Copyright (c) 2025 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # Continuity of the continuous functional calculus in each variable

The continuous functional calculus is a map which takes a pair `a : A` (`A` is a C⋆-algebra) and
a function `f : C(spectrum R a, R)` where `a` satisfies some predicate `p`, depending on `R` and
returns another element of the algebra `A`. This is the map `cfcHom`. The class
`ContinuousFunctionalCalculus` declares that `cfcHom` is a continuous map from `C(spectrum R a, R)`
to `A`. However, users generally interact with the continuous functional calculus through `cfc`,
which operates on bare functions `f : R → R` instead and takes a junk value when `f` is not
continuous on the spectrum of `a`.  In this file we provide some lemma concerning the continuity
of `cfc`, subject to natural hypotheses.

However, the continuous functional calculus is *also* continuous in the variable `a`, but there
are some conditions that must be satisfied. In particular, given a function `f : R → R` the map
`a ↦ cfc f a` is continuous so long as `a` varies over a collection of elements satisfying the
predicate `p` and their spectra are collectively contained in a compact set on which `f` is
continuous. Moreover, it is required that the continuous functional calculus be the isometric
variant.

Finally, all of this is developed for both the unital and non-unital functional calculi.

# To do

+ Get a version with joint continuity in both variables.

-/

open Filter Topology

section Unital

section Left

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
to `cfc f a`. -/
theorem tendsto_cfc_fun {l : Filter X} (F : X → R → R) (f : R → R) (a : A)
    (h_tendsto : TendstoUniformlyOn F f l (spectrum R a))
    (hF : ∀ x, ContinuousOn (F x) (spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    Tendsto (fun x ↦ cfc (F x) a) l (𝓝 (cfc f a)) := by
  open scoped ContinuousFunctionalCalculus in
  by_cases ha : p a
  · conv =>
      enter [1, x]
      rw [cfc_apply (hf := hF x)]
    rw [cfc_apply ..]
    apply cfcHom_continuous _ |>.tendsto _ |>.comp
    rwa [hf.tendsto_restrict_iff_tendstoUniformlyOn hF]
  · simpa [cfc_apply_of_not_predicate a ha] using tendsto_const_nhds

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `a`,
and each `f x` is continuous on the spectrum of `a`, then `fun x ↦ cfc (f x) a` is
continuous at `x₀`. -/
theorem continuousAt_cfc_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (x₀ : X) (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (spectrum R a))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    ContinuousAt (fun x ↦ cfc (f x) a) x₀ :=
  tendsto_cfc_fun f (f x₀) a h_tendsto hf (hf x₀)

open UniformOnFun in
/-- If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → R`,
and each `f` is continuous on the spectrum, then `x ↦ cfc (f x) a` is continuous. -/
theorem continuous_cfc_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {spectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    Continuous fun x ↦ cfc (f x) a := by
  rw [continuous_iff_continuousAt] at h_cont ⊢
  simp only [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn,
    Set.mem_singleton_iff, toFun_ofFun, forall_eq] at h_cont
  exact fun x ↦ continuousAt_cfc_fun f a x (h_cont x)

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    [ContinuousStar A]

/-- `cfcHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`. -/
theorem continuous_cfcHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜))
    (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcHomSuperset (ha' x) (ha x) f) := by
  open scoped ContinuousFunctionalCalculus in
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMap.induction_on_of_compact with
  | const r =>
    have : ContinuousMap.const s r = algebraMap 𝕜 C(s, 𝕜) r := rfl
    simpa only [this, AlgHomClass.commutes] using continuous_const
  | id =>
    simp only [cfcHomSuperset_id]
    fun_prop
  | star_id =>
    simp only [map_star, cfcHomSuperset_id]
    fun_prop
  | add f g hf hg => simpa using hf.add hg
  | mul f g hf hg => simpa using hf.mul hg
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_setOf_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x ↦ ?_⟩
    rw [← map_sub, cfcHomSuperset_apply]
    rw [isometry_cfcHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcHom (ha' x)))]
    rw [ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

/-- `cfc` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a` varies over
elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`, and the
function `f` is continuous on the spectrum of `a`. -/
theorem continuous_cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  convert continuous_cfcHomSuperset_left hs ⟨_, hf.restrict⟩ a ha_cont ha with x
  rw [cfcHomSuperset_apply, cfc_apply (hf := hf.mono (ha x))]
  congr!

theorem continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f) {a | p a ∧ spectrum 𝕜 a ⊆ s} :=
  continuousOn_iff_continuous_restrict.mpr <|
    continuous_cfc hs f _ continuous_subtype_val (by simp)

end RCLike

section NNReal

variable {X A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousStar A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [IsTopologicalRing A]


open scoped NNReal in
/-- A version of `continuous_cfc` over `ℝ≥0` instead of `RCLike 𝕜`. -/
theorem continuous_cfc_nnreal [TopologicalSpace X] (s : Set ℝ≥0) (hs : IsCompact s) (f : ℝ≥0 → ℝ≥0)
    (hf : ContinuousOn f s := by cfc_cont_tac)
    (a : X → A) (ha_cont : Continuous a) (ha' : ∀ x, 0 ≤ a x) (ha : ∀ x, spectrum ℝ≥0 (a x) ⊆ s) :
    Continuous (fun x ↦ cfc f (a x)) := by
  conv =>
    enter [1, x]
    rw [cfc_nnreal_eq_real]
  simp only [nonneg_iff_isSelfAdjoint_and_spectrumRestricts, forall_and] at ha'
  refine continuous_cfc (hs.image (continuous_algebraMap ℝ≥0 ℝ)) _ _ ha_cont ?hf ?hs
  · intro x
    rw [← ha'.2 x |>.algebraMap_image]
    exact Set.image_mono (ha x)
  · apply NNReal.continuous_coe.comp_continuousOn
    refine hf.comp (by fun_prop) ?_
    rintro - ⟨x, hx, rfl⟩
    simpa

end NNReal

end Right

end Unital

section NonUnital

section Left

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalContinuousFunctionalCalculus R A p]

/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum and map zero to itself, then
`fun x ↦ cfcₙ (F x) a` tends to `cfcₙ f a`. -/
theorem tendsto_cfcₙ_fun {l : Filter X} (F : X → R → R) (f : R → R) (a : A)
    (h_tendsto : TendstoUniformlyOn F f l (quasispectrum R a))
    (hF : ∀ x, ContinuousOn (F x) (quasispectrum R a) := by cfc_cont_tac)
    (hF0 : ∀ x, F x 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x ↦ cfcₙ (F x) a) l (𝓝 (cfcₙ f a)) := by
  open scoped NonUnitalContinuousFunctionalCalculus in
  by_cases ha : p a
  · conv =>
      enter [1, x]
      rw [cfcₙ_apply (hf := hF x)]
    rw [cfcₙ_apply ..]
    apply cfcₙHom_continuous _ |>.tendsto _ |>.comp
    rw [ContinuousMapZero.isEmbedding_toContinuousMap.isInducing.tendsto_nhds_iff]
    exact hf.tendsto_restrict_iff_tendstoUniformlyOn hF |>.mpr h_tendsto
  · simpa [cfcₙ_apply_of_not_predicate a ha] using tendsto_const_nhds

/-- If `f : X → R → R` tends to `f x₀` uniformly (along `𝓝 x₀`) on the spectrum of `a`,
and each `f x` is continuous on the spectrum of `a` and maps zero to itself, then
`fun x ↦ cfcₙ (f x) a` is continuous at `x₀`. -/
theorem continuousAt_cfcₙ_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (x₀ : X) (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (quasispectrum R a))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x ↦ cfcₙ (f x) a) x₀ :=
  tendsto_cfcₙ_fun f (f x₀) a h_tendsto hf hf0 (hf x₀) (hf0 x₀)

open UniformOnFun in
/-- If `f : X → R → R` is continuous in the topology on `X → R →ᵤ[{spectrum R a}] → R`,
and each `f` is continuous on the spectrum and maps zero to itself, then
`x ↦ cfcₙ (f x) a` is continuous. -/
theorem continuous_cfcₙ_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {quasispectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) :
    Continuous fun x ↦ cfcₙ (f x) a := by
  rw [continuous_iff_continuousAt] at h_cont ⊢
  simp only [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn,
    Set.mem_singleton_iff, toFun_ofFun, forall_eq] at h_cont
  exact fun x ↦ continuousAt_cfcₙ_fun f a x (h_cont x)

end Left

section Right
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

open scoped NonUnitalContinuousFunctionalCalculus ContinuousMapZero in
/-- `cfcₙHomSuperset` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a`
varies over elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`. -/
theorem continuous_cfcₙHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) [hs0 : Fact (0 ∈ s)]
    (f : C(s, 𝕜)₀) (a : X → A) (ha_cont : Continuous a)
    (ha : ∀ x, quasispectrum 𝕜 (a x) ⊆ s) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙHomSuperset (ha' x) (ha x) f) := by
  have : CompactSpace s := by rwa [isCompact_iff_compactSpace] at hs
  induction f using ContinuousMapZero.induction_on_of_compact with
  | h0 => rfl
  | zero => simpa [map_zero] using continuous_const
  | id => simpa only [cfcₙHomSuperset_id']
  | star_id => simp only [map_star, cfcₙHomSuperset_id']; fun_prop
  | add f g hf hg => simpa only [map_add] using hf.add hg
  | mul f g hf hg => simpa only [map_mul] using hf.mul hg
  | smul r f hf => simpa only [map_smul] using hf.const_smul r
  | frequently f hf =>
    apply continuous_of_uniform_approx_of_continuous
    rw [Metric.uniformity_basis_dist_le.forall_iff (by aesop)]
    intro ε hε
    simp only [Set.mem_setOf_eq, dist_eq_norm]
    obtain ⟨g, hg, g_cont⟩ := frequently_iff.mp hf (Metric.closedBall_mem_nhds f hε)
    simp only [Metric.mem_closedBall, dist_comm g, dist_eq_norm] at hg
    refine ⟨_, g_cont, fun x ↦ ?_⟩
    rw [← map_sub, cfcₙHomSuperset_apply]
    rw [isometry_cfcₙHom (R := 𝕜) _ (ha' x) |>.norm_map_of_map_zero (map_zero (cfcₙHom (ha' x)))]
    rw [ContinuousMapZero.norm_def, ContinuousMap.norm_le _ hε.le] at hg ⊢
    aesop

/-- `cfcₙ` is continuous in the variable `a : A` when `s : Set 𝕜` is compact and `a` varies over
elements whose spectrum is contained in `s`, all of which satisfy the predicate `p`, and the
function `f` is continuous on the spectrum of `a` and maps zero to itself. -/
theorem continuous_cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (hs0 : 0 ∈ s)
    (f : 𝕜 → 𝕜) (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, quasispectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  convert continuous_cfcₙHomSuperset_left hs (hs0 := ⟨hs0⟩) ⟨⟨_, hf.restrict⟩, hf0⟩ a ha_cont ha
  rw [cfcₙHomSuperset_apply, cfcₙ_apply (hf := hf.mono (ha _))]
  congr!

theorem continuousOn_cfcₙ {s : Set 𝕜} (hs : IsCompact s) (hs0 : 0 ∈ s) (f : 𝕜 → 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    ContinuousOn (cfcₙ f · : A → A) {a | p a ∧ quasispectrum 𝕜 a ⊆ s} :=
  continuousOn_iff_continuous_restrict.mpr <|
    continuous_cfcₙ hs hs0 f _ continuous_subtype_val (by simp)

end RCLike

section NNReal

variable {X A : Type*} [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [IsTopologicalRing A]

open scoped NNReal in
/-- A version of `continuous_cfcₙ` over `ℝ≥0` instead of `RCLike 𝕜`. -/
theorem continuous_cfcₙ_nnreal [TopologicalSpace X] (s : Set ℝ≥0)
    (hs : IsCompact s) (hs0 : 0 ∈ s) (f : ℝ≥0 → ℝ≥0) (a : X → A) (ha_cont : Continuous a)
    (ha' : ∀ x, 0 ≤ a x) (ha : ∀ x, quasispectrum ℝ≥0 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  conv =>
    enter [1, x]
    rw [cfcₙ_nnreal_eq_real]
  simp only [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, forall_and] at ha'
  refine continuous_cfcₙ (hs.image (continuous_algebraMap ℝ≥0 ℝ))
    ⟨0, hs0, map_zero _⟩ _ _ ha_cont ?hf ?hs
  · intro x
    rw [← ha'.2 x |>.algebraMap_image]
    exact Set.image_mono (ha x)
  · apply NNReal.continuous_coe.comp_continuousOn
    refine hf.comp (by fun_prop) ?_
    rintro - ⟨x, hx, rfl⟩
    simpa

end NNReal

end Right

end NonUnital
