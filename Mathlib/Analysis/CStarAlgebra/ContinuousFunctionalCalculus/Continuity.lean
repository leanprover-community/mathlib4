import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.MetricSpace.UniformConvergence

open Filter Topology

section Unital

section Right

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] [ContinuousFunctionalCalculus R A p]

open scoped ContinuousFunctionalCalculus in
/-- If `F : X → R → R` tends to `f : R → R` uniformly on the spectrum of `a`, and all
these functions are continuous on the spectrum, then `fun x ↦ cfc (F x) a` tends
to `cfc f a`. -/
theorem tendsto_cfc_fun {l : Filter X} (F : X → R → R) (f : R → R) (a : A)
    (h_tendsto : TendstoUniformlyOn F f l (spectrum R a))
    (hF : ∀ x, ContinuousOn (F x) (spectrum R a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum R a) := by cfc_cont_tac) :
    Tendsto (fun x ↦ cfc (F x) a) l (𝓝 (cfc f a)) := by
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
and each `f` is continuous on the spectrum, then `-/
theorem continuous_cfc_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {spectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (spectrum R a) := by cfc_cont_tac) :
    Continuous fun x ↦ cfc (f x) a := by
  rw [continuous_iff_continuousAt] at h_cont ⊢
  simp only [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn,
    Set.mem_singleton_iff, toFun_ofFun, forall_eq] at h_cont
  exact fun x ↦ continuousAt_cfc_fun f a x (h_cont x)

end Right

section Left
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [IsometricContinuousFunctionalCalculus 𝕜 A p]
    [ContinuousStar A]

open scoped ContinuousFunctionalCalculus in
theorem continuous_cfcHomSuperset_left
    [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : C(s, 𝕜))
    (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcHomSuperset (ha' x) (ha x) f) := by
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

theorem continuous_cfc [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, spectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfc f (a x)) := by
  convert continuous_cfcHomSuperset_left hs ⟨_, hf.restrict⟩ a ha_cont ha with x
  rw [cfcHomSuperset_apply, cfc_apply (hf := hf.mono (ha x))]
  congr!

theorem continuousOn_cfc {s : Set 𝕜} (hs : IsCompact s) (f : 𝕜 → 𝕜)
    (hf : ContinuousOn f s := by cfc_cont_tac) :
    ContinuousOn (cfc f · : A → A) {a | p a ∧ spectrum 𝕜 a ⊆ s} :=
  continuousOn_iff_continuous_restrict.mpr <|
    continuous_cfc hs f _ continuous_subtype_val (by simp)

end RCLike

section NNReal

variable {X A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [ContinuousStar A] [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A]
    [T2Space A] [IsTopologicalRing A]


attribute [fun_prop] continuous_real_toNNReal

open scoped NNReal in
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

end Left

end Unital

section NonUnital

section Right

variable {X R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R] [Nontrivial R]
    [IsTopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]
    [NonUnitalContinuousFunctionalCalculus R A p]

open scoped NonUnitalContinuousFunctionalCalculus in
theorem tendsto_cfcₙ_fun {l : Filter X} (F : X → R → R) (f : R → R) (a : A)
    (h_tendsto : TendstoUniformlyOn F f l (quasispectrum R a))
    (hF : ∀ x, ContinuousOn (F x) (quasispectrum R a) := by cfc_cont_tac)
    (hF0 : ∀ x, F x 0 = 0 := by cfc_zero_tac)
    (hf : ContinuousOn f (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Tendsto (fun x ↦ cfcₙ (F x) a) l (𝓝 (cfcₙ f a)) := by
  by_cases ha : p a
  · conv =>
      enter [1, x]
      rw [cfcₙ_apply (hf := hF x)]
    rw [cfcₙ_apply ..]
    apply cfcₙHom_continuous _ |>.tendsto _ |>.comp
    rw [ContinuousMapZero.isEmbedding_toContinuousMap.isInducing.tendsto_nhds_iff]
    exact hf.tendsto_restrict_iff_tendstoUniformlyOn hF |>.mpr h_tendsto
  · simpa [cfcₙ_apply_of_not_predicate a ha] using tendsto_const_nhds

theorem continuousAt_cfcₙ_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (x₀ : X) (h_tendsto : TendstoUniformlyOn f (f x₀) (𝓝 x₀) (quasispectrum R a))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) :
    ContinuousAt (fun x ↦ cfcₙ (f x) a) x₀ :=
  tendsto_cfcₙ_fun f (f x₀) a h_tendsto hf hf0 (hf x₀) (hf0 x₀)

open UniformOnFun in
theorem continuous_cfcₙ_fun [TopologicalSpace X] (f : X → R → R) (a : A)
    (h_cont : Continuous (fun x ↦ ofFun {quasispectrum R a} (f x)))
    (hf : ∀ x, ContinuousOn (f x) (quasispectrum R a) := by cfc_cont_tac)
    (hf0 : ∀ x, f x 0 = 0 := by cfc_zero_tac) :
    Continuous fun x ↦ cfcₙ (f x) a := by
  rw [continuous_iff_continuousAt] at h_cont ⊢
  simp only [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn,
    Set.mem_singleton_iff, toFun_ofFun, forall_eq] at h_cont
  exact fun x ↦ continuousAt_cfcₙ_fun f a x (h_cont x)

end Right

section Left
section RCLike

variable {X 𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A]
    [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] [ContinuousStar A]
    [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

/-- not marked as an instance because it would be a bad one in general, but it can
be useful when working with `ContinuousMapZero` and the non-unital continuous
functional calculus. -/
def Set.zeroOffFactMem {X : Type*} [Zero X] (s : Set X) [Fact (0 ∈ s)] :
    Zero s where
  zero := ⟨0, Fact.out⟩

scoped[ContinuousMapZero] attribute [instance] Set.zeroOffFactMem

-- This is super ugly, but it's mainly because we need to refactor
-- `cfcₙHomSuperset` not to use `letI`.
open scoped NonUnitalContinuousFunctionalCalculus ContinuousMapZero in
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

theorem continuous_cfcₙ [TopologicalSpace X] {s : Set 𝕜} (hs : IsCompact s) (hs0 : 0 ∈ s)
    (f : 𝕜 → 𝕜) (a : X → A) (ha_cont : Continuous a) (ha : ∀ x, quasispectrum 𝕜 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha' : ∀ x, p (a x) := by cfc_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  convert continuous_cfcₙHomSuperset_left hs (hs0 := ⟨hs0⟩) ⟨⟨_, hf.restrict⟩, hf0⟩ a ha_cont ha with x
  rw [cfcₙHomSuperset_apply, cfcₙ_apply (hf := hf.mono (ha x))]
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
theorem continuous_cfcₙ_nnreal [TopologicalSpace X] (s : Set ℝ≥0)
    (hs : IsCompact s) (hs0 : 0 ∈ s) (f : ℝ≥0 → ℝ≥0) (a : X → A) (ha_cont : Continuous a)
    (ha' : ∀ x, 0 ≤ a x) (ha : ∀ x, quasispectrum ℝ≥0 (a x) ⊆ s)
    (hf : ContinuousOn f s := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac) :
    Continuous (fun x ↦ cfcₙ f (a x)) := by
  conv =>
    enter [1, x]
    rw [cfcₙ_nnreal_eq_real]
  simp only [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, forall_and] at ha'
  refine continuous_cfcₙ (hs.image (continuous_algebraMap ℝ≥0 ℝ)) ⟨0, hs0, map_zero _⟩ _ _ ha_cont ?hf ?hs
  · intro x
    rw [← ha'.2 x |>.algebraMap_image]
    exact Set.image_mono (ha x)
  · apply NNReal.continuous_coe.comp_continuousOn
    refine hf.comp (by fun_prop) ?_
    rintro - ⟨x, hx, rfl⟩
    simpa

end NNReal

end Left

end NonUnital
