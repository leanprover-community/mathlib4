/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.UniformSpace.Cauchy

#align_import topology.metric_space.metrizable from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Metrizability of a T₃ topological space with second countable topology

In this file we define metrizable topological spaces, i.e., topological spaces for which there
exists a metric space structure that generates the same topology.

We also show that a T₃ topological space with second countable topology `X` is metrizable.

First we prove that `X` can be embedded into `l^∞`, then use this embedding to pull back the metric
space structure.
-/


open Set Filter Metric

open BoundedContinuousFunction Filter Topology

namespace TopologicalSpace

variable {ι X Y : Type*} {π : ι → Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (π i)]

/-- A topological space is *pseudo metrizable* if there exists a pseudo metric space structure
compatible with the topology. To endow such a space with a compatible distance, use
`letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X`. -/
class PseudoMetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_pseudo_metric : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.pseudo_metrizable_space TopologicalSpace.PseudoMetrizableSpace

instance (priority := 100) _root_.PseudoMetricSpace.toPseudoMetrizableSpace {X : Type*}
    [m : PseudoMetricSpace X] : PseudoMetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩
#align pseudo_metric_space.to_pseudo_metrizable_space PseudoMetricSpace.toPseudoMetrizableSpace

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def pseudoMetrizableSpacePseudoMetric (X : Type*) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.exists_pseudo_metric.choose.replaceTopology h.exists_pseudo_metric.choose_spec.symm
#align topological_space.pseudo_metrizable_space_pseudo_metric TopologicalSpace.pseudoMetrizableSpacePseudoMetric

instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  letI : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  inferInstance
#align topological_space.pseudo_metrizable_space_prod TopologicalSpace.pseudoMetrizableSpace_prod

/-- Given an inducing map of a topological space into a pseudo metrizable space, the source space
is also pseudo metrizable. -/
theorem _root_.Inducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X → Y}
    (hf : Inducing f) : PseudoMetrizableSpace X :=
  letI : PseudoMetricSpace Y := pseudoMetrizableSpacePseudoMetric Y
  ⟨⟨hf.comapPseudoMetricSpace, rfl⟩⟩
#align inducing.pseudo_metrizable_space Inducing.pseudoMetrizableSpace

/-- Every pseudo-metrizable space is first countable. -/
instance (priority := 100) PseudoMetrizableSpace.firstCountableTopology
    [h : PseudoMetrizableSpace X] : TopologicalSpace.FirstCountableTopology X := by
  rcases h with ⟨_, hm⟩
  -- ⊢ FirstCountableTopology X
  rw [← hm]
  -- ⊢ FirstCountableTopology X
  exact @UniformSpace.firstCountableTopology X PseudoMetricSpace.toUniformSpace
    EMetric.instIsCountablyGeneratedUniformity
#align topological_space.pseudo_metrizable_space.first_countable_topology TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology

instance PseudoMetrizableSpace.subtype [PseudoMetrizableSpace X] (s : Set X) :
    PseudoMetrizableSpace s :=
  inducing_subtype_val.pseudoMetrizableSpace
#align topological_space.pseudo_metrizable_space.subtype TopologicalSpace.PseudoMetrizableSpace.subtype

instance pseudoMetrizableSpace_pi [∀ i, PseudoMetrizableSpace (π i)] :
    PseudoMetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  -- ⊢ PseudoMetrizableSpace ((i : ι) → π i)
  letI := fun i => pseudoMetrizableSpacePseudoMetric (π i)
  -- ⊢ PseudoMetrizableSpace ((i : ι) → π i)
  infer_instance
  -- 🎉 no goals
#align topological_space.pseudo_metrizable_space_pi TopologicalSpace.pseudoMetrizableSpace_pi

/-- A topological space is metrizable if there exists a metric space structure compatible with the
topology. To endow such a space with a compatible distance, use
`letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X`. -/
class MetrizableSpace (X : Type*) [t : TopologicalSpace X] : Prop where
  exists_metric : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.metrizable_space TopologicalSpace.MetrizableSpace

instance (priority := 100) _root_.MetricSpace.toMetrizableSpace {X : Type*} [m : MetricSpace X] :
    MetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩
#align metric_space.to_metrizable_space MetricSpace.toMetrizableSpace

instance (priority := 100) MetrizableSpace.toPseudoMetrizableSpace [h : MetrizableSpace X] :
    PseudoMetrizableSpace X :=
  let ⟨m, hm⟩ := h.1
  ⟨⟨m.toPseudoMetricSpace, hm⟩⟩
#align topological_space.metrizable_space.to_pseudo_metrizable_space TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def metrizableSpaceMetric (X : Type*) [TopologicalSpace X] [h : MetrizableSpace X] :
    MetricSpace X :=
  h.exists_metric.choose.replaceTopology h.exists_metric.choose_spec.symm
#align topological_space.metrizable_space_metric TopologicalSpace.metrizableSpaceMetric

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  letI : MetricSpace X := metrizableSpaceMetric X
  inferInstance
#align topological_space.t2_space_of_metrizable_space TopologicalSpace.t2Space_of_metrizableSpace

instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] : MetrizableSpace (X × Y) :=
  letI : MetricSpace X := metrizableSpaceMetric X
  letI : MetricSpace Y := metrizableSpaceMetric Y
  inferInstance
#align topological_space.metrizable_space_prod TopologicalSpace.metrizableSpace_prod

/-- Given an embedding of a topological space into a metrizable space, the source space is also
metrizable. -/
theorem _root_.Embedding.metrizableSpace [MetrizableSpace Y] {f : X → Y} (hf : Embedding f) :
    MetrizableSpace X :=
  letI : MetricSpace Y := metrizableSpaceMetric Y
  ⟨⟨hf.comapMetricSpace f, rfl⟩⟩
#align embedding.metrizable_space Embedding.metrizableSpace

instance MetrizableSpace.subtype [MetrizableSpace X] (s : Set X) : MetrizableSpace s :=
  embedding_subtype_val.metrizableSpace
#align topological_space.metrizable_space.subtype TopologicalSpace.MetrizableSpace.subtype

instance metrizableSpace_pi [∀ i, MetrizableSpace (π i)] : MetrizableSpace (∀ i, π i) := by
  cases nonempty_fintype ι
  -- ⊢ MetrizableSpace ((i : ι) → π i)
  letI := fun i => metrizableSpaceMetric (π i)
  -- ⊢ MetrizableSpace ((i : ι) → π i)
  infer_instance
  -- 🎉 no goals
#align topological_space.metrizable_space_pi TopologicalSpace.metrizableSpace_pi

theorem IsSeparable.secondCountableTopology [PseudoMetrizableSpace X] {s : Set X}
    (hs : IsSeparable s) : SecondCountableTopology s := by
  letI := pseudoMetrizableSpacePseudoMetric X
  -- ⊢ SecondCountableTopology ↑s
  have := hs.separableSpace
  -- ⊢ SecondCountableTopology ↑s
  exact UniformSpace.secondCountable_of_separable s
  -- 🎉 no goals

variable (X)
variable [T3Space X] [SecondCountableTopology X]

/-- A T₃ topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`. -/
theorem exists_embedding_l_infty : ∃ f : X → ℕ →ᵇ ℝ, Embedding f := by
  haveI : NormalSpace X := normalSpaceOfT3SecondCountable X
  -- ⊢ ∃ f, Embedding f
  -- Choose a countable basis, and consider the set `s` of pairs of set `(U, V)` such that `U ∈ B`,
  -- `V ∈ B`, and `closure U ⊆ V`.
  rcases exists_countable_basis X with ⟨B, hBc, -, hB⟩
  -- ⊢ ∃ f, Embedding f
  let s : Set (Set X × Set X) := { UV ∈ B ×ˢ B | closure UV.1 ⊆ UV.2 }
  -- ⊢ ∃ f, Embedding f
  -- `s` is a countable set.
  haveI : Encodable s := ((hBc.prod hBc).mono (inter_subset_left _ _)).toEncodable
  -- ⊢ ∃ f, Embedding f
  -- We don't have the space of bounded (possibly discontinuous) functions, so we equip `s`
  -- with the discrete topology and deal with `s →ᵇ ℝ` instead.
  letI : TopologicalSpace s := ⊥
  -- ⊢ ∃ f, Embedding f
  haveI : DiscreteTopology s := ⟨rfl⟩
  -- ⊢ ∃ f, Embedding f
  rsuffices ⟨f, hf⟩ : ∃ f : X → s →ᵇ ℝ, Embedding f
  -- ⊢ ∃ f, Embedding f
  · exact ⟨fun x => (f x).extend (Encodable.encode' s) 0,
      (BoundedContinuousFunction.isometry_extend (Encodable.encode' s) (0 : ℕ →ᵇ ℝ)).embedding.comp
        hf⟩
  have hd : ∀ UV : s, Disjoint (closure UV.1.1) UV.1.2ᶜ :=
    fun UV => disjoint_compl_right.mono_right (compl_subset_compl.2 UV.2.2)
  -- Choose a sequence of `εₙ > 0`, `n : s`, that is bounded above by `1` and tends to zero
  -- along the `cofinite` filter.
  obtain ⟨ε, ε01, hε⟩ : ∃ ε : s → ℝ, (∀ UV, ε UV ∈ Ioc (0 : ℝ) 1) ∧ Tendsto ε cofinite (𝓝 0) := by
    rcases posSumOfEncodable zero_lt_one s with ⟨ε, ε0, c, hεc, hc1⟩
    refine' ⟨ε, fun UV => ⟨ε0 UV, _⟩, hεc.summable.tendsto_cofinite_zero⟩
    exact (le_hasSum hεc UV fun _ _ => (ε0 _).le).trans hc1
  /- For each `UV = (U, V) ∈ s` we use Urysohn's lemma to choose a function `f UV` that is equal to
    zero on `U` and is equal to `ε UV` on the complement to `V`. -/
  have : ∀ UV : s, ∃ f : C(X, ℝ),
      EqOn f 0 UV.1.1 ∧ EqOn f (fun _ => ε UV) UV.1.2ᶜ ∧ ∀ x, f x ∈ Icc 0 (ε UV) := by
    intro UV
    rcases exists_continuous_zero_one_of_closed isClosed_closure
        (hB.isOpen UV.2.1.2).isClosed_compl (hd UV) with
      ⟨f, hf₀, hf₁, hf01⟩
    exact ⟨ε UV • f, fun x hx => by simp [hf₀ (subset_closure hx)], fun x hx => by simp [hf₁ hx],
      fun x => ⟨mul_nonneg (ε01 _).1.le (hf01 _).1, mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩
  choose f hf0 hfε hf0ε using this
  -- ⊢ ∃ f, Embedding f
  have hf01 : ∀ UV x, f UV x ∈ Icc (0 : ℝ) 1 :=
    fun UV x => Icc_subset_Icc_right (ε01 _).2 (hf0ε _ _)
  -- The embedding is given by `F x UV = f UV x`.
  set F : X → s →ᵇ ℝ := fun x =>
    ⟨⟨fun UV => f UV x, continuous_of_discreteTopology⟩, 1,
      fun UV₁ UV₂ => Real.dist_le_of_mem_Icc_01 (hf01 _ _) (hf01 _ _)⟩
  have hF : ∀ x UV, F x UV = f UV x := fun _ _ => rfl
  -- ⊢ ∃ f, Embedding f
  refine' ⟨F, Embedding.mk' _ (fun x y hxy => _) fun x => le_antisymm _ _⟩
  · /- First we prove that `F` is injective. Indeed, if `F x = F y` and `x ≠ y`, then we can find
    `(U, V) ∈ s` such that `x ∈ U` and `y ∉ V`, hence `F x UV = 0 ≠ ε UV = F y UV`. -/
    by_contra Hne
    -- ⊢ False
    rcases hB.mem_nhds_iff.1 (isOpen_ne.mem_nhds Hne) with ⟨V, hVB, hxV, hVy⟩
    -- ⊢ False
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    -- ⊢ False
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    -- ⊢ False
    apply (ε01 UV).1.ne
    -- ⊢ 0 = ε UV
    calc
      (0 : ℝ) = F x UV := (hf0 UV hxU).symm
      _ = F y UV := by rw [hxy]
      _ = ε UV := hfε UV fun h : y ∈ V => hVy h rfl
  · /- Now we prove that each neighborhood `V` of `x : X` include a preimage of a neighborhood of
    `F x` under `F`. Without loss of generality, `V` belongs to `B`. Choose `U ∈ B` such that
    `x ∈ V` and `closure V ⊆ U`. Then the preimage of the `(ε (U, V))`-neighborhood of `F x`
    is included by `V`. -/
    refine' ((nhds_basis_ball.comap _).le_basis_iff hB.nhds_hasBasis).2 _
    -- ⊢ ∀ (i' : Set X), i' ∈ B ∧ x ∈ i' → ∃ i, 0 < i ∧ F ⁻¹' ball (F x) i ⊆ i'
    rintro V ⟨hVB, hxV⟩
    -- ⊢ ∃ i, 0 < i ∧ F ⁻¹' ball (F x) i ⊆ V
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    -- ⊢ ∃ i, 0 < i ∧ F ⁻¹' ball (F x) i ⊆ V
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    -- ⊢ ∃ i, 0 < i ∧ F ⁻¹' ball (F x) i ⊆ V
    refine' ⟨ε UV, (ε01 UV).1, fun y (hy : dist (F y) (F x) < ε UV) => _⟩
    -- ⊢ y ∈ V
    replace hy : dist (F y UV) (F x UV) < ε UV
    -- ⊢ dist (↑(F y) UV) (↑(F x) UV) < ε UV
    exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hy
    -- ⊢ y ∈ V
    contrapose! hy
    -- ⊢ ε { val := (U, V), property := (_ : (U, V) ∈ B ×ˢ B ∧ closure (U, V).fst ⊆ ( …
    rw [hF, hF, hfε UV hy, hf0 UV hxU, Pi.zero_apply, dist_zero_right]
    -- ⊢ ε { val := (U, V), property := (_ : (U, V) ∈ B ×ˢ B ∧ closure (U, V).fst ⊆ ( …
    exact le_abs_self _
    -- 🎉 no goals
  · /- Finally, we prove that `F` is continuous. Given `δ > 0`, consider the set `T` of `(U, V) ∈ s`
    such that `ε (U, V) ≥ δ`. Since `ε` tends to zero, `T` is finite. Since each `f` is continuous,
    we can choose a neighborhood such that `dist (F y (U, V)) (F x (U, V)) ≤ δ` for any
    `(U, V) ∈ T`. For `(U, V) ∉ T`, the same inequality is true because both `F y (U, V)` and
    `F x (U, V)` belong to the interval `[0, ε (U, V)]`. -/
    refine' (nhds_basis_closedBall.comap _).ge_iff.2 fun δ δ0 => _
    -- ⊢ F ⁻¹' closedBall (F x) δ ∈ 𝓝 x
    have h_fin : { UV : s | δ ≤ ε UV }.Finite := by simpa only [← not_lt] using hε (gt_mem_nhds δ0)
    -- ⊢ F ⁻¹' closedBall (F x) δ ∈ 𝓝 x
    have : ∀ᶠ y in 𝓝 x, ∀ UV, δ ≤ ε UV → dist (F y UV) (F x UV) ≤ δ := by
      refine' (eventually_all_finite h_fin).2 fun UV _ => _
      exact (f UV).continuous.tendsto x (closedBall_mem_nhds _ δ0)
    refine' this.mono fun y hy => (BoundedContinuousFunction.dist_le δ0.le).2 fun UV => _
    -- ⊢ dist (↑(F y) UV) (↑(F x) UV) ≤ δ
    cases' le_total δ (ε UV) with hle hle
    -- ⊢ dist (↑(F y) UV) (↑(F x) UV) ≤ δ
    exacts [hy _ hle, (Real.dist_le_of_mem_Icc (hf0ε _ _) (hf0ε _ _)).trans (by rwa [sub_zero])]
    -- 🎉 no goals
#align topological_space.exists_embedding_l_infty TopologicalSpace.exists_embedding_l_infty

/-- *Urysohn's metrization theorem* (Tychonoff's version): a T₃ topological space with second
countable topology `X` is metrizable, i.e., there exists a metric space structure that generates the
same topology. -/
theorem metrizableSpace_of_t3_second_countable : MetrizableSpace X :=
  let ⟨_, hf⟩ := exists_embedding_l_infty X
  hf.metrizableSpace
#align topological_space.metrizable_space_of_t3_second_countable TopologicalSpace.metrizableSpace_of_t3_second_countable

instance : MetrizableSpace ENNReal :=
  metrizableSpace_of_t3_second_countable ENNReal

end TopologicalSpace
