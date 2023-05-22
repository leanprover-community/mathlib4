/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module topology.metric_space.metrizable
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecificLimits.Basic
import Mathbin.Topology.UrysohnsLemma
import Mathbin.Topology.ContinuousFunction.Bounded
import Mathbin.Topology.UniformSpace.Cauchy

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

variable {ι X Y : Type _} {π : ι → Type _} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
  [∀ i, TopologicalSpace (π i)]

/-- A topological space is *pseudo metrizable* if there exists a pseudo metric space structure
compatible with the topology. To endow such a space with a compatible distance, use
`letI : pseudo_metric_space X := topological_space.pseudo_metrizable_space_pseudo_metric X`. -/
class PseudoMetrizableSpace (X : Type _) [t : TopologicalSpace X] : Prop where
  exists_pseudo_metric : ∃ m : PseudoMetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.pseudo_metrizable_space TopologicalSpace.PseudoMetrizableSpace

instance (priority := 100) PseudoMetricSpace.to_pseudoMetrizableSpace {X : Type _}
    [m : PseudoMetricSpace X] : PseudoMetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩
#align pseudo_metric_space.to_pseudo_metrizable_space PseudoMetricSpace.to_pseudoMetrizableSpace

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def pseudoMetrizableSpacePseudoMetric (X : Type _) [TopologicalSpace X]
    [h : PseudoMetrizableSpace X] : PseudoMetricSpace X :=
  h.exists_pseudo_metric.some.replaceTopology h.exists_pseudo_metric.choose_spec.symm
#align topological_space.pseudo_metrizable_space_pseudo_metric TopologicalSpace.pseudoMetrizableSpacePseudoMetric

instance pseudoMetrizableSpace_prod [PseudoMetrizableSpace X] [PseudoMetrizableSpace Y] :
    PseudoMetrizableSpace (X × Y) :=
  by
  letI : PseudoMetricSpace X := pseudo_metrizable_space_pseudo_metric X
  letI : PseudoMetricSpace Y := pseudo_metrizable_space_pseudo_metric Y
  infer_instance
#align topological_space.pseudo_metrizable_space_prod TopologicalSpace.pseudoMetrizableSpace_prod

/-- Given an inducing map of a topological space into a pseudo metrizable space, the source space
is also pseudo metrizable. -/
theorem Inducing.pseudoMetrizableSpace [PseudoMetrizableSpace Y] {f : X → Y} (hf : Inducing f) :
    PseudoMetrizableSpace X :=
  letI : PseudoMetricSpace Y := pseudo_metrizable_space_pseudo_metric Y
  ⟨⟨hf.comap_pseudo_metric_space, rfl⟩⟩
#align inducing.pseudo_metrizable_space Inducing.pseudoMetrizableSpace

/-- Every pseudo-metrizable space is first countable. -/
instance (priority := 100) PseudoMetrizableSpace.firstCountableTopology
    [h : PseudoMetrizableSpace X] : TopologicalSpace.FirstCountableTopology X :=
  by
  rcases h with ⟨_, hm⟩
  rw [← hm]
  exact
    @UniformSpace.firstCountableTopology X PseudoMetricSpace.toUniformSpace
      Emetric.Uniformity.Filter.isCountablyGenerated
#align topological_space.pseudo_metrizable_space.first_countable_topology TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology

instance PseudoMetrizableSpace.subtype [PseudoMetrizableSpace X] (s : Set X) :
    PseudoMetrizableSpace s :=
  inducing_subtype_val.PseudoMetrizableSpace
#align topological_space.pseudo_metrizable_space.subtype TopologicalSpace.PseudoMetrizableSpace.subtype

instance pseudoMetrizableSpace_pi [∀ i, PseudoMetrizableSpace (π i)] :
    PseudoMetrizableSpace (∀ i, π i) :=
  by
  cases nonempty_fintype ι
  letI := fun i => pseudo_metrizable_space_pseudo_metric (π i)
  infer_instance
#align topological_space.pseudo_metrizable_space_pi TopologicalSpace.pseudoMetrizableSpace_pi

/-- A topological space is metrizable if there exists a metric space structure compatible with the
topology. To endow such a space with a compatible distance, use
`letI : metric_space X := topological_space.metrizable_space_metric X` -/
class MetrizableSpace (X : Type _) [t : TopologicalSpace X] : Prop where
  exists_metric : ∃ m : MetricSpace X, m.toUniformSpace.toTopologicalSpace = t
#align topological_space.metrizable_space TopologicalSpace.MetrizableSpace

instance (priority := 100) MetricSpace.to_metrizableSpace {X : Type _} [m : MetricSpace X] :
    MetrizableSpace X :=
  ⟨⟨m, rfl⟩⟩
#align metric_space.to_metrizable_space MetricSpace.to_metrizableSpace

instance (priority := 100) MetrizableSpace.to_pseudoMetrizableSpace [h : MetrizableSpace X] :
    PseudoMetrizableSpace X :=
  ⟨let ⟨m, hm⟩ := h.1
    ⟨m.toPseudoMetricSpace, hm⟩⟩
#align topological_space.metrizable_space.to_pseudo_metrizable_space TopologicalSpace.MetrizableSpace.to_pseudoMetrizableSpace

/-- Construct on a metrizable space a metric compatible with the topology. -/
noncomputable def metrizableSpaceMetric (X : Type _) [TopologicalSpace X] [h : MetrizableSpace X] :
    MetricSpace X :=
  h.exists_metric.some.replaceTopology h.exists_metric.choose_spec.symm
#align topological_space.metrizable_space_metric TopologicalSpace.metrizableSpaceMetric

instance (priority := 100) t2Space_of_metrizableSpace [MetrizableSpace X] : T2Space X :=
  by
  letI : MetricSpace X := metrizable_space_metric X
  infer_instance
#align topological_space.t2_space_of_metrizable_space TopologicalSpace.t2Space_of_metrizableSpace

instance metrizableSpace_prod [MetrizableSpace X] [MetrizableSpace Y] : MetrizableSpace (X × Y) :=
  by
  letI : MetricSpace X := metrizable_space_metric X
  letI : MetricSpace Y := metrizable_space_metric Y
  infer_instance
#align topological_space.metrizable_space_prod TopologicalSpace.metrizableSpace_prod

/-- Given an embedding of a topological space into a metrizable space, the source space is also
metrizable. -/
theorem Embedding.metrizableSpace [MetrizableSpace Y] {f : X → Y} (hf : Embedding f) :
    MetrizableSpace X :=
  letI : MetricSpace Y := metrizable_space_metric Y
  ⟨⟨hf.comap_metric_space f, rfl⟩⟩
#align embedding.metrizable_space Embedding.metrizableSpace

instance MetrizableSpace.subtype [MetrizableSpace X] (s : Set X) : MetrizableSpace s :=
  embedding_subtype_val.MetrizableSpace
#align topological_space.metrizable_space.subtype TopologicalSpace.MetrizableSpace.subtype

instance metrizableSpace_pi [∀ i, MetrizableSpace (π i)] : MetrizableSpace (∀ i, π i) :=
  by
  cases nonempty_fintype ι
  letI := fun i => metrizable_space_metric (π i)
  infer_instance
#align topological_space.metrizable_space_pi TopologicalSpace.metrizableSpace_pi

variable (X) [T3Space X] [SecondCountableTopology X]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A T₃ topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`.
-/
theorem exists_embedding_l_infty : ∃ f : X → ℕ →ᵇ ℝ, Embedding f :=
  by
  haveI : NormalSpace X := normalSpaceOfT3SecondCountable X
  -- Choose a countable basis, and consider the set `s` of pairs of set `(U, V)` such that `U ∈ B`,
  -- `V ∈ B`, and `closure U ⊆ V`.
  rcases exists_countable_basis X with ⟨B, hBc, -, hB⟩
  set s : Set (Set X × Set X) := { UV ∈ B ×ˢ B | closure UV.1 ⊆ UV.2 }
  -- `s` is a countable set.
  haveI : Encodable s := ((hBc.prod hBc).mono (inter_subset_left _ _)).toEncodable
  -- We don't have the space of bounded (possibly discontinuous) functions, so we equip `s`
  -- with the discrete topology and deal with `s →ᵇ ℝ` instead.
  letI : TopologicalSpace s := ⊥
  haveI : DiscreteTopology s := ⟨rfl⟩
  rsuffices ⟨f, hf⟩ : ∃ f : X → s →ᵇ ℝ, Embedding f
  ·
    exact
      ⟨fun x => (f x).extend (Encodable.encode' s) 0,
        (BoundedContinuousFunction.isometry_extend (Encodable.encode' s)
                (0 : ℕ →ᵇ ℝ)).Embedding.comp
          hf⟩
  have hd : ∀ UV : s, Disjoint (closure UV.1.1) (UV.1.2ᶜ) := fun UV =>
    disjoint_compl_right.mono_right (compl_subset_compl.2 UV.2.2)
  -- Choose a sequence of `εₙ > 0`, `n : s`, that is bounded above by `1` and tends to zero
  -- along the `cofinite` filter.
  obtain ⟨ε, ε01, hε⟩ : ∃ ε : s → ℝ, (∀ UV, ε UV ∈ Ioc (0 : ℝ) 1) ∧ tendsto ε cofinite (𝓝 0) :=
    by
    rcases posSumOfEncodable zero_lt_one s with ⟨ε, ε0, c, hεc, hc1⟩
    refine' ⟨ε, fun UV => ⟨ε0 UV, _⟩, hεc.summable.tendsto_cofinite_zero⟩
    exact (le_hasSum hεc UV fun _ _ => (ε0 _).le).trans hc1
  /- For each `UV = (U, V) ∈ s` we use Urysohn's lemma to choose a function `f UV` that is equal to
    zero on `U` and is equal to `ε UV` on the complement to `V`. -/
  have :
    ∀ UV : s,
      ∃ f : C(X, ℝ),
        eq_on f 0 UV.1.1 ∧ eq_on f (fun _ => ε UV) (UV.1.2ᶜ) ∧ ∀ x, f x ∈ Icc 0 (ε UV) :=
    by
    intro UV
    rcases exists_continuous_zero_one_of_closed isClosed_closure
        (hB.is_open UV.2.1.2).isClosed_compl (hd UV) with
      ⟨f, hf₀, hf₁, hf01⟩
    exact
      ⟨ε UV • f, fun x hx => by simp [hf₀ (subset_closure hx)], fun x hx => by simp [hf₁ hx],
        fun x =>
        ⟨mul_nonneg (ε01 _).1.le (hf01 _).1, mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩
  choose f hf0 hfε hf0ε
  have hf01 : ∀ UV x, f UV x ∈ Icc (0 : ℝ) 1 := fun UV x =>
    Icc_subset_Icc_right (ε01 _).2 (hf0ε _ _)
  -- The embedding is given by `F x UV = f UV x`.
  set F : X → s →ᵇ ℝ := fun x =>
    ⟨⟨fun UV => f UV x, continuous_of_discreteTopology⟩, 1, fun UV₁ UV₂ =>
      Real.dist_le_of_mem_Icc_01 (hf01 _ _) (hf01 _ _)⟩
  have hF : ∀ x UV, F x UV = f UV x := fun _ _ => rfl
  refine' ⟨F, Embedding.mk' _ (fun x y hxy => _) fun x => le_antisymm _ _⟩
  · /- First we prove that `F` is injective. Indeed, if `F x = F y` and `x ≠ y`, then we can find
        `(U, V) ∈ s` such that `x ∈ U` and `y ∉ V`, hence `F x UV = 0 ≠ ε UV = F y UV`. -/
    refine' Classical.not_not.1 fun Hne => _
    -- `by_contra Hne` timeouts
    rcases hB.mem_nhds_iff.1 (is_open_ne.mem_nhds Hne) with ⟨V, hVB, hxV, hVy⟩
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    apply (ε01 UV).1.Ne
    calc
      (0 : ℝ) = F x UV := (hf0 UV hxU).symm
      _ = F y UV := by rw [hxy]
      _ = ε UV := hfε UV fun h : y ∈ V => hVy h rfl
      
  · /- Now we prove that each neighborhood `V` of `x : X` include a preimage of a neighborhood of
        `F x` under `F`. Without loss of generality, `V` belongs to `B`. Choose `U ∈ B` such that
        `x ∈ V` and `closure V ⊆ U`. Then the preimage of the `(ε (U, V))`-neighborhood of `F x`
        is included by `V`. -/
    refine' ((nhds_basis_ball.comap _).le_basis_iffₓ hB.nhds_has_basis).2 _
    rintro V ⟨hVB, hxV⟩
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    refine' ⟨ε UV, (ε01 UV).1, fun y (hy : dist (F y) (F x) < ε UV) => _⟩
    replace hy : dist (F y UV) (F x UV) < ε UV
    exact (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hy
    contrapose! hy
    rw [hF, hF, hfε UV hy, hf0 UV hxU, Pi.zero_apply, dist_zero_right]
    exact le_abs_self _
  · /- Finally, we prove that `F` is continuous. Given `δ > 0`, consider the set `T` of `(U, V) ∈ s`
        such that `ε (U, V) ≥ δ`. Since `ε` tends to zero, `T` is finite. Since each `f` is continuous,
        we can choose a neighborhood such that `dist (F y (U, V)) (F x (U, V)) ≤ δ` for any
        `(U, V) ∈ T`. For `(U, V) ∉ T`, the same inequality is true because both `F y (U, V)` and
        `F x (U, V)` belong to the interval `[0, ε (U, V)]`. -/
    refine' (nhds_basis_closed_ball.comap _).ge_iff.2 fun δ δ0 => _
    have h_fin : { UV : s | δ ≤ ε UV }.Finite := by simpa only [← not_lt] using hε (gt_mem_nhds δ0)
    have : ∀ᶠ y in 𝓝 x, ∀ UV, δ ≤ ε UV → dist (F y UV) (F x UV) ≤ δ :=
      by
      refine' (eventually_all_finite h_fin).2 fun UV hUV => _
      exact (f UV).Continuous.Tendsto x (closed_ball_mem_nhds _ δ0)
    refine' this.mono fun y hy => (BoundedContinuousFunction.dist_le δ0.le).2 fun UV => _
    cases' le_total δ (ε UV) with hle hle
    exacts[hy _ hle, (Real.dist_le_of_mem_Icc (hf0ε _ _) (hf0ε _ _)).trans (by rwa [sub_zero])]
#align topological_space.exists_embedding_l_infty TopologicalSpace.exists_embedding_l_infty

/-- *Urysohn's metrization theorem* (Tychonoff's version): a T₃ topological space with second
countable topology `X` is metrizable, i.e., there exists a metric space structure that generates the
same topology. -/
theorem metrizableSpace_of_t3_second_countable : MetrizableSpace X :=
  let ⟨f, hf⟩ := exists_embedding_l_infty X
  hf.MetrizableSpace
#align topological_space.metrizable_space_of_t3_second_countable TopologicalSpace.metrizableSpace_of_t3_second_countable

instance : MetrizableSpace ENNReal :=
  metrizableSpace_of_t3_second_countable ENNReal

end TopologicalSpace

