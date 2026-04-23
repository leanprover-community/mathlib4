/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Topology.UniformSpace.Separation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

Further results about extended metric spaces.
-/

@[expose] public section

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, edist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, edist_self]
  | succ n hle ihn =>
    calc
      edist (f m) (f (n + 1)) ≤ edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i ∈ Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle, Finset.sum_insert, add_comm]; simp

/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i :=
  le_trans (edist_le_Ico_sum_edist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_of_edist_le (zero_le n) fun _ => hd

namespace EMetric

theorem isUniformInducing_iff [PseudoEMetricSpace β] {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  isUniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).trans <| by
      simp only [subset_def, Prod.forall]; rfl

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
nonrec theorem isUniformEmbedding_iff [PseudoEMetricSpace β] {f : α → β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  (isUniformEmbedding_iff _).trans <| and_comm.trans <| Iff.rfl.and isUniformInducing_iff

/-- If a map between pseudoemetric spaces is a uniform inducing map then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
theorem controlled_of_isUniformInducing [PseudoEMetricSpace β] {f : α → β}
    (h : IsUniformInducing f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]
theorem controlled_of_isUniformEmbedding [PseudoEMetricSpace β] {f : α → β}
    (h : IsUniformEmbedding f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  controlled_of_isUniformInducing h.toIsUniformInducing

/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x, x ∈ t → ∀ y, y ∈ t → edist x y < ε := by
  rw [← neBot_iff]; exact uniformity_basis_edist.cauchy_iff

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀ n, 0 < B n)
    (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) →
      ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H

/-- A sequentially complete pseudoemetric space is complete. -/
theorem complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  UniformSpace.complete_of_cauchySeq_tendsto

/-- Expressing locally uniform convergence on a set using `edist`. -/
theorem tendstoLocallyUniformlyOn_iff {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `edist`. -/
theorem tendstoUniformlyOn_iff {ι : Type*} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, edist (f x) (F n x) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/-- Expressing locally uniform convergence using `edist`. -/
theorem tendstoLocallyUniformly_iff {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, mem_univ,
    forall_const, nhdsWithin_univ]

/-- Expressing uniform convergence using `edist`. -/
theorem tendstoUniformly_iff {ι : Type*} {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, edist (f x) (F n x) < ε := by
  simp only [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff, mem_univ, forall_const]

end EMetric

open Metric

namespace EMetric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s t : Set α}

theorem inseparable_iff : Inseparable x y ↔ edist x y = 0 := by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_gt_iff_le]

alias ⟨_root_.Inseparable.edist_eq_zero, _⟩ := EMetric.inseparable_iff

theorem nontrivial_iff_nontrivialTopology {α} [EMetricSpace α] :
    Nontrivial α ↔ NontrivialTopology α := by
  simp_rw [nontrivial_iff, TopologicalSpace.nontrivial_iff_exists_not_inseparable,
    EMetric.inseparable_iff, edist_eq_zero]

theorem subsingleton_iff_indiscreteTopology {α} [EMetricSpace α] :
    Subsingleton α ↔ IndiscreteTopology α := by
  simpa [not_nontrivial_iff_subsingleton] using nontrivial_iff_nontrivialTopology (α := α).not

/-- In an (e)metric space, every nontrivial type has a nontrivial topology. -/
instance (priority := 100) {α} [EMetricSpace α] [Nontrivial α] : NontrivialTopology α :=
  nontrivial_iff_nontrivialTopology.1 ‹_›

/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
theorem cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchySeq_iff

/-- A variation around the emetric characterization of Cauchy sequences -/
theorem cauchySeq_iff' [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ n ≥ N, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchySeq_iff'

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
theorem cauchySeq_iff_NNReal [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
  uniformity_basis_edist_nnreal.cauchySeq_iff'

theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, eball y ε :=
  ⟨fun H _ε ε0 => H _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| iUnion₂_mono fun _ _ _ => hε⟩⟩

theorem totallyBounded_iff' {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, eball y ε :=
  ⟨fun H _ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| iUnion₂_mono fun _ _ _ => hε⟩⟩

section Compact

/-- For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a countable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that is dense in `s`. -/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ s ⊆ ⋃ x ∈ t, Metric.closedEBall x ε) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  apply UniformSpace.subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := uniformity_basis_edist_le.mem_iff.1 hU
  obtain ⟨t, tC, ht⟩ := hs ε hε
  refine ⟨t, tC, ht.trans (iUnion₂_mono fun x hx y hy => UniformSpace.ball_mono hεU x ?_)⟩
  rwa [mem_closedEBall, edist_comm] at hy

-- TODO: generalize to metrizable spaces
/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set. -/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  refine subset_countable_closure_of_almost_dense_set s fun ε hε => ?_
  rcases totallyBounded_iff'.1 hs.totallyBounded ε hε with ⟨t, -, htf, hst⟩
  exact ⟨t, htf.countable, hst.trans <| iUnion₂_mono fun _ _ => eball_subset_closedEBall⟩

end Compact

section SecondCountable

open TopologicalSpace

variable (α) in
/-- A sigma compact pseudo emetric space has second countable topology. -/
instance (priority := 90) secondCountable_of_sigmaCompact [SigmaCompactSpace α] :
    SecondCountableTopology α := by
  suffices SeparableSpace α by exact UniformSpace.secondCountable_of_separable α
  choose T _ hTc hsubT using fun n =>
    subset_countable_closure_of_compact (isCompact_compactCovering α n)
  refine ⟨⟨⋃ n, T n, countable_iUnion hTc, fun x => ?_⟩⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering α) x with ⟨n, hn⟩
  exact closure_mono (subset_iUnion _ n) (hsubT _ hn)

theorem secondCountable_of_almost_dense_set
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ ⋃ x ∈ t, closedEBall x ε = univ) :
    SecondCountableTopology α := by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : ∀ ε > 0, ∃ t : Set α, Set.Countable t ∧ univ ⊆ ⋃ x ∈ t, closedEBall x ε := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this with ⟨t, -, htc, ht⟩
  exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩

end SecondCountable

end EMetric

variable {γ : Type w} [EMetricSpace γ]

-- see Note [lower instance priority]
/-- An emetric space is separated -/
instance (priority := 100) EMetricSpace.instT0Space : T0Space γ where
  t0 _ _ h := eq_of_edist_eq_zero <| EMetric.inseparable_iff.1 h

/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
theorem EMetric.isUniformEmbedding_iff' [PseudoEMetricSpace β] {f : γ → β} :
    IsUniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, edist (f a) (f b) < ε → edist a b < δ := by
  rw [isUniformEmbedding_iff_isUniformInducing, isUniformInducing_iff, uniformContinuous_iff]

/-- If a `PseudoEMetricSpace` is a T₀ space, then it is an `EMetricSpace`. -/
-- TODO: make it an instance?
abbrev EMetricSpace.ofT0PseudoEMetricSpace (α : Type*) [PseudoEMetricSpace α] [T0Space α] :
    EMetricSpace α :=
  { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun h => (EMetric.inseparable_iff.2 h).eq }

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
instance Prod.emetricSpaceMax [EMetricSpace β] : EMetricSpace (γ × β) :=
  .ofT0PseudoEMetricSpace _

namespace EMetric

/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s = closure t := by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, hsub.antisymm (closure_minimal hts hs.isClosed)⟩

end EMetric

/-!
### Separation quotient
-/

instance [PseudoEMetricSpace X] : EDist (SeparationQuotient X) where
  edist := SeparationQuotient.lift₂ edist fun _ _ _ _ hx hy =>
    edist_congr (EMetric.inseparable_iff.1 hx) (EMetric.inseparable_iff.1 hy)

@[simp] theorem SeparationQuotient.edist_mk [PseudoEMetricSpace X] (x y : X) :
    edist (mk x) (mk y) = edist x y :=
  rfl

open SeparationQuotient in
instance [PseudoEMetricSpace X] : EMetricSpace (SeparationQuotient X) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (SeparationQuotient X)
    { edist_self := surjective_mk.forall.2 edist_self,
      edist_comm := surjective_mk.forall₂.2 edist_comm,
      edist_triangle := surjective_mk.forall₃.2 edist_triangle,
      toUniformSpace := inferInstance,
      uniformity_edist := comap_injective (surjective_mk.prodMap surjective_mk) <| by
        simp [comap_mk_uniformity, PseudoEMetricSpace.uniformity_edist] } _

section LebesgueNumberLemma

variable {s : Set α}

theorem lebesgue_number_lemma_of_emetric {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, eball x δ ⊆ c i := by
  simpa only [eball, UniformSpace.ball, preimage_setOf_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma hs hc₁ hc₂

theorem lebesgue_number_lemma_of_emetric_nhds' {c : (x : α) → x ∈ s → Set α} (hs : IsCompact s)
    (hc : ∀ x hx, c x hx ∈ 𝓝 x) : ∃ δ > 0, ∀ x ∈ s, ∃ y : s, eball x δ ⊆ c y y.2 := by
  simpa only [eball, UniformSpace.ball, preimage_setOf_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds' hs hc

theorem lebesgue_number_lemma_of_emetric_nhds {c : α → Set α} (hs : IsCompact s)
    (hc : ∀ x ∈ s, c x ∈ 𝓝 x) : ∃ δ > 0, ∀ x ∈ s, ∃ y, eball x δ ⊆ c y := by
  simpa only [eball, UniformSpace.ball, preimage_setOf_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds hs hc

theorem lebesgue_number_lemma_of_emetric_nhdsWithin' {c : (x : α) → x ∈ s → Set α}
    (hs : IsCompact s) (hc : ∀ x hx, c x hx ∈ 𝓝[s] x) :
    ∃ δ > 0, ∀ x ∈ s, ∃ y : s, eball x δ ∩ s ⊆ c y y.2 := by
  simpa only [eball, UniformSpace.ball, preimage_setOf_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin' hs hc

theorem lebesgue_number_lemma_of_emetric_nhdsWithin {c : α → Set α} (hs : IsCompact s)
    (hc : ∀ x ∈ s, c x ∈ 𝓝[s] x) : ∃ δ > 0, ∀ x ∈ s, ∃ y, eball x δ ∩ s ⊆ c y := by
  simpa only [eball, UniformSpace.ball, preimage_setOf_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin hs hc

theorem lebesgue_number_lemma_of_emetric_sUnion {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) : ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, eball x δ ⊆ t := by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_emetric hs (by simpa) hc₂

end LebesgueNumberLemma
