/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Justin Palumbo
-/
module

public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Topology.Metrizable.CompletelyMetrizable
public import Mathlib.Topology.Sets.Opens

/-!
# Polish spaces

A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this file, we establish the basic properties of Polish spaces.

## Main definitions and results

* `PolishSpace α` is a mixin typeclass on a topological space, requiring that the topology is
  second-countable and compatible with a complete metric. To endow the space with such a metric,
  use in a proof `let := upgradeIsCompletelyMetrizable α`.
* `IsClosed.polishSpace`: a closed subset of a Polish space is Polish.
* `IsOpen.polishSpace`: an open subset of a Polish space is Polish.
* `IsGδ.polishSpace`: a countable intersection of open subsets of a Polish space is Polish.
* `exists_nat_nat_continuous_surjective`: any nonempty Polish space is the continuous image
  of the fundamental Polish space `ℕ → ℕ`.

A fundamental property of Polish spaces is that one can put finer topologies, still Polish,
with additional properties:

* `exists_polishSpace_forall_le`: on a topological space, consider countably many topologies
  `t n`, all Polish and finer than the original topology. Then there exists another Polish
  topology which is finer than all the `t n`.
* `IsClopenable s` is a property of a subset `s` of a topological space, requiring that there
  exists a finer topology, which is Polish, for which `s` becomes open and closed. We show that
  this property is satisfied for open sets, closed sets, for complements, and for countable unions.
  Once Borel-measurable sets are defined in later files, it will follow that any Borel-measurable
  set is clopenable. Once the Lusin-Souslin theorem is proved using analytic sets, we will even
  show that a set is clopenable if and only if it is Borel-measurable, see
  `isClopenable_iff_measurableSet`.
-/

@[expose] public section

noncomputable section

open Filter Function Metric TopologicalSpace Set Topology
open scoped Uniformity

variable {α : Type*} {β : Type*}

/-! ### Basic properties of Polish spaces -/


/-- A Polish space is a topological space with second countable topology, that can be endowed
with a metric for which it is complete.

To endow a Polish space with a complete metric space structure, do
`letI := upgradeIsCompletelyMetrizable α`.
-/
class PolishSpace (α : Type*) [h : TopologicalSpace α] : Prop
    extends SecondCountableTopology α, IsCompletelyMetrizableSpace α

instance [TopologicalSpace α] [SeparableSpace α] [IsCompletelyMetrizableSpace α] :
    PolishSpace α := by
  let := upgradeIsCompletelyMetrizable α
  have := UniformSpace.secondCountable_of_separable α
  constructor

namespace PolishSpace

/-- Any nonempty Polish space is the continuous image of the fundamental space `ℕ → ℕ`. -/
theorem exists_nat_nat_continuous_surjective (α : Type*) [TopologicalSpace α] [PolishSpace α]
    [Nonempty α] : ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Surjective f :=
  letI := upgradeIsCompletelyMetrizable α
  exists_nat_nat_continuous_surjective_of_completeSpace α

/-- Given a closed embedding into a Polish space, the source space is also Polish. -/
theorem _root_.Topology.IsClosedEmbedding.polishSpace [TopologicalSpace α] [TopologicalSpace β]
    [PolishSpace β] {f : α → β} (hf : IsClosedEmbedding f) : PolishSpace α := by
  let := upgradeIsCompletelyMetrizable β
  let : MetricSpace α := hf.isEmbedding.comapMetricSpace f
  have : SecondCountableTopology α := hf.isEmbedding.secondCountableTopology
  have : CompleteSpace α := by
    rw [completeSpace_iff_isComplete_range hf.isEmbedding.to_isometry.isUniformInducing]
    exact hf.isClosed_range.isComplete
  infer_instance

/-- Pulling back a Polish topology under an equiv gives again a Polish topology. -/
theorem _root_.Equiv.polishSpace_induced [t : TopologicalSpace β] [PolishSpace β] (f : α ≃ β) :
    @PolishSpace α (t.induced f) :=
  letI : TopologicalSpace α := t.induced f
  (f.toHomeomorphOfIsInducing ⟨rfl⟩).isClosedEmbedding.polishSpace

/-- A closed subset of a Polish space is also Polish. -/
theorem _root_.IsClosed.polishSpace [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsClosed s) : PolishSpace s :=
  hs.isClosedEmbedding_subtypeVal.polishSpace

protected theorem _root_.CompletePseudometrizable.iInf {ι : Type*} [Countable ι]
    {t : ι → TopologicalSpace α} (ht₀ : ∃ t₀, @T2Space α t₀ ∧ ∀ i, t i ≤ t₀)
    (ht : ∀ i, ∃ u : UniformSpace α, CompleteSpace α ∧ 𝓤[u].IsCountablyGenerated ∧
      u.toTopologicalSpace = t i) :
    ∃ u : UniformSpace α, CompleteSpace α ∧
      𝓤[u].IsCountablyGenerated ∧ u.toTopologicalSpace = ⨅ i, t i := by
  choose u hcomp hcount hut using ht
  obtain rfl : t = fun i ↦ (u i).toTopologicalSpace := (funext hut).symm
  refine ⟨⨅ i, u i, .iInf hcomp ht₀, ?_, UniformSpace.toTopologicalSpace_iInf⟩
  rw [iInf_uniformity]
  infer_instance

protected theorem iInf {ι : Type*} [Countable ι] {t : ι → TopologicalSpace α}
    (ht₀ : ∃ i₀, ∀ i, t i ≤ t i₀) (ht : ∀ i, @PolishSpace α (t i)) : @PolishSpace α (⨅ i, t i) := by
  rcases ht₀ with ⟨i₀, hi₀⟩
  rcases CompletePseudometrizable.iInf ⟨t i₀, letI := t i₀; haveI := ht i₀; inferInstance, hi₀⟩
    fun i ↦
      letI := t i; haveI := ht i; letI := upgradeIsCompletelyMetrizable α
      ⟨inferInstance, inferInstance, inferInstance, rfl⟩
    with ⟨u, hcomp, hcount, htop⟩
  rw [← htop]
  have : @SecondCountableTopology α u.toTopologicalSpace :=
    htop.symm ▸ secondCountableTopology_iInf fun i ↦ letI := t i; (ht i).toSecondCountableTopology
  have : @T1Space α u.toTopologicalSpace :=
    htop.symm ▸ t1Space_antitone (iInf_le _ i₀) (by let := t i₀; have := ht i₀; infer_instance)
  infer_instance

/-- Given a Polish space, and countably many finer Polish topologies, there exists another Polish
topology which is finer than all of them. -/
theorem exists_polishSpace_forall_le {ι : Type*} [Countable ι] [t : TopologicalSpace α]
    [p : PolishSpace α] (m : ι → TopologicalSpace α) (hm : ∀ n, m n ≤ t)
    (h'm : ∀ n, @PolishSpace α (m n)) :
    ∃ t' : TopologicalSpace α, (∀ n, t' ≤ m n) ∧ t' ≤ t ∧ @PolishSpace α t' :=
  ⟨⨅ i : Option ι, i.elim t m, fun i ↦ iInf_le _ (some i), iInf_le _ none,
    .iInf ⟨none, Option.forall.2 ⟨le_rfl, hm⟩⟩ <| Option.forall.2 ⟨p, h'm⟩⟩

instance : PolishSpace ENNReal :=
  ENNReal.orderIsoUnitIntervalBirational.toHomeomorph.isClosedEmbedding.polishSpace

end PolishSpace

/-!
### An open subset of a Polish space is Polish

To prove this fact, one needs to construct another metric, giving rise to the same topology,
for which the open subset is complete. This is not obvious, as for instance `(0,1) ⊆ ℝ` is not
complete for the usual metric of `ℝ`: one should build a new metric that blows up close to the
boundary.
-/

namespace TopologicalSpace.Opens

variable [MetricSpace α] {s : Opens α}

/-- A type synonym for a subset `s` of a metric space, on which we will construct another metric
for which it will be complete. -/
def CompleteCopy {α : Type*} [MetricSpace α] (s : Opens α) : Type _ := s

namespace CompleteCopy

/-- A distance on an open subset `s` of a metric space, designed to make it complete.  It is given
by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the second term blows up close to
the boundary to ensure that Cauchy sequences for `dist'` remain well inside `s`. -/
instance instDist : Dist (CompleteCopy s) where
  dist x y := dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ)

theorem dist_eq (x y : CompleteCopy s) :
    dist x y = dist x.1 y.1 + abs (1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ) :=
  rfl

theorem dist_val_le_dist (x y : CompleteCopy s) : dist x.1 y.1 ≤ dist x y :=
  le_add_of_nonneg_right (abs_nonneg _)

instance : TopologicalSpace (CompleteCopy s) := inferInstanceAs (TopologicalSpace s)
instance [SecondCountableTopology α] : SecondCountableTopology (CompleteCopy s) :=
  inferInstanceAs (SecondCountableTopology s)
instance : T0Space (CompleteCopy s) := inferInstanceAs (T0Space s)

/--
A metric space structure on a subset `s` of a metric space, designed to make it complete
if `s` is open. It is given by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the
second term blows up close to the boundary to ensure that Cauchy sequences for `dist'` remain well
inside `s`.

This definition ensures the `TopologicalSpace` structure on
`TopologicalSpace.Opens.CompleteCopy s` is definitionally equal to the original one.
-/
instance instMetricSpace : MetricSpace (CompleteCopy s) := by
  refine @MetricSpace.ofT0PseudoMetricSpace (CompleteCopy s)
    (.ofDistTopology dist (fun _ ↦ ?_) (fun _ _ ↦ ?_) (fun x y z ↦ ?_) fun t ↦ ?_) _
  · simp only [dist_eq, dist_self, one_div, sub_self, abs_zero, add_zero]
  · simp only [dist_eq, dist_comm, abs_sub_comm]
  · calc
      dist x z = dist x.1 z.1 + |1 / infDist x.1 sᶜ - 1 / infDist z.1 sᶜ| := rfl
      _ ≤ dist x.1 y.1 + dist y.1 z.1 + (|1 / infDist x.1 sᶜ - 1 / infDist y.1 sᶜ| +
            |1 / infDist y.1 sᶜ - 1 / infDist z.1 sᶜ|) :=
        add_le_add (dist_triangle _ _ _) (dist_triangle (1 / infDist _ _) _ _)
      _ = dist x y + dist y z := add_add_add_comm ..
  · refine ⟨fun h x hx ↦ ?_, fun h ↦ isOpen_iff_mem_nhds.2 fun x hx ↦ ?_⟩
    · rcases (Metric.isOpen_iff (α := s)).1 h x hx with ⟨ε, ε0, hε⟩
      exact ⟨ε, ε0, fun y hy ↦ hε <| (dist_comm _ _).trans_lt <| (dist_val_le_dist _ _).trans_lt hy⟩
    · rcases h x hx with ⟨ε, ε0, hε⟩
      simp only [dist_eq, one_div] at hε
      have : Tendsto (fun y : s ↦ dist x.1 y.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist y.1 sᶜ)⁻¹|)
          (𝓝 x) (𝓝 (dist x.1 x.1 + |(infDist x.1 sᶜ)⁻¹ - (infDist x.1 sᶜ)⁻¹|)) := by
        refine (tendsto_const_nhds.dist continuous_subtype_val.continuousAt).add
          (tendsto_const_nhds.sub <| ?_).abs
        refine (continuousAt_inv_infDist_pt ?_).comp continuous_subtype_val.continuousAt
        rw [s.isOpen.isClosed_compl.closure_eq, mem_compl_iff, not_not]
        exact x.2
      simp only [dist_self, sub_self, abs_zero, zero_add] at this
      exact mem_of_superset (this <| gt_mem_nhds ε0) hε

instance instCompleteSpace [CompleteSpace α] : CompleteSpace (CompleteCopy s) := by
  refine Metric.complete_of_convergent_controlled_sequences ((1 / 2) ^ ·) (by simp) fun u hu ↦ ?_
  have A : CauchySeq fun n => (u n).1 := by
    refine cauchySeq_of_le_tendsto_0 (fun n : ℕ => (1 / 2) ^ n) (fun n m N hNn hNm => ?_) ?_
    · exact (dist_val_le_dist (u n) (u m)).trans (hu N n m hNn hNm).le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by simp) (by norm_num)
  obtain ⟨x, xlim⟩ : ∃ x, Tendsto (fun n => (u n).1) atTop (𝓝 x) := cauchySeq_tendsto_of_complete A
  by_cases xs : x ∈ s
  · exact ⟨⟨x, xs⟩, tendsto_subtype_rng.2 xlim⟩
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, 1 / infDist (u n).1 sᶜ < C := by
    refine ⟨(1 / 2) ^ 0 + 1 / infDist (u 0).1 sᶜ, fun n ↦ ?_⟩
    rw [← sub_lt_iff_lt_add]
    calc
      _ ≤ |1 / infDist (u n).1 sᶜ - 1 / infDist (u 0).1 sᶜ| := le_abs_self _
      _ = |1 / infDist (u 0).1 sᶜ - 1 / infDist (u n).1 sᶜ| := abs_sub_comm _ _
      _ ≤ dist (u 0) (u n) := le_add_of_nonneg_left dist_nonneg
      _ < (1 / 2) ^ 0 := hu 0 0 n le_rfl n.zero_le
  have Cpos : 0 < C := lt_of_le_of_lt (div_nonneg zero_le_one infDist_nonneg) (hC 0)
  have Hmem : ∀ {y}, y ∈ s ↔ 0 < infDist y sᶜ := fun {y} ↦ by
    rw [← s.isOpen.isClosed_compl.notMem_iff_infDist_pos ⟨x, xs⟩]; exact not_not.symm
  have I : ∀ n, 1 / C ≤ infDist (u n).1 sᶜ := fun n ↦ by
    have : 0 < infDist (u n).1 sᶜ := Hmem.1 (u n).2
    rw [div_le_iff₀' Cpos]
    exact (div_le_iff₀ this).1 (hC n).le
  have I' : 1 / C ≤ infDist x sᶜ :=
    have : Tendsto (fun n => infDist (u n).1 sᶜ) atTop (𝓝 (infDist x sᶜ)) :=
      ((continuous_infDist_pt (sᶜ : Set α)).tendsto x).comp xlim
    ge_of_tendsto' this I
  exact absurd (Hmem.2 <| lt_of_lt_of_le (div_pos one_pos Cpos) I') xs

/-- An open subset of a Polish space is also Polish. -/
theorem _root_.IsOpen.polishSpace {α : Type*} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsOpen s) : PolishSpace s := by
  let := upgradeIsCompletelyMetrizable α
  lift s to Opens α using hs
  exact inferInstanceAs (PolishSpace s.CompleteCopy)

end CompleteCopy

end TopologicalSpace.Opens

/-!
### A Gδ subset of a Polish space is Polish

To prove this fact, we follow a proof attributed to A. Bernshteyn. We homeomorphically map a Gδ
subset of α to a subset of α × (ℕ → ℝ), which is closed and thus Polish.

This result is a generalization of the fact that open subsets of a Polish space are open,
and could be used to separately derive the open case, which was proved separately above by
directly constructing a complete compatible metric.
-/

namespace GδEmbedding

variable [MetricSpace α] {U : ℕ → Set α}

/-- The map `x ↦ (x, fun n ↦ d(x, U nᶜ)⁻¹)` from `⋂ n, U n` into `X × (ℕ → ℝ)`. When the `U n`
are open, this is a closed embedding: the `n`-th coordinate of the second component blows up as
`x` approaches the boundary of `U n`, so that the boundary is sent "to infinity". This guarantees
limit points will have their first coordinates within all of the `U n` -/
def gδEmbedding (U : ℕ → Set α) (x : ↥(⋂ n, U n)) : α × (ℕ → ℝ) :=
  (x.1, fun n : ℕ ↦ (infDist x.1 (U n)ᶜ)⁻¹)

/-- A point of `⋂ n, U n` is at positive distance from each `U nᶜ`, as long as the latter is a
nonempty closed set. -/
theorem infDist_compl_pos (hUo : ∀ n, IsOpen (U n)) (hUne : ∀ n, ((U n)ᶜ).Nonempty)
    (x : ↥(⋂ n, U n)) (n : ℕ) : 0 < infDist x.1 (U n)ᶜ :=
  ((hUo n).isClosed_compl.notMem_iff_infDist_pos (hUne n)).1 (not_not.2 (mem_iInter.1 x.2 n))

theorem continuous_gδEmbedding (hUo : ∀ n, IsOpen (U n)) : Continuous (gδEmbedding U) := by
  refine continuous_subtype_val.prodMk (continuous_pi fun n ↦ ?_)
  refine continuous_iff_continuousAt.2 fun x : ⋂ n, U n ↦ ?_
  refine (continuousAt_inv_infDist_pt ?_).comp continuous_subtype_val.continuousAt
  rw [(hUo n).isClosed_compl.closure_eq, mem_compl_iff, not_not]
  exact mem_iInter.1 x.2 n

/-- `gδEmbedding U` is an embedding: a) it is inducing because composing it with `Prod.fst`
gives the inclusion `⋂ n, U n → X` and b) it is injective because its projection to the
first coordinate is. -/
theorem isEmbedding_gδEmbedding (hUo : ∀ n, IsOpen (U n)) : IsEmbedding (gδEmbedding U) :=
  ⟨IsInducing.of_comp (continuous_gδEmbedding hUo) continuous_fst IsInducing.subtypeVal,
   fun (x y : ⋂ n, U n) (hxy : (gδEmbedding U x = gδEmbedding U y))
     ↦ Subtype.ext (congrArg Prod.fst hxy)⟩

/-- The range of `gδEmbedding U` is definable as the set of pairs `x` `r` satisfying the countably
many equations `r n * d(x, U nᶜ) = 1`. This is because such an equation forces `d(x, U nᶜ) ≠ 0`,
i.e. `x ∈ U n`, and at the same time determines `r n`. -/
theorem range_gδEmbedding (hUo : ∀ n, IsOpen (U n)) (hUne : ∀ n, ((U n)ᶜ).Nonempty) :
    range (gδEmbedding U) = {q : α × (ℕ → ℝ) | ∀ n, q.2 n * infDist q.1 (U n)ᶜ = 1} := by
  ext q
  simp only [mem_range, mem_ofPred_eq]
  constructor
  · rintro ⟨y, rfl⟩ n
    exact inv_mul_cancel₀ (infDist_compl_pos hUo hUne y n).ne'
  · intro h
    have hne : ∀ n, infDist q.1 (U n)ᶜ ≠ 0 := by
      intro n h0
      have : q.2 n * infDist q.1 (U n)ᶜ = 1 := h n
      rw [h0, mul_zero] at this
      exact zero_ne_one this
    have hmem : q.1 ∈ ⋂ n, U n := mem_iInter.2 fun n ↦ by
      have : q.1 ∉ (U n)ᶜ :=
        ((hUo n).isClosed_compl.notMem_iff_infDist_pos (hUne n)).2
          (infDist_nonneg.lt_of_ne' (hne n))
      exact not_not.1 this
    refine ⟨⟨q.1, hmem⟩, ?_ ⟩
    refine Prod.ext rfl ?_
    funext n
    exact inv_eq_of_mul_eq_one_left (h n)

theorem isClosed_range_gδEmbedding (hUo : ∀ n, IsOpen (U n)) (hUne : ∀ n, ((U n)ᶜ).Nonempty) :
    IsClosed (range (gδEmbedding U)) := by
  rw [range_gδEmbedding hUo hUne, ofPred_forall]
  refine isClosed_iInter fun n ↦ isClosed_eq ?_ continuous_const
  exact ((continuous_apply n).comp continuous_snd).mul
    ((continuous_infDist_pt (U n)ᶜ).comp continuous_fst)

/-- If `U n` is a sequence of open sets, none of which is all of `X`, then `⋂ n, U n` is
homeomorphic to a closed subset of `X × (ℕ → ℝ)` via `gδEmbedding U`. -/
theorem isClosedEmbedding_gδEmbedding (hUo : ∀ n, IsOpen (U n)) (hUne : ∀ n, ((U n)ᶜ).Nonempty) :
    IsClosedEmbedding (gδEmbedding U) :=
  ⟨isEmbedding_gδEmbedding hUo, isClosed_range_gδEmbedding hUo hUne⟩

/-- A countable intersection of proper open subsets of a Polish space is Polish. -/
theorem polishSpace_iInter_of_isOpen
    [CompleteSpace α] [SecondCountableTopology α] (hUo : ∀ n, IsOpen (U n))
    (hUne : ∀ n, ((U n)ᶜ).Nonempty) : PolishSpace (⋂ n, U n) :=
  (isClosedEmbedding_gδEmbedding hUo hUne).polishSpace

/-- A Gδ subset of a Polish space is also Polish. -/
theorem _root_.IsGδ.polishSpace {α : Type*} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsGδ s) : PolishSpace s := by
  let := upgradeIsCompletelyMetrizable α
  obtain ⟨V, V_open, rfl⟩ := hs.eq_iInter_nat
  -- dispose of the case `s = univ` so we may assume nonempty complements
  rcases eq_or_ne (⋂ n, V n) univ with h | h
  · rw [h]
    exact isClosed_univ.polishSpace
  -- otherwise pick `x₀ ∉ ⋂ n, V n`, say `x₀ ∉ V m`, and shrink every `V n` by intersecting
  -- with `V m`; this changes neither the intersection nor its openness, but now no member of
  -- the family is equal to `univ`
  obtain ⟨x₀, hx₀⟩ := nonempty_compl.2 h
  simp only [mem_compl_iff, mem_iInter, not_forall] at hx₀
  obtain ⟨m, hm⟩ := hx₀
  have hVeq : (⋂ n, V n ∩ V m) = ⋂ n, V n := by
    ext x
    simp only [mem_iInter, mem_inter_iff]
    exact ⟨fun hx n ↦ (hx n).1, fun hx n ↦ ⟨hx n, hx m⟩⟩
  rw [← hVeq]
  exact polishSpace_iInter_of_isOpen (fun n ↦ (V_open n).inter (V_open m))
    fun n ↦ ⟨x₀, fun hc ↦ hm hc.2⟩

end GδEmbedding

namespace PolishSpace

/-! ### Clopenable sets in Polish spaces -/

/-- A set in a topological space is clopenable if there exists a finer Polish topology for which
this set is open and closed. It turns out that this notion is equivalent to being Borel-measurable,
but this is nontrivial (see `isClopenable_iff_measurableSet`). -/
def IsClopenable [t : TopologicalSpace α] (s : Set α) : Prop :=
  ∃ t' : TopologicalSpace α, t' ≤ t ∧ @PolishSpace α t' ∧ IsClosed[t'] s ∧ IsOpen[t'] s

/-- Given a closed set `s` in a Polish space, one can construct a finer Polish topology for
which `s` is both open and closed. -/
theorem _root_.IsClosed.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsClosed s) : IsClopenable s := by
  /- Both sets `s` and `sᶜ` admit a Polish topology. So does their disjoint union `s ⊕ sᶜ`.
    Pulling back this topology by the canonical bijection with `α` gives the desired Polish
    topology in which `s` is both open and closed. -/
  classical
  have : PolishSpace s := hs.polishSpace
  let t : Set α := sᶜ
  have : PolishSpace t := hs.isOpen_compl.polishSpace
  let f : s ⊕ t ≃ α := Equiv.Set.sumCompl s
  have hle : TopologicalSpace.coinduced f instTopologicalSpaceSum ≤ ‹_› := by
    simp only [instTopologicalSpaceSum, coinduced_sup, coinduced_compose, sup_le_iff,
      ← continuous_iff_coinduced_le]
    exact ⟨continuous_subtype_val, continuous_subtype_val⟩
  refine ⟨.coinduced f instTopologicalSpaceSum, hle, ?_, hs.mono hle, ?_⟩
  · rw [← f.induced_symm]
    exact f.symm.polishSpace_induced
  · rw [isOpen_coinduced, isOpen_sum_iff]
    simp [preimage_preimage, f, t]

theorem IsClopenable.compl [TopologicalSpace α] {s : Set α} (hs : IsClopenable s) :
    IsClopenable sᶜ := by
  rcases hs with ⟨t, t_le, t_polish, h, h'⟩
  exact ⟨t, t_le, t_polish, @IsOpen.isClosed_compl α t s h', @IsClosed.isOpen_compl α t s h⟩

theorem _root_.IsOpen.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsOpen s) : IsClopenable s := by
  simpa using hs.isClosed_compl.isClopenable.compl

-- TODO: generalize for free to `[Countable ι] {s : ι → Set α}`
theorem IsClopenable.iUnion [t : TopologicalSpace α] [PolishSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClopenable (s n)) : IsClopenable (⋃ n, s n) := by
  choose m mt m_polish _ m_open using hs
  obtain ⟨t', t'm, -, t'_polish⟩ :
      ∃ t' : TopologicalSpace α, (∀ n : ℕ, t' ≤ m n) ∧ t' ≤ t ∧ @PolishSpace α t' :=
    exists_polishSpace_forall_le m mt m_polish
  have A : IsOpen[t'] (⋃ n, s n) := by
    apply isOpen_iUnion
    intro n
    apply t'm n
    exact m_open n
  obtain ⟨t'', t''_le, t''_polish, h1, h2⟩ : ∃ t'' : TopologicalSpace α,
      t'' ≤ t' ∧ @PolishSpace α t'' ∧ IsClosed[t''] (⋃ n, s n) ∧ IsOpen[t''] (⋃ n, s n) :=
    @IsOpen.isClopenable α t' t'_polish _ A
  exact ⟨t'', t''_le.trans ((t'm 0).trans (mt 0)), t''_polish, h1, h2⟩

end PolishSpace
