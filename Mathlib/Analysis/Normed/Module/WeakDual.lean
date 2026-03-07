/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov, Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

/-!
# Weak dual of normed space

Let `E` be a normed space over a field `𝕜`. This file is concerned with properties of the weak-*
topology on the dual of `E`. By the dual, we mean either of the type synonyms
`StrongDual 𝕜 E` or `WeakDual 𝕜 E`, depending on whether it is viewed as equipped with its usual
operator norm topology or the weak-* topology.

It is shown that the canonical mapping `StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous, and
as a consequence the weak-* topology is coarser than the topology obtained from the operator norm
(dual norm).

In this file, we also establish the Banach-Alaoglu theorem about the compactness of closed balls
in the dual of `E` (as well as sets of somewhat more general form) with respect to the weak-*
topology.

## Main definitions

The main definitions concern the canonical mapping `StrongDual 𝕜 E → WeakDual 𝕜 E`.

* `StrongDual.toWeakDual` and `WeakDual.toStrongDual`: Linear equivalences from `StrongDual 𝕜 E` to
  `WeakDual 𝕜 E` and in the converse direction.
* `NormedSpace.Dual.continuousLinearMapToWeakDual`: A continuous linear mapping from
  `StrongDual 𝕜 E` to `WeakDual 𝕜 E` (same as `StrongDual.toWeakDual` but different bundled data).

## Main results

The first main result concerns the comparison of the operator norm topology on `StrongDual 𝕜 E` and
the weak-* topology on (its type synonym) `WeakDual 𝕜 E`:
* `dual_norm_topology_le_weak_dual_topology`: The weak-* topology on the dual of a normed space is
  coarser (not necessarily strictly) than the operator norm topology.
* `WeakDual.isCompact_polar` (a version of the Banach-Alaoglu theorem): The polar set of a
  neighborhood of the origin in a normed space `E` over `𝕜` is compact in `WeakDual _ E`, if the
  nontrivially normed field `𝕜` is proper as a topological space.
* `WeakDual.isCompact_closedBall` (the most common special case of the Banach-Alaoglu theorem):
  Closed balls in the dual of a normed space `E` over `ℝ` or `ℂ` are compact in the weak-star
  topology.

## TODO
* Add that in finite dimensions, the weak-* topology and the dual norm topology coincide.
* Add that in infinite dimensions, the weak-* topology is strictly coarser than the dual norm
  topology.
* Add metrizability of the dual unit ball (more generally weak-star compact subsets) of
  `WeakDual 𝕜 E` under the assumption of separability of `E`.
* Add the sequential Banach-Alaoglu theorem: the dual unit ball of a separable normed space `E`
  is sequentially compact in the weak-star topology. This would follow from the metrizability above.

## Implementation notes

Weak-* topology is defined generally in the file `Mathlib/Topology/Algebra/Module/WeakDual.lean`.

When `M` is a vector space, the duals `StrongDual 𝕜 M` and `WeakDual 𝕜 M` are type synonyms with
different topology instances.

For the proof of Banach-Alaoglu theorem, the weak dual of `E` is embedded in the space of
functions `E → 𝕜` with the topology of pointwise convergence.

The polar set `polar 𝕜 s` of a subset `s` of `E` is originally defined as a subset of the dual
`StrongDual 𝕜 E`. We care about properties of these w.r.t. weak-* topology, and for this purpose
give the definition `WeakDual.polar 𝕜 s` for the "same" subset viewed as a subset of `WeakDual 𝕜 E`
(a type synonym of the dual but with a different topology instance).

## References

* https://en.wikipedia.org/wiki/Weak_topology#Weak-*_topology
* https://en.wikipedia.org/wiki/Banach%E2%80%93Alaoglu_theorem

## Tags

weak-star, weak dual

-/

@[expose] public section

noncomputable section

open Filter Function Bornology Metric Set Topology Filter

/-!
### Equivalences between `StrongDual` and `WeakDual`
-/

namespace StrongDual

section

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousConstSMul R R]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [Module R M]

/-- For vector spaces `M`, there is a canonical map `StrongDual R M → WeakDual R M` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakDual : StrongDual R M ≃ₗ[R] WeakDual R M :=
  LinearEquiv.refl R (StrongDual R M)

@[deprecated (since := "2025-08-03")] alias _root_.NormedSpace.Dual.toWeakDual := toWeakDual

@[simp]
theorem coe_toWeakDual (x' : StrongDual R M) : toWeakDual x' = x' :=
  rfl

@[deprecated (since := "2025-08-03")]
alias _root_.NormedSpace.Dual.coe_toWeakDual := coe_toWeakDual

@[simp]
theorem toWeakDual_inj (x' y' : StrongDual R M) : toWeakDual x' = toWeakDual y' ↔ x' = y' :=
  (LinearEquiv.injective toWeakDual).eq_iff

@[deprecated (since := "2025-08-03")]
alias _root_.NormedSpace.Dual.toWeakDual_inj := toWeakDual_inj

end

end StrongDual

namespace WeakDual

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]

/-- For vector spaces `E`, there is a canonical map `WeakDual 𝕜 E → StrongDual 𝕜 E` (the "identity"
mapping). It is a linear equivalence. Here it is implemented as the inverse of the linear
equivalence `StrongDual.toWeakDual` in the other direction. -/
def toStrongDual : WeakDual 𝕜 E ≃ₗ[𝕜] StrongDual 𝕜 E :=
  StrongDual.toWeakDual.symm

theorem toStrongDual_apply (x : WeakDual 𝕜 E) (y : E) : (toStrongDual x) y = x y :=
  rfl

@[simp]
theorem coe_toStrongDual (x' : WeakDual 𝕜 E) : toStrongDual x' = x' :=
  rfl

@[simp]
theorem toStrongDual_inj (x' y' : WeakDual 𝕜 E) : toStrongDual x' = toStrongDual y' ↔ x' = y' :=
  (LinearEquiv.injective toStrongDual).eq_iff

section Bornology

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The norm bornology on `WeakDual 𝕜 F`, inherited from `StrongDual 𝕜 F`. -/
instance instBornology : Bornology (WeakDual 𝕜 F) := inferInstanceAs (Bornology (StrongDual 𝕜 F))

/-- A set in `WeakDual 𝕜 F` is bounded iff its image in `StrongDual 𝕜 F` is bounded. -/
@[simp]
theorem isBounded_toStrongDual_preimage {s : Set (StrongDual 𝕜 F)} :
    IsBounded (WeakDual.toStrongDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

/-- A set in `StrongDual 𝕜 F` is bounded iff its image in `WeakDual 𝕜 F` is bounded. -/
@[simp]
theorem isBounded_toWeakDual_preimage {s : Set (WeakDual 𝕜 F)} :
    IsBounded (StrongDual.toWeakDual ⁻¹' s) ↔ IsBounded s := Iff.rfl

end Bornology

end WeakDual

/-!
### Weak star topology on duals of normed spaces

In this section, we prove properties about the weak-* topology on duals of normed spaces.
We prove in particular that the canonical mapping `StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous,
i.e., that the weak-* topology is coarser (not necessarily strictly) than the topology given
by the dual-norm (i.e. the operator-norm).
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace NormedSpace

namespace Dual

theorem toWeakDual_continuous : Continuous fun x' : StrongDual 𝕜 E => StrongDual.toWeakDual x' :=
  WeakBilin.continuous_of_continuous_eval _ fun z => (inclusionInDoubleDual 𝕜 E z).continuous

/-- For a normed space `E`, according to `toWeakDual_continuous` the "identity mapping"
`StrongDual 𝕜 E → WeakDual 𝕜 E` is continuous. This definition implements it as a continuous linear
map. -/
def continuousLinearMapToWeakDual : StrongDual 𝕜 E →L[𝕜] WeakDual 𝕜 E :=
  { StrongDual.toWeakDual with cont := toWeakDual_continuous }

/-- The weak-star topology is coarser than the dual-norm topology. -/
theorem dual_norm_topology_le_weak_dual_topology :
    (UniformSpace.toTopologicalSpace : TopologicalSpace (StrongDual 𝕜 E)) ≤
      (instTopologicalSpaceWeakDual .. : TopologicalSpace (WeakDual 𝕜 E)) := by
  convert (@toWeakDual_continuous _ _ _ _ (by assumption)).le_induced
  exact induced_id.symm

end Dual

end NormedSpace

namespace WeakDual

open NormedSpace

/-!
### Bornology and pointwise bounds
-/

theorem isVonNBounded_iff_pointwise_bounded {s : Set (WeakDual 𝕜 E)} :
    Bornology.IsVonNBounded 𝕜 s ↔ ∀ x : E, ∃ r : ℝ, ∀ f ∈ s, ‖f x‖ ≤ r := by
  constructor
  · intro h_vN x
    have hU : (fun f : WeakDual 𝕜 E => f x) ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : WeakDual 𝕜 E) :=
      (eval_continuous x).continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds 0 one_pos)
    obtain ⟨r, _, hab⟩ := (h_vN hU).exists_pos
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm 𝕜 r
    refine ⟨‖a‖, fun f hf => ?_⟩
    obtain ⟨g, hg, rfl⟩ := (hab a ha.le) hf
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hg
    change ‖a * g x‖ ≤ ‖a‖
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hg.le
  · intro h V hV
    rw [show 𝓝 (0 : WeakDual 𝕜 E) = Filter.comap (fun f x ↦ f x) (𝓝 0) from
      nhds_induced _ _] at hV
    obtain ⟨W, hW, hWV⟩ := hV
    have hpi : Bornology.IsVonNBounded 𝕜 ((fun f x ↦ f x : WeakDual 𝕜 E → E → 𝕜) '' s) :=
      isVonNBounded_pi_iff.mpr fun x ↦ let ⟨C, hC⟩ := h x
        (NormedSpace.isVonNBounded_iff' 𝕜).mpr
          ⟨C, by rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩; exact hC f hf⟩
    obtain ⟨r, hr, hab⟩ := (hpi hW).exists_pos
    refine Absorbs.mono_left (.of_norm ⟨r, fun c hc f hf ↦ ?_⟩) hWV
    have hc0 : c ≠ 0 := norm_pos_iff.mp (hr.trans_le hc)
    have hmem := hab c hc (Set.mem_image_of_mem (fun f x ↦ f x) hf)
    rwa [Set.mem_smul_set_iff_inv_smul_mem₀ hc0] at hmem ⊢

/-- By the Uniform Boundedness Principle, norm-boundedness (the default bornology)
and pointwise-boundedness (`IsVonNBounded`) coincide on the weak dual of a Banach space. -/
theorem isBounded_iff_isVonNBounded [CompleteSpace E] {s : Set (WeakDual 𝕜 E)} :
    IsBounded s ↔ Bornology.IsVonNBounded 𝕜 s := by
  constructor
  · exact fun h => ((NormedSpace.isVonNBounded_iff 𝕜).mpr h).of_topologicalSpace_le
      Dual.dual_norm_topology_le_weak_dual_topology
  · intro h_vN
    have h_ptwise := isVonNBounded_iff_pointwise_bounded.mp h_vN
    obtain ⟨C, hC⟩ := banach_steinhaus (g := fun i : s ↦ WeakDual.toStrongDual i.val) fun x ↦
      let ⟨M, hM⟩ := h_ptwise x
      ⟨M, fun i ↦ hM i.val i.property⟩
    rw [← isBounded_toWeakDual_preimage, isBounded_iff_forall_norm_le]
    exact ⟨C, fun f hf ↦ hC ⟨StrongDual.toWeakDual f, hf⟩⟩

/-- By the Uniform Boundedness Principle, a set in the weak dual of a Banach space
is norm-bounded if and only if it is pointwise bounded. -/
theorem isBounded_iff_pointwise_bounded [CompleteSpace E] {s : Set (WeakDual 𝕜 E)} :
    IsBounded s ↔ ∀ x : E, ∃ C : ℝ, ∀ f ∈ s, ‖f x‖ ≤ C := by
  rw [isBounded_iff_isVonNBounded, isVonNBounded_iff_pointwise_bounded]

/-!
### Compactness of bounded closed sets

While the coercion `↑ : WeakDual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets.
-/

theorem isClosed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' s) :=
  ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)

theorem isCompact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded s) (hc : IsClosed s) : IsCompact s :=
  DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr <|
    ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb <|
      isClosed_image_coe_of_bounded_of_closed hb hc

/-!
### Closed balls
-/

theorem isClosed_closedBall (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsClosed (toStrongDual ⁻¹' closedBall x' r) :=
  isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)

/-- Closed balls are bounded in the weak dual. -/
theorem isBounded_closedBall (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsBounded (toStrongDual ⁻¹' closedBall x' r) :=
  isBounded_toStrongDual_preimage.mpr Metric.isBounded_closedBall

/-- The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` are compact in
the weak-star topology. -/
theorem isCompact_closedBall [ProperSpace 𝕜] (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsCompact (toStrongDual ⁻¹' closedBall x' r) :=
  isCompact_of_bounded_of_closed (isBounded_closedBall x' r) (isClosed_closedBall x' r)

/-!
### Polar sets in the weak dual space
-/

variable (𝕜)

/-- The polar set `polar 𝕜 s` of `s : Set E` seen as a subset of the dual of `E` with the
weak-star topology is `WeakDual.polar 𝕜 s`. -/
def polar (s : Set E) : Set (WeakDual 𝕜 E) :=
  toStrongDual ⁻¹' (StrongDual.polar 𝕜) s

theorem polar_def (s : Set E) : polar 𝕜 s = { f : WeakDual 𝕜 E | ∀ x ∈ s, ‖f x‖ ≤ 1 } :=
  rfl

/-- The polar `polar 𝕜 s` of a set `s : E` is a closed subset when the weak star topology
is used. -/
theorem isClosed_polar (s : Set E) : IsClosed (polar 𝕜 s) := by
  simp only [polar_def, setOf_forall]
  exact isClosed_biInter fun x hx => isClosed_Iic.preimage (WeakBilin.eval_continuous _ _).norm

/-- Polar sets of neighborhoods of the origin are bounded in the weak dual. -/
theorem isBounded_polar {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsBounded (polar 𝕜 s) :=
  isBounded_toStrongDual_preimage.mpr (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds)

/-- The image under `↑ : WeakDual 𝕜 E → (E → 𝕜)` of a polar `WeakDual.polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 s) :=
  isClosed_image_coe_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

/-- The image under `↑ : StrongDual 𝕜 E → (E → 𝕜)` of a polar `polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem _root_.NormedSpace.Dual.isClosed_image_polar_of_mem_nhds {s : Set E}
    (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : StrongDual 𝕜 E → E → 𝕜) '' StrongDual.polar 𝕜 s) :=
  WeakDual.isClosed_image_polar_of_mem_nhds 𝕜 s_nhds

/-- The **Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in a
normed space `E` is a compact subset of `WeakDual 𝕜 E`. -/
theorem isCompact_polar [ProperSpace 𝕜] {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsCompact (polar 𝕜 s) :=
  isCompact_of_bounded_of_closed (isBounded_polar 𝕜 s_nhds) (isClosed_polar _ _)

/-!
### Sequential compactness
-/

open TopologicalSpace

variable (𝕜 V : Type*) [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
variable [TopologicalSpace.SeparableSpace V] (K : Set (WeakDual 𝕜 V))

/-- In a separable normed space, there exists a sequence of continuous functions that
separates points of the weak dual. -/
lemma exists_countable_separating : ∃ (gs : ℕ → (WeakDual 𝕜 V) → 𝕜),
    (∀ n, Continuous (gs n)) ∧ (∀ ⦃x y⦄, x ≠ y → ∃ n, gs n x ≠ gs n y) := by
  use (fun n φ ↦ φ (denseSeq V n))
  constructor
  · exact fun _ ↦ eval_continuous _
  · intro w y w_ne_y
    contrapose! w_ne_y
    exact DFunLike.ext'_iff.mpr <| (map_continuous w).ext_on
      (denseRange_denseSeq V) (map_continuous y) (by grind [Set.eqOn_range])

/-- A compact subset of the dual space of a separable space is metrizable. -/
lemma metrizable_of_isCompact (K_cpt : IsCompact K) : TopologicalSpace.MetrizableSpace K := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp K_cpt
  obtain ⟨gs, gs_cont, gs_sep⟩ := exists_countable_separating 𝕜 V
  exact Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun n k ↦ gs n k) (fun n ↦ (gs_cont n).comp continuous_subtype_val)
    fun x y hxy ↦ gs_sep <| Subtype.val_injective.ne hxy

variable [ProperSpace 𝕜] (K_cpt : IsCompact K)

theorem isSeqCompact_of_isBounded_of_isClosed {s : Set (WeakDual 𝕜 V)}
    (hb : IsBounded s) (hc : IsClosed s) :
    IsSeqCompact s := by
  have b_isCompact' : CompactSpace s :=
    isCompact_iff_compactSpace.mp <| isCompact_of_bounded_of_closed hb hc
  have b_isMetrizable : TopologicalSpace.MetrizableSpace s :=
    metrizable_of_isCompact 𝕜 V s <| isCompact_of_bounded_of_closed hb hc
  have seq_cont_phi : SeqContinuous (fun φ : s ↦ (φ : WeakDual 𝕜 V)) :=
    continuous_iff_seqContinuous.mp continuous_subtype_val
  simpa using IsSeqCompact.range seq_cont_phi

/-- The **Sequential Banach-Alaoglu theorem**: the polar set of a neighborhood `s` of the origin in
a separable normed space `V` is a sequentially compact subset of `WeakDual 𝕜 V`. -/
theorem isSeqCompact_polar {s : Set V} (s_nhd : s ∈ 𝓝 (0 : V)) :
    IsSeqCompact (polar 𝕜 s) :=
  isSeqCompact_of_isBounded_of_isClosed (s := polar 𝕜 s) _ _
    (isBounded_polar 𝕜 s_nhd) (isClosed_polar _ _)

/-- The **Sequential Banach-Alaoglu theorem**: closed balls of the dual of a separable
normed space `V` are sequentially compact in the weak-* topology. -/
theorem isSeqCompact_closedBall (x' : StrongDual 𝕜 V) (r : ℝ) :
    IsSeqCompact (toStrongDual ⁻¹' Metric.closedBall x' r) :=
  isSeqCompact_of_isBounded_of_isClosed 𝕜 V
    (isBounded_closedBall x' r) (isClosed_closedBall x' r)

end WeakDual
