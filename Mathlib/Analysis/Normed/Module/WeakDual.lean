/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.MetricSpace.PiNat

/-!
# Weak dual of normed space
-- **ADD SOMETHING?**

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

open Filter Function Bornology Metric Set

open Topology Filter

namespace StrongDual

section

variable {R : Type*} [CommSemiring R] [TopologicalSpace R] [ContinuousAdd R]
  [ContinuousConstSMul R R]
variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M] [Module R M]

/-- For vector spaces `M`, there is a canonical map `StrongDual R M → WeakDual R M` (the "identity"
mapping). It is a linear equivalence. -/
def toWeakDual : StrongDual R M ≃ₗ[R] WeakDual R M :=
  LinearEquiv.refl R (StrongDual R M)

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.Dual.toWeakDual := toWeakDual

@[simp]
theorem coe_toWeakDual (x' : StrongDual R M) : toWeakDual x' = x' :=
  rfl

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.Dual.coe_toWeakDual := coe_toWeakDual

@[simp]
theorem toWeakDual_inj (x' y' : StrongDual R M) : toWeakDual x' = toWeakDual y' ↔ x' = y' :=
  (LinearEquiv.injective toWeakDual).eq_iff

@[deprecated (since := "2025-08-3")] alias _root_.NormedSpace.Dual.toWeakDual_inj := toWeakDual_inj

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

@[deprecated (since := "2025-08-03")] alias toNormedDual := toStrongDual

theorem toStrongDual_apply (x : WeakDual 𝕜 E) (y : E) : (toStrongDual x) y = x y :=
  rfl

@[deprecated (since := "2025-08-03")] alias toNormedDual_apply := toStrongDual_apply

@[simp]
theorem coe_toStrongDual (x' : WeakDual 𝕜 E) : toStrongDual x' = x' :=
  rfl

@[deprecated (since := "2025-08-03")] alias coe_toNormedDual := coe_toStrongDual

@[simp]
theorem toStrongDual_inj (x' y' : WeakDual 𝕜 E) : toStrongDual x' = toStrongDual y' ↔ x' = y' :=
  (LinearEquiv.injective toStrongDual).eq_iff

@[deprecated (since := "2025-08-03")] alias toNormedDual_inj := toStrongDual_inj

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

theorem isClosed_closedBall (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsClosed (toStrongDual ⁻¹' closedBall x' r) :=
  isClosed_induced_iff'.2 (ContinuousLinearMap.is_weak_closed_closedBall x' r)

/-!
### Polar sets in the weak dual space
-/

/-- While the coercion `↑ : WeakDual 𝕜 E → (E → 𝕜)` is not a closed map, it sends *bounded*
closed sets to closed sets. -/
theorem isClosed_image_coe_of_bounded_of_closed {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded (StrongDual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' s) :=
  ContinuousLinearMap.isClosed_image_coe_of_bounded_of_weak_closed hb (isClosed_induced_iff'.1 hc)

theorem isCompact_of_bounded_of_closed [ProperSpace 𝕜] {s : Set (WeakDual 𝕜 E)}
    (hb : IsBounded (StrongDual.toWeakDual ⁻¹' s)) (hc : IsClosed s) : IsCompact s :=
  DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr <|
    ContinuousLinearMap.isCompact_image_coe_of_bounded_of_closed_image hb <|
      isClosed_image_coe_of_bounded_of_closed hb hc

variable (𝕜)

/-- The image under `↑ : WeakDual 𝕜 E → (E → 𝕜)` of a polar `WeakDual.polar 𝕜 s` of a
neighborhood `s` of the origin is a closed set. -/
theorem isClosed_image_polar_of_mem_nhds {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsClosed (((↑) : WeakDual 𝕜 E → E → 𝕜) '' polar 𝕜 s) :=
  isClosed_image_coe_of_bounded_of_closed (isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds)
    (isClosed_polar _ _)

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
  isCompact_of_bounded_of_closed (isBounded_polar_of_mem_nhds_zero 𝕜 s_nhds) (isClosed_polar _ _)

/-- The **Banach-Alaoglu theorem**: closed balls of the dual of a normed space `E` are compact in
the weak-star topology. -/
theorem isCompact_closedBall [ProperSpace 𝕜] (x' : StrongDual 𝕜 E) (r : ℝ) :
    IsCompact (toStrongDual ⁻¹' closedBall x' r) :=
  isCompact_of_bounded_of_closed isBounded_closedBall (isClosed_closedBall x' r)

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
    (hb : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' s)) (hc : IsClosed s) :
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
    (NormedSpace.isBounded_polar_of_mem_nhds_zero 𝕜 s_nhd) (isClosed_polar _ _)

/-- The **Sequential Banach-Alaoglu theorem**: closed balls of the dual of a separable
normed space `V` are sequentially compact in the weak-* topology. -/
theorem isSeqCompact_closedBall (x' : StrongDual 𝕜 V) (r : ℝ) :
    IsSeqCompact (toStrongDual ⁻¹' Metric.closedBall x' r) :=
  isSeqCompact_of_isBounded_of_isClosed 𝕜 V Metric.isBounded_closedBall
    (isClosed_closedBall x' r)

end WeakDual

end
section Goldstine

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]



open NormedSpace Metric
open scoped BigOperators


theorem Helly {I : Type*} [Fintype I] (f : I → StrongDual 𝕜 E) (α : I → 𝕜) (r : ℝ) :
    (∀ {ε : ℝ} (hε : 0 < ε), ∃ x : E, ‖x‖ ≤ r + ε ∧ ∀ i, f i x = α i) ↔
    (∀ β : I → 𝕜, ‖∑ i : I, β i * α i‖ ≤ r * ‖∑ i : I, β i • f i‖) := sorry

-- #synth Module 𝕜 E (restate without `ε`?) -- I might be implicit below
theorem three (I : Type*) [Fintype I] (φ : StrongDual 𝕜 (StrongDual 𝕜 E)) {ε : ℝ} (hε : 0 < ε)
    (f : I → StrongDual 𝕜 E) : ∃ x : E, ‖x‖ ≤ ‖φ‖ + ε ∧ ∀ i, f i (x) = φ (f i) := by
  apply (Helly 𝕜 f (fun i ↦ φ (f i)) ‖φ‖).mpr _ hε
  intro β
  calc ‖∑ i, β i * φ (f i)‖ = ‖φ (∑ i, β i • f i)‖ := by simp
                          _ ≤ ‖φ‖ * ‖∑ i, β i • f i‖ := ContinuousLinearMap.le_opNorm ..

-- #synth Module 𝕜 E (restate without `ε`?) -- I might be implicit below
theorem three' (I : Type*) [Fintype I] (φ : StrongDual 𝕜 (StrongDual 𝕜 E)) {ε : ℝ} (hε : 0 < ε)
    (f : I → StrongDual 𝕜 E) : ∃ x : E, ‖x‖ ≤ 1 ∧ ∀ i, ‖f i x - φ (f i)‖ < ε := by
  sorry

theorem aux : IsClosed (X := WeakDual 𝕜 (StrongDual 𝕜 E))
    (inclusionInDoubleDual 𝕜 E '' closedBall 0 1) := by
  sorry
  -- apply WeakDual.isClosed_closedBall


/-- Goldstine Lemma: the image along `inclusionInDoubleDual` of the (unit) ball of `E` is dense in
the unit sphere of the double dual.
See [K. Yosida, "Functional Analysis", Chap IV, 8, Corollary to Theorem 3]. -/
-- **RENAME!!!**
theorem goldstine : closure (X := WeakDual 𝕜 (StrongDual 𝕜 E))
    (inclusionInDoubleDual 𝕜 E '' closedBall 0 1)
    = closedBall (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 := by
  -- have uno := @LinearMap.weakBilin_withSeminorms 𝕜 (StrongDual 𝕜 E) E _ _ _ _ _
  --   (topDualPairing 𝕜 E)
  -- let F := (topDualPairing 𝕜 (StrongDual 𝕜 E)).toSeminormFamily
  -- let f := F 0
  set B' := topDualPairing 𝕜 (StrongDual 𝕜 E) with hB'
  let F' := LinearMap.toSeminormFamily B'
  -- let B := (topDualPairing 𝕜 E) This, I don't care
  -- let Estar' := WeakBilin B'
  -- let f : Estar' → StrongDual 𝕜 (StrongDual 𝕜 E) := fun x ↦ x
  -- let Estar'₀ := WeakDual 𝕜 (StrongDual 𝕜 E)
  -- let Estar'₁ := WeakDual 𝕜 E This is the weak top on E* not on E**
  -- let g₀ : Estar'₀ → StrongDual 𝕜 (StrongDual 𝕜 E) := fun x ↦ x
  have uno : WithSeminorms (𝕜 := 𝕜) (E := WeakDual 𝕜 (StrongDual 𝕜 E)) F' := by
    apply LinearMap.weakBilin_withSeminorms
  -- have due'' := uno.hasBasis_zero_ball
  -- have due' := uno.mem_nhds_iff
  ext ξ
  have due := uno.hasBasis_ball (x := ξ)
  -- have tre' := mem_closure_iff_nhds_basis (X := WeakDual 𝕜 (StrongDual 𝕜 E))
  --   (t := (inclusionInDoubleDual 𝕜 E '' closedBall 0 1)) due'' --ci siamo quasi
  -- -- above, use mem_closure_iff_nhds_basis nhds_basis_ball
  -- have brez := mem_closure_iff_nhds (X := WeakDual 𝕜 (StrongDual 𝕜 E))
  --   (s := (inclusionInDoubleDual 𝕜 E '' closedBall 0 1)) (x := ξ)
  -- rw [brez]
  -- refine ⟨fun hξ ↦ ?_, fun hξ U hU ↦ ?_⟩
  -- · sorry
  -- ·

--
  have tre := mem_closure_iff_nhds_basis' (X := WeakDual 𝕜 (StrongDual 𝕜 E))
    (t := (inclusionInDoubleDual 𝕜 E '' closedBall 0 1)) due --ci siamo quasi
  rw [tre]
  refine ⟨fun hξ ↦ ?_, fun hξ ⟨I, ε⟩ hε ↦ ?_⟩
  · sorry
  · obtain ⟨y, hy_le, hy_eq⟩ := three' 𝕜 I ξ hε (·)
    refine ⟨inclusionInDoubleDual 𝕜 E y, ?_, ⟨y, by simp [hy_le], rfl⟩⟩
    · --simp only at hy_le --useless of course
      simp only [Seminorm.mem_ball]
      apply Seminorm.finset_sup_apply_lt hε
      intro i hi
      -- simp only --remove
      replace hy_eq := hy_eq ⟨i, hi⟩
      rw [LinearMap.toSeminormFamily_apply]
      simp only [map_sub, LinearMap.sub_apply, gt_iff_lt]
      have repl_ξ := @topDualPairing_apply 𝕜 _ _ _ _ _ _ _ _ ξ i
      have repl_iDD := @topDualPairing_apply 𝕜 _ _ _ _ _ _ _ _ (inclusionInDoubleDual 𝕜 E y) i
      -- rw [hB']
      erw [repl_ξ, repl_iDD] --not very nice, probably related to `(·)`
      exact hy_eq

      -- simp only at hy_eq
--
--       set ξ' : StrongDual 𝕜 (StrongDual 𝕜 E):= by
--         use ξ
--         exact map_continuous ξ with hξ'
--         -- not really nice...
--       set v : StrongDual 𝕜 E →L[𝕜] 𝕜 := (inclusionInDoubleDual 𝕜 E) y - ξ' with hv
--       erw [← hv]
--       convert_to (⨆ i : I, F' i) v < ε
--       rw [Seminorm.coe_iSup_eq]
--       have := @Seminorm.iSup_apply 𝕜 _ _ _ _ I (fun i ↦ F' i) ?_ v
--       -- rw [hξ']
--       -- simp_rw [Finset.sup_eq_iSup]
--       -- simp at this
--
--         -- (x := ((inclusionInDoubleDual 𝕜 E) y - ξ))
--       -- rw [this]
--       -- simp only [Set.mem_image, mem_closedBall, dist_zero_right]
--       -- refine ⟨y, ?_, rfl⟩
--       -- sorry -- use somewhere hy.1
--     · simp
--       sorry -- use somewhere hy.2


end Goldstine
