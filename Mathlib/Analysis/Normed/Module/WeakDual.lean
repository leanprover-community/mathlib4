/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.Uniform
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Algebra.Module.LinearMap
public import Mathlib.Analysis.LocallyConvex.WeakDual --minimize imports
public import Mathlib.Analysis.Normed.Module.Dual
public import Mathlib.Analysis.Normed.Operator.Completeness
public import Mathlib.Topology.Algebra.Module.WeakDual
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.Analysis.LocallyConvex.Separation
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
* [H. Brezis, *Functional Analysis, Sobolev spaces, and partial differential equations*][brezis2011]

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
variable (𝕜₁ : Type*) [NontriviallyNormedField 𝕜₁]
variable {E₁ : Type*} [SeminormedAddCommGroup E₁] [NormedSpace 𝕜₁ E₁]

open Metric NormedSpace Function ContinuousLinearMap Pointwise Topology

open scoped BigOperators Topology

/- Move the next two lemmas above, checking hp-/
lemma IsClosed_image_ball [CompleteSpace E] : IsClosed
    ((inclusionInDoubleDual 𝕜 E) '' closedBall 0 1) :=
  inclusionInDoubleDualLi 𝕜 (E := E).isometry.isClosedEmbedding.isClosedMap _ isClosed_closedBall

lemma WeakClosure_subset_closedBall {s : Set (StrongDual 𝕜₁ (StrongDual 𝕜₁ E₁))}
    {c : (StrongDual 𝕜₁ (StrongDual 𝕜₁ E₁))} {ε : ℝ} (hs : s ⊆ closedBall c ε) :
    letI 𝒯 : TopologicalSpace (WeakDual 𝕜₁ (StrongDual 𝕜₁ E₁)) := inferInstance
    (closure[𝒯] s) ⊆ closedBall (α := ((StrongDual 𝕜₁ (StrongDual 𝕜₁ E₁)))) c ε :=
  closure_minimal hs (WeakDual.isClosed_closedBall ..)


theorem Helly_opp {I : Type*} [Fintype I] (f : I → StrongDual 𝕜₁ E₁) (α : I → 𝕜₁) :
    (∀ {ε : ℝ} (_ : 0 < ε), ∃ x : E₁, ‖x‖ ≤ 1 ∧ ∀ i, ‖f i x - α i‖ < ε) →
    (∀ β : I → 𝕜₁, ‖∑ i : I, β i * α i‖ ≤ ‖∑ i : I, β i • f i‖) := by
  intro h β
  · by_cases hβ : β = 0
    · simp [hβ]
    replace hβ : 0 < ∑ i, ‖β i‖ := by
      apply Finset.sum_pos' (s := Finset.univ) (fun i _ ↦ norm_nonneg (β i))
      simpa [← not_forall, ← funext_iff]
    apply le_of_forall_pos_le_add
    intro ε hε
    set ε' := ε * (∑ i, ‖β i‖)⁻¹ with hε'
    obtain ⟨x, hx_le, h_lt⟩ := h (ε := ε') (by positivity)
    have : ‖(∑ i, β i * α i) - (∑ i, β i * (f i x))‖ ≤ ε' * ∑ i, ‖β i‖ := by
      grw [← Finset.sum_sub_distrib, Finset.mul_sum, norm_sum_le]
      apply Finset.sum_le_sum (fun i _ ↦ ?_)
      rw [← mul_sub, norm_mul, mul_comm, ← norm_neg, neg_sub]
      exact mul_le_mul_of_nonneg_right (le_of_lt (h_lt i)) <| norm_nonneg (β i)
    calc ‖(∑ i, β i * α i)‖ ≤ ‖(∑ i, β i * α i) - (∑ i, β i * (f i x))‖ + ‖∑ i, β i * (f i x)‖ := by
                                  apply norm_le_norm_sub_add
        _ ≤ ‖∑ i : I, β i * (f i x)‖ + ε' * ∑ i : I, ‖β i‖ := by
                grw [this, add_comm, add_le_add_left]
                rfl
        _ ≤ ‖∑ i : I, β i • f i‖ + ε' * ∑ i : I, ‖β i‖ := by
                grw [add_le_add_left]
                erw [← sum_apply Finset.univ (fun i ↦ β i • f i) x]
                exact ContinuousLinearMap.unit_le_opNorm _ _ hx_le
        _ ≤ ‖∑ i : I, β i • f i‖ + ε := by
          rw [hε', mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/- Using `RCLike.geometric_hahn_banach_closed_point` can be extended to `RCLike`-/
theorem Helly {I : Type*} [Fintype I] /- [DecidableEq I] -/ (f : I → StrongDual ℝ F) (γ : I → ℝ)
    (H : ∀ β : I → ℝ, ‖∑ i : I, β i * γ i‖ ≤ ‖∑ i : I, β i • f i‖) :
    ∀ {ε : ℝ} (_ : 0 < ε), ∃ x : F, ‖x‖ ≤ 1 ∧ ∀ i, ‖f i x - γ i‖ < ε := by
  classical
  let φ : F →ₗ[ℝ] (I → ℝ) :=
    { toFun := fun x ↦ (fun i ↦ f i x)
      map_add' (x y) := by simp [Pi.add_def]
      map_smul' := by simp [Pi.smul_def] }
  suffices hφ : γ ∈ closure (φ '' closedBall 0 1) by
    intro ε hε
    rw [Metric.mem_closure_iff] at hφ
    obtain ⟨t, ⟨x, hx_mem, rfl⟩, ht_dist⟩ := hφ ε hε
    refine ⟨x, mem_closedBall_zero_iff.mp hx_mem, fun i ↦ ?_⟩
    rw [dist_pi_lt_iff hε] at ht_dist
    specialize ht_dist i
    rw [dist_comm] at ht_dist
    congr
  by_contra h_abs
  obtain ⟨g, α, hg, hα⟩ := geometric_hahn_banach_closed_point
    ((convex_closedBall 0 1).linear_image φ).closure isClosed_closure h_abs
  let β : I → ℝ := fun i ↦ g (Pi.single i 1)
  have hleft (x : _) (hx : x ∈ closedBall 0 1) : (∑ i, β i • f i) x ≤ α := by
    apply le_of_lt <| lt_of_eq_of_lt _ <| hg (φ x) (subset_closure ⟨x, hx, rfl⟩)
    simp only [coe_sum', coe_smul', Finset.sum_apply, Pi.smul_apply, LinearMap.coe_mk,
      AddHom.coe_mk, β, φ]
    simp_rw [smul_eq_mul, mul_comm, ← smul_eq_mul]
    have h1 (i : I) : f i x • g ((Pi.single i 1) : I → ℝ) =
      g ((f i) x • ((Pi.single i 1) : I → ℝ)) := by
      simp-- [Eq.symm (map_smul_of_tower g ((f i) x) (Pi.single i 1))]
    -- have h2 (i : I) : (f i) x • ((Pi.single i (1 : ℝ)) : I → ℝ) =
    --   (Pi.single i ((f i) x) : I → ℝ):= by
    --   rw [← Pi.single_smul i ((f i) x) 1, smul_eq_mul, mul_one]
    simp_rw [h1, ← Pi.single_smul, smul_eq_mul, mul_one, ← map_sum,
      Finset.univ_sum_single fun i ↦ (f i) x]
  have hright : α < ∑ i, β i • γ i := by
    apply lt_of_lt_of_eq hα
    simp_rw [β, smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, ← map_sum]
    congr
    exact pi_eq_sum_univ' γ
  replace hleft (x : _) (hx : x ∈ closedBall 0 1) : ‖(∑ i, β i • f i) x‖ ≤ α := by
    rw [Real.norm_eq_abs, abs_eq_max_neg]
    apply max_le
    · exact hleft x hx
    · rw [← map_neg]
      apply hleft (-x)
      simp_all
  replace hleft : ‖∑ i, β i • f i‖ ≤ α := by
    refine ContinuousLinearMap.opNorm_le_of_unit_norm ?_ (fun x hx ↦ ?_)
    · apply le_trans (norm_nonneg _) <| hleft 0 (mem_closedBall_self (zero_le_one))
    · apply le_trans (hleft x (mem_closedBall_zero_iff.mpr (le_of_eq hx))) (by rfl)
  replace h : ‖∑ i, β i • f i‖ < ∑ i, β i • γ i := lt_of_le_of_lt hleft hright
  have uff : ∑ i, β i • γ i ≤ ‖∑ i, β i • γ i‖ := by
    exact Real.le_norm_self (∑ i, β i • γ i)
  replace uff : _ < _ := lt_of_lt_of_le h uff
  specialize H β
  exact not_le_of_gt uff H



-- #synth Module 𝕜 E (restate without `ε`?) -- I might be implicit below
theorem three (I : Type*) [Fintype I] {φ : StrongDual ℝ (StrongDual ℝ F)} (hφ : ‖φ‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε)
    (f : I → StrongDual ℝ F) : ∃ x : F, ‖x‖ ≤ 1 ∧ ∀ i, ‖f i x - φ (f i)‖ < ε := by
  apply Helly f (fun i ↦ φ (f i)) _ hε
  intro β
  calc ‖∑ i, β i * φ (f i)‖ = ‖φ (∑ i, β i • f i)‖ := by simp
                          _ ≤ ‖φ‖ * ‖∑ i, β i • f i‖ := ContinuousLinearMap.le_opNorm ..
                          _ ≤ ‖∑ i, β i • f i‖ := by grw [hφ, one_mul]

/-- Goldstine Lemma: the image along `inclusionInDoubleDual` of the (unit) ball of `E` is dense in
the unit sphere of the double dual. The result below is somewhat stronger, and it would be better
to move the inclusion back to `Normed.Module.Dual` and to keep here the full equality.

See [K. Yosida, "Functional Analysis", Chap IV, 8, Corollary to Theorem 3]. -/
-- **RENAME!!!**
theorem goldstine : letI 𝒯 : TopologicalSpace (WeakDual ℝ (StrongDual ℝ F)) := inferInstance
    closure[𝒯] (inclusionInDoubleDual ℝ F '' closedBall 0 1)
    = closedBall (0 : StrongDual ℝ (StrongDual ℝ F)) 1 := by
  have : (inclusionInDoubleDualLi ℝ (E := F)) '' closedBall 0 1 ⊆ closedBall 0 1 := by
    rw [Set.image_subset_iff]
    intro _ hx
    simp_all
  apply (WeakClosure_subset_closedBall _ this).antisymm
  -- have uno := @LinearMap.weakBilin_withSeminorms 𝕜 (StrongDual 𝕜 E) E _ _ _ _ _
  --   (topDualPairing 𝕜 E)
  -- let F := (topDualPairing 𝕜 (StrongDual 𝕜  E)).toSeminormFamily
  -- let f := F 0
  set B' := topDualPairing ℝ (StrongDual ℝ F) with hB'
  let F' := LinearMap.toSeminormFamily B'
  -- let B := (topDualPairing 𝕜 E) This, I don't care
  -- let Estar' := WeakBilin B'
  -- let f : Estar' → StrongDual 𝕜 (StrongDual 𝕜 E) := fun x ↦ x
  -- let Estar'₀ := WeakDual 𝕜 (StrongDual 𝕜 E)
  -- let Estar'₁ := WeakDual 𝕜 E This is the weak top on E* not on E**
  -- let g₀ : Estar'₀ → StrongDual 𝕜 (StrongDual 𝕜 E) := fun x ↦ x
  have uno : WithSeminorms (𝕜 := ℝ) (E := WeakDual ℝ (StrongDual ℝ F)) F' := by
    apply LinearMap.weakBilin_withSeminorms
  -- have due'' := uno.hasBasis_zero_ball
  -- have due' := uno.mem_nhds_iff
  intro ξ hξ
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
  have tre := mem_closure_iff_nhds_basis' (X := WeakDual ℝ (StrongDual ℝ F))
    (t := (inclusionInDoubleDualLi ℝ (E := F) '' closedBall 0 1)) due --ci siamo quasi
  rw [tre]
  rintro ⟨I, ε⟩ hε
  -- refine ⟨fun hξ ↦ ?_, fun hξ ⟨I, ε⟩ hε ↦ ?_⟩
  -- · sorry
  · simp only [mem_closedBall] at hξ
    obtain ⟨y, hy_le, hy_eq⟩ := three I hξ hε (·)
    refine ⟨inclusionInDoubleDual ℝ F y, ?_, ⟨y, by simp [hy_le], rfl⟩⟩
    · --simp only at hy_le --useless of course
      simp only [Seminorm.mem_ball]
      apply Seminorm.finset_sup_apply_lt hε
      intro i hi
      -- simp only --remove
      replace hy_eq := sub_zero (a := ξ) ▸ hy_eq ⟨i, hi⟩
      rw [LinearMap.toSeminormFamily_apply]
      simp only [map_sub, LinearMap.sub_apply, gt_iff_lt]
      have repl_ξ := @topDualPairing_apply ℝ _ _ _ _ _ _ _ _ ξ i
      have repl_iDD := @topDualPairing_apply ℝ _ _ _ _ _ _ _ _ (inclusionInDoubleDual ℝ F y) i
      -- rw [hB']
      erw [repl_ξ, repl_iDD] --not very nice, probably related to `(·)`
      exact hy_eq



end Goldstine
