/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.polish
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.MetricSpace.PiNat
import Mathbin.Topology.MetricSpace.Isometry
import Mathbin.Topology.MetricSpace.Gluing
import Mathbin.Analysis.Normed.Field.Basic

/-!
# Polish spaces

A topological space is Polish if its topology is second-countable and there exists a compatible
complete metric. This is the class of spaces that is well-behaved with respect to measure theory.
In this file, we establish the basic properties of Polish spaces.

## Main definitions and results

* `polish_space α` is a mixin typeclass on a topological space, requiring that the topology is
  second-countable and compatible with a complete metric. To endow the space with such a metric,
  use in a proof `letI := upgrade_polish_space α`.
  We register an instance from complete second-countable metric spaces to Polish spaces, not the
  other way around.
* We register that countable products and sums of Polish spaces are Polish.
* `is_closed.polish_space`: a closed subset of a Polish space is Polish.
* `is_open.polish_space`: an open subset of a Polish space is Polish.
* `exists_nat_nat_continuous_surjective`: any nonempty Polish space is the continuous image
  of the fundamental Polish space `ℕ → ℕ`.

A fundamental property of Polish spaces is that one can put finer topologies, still Polish,
with additional properties:

* `exists_polish_space_forall_le`: on a topological space, consider countably many topologies
  `t n`, all Polish and finer than the original topology. Then there exists another Polish
  topology which is finer than all the `t n`.
* `is_clopenable s` is a property of a subset `s` of a topological space, requiring that there
  exists a finer topology, which is Polish, for which `s` becomes open and closed. We show that
  this property is satisfied for open sets, closed sets, for complements, and for countable unions.
  Once Borel-measurable sets are defined in later files, it will follow that any Borel-measurable
  set is clopenable. Once the Lusin-Souslin theorem is proved using analytic sets, we will even
  show that a set is clopenable if and only if it is Borel-measurable, see
  `is_clopenable_iff_measurable_set`.
-/


noncomputable section

open Classical Topology Filter

open TopologicalSpace Set Metric Filter Function

variable {α : Type _} {β : Type _}

/-! ### Basic properties of Polish spaces -/


/- ./././Mathport/Syntax/Translate/Command.lean:388:30: infer kinds are unsupported in Lean 4: #[`second_countable] [] -/
/-- A Polish space is a topological space with second countable topology, that can be endowed
with a metric for which it is complete.
We register an instance from complete second countable metric space to polish space, and not the
other way around as this is the most common use case.

To endow a Polish space with a complete metric space structure, do `letI := upgrade_polish_space α`.
-/
class PolishSpace (α : Type _) [h : TopologicalSpace α] : Prop where
  second_countable : SecondCountableTopology α
  complete :
    ∃ m : MetricSpace α, m.toUniformSpace.toTopologicalSpace = h ∧ @CompleteSpace α m.toUniformSpace
#align polish_space PolishSpace

/-- A convenience class, for a Polish space endowed with a complete metric. No instance of this
class should be registered: It should be used as `letI := upgrade_polish_space α` to endow a Polish
space with a complete metric. -/
class UpgradedPolishSpace (α : Type _) extends MetricSpace α, SecondCountableTopology α,
  CompleteSpace α
#align upgraded_polish_space UpgradedPolishSpace

instance (priority := 100) polishSpace_of_complete_second_countable [m : MetricSpace α]
    [h : SecondCountableTopology α] [h' : CompleteSpace α] : PolishSpace α
    where
  second_countable := h
  complete := ⟨m, rfl, h'⟩
#align polish_space_of_complete_second_countable polishSpace_of_complete_second_countable

/-- Construct on a Polish space a metric (compatible with the topology) which is complete. -/
def polishSpaceMetric (α : Type _) [ht : TopologicalSpace α] [h : PolishSpace α] : MetricSpace α :=
  h.complete.some.replaceTopology h.complete.choose_spec.1.symm
#align polish_space_metric polishSpaceMetric

theorem complete_polishSpaceMetric (α : Type _) [ht : TopologicalSpace α] [h : PolishSpace α] :
    @CompleteSpace α (polishSpaceMetric α).toUniformSpace :=
  by
  convert h.complete.some_spec.2
  exact MetricSpace.replaceTopology_eq _ _
#align complete_polish_space_metric complete_polishSpaceMetric

/-- This definition endows a Polish space with a complete metric. Use it as:
`letI := upgrade_polish_space α`. -/
def upgradePolishSpace (α : Type _) [ht : TopologicalSpace α] [h : PolishSpace α] :
    UpgradedPolishSpace α :=
  letI := polishSpaceMetric α
  { complete_polishSpaceMetric α, PolishSpace.second_countable α with }
#align upgrade_polish_space upgradePolishSpace

namespace PolishSpace

instance (priority := 100) t2Space (α : Type _) [TopologicalSpace α] [PolishSpace α] : T2Space α :=
  by
  letI := upgradePolishSpace α
  infer_instance
#align polish_space.t2_space PolishSpace.t2Space

/-- A countable product of Polish spaces is Polish. -/
instance pi_countable {ι : Type _} [Countable ι] {E : ι → Type _} [∀ i, TopologicalSpace (E i)]
    [∀ i, PolishSpace (E i)] : PolishSpace (∀ i, E i) :=
  by
  cases nonempty_encodable ι
  letI := fun i => upgradePolishSpace (E i)
  letI : MetricSpace (∀ i, E i) := PiCountable.metricSpace
  infer_instance
#align polish_space.pi_countable PolishSpace.pi_countable

/-- Without this instance, `polish_space (ℕ → ℕ)` is not found by typeclass inference. -/
instance nat_fun [TopologicalSpace α] [PolishSpace α] : PolishSpace (ℕ → α) := by infer_instance
#align polish_space.nat_fun PolishSpace.nat_fun

/-- A countable disjoint union of Polish spaces is Polish. -/
instance sigma {ι : Type _} [Countable ι] {E : ι → Type _} [∀ n, TopologicalSpace (E n)]
    [∀ n, PolishSpace (E n)] : PolishSpace (Σn, E n) :=
  by
  letI := fun n => upgradePolishSpace (E n)
  letI : MetricSpace (Σn, E n) := sigma.metric_space
  haveI : CompleteSpace (Σn, E n) := sigma.complete_space
  infer_instance
#align polish_space.sigma PolishSpace.sigma

/-- The disjoint union of two Polish spaces is Polish. -/
instance sum [TopologicalSpace α] [PolishSpace α] [TopologicalSpace β] [PolishSpace β] :
    PolishSpace (Sum α β) := by
  letI := upgradePolishSpace α
  letI := upgradePolishSpace β
  letI : MetricSpace (Sum α β) := metric_space_sum
  infer_instance
#align polish_space.sum PolishSpace.sum

/-- Any nonempty Polish space is the continuous image of the fundamental space `ℕ → ℕ`. -/
theorem exists_nat_nat_continuous_surjective (α : Type _) [TopologicalSpace α] [PolishSpace α]
    [Nonempty α] : ∃ f : (ℕ → ℕ) → α, Continuous f ∧ Surjective f :=
  letI := upgradePolishSpace α
  exists_nat_nat_continuous_surjective_of_completeSpace α
#align polish_space.exists_nat_nat_continuous_surjective PolishSpace.exists_nat_nat_continuous_surjective

/-- Given a closed embedding into a Polish space, the source space is also Polish. -/
theorem ClosedEmbedding.polishSpace [TopologicalSpace α] [TopologicalSpace β] [PolishSpace β]
    {f : α → β} (hf : ClosedEmbedding f) : PolishSpace α :=
  by
  letI := upgradePolishSpace β
  letI : MetricSpace α := hf.to_embedding.comap_metric_space f
  haveI : second_countable_topology α := hf.to_embedding.second_countable_topology
  have : CompleteSpace α :=
    by
    rw [completeSpace_iff_isComplete_range hf.to_embedding.to_isometry.uniform_inducing]
    apply IsClosed.isComplete
    exact hf.closed_range
  infer_instance
#align closed_embedding.polish_space ClosedEmbedding.polishSpace

/-- Pulling back a Polish topology under an equiv gives again a Polish topology. -/
theorem Equiv.polishSpace_induced [t : TopologicalSpace β] [PolishSpace β] (f : α ≃ β) :
    @PolishSpace α (t.induced f) :=
  letI : TopologicalSpace α := t.induced f
  (f.to_homeomorph_of_inducing ⟨rfl⟩).ClosedEmbedding.PolishSpace
#align equiv.polish_space_induced Equiv.polishSpace_induced

/-- A closed subset of a Polish space is also Polish. -/
theorem IsClosed.polishSpace {α : Type _} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsClosed s) : PolishSpace s :=
  (IsClosed.closedEmbedding_subtype_val hs).PolishSpace
#align is_closed.polish_space IsClosed.polishSpace

/-- A sequence of type synonyms of a given type `α`, useful in the proof of
`exists_polish_space_forall_le` to endow each copy with a different topology. -/
@[nolint unused_arguments has_nonempty_instance]
def AuxCopy (α : Type _) {ι : Type _} (i : ι) : Type _ :=
  α
#align polish_space.aux_copy PolishSpace.AuxCopy

/-- Given a Polish space, and countably many finer Polish topologies, there exists another Polish
topology which is finer than all of them. -/
theorem exists_polishSpace_forall_le {ι : Type _} [Countable ι] [t : TopologicalSpace α]
    [p : PolishSpace α] (m : ι → TopologicalSpace α) (hm : ∀ n, m n ≤ t)
    (h'm : ∀ n, @PolishSpace α (m n)) :
    ∃ t' : TopologicalSpace α, (∀ n, t' ≤ m n) ∧ t' ≤ t ∧ @PolishSpace α t' :=
  by
  rcases isEmpty_or_nonempty ι with (hι | hι)
  · exact ⟨t, fun i => (IsEmpty.elim hι i : _), le_rfl, p⟩
  inhabit ι
  /- Consider the product of infinitely many copies of `α`, each endowed with the topology `m n`.
    This is a Polish space, as a product of Polish spaces. Pulling back this topology under the
    diagonal embedding of `α`, one gets a Polish topology which is finer than all the `m n`. -/
  letI : ∀ n : ι, TopologicalSpace (aux_copy α n) := fun n => m n
  haveI : ∀ n : ι, PolishSpace (aux_copy α n) := fun n => h'm n
  letI T : TopologicalSpace (∀ n : ι, aux_copy α n) := by infer_instance
  let f : α → ∀ n : ι, aux_copy α n := fun x n => x
  -- show that the induced topology is finer than all the `m n`.
  have T_le_m : ∀ n, T.induced f ≤ m n := by
    intro n s hs
    refine' ⟨Set.pi ({n} : Set ι) fun i => s, _, _⟩
    · apply isOpen_set_pi (finite_singleton _)
      intro a ha
      rw [mem_singleton_iff.1 ha]
      exact hs
    · ext x
      simp only [singleton_pi, mem_preimage]
  refine' ⟨T.induced f, fun n => T_le_m n, (T_le_m default).trans (hm default), _⟩
  -- show that the new topology is Polish, as the pullback of a Polish topology under a closed
  -- embedding.
  have A : range f = ⋂ n, { x | x n = x default } :=
    by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_Inter.2 fun n => by simp only [mem_set_of_eq]
    · intro hx
      refine' ⟨x default, _⟩
      ext1 n
      symm
      exact (mem_Inter.1 hx n : _)
  have f_closed : IsClosed (range f) := by
    rw [A]
    apply isClosed_interᵢ fun n => _
    have C : ∀ i : ι, Continuous fun x : ∀ n, aux_copy α n => (id (x i) : α) :=
      by
      intro i
      apply Continuous.comp _ (continuous_apply i)
      apply continuous_def.2 fun s hs => _
      exact hm i s hs
    apply isClosed_eq (C n) (C default)
  have K : @_root_.embedding _ _ (T.induced f) T f :=
    by
    apply Function.Injective.embedding_induced
    intro x y hxy
    have : f x default = f y default := by rw [hxy]
    exact this
  have L : @ClosedEmbedding _ _ (T.induced f) T f :=
    by
    constructor
    · exact K
    · exact f_closed
  exact @ClosedEmbedding.polishSpace _ _ (T.induced f) T (by infer_instance) _ L
#align polish_space.exists_polish_space_forall_le PolishSpace.exists_polishSpace_forall_le

/-!
### An open subset of a Polish space is Polish

To prove this fact, one needs to construct another metric, giving rise to the same topology,
for which the open subset is complete. This is not obvious, as for instance `(0,1) ⊆ ℝ` is not
complete for the usual metric of `ℝ`: one should build a new metric that blows up close to the
boundary.
-/


section CompleteCopy

variable [MetricSpace α] {s : Set α}

/-- A type synonym for a subset `s` of a metric space, on which we will construct another metric
for which it will be complete. -/
@[nolint has_nonempty_instance]
def CompleteCopy {α : Type _} (s : Set α) : Type _ :=
  s
#align polish_space.complete_copy PolishSpace.CompleteCopy

/-- A distance on a subset `s` of a metric space, designed to make it complete if `s` is open.
It is given by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the second term
blows up close to the boundary to ensure that Cauchy sequences for `dist'` remain well
inside `s`. -/
def hasDistCompleteCopy (s : Set α) : Dist (CompleteCopy s) :=
  ⟨fun x y => dist x.1 y.1 + abs (1 / infDist x.1 (sᶜ) - 1 / infDist y.1 (sᶜ))⟩
#align polish_space.has_dist_complete_copy PolishSpace.hasDistCompleteCopy

attribute [local instance] has_dist_complete_copy

theorem dist_completeCopy_eq (x y : CompleteCopy s) :
    dist x y = dist x.1 y.1 + abs (1 / infDist x.1 (sᶜ) - 1 / infDist y.1 (sᶜ)) :=
  rfl
#align polish_space.dist_complete_copy_eq PolishSpace.dist_completeCopy_eq

theorem dist_le_dist_completeCopy (x y : CompleteCopy s) : dist x.1 y.1 ≤ dist x y :=
  (le_add_iff_nonneg_right _).2 (abs_nonneg _)
#align polish_space.dist_le_dist_complete_copy PolishSpace.dist_le_dist_completeCopy

/-- A metric space structure on a subset `s` of a metric space, designed to make it complete
if `s` is open. It is given by `dist' x y = dist x y + |1 / dist x sᶜ - 1 / dist y sᶜ|`, where the
second term blows up close to the boundary to ensure that Cauchy sequences for `dist'` remain well
inside `s`. -/
def completeCopyMetricSpace (s : Set α) : MetricSpace (CompleteCopy s)
    where
  dist_self x := by simp [dist_complete_copy_eq]
  dist_comm x y := by simp [dist_complete_copy_eq, dist_comm, abs_sub_comm]
  dist_triangle x y z :=
    calc
      dist x z = dist x.1 z.1 + abs (1 / infDist x.1 (sᶜ) - 1 / infDist z.1 (sᶜ)) := rfl
      _ ≤
          dist x.1 y.1 + dist y.1 z.1 +
            (abs (1 / infDist x.1 (sᶜ) - 1 / infDist y.1 (sᶜ)) +
              abs (1 / infDist y.1 (sᶜ) - 1 / infDist z.1 (sᶜ))) :=
        by
        rw [← Real.dist_eq, ← Real.dist_eq, ← Real.dist_eq]
        exact add_le_add (dist_triangle _ _ _) (dist_triangle _ _ _)
      _ = dist x y + dist y z :=
        by
        rw [dist_complete_copy_eq, dist_complete_copy_eq]
        abel
      
  eq_of_dist_eq_zero := by
    intro x y hxy
    apply Subtype.coe_injective
    refine' dist_le_zero.1 _
    rw [← hxy]
    exact dist_le_dist_complete_copy x y
#align polish_space.complete_copy_metric_space PolishSpace.completeCopyMetricSpace

attribute [local instance] complete_copy_metric_space

/-- The identity between the type synonym `complete_copy s` (with its modified metric) and the
original subtype `s` is a homeomorphism. -/
def completeCopyIdHomeo (hs : IsOpen s) (h's : sᶜ.Nonempty) : CompleteCopy s ≃ₜ s
    where
  toFun := id
  invFun := id
  left_inv x := rfl
  right_inv x := rfl
  continuous_toFun :=
    haveI : LipschitzWith 1 fun x : complete_copy s => (id x : s) :=
      by
      apply LipschitzWith.mk_one
      exact dist_le_dist_complete_copy
    this.continuous
  continuous_invFun := by
    apply continuous_iff_continuousAt.2 fun x => _
    suffices H :
      tendsto (fun b : s => dist b.1 x.1 + |1 / inf_dist b.1 (sᶜ) - 1 / inf_dist x.1 (sᶜ)|) (𝓝 x)
        (𝓝 (dist x.1 x.1 + abs (1 / inf_dist x.1 (sᶜ) - 1 / inf_dist x.1 (sᶜ))))
    · rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
      simpa only [sub_self, abs_zero, add_zero, dist_self] using H
    have I : 0 < inf_dist x.val (sᶜ) :=
      by
      rw [← hs.is_closed_compl.not_mem_iff_inf_dist_pos h's]
      simp
    apply tendsto.add
    · apply Continuous.tendsto
      exact continuous_subtype_coe.dist continuous_const
    · refine' (tendsto.sub_const _ _).abs
      refine' tendsto.div tendsto_const_nhds _ I.ne'
      exact ((continuous_inf_dist_pt _).comp continuous_subtype_val).Tendsto _
#align polish_space.complete_copy_id_homeo PolishSpace.completeCopyIdHomeo

theorem completeSpace_completeCopy [CompleteSpace α] (hs : IsOpen s) (h's : sᶜ.Nonempty) :
    CompleteSpace (CompleteCopy s) :=
  by
  refine' Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) (by simp) _
  intro u hu
  have A : CauchySeq fun n => (u n).1 :=
    by
    apply cauchySeq_of_le_tendsto_0 (fun n : ℕ => (1 / 2) ^ n) (fun n m N hNn hNm => _) _
    · exact (dist_le_dist_complete_copy (u n) (u m)).trans (hu N n m hNn hNm).le
    · exact tendsto_pow_atTop_nhds_0_of_lt_1 (by norm_num) (by norm_num)
  obtain ⟨x, xlim⟩ : ∃ x, tendsto (fun n => (u n).1) at_top (𝓝 x) :=
    haveI : Nonempty α := ⟨(u 0).1⟩
    ⟨_, A.tendsto_lim⟩
  suffices xs : x ∈ s
  · refine' ⟨⟨x, xs⟩, _⟩
    have L : tendsto (fun n => (id ⟨(u n).1, (u n).2⟩ : s)) at_top (𝓝 ⟨x, xs⟩) :=
      by
      apply embedding_subtype_coe.tendsto_nhds_iff.2
      exact xlim
    convert((complete_copy_id_homeo hs h's).symm.Continuous.Tendsto _).comp L
    ext1 n
    simp [complete_copy_id_homeo]
  obtain ⟨C, hC⟩ : ∃ C, ∀ n, 1 / inf_dist (u n).1 (sᶜ) < C :=
    by
    refine' ⟨(1 / 2) ^ 0 + dist (1 / inf_dist (u 0).1 (sᶜ)) 0, fun n => _⟩
    calc
      1 / inf_dist (u n).val (sᶜ) ≤ dist (1 / inf_dist (u n).val (sᶜ)) 0 :=
        by
        rw [Real.dist_0_eq_abs]
        exact le_abs_self _
      _ ≤
          dist (1 / inf_dist (u n).1 (sᶜ)) (1 / inf_dist (u 0).1 (sᶜ)) +
            dist (1 / inf_dist (u 0).1 (sᶜ)) 0 :=
        (dist_triangle _ _ _)
      _ ≤
          dist (u n).1 (u 0).1 + dist (1 / inf_dist (u n).1 (sᶜ)) (1 / inf_dist (u 0).1 (sᶜ)) +
            dist (1 / inf_dist (u 0).1 (sᶜ)) 0 :=
        (add_le_add (le_add_of_nonneg_left dist_nonneg) le_rfl)
      _ = dist (u n) (u 0) + dist (1 / inf_dist (u 0).1 (sᶜ)) 0 := rfl
      _ < (1 / 2) ^ 0 + dist (1 / inf_dist (u 0).1 (sᶜ)) 0 :=
        add_lt_add_right (hu 0 n 0 (zero_le _) le_rfl) _
      
  have Cpos : 0 < C := by
    apply lt_of_le_of_lt _ (hC 0)
    simp [inf_dist_nonneg]
  have I : ∀ n, 1 / C ≤ inf_dist (u n).1 (sᶜ) :=
    by
    intro n
    have : 0 < inf_dist (u n).val (sᶜ) :=
      by
      apply (hs.is_closed_compl.not_mem_iff_inf_dist_pos h's).1
      simp
    rw [div_le_iff' Cpos]
    exact (div_le_iff this).1 (hC n).le
  have I' : 1 / C ≤ inf_dist x (sᶜ) :=
    haveI : tendsto (fun n => inf_dist (u n).1 (sᶜ)) at_top (𝓝 (inf_dist x (sᶜ))) :=
      ((continuous_inf_dist_pt (sᶜ)).Tendsto x).comp xlim
    ge_of_tendsto' this I
  suffices x ∉ sᶜ by simpa
  apply (hs.is_closed_compl.not_mem_iff_inf_dist_pos h's).2 (lt_of_lt_of_le _ I')
  simp [Cpos]
#align polish_space.complete_space_complete_copy PolishSpace.completeSpace_completeCopy

/-- An open subset of a Polish space is also Polish. -/
theorem IsOpen.polishSpace {α : Type _} [TopologicalSpace α] [PolishSpace α] {s : Set α}
    (hs : IsOpen s) : PolishSpace s :=
  by
  rcases eq_empty_or_nonempty (sᶜ) with (h's | h's)
  · simp at h's
    apply IsClosed.polishSpace
    rw [h's]
    exact isClosed_univ
  · letI := upgradePolishSpace α
    haveI : CompleteSpace (complete_copy s) := complete_space_complete_copy hs h's
    haveI : second_countable_topology (complete_copy s) :=
      (complete_copy_id_homeo hs h's).Embedding.SecondCountableTopology
    exact (complete_copy_id_homeo hs h's).symm.ClosedEmbedding.PolishSpace
#align is_open.polish_space IsOpen.polishSpace

end CompleteCopy

/-! ### Clopenable sets in Polish spaces -/


/-- A set in a topological space is clopenable if there exists a finer Polish topology for which
this set is open and closed. It turns out that this notion is equivalent to being Borel-measurable,
but this is nontrivial (see `is_clopenable_iff_measurable_set`). -/
def IsClopenable [t : TopologicalSpace α] (s : Set α) : Prop :=
  ∃ t' : TopologicalSpace α, t' ≤ t ∧ @PolishSpace α t' ∧ is_closed[t'] s ∧ is_open[t'] s
#align polish_space.is_clopenable PolishSpace.IsClopenable

/-- Given a closed set `s` in a Polish space, one can construct a finer Polish topology for
which `s` is both open and closed. -/
theorem IsClosed.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α} (hs : IsClosed s) :
    IsClopenable s :=
  by
  /- Both sets `s` and `sᶜ` admit a Polish topology. So does their disjoint union `s ⊕ sᶜ`.
    Pulling back this topology by the canonical bijection with `α` gives the desired Polish
    topology in which `s` is both open and closed. -/
  haveI : PolishSpace s := hs.polish_space
  let t : Set α := sᶜ
  haveI : PolishSpace t := hs.is_open_compl.polish_space
  let f : α ≃ Sum s t := (Equiv.Set.sumCompl s).symm
  letI T : TopologicalSpace (Sum s t) := by infer_instance
  let t' : TopologicalSpace α := T.induced f
  let g := @Equiv.toHomeomorphOfInducing _ _ t' T f { induced := rfl }
  have A : g ⁻¹' range (Sum.inl : s → Sum s t) = s :=
    by
    ext x
    by_cases h : x ∈ s
    ·
      simp only [Equiv.Set.sumCompl_symm_apply_of_mem, h, mem_preimage, Equiv.toFun_as_coe,
        mem_range_self, Equiv.toHomeomorphOfInducing_apply]
    ·
      simp only [Equiv.Set.sumCompl_symm_apply_of_not_mem, h, not_false_iff, mem_preimage,
        Equiv.toHomeomorphOfInducing_apply, Equiv.toFun_as_coe, mem_range, exists_false]
  refine' ⟨t', _, f.polish_space_induced, _, _⟩
  · intro u hu
    change ∃ s' : Set (Sum (↥s) ↥t), T.is_open s' ∧ f ⁻¹' s' = u
    refine' ⟨f.symm ⁻¹' u, _, by simp only [Equiv.symm_symm, Equiv.symm_preimage_preimage]⟩
    refine' isOpen_sum_iff.2 ⟨_, _⟩
    · have : IsOpen ((coe : s → α) ⁻¹' u) := IsOpen.preimage continuous_subtype_val hu
      have : Sum.inl ⁻¹' (⇑f.symm ⁻¹' u) = (coe : s → α) ⁻¹' u :=
        by
        ext x
        simp only [Equiv.symm_symm, mem_preimage, Equiv.Set.sumCompl_apply_inl]
      rwa [this]
    · have : IsOpen ((coe : t → α) ⁻¹' u) := IsOpen.preimage continuous_subtype_val hu
      have : Sum.inr ⁻¹' (⇑f.symm ⁻¹' u) = (coe : t → α) ⁻¹' u :=
        by
        ext x
        simp only [Equiv.symm_symm, mem_preimage, Equiv.Set.sumCompl_apply_inr]
      rwa [this]
  · have : is_closed[t'] (g ⁻¹' range (Sum.inl : s → Sum s t)) :=
      by
      apply IsClosed.preimage
      · exact @Homeomorph.continuous _ _ t' _ g
      · exact isClosed_range_inl
    convert this
    exact A.symm
  · have : is_open[t'] (g ⁻¹' range (Sum.inl : s → Sum s t)) :=
      by
      apply IsOpen.preimage
      · exact @Homeomorph.continuous _ _ t' _ g
      · exact isOpen_range_inl
    convert this
    exact A.symm
#align is_closed.is_clopenable IsClosed.isClopenable

theorem IsClopenable.compl [TopologicalSpace α] {s : Set α} (hs : IsClopenable s) :
    IsClopenable (sᶜ) := by
  rcases hs with ⟨t, t_le, t_polish, h, h'⟩
  exact ⟨t, t_le, t_polish, @IsOpen.isClosed_compl α t s h', @IsClosed.isOpen_compl α t s h⟩
#align polish_space.is_clopenable.compl PolishSpace.IsClopenable.compl

theorem IsOpen.isClopenable [TopologicalSpace α] [PolishSpace α] {s : Set α} (hs : IsOpen s) :
    IsClopenable s := by simpa using hs.is_closed_compl.is_clopenable.compl
#align is_open.is_clopenable IsOpen.isClopenable

theorem IsClopenable.unionᵢ [t : TopologicalSpace α] [PolishSpace α] {s : ℕ → Set α}
    (hs : ∀ n, IsClopenable (s n)) : IsClopenable (⋃ n, s n) :=
  by
  choose m mt m_polish m_closed m_open using hs
  obtain ⟨t', t'm, -, t'_polish⟩ :
    ∃ t' : TopologicalSpace α, (∀ n : ℕ, t' ≤ m n) ∧ t' ≤ t ∧ @PolishSpace α t' :=
    exists_polish_space_forall_le m mt m_polish
  have A : is_open[t'] (⋃ n, s n) := by
    apply isOpen_unionᵢ
    intro n
    apply t'm n
    exact m_open n
  obtain ⟨t'', t''_le, t''_polish, h1, h2⟩ :
    ∃ t'' : TopologicalSpace α,
      t'' ≤ t' ∧ @PolishSpace α t'' ∧ is_closed[t''] (⋃ n, s n) ∧ is_open[t''] (⋃ n, s n) :=
    @IsOpen.isClopenable α t' t'_polish _ A
  exact ⟨t'', t''_le.trans ((t'm 0).trans (mt 0)), t''_polish, h1, h2⟩
#align polish_space.is_clopenable.Union PolishSpace.IsClopenable.unionᵢ

end PolishSpace

