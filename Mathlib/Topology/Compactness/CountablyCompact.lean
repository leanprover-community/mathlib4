/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek, Yongxi Lin
-/
module

public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Sequences

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.Perfect

/-!
# Countably compact sets

A set `A` in a topological space is **countably compact** if every countably generated proper
filter contained in `A` has a cluster point in `A`. Equivalently, every sequence in `A` has a
cluster point in `A`, and every countable open cover of `A` admits a finite subcover.

## Main definitions

* `IsCountablyCompact A`: `A` is countably compact (every countably generated proper filter
  contained in `A` has a cluster point in `A`).
* `CountablyCompactSpace E`: the whole space `E` is countably compact.

## Main results

* `IsCountablyCompact.elim_directed_cover`: for every countable open directed cover of a
  countably compact set, some single element of the cover contains the set.
* `IsCountablyCompact.elim_finite_subcover`: a countably compact set has a finite subcover for
  any countable open cover.
* `isCountablyCompact_iff_countable_open_cover`: countable compactness is equivalent to the
  finite subcover property for countable covers.
* `IsCompact.isCountablyCompact`: compact sets are countably compact.
* `IsSeqCompact.isCountablyCompact`: sequentially compact sets are countably compact.
* `IsCountablyCompact.isSeqCompact`: in a first-countable space, countable compactness implies
  sequential compactness.
* `IsCountablyCompact.exists_accPt_of_infinite`: every infinite subset of a countably compact
  set has an accumulation point in the set.
* `isCountablyCompact_iff_infinite_subset_has_accPt`: in a T₁ space, countable compactness is
  equivalent to the Bolzano–Weierstrass property (every infinite subset has an accumulation point).
* `IsLindelof.isCompact`: a countably compact Lindelöf set is compact.
* `IsCountablyCompact.image`: the continuous image of a countably compact set is countably compact.

## References

* [Engelking, *General Topology*][engelking1989]
-/

@[expose] public section

noncomputable section

open Set Filter Topology

variable {ι E F : Type*} [TopologicalSpace E] [TopologicalSpace F] {A B : Set E}

/-- A set `A` is countably compact if every countably generated proper filter `f` with
`f ≤ 𝓟 A` has a cluster point in `A`. -/
def IsCountablyCompact (A : Set E) : Prop :=
  ∀ ⦃f⦄ [NeBot f] [f.IsCountablyGenerated], f ≤ 𝓟 A → ∃ a ∈ A, ClusterPt a f

/-- A topological space is countably compact if every countably generated proper filter has a
cluster point. -/
class CountablyCompactSpace (E : Type*) [TopologicalSpace E] : Prop where
  isCountablyCompact_univ : IsCountablyCompact (Set.univ : Set E)

/-- The empty set is countably compact. -/
theorem isCountablyCompact_empty : IsCountablyCompact (∅ : Set E) :=
  fun _f _ _ hle => absurd (empty_mem_iff_bot.mp (le_principal_iff.mp hle)) NeBot.ne'

/-- A singleton set is countably compact. -/
theorem isCountablyCompact_singleton {x : E} : IsCountablyCompact ({x} : Set E) := fun _ _ _ hle ↦
  ⟨x, rfl, ClusterPt.of_le_nhds <| hle.trans (principal_singleton x ▸ pure_le_nhds x)⟩

/-- A closed subset of a countably compact set is countably compact. -/
theorem IsCountablyCompact.of_isClosed_subset (hA : IsCountablyCompact A) (hB : IsClosed B)
    (hBA : B ⊆ A) : IsCountablyCompact B := fun _f _ _ hle ↦
  let ⟨a, _, hac⟩ := hA (hle.trans (principal_mono.mpr hBA))
  ⟨a, isClosed_iff_clusterPt.mp hB a (hac.mono hle), hac⟩

/-- A set is countably compact if and only if every sequence eventually in it has a cluster point
in it. -/
theorem isCountablyCompact_iff_seq_clusterPt :
    IsCountablyCompact A ↔
      ∀ x : ℕ → E, (∀ᶠ n in atTop, x n ∈ A) → ∃ a ∈ A, MapClusterPt a atTop x where
  mp h x hx := h (tendsto_principal.mpr hx)
  mpr hA f _ _ hle := by
    obtain ⟨x, hx⟩ := f.exists_seq_tendsto
    obtain ⟨a, ha, hxa⟩ := hA x (by simpa using hx.mono_right hle)
    exact ⟨a, ha, hxa.clusterPt.mono hx⟩

alias ⟨IsCountablyCompact.seq_clusterPt,
  IsCountablyCompact.of_seq_clusterPt⟩ := isCountablyCompact_iff_seq_clusterPt

/-- For every countable open directed cover of a countably compact set, there exists a single
element of the cover which itself includes the set. -/
theorem IsCountablyCompact.elim_directed_cover [Countable ι] [Nonempty ι]
    (hA : IsCountablyCompact A) (U : ι → Set E) (hUo : ∀ i, IsOpen (U i))
    (hAU : A ⊆ ⋃ i, U i) (hdU : Directed (· ⊆ ·) U) : ∃ i, A ⊆ U i := by
  by_contra! h
  have hdir : Directed (· ≥ ·) fun i => 𝓟 (A \ U i) :=
    fun i j => (hdU i j).imp fun _ ⟨hi, hj⟩ => ⟨principal_mono.mpr <| diff_subset_diff_right hi,
      principal_mono.mpr <| diff_subset_diff_right hj⟩
  have : NeBot (⨅ i, 𝓟 (A \ U i)) :=
    iInf_neBot_of_directed' hdir fun i => (diff_nonempty.mpr (h i)).principal_neBot
  have hle : (⨅ i, 𝓟 (A \ U i)) ≤ 𝓟 A :=
    iInf_le_of_le ‹Nonempty ι›.some <| principal_mono.mpr diff_subset
  rcases hA hle with ⟨a, ha, hac⟩
  rcases mem_iUnion.mp (hAU ha) with ⟨k, hk⟩
  exact closure_minimal (fun _ hx => hx.2) (hUo k).isClosed_compl
    (hac.mono (iInf_le _ k)).mem_closure hk

/-- A countably compact set has a finite subcover for any countable open cover. -/
theorem IsCountablyCompact.elim_finite_subcover (hA : IsCountablyCompact A) [Countable ι]
    {U : ι → Set E} (hUo : ∀ i, IsOpen (U i)) (hAU : A ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i :=
  hA.elim_directed_cover _ (fun _ => isOpen_biUnion fun i _ => hUo i)
    (iUnion_eq_iUnion_finset U ▸ hAU)
    (directed_of_isDirected_le fun _ _ h => biUnion_subset_biUnion_left h)

/-- A set is countably compact if and only if every countable open cover has a finite subcover. -/
theorem isCountablyCompact_iff_countable_open_cover :
    IsCountablyCompact A ↔ ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
        ∃ t : Finset ℕ, A ⊆ ⋃ i ∈ t, U i where
  mp hA _ hUo hAU := hA.elim_finite_subcover hUo hAU
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    by_contra! hac
    let V : ℕ → Set E := fun n => (closure (x '' Ici n))ᶜ
    have hVmono : Monotone V := fun _ _ hmn =>
      compl_subset_compl.2 <| closure_mono <| image_mono <| Ici_subset_Ici.2 hmn
    simp only [mapClusterPt_atTop_iff_forall_mem_closure, not_forall] at hac
    have hAV : A ⊆ ⋃ n, V n := fun a haA => mem_iUnion.2 (hac a haA)
    obtain ⟨t, ht⟩ := h V (fun _ => isClosed_closure.isOpen_compl) hAV
    obtain ⟨N, hN⟩ := eventually_atTop.mp hx
    let m := max N (t.sup id)
    obtain ⟨j, hjt, hjV⟩ := mem_iUnion₂.mp (ht (hN m (le_max_left _ _)))
    have hxmV : x m ∈ V m := hVmono ((Finset.le_sup hjt).trans (le_max_right _ _)) hjV
    exact hxmV (subset_closure ⟨m, mem_Ici.mpr le_rfl, rfl⟩)

/-- A countably compact set has a finite subcover for any countable open cover indexed by a
subset. -/
theorem IsCountablyCompact.elim_finite_subcover_image (hA : IsCountablyCompact A)
    {b : Set ι} (hb : b.Countable) {U : ι → Set E} (hUo : ∀ i ∈ b, IsOpen (U i))
    (hAU : A ⊆ ⋃ i ∈ b, U i) : ∃ t ⊆ b, t.Finite ∧ A ⊆ ⋃ i ∈ t, U i := by
  have := hb.to_subtype
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun (i : b) ↦ hUo i i.prop) (by simpa using hAU)
  classical
  simp only [Subtype.forall', biUnion_eq_iUnion] at hUo hAU
  replace hb := hb.to_subtype
  obtain ⟨d, hd⟩ := hA.elim_finite_subcover hUo hAU
  refine ⟨Subtype.val '' (d : Set b), ?_, d.finite_toSet.image _, ?_⟩
  · simp
  · rwa [biUnion_image]

/-- Variant of `isCountablyCompact_iff_countable_open_cover` with `Set ℕ` instead of `Finset ℕ`. -/
theorem isCountablyCompact_iff_countable_open_cover' :
    IsCountablyCompact A ↔ ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
      ∃ t : Set ℕ, t.Finite ∧ A ⊆ ⋃ i ∈ t, U i := by
  simp [isCountablyCompact_iff_countable_open_cover, Finset.exists]

/-- A compact set is countably compact. -/
theorem IsCompact.isCountablyCompact (hA : IsCompact A) : IsCountablyCompact A :=
  fun _ _ _ hle => hA hle

/-- A compact space is countably compact. -/
instance instCompactSpaceCountablyCompactSpace
    {X : Type*} [TopologicalSpace X] [CompactSpace X] : CountablyCompactSpace X where
  isCountablyCompact_univ := isCompact_univ.isCountablyCompact

/-- A sequentially compact set is countably compact. -/
theorem IsSeqCompact.isCountablyCompact (hA : IsSeqCompact A) :
    IsCountablyCompact A := IsCountablyCompact.of_seq_clusterPt fun x hx => by
  obtain ⟨a, ha, φ, hφ, hφa⟩ := hA.subseq_of_frequently_in hx.frequently
  exact ⟨a, ha, hφa.mapClusterPt.of_comp hφ.tendsto_atTop⟩

/-- The continuous image of a countably compact set is countably compact. -/
theorem IsCountablyCompact.image (hA : IsCountablyCompact A)
    {f : E → F} (hf : Continuous f) : IsCountablyCompact (f '' A) := by
  intro l hl_nebot hl_count hle
  have : NeBot (l.comap f ⊓ 𝓟 A) :=
    comap_inf_principal_neBot_of_image_mem hl_nebot (le_principal_iff.mp hle)
  obtain ⟨x, hxA, hx⟩ := hA (f := l.comap f ⊓ 𝓟 A) inf_le_right
  have := (hx.mono inf_le_left).neBot
  exact ⟨f x, mem_image_of_mem f hxA, (hf.continuousAt.inf tendsto_comap).neBot⟩

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is countably compact if and
only if `s` is countably compact. -/
theorem Topology.IsInducing.isCountablyCompact_iff {f : E → F} (hf : IsInducing f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot Fc F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ A, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is countably compact if and
only if `s` is countably compact. -/
theorem Topology.IsEmbedding.isCountablyCompact_iff {f : E → F} (hf : IsEmbedding f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) :=
  hf.isInducing.isCountablyCompact_iff

theorem Subtype.isCountablyCompact_iff {p : E → Prop} {A : Set { x // p x }} :
    IsCountablyCompact A ↔ IsCountablyCompact ((↑) '' A : Set E) :=
  IsEmbedding.subtypeVal.isCountablyCompact_iff

theorem isCountablyCompact_iff_isCountablyCompact_univ :
    IsCountablyCompact A ↔ IsCountablyCompact (univ : Set A) := by
  rw [Subtype.isCountablyCompact_iff, image_univ, Subtype.range_coe]

theorem isCountablyCompact_univ_iff : IsCountablyCompact (univ : Set E) ↔ CountablyCompactSpace E :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem isCountablyCompact_iff_countablyCompactSpace :
    IsCountablyCompact A ↔ CountablyCompactSpace A :=
  isCountablyCompact_iff_isCountablyCompact_univ.trans isCountablyCompact_univ_iff

/-- If `x : ℕ → E` has no convergent subsequence, then `⋃ i, closure {x i}` is closed. -/
private lemma isClosed_of_not_tendsto {x : ℕ → E} [SequentialSpace E]
    (hx : ∀ (l : E) (φ : ℕ → ℕ), StrictMono φ → ¬Tendsto (x ∘ φ) atTop (𝓝 l)) :
    IsClosed (⋃ i, closure {x i}) := by
  refine IsSeqClosed.isClosed fun y l hy hy' => ?_
  by_cases! hm : ∃ m, ∃ᶠ n in atTop, y n ∈ closure {x m}
  · obtain ⟨m, pm⟩ := hm
    exact subset_iUnion _ m (isClosed_closure.mem_of_frequently_of_tendsto pm hy')
  · have (j : ℕ) : ∃ᶠ k in atTop, ∃ n ≥ j, y n ∈ closure {x k} := by
      refine frequently_atTop.2 fun a => ?_
      have := (Filter.eventually_all_finite (by simp : (Iic a).Finite)).2 fun i hi => hm i
      simp only [mem_Iic, eventually_atTop, ge_iff_le] at this
      obtain ⟨c, hc⟩ := this
      obtain ⟨b, hb⟩ := mem_iUnion.1 (hy (c + j))
      refine ⟨b, ?_, c + j, j.le_add_left c, hb⟩
      by_contra! hab
      simp_all [hc (c + j) (c.le_add_right j) b hab.le]
    obtain ⟨φ, hφ⟩ := extraction_forall_of_frequently this
    choose ψ hψ1 hψ2 using hφ.2
    have : Tendsto ψ atTop atTop := tendsto_atTop_mono hψ1 tendsto_id
    refine (hx l φ hφ.1 (Tendsto.specializes (hy'.comp this) (fun n => ?_))).elim
    exact specializes_iff_mem_closure.2 (hψ2 n)

/-- If a sequential space is countably compact, then it is sequentially compact. We follow the proof
in [kremsater1972sequential]. -/
instance [SequentialSpace E] [CountablyCompactSpace E] :
    SeqCompactSpace E := by
  -- We prove by contradiction. If `E` is not sequentially compact, then there exists a sequence
  -- `x : ℕ → E` with no convergent subsequence.
  by_contra
  simp only [seqCompactSpace_iff, IsSeqCompact, mem_univ, not_forall,
    true_and, not_exists, not_and, exists_const] at this
  obtain ⟨x, hx⟩ := this
  -- Consider the set `A = ⋃ i, closure {x i}`. It is closed by `isClosed_of_not_tendsto` and thus
  -- countably compact.
  let A := ⋃ i, closure {x i}
  have : IsCountablyCompact A :=
    (isCountablyCompact_univ_iff.2 inferInstance).of_isClosed_subset
      (isClosed_of_not_tendsto hx) (by simp)
  -- We use the countably compactness of `A` to find a cluster point `a`. Eventually `a` does not
  -- belong to the closure of `{x n}` as `x` has no convergent subsequence, and this contradicts `a`
  -- being a cluster point.
  obtain ⟨a, ha⟩ : ∃ a ∈ A, MapClusterPt a atTop x := by
    refine isCountablyCompact_iff_seq_clusterPt.1 this _ (.of_forall fun n => ?_)
    exact mem_iUnion_of_mem n <| subset_closure <| mem_singleton (x n)
  obtain ⟨k, hk⟩ : ∃ k, ∀ n > k, a ∉ closure {x n} := by
    by_contra!
    obtain ⟨φ, hφ1, hφ2⟩ := Nat.exists_strictMono_subsequence this
    refine hx a φ hφ1 (tendsto_atTop_nhds.2 fun U ha hUo => ⟨0, fun n _ => ?_⟩)
    simpa using mem_closure_iff.1 (hφ2 n) U hUo ha
  have : a ∉ ⋃ i, closure {x (i + (k + 1))} := by
    simpa [← iUnion_ge_eq_iUnion_nat_add (fun n => closure {x n}) (k + 1)] using
      fun i hi => hk i (Nat.lt_of_lt_of_eq hi rfl)
  apply this
  have := mapClusterPt_atTop_iff_forall_mem_closure.1 ha.2 (k + 1)
  suffices h : closure (x '' Ici (k + 1)) ⊆ ⋃ i, closure {x (i + (k + 1))} from h this
  refine (IsClosed.closure_subset_iff (isClosed_of_not_tendsto fun l φ hφ => ?_)).2 ?_
  · exact hx l _ ((strictMono_id.add_const _).comp hφ)
  · simp only [image_eq_iUnion, mem_Ici, iUnion_ge_eq_iUnion_nat_add _ (k + 1)]
    exact iUnion_mono fun i => subset_closure

/-- If `f : X → Y` is an embedding map, the image `f '' s` of a set `s` is sequentially compact
  if and only if `s` is sequentially compact. -/
theorem Topology.IsEmbedding.isSeqCompact_iff {f : E → F} (hf : IsEmbedding f) :
    IsSeqCompact A ↔ IsSeqCompact (f '' A) where
  mp hA x hx := by
    choose y hy using hx
    obtain ⟨a, ha, ⟨φ, hφ⟩⟩ := hA (fun n => (hy n).1)
    refine ⟨f a, mem_image_of_mem f ha, φ, hφ.1, ?_⟩
    suffices f ∘ y ∘ φ = x ∘ φ from this ▸ (hf.continuous.tendsto a).comp hφ.2
    grind
  mpr hA x hx := by
    obtain ⟨fa, hfa, ⟨φ, hφ⟩⟩ := hA (fun n => mem_image_of_mem f (hx n))
    choose a ha using hfa
    exact ⟨a, ha.1, φ, hφ.1, hf.tendsto_nhds_iff.2 (ha.2 ▸ hφ.2)⟩

theorem Subtype.isSeqCompact_iff {p : E → Prop} {A : Set { x // p x }} :
    IsSeqCompact A ↔ IsSeqCompact ((↑) '' A : Set E) :=
  IsEmbedding.subtypeVal.isSeqCompact_iff

theorem isSeqCompact_iff_isSeqCompact_univ : IsSeqCompact A ↔ IsSeqCompact (univ : Set A) := by
  rw [Subtype.isSeqCompact_iff, image_univ, Subtype.range_coe]

theorem isSeqCompact_univ_iff : IsSeqCompact (univ : Set E) ↔ SeqCompactSpace E :=
  ⟨fun h => ⟨h⟩, fun h => h.1⟩

theorem isSeqCompact_iff_seqCompactSpace : IsSeqCompact A ↔ SeqCompactSpace A :=
  isSeqCompact_iff_isSeqCompact_univ.trans isSeqCompact_univ_iff

/-- A sequentially compact space is countably compact. -/
instance instSeqCompactSpaceCountablyCompactSpace
    {X : Type*} [TopologicalSpace X] [SeqCompactSpace X] : CountablyCompactSpace X where
  isCountablyCompact_univ := isSeqCompact_univ.isCountablyCompact

/-- In a first-countable space, a countably compact set is sequentially compact. -/
theorem IsCountablyCompact.isSeqCompact [FirstCountableTopology E]
    (hA : IsCountablyCompact A) : IsSeqCompact A :=
  have : CountablyCompactSpace A := isCountablyCompact_iff_countablyCompactSpace.1 hA
  isSeqCompact_iff_seqCompactSpace.2 inferInstance

/-- A first-countable countably compact space is sequentially compact. -/
instance instCountablyCompactSpaceSeqCompactSpace {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [CountablyCompactSpace X] : SeqCompactSpace X where
  isSeqCompact_univ := CountablyCompactSpace.isCountablyCompact_univ.isSeqCompact

/-- In a first-countable space, a set is countably compact iff it is sequentially compact. -/
theorem isCountablyCompact_iff_isSeqCompact [FirstCountableTopology E] :
    IsCountablyCompact A ↔ IsSeqCompact A :=
  ⟨fun h => h.isSeqCompact, fun h => h.isCountablyCompact⟩

/-- Every infinite subset of a countably compact set has an accumulation point in the set. -/
theorem IsCountablyCompact.exists_accPt_of_infinite
    (hA : IsCountablyCompact A) (hBA : B ⊆ A) (hB : B.Infinite) :
    ∃ a ∈ A, AccPt a (𝓟 B) := by
  let f := hB.natEmbedding
  let x : ℕ → E := (↑) ∘ f
  have hx_inj : Function.Injective x := Subtype.val_injective.comp f.injective
  obtain ⟨a, haA, hac⟩ :=
    IsCountablyCompact.seq_clusterPt hA x (Eventually.of_forall (fun n => hBA (f n).2))
  refine ⟨a, haA, accPt_iff_clusterPt.2 <| ClusterPt.mono hac <| le_inf ?_ ?_⟩
  · exact tendsto_principal.mpr <| Nat.cofinite_eq_atTop ▸
      ((Set.finite_singleton a).preimage hx_inj.injOn).compl_mem_cofinite
  · exact tendsto_principal.mpr <| Eventually.of_forall fun n => (f n).2

/-- In a `T₁` space, a set is countably compact if and only if every infinite subset has an
accumulation point in the set. -/
theorem isCountablyCompact_iff_infinite_subset_has_accPt [T1Space E] {A : Set E} :
    IsCountablyCompact A ↔ ∀ B ⊆ A, B.Infinite → ∃ a ∈ A, AccPt a (𝓟 B) where
  mp hA _ hBA hB := hA.exists_accPt_of_infinite hBA hB
  mpr h := by
    refine IsCountablyCompact.of_seq_clusterPt fun x hx => ?_
    rw [← Nat.cofinite_eq_atTop] at hx ⊢
    by_cases! hfin : (Set.range x).Finite
    · -- Case 1: Finite range
      suffices ∃ a ∈ range x ∩ A, MapClusterPt a cofinite x by aesop
      exact hfin.inter_of_left A |>.isCompact.exists_mapClusterPt_of_frequently <|
        hx.frequently.mp (by simp)
    · -- Case 2: Infinite range
      obtain ⟨a, haA, hacc⟩ := h (Set.range x ∩ A) inter_subset_right <| by
        rw [eventually_iff, mem_cofinite, compl_setOf] at hx
        exact hfin.inter_of_finite_diff (hx.image x |>.subset (by grind))
      refine ⟨a, haA, ?_⟩
      simp_rw [mapClusterPt_iff_frequently, frequently_cofinite_iff_infinite]
      exact fun s hs ↦ Infinite.of_accPt (hacc.nhds_inter hs) |>.mono (by grind) |>.of_image x

/-- A countably compact Lindelöf set is compact. -/
theorem IsLindelof.isCompact (hA : IsCountablyCompact A) (hl : IsLindelof A) :
    IsCompact A := by
  refine isCompact_of_finite_subcover fun {ι} U hUo hAU => ?_
  by_cases! h : Nonempty ι
  · obtain ⟨f, hf⟩ := hl.indexed_countable_subcover U hUo hAU
    obtain ⟨t, ht⟩ := isCountablyCompact_iff_countable_open_cover.1 hA (U ∘ f)
      (fun n => hUo (f n)) hf
    classical
    exact ⟨t.image f, by simp_all⟩
  · exact ⟨∅, by simp_all⟩

/-- A countably compact Lindelöf space is compact. -/
theorem LindelofSpace.CompactSpace {X : Type*} [TopologicalSpace X]
    [LindelofSpace X] [h : CountablyCompactSpace X] : CompactSpace X where
  isCompact_univ := isLindelof_univ.isCompact h.isCountablyCompact_univ

/-- In a Hereditarily Lindelöf space, a countably compact set is compact. -/
theorem IsCountablyCompact.isCompact [HereditarilyLindelofSpace E]
    (hA : IsCountablyCompact A) : IsCompact A :=
  (HereditarilyLindelofSpace.isLindelof A).isCompact hA

/-- The union of two countably compact sets is countably compact. -/
theorem IsCountablyCompact.union (hA : IsCountablyCompact A) (hB : IsCountablyCompact B) :
    IsCountablyCompact (A ∪ B) := by
  rw [isCountablyCompact_iff_countable_open_cover'] at hA hB ⊢
  intro U hUo hAU
  obtain ⟨t₁, ht₁, hA_sub⟩ : ∃ (t₁ : Set ℕ), t₁.Finite ∧ A ⊆ ⋃ k ∈ t₁, U k :=
    hA U hUo (subset_union_left.trans hAU)
  obtain  ⟨t₂, ht₂, hB_sub⟩ : ∃ (t₂ : Set ℕ), t₂.Finite ∧ B ⊆ ⋃ k ∈ t₂, U k :=
    hB U hUo (subset_union_right.trans hAU)
  have h : (⋃ k ∈ t₁, U k) ∪ (⋃ k ∈ t₂, U k) = ⋃ k ∈ (t₁ ∪ t₂), U k := by ext; aesop
  exact ⟨t₁ ∪ t₂, ht₁.union ht₂, h ▸ union_subset_union hA_sub hB_sub⟩

/-- A finite union of countably compact sets is countably compact. -/
theorem Finset.isCountablyCompact_biUnion (s : Finset ι) {f : ι → Set E}
    (hf : ∀ i ∈ s, IsCountablyCompact (f i)) :
    IsCountablyCompact (⋃ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isCountablyCompact_empty
  | @insert a s ha ih => simpa [Finset.biUnion_insert] using
    (hf a (Finset.mem_insert_self a s)).union <| ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite union of countably compact sets is countably compact. -/
theorem Set.Finite.isCountablyCompact_biUnion {s : Set ι} {f : ι → Set E} (hs : s.Finite)
    (hf : ∀ i ∈ s, IsCountablyCompact (f i)) : IsCountablyCompact (⋃ i ∈ s, f i) := by
  let s' : Finset ι := hs.toFinset
  have h1 : (⋃ i ∈ s, f i) = (⋃ i ∈ s', f i) := by simp [s']
  exact h1 ▸ Finset.isCountablyCompact_biUnion s' (fun i hi => hf i ((hs.mem_toFinset).mp hi))

/-- A finite union of countably compact sets is countably compact. -/
theorem Set.Finite.isCountablyCompact_sUnion {S : Set (Set E)} (hf : S.Finite)
    (hc : ∀ s ∈ S, IsCountablyCompact s) :
    IsCountablyCompact (⋃₀ S) := by
  rw [sUnion_eq_biUnion]; exact hf.isCountablyCompact_biUnion hc

/-- A finite union of countably compact sets is countably compact. -/
theorem isCountablyCompact_iUnion {ι : Sort*} {f : ι → Set E} [Finite ι]
    (h : ∀ i, IsCountablyCompact (f i)) :
    IsCountablyCompact (⋃ i, f i) :=
  (finite_range f).isCountablyCompact_sUnion <| forall_mem_range.2 h

end
