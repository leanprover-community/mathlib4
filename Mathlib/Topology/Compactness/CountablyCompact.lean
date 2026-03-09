/-
Copyright (c) 2026 Michał Świętek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Świętek, Yongxi Lin
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Topology.Separation.Basic
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Compactness.Lindelof

import Mathlib.Data.Fintype.Pigeonhole

/-!
A set `A` in a topological space is **countably compact** if every countably generated proper
filter contained in `A` has a cluster point in `A`. Equivalently, every sequence in `A` has a
cluster point in `A`, and every countable open cover of `A` admits a finite subcover.

## Main definitions

* `IsCountablyCompact A`: `A` is countably compact (every countably generated proper filter
  contained in `A` has a cluster point in `A`).
* `CountablyCompactSpace E`: the whole space `E` is countably compact.

## Main results

* `IsCountablyCompact.elim_finite_subcover`: a countably compact set has a finite subcover for
  any countable open cover.
* `isCountablyCompact_iff_countable_open_cover`: countable compactness is equivalent to the
  finite subcover property for countable covers.
* `IsCompact.IsCountablyCompact`: compact sets are countably compact.
* `IsSeqCompact.IsCountablyCompact`: sequentially compact sets are countably compact.
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
* [Kremsater, *Sequential Space Methods*][kremsater1972sequential]
-/

@[expose] public section

noncomputable section

open Set Filter Topology

variable {ι E F : Type*} [TopologicalSpace E] [TopologicalSpace F] {A B : Set E}

/-- A set `A` is countably compact if every countably generated proper filter `f` with
`f ≤ 𝓟 A` has a cluster point in `A`. -/
def IsCountablyCompact (A : Set E) : Prop :=
  ∀ ⦃f⦄ [NeBot f] [Filter.IsCountablyGenerated f], f ≤ 𝓟 A → ∃ a ∈ A, ClusterPt a f

/-- A topological space is countably compact if every countably generated proper filter has a
cluster point. -/
@[mk_iff]
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

/-- A set is countably compact if and only if every sequence in it has a cluster point in it. -/
theorem isCountablyCompact_iff_seq_clusterPt :
    IsCountablyCompact A ↔ ∀ x : ℕ → E, (∀ n, x n ∈ A) → ∃ a ∈ A, MapClusterPt a atTop x where
  mp h x hx := h (tendsto_principal.mpr (Eventually.of_forall hx))
  mpr hA f _ _ hle := by
    obtain ⟨s, hs⟩ := f.exists_antitone_basis
    have hmem (n : ℕ) : (s n ∩ A).Nonempty :=
      Filter.nonempty_of_mem (Filter.inter_mem (hs.mem n) (le_principal_iff.mp hle))
    choose x hx using hmem
    obtain ⟨a, ha, hac⟩ := hA x (fun n => (hx n).2)
    exact ⟨a, ha, ClusterPt.mono hac (hs.tendsto (fun n => (hx n).1))⟩

/-- A countably compact set has a finite subcover for any countable open cover. -/
theorem IsCountablyCompact.elim_finite_subcover (hA : IsCountablyCompact A) [Countable ι]
    {U : ι → Set E} (hUo : ∀ i, IsOpen (U i)) (hAU : A ⊆ ⋃ i, U i) :
    ∃ t : Finset ι, A ⊆ ⋃ i ∈ t, U i := by
  classical
  rcases isEmpty_or_nonempty ι
  · exact ⟨∅, by simpa using hAU⟩
  · obtain ⟨e, he⟩ := exists_surjective_nat ι
    suffices ∃ t : Finset ℕ, A ⊆ ⋃ n ∈ t, U (e n) by
      obtain ⟨s, hs⟩ := this
      exact ⟨s.image e, hs.trans (iUnion₂_subset fun _ hn =>
        subset_biUnion_of_mem (Finset.mem_image_of_mem e hn))⟩
    by_contra! h
    choose x hxA hxU using fun n => not_subset.mp (h (Finset.range (n + 1)))
    obtain ⟨a, haA, hac⟩ := isCountablyCompact_iff_seq_clusterPt.mp hA x hxA
    obtain ⟨k, hk⟩ := mem_iUnion.mp ((he.iUnion_comp U ▸ hAU) haA)
    have : ∀ᶠ n in atTop, x n ∉ U (e k) :=
      eventually_atTop.mpr ⟨k, fun n hn hxn =>
        hxU n <| mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)) hxn⟩
    exact hac.frequently ((hUo (e k)).mem_nhds hk) this

/-- A set is countably compact if and only if every countable open cover has a finite subcover. -/
theorem isCountablyCompact_iff_countable_open_cover :
    IsCountablyCompact A ↔ ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
        ∃ t : Finset ℕ, A ⊆ ⋃ i ∈ t, U i where
  mp hA _ hUo hAU := hA.elim_finite_subcover hUo hAU
  mpr h := by
    refine isCountablyCompact_iff_seq_clusterPt.2 fun x hx => ?_
    by_contra! hac
    let V : ℕ → Set E := fun n => (closure (x '' Ici n))ᶜ
    have hVmono : Monotone V := fun _ _ hmn =>
      compl_subset_compl.2 <| closure_mono <| image_mono <| Ici_subset_Ici.2 hmn
    simp only [mapClusterPt_atTop_iff_forall_mem_closure, not_forall] at hac
    have hAV : A ⊆ ⋃ n, V n := fun a haA => mem_iUnion.2 (hac a haA)
    obtain ⟨t, ht⟩ := h V (fun _ => isClosed_closure.isOpen_compl) hAV
    let m := t.sup id
    obtain ⟨j, hjt, hjV⟩ := mem_iUnion₂.mp (ht (hx m))
    have hxmV : x m ∈ V m := hVmono (Finset.le_sup hjt) hjV
    exact hxmV (subset_closure ⟨m, mem_Ici.mpr le_rfl, rfl⟩)

/-- A countably compact set has a finite subcover for any countable open cover indexed by a
subset. -/
theorem IsCountablyCompact.elim_finite_subcover_image (hA : IsCountablyCompact A)
    {b : Set ι} (hb : b.Countable) {U : ι → Set E} (hUo : ∀ i ∈ b, IsOpen (U i))
    (hAU : A ⊆ ⋃ i ∈ b, U i) : ∃ t ⊆ b, t.Finite ∧ A ⊆ ⋃ i ∈ t, U i := by
  haveI := hb.to_subtype
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun (i : b) ↦ hUo i i.prop) (by simpa using hAU)
  classical
  let t' := t.image Subtype.val
  have ht_subset : ↑t' ⊆ b := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact i.prop
  have ht_cover : A ⊆ ⋃ i ∈ t', U i := by
    intro x hx
    obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp (ht hx)
    exact mem_iUnion₂.mpr ⟨i, Finset.mem_image_of_mem _ hit, hxi⟩
  exact ⟨↑t', ht_subset, t'.finite_toSet, ht_cover⟩

/-- Variant of `isCountablyCompact_iff_countable_open_cover` with `Set ℕ` instead of `Finset ℕ`. -/
theorem isCountablyCompact_iff_countable_open_cover' :
    IsCountablyCompact A ↔ ∀ (U : ℕ → Set E), (∀ i, IsOpen (U i)) → A ⊆ ⋃ i, U i →
        ∃ t : Set ℕ, t.Finite ∧ A ⊆ ⋃ i ∈ t, U i := by
  rw [isCountablyCompact_iff_countable_open_cover]
  refine ⟨fun h U hUo hAU => ?_, fun h U hUo hAU => ?_⟩
  · obtain ⟨t, ht⟩ := h U hUo hAU
    exact ⟨(t : Set ℕ), Finset.finite_toSet t, ht⟩
  · obtain ⟨t, htfin, ht⟩ := h U hUo hAU
    exact ⟨htfin.toFinset, by simpa [htfin.coe_toFinset] using ht⟩

/-- A compact set is countably compact. -/
theorem IsCompact.IsCountablyCompact (hA : IsCompact A) : IsCountablyCompact A :=
  fun _ _ _ hle => hA hle

/-- A sequentially compact set is countably compact. -/
theorem IsSeqCompact.IsCountablyCompact (hA : IsSeqCompact A) :
    IsCountablyCompact A := isCountablyCompact_iff_seq_clusterPt.mpr fun _ h =>
    let ⟨a, ha, _, h_mono, h_tendsto⟩ := hA h
    ⟨a, ha, h_tendsto.mapClusterPt.of_comp h_mono.tendsto_atTop⟩

/-- If a sequential space is countably compact, then it is sequentially compact. We follow the
proof in [kremsater1972sequential]. -/
instance [SequentialSpace E] [CountablyCompactSpace E] :
    SeqCompactSpace E := by
  by_contra!
  simp_all only [seqCompactSpace_iff, IsSeqCompact, mem_univ, not_forall]
  obtain ⟨x, hx⟩ := this
  simp only [true_and, not_exists, not_and, exists_const] at hx
  let A := ⋃ i, closure {x i}
  have hc {x : ℕ → E} (hx : ∀ (l : E) (φ : ℕ → ℕ), StrictMono φ → ¬Tendsto (x ∘ φ) atTop (𝓝 l)) :
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
        refine ⟨b, ?_, c + j, by grind, hb⟩
        by_contra! hab
        grind [hc (c + j) (by grind) b hab.le]
      obtain ⟨φ, hφ⟩ := extraction_forall_of_frequently this
      choose ψ hψ1 hψ2 using hφ.2
      have : Tendsto ψ atTop atTop := tendsto_atTop_mono hψ1 tendsto_id
      refine (hx l φ hφ.1 (Tendsto.specializes (hy'.comp this) (fun n => ?_))).elim
      exact specializes_iff_mem_closure.2 (hψ2 n)
  have : IsCountablyCompact A :=
    ((countablyCompactSpace_iff E).1 inferInstance).of_isClosed_subset (hc hx) (by simp)
  obtain ⟨a, ha⟩ : ∃ a ∈ A, MapClusterPt a atTop x := by
    refine isCountablyCompact_iff_seq_clusterPt.1 this x (fun n => ?_)
    exact mem_iUnion_of_mem n <| subset_closure <| mem_singleton (x n)
  obtain ⟨k, hk⟩ : ∃ k, ∀ n > k, a ∉ closure {x n} := by
    by_contra!
    obtain ⟨φ, hφ1, hφ2⟩ := Nat.exists_strictMono_subsequence this
    refine hx a φ hφ1 (tendsto_atTop_nhds.2 fun U ha hUo => ⟨0, fun n _ => ?_⟩)
    simpa using mem_closure_iff.1 (hφ2 n) U hUo ha
  have : a ∉ ⋃ i, closure {x (i + (k + 1))} := by
    simpa [← iUnion_ge_eq_iUnion_nat_add (fun n => closure {x n}) (k + 1)] using
      fun i hi => hk i (by grind)
  have : a ∈ ⋃ i, closure {x (i + (k + 1))} := by
    have := mapClusterPt_atTop_iff_forall_mem_closure.1 ha.2 (k + 1)
    suffices h : closure (x '' Ici (k + 1)) ⊆ ⋃ i, closure {x (i + (k + 1))} from h this
    refine (IsClosed.closure_subset_iff (hc fun l φ hφ => ?_)).2 ?_
    · suffices (fun i => x (i + (k + 1))) ∘ φ = x ∘ (fun i => i + (k + 1)) ∘ φ from by
        refine this.symm ▸ hx l _ (StrictMono.comp (strictMono_id.add_const _) hφ)
      grind
    · simp only [image_eq_iUnion, mem_Ici, iUnion_ge_eq_iUnion_nat_add _ (k + 1)]
      exact iUnion_mono fun i => subset_closure
  grind

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

/-- The continuous image of a countably compact set is countably compact. -/
theorem IsCountablyCompact.image (hA : IsCountablyCompact A)
    {f : E → F} (hf : Continuous f) : IsCountablyCompact (f '' A) := by
  intro l hl_nebot hl_count hle
  haveI : NeBot (l.comap f ⊓ 𝓟 A) :=
    comap_inf_principal_neBot_of_image_mem hl_nebot (le_principal_iff.mp hle)
  obtain ⟨x, hxA, hx⟩ := hA (f := l.comap f ⊓ 𝓟 A) inf_le_right
  haveI := (hx.mono inf_le_left).neBot
  exact ⟨f x, mem_image_of_mem f hxA, (hf.continuousAt.inf (@tendsto_comap _ _ f l)).neBot⟩

/-- If `f : X → Y` is an inducing map, the image `f '' s` of a set `s` is countably compact
  if and only if `s` is countably compact. -/
theorem Topology.IsInducing.isCountablyCompact_iff {f : E → F} (hf : IsInducing f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) := by
  refine ⟨fun hs => hs.image hf.continuous, fun hs F F_ne_bot Fc F_le => ?_⟩
  obtain ⟨_, ⟨x, x_in : x ∈ A, rfl⟩, hx : ClusterPt (f x) (map f F)⟩ :=
    hs ((map_mono F_le).trans_eq map_principal)
  exact ⟨x, x_in, hf.mapClusterPt_iff.1 hx⟩

/-- If `f : X → Y` is an embedding, the image `f '' s` of a set `s` is countably compact
if and only if `s` is countably compact. -/
theorem Topology.IsEmbedding.isCountablyCompact_iff {f : E → F} (hf : IsEmbedding f) :
    IsCountablyCompact A ↔ IsCountablyCompact (f '' A) := hf.isInducing.isCountablyCompact_iff

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

/-- In a first-countable space, a countably compact set is sequentially compact. -/
theorem IsCountablyCompact.isSeqCompact [FirstCountableTopology E]
    (hA : IsCountablyCompact A) : IsSeqCompact A := by
  simp_all only [isCountablyCompact_iff_countablyCompactSpace, isSeqCompact_iff_seqCompactSpace]
  infer_instance

/-- Every infinite subset of a countably compact set has an accumulation point in the set. -/
theorem IsCountablyCompact.exists_accPt_of_infinite
    (hA : IsCountablyCompact A) (hBA : B ⊆ A) (hB : B.Infinite) :
    ∃ a ∈ A, AccPt a (𝓟 B) := by
  let f := hB.natEmbedding
  let x : ℕ → E := (↑) ∘ f
  have hx_inj : Function.Injective x := Subtype.val_injective.comp f.injective
  obtain ⟨a, haA, hac⟩ := isCountablyCompact_iff_seq_clusterPt.mp hA x (fun n => hBA (f n).2)
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
    refine isCountablyCompact_iff_seq_clusterPt.2 fun x hx => ?_
    by_cases hfin : (Set.range x).Finite
    · -- Case 1: Finite range (Pigeonhole principle)
      haveI := hfin.to_subtype
      obtain ⟨⟨a, ha_range⟩, ha_inf⟩ := Finite.exists_infinite_fiber (Set.rangeFactorization x)
      rw [Set.infinite_coe_iff] at ha_inf
      simp only [Set.preimage, Set.mem_singleton_iff, Set.rangeFactorization, Subtype.mk.injEq]
        at ha_inf
      refine ⟨a, range_subset_iff.2 hx ha_range, mapClusterPt_iff_frequently.2 fun U hU => ?_⟩
      exact (Nat.frequently_atTop_iff_infinite.mpr ha_inf).mono fun _ hn =>
        hn.symm ▸ mem_of_mem_nhds hU
    · -- Case 2: Infinite range (T1 Space contradiction)
      obtain ⟨a, haA, hacc⟩ := h (Set.range x) (range_subset_iff.2 hx) hfin
      refine ⟨a, haA,
        mapClusterPt_iff_frequently.mpr fun U hU => Nat.frequently_atTop_iff_infinite.mpr ?_⟩
      suffices h_inf_inter : (U ∩ Set.range x).Infinite from
        (h_inf_inter.preimage inter_subset_right).mono (preimage_mono inter_subset_left)
      by_contra h_fin
      have hF_closed : IsClosed ((U ∩ Set.range x) \ {a}) :=
        (Set.not_infinite.1 h_fin |>.subset diff_subset).isClosed
      obtain ⟨y, ⟨hya, hyr⟩, hyU, hyFc⟩ :=
        ((accPt_iff_frequently.1 hacc).and_eventually
          (Filter.inter_mem hU (hF_closed.isOpen_compl.mem_nhds fun hf => hf.2 rfl))).exists
      exact hyFc ⟨⟨hyU, hyr⟩, hya⟩

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
