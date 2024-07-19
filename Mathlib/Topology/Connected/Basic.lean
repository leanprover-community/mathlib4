/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Data.Set.Image
import Mathlib.Order.SuccPred.Relation
import Mathlib.Topology.Clopen
import Mathlib.Topology.Irreducible

/-!
# Connected subsets of topological spaces

In this file we define connected subsets of a topological spaces and various other properties and
classes related to connectivity.

## Main definitions

We define the following properties for sets in a topological space:

* `IsConnected`: a nonempty set that has no non-trivial open partition.
  See also the section below in the module doc.
* `connectedComponent` is the connected component of an element in the space.

We also have a class stating that the whole space satisfies that property: `ConnectedSpace`

## On the definition of connected sets/spaces

In informal mathematics, connected spaces are assumed to be nonempty.
We formalise the predicate without that assumption as `IsPreconnected`.
In other words, the only difference is whether the empty space counts as connected.
There are good reasons to consider the empty space to be “too simple to be simple”
See also https://ncatlab.org/nlab/show/too+simple+to+be+simple,
and in particular
https://ncatlab.org/nlab/show/too+simple+to+be+simple#relationship_to_biased_definitions.
-/


open Set Function Topology TopologicalSpace Relation
open scoped Classical

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {π : ι → Type*} [TopologicalSpace α]
  {s t u v : Set α}

section Preconnected

/-- A preconnected set is one where there is no non-trivial open partition. -/
def IsPreconnected (s : Set α) : Prop :=
  ∀ u v : Set α, IsOpen u → IsOpen v → s ⊆ u ∪ v → (s ∩ u).Nonempty → (s ∩ v).Nonempty →
    (s ∩ (u ∩ v)).Nonempty

/-- A connected set is one that is nonempty and where there is no non-trivial open partition. -/
def IsConnected (s : Set α) : Prop :=
  s.Nonempty ∧ IsPreconnected s

theorem IsConnected.nonempty {s : Set α} (h : IsConnected s) : s.Nonempty :=
  h.1

theorem IsConnected.isPreconnected {s : Set α} (h : IsConnected s) : IsPreconnected s :=
  h.2

theorem IsPreirreducible.isPreconnected {s : Set α} (H : IsPreirreducible s) : IsPreconnected s :=
  fun _ _ hu hv _ => H _ _ hu hv

theorem IsIrreducible.isConnected {s : Set α} (H : IsIrreducible s) : IsConnected s :=
  ⟨H.nonempty, H.isPreirreducible.isPreconnected⟩

theorem isPreconnected_empty : IsPreconnected (∅ : Set α) :=
  isPreirreducible_empty.isPreconnected

theorem isConnected_singleton {x} : IsConnected ({x} : Set α) :=
  isIrreducible_singleton.isConnected

theorem isPreconnected_singleton {x} : IsPreconnected ({x} : Set α) :=
  isConnected_singleton.isPreconnected

theorem Set.Subsingleton.isPreconnected {s : Set α} (hs : s.Subsingleton) : IsPreconnected s :=
  hs.induction_on isPreconnected_empty fun _ => isPreconnected_singleton

/-- If any point of a set is joined to a fixed point by a preconnected subset,
then the original set is preconnected as well. -/
theorem isPreconnected_of_forall {s : Set α} (x : α)
    (H : ∀ y ∈ s, ∃ t, t ⊆ s ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t) : IsPreconnected s := by
  rintro u v hu hv hs ⟨z, zs, zu⟩ ⟨y, ys, yv⟩
  have xs : x ∈ s := by
    rcases H y ys with ⟨t, ts, xt, -, -⟩
    exact ts xt
  -- Porting note (#11215): TODO: use `wlog xu : x ∈ u := hs xs using u v y z, v u z y`
  cases hs xs with
  | inl xu =>
    rcases H y ys with ⟨t, ts, xt, yt, ht⟩
    have := ht u v hu hv (ts.trans hs) ⟨x, xt, xu⟩ ⟨y, yt, yv⟩
    exact this.imp fun z hz => ⟨ts hz.1, hz.2⟩
  | inr xv =>
    rcases H z zs with ⟨t, ts, xt, zt, ht⟩
    have := ht v u hv hu (ts.trans <| by rwa [union_comm]) ⟨x, xt, xv⟩ ⟨z, zt, zu⟩
    exact this.imp fun _ h => ⟨ts h.1, h.2.2, h.2.1⟩

/-- If any two points of a set are contained in a preconnected subset,
then the original set is preconnected as well. -/
theorem isPreconnected_of_forall_pair {s : Set α}
    (H : ∀ x ∈ s, ∀ y ∈ s, ∃ t, t ⊆ s ∧ x ∈ t ∧ y ∈ t ∧ IsPreconnected t) :
    IsPreconnected s := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨x, hx⟩)
  exacts [isPreconnected_empty, isPreconnected_of_forall x fun y => H x hx y]

/-- A union of a family of preconnected sets with a common point is preconnected as well. -/
theorem isPreconnected_sUnion (x : α) (c : Set (Set α)) (H1 : ∀ s ∈ c, x ∈ s)
    (H2 : ∀ s ∈ c, IsPreconnected s) : IsPreconnected (⋃₀ c) := by
  apply isPreconnected_of_forall x
  rintro y ⟨s, sc, ys⟩
  exact ⟨s, subset_sUnion_of_mem sc, H1 s sc, ys, H2 s sc⟩

theorem isPreconnected_iUnion {ι : Sort*} {s : ι → Set α} (h₁ : (⋂ i, s i).Nonempty)
    (h₂ : ∀ i, IsPreconnected (s i)) : IsPreconnected (⋃ i, s i) :=
  Exists.elim h₁ fun f hf => isPreconnected_sUnion f _ hf (forall_mem_range.2 h₂)

theorem IsPreconnected.union (x : α) {s t : Set α} (H1 : x ∈ s) (H2 : x ∈ t) (H3 : IsPreconnected s)
    (H4 : IsPreconnected t) : IsPreconnected (s ∪ t) :=
  sUnion_pair s t ▸ isPreconnected_sUnion x {s, t} (by rintro r (rfl | rfl | h) <;> assumption)
    (by rintro r (rfl | rfl | h) <;> assumption)

theorem IsPreconnected.union' {s t : Set α} (H : (s ∩ t).Nonempty) (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ∪ t) := by
  rcases H with ⟨x, hxs, hxt⟩
  exact hs.union x hxs hxt ht

theorem IsConnected.union {s t : Set α} (H : (s ∩ t).Nonempty) (Hs : IsConnected s)
    (Ht : IsConnected t) : IsConnected (s ∪ t) := by
  rcases H with ⟨x, hx⟩
  refine ⟨⟨x, mem_union_left t (mem_of_mem_inter_left hx)⟩, ?_⟩
  exact Hs.isPreconnected.union x (mem_of_mem_inter_left hx) (mem_of_mem_inter_right hx)
    Ht.isPreconnected

/-- The directed sUnion of a set S of preconnected subsets is preconnected. -/
theorem IsPreconnected.sUnion_directed {S : Set (Set α)} (K : DirectedOn (· ⊆ ·) S)
    (H : ∀ s ∈ S, IsPreconnected s) : IsPreconnected (⋃₀ S) := by
  rintro u v hu hv Huv ⟨a, ⟨s, hsS, has⟩, hau⟩ ⟨b, ⟨t, htS, hbt⟩, hbv⟩
  obtain ⟨r, hrS, hsr, htr⟩ : ∃ r ∈ S, s ⊆ r ∧ t ⊆ r := K s hsS t htS
  have Hnuv : (r ∩ (u ∩ v)).Nonempty :=
    H _ hrS u v hu hv ((subset_sUnion_of_mem hrS).trans Huv) ⟨a, hsr has, hau⟩ ⟨b, htr hbt, hbv⟩
  have Kruv : r ∩ (u ∩ v) ⊆ ⋃₀ S ∩ (u ∩ v) := inter_subset_inter_left _ (subset_sUnion_of_mem hrS)
  exact Hnuv.mono Kruv

/-- The biUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
theorem IsPreconnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι → Set α}
    (H : ∀ i ∈ t, IsPreconnected (s i))
    (K : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen (fun i j => (s i ∩ s j).Nonempty ∧ i ∈ t) i j) :
    IsPreconnected (⋃ n ∈ t, s n) := by
  let R := fun i j : ι => (s i ∩ s j).Nonempty ∧ i ∈ t
  have P : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen R i j →
      ∃ p, p ⊆ t ∧ i ∈ p ∧ j ∈ p ∧ IsPreconnected (⋃ j ∈ p, s j) := fun i hi j hj h => by
    induction h with
    | refl =>
      refine ⟨{i}, singleton_subset_iff.mpr hi, mem_singleton i, mem_singleton i, ?_⟩
      rw [biUnion_singleton]
      exact H i hi
    | @tail j k _ hjk ih =>
      obtain ⟨p, hpt, hip, hjp, hp⟩ := ih hjk.2
      refine ⟨insert k p, insert_subset_iff.mpr ⟨hj, hpt⟩, mem_insert_of_mem k hip,
        mem_insert k p, ?_⟩
      rw [biUnion_insert]
      refine (H k hj).union' (hjk.1.mono ?_) hp
      rw [inter_comm]
      exact inter_subset_inter_right _ (subset_biUnion_of_mem hjp)
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  obtain ⟨i : ι, hi : i ∈ t, hxi : x ∈ s i⟩ := mem_iUnion₂.1 hx
  obtain ⟨j : ι, hj : j ∈ t, hyj : y ∈ s j⟩ := mem_iUnion₂.1 hy
  obtain ⟨p, hpt, hip, hjp, hp⟩ := P i hi j hj (K i hi j hj)
  exact ⟨⋃ j ∈ p, s j, biUnion_subset_biUnion_left hpt, mem_biUnion hip hxi,
    mem_biUnion hjp hyj, hp⟩

/-- The biUnion of a family of preconnected sets is preconnected if the graph determined by
whether two sets intersect is preconnected. -/
theorem IsConnected.biUnion_of_reflTransGen {ι : Type*} {t : Set ι} {s : ι → Set α}
    (ht : t.Nonempty) (H : ∀ i ∈ t, IsConnected (s i))
    (K : ∀ i, i ∈ t → ∀ j, j ∈ t → ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty ∧ i ∈ t) i j) :
    IsConnected (⋃ n ∈ t, s n) :=
  ⟨nonempty_biUnion.2 <| ⟨ht.some, ht.some_mem, (H _ ht.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_reflTransGen (fun i hi => (H i hi).isPreconnected) K⟩

/-- Preconnectedness of the iUnion of a family of preconnected sets
indexed by the vertices of a preconnected graph,
where two vertices are joined when the corresponding sets intersect. -/
theorem IsPreconnected.iUnion_of_reflTransGen {ι : Type*} {s : ι → Set α}
    (H : ∀ i, IsPreconnected (s i))
    (K : ∀ i j, ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty) i j) :
    IsPreconnected (⋃ n, s n) := by
  rw [← biUnion_univ]
  exact IsPreconnected.biUnion_of_reflTransGen (fun i _ => H i) fun i _ j _ => by
    simpa [mem_univ] using K i j

theorem IsConnected.iUnion_of_reflTransGen {ι : Type*} [Nonempty ι] {s : ι → Set α}
    (H : ∀ i, IsConnected (s i))
    (K : ∀ i j, ReflTransGen (fun i j : ι => (s i ∩ s j).Nonempty) i j) : IsConnected (⋃ n, s n) :=
  ⟨nonempty_iUnion.2 <| Nonempty.elim ‹_› fun i : ι => ⟨i, (H _).nonempty⟩,
    IsPreconnected.iUnion_of_reflTransGen (fun i => (H i).isPreconnected) K⟩

section SuccOrder

open Order

variable [LinearOrder β] [SuccOrder β] [IsSuccArchimedean β]

/-- The iUnion of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is preconnected. -/
theorem IsPreconnected.iUnion_of_chain {s : β → Set α} (H : ∀ n, IsPreconnected (s n))
    (K : ∀ n, (s n ∩ s (succ n)).Nonempty) : IsPreconnected (⋃ n, s n) :=
  IsPreconnected.iUnion_of_reflTransGen H fun i j =>
    reflTransGen_of_succ _ (fun i _ => K i) fun i _ => by
      rw [inter_comm]
      exact K i

/-- The iUnion of connected sets indexed by a type with an archimedean successor (like `ℕ` or `ℤ`)
  such that any two neighboring sets meet is connected. -/
theorem IsConnected.iUnion_of_chain [Nonempty β] {s : β → Set α} (H : ∀ n, IsConnected (s n))
    (K : ∀ n, (s n ∩ s (succ n)).Nonempty) : IsConnected (⋃ n, s n) :=
  IsConnected.iUnion_of_reflTransGen H fun i j =>
    reflTransGen_of_succ _ (fun i _ => K i) fun i _ => by
      rw [inter_comm]
      exact K i

/-- The iUnion of preconnected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
theorem IsPreconnected.biUnion_of_chain {s : β → Set α} {t : Set β} (ht : OrdConnected t)
    (H : ∀ n ∈ t, IsPreconnected (s n))
    (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).Nonempty) :
    IsPreconnected (⋃ n ∈ t, s n) := by
  have h1 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → k ∈ t := fun hi hj hk =>
    ht.out hi hj (Ico_subset_Icc_self hk)
  have h2 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → succ k ∈ t := fun hi hj hk =>
    ht.out hi hj ⟨hk.1.trans <| le_succ _, succ_le_of_lt hk.2⟩
  have h3 : ∀ {i j k : β}, i ∈ t → j ∈ t → k ∈ Ico i j → (s k ∩ s (succ k)).Nonempty :=
    fun hi hj hk => K _ (h1 hi hj hk) (h2 hi hj hk)
  refine IsPreconnected.biUnion_of_reflTransGen H fun i hi j hj => ?_
  exact reflTransGen_of_succ _ (fun k hk => ⟨h3 hi hj hk, h1 hi hj hk⟩) fun k hk =>
      ⟨by rw [inter_comm]; exact h3 hj hi hk, h2 hj hi hk⟩

/-- The iUnion of connected sets indexed by a subset of a type with an archimedean successor
  (like `ℕ` or `ℤ`) such that any two neighboring sets meet is preconnected. -/
theorem IsConnected.biUnion_of_chain {s : β → Set α} {t : Set β} (hnt : t.Nonempty)
    (ht : OrdConnected t) (H : ∀ n ∈ t, IsConnected (s n))
    (K : ∀ n : β, n ∈ t → succ n ∈ t → (s n ∩ s (succ n)).Nonempty) : IsConnected (⋃ n ∈ t, s n) :=
  ⟨nonempty_biUnion.2 <| ⟨hnt.some, hnt.some_mem, (H _ hnt.some_mem).nonempty⟩,
    IsPreconnected.biUnion_of_chain ht (fun i hi => (H i hi).isPreconnected) K⟩

end SuccOrder

/-- Theorem of bark and tree: if a set is within a preconnected set and its closure, then it is
preconnected as well. See also `IsConnected.subset_closure`. -/
protected theorem IsPreconnected.subset_closure {s : Set α} {t : Set α} (H : IsPreconnected s)
    (Kst : s ⊆ t) (Ktcs : t ⊆ closure s) : IsPreconnected t :=
  fun u v hu hv htuv ⟨_y, hyt, hyu⟩ ⟨_z, hzt, hzv⟩ =>
  let ⟨p, hpu, hps⟩ := mem_closure_iff.1 (Ktcs hyt) u hu hyu
  let ⟨q, hqv, hqs⟩ := mem_closure_iff.1 (Ktcs hzt) v hv hzv
  let ⟨r, hrs, hruv⟩ := H u v hu hv (Subset.trans Kst htuv) ⟨p, hps, hpu⟩ ⟨q, hqs, hqv⟩
  ⟨r, Kst hrs, hruv⟩

/-- Theorem of bark and tree: if a set is within a connected set and its closure, then it is
connected as well. See also `IsPreconnected.subset_closure`. -/
protected theorem IsConnected.subset_closure {s : Set α} {t : Set α} (H : IsConnected s)
    (Kst : s ⊆ t) (Ktcs : t ⊆ closure s) : IsConnected t :=
  ⟨Nonempty.mono Kst H.left, IsPreconnected.subset_closure H.right Kst Ktcs⟩

/-- The closure of a preconnected set is preconnected as well. -/
protected theorem IsPreconnected.closure {s : Set α} (H : IsPreconnected s) :
    IsPreconnected (closure s) :=
  IsPreconnected.subset_closure H subset_closure Subset.rfl

/-- The closure of a connected set is connected as well. -/
protected theorem IsConnected.closure {s : Set α} (H : IsConnected s) : IsConnected (closure s) :=
  IsConnected.subset_closure H subset_closure <| Subset.rfl

/-- The image of a preconnected set is preconnected as well. -/
protected theorem IsPreconnected.image [TopologicalSpace β] {s : Set α} (H : IsPreconnected s)
    (f : α → β) (hf : ContinuousOn f s) : IsPreconnected (f '' s) := by
  -- Unfold/destruct definitions in hypotheses
  rintro u v hu hv huv ⟨_, ⟨x, xs, rfl⟩, xu⟩ ⟨_, ⟨y, ys, rfl⟩, yv⟩
  rcases continuousOn_iff'.1 hf u hu with ⟨u', hu', u'_eq⟩
  rcases continuousOn_iff'.1 hf v hv with ⟨v', hv', v'_eq⟩
  -- Reformulate `huv : f '' s ⊆ u ∪ v` in terms of `u'` and `v'`
  replace huv : s ⊆ u' ∪ v' := by
    rw [image_subset_iff, preimage_union] at huv
    replace huv := subset_inter huv Subset.rfl
    rw [union_inter_distrib_right, u'_eq, v'_eq, ← union_inter_distrib_right] at huv
    exact (subset_inter_iff.1 huv).1
  -- Now `s ⊆ u' ∪ v'`, so we can apply `‹IsPreconnected s›`
  obtain ⟨z, hz⟩ : (s ∩ (u' ∩ v')).Nonempty := by
    refine H u' v' hu' hv' huv ⟨x, ?_⟩ ⟨y, ?_⟩ <;> rw [inter_comm]
    exacts [u'_eq ▸ ⟨xu, xs⟩, v'_eq ▸ ⟨yv, ys⟩]
  rw [← inter_self s, inter_assoc, inter_left_comm s u', ← inter_assoc, inter_comm s, inter_comm s,
    ← u'_eq, ← v'_eq] at hz
  exact ⟨f z, ⟨z, hz.1.2, rfl⟩, hz.1.1, hz.2.1⟩

/-- The image of a connected set is connected as well. -/
protected theorem IsConnected.image [TopologicalSpace β] {s : Set α} (H : IsConnected s) (f : α → β)
    (hf : ContinuousOn f s) : IsConnected (f '' s) :=
  ⟨image_nonempty.mpr H.nonempty, H.isPreconnected.image f hf⟩

theorem isPreconnected_closed_iff {s : Set α} :
    IsPreconnected s ↔ ∀ t t', IsClosed t → IsClosed t' →
      s ⊆ t ∪ t' → (s ∩ t).Nonempty → (s ∩ t').Nonempty → (s ∩ (t ∩ t')).Nonempty :=
  ⟨by
      rintro h t t' ht ht' htt' ⟨x, xs, xt⟩ ⟨y, ys, yt'⟩
      rw [← not_disjoint_iff_nonempty_inter, ← subset_compl_iff_disjoint_right, compl_inter]
      intro h'
      have xt' : x ∉ t' := (h' xs).resolve_left (absurd xt)
      have yt : y ∉ t := (h' ys).resolve_right (absurd yt')
      have := h _ _ ht.isOpen_compl ht'.isOpen_compl h' ⟨y, ys, yt⟩ ⟨x, xs, xt'⟩
      rw [← compl_union] at this
      exact this.ne_empty htt'.disjoint_compl_right.inter_eq,
    by
      rintro h u v hu hv huv ⟨x, xs, xu⟩ ⟨y, ys, yv⟩
      rw [← not_disjoint_iff_nonempty_inter, ← subset_compl_iff_disjoint_right, compl_inter]
      intro h'
      have xv : x ∉ v := (h' xs).elim (absurd xu) id
      have yu : y ∉ u := (h' ys).elim id (absurd yv)
      have := h _ _ hu.isClosed_compl hv.isClosed_compl h' ⟨y, ys, yu⟩ ⟨x, xs, xv⟩
      rw [← compl_union] at this
      exact this.ne_empty huv.disjoint_compl_right.inter_eq⟩

theorem Inducing.isPreconnected_image [TopologicalSpace β] {s : Set α} {f : α → β}
    (hf : Inducing f) : IsPreconnected (f '' s) ↔ IsPreconnected s := by
  refine ⟨fun h => ?_, fun h => h.image _ hf.continuous.continuousOn⟩
  rintro u v hu' hv' huv ⟨x, hxs, hxu⟩ ⟨y, hys, hyv⟩
  rcases hf.isOpen_iff.1 hu' with ⟨u, hu, rfl⟩
  rcases hf.isOpen_iff.1 hv' with ⟨v, hv, rfl⟩
  replace huv : f '' s ⊆ u ∪ v := by rwa [image_subset_iff]
  rcases h u v hu hv huv ⟨f x, mem_image_of_mem _ hxs, hxu⟩ ⟨f y, mem_image_of_mem _ hys, hyv⟩ with
    ⟨_, ⟨z, hzs, rfl⟩, hzuv⟩
  exact ⟨z, hzs, hzuv⟩

/- TODO: The following lemmas about connection of preimages hold more generally for strict maps
(the quotient and subspace topologies of the image agree) whose fibers are preconnected. -/

theorem IsPreconnected.preimage_of_isOpenMap [TopologicalSpace β] {f : α → β} {s : Set β}
    (hs : IsPreconnected s) (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ range f) :
    IsPreconnected (f ⁻¹' s) := fun u v hu hv hsuv hsu hsv => by
  replace hsf : f '' (f ⁻¹' s) = s := image_preimage_eq_of_subset hsf
  obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s ∩ (f '' u ∩ f '' v)).Nonempty := by
    refine hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
    · simpa only [hsf, image_union] using image_subset f hsuv
    · simpa only [image_preimage_inter] using hsu.image f
    · simpa only [image_preimage_inter] using hsv.image f
  · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

theorem IsPreconnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β}
    (hs : IsPreconnected s) {f : α → β} (hinj : Function.Injective f) (hf : IsClosedMap f)
    (hsf : s ⊆ range f) : IsPreconnected (f ⁻¹' s) :=
  isPreconnected_closed_iff.2 fun u v hu hv hsuv hsu hsv => by
    replace hsf : f '' (f ⁻¹' s) = s := image_preimage_eq_of_subset hsf
    obtain ⟨_, has, ⟨a, hau, rfl⟩, hav⟩ : (s ∩ (f '' u ∩ f '' v)).Nonempty := by
      refine isPreconnected_closed_iff.1 hs (f '' u) (f '' v) (hf u hu) (hf v hv) ?_ ?_ ?_
      · simpa only [hsf, image_union] using image_subset f hsuv
      · simpa only [image_preimage_inter] using hsu.image f
      · simpa only [image_preimage_inter] using hsv.image f
    · exact ⟨a, has, hau, hinj.mem_set_image.1 hav⟩

theorem IsConnected.preimage_of_isOpenMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α → β} (hinj : Function.Injective f) (hf : IsOpenMap f) (hsf : s ⊆ range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isOpenMap hinj hf hsf⟩

theorem IsConnected.preimage_of_isClosedMap [TopologicalSpace β] {s : Set β} (hs : IsConnected s)
    {f : α → β} (hinj : Function.Injective f) (hf : IsClosedMap f) (hsf : s ⊆ range f) :
    IsConnected (f ⁻¹' s) :=
  ⟨hs.nonempty.preimage' hsf, hs.isPreconnected.preimage_of_isClosedMap hinj hf hsf⟩

theorem IsPreconnected.subset_or_subset (hu : IsOpen u) (hv : IsOpen v) (huv : Disjoint u v)
    (hsuv : s ⊆ u ∪ v) (hs : IsPreconnected s) : s ⊆ u ∨ s ⊆ v := by
  specialize hs u v hu hv hsuv
  obtain hsu | hsu := (s ∩ u).eq_empty_or_nonempty
  · exact Or.inr ((Set.disjoint_iff_inter_eq_empty.2 hsu).subset_right_of_subset_union hsuv)
  · replace hs := mt (hs hsu)
    simp_rw [Set.not_nonempty_iff_eq_empty, ← Set.disjoint_iff_inter_eq_empty,
      disjoint_iff_inter_eq_empty.1 huv] at hs
    exact Or.inl ((hs s.disjoint_empty).subset_left_of_subset_union hsuv)

theorem IsPreconnected.subset_left_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v) (hsu : (s ∩ u).Nonempty) (hs : IsPreconnected s) :
    s ⊆ u :=
  Disjoint.subset_left_of_subset_union hsuv
    (by
      by_contra hsv
      rw [not_disjoint_iff_nonempty_inter] at hsv
      obtain ⟨x, _, hx⟩ := hs u v hu hv hsuv hsu hsv
      exact Set.disjoint_iff.1 huv hx)

theorem IsPreconnected.subset_right_of_subset_union (hu : IsOpen u) (hv : IsOpen v)
    (huv : Disjoint u v) (hsuv : s ⊆ u ∪ v) (hsv : (s ∩ v).Nonempty) (hs : IsPreconnected s) :
    s ⊆ v :=
  hs.subset_left_of_subset_union hv hu huv.symm (union_comm u v ▸ hsuv) hsv

-- Porting note: moved up
/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem IsPreconnected.subset_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t)
    (hne : (s ∩ t).Nonempty) : s ⊆ t :=
  hs.subset_left_of_subset_union ht.isOpen ht.compl.isOpen disjoint_compl_right (by simp) hne

/-- If a preconnected set `s` intersects an open set `u`, and limit points of `u` inside `s` are
contained in `u`, then the whole set `s` is contained in `u`. -/
theorem IsPreconnected.subset_of_closure_inter_subset (hs : IsPreconnected s) (hu : IsOpen u)
    (h'u : (s ∩ u).Nonempty) (h : closure u ∩ s ⊆ u) : s ⊆ u := by
  have A : s ⊆ u ∪ (closure u)ᶜ := by
    intro x hx
    by_cases xu : x ∈ u
    · exact Or.inl xu
    · right
      intro h'x
      exact xu (h (mem_inter h'x hx))
  apply hs.subset_left_of_subset_union hu isClosed_closure.isOpen_compl _ A h'u
  exact disjoint_compl_right.mono_right (compl_subset_compl.2 subset_closure)

theorem IsPreconnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsPreconnected s)
    (ht : IsPreconnected t) : IsPreconnected (s ×ˢ t) := by
  apply isPreconnected_of_forall_pair
  rintro ⟨a₁, b₁⟩ ⟨ha₁, hb₁⟩ ⟨a₂, b₂⟩ ⟨ha₂, hb₂⟩
  refine ⟨Prod.mk a₁ '' t ∪ flip Prod.mk b₂ '' s, ?_, .inl ⟨b₁, hb₁, rfl⟩, .inr ⟨a₂, ha₂, rfl⟩, ?_⟩
  · rintro _ (⟨y, hy, rfl⟩ | ⟨x, hx, rfl⟩)
    exacts [⟨ha₁, hy⟩, ⟨hx, hb₂⟩]
  · exact (ht.image _ (Continuous.Prod.mk _).continuousOn).union (a₁, b₂) ⟨b₂, hb₂, rfl⟩
      ⟨a₁, ha₁, rfl⟩ (hs.image _ (continuous_id.prod_mk continuous_const).continuousOn)

theorem IsConnected.prod [TopologicalSpace β] {s : Set α} {t : Set β} (hs : IsConnected s)
    (ht : IsConnected t) : IsConnected (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

theorem isPreconnected_univ_pi [∀ i, TopologicalSpace (π i)] {s : ∀ i, Set (π i)}
    (hs : ∀ i, IsPreconnected (s i)) : IsPreconnected (pi univ s) := by
  rintro u v uo vo hsuv ⟨f, hfs, hfu⟩ ⟨g, hgs, hgv⟩
  rcases exists_finset_piecewise_mem_of_mem_nhds (uo.mem_nhds hfu) g with ⟨I, hI⟩
  induction' I using Finset.induction_on with i I _ ihI
  · refine ⟨g, hgs, ⟨?_, hgv⟩⟩
    simpa using hI
  · rw [Finset.piecewise_insert] at hI
    have := I.piecewise_mem_set_pi hfs hgs
    refine (hsuv this).elim ihI fun h => ?_
    set S := update (I.piecewise f g) i '' s i
    have hsub : S ⊆ pi univ s := by
      refine image_subset_iff.2 fun z hz => ?_
      rwa [update_preimage_univ_pi]
      exact fun j _ => this j trivial
    have hconn : IsPreconnected S :=
      (hs i).image _ (continuous_const.update i continuous_id).continuousOn
    have hSu : (S ∩ u).Nonempty := ⟨_, mem_image_of_mem _ (hfs _ trivial), hI⟩
    have hSv : (S ∩ v).Nonempty := ⟨_, ⟨_, this _ trivial, update_eq_self _ _⟩, h⟩
    refine (hconn u v uo vo (hsub.trans hsuv) hSu hSv).mono ?_
    exact inter_subset_inter_left _ hsub

@[simp]
theorem isConnected_univ_pi [∀ i, TopologicalSpace (π i)] {s : ∀ i, Set (π i)} :
    IsConnected (pi univ s) ↔ ∀ i, IsConnected (s i) := by
  simp only [IsConnected, ← univ_pi_nonempty_iff, forall_and, and_congr_right_iff]
  refine fun hne => ⟨fun hc i => ?_, isPreconnected_univ_pi⟩
  rw [← eval_image_univ_pi hne]
  exact hc.image _ (continuous_apply _).continuousOn

theorem Sigma.isConnected_iff [∀ i, TopologicalSpace (π i)] {s : Set (Σi, π i)} :
    IsConnected s ↔ ∃ i t, IsConnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨⟨i, x⟩, hx⟩ := hs.nonempty
    have : s ⊆ range (Sigma.mk i) :=
      hs.isPreconnected.subset_isClopen isClopen_range_sigmaMk ⟨⟨i, x⟩, hx, x, rfl⟩
    exact ⟨i, Sigma.mk i ⁻¹' s, hs.preimage_of_isOpenMap sigma_mk_injective isOpenMap_sigmaMk this,
      (Set.image_preimage_eq_of_subset this).symm⟩
  · rintro ⟨i, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

theorem Sigma.isPreconnected_iff [hι : Nonempty ι] [∀ i, TopologicalSpace (π i)]
    {s : Set (Σi, π i)} : IsPreconnected s ↔ ∃ i t, IsPreconnected t ∧ s = Sigma.mk i '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact ⟨Classical.choice hι, ∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    · obtain ⟨a, t, ht, rfl⟩ := Sigma.isConnected_iff.1 ⟨h, hs⟩
      exact ⟨a, t, ht.isPreconnected, rfl⟩
  · rintro ⟨a, t, ht, rfl⟩
    exact ht.image _ continuous_sigmaMk.continuousOn

theorem Sum.isConnected_iff [TopologicalSpace β] {s : Set (Sum α β)} :
    IsConnected s ↔
      (∃ t, IsConnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsConnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨x | x, hx⟩ := hs.nonempty
    · have h : s ⊆ range Sum.inl :=
        hs.isPreconnected.subset_isClopen isClopen_range_inl ⟨.inl x, hx, x, rfl⟩
      refine Or.inl ⟨Sum.inl ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inl_injective isOpenMap_inl h
      · exact (image_preimage_eq_of_subset h).symm
    · have h : s ⊆ range Sum.inr :=
        hs.isPreconnected.subset_isClopen isClopen_range_inr ⟨.inr x, hx, x, rfl⟩
      refine Or.inr ⟨Sum.inr ⁻¹' s, ?_, ?_⟩
      · exact hs.preimage_of_isOpenMap Sum.inr_injective isOpenMap_inr h
      · exact (image_preimage_eq_of_subset h).symm
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

theorem Sum.isPreconnected_iff [TopologicalSpace β] {s : Set (Sum α β)} :
    IsPreconnected s ↔
      (∃ t, IsPreconnected t ∧ s = Sum.inl '' t) ∨ ∃ t, IsPreconnected t ∧ s = Sum.inr '' t := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain rfl | h := s.eq_empty_or_nonempty
    · exact Or.inl ⟨∅, isPreconnected_empty, (Set.image_empty _).symm⟩
    obtain ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩ := Sum.isConnected_iff.1 ⟨h, hs⟩
    · exact Or.inl ⟨t, ht.isPreconnected, rfl⟩
    · exact Or.inr ⟨t, ht.isPreconnected, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact ht.image _ continuous_inl.continuousOn
    · exact ht.image _ continuous_inr.continuousOn

/-- The connected component of a point is the maximal connected set
that contains this point. -/
def connectedComponent (x : α) : Set α :=
  ⋃₀ { s : Set α | IsPreconnected s ∧ x ∈ s }

/-- Given a set `F` in a topological space `α` and a point `x : α`, the connected
component of `x` in `F` is the connected component of `x` in the subtype `F` seen as
a set in `α`. This definition does not make sense if `x` is not in `F` so we return the
empty set in this case. -/
def connectedComponentIn (F : Set α) (x : α) : Set α :=
  if h : x ∈ F then (↑) '' connectedComponent (⟨x, h⟩ : F) else ∅

theorem connectedComponentIn_eq_image {F : Set α} {x : α} (h : x ∈ F) :
    connectedComponentIn F x = (↑) '' connectedComponent (⟨x, h⟩ : F) :=
  dif_pos h

theorem connectedComponentIn_eq_empty {F : Set α} {x : α} (h : x ∉ F) :
    connectedComponentIn F x = ∅ :=
  dif_neg h

theorem mem_connectedComponent {x : α} : x ∈ connectedComponent x :=
  mem_sUnion_of_mem (mem_singleton x) ⟨isPreconnected_singleton, mem_singleton x⟩

theorem mem_connectedComponentIn {x : α} {F : Set α} (hx : x ∈ F) :
    x ∈ connectedComponentIn F x := by
  simp [connectedComponentIn_eq_image hx, mem_connectedComponent, hx]

theorem connectedComponent_nonempty {x : α} : (connectedComponent x).Nonempty :=
  ⟨x, mem_connectedComponent⟩

theorem connectedComponentIn_nonempty_iff {x : α} {F : Set α} :
    (connectedComponentIn F x).Nonempty ↔ x ∈ F := by
  rw [connectedComponentIn]
  split_ifs <;> simp [connectedComponent_nonempty, *]

theorem connectedComponentIn_subset (F : Set α) (x : α) : connectedComponentIn F x ⊆ F := by
  rw [connectedComponentIn]
  split_ifs <;> simp

theorem isPreconnected_connectedComponent {x : α} : IsPreconnected (connectedComponent x) :=
  isPreconnected_sUnion x _ (fun _ => And.right) fun _ => And.left

theorem isPreconnected_connectedComponentIn {x : α} {F : Set α} :
    IsPreconnected (connectedComponentIn F x) := by
  rw [connectedComponentIn]; split_ifs
  · exact inducing_subtype_val.isPreconnected_image.mpr isPreconnected_connectedComponent
  · exact isPreconnected_empty

theorem isConnected_connectedComponent {x : α} : IsConnected (connectedComponent x) :=
  ⟨⟨x, mem_connectedComponent⟩, isPreconnected_connectedComponent⟩

theorem isConnected_connectedComponentIn_iff {x : α} {F : Set α} :
    IsConnected (connectedComponentIn F x) ↔ x ∈ F := by
  simp_rw [← connectedComponentIn_nonempty_iff, IsConnected, isPreconnected_connectedComponentIn,
    and_true_iff]

theorem IsPreconnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsPreconnected s)
    (H2 : x ∈ s) : s ⊆ connectedComponent x := fun _z hz => mem_sUnion_of_mem hz ⟨H1, H2⟩

theorem IsPreconnected.subset_connectedComponentIn {x : α} {F : Set α} (hs : IsPreconnected s)
    (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ connectedComponentIn F x := by
  have : IsPreconnected (((↑) : F → α) ⁻¹' s) := by
    refine inducing_subtype_val.isPreconnected_image.mp ?_
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hsF]
  have h2xs : (⟨x, hsF hxs⟩ : F) ∈ (↑) ⁻¹' s := by
    rw [mem_preimage]
    exact hxs
  have := this.subset_connectedComponent h2xs
  rw [connectedComponentIn_eq_image (hsF hxs)]
  refine Subset.trans ?_ (image_subset _ this)
  rw [Subtype.image_preimage_coe, inter_eq_right.mpr hsF]

theorem IsConnected.subset_connectedComponent {x : α} {s : Set α} (H1 : IsConnected s)
    (H2 : x ∈ s) : s ⊆ connectedComponent x :=
  H1.2.subset_connectedComponent H2

theorem IsPreconnected.connectedComponentIn {x : α} {F : Set α} (h : IsPreconnected F)
    (hx : x ∈ F) : connectedComponentIn F x = F :=
  (connectedComponentIn_subset F x).antisymm (h.subset_connectedComponentIn hx subset_rfl)

theorem connectedComponent_eq {x y : α} (h : y ∈ connectedComponent x) :
    connectedComponent x = connectedComponent y :=
  eq_of_subset_of_subset (isConnected_connectedComponent.subset_connectedComponent h)
    (isConnected_connectedComponent.subset_connectedComponent
      (Set.mem_of_mem_of_subset mem_connectedComponent
        (isConnected_connectedComponent.subset_connectedComponent h)))

theorem connectedComponent_eq_iff_mem {x y : α} :
    connectedComponent x = connectedComponent y ↔ x ∈ connectedComponent y :=
  ⟨fun h => h ▸ mem_connectedComponent, fun h => (connectedComponent_eq h).symm⟩

theorem connectedComponentIn_eq {x y : α} {F : Set α} (h : y ∈ connectedComponentIn F x) :
    connectedComponentIn F x = connectedComponentIn F y := by
  have hx : x ∈ F := connectedComponentIn_nonempty_iff.mp ⟨y, h⟩
  simp_rw [connectedComponentIn_eq_image hx] at h ⊢
  obtain ⟨⟨y, hy⟩, h2y, rfl⟩ := h
  simp_rw [connectedComponentIn_eq_image hy, connectedComponent_eq h2y]

theorem connectedComponentIn_univ (x : α) : connectedComponentIn univ x = connectedComponent x :=
  subset_antisymm
    (isPreconnected_connectedComponentIn.subset_connectedComponent <|
      mem_connectedComponentIn trivial)
    (isPreconnected_connectedComponent.subset_connectedComponentIn mem_connectedComponent <|
      subset_univ _)

theorem connectedComponent_disjoint {x y : α} (h : connectedComponent x ≠ connectedComponent y) :
    Disjoint (connectedComponent x) (connectedComponent y) :=
  Set.disjoint_left.2 fun _ h1 h2 =>
    h ((connectedComponent_eq h1).trans (connectedComponent_eq h2).symm)

theorem isClosed_connectedComponent {x : α} : IsClosed (connectedComponent x) :=
  closure_subset_iff_isClosed.1 <|
    isConnected_connectedComponent.closure.subset_connectedComponent <|
      subset_closure mem_connectedComponent

theorem Continuous.image_connectedComponent_subset [TopologicalSpace β] {f : α → β}
    (h : Continuous f) (a : α) : f '' connectedComponent a ⊆ connectedComponent (f a) :=
  (isConnected_connectedComponent.image f h.continuousOn).subset_connectedComponent
    ((mem_image f (connectedComponent a) (f a)).2 ⟨a, mem_connectedComponent, rfl⟩)

theorem Continuous.image_connectedComponentIn_subset [TopologicalSpace β] {f : α → β} {s : Set α}
    {a : α} (hf : Continuous f) (hx : a ∈ s) :
    f '' connectedComponentIn s a ⊆ connectedComponentIn (f '' s) (f a) :=
  (isPreconnected_connectedComponentIn.image _ hf.continuousOn).subset_connectedComponentIn
    (mem_image_of_mem _ <| mem_connectedComponentIn hx)
    (image_subset _ <| connectedComponentIn_subset _ _)

theorem Continuous.mapsTo_connectedComponent [TopologicalSpace β] {f : α → β} (h : Continuous f)
    (a : α) : MapsTo f (connectedComponent a) (connectedComponent (f a)) :=
  mapsTo'.2 <| h.image_connectedComponent_subset a

theorem Continuous.mapsTo_connectedComponentIn [TopologicalSpace β] {f : α → β} {s : Set α}
    (h : Continuous f) {a : α} (hx : a ∈ s) :
    MapsTo f (connectedComponentIn s a) (connectedComponentIn (f '' s) (f a)) :=
  mapsTo'.2 <| image_connectedComponentIn_subset h hx

theorem irreducibleComponent_subset_connectedComponent {x : α} :
    irreducibleComponent x ⊆ connectedComponent x :=
  isIrreducible_irreducibleComponent.isConnected.subset_connectedComponent mem_irreducibleComponent

@[mono]
theorem connectedComponentIn_mono (x : α) {F G : Set α} (h : F ⊆ G) :
    connectedComponentIn F x ⊆ connectedComponentIn G x := by
  by_cases hx : x ∈ F
  · rw [connectedComponentIn_eq_image hx, connectedComponentIn_eq_image (h hx), ←
      show ((↑) : G → α) ∘ inclusion h = (↑) from rfl, image_comp]
    exact image_subset _ ((continuous_inclusion h).image_connectedComponent_subset ⟨x, hx⟩)
  · rw [connectedComponentIn_eq_empty hx]
    exact Set.empty_subset _

/-- A preconnected space is one where there is no non-trivial open partition. -/
class PreconnectedSpace (α : Type u) [TopologicalSpace α] : Prop where
  /-- The universal set `Set.univ` in a preconnected space is a preconnected set. -/
  isPreconnected_univ : IsPreconnected (univ : Set α)

export PreconnectedSpace (isPreconnected_univ)

/-- A connected space is a nonempty one where there is no non-trivial open partition. -/
class ConnectedSpace (α : Type u) [TopologicalSpace α] extends PreconnectedSpace α : Prop where
  /-- A connected space is nonempty. -/
  toNonempty : Nonempty α

attribute [instance 50] ConnectedSpace.toNonempty  -- see Note [lower instance priority]

-- see Note [lower instance priority]
theorem isConnected_univ [ConnectedSpace α] : IsConnected (univ : Set α) :=
  ⟨univ_nonempty, isPreconnected_univ⟩

lemma preconnectedSpace_iff_univ : PreconnectedSpace α ↔ IsPreconnected (univ : Set α) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

lemma connectedSpace_iff_univ : ConnectedSpace α ↔ IsConnected (univ : Set α) :=
  ⟨fun h ↦ ⟨univ_nonempty, h.1.1⟩,
   fun h ↦ ConnectedSpace.mk (toPreconnectedSpace := ⟨h.2⟩) ⟨h.1.some⟩⟩

theorem isPreconnected_range [TopologicalSpace β] [PreconnectedSpace α] {f : α → β}
    (h : Continuous f) : IsPreconnected (range f) :=
  @image_univ _ _ f ▸ isPreconnected_univ.image _ h.continuousOn

theorem isConnected_range [TopologicalSpace β] [ConnectedSpace α] {f : α → β} (h : Continuous f) :
    IsConnected (range f) :=
  ⟨range_nonempty f, isPreconnected_range h⟩

theorem Function.Surjective.connectedSpace [ConnectedSpace α] [TopologicalSpace β]
    {f : α → β} (hf : Surjective f) (hf' : Continuous f) : ConnectedSpace β := by
  rw [connectedSpace_iff_univ, ← hf.range_eq]
  exact isConnected_range hf'

instance Quotient.instConnectedSpace {s : Setoid α} [ConnectedSpace α] :
    ConnectedSpace (Quotient s) :=
  (surjective_quotient_mk' _).connectedSpace continuous_coinduced_rng

theorem DenseRange.preconnectedSpace [TopologicalSpace β] [PreconnectedSpace α] {f : α → β}
    (hf : DenseRange f) (hc : Continuous f) : PreconnectedSpace β :=
  ⟨hf.closure_eq ▸ (isPreconnected_range hc).closure⟩

theorem connectedSpace_iff_connectedComponent :
    ConnectedSpace α ↔ ∃ x : α, connectedComponent x = univ := by
  constructor
  · rintro ⟨⟨x⟩⟩
    exact
      ⟨x, eq_univ_of_univ_subset <| isPreconnected_univ.subset_connectedComponent (mem_univ x)⟩
  · rintro ⟨x, h⟩
    haveI : PreconnectedSpace α :=
      ⟨by rw [← h]; exact isPreconnected_connectedComponent⟩
    exact ⟨⟨x⟩⟩

theorem preconnectedSpace_iff_connectedComponent :
    PreconnectedSpace α ↔ ∀ x : α, connectedComponent x = univ := by
  constructor
  · intro h x
    exact eq_univ_of_univ_subset <| isPreconnected_univ.subset_connectedComponent (mem_univ x)
  · intro h
    cases' isEmpty_or_nonempty α with hα hα
    · exact ⟨by rw [univ_eq_empty_iff.mpr hα]; exact isPreconnected_empty⟩
    · exact ⟨by rw [← h (Classical.choice hα)]; exact isPreconnected_connectedComponent⟩

@[simp]
theorem PreconnectedSpace.connectedComponent_eq_univ {X : Type*} [TopologicalSpace X]
    [h : PreconnectedSpace X] (x : X) : connectedComponent x = univ :=
  preconnectedSpace_iff_connectedComponent.mp h x

instance [TopologicalSpace β] [PreconnectedSpace α] [PreconnectedSpace β] :
    PreconnectedSpace (α × β) :=
  ⟨by
    rw [← univ_prod_univ]
    exact isPreconnected_univ.prod isPreconnected_univ⟩

instance [TopologicalSpace β] [ConnectedSpace α] [ConnectedSpace β] : ConnectedSpace (α × β) :=
  ⟨inferInstance⟩

instance [∀ i, TopologicalSpace (π i)] [∀ i, PreconnectedSpace (π i)] :
    PreconnectedSpace (∀ i, π i) :=
  ⟨by rw [← pi_univ univ]; exact isPreconnected_univ_pi fun i => isPreconnected_univ⟩

instance [∀ i, TopologicalSpace (π i)] [∀ i, ConnectedSpace (π i)] : ConnectedSpace (∀ i, π i) :=
  ⟨inferInstance⟩

-- see Note [lower instance priority]
instance (priority := 100) PreirreducibleSpace.preconnectedSpace (α : Type u) [TopologicalSpace α]
    [PreirreducibleSpace α] : PreconnectedSpace α :=
  ⟨isPreirreducible_univ.isPreconnected⟩

-- see Note [lower instance priority]
instance (priority := 100) IrreducibleSpace.connectedSpace (α : Type u) [TopologicalSpace α]
    [IrreducibleSpace α] : ConnectedSpace α where toNonempty := IrreducibleSpace.toNonempty

/-- A continuous map from a connected space to a disjoint union `Σ i, π i` can be lifted to one of
the components `π i`. See also `ContinuousMap.exists_lift_sigma` for a version with bundled
`ContinuousMap`s. -/
theorem Continuous.exists_lift_sigma [ConnectedSpace α] [∀ i, TopologicalSpace (π i)]
    {f : α → Σ i, π i} (hf : Continuous f) :
    ∃ (i : ι) (g : α → π i), Continuous g ∧ f = Sigma.mk i ∘ g := by
  obtain ⟨i, hi⟩ : ∃ i, range f ⊆ range (.mk i) := by
    rcases Sigma.isConnected_iff.1 (isConnected_range hf) with ⟨i, s, -, hs⟩
    exact ⟨i, hs.trans_subset (image_subset_range _ _)⟩
  rcases range_subset_range_iff_exists_comp.1 hi with ⟨g, rfl⟩
  refine ⟨i, g, ?_, rfl⟩
  rwa [← embedding_sigmaMk.continuous_iff] at hf

theorem nonempty_inter [PreconnectedSpace α] {s t : Set α} :
    IsOpen s → IsOpen t → s ∪ t = univ → s.Nonempty → t.Nonempty → (s ∩ t).Nonempty := by
  simpa only [univ_inter, univ_subset_iff] using @PreconnectedSpace.isPreconnected_univ α _ _ s t

theorem isClopen_iff [PreconnectedSpace α] {s : Set α} : IsClopen s ↔ s = ∅ ∨ s = univ :=
  ⟨fun hs =>
    by_contradiction fun h =>
      have h1 : s ≠ ∅ ∧ sᶜ ≠ ∅ :=
        ⟨mt Or.inl h,
          mt (fun h2 => Or.inr <| (by rw [← compl_compl s, h2, compl_empty] : s = univ)) h⟩
      let ⟨_, h2, h3⟩ :=
        nonempty_inter hs.2 hs.1.isOpen_compl (union_compl_self s) (nonempty_iff_ne_empty.2 h1.1)
          (nonempty_iff_ne_empty.2 h1.2)
      h3 h2,
    by rintro (rfl | rfl) <;> [exact isClopen_empty; exact isClopen_univ]⟩

theorem IsClopen.eq_univ [PreconnectedSpace α] {s : Set α} (h' : IsClopen s) (h : s.Nonempty) :
    s = univ :=
  (isClopen_iff.mp h').resolve_left h.ne_empty

section disjoint_subsets

variable [PreconnectedSpace α]
  {s : ι → Set α} (h_nonempty : ∀ i, (s i).Nonempty) (h_disj : Pairwise (Disjoint on s))

/-- In a preconnected space, any disjoint family of non-empty clopen subsets has at most one
element. -/
lemma subsingleton_of_disjoint_isClopen
    (h_clopen : ∀ i, IsClopen (s i)) :
    Subsingleton ι := by
  replace h_nonempty : ∀ i, s i ≠ ∅ := by intro i; rw [← nonempty_iff_ne_empty]; exact h_nonempty i
  rw [← not_nontrivial_iff_subsingleton]
  by_contra contra
  obtain ⟨i, j, h_ne⟩ := contra
  replace h_ne : s i ∩ s j = ∅ := by
    simpa only [← bot_eq_empty, eq_bot_iff, ← inf_eq_inter, ← disjoint_iff_inf_le] using h_disj h_ne
  cases' isClopen_iff.mp (h_clopen i) with hi hi
  · exact h_nonempty i hi
  · rw [hi, univ_inter] at h_ne
    exact h_nonempty j h_ne

/-- In a preconnected space, any disjoint cover by non-empty open subsets has at most one
element. -/
lemma subsingleton_of_disjoint_isOpen_iUnion_eq_univ
    (h_open : ∀ i, IsOpen (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨?_, h_open i⟩)
  rw [← isOpen_compl_iff, compl_eq_univ_diff, ← h_Union, iUnion_diff]
  refine isOpen_iUnion (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_open j

/-- In a preconnected space, any finite disjoint cover by non-empty closed subsets has at most one
element. -/
lemma subsingleton_of_disjoint_isClosed_iUnion_eq_univ [Finite ι]
    (h_closed : ∀ i, IsClosed (s i)) (h_Union : ⋃ i, s i = univ) :
    Subsingleton ι := by
  refine subsingleton_of_disjoint_isClopen h_nonempty h_disj (fun i ↦ ⟨h_closed i, ?_⟩)
  rw [← isClosed_compl_iff, compl_eq_univ_diff, ← h_Union, iUnion_diff]
  refine isClosed_iUnion_of_finite (fun j ↦ ?_)
  rcases eq_or_ne i j with rfl | h_ne
  · simp
  · simpa only [(h_disj h_ne.symm).sdiff_eq_left] using h_closed j

end disjoint_subsets

theorem frontier_eq_empty_iff [PreconnectedSpace α] {s : Set α} :
    frontier s = ∅ ↔ s = ∅ ∨ s = univ :=
  isClopen_iff_frontier_eq_empty.symm.trans isClopen_iff

theorem nonempty_frontier_iff [PreconnectedSpace α] {s : Set α} :
    (frontier s).Nonempty ↔ s.Nonempty ∧ s ≠ univ := by
  simp only [nonempty_iff_ne_empty, Ne, frontier_eq_empty_iff, not_or]

theorem Subtype.preconnectedSpace {s : Set α} (h : IsPreconnected s) : PreconnectedSpace s where
  isPreconnected_univ := by
    rwa [← inducing_subtype_val.isPreconnected_image, image_univ, Subtype.range_val]

theorem Subtype.connectedSpace {s : Set α} (h : IsConnected s) : ConnectedSpace s where
  toPreconnectedSpace := Subtype.preconnectedSpace h.isPreconnected
  toNonempty := h.nonempty.to_subtype

theorem isPreconnected_iff_preconnectedSpace {s : Set α} : IsPreconnected s ↔ PreconnectedSpace s :=
  ⟨Subtype.preconnectedSpace, fun h => by
    simpa using isPreconnected_univ.image ((↑) : s → α) continuous_subtype_val.continuousOn⟩

theorem isConnected_iff_connectedSpace {s : Set α} : IsConnected s ↔ ConnectedSpace s :=
  ⟨Subtype.connectedSpace, fun h =>
    ⟨nonempty_subtype.mp h.2, isPreconnected_iff_preconnectedSpace.mpr h.1⟩⟩

/-- In a preconnected space, given a transitive relation `P`, if `P x y` and `P y x` are true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a version of the fact
that, if an equivalence relation has open classes, then it has a single equivalence class. -/
lemma PreconnectedSpace.induction₂' [PreconnectedSpace α] (P : α → α → Prop)
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y ∧ P y x) (h' : Transitive P) (x y : α) :
    P x y := by
  let u := {z | P x z}
  have A : IsClosed u := by
    apply isClosed_iff_nhds.2 (fun z hz ↦ ?_)
    rcases hz _ (h z) with ⟨t, ht, h't⟩
    exact h' h't ht.2
  have B : IsOpen u := by
    apply isOpen_iff_mem_nhds.2 (fun z hz ↦ ?_)
    filter_upwards [h z] with t ht
    exact h' hz ht.1
  have C : u.Nonempty := ⟨x, (mem_of_mem_nhds (h x)).1⟩
  have D : u = Set.univ := IsClopen.eq_univ ⟨A, B⟩ C
  show y ∈ u
  simp [D]

/-- In a preconnected space, if a symmetric transitive relation `P x y` is true for `y` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that, if an equivalence
relation has open classes, then it has a single equivalence class. -/
lemma PreconnectedSpace.induction₂ [PreconnectedSpace α] (P : α → α → Prop)
    (h : ∀ x, ∀ᶠ y in 𝓝 x, P x y) (h' : Transitive P) (h'' : Symmetric P) (x y : α) :
    P x y := by
  refine PreconnectedSpace.induction₂' P (fun z ↦ ?_) h' x y
  filter_upwards [h z] with a ha
  exact ⟨ha, h'' ha⟩

/-- In a preconnected set, given a transitive relation `P`, if `P x y` and `P y x` are true
for `y` close enough to `x`, then `P x y` holds for all `x, y`. This is a version of the fact
that, if an equivalence relation has open classes, then it has a single equivalence class. -/
lemma IsPreconnected.induction₂' {s : Set α} (hs : IsPreconnected s) (P : α → α → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, P x y ∧ P y x)
    (h' : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → P x y → P y z → P x z)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : P x y := by
  let Q : s → s → Prop := fun a b ↦ P a b
  show Q ⟨x, hx⟩ ⟨y, hy⟩
  have : PreconnectedSpace s := Subtype.preconnectedSpace hs
  apply PreconnectedSpace.induction₂'
  · rintro ⟨x, hx⟩
    have Z := h x hx
    rwa [nhdsWithin_eq_map_subtype_coe] at Z
  · rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hab hbc
    exact h' a b c ha hb hc hab hbc

/-- In a preconnected set, if a symmetric transitive relation `P x y` is true for `y` close
enough to `x`, then it holds for all `x, y`. This is a version of the fact that, if an equivalence
relation has open classes, then it has a single equivalence class. -/
lemma IsPreconnected.induction₂ {s : Set α} (hs : IsPreconnected s) (P : α → α → Prop)
    (h : ∀ x ∈ s, ∀ᶠ y in 𝓝[s] x, P x y)
    (h' : ∀ x y z, x ∈ s → y ∈ s → z ∈ s → P x y → P y z → P x z)
    (h'' : ∀ x y, x ∈ s → y ∈ s → P x y → P y x)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : P x y := by
  apply hs.induction₂' P (fun z hz ↦ ?_) h' hx hy
  filter_upwards [h z hz, self_mem_nhdsWithin] with a ha h'a
  exact ⟨ha, h'' z a hz h'a ha⟩

/-- A set `s` is preconnected if and only if for every cover by two open sets that are disjoint on
`s`, it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_disjoint {s : Set α} :
    IsPreconnected s ↔
      ∀ u v, IsOpen u → IsOpen v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    specialize h u v hu hv hs
    contrapose! huv
    simp [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    cases' h with h h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/-- A set `s` is connected if and only if
for every cover by a finite collection of open sets that are pairwise disjoint on `s`,
it is contained in one of the members of the collection. -/
theorem isConnected_iff_sUnion_disjoint_open {s : Set α} :
    IsConnected s ↔
      ∀ U : Finset (Set α), (∀ u v : Set α, u ∈ U → v ∈ U → (s ∩ (u ∩ v)).Nonempty → u = v) →
        (∀ u ∈ U, IsOpen u) → (s ⊆ ⋃₀ ↑U) → ∃ u ∈ U, s ⊆ u := by
  rw [IsConnected, isPreconnected_iff_subset_of_disjoint]
  refine ⟨fun ⟨hne, h⟩ U hU hUo hsU => ?_, fun h => ⟨?_, fun u v hu hv hs hsuv => ?_⟩⟩
  · induction U using Finset.induction_on with
    | empty => exact absurd (by simpa using hsU) hne.not_subset_empty
    | @insert u U uU IH =>
      simp only [← forall_cond_comm, Finset.forall_mem_insert, Finset.exists_mem_insert,
        Finset.coe_insert, sUnion_insert, implies_true, true_and] at *
      refine (h _ hUo.1 (⋃₀ ↑U) (isOpen_sUnion hUo.2) hsU ?_).imp_right ?_
      · refine subset_empty_iff.1 fun x ⟨hxs, hxu, v, hvU, hxv⟩ => ?_
        exact ne_of_mem_of_not_mem hvU uU (hU.1 v hvU ⟨x, hxs, hxu, hxv⟩).symm
      · exact IH (fun u hu => (hU.2 u hu).2) hUo.2
  · simpa [subset_empty_iff, nonempty_iff_ne_empty] using h ∅
  · rw [← not_nonempty_iff_eq_empty] at hsuv
    have := hsuv; rw [inter_comm u] at this
    simpa [*, or_imp, forall_and] using h {u, v}

-- Porting note: `IsPreconnected.subset_isClopen` moved up from here

/-- Preconnected sets are either contained in or disjoint to any given clopen set. -/
theorem disjoint_or_subset_of_isClopen {s t : Set α} (hs : IsPreconnected s) (ht : IsClopen t) :
    Disjoint s t ∨ s ⊆ t :=
  (disjoint_or_nonempty_inter s t).imp_right <| hs.subset_isClopen ht

/-- A set `s` is preconnected if and only if
for every cover by two closed sets that are disjoint on `s`,
it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_disjoint_closed :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → s ∩ (u ∩ v) = ∅ → s ⊆ u ∨ s ⊆ v := by
  constructor <;> intro h
  · intro u v hu hv hs huv
    rw [isPreconnected_closed_iff] at h
    specialize h u v hu hv hs
    contrapose! huv
    simp [not_subset] at huv
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩
  · rw [isPreconnected_closed_iff]
    intro u v hu hv hs hsu hsv
    by_contra H
    specialize h u v hu hv hs (Set.not_nonempty_iff_eq_empty.mp H)
    apply H
    cases' h with h h
    · rcases hsv with ⟨x, hxs, hxv⟩
      exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩
    · rcases hsu with ⟨x, hxs, hxu⟩
      exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩

/-- A closed set `s` is preconnected if and only if for every cover by two closed sets that are
disjoint, it is contained in one of the two covering sets. -/
theorem isPreconnected_iff_subset_of_fully_disjoint_closed {s : Set α} (hs : IsClosed s) :
    IsPreconnected s ↔
      ∀ u v, IsClosed u → IsClosed v → s ⊆ u ∪ v → Disjoint u v → s ⊆ u ∨ s ⊆ v := by
  refine isPreconnected_iff_subset_of_disjoint_closed.trans ⟨?_, ?_⟩ <;> intro H u v hu hv hss huv
  · apply H u v hu hv hss
    rw [huv.inter_eq, inter_empty]
  have H1 := H (u ∩ s) (v ∩ s)
  rw [subset_inter_iff, subset_inter_iff] at H1
  simp only [Subset.refl, and_true] at H1
  apply H1 (hu.inter hs) (hv.inter hs)
  · rw [← union_inter_distrib_right]
    exact subset_inter hss Subset.rfl
  · rwa [disjoint_iff_inter_eq_empty, ← inter_inter_distrib_right, inter_comm]

theorem IsClopen.connectedComponent_subset {x} (hs : IsClopen s) (hx : x ∈ s) :
    connectedComponent x ⊆ s :=
  isPreconnected_connectedComponent.subset_isClopen hs ⟨x, mem_connectedComponent, hx⟩

/-- The connected component of a point is always a subset of the intersection of all its clopen
neighbourhoods. -/
theorem connectedComponent_subset_iInter_isClopen {x : α} :
    connectedComponent x ⊆ ⋂ Z : { Z : Set α // IsClopen Z ∧ x ∈ Z }, Z :=
  subset_iInter fun Z => Z.2.1.connectedComponent_subset Z.2.2

/-- A clopen set is the union of its connected components. -/
theorem IsClopen.biUnion_connectedComponent_eq {Z : Set α} (h : IsClopen Z) :
    ⋃ x ∈ Z, connectedComponent x = Z :=
  Subset.antisymm (iUnion₂_subset fun _ => h.connectedComponent_subset) fun _ h =>
    mem_iUnion₂_of_mem h mem_connectedComponent

/-- The preimage of a connected component is preconnected if the function has connected fibers
and a subset is closed iff the preimage is. -/
theorem preimage_connectedComponent_connected [TopologicalSpace β] {f : α → β}
    (connected_fibers : ∀ t : β, IsConnected (f ⁻¹' {t}))
    (hcl : ∀ T : Set β, IsClosed T ↔ IsClosed (f ⁻¹' T)) (t : β) :
    IsConnected (f ⁻¹' connectedComponent t) := by
  -- The following proof is essentially https://stacks.math.columbia.edu/tag/0377
  -- although the statement is slightly different
  have hf : Surjective f := Surjective.of_comp fun t : β => (connected_fibers t).1
  refine ⟨Nonempty.preimage connectedComponent_nonempty hf, ?_⟩
  have hT : IsClosed (f ⁻¹' connectedComponent t) :=
    (hcl (connectedComponent t)).1 isClosed_connectedComponent
  -- To show it's preconnected we decompose (f ⁻¹' connectedComponent t) as a subset of two
  -- closed disjoint sets in α. We want to show that it's a subset of either.
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hT]
  intro u v hu hv huv uv_disj
  -- To do this we decompose connectedComponent t into T₁ and T₂
  -- we will show that connectedComponent t is a subset of either and hence
  -- (f ⁻¹' connectedComponent t) is a subset of u or v
  let T₁ := { t' ∈ connectedComponent t | f ⁻¹' {t'} ⊆ u }
  let T₂ := { t' ∈ connectedComponent t | f ⁻¹' {t'} ⊆ v }
  have fiber_decomp : ∀ t' ∈ connectedComponent t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v := by
    intro t' ht'
    apply isPreconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv
    · exact Subset.trans (preimage_mono (singleton_subset_iff.2 ht')) huv
    rw [uv_disj.inter_eq, inter_empty]
  have T₁_u : f ⁻¹' T₁ = f ⁻¹' connectedComponent t ∩ u := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hau⟩
    constructor
    · exact mem_preimage.1 hat
    refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_right fun h => ?_
    exact uv_disj.subset_compl_right hau (h rfl)
  -- This proof is exactly the same as the above (modulo some symmetry)
  have T₂_v : f ⁻¹' T₂ = f ⁻¹' connectedComponent t ∩ v := by
    apply eq_of_subset_of_subset
    · rw [← biUnion_preimage_singleton]
      refine iUnion₂_subset fun t' ht' => subset_inter ?_ ht'.2
      rw [hf.preimage_subset_preimage_iff, singleton_subset_iff]
      exact ht'.1
    rintro a ⟨hat, hav⟩
    constructor
    · exact mem_preimage.1 hat
    · refine (fiber_decomp (f a) (mem_preimage.1 hat)).resolve_left fun h => ?_
      exact uv_disj.subset_compl_left hav (h rfl)
  -- Now we show T₁, T₂ are closed, cover connectedComponent t and are disjoint.
  have hT₁ : IsClosed T₁ := (hcl T₁).2 (T₁_u.symm ▸ IsClosed.inter hT hu)
  have hT₂ : IsClosed T₂ := (hcl T₂).2 (T₂_v.symm ▸ IsClosed.inter hT hv)
  have T_decomp : connectedComponent t ⊆ T₁ ∪ T₂ := fun t' ht' => by
    rw [mem_union t' T₁ T₂]
    cases' fiber_decomp t' ht' with htu htv
    · left
      exact ⟨ht', htu⟩
    right
    exact ⟨ht', htv⟩
  have T_disjoint : Disjoint T₁ T₂ := by
    refine Disjoint.of_preimage hf ?_
    rw [T₁_u, T₂_v, disjoint_iff_inter_eq_empty, ← inter_inter_distrib_left, uv_disj.inter_eq,
      inter_empty]
  -- Now we do cases on whether (connectedComponent t) is a subset of T₁ or T₂ to show
  -- that the preimage is a subset of u or v.
  cases' (isPreconnected_iff_subset_of_fully_disjoint_closed isClosed_connectedComponent).1
    isPreconnected_connectedComponent T₁ T₂ hT₁ hT₂ T_decomp T_disjoint with h h
  · left
    rw [Subset.antisymm_iff] at T₁_u
    suffices f ⁻¹' connectedComponent t ⊆ f ⁻¹' T₁
      from (this.trans T₁_u.1).trans inter_subset_right
    exact preimage_mono h
  · right
    rw [Subset.antisymm_iff] at T₂_v
    suffices f ⁻¹' connectedComponent t ⊆ f ⁻¹' T₂
      from (this.trans T₂_v.1).trans inter_subset_right
    exact preimage_mono h

theorem QuotientMap.preimage_connectedComponent [TopologicalSpace β] {f : α → β}
    (hf : QuotientMap f) (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f ⁻¹' connectedComponent (f a) = connectedComponent a :=
  ((preimage_connectedComponent_connected h_fibers (fun _ => hf.isClosed_preimage.symm)
      _).subset_connectedComponent mem_connectedComponent).antisymm
    (hf.continuous.mapsTo_connectedComponent a)

theorem QuotientMap.image_connectedComponent [TopologicalSpace β] {f : α → β} (hf : QuotientMap f)
    (h_fibers : ∀ y : β, IsConnected (f ⁻¹' {y})) (a : α) :
    f '' connectedComponent a = connectedComponent (f a) := by
  rw [← hf.preimage_connectedComponent h_fibers, image_preimage_eq _ hf.surjective]

end Preconnected

section connectedComponentSetoid
/-- The setoid of connected components of a topological space -/
def connectedComponentSetoid (α : Type*) [TopologicalSpace α] : Setoid α :=
  ⟨fun x y => connectedComponent x = connectedComponent y,
    ⟨fun x => by trivial, fun h1 => h1.symm, fun h1 h2 => h1.trans h2⟩⟩

/-- The quotient of a space by its connected components -/
def ConnectedComponents (α : Type u) [TopologicalSpace α] :=
  Quotient (connectedComponentSetoid α)

namespace ConnectedComponents

/-- Coercion from a topological space to the set of connected components of this space. -/
def mk : α → ConnectedComponents α := Quotient.mk''

instance : CoeTC α (ConnectedComponents α) := ⟨mk⟩

@[simp]
theorem coe_eq_coe {x y : α} :
    (x : ConnectedComponents α) = y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''

theorem coe_ne_coe {x y : α} :
    (x : ConnectedComponents α) ≠ y ↔ connectedComponent x ≠ connectedComponent y :=
  coe_eq_coe.not

theorem coe_eq_coe' {x y : α} : (x : ConnectedComponents α) = y ↔ x ∈ connectedComponent y :=
  coe_eq_coe.trans connectedComponent_eq_iff_mem

instance [Inhabited α] : Inhabited (ConnectedComponents α) :=
  ⟨mk default⟩

instance : TopologicalSpace (ConnectedComponents α) :=
  inferInstanceAs (TopologicalSpace (Quotient _))

theorem surjective_coe : Surjective (mk : α → ConnectedComponents α) :=
  surjective_quot_mk _

theorem quotientMap_coe : QuotientMap (mk : α → ConnectedComponents α) :=
  quotientMap_quot_mk

@[continuity]
theorem continuous_coe : Continuous (mk : α → ConnectedComponents α) :=
  quotientMap_coe.continuous

@[simp]
theorem range_coe : range (mk : α → ConnectedComponents α) = univ :=
  surjective_coe.range_eq

end ConnectedComponents

/-- The preimage of a singleton in `connectedComponents` is the connected component
of an element in the equivalence class. -/
theorem connectedComponents_preimage_singleton {x : α} :
    (↑) ⁻¹' ({↑x} : Set (ConnectedComponents α)) = connectedComponent x := by
  ext y
  rw [mem_preimage, mem_singleton_iff, ConnectedComponents.coe_eq_coe']

/-- The preimage of the image of a set under the quotient map to `connectedComponents α`
is the union of the connected components of the elements in it. -/
theorem connectedComponents_preimage_image (U : Set α) :
    (↑) ⁻¹' ((↑) '' U : Set (ConnectedComponents α)) = ⋃ x ∈ U, connectedComponent x := by
  simp only [connectedComponents_preimage_singleton, preimage_iUnion₂, image_eq_iUnion]



end connectedComponentSetoid

/-- If every map to `Bool` (a discrete two-element space), that is
continuous on a set `s`, is constant on s, then s is preconnected -/
theorem isPreconnected_of_forall_constant {s : Set α}
    (hs : ∀ f : α → Bool, ContinuousOn f s → ∀ x ∈ s, ∀ y ∈ s, f x = f y) : IsPreconnected s := by
  unfold IsPreconnected
  by_contra!
  rcases this with ⟨u, v, u_op, v_op, hsuv, ⟨x, x_in_s, x_in_u⟩, ⟨y, y_in_s, y_in_v⟩, H⟩
  have hy : y ∉ u := fun y_in_u => eq_empty_iff_forall_not_mem.mp H y ⟨y_in_s, ⟨y_in_u, y_in_v⟩⟩
  have : ContinuousOn u.boolIndicator s := by
    apply (continuousOn_boolIndicator_iff_isClopen _ _).mpr ⟨_, _⟩
    · rw [preimage_subtype_coe_eq_compl hsuv H]
      exact (v_op.preimage continuous_subtype_val).isClosed_compl
    · exact u_op.preimage continuous_subtype_val
  simpa [(u.mem_iff_boolIndicator _).mp x_in_u, (u.not_mem_iff_boolIndicator _).mp hy] using
    hs _ this x x_in_s y y_in_s

/-- A `PreconnectedSpace` version of `isPreconnected_of_forall_constant` -/
theorem preconnectedSpace_of_forall_constant
    (hs : ∀ f : α → Bool, Continuous f → ∀ x y, f x = f y) : PreconnectedSpace α :=
  ⟨isPreconnected_of_forall_constant fun f hf x _ y _ =>
      hs f (continuous_iff_continuousOn_univ.mpr hf) x y⟩
