/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Compactness.LocallyCompact
/-!
# Sigma-compact spaces

A σ-compact space is a topological space that is the union of a countable collection of compact
subspaces.

-/
open Set Filter Topology TopologicalSpace Classical

universe u v

variable {α : Type u} {β : Type v} {ι : Type*} {π : ι → Type*}

variable [TopologicalSpace α] [TopologicalSpace β] {s t : Set α}
/-- A σ-compact space is a space that is the union of a countable collection of compact subspaces.
  Note that a locally compact separable T₂ space need not be σ-compact.
  The sequence can be extracted using `compactCovering`. -/
class SigmaCompactSpace (α : Type*) [TopologicalSpace α] : Prop where
  /-- In a σ-compact space, there exists (by definition) a countable collection of compact subspaces
  that cover the entire space. -/
  exists_compact_covering : ∃ K : ℕ → Set α, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = univ
#align sigma_compact_space SigmaCompactSpace

-- see Note [lower instance priority]
instance (priority := 200) CompactSpace.sigma_compact [CompactSpace α] : SigmaCompactSpace α :=
  ⟨⟨fun _ => univ, fun _ => isCompact_univ, iUnion_const _⟩⟩
#align compact_space.sigma_compact CompactSpace.sigma_compact

theorem SigmaCompactSpace.of_countable (S : Set (Set α)) (Hc : S.Countable)
    (Hcomp : ∀ s ∈ S, IsCompact s) (HU : ⋃₀ S = univ) : SigmaCompactSpace α :=
  ⟨(exists_seq_cover_iff_countable ⟨_, isCompact_empty⟩).2 ⟨S, Hc, Hcomp, HU⟩⟩
#align sigma_compact_space.of_countable SigmaCompactSpace.of_countable

-- see Note [lower instance priority]
instance (priority := 100) sigmaCompactSpace_of_locally_compact_second_countable
    [LocallyCompactSpace α] [SecondCountableTopology α] : SigmaCompactSpace α := by
  choose K hKc hxK using fun x : α => exists_compact_mem_nhds x
  rcases countable_cover_nhds hxK with ⟨s, hsc, hsU⟩
  refine' SigmaCompactSpace.of_countable _ (hsc.image K) (ball_image_iff.2 fun x _ => hKc x) _
  rwa [sUnion_image]
#align sigma_compact_space_of_locally_compact_second_countable sigmaCompactSpace_of_locally_compact_second_countable

-- porting note: doesn't work on the same line
variable (α)
variable [SigmaCompactSpace α]

open SigmaCompactSpace

/-- A choice of compact covering for a `σ`-compact space, chosen to be monotone. -/
def compactCovering : ℕ → Set α :=
  Accumulate exists_compact_covering.choose
#align compact_covering compactCovering

theorem isCompact_compactCovering (n : ℕ) : IsCompact (compactCovering α n) :=
  isCompact_accumulate (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).1 n
#align is_compact_compact_covering isCompact_compactCovering

theorem iUnion_compactCovering : ⋃ n, compactCovering α n = univ := by
  rw [compactCovering, iUnion_accumulate]
  exact (Classical.choose_spec SigmaCompactSpace.exists_compact_covering).2
#align Union_compact_covering iUnion_compactCovering

@[mono]
theorem compactCovering_subset ⦃m n : ℕ⦄ (h : m ≤ n) : compactCovering α m ⊆ compactCovering α n :=
  monotone_accumulate h
#align compact_covering_subset compactCovering_subset

variable {α}

theorem exists_mem_compactCovering (x : α) : ∃ n, x ∈ compactCovering α n :=
  iUnion_eq_univ_iff.mp (iUnion_compactCovering α) x
#align exists_mem_compact_covering exists_mem_compactCovering

instance [SigmaCompactSpace β] : SigmaCompactSpace (α × β) :=
  ⟨⟨fun n => compactCovering α n ×ˢ compactCovering β n, fun _ =>
      (isCompact_compactCovering _ _).prod (isCompact_compactCovering _ _), by
      simp only [iUnion_prod_of_monotone (compactCovering_subset α) (compactCovering_subset β),
        iUnion_compactCovering, univ_prod_univ]⟩⟩

instance [Finite ι] [∀ i, TopologicalSpace (π i)] [∀ i, SigmaCompactSpace (π i)] :
    SigmaCompactSpace (∀ i, π i) := by
  refine' ⟨⟨fun n => Set.pi univ fun i => compactCovering (π i) n,
    fun n => isCompact_univ_pi fun i => isCompact_compactCovering (π i) _, _⟩⟩
  rw [iUnion_univ_pi_of_monotone]
  · simp only [iUnion_compactCovering, pi_univ]
  · exact fun i => compactCovering_subset (π i)

instance [SigmaCompactSpace β] : SigmaCompactSpace (Sum α β) :=
  ⟨⟨fun n => Sum.inl '' compactCovering α n ∪ Sum.inr '' compactCovering β n, fun n =>
      ((isCompact_compactCovering α n).image continuous_inl).union
        ((isCompact_compactCovering β n).image continuous_inr),
      by simp only [iUnion_union_distrib, ← image_iUnion, iUnion_compactCovering, image_univ,
        range_inl_union_range_inr]⟩⟩

instance [Countable ι] [∀ i, TopologicalSpace (π i)] [∀ i, SigmaCompactSpace (π i)] :
    SigmaCompactSpace (Σi, π i) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · rcases exists_surjective_nat ι with ⟨f, hf⟩
    refine' ⟨⟨fun n => ⋃ k ≤ n, Sigma.mk (f k) '' compactCovering (π (f k)) n, fun n => _, _⟩⟩
    · refine' (finite_le_nat _).isCompact_biUnion fun k _ => _
      exact (isCompact_compactCovering _ _).image continuous_sigmaMk
    · simp only [iUnion_eq_univ_iff, Sigma.forall, mem_iUnion]
      rw [hf.forall] -- porting note: `simp only` failed to use `hf.forall`
      intro k y
      rcases exists_mem_compactCovering y with ⟨n, hn⟩
      refine' ⟨max k n, k, le_max_left _ _, mem_image_of_mem _ _⟩
      exact compactCovering_subset _ (le_max_right _ _) hn

protected theorem ClosedEmbedding.sigmaCompactSpace {e : β → α} (he : ClosedEmbedding e) :
    SigmaCompactSpace β :=
  ⟨⟨fun n => e ⁻¹' compactCovering α n, fun n =>
      he.isCompact_preimage (isCompact_compactCovering _ _), by
      rw [← preimage_iUnion, iUnion_compactCovering, preimage_univ]⟩⟩
#align closed_embedding.sigma_compact_space ClosedEmbedding.sigmaCompactSpace

-- porting note: new lemma
theorem IsClosed.sigmaCompactSpace {s : Set α} (hs : IsClosed s) : SigmaCompactSpace s :=
  (closedEmbedding_subtype_val hs).sigmaCompactSpace

instance [SigmaCompactSpace β] : SigmaCompactSpace (ULift.{u} β) :=
  ULift.closedEmbedding_down.sigmaCompactSpace

/-- If `α` is a `σ`-compact space, then a locally finite family of nonempty sets of `α` can have
only countably many elements, `Set.Countable` version. -/
protected theorem LocallyFinite.countable_univ {ι : Type*} {f : ι → Set α} (hf : LocallyFinite f)
    (hne : ∀ i, (f i).Nonempty) : (univ : Set ι).Countable := by
  have := fun n => hf.finite_nonempty_inter_compact (isCompact_compactCovering α n)
  refine (countable_iUnion fun n => (this n).countable).mono fun i _ => ?_
  rcases hne i with ⟨x, hx⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering α) x with ⟨n, hn⟩
  exact mem_iUnion.2 ⟨n, x, hx, hn⟩
#align locally_finite.countable_univ LocallyFinite.countable_univ

/-- If `f : ι → Set α` is a locally finite covering of a σ-compact topological space by nonempty
sets, then the index type `ι` is encodable. -/
protected noncomputable def LocallyFinite.encodable {ι : Type*} {f : ι → Set α}
    (hf : LocallyFinite f) (hne : ∀ i, (f i).Nonempty) : Encodable ι :=
  @Encodable.ofEquiv _ _ (hf.countable_univ hne).toEncodable (Equiv.Set.univ _).symm
#align locally_finite.encodable LocallyFinite.encodable

/-- In a topological space with sigma compact topology, if `f` is a function that sends each point
`x` of a closed set `s` to a neighborhood of `x` within `s`, then for some countable set `t ⊆ s`,
the neighborhoods `f x`, `x ∈ t`, cover the whole set `s`. -/
theorem countable_cover_nhdsWithin_of_sigma_compact {f : α → Set α} {s : Set α} (hs : IsClosed s)
    (hf : ∀ x ∈ s, f x ∈ 𝓝[s] x) : ∃ (t : _) (_ : t ⊆ s), t.Countable ∧ s ⊆ ⋃ x ∈ t, f x := by
  simp only [nhdsWithin, mem_inf_principal] at hf
  choose t ht hsub using fun n =>
    ((isCompact_compactCovering α n).inter_right hs).elim_nhds_subcover _ fun x hx => hf x hx.right
  refine'
    ⟨⋃ n, (t n : Set α), iUnion_subset fun n x hx => (ht n x hx).2,
      countable_iUnion fun n => (t n).countable_toSet, fun x hx => mem_iUnion₂.2 _⟩
  rcases exists_mem_compactCovering x with ⟨n, hn⟩
  rcases mem_iUnion₂.1 (hsub n ⟨hn, hx⟩) with ⟨y, hyt : y ∈ t n, hyf : x ∈ s → x ∈ f y⟩
  exact ⟨y, mem_iUnion.2 ⟨n, hyt⟩, hyf hx⟩
#align countable_cover_nhds_within_of_sigma_compact countable_cover_nhdsWithin_of_sigma_compact

/-- In a topological space with sigma compact topology, if `f` is a function that sends each
point `x` to a neighborhood of `x`, then for some countable set `s`, the neighborhoods `f x`,
`x ∈ s`, cover the whole space. -/
theorem countable_cover_nhds_of_sigma_compact {f : α → Set α} (hf : ∀ x, f x ∈ 𝓝 x) :
    ∃ s : Set α, s.Countable ∧ ⋃ x ∈ s, f x = univ := by
  simp only [← nhdsWithin_univ] at hf
  rcases countable_cover_nhdsWithin_of_sigma_compact isClosed_univ fun x _ => hf x with
    ⟨s, -, hsc, hsU⟩
  exact ⟨s, hsc, univ_subset_iff.1 hsU⟩
#align countable_cover_nhds_of_sigma_compact countable_cover_nhds_of_sigma_compact




/-- An [exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets) of a
topological space is a sequence of compact sets `K n` such that `K n ⊆ interior (K (n + 1))` and
`⋃ n, K n = univ`.

If `X` is a locally compact sigma compact space, then `CompactExhaustion.choice X` provides
a choice of an exhaustion by compact sets. This choice is also available as
`(default : CompactExhaustion X)`. -/
structure CompactExhaustion (X : Type*) [TopologicalSpace X] where
  /-- The sequence of compact sets that form a compact exhaustion. -/
  toFun : ℕ → Set X
  /-- The sets in the compact exhaustion are in fact compact. -/
  isCompact' : ∀ n, IsCompact (toFun n)
  /-- The sets in the compact exhaustion form a sequence:
    each set is contained in the interior of the next. -/
  subset_interior_succ' : ∀ n, toFun n ⊆ interior (toFun (n + 1))
  /-- The union of all sets in a compact exhaustion equals the entire space. -/
  iUnion_eq' : ⋃ n, toFun n = univ
#align compact_exhaustion CompactExhaustion

namespace CompactExhaustion

instance : @RelHomClass (CompactExhaustion α) ℕ (Set α) LE.le HasSubset.Subset where
  coe := toFun
  coe_injective' | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, rfl => rfl
  map_rel f _ _ h := monotone_nat_of_le_succ
    (fun n ↦ (f.subset_interior_succ' n).trans interior_subset) h

variable (K : CompactExhaustion α)

@[simp]
theorem toFun_eq_coe : K.toFun = K := rfl

protected theorem isCompact (n : ℕ) : IsCompact (K n) :=
  K.isCompact' n
#align compact_exhaustion.is_compact CompactExhaustion.isCompact

theorem subset_interior_succ (n : ℕ) : K n ⊆ interior (K (n + 1)) :=
  K.subset_interior_succ' n
#align compact_exhaustion.subset_interior_succ CompactExhaustion.subset_interior_succ

@[mono]
protected theorem subset ⦃m n : ℕ⦄ (h : m ≤ n) : K m ⊆ K n :=
  OrderHomClass.mono K h
#align compact_exhaustion.subset CompactExhaustion.subset

theorem subset_succ (n : ℕ) : K n ⊆ K (n + 1) := K.subset n.le_succ
#align compact_exhaustion.subset_succ CompactExhaustion.subset_succ

theorem subset_interior ⦃m n : ℕ⦄ (h : m < n) : K m ⊆ interior (K n) :=
  Subset.trans (K.subset_interior_succ m) <| interior_mono <| K.subset h
#align compact_exhaustion.subset_interior CompactExhaustion.subset_interior

theorem iUnion_eq : ⋃ n, K n = univ :=
  K.iUnion_eq'
#align compact_exhaustion.Union_eq CompactExhaustion.iUnion_eq

theorem exists_mem (x : α) : ∃ n, x ∈ K n :=
  iUnion_eq_univ_iff.1 K.iUnion_eq x
#align compact_exhaustion.exists_mem CompactExhaustion.exists_mem

/-- The minimal `n` such that `x ∈ K n`. -/
protected noncomputable def find (x : α) : ℕ :=
  Nat.find (K.exists_mem x)
#align compact_exhaustion.find CompactExhaustion.find

theorem mem_find (x : α) : x ∈ K (K.find x) :=
  Nat.find_spec (K.exists_mem x)
#align compact_exhaustion.mem_find CompactExhaustion.mem_find

theorem mem_iff_find_le {x : α} {n : ℕ} : x ∈ K n ↔ K.find x ≤ n :=
  ⟨fun h => Nat.find_min' (K.exists_mem x) h, fun h => K.subset h <| K.mem_find x⟩
#align compact_exhaustion.mem_iff_find_le CompactExhaustion.mem_iff_find_le

/-- Prepend the empty set to a compact exhaustion `K n`. -/
def shiftr : CompactExhaustion α where
  toFun n := Nat.casesOn n ∅ K
  isCompact' n := Nat.casesOn n isCompact_empty K.isCompact
  subset_interior_succ' n := Nat.casesOn n (empty_subset _) K.subset_interior_succ
  iUnion_eq' := iUnion_eq_univ_iff.2 fun x => ⟨K.find x + 1, K.mem_find x⟩
#align compact_exhaustion.shiftr CompactExhaustion.shiftr

@[simp]
theorem find_shiftr (x : α) : K.shiftr.find x = K.find x + 1 :=
  Nat.find_comp_succ _ _ (not_mem_empty _)
#align compact_exhaustion.find_shiftr CompactExhaustion.find_shiftr

theorem mem_diff_shiftr_find (x : α) : x ∈ K.shiftr (K.find x + 1) \ K.shiftr (K.find x) :=
  ⟨K.mem_find _,
    mt K.shiftr.mem_iff_find_le.1 <| by simp only [find_shiftr, not_le, Nat.lt_succ_self]⟩
#align compact_exhaustion.mem_diff_shiftr_find CompactExhaustion.mem_diff_shiftr_find

/-- A choice of an
[exhaustion by compact sets](https://en.wikipedia.org/wiki/Exhaustion_by_compact_sets)
of a weakly locally compact σ-compact space. -/
noncomputable def choice (X : Type*) [TopologicalSpace X] [WeaklyLocallyCompactSpace X]
    [SigmaCompactSpace X] : CompactExhaustion X := by
  apply Classical.choice
  let K : ℕ → { s : Set X // IsCompact s } := fun n =>
    Nat.recOn n ⟨∅, isCompact_empty⟩ fun n s =>
      ⟨(exists_compact_superset s.2).choose ∪ compactCovering X n,
        (exists_compact_superset s.2).choose_spec.1.union (isCompact_compactCovering _ _)⟩
  refine' ⟨⟨fun n => (K n).1, fun n => (K n).2, fun n => _, _⟩⟩
  · exact Subset.trans (exists_compact_superset (K n).2).choose_spec.2
      (interior_mono <| subset_union_left _ _)
  · refine' univ_subset_iff.1 (iUnion_compactCovering X ▸ _)
    exact iUnion_mono' fun n => ⟨n + 1, subset_union_right _ _⟩
#align compact_exhaustion.choice CompactExhaustion.choice

noncomputable instance [LocallyCompactSpace α] [SigmaCompactSpace α] :
    Inhabited (CompactExhaustion α) :=
  ⟨CompactExhaustion.choice α⟩

end CompactExhaustion
