/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.SupIndep

/-!
# Partitions

A `Partition` of an element `a` in a complete lattice is an independent family of nontrivial
elements whose supremum is `a`.

An important special case is where `s : Set α`, where a `Partition s` corresponds to a partition
of the elements of `s` into a family of nonempty sets.
This is equivalent to a transitive and symmetric binary relation `r : α → α → Prop`
where `s` is the set of all `x` for which `r x x`.

Partitions are ordered by refinement: `P ≤ Q` if every part of `P` is less than or equal to a part
of `Q`.

## Main definitions

* `Partition s`: For `[CompleteLattice α]` and `s : α`, a `Partition s` is an independent
  collection of nontrivial elements whose supremum is `s`.
* `Partition.removeBot`: A constructor for `Partition s` that removes `⊥` from a set of parts.

## TODO

* Link this to `Finpartition`.
* Define the partial equivalence relation induced by a partition.

-/

@[expose] public section
variable {α : Type*} {s t x y z : α} {S : Set α}

open Set

/-- A `Partition` of an element `s` of a `CompleteLattice` is a collection of
independent nontrivial elements whose supremum is `s`. -/
structure Partition [CompleteLattice α] (s : α) where
  /-- The collection of parts -/
  parts : Set α
  /-- The parts are `sSupIndep`. -/
  sSupIndep' : sSupIndep parts
  /-- The bottom element is not a part. -/
  bot_notMem' : ⊥ ∉ parts
  /-- The supremum of all parts is `s`. -/
  sSup_eq' : sSup parts = s

namespace Partition

section Basic

variable [CompleteLattice α] {P Q : Partition s}

instance {s : α} : SetLike (Partition s) α where
  coe := Partition.parts
  coe_injective' p p' h := by cases p; cases p'; simpa using h

/-- See Note [custom simps projection]. -/
def Simps.coe {s : α} (P : Partition s) : Set α := P

initialize_simps_projections Partition (parts → coe, as_prefix coe)

@[simp] lemma coe_parts : P.parts = P := rfl

@[ext] lemma ext (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q :=
  SetLike.ext hP

@[simp]
lemma sSupIndep (P : Partition s) : sSupIndep (P : Set α) :=
  P.sSupIndep'

lemma disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : x ≠ y) : Disjoint x y :=
  P.sSupIndep.pairwiseDisjoint hx hy hxy

lemma pairwiseDisjoint : Set.PairwiseDisjoint (P : Set α) id :=
  P.sSupIndep'.pairwiseDisjoint

lemma eq_or_disjoint (hx : x ∈ P) (hy : y ∈ P) : x = y ∨ Disjoint x y :=
  or_iff_not_imp_left.mpr (P.disjoint hx hy)

lemma eq_of_not_disjoint (hx : x ∈ P) (hy : y ∈ P) (hxy : ¬ Disjoint x y) : x = y :=
  (P.eq_or_disjoint hx hy).resolve_right hxy

@[simp]
lemma sSup_eq (P : Partition s) : sSup P = s :=
  P.sSup_eq'

@[simp]
lemma iSup_eq (P : Partition s) : ⨆ x ∈ P, x = s := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

lemma le_of_mem (P : Partition s) (hx : x ∈ P) : x ≤ s :=
  (le_sSup hx).trans_eq P.sSup_eq

lemma parts_nonempty (P : Partition s) (hs : s ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

@[simp]
lemma bot_notMem (P : Partition s) : ⊥ ∉ P :=
  P.bot_notMem'

lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_notMem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

/-- Convert a `Partition s` into a `Partition t` via an equality `s = t`. -/
@[simps]
protected def copy (P : Partition s) (hst : s = t) : Partition t where
  parts := P
  sSupIndep' := P.sSupIndep
  bot_notMem' := P.bot_notMem
  sSup_eq' := hst ▸ P.sSup_eq

@[simp]
lemma mem_copy_iff (hst : s = t) : x ∈ P.copy hst ↔ x ∈ P := Iff.rfl

/-- The natural equivalence between the subtype of parts and the subtype of parts of a copy. -/
@[simps!]
def partscopyEquiv (P : Partition s) (hst : s = t) : ↥(P.copy hst) ≃ ↥P :=
  Equiv.setCongr rfl

/-- A constructor for `Partition s` that removes `⊥` from the set of parts. -/
@[simps]
def removeBot (P : Set α) (indep : _root_.sSupIndep P) (sSup_eq : sSup P = s) : Partition s where
  parts := P \ {⊥}
  sSupIndep' := indep.mono diff_subset
  bot_notMem' := by simp
  sSup_eq' := by simp [← sSup_eq]

@[simp]
lemma mem_removeBot_iff (P : Set α) (indep : _root_.sSupIndep P) (sSup_eq : sSup P = s) :
  x ∈ removeBot P indep sSup_eq ↔ x ∈ P ∧ x ≠ ⊥ := Iff.rfl

@[simp]
lemma notMem_of_bot (P : Partition (⊥ : α)) (x : α) : x ∉ P := by
  rintro hxP
  obtain rfl := le_bot_iff.mp <| P.le_of_mem hxP
  exact P.bot_notMem hxP

/-- There is a unique partition of `⊥`. -/
instance : Unique (Partition (⊥ : α)) where
  default := removeBot {⊥} (sSupIndep_singleton ⊥) sSup_singleton
  uniq P := by
    ext x
    simp

lemma ne_bot_of_mem' (hxP : x ∈ P) : s ≠ ⊥ := by
  rintro rfl
  exact P.notMem_of_bot _ hxP

end Basic

section Order

variable [CompleteLattice α] {P Q : Partition s}

/-- Partitions on `s` are ordered by refinement: `P ≤ Q` if every part of `P` is contained in a part
of `Q`. -/
instance : PartialOrder (Partition s) where
  le P Q := ∀ x ∈ P, ∃ y ∈ Q, x ≤ y
  lt := _
  le_refl P x hx := ⟨x,hx,rfl.le⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ x hxP
    obtain ⟨z, hz, hyz⟩ := hQR y hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hp x h
      obtain ⟨x', hx', hyx'⟩ := hq y hy
      obtain rfl := P.pairwiseDisjoint.eq_of_le h hx' (P.ne_bot_of_mem h)
        (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq x h
    obtain ⟨x', hx', hyx'⟩ := hp y hy
    obtain rfl := Q.pairwiseDisjoint.eq_of_le h hx' (Q.ne_bot_of_mem h)
      (hxy.trans hyx')
    rwa [hxy.antisymm hyx']

lemma le_def : P ≤ Q ↔ ∀ x ∈ P, ∃ y ∈ Q, x ≤ y := Iff.rfl

lemma exists_le_of_mem_le (h : P ≤ Q) (hx : x ∈ P) : ∃ y ∈ Q, x ≤ y := h x hx

lemma exists_unique_of_mem_le (h : P ≤ Q) (hx : x ∈ P) :
    ∃! y ∈ Q, x ≤ y := by
  obtain ⟨y, hy, hxy⟩ := h x hx
  refine ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ => Q.eq_of_not_disjoint hz hy ?_⟩
  have := P.ne_bot_of_mem hx
  contrapose! this
  exact le_bot_iff.mp (this hxz hxy)

/-- The top partition of `s` is the partition with the single part `s`. -/
instance : OrderTop (Partition s) where
  top := removeBot {s} (sSupIndep_singleton s) sSup_singleton
  le_top P x hxP := by
    simp [P.ne_bot_of_mem' hxP, P.le_of_mem hxP]

@[simp] lemma parts_top (hs : s ≠ ⊥) : (⊤ : Partition s).parts = {s} := by
  change (removeBot {s} (sSupIndep_singleton s) sSup_singleton).parts = _
  simpa

@[simp] lemma mem_top_iff {a : α} : a ∈ (⊤ : Partition s) ↔ a = s ∧ a ≠ ⊥ := by
  change a ∈ removeBot {s} (sSupIndep_singleton s) sSup_singleton ↔ _
  rw [mem_removeBot_iff, mem_singleton_iff]

lemma parts_top_subset : ((⊤ : Partition s) : Set α) ⊆ {s} := by
  simp

end Order

section Set

variable {s t u : Set α} {S T : Set (Set α)} {P Q : Partition s}

@[simp] protected lemma sUnion_eq (P : Partition s) : ⋃₀ P = s := P.sSup_eq

lemma nonempty_of_mem (ht : t ∈ P) : t.Nonempty :=
  notMem_singleton_empty.1 <| P.ne_bot_of_mem ht

lemma empty_not_mem : ∅ ∉ P := P.bot_notMem

lemma subset_of_mem (ht : t ∈ P) : t ⊆ s := P.le_of_mem ht

lemma mem_iff_exists : x ∈ s ↔ ∃ t ∈ P, x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨t, htP, hxt⟩ ↦ subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx

lemma eq_of_mem_inter (ht : t ∈ P) (hu : u ∈ P) (hx : x ∈ t ∩ u) : t = u :=
  PairwiseDisjoint.elim P.pairwiseDisjoint ht hu fun
    (hdj : Disjoint t u) ↦ by simp [hdj.inter_eq] at hx

lemma eq_of_mem_of_mem (ht : t ∈ P) (hu : u ∈ P) (hxt : x ∈ t) (hxu : x ∈ u) : t = u :=
  eq_of_mem_inter ht hu ⟨hxt, hxu⟩

lemma exists_unique_of_mem (hx : x ∈ s) : ∃! t, t ∈ P ∧ x ∈ t := by
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, hxt⟩ := hx
  exact ⟨t, hxt, fun u ⟨huP, hxu⟩ ↦ eq_of_mem_inter huP hxt.1 ⟨hxu, hxt.2⟩⟩

lemma mem_iff_unique : x ∈ s ↔ ∃! t, t ∈ P ∧ x ∈ t :=
  ⟨exists_unique_of_mem, fun ⟨_, ⟨htP, hxt⟩, _⟩ ↦ subset_of_mem htP hxt⟩

lemma subset_sUnion_and_mem_iff_mem (hSP : S ⊆ P) : t ⊆ ⋃₀ S ∧ t ∈ P ↔ t ∈ S := by
  refine ⟨fun ⟨htsu, htP⟩ ↦ ?_, fun htS ↦ ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  obtain rfl := eq_of_mem_of_mem htP (hSP hsS) hxt hxs
  exact hsS

@[simp]
lemma subset_sUnion_iff_mem (ht : t ∈ P) (hSP : S ⊆ P.parts) : t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

end Set

end Partition
