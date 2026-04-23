/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Order.SupIndep
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Lattice
import Mathlib.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

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

## Main declarations

* `Partition s`: For `[CompleteLattice α]` and `s : α`, a `Partition s` is an independent
  collection of nontrivial elements whose supremum is `s`.
* `Partition.removeBot`: A constructor for `Partition s` that removes `⊥` from a set of parts.
* `Partition.instOrderTop`: `Partition s` has a top element, consisting of just `s` if `s ≠ ⊥` or
  nothing otherwise.
* `Partition.instSemilatticeInf`: `Partition s` has finite meets `P ⊓ Q` when `α` is a frame,
  given by the collection of all non-bottom infima `p ⊓ q` of parts of the two partitions.
* `Partition.Rel`: The partial equivalence relation induced by a partition of a set.
* `Partition.IsRepFun`: A predicate characterizing a representative function for a partition.

## Representative functions (`IsRepFun`)

`IsRepFun P f` means that `f` sends each element of the support to a representative in its
`Partition.Rel`-class, agrees on related elements, and is the identity outside the support.

This is useful whenever a construction must pick one distinguished element per part of a partition.
For example, in graph theory one may partition edges into parallel classes or vertices into
connected components; a representative function can specify which edge remains when simplifying
parallel edges, or how supervertices are labeled after contraction. Similar uses arise in matroid
theory and in the definition of minors.

Tempting alternatives are to use `Classical.choice` or fix a global well-order and take minimal
representatives. However, these lead to issues with inconsistencies: independent choices need not
respect relations between different instances (e.g. monotonicity of simplifications with respect
to subgraph order), a global order can clash with structure already carried by the type, and maps
between different types need not intertwine two separate canonical choices. Stating hypotheses with
`IsRepFun` keeps the chosen representatives explicit; existence under suitable conditions can be
proved separately.

## TODO

* Link this to `Finpartition`.
* Show that when `α` is a frame `Partition α` also has finite joins, i.e. that it is a lattice.

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
lemma mem_removeBot (P : Set α) (indep : _root_.sSupIndep P) (sSup_eq : sSup P = s) :
    x ∈ removeBot P indep sSup_eq ↔ x ∈ P ∧ x ≠ ⊥ := Iff.rfl

@[simp]
lemma notMem_of_bot (P : Partition (⊥ : α)) (x : α) : x ∉ P := by
  rintro hxP
  obtain rfl := le_bot_iff.mp <| P.le_of_mem hxP
  exact P.bot_notMem hxP

/-- There is a unique partition of `⊥`. -/
instance : Unique (Partition (⊥ : α)) where
  default := removeBot (∅ : Set α) sSupIndep_empty sSup_empty
  uniq P := by ext; simp

lemma ne_bot_of_mem' (hxP : x ∈ P) : s ≠ ⊥ := by
  rintro rfl
  exact P.notMem_of_bot _ hxP

end Basic

section Order

variable [CompleteLattice α] {P Q : Partition s}

/-- Partitions on `s` are ordered by refinement: `P ≤ Q` if every part of `P` is contained in a part
of `Q`. -/
instance : PartialOrder (Partition s) where
  le P Q := ∀ ⦃x⦄, x ∈ P → ∃ y ∈ Q, x ≤ y
  lt := _
  le_refl P x hx := ⟨x, hx, le_rfl⟩
  le_trans P Q R hPQ hQR x hxP := by
    obtain ⟨y, hy, hxy⟩ := hPQ hxP
    obtain ⟨z, hz, hyz⟩ := hQR hy
    exact ⟨z, hz, hxy.trans hyz⟩
  le_antisymm P Q hp hq := by
    refine Partition.ext fun x ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hp h
      obtain ⟨x', hx', hyx'⟩ := hq hy
      obtain rfl := P.pairwiseDisjoint.eq_of_le h hx' (P.ne_bot_of_mem h) (hxy.trans hyx')
      rwa [hxy.antisymm hyx']
    obtain ⟨y, hy, hxy⟩ := hq h
    obtain ⟨x', hx', hyx'⟩ := hp hy
    obtain rfl := Q.pairwiseDisjoint.eq_of_le h hx' (Q.ne_bot_of_mem h) (hxy.trans hyx')
    rwa [hxy.antisymm hyx']

lemma le_def : P ≤ Q ↔ ∀ x ∈ P, ∃ y ∈ Q, x ≤ y := .rfl

lemma exists_le_of_mem_le (h : P ≤ Q) (hx : x ∈ P) : ∃ y ∈ Q, x ≤ y := h hx

lemma existsUnique_of_mem_le (h : P ≤ Q) (hx : x ∈ P) : ∃! y ∈ Q, x ≤ y := by
  obtain ⟨y, hy, hxy⟩ := h hx
  refine ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ ↦ Q.eq_of_not_disjoint hz hy ?_⟩
  have := P.ne_bot_of_mem hx
  contrapose this
  exact le_bot_iff.mp (this hxz hxy)

/-- The top partition of `s` is the partition with the single part `s`, or no parts if `s` is the
bottom element. -/
instance instOrderTop : OrderTop (Partition s) where
  top := removeBot {s} (sSupIndep_singleton s) sSup_singleton
  le_top P x hxP := by simp [P.ne_bot_of_mem' hxP, P.le_of_mem hxP]

lemma top_def : (⊤ : Partition s) = removeBot {s} (sSupIndep_singleton s) sSup_singleton := rfl

@[simp] lemma parts_top (hs : s ≠ ⊥) : ((⊤ : Partition s) : Set α) = {s} := by
  simpa [top_def]

@[simp] lemma mem_top_iff {a : α} : a ∈ (⊤ : Partition s) ↔ a = s ∧ a ≠ ⊥ := by
  rw [top_def, mem_removeBot, mem_singleton_iff]

lemma parts_top_subset : ((⊤ : Partition s) : Set α) ⊆ {s} := by simp

/-- When `α` is a frame, the meet `P ⊓ Q` of two partitions is the partition consisting of all
non-bottom meets `p ⊓ q` for `p ∈ P` and `q ∈ Q`.

Note that while finite meets of partitions can be constructed in this way, arbitrary meets generally
do not exist: for example when `α` is the frame of open subsets of the Cantor space, `Partition α`
has no bottom element. -/
instance instSemilatticeInf {α : Type*} [Order.Frame α] (s : α) : SemilatticeInf (Partition s) where
  inf P Q := removeBot {a | ∃ p ∈ P, ∃ q ∈ Q, a = p ⊓ q} (by
      rw [sSupIndep_iff_pairwiseDisjoint]
      intro a ha a' ha' h
      grind [Partition.eq_or_disjoint, Disjoint.inf_left, Disjoint.inf_left'])
    (by
      suffices sSup {a | ∃ p ∈ P, ∃ q ∈ Q, a = p ⊓ q} = sSup P ⊓ sSup Q by simpa
      rw [sSup_inf_sSup]
      refine le_antisymm ?_ ?_
      · exact sSup_le fun a ⟨p, hp, q, hq, ha⟩ ↦ le_iSup₂_of_le (p, q) ⟨hp, hq⟩ <| by grind
      · exact iSup₂_le fun (p, q) ⟨hp, hq⟩ ↦ le_sSup_of_le ⟨p, hp, q, hq, rfl⟩ (by simp))
  inf_le_left P Q a ha := by
    obtain ⟨⟨p, hp, q, hq, rfl⟩, h⟩ := ha
    grind [inf_le_left]
  inf_le_right P Q a ha := by
    obtain ⟨⟨p, hp, q, hq, rfl⟩, h⟩ := ha
    grind [inf_le_right]
  le_inf P Q R hQ hR a ha := by
    have ⟨q, hq⟩ := hQ ha
    have ⟨r, hr⟩ := hR ha
    refine ⟨q ⊓ r, ⟨?_, ?_⟩, ?_⟩ <;> grind [le_inf_iff, P.ne_bot_of_mem ha]

@[simp]
lemma mem_inf_iff {α : Type*} [Order.Frame α] {s a : α} {P Q : Partition s} :
    a ∈ P ⊓ Q ↔ a ≠ ⊥ ∧ ∃ p ∈ P, ∃ q ∈ Q, a = p ⊓ q :=
  and_comm

end Order

variable {S : Set (Set α)} {u s t : Set α} {a b c : α} {P Q : Partition u}

section Set

@[simp] protected lemma sUnion_eq (P : Partition s) : ⋃₀ P = s := P.sSup_eq

lemma nonempty_of_mem (ht : t ∈ P) : t.Nonempty := notMem_singleton_empty.1 <| P.ne_bot_of_mem ht

lemma empty_notMem : ∅ ∉ P := P.bot_notMem

lemma subset_of_mem (ht : t ∈ P) : t ⊆ u := P.le_of_mem ht

lemma mem_iff_exists : x ∈ u ↔ ∃ t ∈ P, x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨t, htP, hxt⟩ ↦ subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx

lemma eq_of_mem_inter (ht : t ∈ P) (hs : s ∈ P) (hx : x ∈ t ∩ s) : t = s :=
  P.pairwiseDisjoint.elim ht hs fun (hdj : Disjoint t s) ↦ by simp [hdj.inter_eq] at hx

lemma eq_of_mem_of_mem (ht : t ∈ P) (hus : s ∈ P) (hxt : x ∈ t) (hxs : x ∈ s) : t = s :=
  eq_of_mem_inter ht hus ⟨hxt, hxs⟩

lemma mem_iff_unique : x ∈ u ↔ ∃! t, t ∈ P ∧ x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, ⟨htP, hxt⟩, _⟩ ↦ subset_of_mem htP hxt⟩
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t, ⟨ht, hxt⟩, fun s ⟨hsP, hxs⟩ ↦ P.eq_of_mem_of_mem hsP ht hxs hxt⟩

lemma subset_sUnion_and_mem_iff_mem (hSP : S ⊆ P) : t ⊆ ⋃₀ S ∧ t ∈ P ↔ t ∈ S := by
  refine ⟨fun ⟨htsu, htP⟩ ↦ ?_, fun htS ↦ ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  exact eq_of_mem_of_mem htP (hSP hsS) hxt hxs ▸ hsS

lemma subset_sUnion_iff_mem (ht : t ∈ P) (hSP : S ⊆ P.parts) : t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

/-- Noncomputably choose a representative from an equivalence class. -/
noncomputable def rep (P : Partition u) (ht : t ∈ P) : α := (P.nonempty_of_mem ht).some

/-- The representative of a part belongs to that part. -/
@[simp] lemma rep_mem (ht : t ∈ P) : P.rep ht ∈ t := (P.nonempty_of_mem ht).some_mem

/-- The representative of a part belongs to the underlying set. -/
@[simp] lemma rep_mem_supp (ht : t ∈ P) : P.rep ht ∈ u := P.subset_of_mem ht <| rep_mem ht

end Set

/-! ### Induced relation -/

section Rel

/-- Every partition of `s : Set α` induces a transitive, symmetric binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside `s`. -/
def Rel (P : Partition s) (a b : α) : Prop :=
  ∃ t ∈ P, a ∈ t ∧ b ∈ t

lemma rel_le_iff_le : P.Rel ≤ Q.Rel ↔ P ≤ Q := by
  refine ⟨fun h S hS ↦ ?_, fun h a b ⟨t, ht, ha, hb⟩ ↦ ?_⟩
  · obtain ⟨x, hxS⟩ := nonempty_of_mem hS
    obtain ⟨T, hT, hxT, -⟩ := h x x ⟨S, hS, hxS, hxS⟩
    refine ⟨T, hT, fun a haS ↦ ?_⟩
    obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
    exact eq_of_mem_of_mem hT hT' hxT hxT' ▸ haT'
  obtain ⟨t', ht', htt'⟩ := h ht
  use t', ht', htt' ha, htt' hb

lemma Rel.exists (h : P.Rel x y) : ∃ t ∈ P, x ∈ t ∧ y ∈ t := h

lemma Rel.forall (h : P.Rel x y) (ht : t ∈ P) : x ∈ t ↔ y ∈ t := by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

@[simp]
lemma rel_rfl_iff : P.Rel x x ↔ x ∈ u := by
  refine ⟨fun ⟨t, ht, hxP, _⟩ ↦ subset_of_mem ht hxP, fun hx ↦ ?_⟩
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.mem_iff_unique.mp hx
  exact ⟨t, ht, hxt, hxt⟩

instance (P : Partition u) : Std.Symm P.Rel where
  symm _ _ := fun ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition u) : IsTrans α P.Rel where
  trans _ _ _ := fun ⟨t, ht, ha, hb⟩ ⟨t', ht', hb', hc⟩ ↦
    ⟨t, ht, ha, by rwa [eq_of_mem_of_mem ht ht' hb hb']⟩

@[symm] lemma Rel.symm (h : P.Rel x y) : P.Rel y x := symm_of P.Rel h

lemma rel_comm : P.Rel x y ↔ P.Rel y x := ⟨Rel.symm, Rel.symm⟩

lemma Rel.trans (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z := trans_of P.Rel hxy hyz

lemma Rel.left_mem (h : P.Rel x y) : x ∈ u := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

lemma Rel.right_mem (h : P.Rel x y) : y ∈ u := h.symm.left_mem

/-- Any element of a part is related to the representative of that part. -/
lemma rep_rel (ht : t ∈ P) (hx : x ∈ t) : P.Rel x (P.rep ht) := ⟨t, ht, hx, P.rep_mem ht⟩

end Rel

section partOf

/-- The part of a partition containing a given element. If the element is not in the
underlying set, this is empty. -/
def partOf (P : Partition u) (a : α) : Set α := {b | P.Rel a b}

lemma partOf_subset : P.partOf x ⊆ u := fun _ ⟨_, ht, _, hyt⟩ ↦ subset_of_mem ht hyt

@[simp] lemma mem_partOf_iff : x ∈ P.partOf y ↔ P.Rel y x := Iff.rfl

lemma eq_partOf_of_mem (ht : t ∈ P) (hxt : x ∈ t) : t = P.partOf x := by
  ext y
  exact ⟨(⟨t, ht, hxt, ·⟩), fun ⟨s, hsP, hxs, hys⟩ ↦ (P.eq_of_mem_of_mem ht hsP hxt hxs) ▸ hys⟩

lemma mem_iff_mem_partOf_mem : x ∈ u ↔ x ∈ P.partOf x ∧ P.partOf x ∈ P := by
  refine ⟨fun hx ↦ ?_, fun ⟨hx, hP⟩ ↦ subset_of_mem hP hx⟩
  obtain ⟨t, htP, hxt⟩ := P.mem_iff_exists.mp hx
  exact P.eq_partOf_of_mem htP hxt ▸ ⟨hxt, htP⟩

lemma mem_partOf (hxu : x ∈ u) : x ∈ P.partOf x := (P.mem_iff_mem_partOf_mem.mp hxu).1

lemma partOf_mem (hxu : x ∈ u) : P.partOf x ∈ P := (P.mem_iff_mem_partOf_mem.mp hxu).2

@[simp]
lemma partOf_rep (hs : s ∈ P) : P.partOf (P.rep hs) = s :=
  eq_partOf_of_mem hs (rep_mem hs) |>.symm

lemma mem_iff_exists_partOf : s ∈ P ↔ ∃ x ∈ u, partOf P x = s :=
  ⟨fun hs ↦ ⟨P.rep hs, rep_mem_supp hs, partOf_rep hs⟩, fun ⟨_, hxu, h⟩ ↦ h ▸ partOf_mem hxu⟩

lemma partOf_nonempty_iff : (P.partOf x).Nonempty ↔ x ∈ u := by
  refine ⟨fun ⟨y, hy⟩ ↦ hy.left_mem, fun h ↦ ?_⟩
  simpa [nonempty_iff_ne_empty] using P.ne_bot_of_mem (partOf_mem h)

@[simp]
lemma partOf_eq_empty_iff : P.partOf x = ∅ ↔ x ∉ u := by
  rw [← partOf_nonempty_iff, not_nonempty_iff_eq_empty]

lemma rel_iff_partOf_eq_partOf_of_mem (P : Partition u) (hx : x ∈ u) (hy : y ∈ u) :
    P.Rel x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ ↦ eq_partOf_of_mem (P.partOf_mem hx) ?_,
    fun h ↦ ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, h ▸ mem_partOf hy⟩⟩
  rwa [← eq_partOf_of_mem htP hxt]

lemma rel_iff_partOf_eq_partOf (P : Partition u) :
    P.Rel x y ↔ ∃ (_ : x ∈ u) (_ : y ∈ u), P.partOf x = P.partOf y := by
  grind [rel_iff_partOf_eq_partOf_of_mem, Rel.left_mem, Rel.right_mem]

end partOf

/-! ### Representative functions

See the module docstring for motivation (graph simplification, minors, and why we use an explicit
`IsRepFun` hypothesis rather than a global choice of representatives).
-/

section IsRepFun

/-- A predicate characterizing when a function `f : α → α` is a representative function for a
partition `P`. A representative function maps each element to a canonical representative in its
equivalence class, is the identity outside the support, and maps related elements to the same
representative. -/
structure IsRepFun {u : Set α} (P : Partition u) (f : α → α) : Prop where
  /-- The function is the identity outside the support. -/
  apply_of_notMem : ∀ ⦃a⦄, a ∉ u → f a = a
  /-- The function maps each element in the support to a related element. -/
  rel_apply : ∀ ⦃a⦄, a ∈ u → P.Rel a (f a)
  /-- The function maps related elements to the same representative. -/
  apply_eq_apply : ∀ ⦃a b⦄, P.Rel a b → f a = f b

namespace IsRepFun

variable {u : Set α} {P : Partition u} {f g : α → α} {a b c : α}

lemma apply_mem (hf : IsRepFun P f) (ha : a ∈ u) : f a ∈ u := (hf.rel_apply ha).right_mem

lemma image_subset (hf : IsRepFun P f) (hs : u ⊆ s) : f '' s ⊆ s := by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a ∈ u
  · exact hs <| hf.apply_mem ha
  exact (hf.apply_of_notMem ha).symm ▸ haS

lemma mapsTo (hf : IsRepFun P f) (hs : u ⊆ s) : Set.MapsTo f s s :=
  fun x h ↦ hf.image_subset hs ⟨x, h, rfl⟩

lemma mapsTo_of_disjoint (hf : IsRepFun P f) (hs : Disjoint u s) : Set.MapsTo f s s :=
  fun _ h ↦ (hf.apply_of_notMem <| hs.notMem_of_mem_right h).symm ▸ h

lemma apply_mem_iff (hf : IsRepFun P f) (hs : u ⊆ s) : f a ∈ s ↔ a ∈ s :=
  hf.mapsTo hs |>.mem_iff <| mapsTo_of_disjoint hf hs.disjoint_compl_right

lemma apply_eq_apply_iff_rel (hf : IsRepFun P f) (ha : a ∈ u) : f a = f b ↔ P.Rel a b := by
  refine ⟨fun hab ↦ (hf.rel_apply ha).trans ?_, (hf.apply_eq_apply ·)⟩
  rw [hab, P.rel_comm]
  refine hf.rel_apply <| by_contra fun hb ↦ ?_
  rw [hf.apply_of_notMem hb] at hab
  exact hab ▸ hb <| hf.apply_mem ha

lemma apply_eq_apply_iff (hf : IsRepFun P f) : f a = f b ↔ a = b ∨ P.Rel a b := by
  simp only [or_iff_not_imp_left, ← ne_eq]
  refine ⟨fun hab hne ↦ ?_, fun h ↦ ?_⟩
  · obtain (ha | ha) := em (a ∈ u)
    · exact hf.apply_eq_apply_iff_rel ha |>.mp hab
    obtain (hb | hb) := em (b ∈ u)
    · exact (hf.apply_eq_apply_iff_rel hb |>.mp hab.symm).symm
    rw [hf.apply_of_notMem ha, hf.apply_of_notMem hb] at hab
    contradiction
  obtain rfl | hne := eq_or_ne a b
  · rfl
  exact hf.apply_eq_apply (h hne)

lemma forall_apply_eq_apply_iff (hf : IsRepFun P f) (a) :
    (∀ (x : α), f a = f x ↔ a = x) ∨ (∀ (x : α), f a = f x ↔ P.Rel a x) := by
  refine (em (a ∈ u)).elim (fun ha ↦ Or.inr fun b ↦ ?_) (fun ha ↦ Or.inl fun b ↦ ?_)
  · rw [hf.apply_eq_apply_iff_rel ha]
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
  · exact hf.apply_of_notMem <| hf.apply_mem_iff le_rfl |>.not.mp ha
  exact hf.apply_of_notMem ha |>.symm

lemma apply_eq_apply_iff' (hf : IsRepFun P f) :
    f a = f b ↔ (a = b ∧ ∀ c, f a = f c ↔ a = c) ∨ P.Rel a b := by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a
  · refine ⟨by grind, ?_⟩
    rintro (h | h)
    · exact congrArg _ h.1
    exact hf.apply_eq_apply h
  grind

lemma idem (hf : IsRepFun P f) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ u)
  · rw [eq_comm, hf.apply_eq_apply_iff_rel ha]
    exact hf.rel_apply ha
  simp_rw [hf.apply_of_notMem ha]

theorem apply_apply (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α) : f (g x) = f x := by
  obtain (hx | hx) := em (x ∈ u)
  · exact hf.apply_eq_apply (hg.rel_apply hx).symm
  rw [hg.apply_of_notMem hx, hf.apply_of_notMem hx]

/-- Any partially defined representative function extends to a complete one. -/
lemma exists_extend_partial (P : Partition u) (f₀ : t → α)
    (h_notMem : ∀ x : t, x.1 ∉ u → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ u → P.Rel x (f₀ x))
    (h_eq : ∀ x y : t, P.Rel x y → f₀ x = f₀ y) : ∃ f, IsRepFun P f ∧ ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ u then
    (if hb : ∃ b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hfdef
  refine ⟨f, ⟨fun a ha ↦ by simp [hfdef, ha], fun a ha ↦ ?_, fun a b hab ↦ ?_⟩, fun a ↦ ?_⟩
  · simp only [hfdef, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.right_mem
    push Not at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hfdef, dif_pos hab.left_mem, dif_pos hab.right_mem]
    split_ifs with h₁ h₂ h₂
    · exact h_eq _ _ <| (hab.symm.trans h₁.choose_spec).symm.trans h₂.choose_spec
    · exact h₂ ⟨_, hab.symm.trans h₁.choose_spec⟩ |>.elim
    · exact h₁ ⟨_, hab.trans h₂.choose_spec⟩ |>.elim
    congr 1
    rwa [← rel_iff_partOf_eq_partOf_of_mem _ hab.left_mem hab.right_mem]
  obtain (ha | ha) := em (a.1 ∈ u) |>.symm
  · simp [hfdef, ha, h_notMem _ ha]
  simp only [hfdef, ha, ↓reduceDIte]
  split_ifs with h
  · exact h_eq _ _ h.choose_spec |>.symm
  exact h ⟨a, rel_rfl_iff.mpr ha⟩ |>.elim

/-- For any set `t` containing no two distinct related elements, there is a representative function
equal to the identity on `t`. -/
lemma exists_extend_partial' (P : Partition u)
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P.Rel x y → x = y) : ∃ f, IsRepFun P f ∧ EqOn f id t := by
  simpa using exists_extend_partial P (fun x : t ↦ x) (by simp) (by simp) (fun x y ↦ h x.2 y.2)

/-- Every partition has a representative function. -/
lemma nonempty (P : Partition u) : ∃ f, IsRepFun P f := by
  obtain ⟨f, hf, -⟩ := exists_extend_partial' P (t := ∅) (by simp)
  exact ⟨f, hf⟩

end IsRepFun
end Partition.IsRepFun
