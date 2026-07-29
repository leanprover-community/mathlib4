/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Hyeokjun Kwon
-/
module

public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.SupIndep

/-!
# Partitions

A `Partition` of a complete lattice `α` is an independent family of nontrivial elements.
Its support `Partition.supp` is the supremum of its parts.

An important special case is where `α` is `Set β`; see `Mathlib.Order.Partition.Set`.

Partitions are ordered by refinement: `P ≤ Q` if every part of `P` is less than or equal to a part
of `Q`.

## Main declarations

* `Partition α`: For `[CompleteLattice α]`, a `Partition α` is an independent collection of
  nontrivial elements.
* `Partition.supp`: The supremum of the parts of a partition.
* `Partition.removeBot`: A constructor for `Partition α` that removes `⊥` from a set of parts.
* `Partition.induce`: The partition obtained by meeting every part with a fixed element.
* `Partition.bind`: Combine a partition with a family of partitions of its parts.
* `Partition.instOrderTop`: `Partition α` has a top element, consisting of just `⊤`
  if `⊤ ≠ ⊥` or nothing otherwise.
* `Partition.instSemilatticeInf`: `Partition α` has finite meets `P ⊓ Q` when `α` is a frame,
  given by binding `P` with the induced partitions of `Q` on each part of `P`.

See `Mathlib.Order.Partition.Lattice` for the complete lattice structure when `α` is a frame.

## TODO

* Link this to `Finpartition`.

-/

@[expose] public section
variable {α : Type*} {s t x y z : α}

open Set

/-- A `Partition` of a `CompleteLattice` is a collection of independent nontrivial elements.
The support of the partition is the supremum of its parts. -/
structure Partition (α : Type*) [CompleteLattice α] where
  /-- The collection of parts -/
  parts : Set α
  /-- The parts are `sSupIndep`. -/
  sSupIndep' : sSupIndep parts
  /-- The bottom element is not a part. -/
  bot_notMem' : ⊥ ∉ parts

namespace Partition

section Basic

variable [CompleteLattice α] {P Q : Partition α}

/-- The support of a partition is the supremum of its parts. -/
def supp (P : Partition α) : α := sSup P.parts

instance : SetLike (Partition α) α where
  coe := Partition.parts
  coe_injective p p' h := by
    cases p
    cases p'
    simpa using h

/-- See Note [custom simps projection]. -/
def Simps.coe (P : Partition α) : Set α := P

initialize_simps_projections Partition (parts → coe, as_prefix coe)

@[simp] lemma coe_parts : P.parts = P := rfl

lemma mem_parts : x ∈ P.parts ↔ x ∈ P := Iff.rfl

@[ext] lemma ext (hP : ∀ x, x ∈ P ↔ x ∈ Q) : P = Q :=
  SetLike.ext hP

@[simp]
lemma sSupIndep (P : Partition α) : sSupIndep (P : Set α) :=
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
lemma sSup_eq (P : Partition α) : sSup P = P.supp :=
  rfl

@[deprecated (since := "2026-07-28")] alias sSup_eq' := sSup_eq

@[simp]
lemma iSup_eq (P : Partition α) : ⨆ x ∈ P, x = P.supp := by
  simp_rw [← P.sSup_eq, sSup_eq_iSup]
  rfl

@[grind →]
lemma le_of_mem (P : Partition α) (hx : x ∈ P) : x ≤ P.supp :=
  (le_sSup hx).trans_eq P.sSup_eq

lemma parts_nonempty (P : Partition α) (hs : P.supp ≠ ⊥) : (P : Set α).Nonempty :=
  nonempty_iff_ne_empty.2 fun hP ↦ by simp [← P.sSup_eq, hP, sSup_empty] at hs

@[simp]
lemma bot_notMem (P : Partition α) : ⊥ ∉ P :=
  P.bot_notMem'

@[grind →]
lemma ne_bot_of_mem (hx : x ∈ P) : x ≠ ⊥ :=
  fun h ↦ P.bot_notMem <| h ▸ hx

lemma bot_lt_of_mem (hx : x ∈ P) : ⊥ < x :=
  bot_lt_iff_ne_bot.2 <| P.ne_bot_of_mem hx

lemma supp_ne_bot_of_mem (hx : x ∈ P) : P.supp ≠ ⊥ :=
  fun hP ↦ P.ne_bot_of_mem hx <| le_bot_iff.mp <| (P.le_of_mem hx).trans_eq hP

@[deprecated (since := "2026-07-28")] alias ne_bot_of_mem' := supp_ne_bot_of_mem

/-- A constructor for `Partition α` that removes `⊥` from the set of parts. -/
@[simps]
def removeBot (P : Set α) (indep : _root_.sSupIndep P) : Partition α where
  parts := P \ {⊥}
  sSupIndep' := indep.mono sdiff_subset
  bot_notMem' := by simp

@[simp]
lemma mem_removeBot (P : Set α) (indep : _root_.sSupIndep P) :
    x ∈ removeBot P indep ↔ x ∈ P ∧ x ≠ ⊥ := Iff.rfl

@[simp]
lemma supp_removeBot (P : Set α) (indep : _root_.sSupIndep P) :
    (removeBot P indep).supp = sSup P := by
  change sSup (P \ {⊥}) = sSup P
  simp

end Basic

section Order

variable [CompleteLattice α] {P Q : Partition α} {a : α}

/-- Partitions are ordered by refinement: `P ≤ Q` if every part of `P` is contained in a part
of `Q`. -/
instance : PartialOrder (Partition α) where
  le P Q := ∀ ⦃x⦄, x ∈ P → ∃ y ∈ Q, x ≤ y
  lt := _
  le_refl P x hx := ⟨x, hx, le_rfl⟩
  le_trans P Q R hPQ hQR x hxP := by grind
  le_antisymm P Q hp hq := Partition.ext fun x ↦ by grind [eq_of_not_disjoint]

lemma le_def : P ≤ Q ↔ ∀ x ∈ P, ∃ y ∈ Q, x ≤ y := .rfl

lemma exists_le_of_mem_le (h : P ≤ Q) (hx : x ∈ P) : ∃ y ∈ Q, x ≤ y := h hx

lemma existsUnique_of_mem_le (h : P ≤ Q) (hx : x ∈ P) : ∃! y ∈ Q, x ≤ y := by
  obtain ⟨y, hy, hxy⟩ := h hx
  exact ⟨y, ⟨hy, hxy⟩, fun z ⟨hz, hxz⟩ ↦ Q.eq_of_not_disjoint hz hy (by grind)⟩

/-- If the support of `Q` is contained in a part of `P`, then `Q` refines `P`. -/
lemma le_of_supp_le_part (ha : a ∈ P) (hQa : Q.supp ≤ a) : Q ≤ P :=
  fun _ hx ↦ ⟨a, ha, (Q.le_of_mem hx).trans hQa⟩

/-- The empty partition, which is least in the refinement order. -/
instance : OrderBot (Partition α) where
  bot := { parts := ∅
           sSupIndep' := by simp
           bot_notMem' := by simp }
  bot_le _ _ hs := hs.elim

@[simp] lemma parts_bot : (⊥ : Partition α).parts = ∅ := rfl

@[simp] lemma notMem_bot : x ∉ (⊥ : Partition α) := notMem_empty _

@[simp] lemma coe_bot : ((⊥ : Partition α) : Set α) = ∅ := rfl

/-- A partition is empty iff it is the bottom partition. -/
@[simp]
lemma coe_eq_empty_iff (P : Partition α) : (P : Set α) = ∅ ↔ P = ⊥ :=
  ⟨fun h ↦ SetLike.coe_injective (h.trans coe_bot.symm), fun h ↦ h ▸ coe_bot⟩

@[simp] lemma supp_bot : (⊥ : Partition α).supp = ⊥ := sSup_empty

/-- A partition with bottom support is the empty partition. -/
lemma eq_bot (hP : P.supp = ⊥) : P = ⊥ := by
  ext x
  have hsup := P.sSup_eq
  simp only [sSup_eq_bot, SetLike.mem_coe, hP] at hsup
  simp only [notMem_bot, iff_false]
  exact fun hx ↦ P.ne_bot_of_mem hx <| hsup x hx

/-- The support of a partition is bottom iff the partition is empty. -/
@[simp]
lemma supp_eq_bot_iff : P.supp = ⊥ ↔ P = ⊥ :=
  ⟨eq_bot, (· ▸ supp_bot)⟩

lemma notMem_of_bot (hP : P.supp = ⊥) (x : α) : x ∉ P :=
  (eq_bot hP).symm ▸ notMem_bot

/-- A partition has a part iff it is not the empty partition. -/
lemma parts_nonempty_iff (P : Partition α) : P.parts.Nonempty ↔ P ≠ ⊥ := by
  refine ⟨?_, fun hP ↦ nonempty_iff_ne_empty.mpr <| mt (coe_eq_empty_iff P).mp hP⟩
  rintro ⟨x, hx⟩ rfl
  exact notMem_bot hx

/-- On a subsingleton complete lattice there is a unique partition. -/
instance {α : Type*} [CompleteLattice α] [Subsingleton α] : Unique (Partition α) where
  default := ⊥
  uniq P := eq_bot (by
    simp only [← P.sSup_eq, sSup_eq_bot, SetLike.mem_coe]
    exact fun a _ ↦ Subsingleton.elim _ _)

/-- The top partition is the partition with the single part `⊤`, or no parts if `⊤` is the
bottom element. -/
instance instOrderTop : OrderTop (Partition α) where
  top := removeBot {⊤} (sSupIndep_singleton ⊤)
  le_top P x hxP := by
    obtain (hs | hs) := eq_or_ne (⊤ : α) ⊥
    · have : Subsingleton α := subsingleton_of_bot_eq_top hs.symm
      exact (P.ne_bot_of_mem hxP (Subsingleton.elim _ _)).elim
    exact ⟨⊤, by simp [hs], by simp⟩

lemma top_def : (⊤ : Partition α) = removeBot {⊤} (sSupIndep_singleton ⊤) := rfl

@[simp] lemma supp_top : (⊤ : Partition α).supp = ⊤ := by
  simp [top_def]

@[simp] lemma parts_top [Nontrivial α] : ((⊤ : Partition α) : Set α) = {⊤} := by
  change (removeBot {(⊤ : α)} _).parts = {⊤}
  simp

@[simp] lemma mem_top_iff {a : α} : a ∈ (⊤ : Partition α) ↔ a = ⊤ ∧ a ≠ ⊥ := by
  rw [top_def, mem_removeBot, mem_singleton_iff]

lemma parts_top_subset : ((⊤ : Partition α) : Set α) ⊆ {⊤} :=
  fun _ ha ↦ (mem_top_iff.mp ha).1 ▸ rfl

/-- Refinement of partitions implies inequality of supports. -/
lemma supp_mono {P Q : Partition α} (h : P ≤ Q) : P.supp ≤ Q.supp :=
  sSup_le_sSup_of_isCofinalFor h

lemma supp_monotone : Monotone (Partition.supp (α := α)) := fun _ _ ↦ supp_mono

/-- On a nontrivial complete lattice there are at least two partitions. -/
instance [Nontrivial α] : Nontrivial (Partition α) :=
  ⟨⊥, ⊤, mt (congrArg (·.parts)) <| by simp [parts_top]⟩

end Order

section Induce

variable [CompleteLattice α] {P Q : Partition α} {a b : α}

/-- Meet every part of `P` with `a`, discarding bottom. -/
@[simps!]
protected def induce (P : Partition α) (a : α) : Partition α :=
  removeBot ((a ⊓ ·) '' P.parts) <| P.sSupIndep'.image_of_le_self fun _ _ ↦ inf_le_right

/-- Membership in an induced partition is equivalent to being a nontrivial meet of `a` with a
part of `P`. -/
@[simp]
lemma mem_induce_iff : x ∈ P.induce a ↔ x ≠ ⊥ ∧ ∃ t ∈ P, a ⊓ t = x := by
  simp [Partition.induce, and_comm]

/-- The nontrivial meet of an element with a part belongs to the induced partition. -/
lemma inf_mem_induce (h : x ∈ P) (hne : a ⊓ x ≠ ⊥) : a ⊓ x ∈ P.induce a :=
  mem_induce_iff.mpr ⟨hne, x, h, rfl⟩

/-- An induced partition always refines the original partition. -/
@[simp]
lemma induce_le : P.induce a ≤ P := by
  intro T hT
  rw [mem_induce_iff] at hT
  obtain ⟨hne, t, htP, rfl⟩ := hT
  exact ⟨t, htP, inf_le_right⟩

/-- Inducing preserves refinement in the partition being induced. -/
lemma induce_le_induce_left (hPQ : P ≤ Q) : P.induce a ≤ Q.induce a := by
  intro t ht
  simp_rw [mem_induce_iff] at ht ⊢
  obtain ⟨hne, t', ht'Q, rfl⟩ := ht
  obtain ⟨s, hsQ, ht's⟩ := hPQ ht'Q
  have hsu := inf_le_inf_left a ht's
  use a ⊓ s, ?_, hsu
  use ne_bot_of_le_ne_bot hne hsu, s

end Induce

section InduceFrame

variable [Order.Frame α] {P : Partition α} {a : α}

/-- In a frame, the support of an induced partition is the meet of the inducing element with the
original support. -/
@[simp]
lemma supp_induce (P : Partition α) (a : α) : (P.induce a).supp = a ⊓ P.supp := by
  change (removeBot ((a ⊓ ·) '' P.parts) _).supp = a ⊓ P.supp
  rw [supp_removeBot, sSup_image, supp, inf_sSup_eq]

end InduceFrame

section Bind

variable [Order.Frame α] {P Q : Partition α} {a : α} {Qs : ∀ a ∈ P, Partition α}

/-- Combine a partition with a family of partitions of (subparts of) its parts. -/
@[simps] protected def bind (P : Partition α) (Qs : ∀ a ∈ P, Partition α)
    (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) : Partition α where
  parts := ⋃ a : P, (Qs a a.prop).parts
  sSupIndep' b hb := by
    simp only [mem_iUnion, Subtype.exists] at hb
    obtain ⟨a, haP, hba⟩ := hb
    refine (Qs a haP).sSupIndep hba |>.sup_right ((P.sSupIndep haP).mono_left
      <| ((Qs a haP).le_of_mem hba).trans (hQs a haP)) |>.mono_right ?_
    simp only [sSup_le_iff, mem_sdiff, mem_iUnion, Subtype.exists, mem_singleton_iff, and_imp,
      forall_exists_index]
    rintro t' x hx ht' hne
    obtain rfl | hne := eq_or_ne x a
    · exact (le_sSup_of_le (show t' ∈ _ \ {b} from ⟨ht', hne⟩) rfl.le).trans le_sup_left
    exact le_trans (le_sSup_of_le (mem_sdiff_of_mem hx hne) <| (Qs x hx).le_of_mem ht' |>.trans
      <| hQs x hx) le_sup_right
  bot_notMem' := by
    simp only [mem_iUnion, Subtype.exists, not_exists]
    exact fun x hx ↦ (Qs x hx).bot_notMem

/-- Membership in a bind is equivalent to membership in one of the constituent partitions. -/
@[simp] lemma mem_bind_iff (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) :
    a ∈ P.bind Qs hQs ↔ ∃ (b : α) (hb : b ∈ P), a ∈ Qs b hb := by
  change _ ∈ ⋃ _, _ ↔ _
  simp

/-- A bind refines `Q` iff every constituent partition refines `Q`. -/
@[simp]
lemma bind_le_iff (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) :
    P.bind Qs hQs ≤ Q ↔ ∀ a, (h : a ∈ P) → (Qs a h) ≤ Q := by
  simp_rw [le_def, mem_bind_iff hQs, forall_exists_index]
  tauto

/-- A bind always refines the original partition. -/
lemma bind_le (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) : P.bind Qs hQs ≤ P := by
  rw [bind_le_iff hQs]
  exact fun a haP ↦ le_of_supp_le_part haP (hQs a haP)

/-- `Q` refines a bind of `P` iff `Q` refines `P` and, on each part of `P`, the induced partition
of `Q` refines the corresponding constituent. -/
@[simp]
lemma le_bind_iff (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) :
    Q ≤ P.bind Qs hQs ↔ Q ≤ P ∧ ∀ a, (h : a ∈ P) → Q.induce a ≤ Qs a h := by
  refine ⟨fun h ↦ ⟨h.trans (bind_le hQs), fun a haP b hbQsa ↦ ?_⟩,
    fun ⟨hQP, h⟩ a haQ ↦ ?_⟩
  · obtain ⟨hcnea, c, hcQ, rfl⟩ := (by simpa using hbQsa); clear hbQsa
    obtain ⟨d, hd, hcd⟩ := h hcQ
    obtain ⟨e, heP, hdQse⟩ := (by simpa using hd); clear hd
    have hne : ¬Disjoint a e := by
      contrapose! hcnea
      have hce := hcd.trans <| (le_of_mem _ hdQse).trans <| hQs e heP
      exact disjoint_iff.mp (hcnea.mono_right hce)
    obtain rfl := P.eq_of_not_disjoint haP heP hne
    exact ⟨d, hdQse, inf_le_of_right_le hcd⟩
  obtain ⟨p, hpP, hap⟩ := hQP haQ
  obtain ⟨q, hqQsp, haq⟩ := h p hpP <| inf_mem_induce haQ <| by simp [hap, Q.ne_bot_of_mem haQ]
  simp only [hap, inf_of_le_right] at haq
  exact ⟨q, (mem_bind_iff hQs).mpr ⟨p, hpP, hqQsp⟩, haq⟩

lemma supp_bind (hQs : ∀ a, (h : a ∈ P) → (Qs a h).supp ≤ a) :
    (P.bind Qs hQs).supp = ⨆ a : P, (Qs a a.prop).supp := by
  rw [← sSup_eq, coe_bind, sSup_iUnion]
  rfl

end Bind

section Inf

variable [Order.Frame α] {P Q R : Partition α}

/-- When `α` is a frame, partitions form a semilattice under refinement, with meet given by
`Partition.inf`. -/
instance instSemilatticeInf : SemilatticeInf (Partition α) where
  inf P Q := P.bind (fun a _ ↦ Q.induce a) (by simp)
  inf_le_left P Q := bind_le (by simp)
  inf_le_right P Q := by
    rw [bind_le_iff (by simp)]
    exact fun _ _ ↦ induce_le
  le_inf P Q R hPQ hPR := by
    rw [le_bind_iff (by simp)]
    exact ⟨hPQ, fun a _ ↦ induce_le_induce_left hPR⟩

/-- Membership in a meet is equivalent to being a nontrivial meet of parts from each
partition. -/
@[simp]
lemma mem_inf_iff {a : α} : a ∈ P ⊓ Q ↔ (∃ p ∈ P, ∃ q ∈ Q, p ⊓ q = a) ∧ a ≠ ⊥ := by
  change a ∈ (P.bind _ _).parts ↔ _
  simp [and_comm, eq_comm]

@[simp]
lemma supp_inf (P Q : Partition α) : (P ⊓ Q).supp = P.supp ⊓ Q.supp := by
  rw [show P ⊓ Q = P.bind (fun a _ ↦ Q.induce a) (by simp) from rfl, supp_bind]
  simp only [supp_induce, iSup_subtype', ← iSup_inf_eq, ← P.iSup_eq]

end Inf

end Partition
