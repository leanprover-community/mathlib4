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
* `Partition.Rel`: The partial equivalence relation induced by a partition of a set.
* `Partition.IsRepFun`: A predicate characterizing a representative function for a partition.

## TODO

* Link this to `Finpartition`.

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

@[simp] lemma parts_top (hs : s ≠ ⊥) : ((⊤ : Partition s) : Set α) = {s} := by
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

lemma subset_sUnion_iff_mem (ht : t ∈ P) (hSP : S ⊆ P.parts) : t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

end Set

/-! ### Induced relation -/

section Rel

variable {S T u : Set α} {a b c : α} {P Q : Partition u}

/-- Every partition of `s : Set α` induces a transitive, symmetric Binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside `s`. -/
def Rel (P : Partition u) (a b : α) : Prop :=
  ∃ t ∈ P, a ∈ t ∧ b ∈ t

lemma le_of_rel_le (h : P.Rel ≤ Q.Rel) : P ≤ Q := by
  intro S hS
  obtain ⟨x, hxS⟩ := nonempty_of_mem hS
  obtain ⟨T, hT, hxT, -⟩ := h x x ⟨S, hS, hxS, hxS⟩
  refine ⟨T, hT, fun a haS ↦ ?_⟩
  obtain ⟨T', hT', haT', hxT'⟩ := h a x ⟨S, hS, haS, hxS⟩
  obtain rfl := eq_of_mem_of_mem hT hT' hxT hxT'
  exact haT'

lemma Rel.exists (h : P.Rel x y) : ∃ t ∈ P, x ∈ t ∧ y ∈ t := h

lemma Rel.forall (h : P.Rel x y) (ht : T ∈ P) : x ∈ T ↔ y ∈ T := by
  obtain ⟨t, ht', hx, hy⟩ := h
  exact ⟨fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hx],
    fun h ↦ by rwa [P.eq_of_mem_of_mem ht ht' h hy]⟩

lemma rel_symmectric (P : Partition u) : Symmetric P.Rel :=
  fun _ _ ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition u) : Std.Symm P.Rel where
  symm _ _ := fun ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition u) : IsTrans α P.Rel where
  trans _ _ _ := fun ⟨t, ht, ha, hb⟩ ⟨t', ht', hb', hc⟩ ↦
    ⟨t, ht, ha, by rwa [eq_of_mem_of_mem ht ht' hb hb']⟩

lemma Rel.symm (h : P.Rel x y) : P.Rel y x := symm_of P.Rel h

lemma rel_comm : P.Rel x y ↔ P.Rel y x := ⟨Rel.symm, Rel.symm⟩

lemma Rel.trans (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z := trans_of P.Rel hxy hyz

lemma Rel.left_mem (h : P.Rel x y) : x ∈ u := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

lemma Rel.right_mem (h : P.Rel x y) : y ∈ u := h.symm.left_mem

end Rel

/-! ### Representative functions -/

section IsRepFun

/-- A predicate characterizing when a function `f : α → α` is a representative function for a
partition `P`. A representative function maps each element to a canonical representative in its
equivalence class, is the identity outside the support, and maps related elements to the same
representative. -/
structure IsRepFun {u : Set α} (P : Partition u) (f : α → α) : Prop where
  apply_of_notMem : ∀ ⦃a⦄, a ∉ u → f a = a
  rel_apply : ∀ ⦃a⦄, a ∈ u → P.Rel a (f a)
  apply_eq_apply : ∀ ⦃a b⦄, P.Rel a b → f a = f b

namespace IsRepFun

variable {u : Set α} {p : α → Prop} {P : Partition u} {f g : α → α} {a b c : α}

/-- Constructor for `IsRepFun` that uses a custom membership predicate. -/
lemma mk' (P : Partition u) (f : α → α) (hP : ∀ {x}, x ∈ u ↔ p x)
    (h₁ : ∀ a, ¬ p a → f a = a) (h₂ : ∀ a, p a → P.Rel a (f a))
    (h₃ : ∀ a b, P.Rel a b → f a = f b) : IsRepFun P f :=
  ⟨fun a ha ↦ h₁ a (hP.not.mp ha), fun a ha ↦ h₂ a (hP.mp ha), h₃⟩

lemma rel_apply' (hf : IsRepFun P f) (hP : ∀ {x}, x ∈ u ↔ p x) (ha : p a) : P.Rel a (f a) :=
  hf.rel_apply <| hP.mpr ha

lemma apply_mem (hf : IsRepFun P f) (ha : a ∈ u) : f a ∈ u := (hf.rel_apply ha).right_mem

lemma apply_mem' (hf : IsRepFun P f) (hP : ∀ {x}, x ∈ u ↔ p x) (ha : p a) : p (f a) :=
  hP.mp <| hf.apply_mem <| hP.mpr ha

lemma image_subset_supp (hf : IsRepFun P f) : f '' u ⊆ u := by
  rintro _ ⟨a, ha, rfl⟩
  exact hf.apply_mem ha

lemma image_subset {S : Set α} (hf : IsRepFun P f) (hS : u ⊆ S) : f '' S ⊆ S := by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a ∈ u
  · exact hS <| hf.apply_mem ha
  · exact (hf.apply_of_notMem ha).symm ▸ haS

lemma mapsTo_supp (hf : IsRepFun P f) : Set.MapsTo f u u :=
  fun _ ↦ hf.apply_mem

lemma mapsTo {S : Set α} (hf : IsRepFun P f) (hS : u ⊆ S) : Set.MapsTo f S S :=
  fun x h ↦ hf.image_subset hS ⟨x, h, rfl⟩

@[simp]
lemma apply_mem_iff (hf : IsRepFun P f) : f a ∈ u ↔ a ∈ u := by
  refine ⟨fun h ↦ ?_, hf.apply_mem⟩
  by_contra ha
  exact ha <| hf.apply_of_notMem ha ▸ h

lemma apply_mem_iff_of_subset {S} (hf : IsRepFun P f) (hS : u ⊆ S) : f a ∈ S ↔ a ∈ S := by
  obtain haS | haS := em (a ∈ u)
  · simp [hS haS, hS <| hf.apply_mem haS]
  rw [hf.apply_of_notMem haS]

lemma rel_of_apply_eq_apply (hf : IsRepFun P f) (ha : a ∈ u) (hab : f a = f b) : P.Rel a b := by
  refine (hf.rel_apply ha).trans ?_
  rw [hab, P.rel_comm]
  refine hf.rel_apply <| by_contra fun hb ↦ ?_
  rw [hf.apply_of_notMem hb] at hab
  exact hab ▸ hb <| hf.apply_mem ha

lemma rel_of_ne_of_apply_eq_apply (hf : IsRepFun P f) (hne : a ≠ b) (hab : f a = f b) :
    P.Rel a b := by
  obtain (ha | ha) := em (a ∈ u)
  · exact hf.rel_of_apply_eq_apply ha hab
  obtain (hb | hb) := em (b ∈ u)
  · exact (hf.rel_of_apply_eq_apply hb hab.symm).symm
  rw [hf.apply_of_notMem ha, hf.apply_of_notMem hb] at hab
  contradiction

lemma apply_eq_apply_iff_rel (hf : IsRepFun P f) (ha : a ∈ u) : f a = f b ↔ P.Rel a b :=
  ⟨hf.rel_of_apply_eq_apply ha, (hf.apply_eq_apply ·)⟩

lemma apply_eq_apply_iff_rel_of_ne (hf : IsRepFun P f) (hne : a ≠ b) : f a = f b ↔ P.Rel a b :=
  ⟨hf.rel_of_ne_of_apply_eq_apply hne, (hf.apply_eq_apply ·)⟩

lemma apply_eq_apply_iff (hf : IsRepFun P f) : f a = f b ↔ a = b ∨ P.Rel a b := by
  simp only [or_iff_not_imp_left, ← ne_eq]
  refine ⟨fun hab hne ↦ hf.rel_of_ne_of_apply_eq_apply hne hab, fun h ↦ ?_⟩
  obtain rfl | hne := eq_or_ne a b
  · rfl
  exact hf.apply_eq_apply (h hne)

lemma forall_apply_eq_apply_iff (hf : IsRepFun P f) (a) :
    (∀ (x : α), f a = f x ↔ a = x) ∨ (∀ (x : α), f a = f x ↔ P.Rel a x) := by
  refine (em (a ∈ u)).elim (fun ha ↦ Or.inr fun b ↦ ?_) (fun ha ↦ Or.inl fun b ↦ ?_)
  · rw [hf.apply_eq_apply_iff_rel ha]
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
  · rw [hf.apply_mem_iff] at ha
    exact hf.apply_of_notMem ha
  exact hf.apply_of_notMem ha |>.symm

lemma apply_eq_apply_iff' (hf : IsRepFun P f) :
    f a = f b ↔ (a = b ∧ ∀ c, f a = f c ↔ a = c) ∨ P.Rel a b := by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a
  · refine ⟨by grind, ?_⟩
    rintro (h | h)
    · exact congrArg _ h.1
    exact hf.apply_eq_apply h
  grind

@[simp]
lemma idem (hf : IsRepFun P f) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ u)
  · rw [eq_comm, hf.apply_eq_apply_iff_rel ha]
    exact hf.rel_apply ha
  simp_rw [hf.apply_of_notMem ha]

theorem isRepFun_isRepFun (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α) : f (g x) = f x := by
  obtain (hx | hx) := em (x ∈ u)
  · exact hf.apply_eq_apply (hg.rel_apply hx).symm
  rw [hg.apply_of_notMem hx, hf.apply_of_notMem hx]

end IsRepFun
end Partition.IsRepFun
