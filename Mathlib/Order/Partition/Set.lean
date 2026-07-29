/-
Copyright (c) 2025 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Hyeokjun Kwon
-/
module

public import Mathlib.Order.Partition.Basic

/-!
# Partitions of sets

This file specialises `Partition` to the complete lattice `Set α`. A `Partition (Set α)` is an
independent family of nonempty sets; its support `Partition.supp` is their union.

This is equivalent to a transitive and symmetric binary relation `r : α → α → Prop` where the
support is the set of all `x` for which `r x x`.

## Main declarations

* `Partition.Rel`: The partial equivalence relation induced by a partition of a set.
* `Partition.ofRel`: Reconstruct a partition from a transitive, symmetric relation.
* `Partition.partOf`: The part of a partition containing a given element.
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

-/

@[expose] public section
variable {α : Type*} {S : Set (Set α)} {s t : Set α} {a b c x y z : α} {P Q : Partition (Set α)}

open Set

namespace Partition

section Set

@[simp] protected lemma sUnion_eq (P : Partition (Set α)) : ⋃₀ P = P.supp := P.sSup_eq

lemma nonempty_of_mem (ht : t ∈ P) : t.Nonempty := notMem_singleton_empty.1 <| P.ne_bot_of_mem ht

lemma empty_notMem : ∅ ∉ P := P.bot_notMem

lemma subset_of_mem (ht : t ∈ P) : t ⊆ P.supp := P.le_of_mem ht

@[grind =]
lemma mem_supp_iff : x ∈ P.supp ↔ ∃ t ∈ P, x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨t, htP, hxt⟩ ↦ subset_of_mem htP hxt⟩
  rwa [← P.sUnion_eq, mem_sUnion] at hx

@[deprecated (since := "2026-07-28")] alias mem_iff_exists := mem_supp_iff

lemma eq_of_mem_inter (ht : t ∈ P) (hs : s ∈ P) (hx : x ∈ t ∩ s) : t = s :=
  P.pairwiseDisjoint.elim ht hs fun (hdj : Disjoint t s) ↦ by simp [hdj.inter_eq] at hx

@[grind →]
lemma eq_of_mem_of_mem (ht : t ∈ P) (hus : s ∈ P) (hxt : x ∈ t) (hxs : x ∈ s) : t = s :=
  eq_of_mem_inter ht hus ⟨hxt, hxs⟩

lemma mem_supp_iff_unique : x ∈ P.supp ↔ ∃! t, t ∈ P ∧ x ∈ t := by
  refine ⟨fun hx ↦ ?_, fun ⟨_, ⟨htP, hxt⟩, _⟩ ↦ subset_of_mem htP hxt⟩
  rw [← P.sUnion_eq, mem_sUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact ⟨t, ⟨ht, hxt⟩, fun s ⟨hsP, hxs⟩ ↦ P.eq_of_mem_of_mem hsP ht hxs hxt⟩

@[deprecated (since := "2026-07-28")] alias mem_iff_unique := mem_supp_iff_unique

lemma subset_sUnion_and_mem_iff_mem (hSP : S ⊆ P) : t ⊆ ⋃₀ S ∧ t ∈ P ↔ t ∈ S := by
  refine ⟨fun ⟨htsu, htP⟩ ↦ ?_, fun htS ↦ ⟨subset_sUnion_of_mem htS, hSP htS⟩⟩
  obtain ⟨x, hxt⟩ := nonempty_of_mem htP
  obtain ⟨s, hsS, hxs⟩ := htsu hxt
  exact eq_of_mem_of_mem htP (hSP hsS) hxt hxs ▸ hsS

lemma subset_sUnion_iff_mem (ht : t ∈ P) (hSP : S ⊆ P.parts) : t ⊆ ⋃₀ S ↔ t ∈ S := by
  rw [← subset_sUnion_and_mem_iff_mem hSP]
  simp [ht]

/-- Noncomputably choose a representative from an equivalence class. -/
noncomputable def rep (P : Partition (Set α)) (ht : t ∈ P) : α := (P.nonempty_of_mem ht).some

/-- The representative of a part belongs to that part. -/
@[simp] lemma rep_mem (ht : t ∈ P) : P.rep ht ∈ t := (P.nonempty_of_mem ht).some_mem

/-- The representative of a part belongs to the underlying set. -/
@[simp] lemma rep_mem_supp (ht : t ∈ P) : P.rep ht ∈ P.supp := P.subset_of_mem ht <| rep_mem ht

end Set

/-! ### Induced relation -/

section Rel

/-- Every partition of sets induces a transitive, symmetric binary relation on `α`
  whose equivalence classes are the parts of `P`. The relation is irreflexive outside the
  support. -/
def Rel (P : Partition (Set α)) (a b : α) : Prop :=
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
lemma rel_rfl_iff : P.Rel x x ↔ x ∈ P.supp := by
  refine ⟨fun ⟨t, ht, hxP, _⟩ ↦ subset_of_mem ht hxP, fun hx ↦ ?_⟩
  obtain ⟨t, ⟨ht, hxt⟩, -⟩ := P.mem_supp_iff_unique.mp hx
  exact ⟨t, ht, hxt, hxt⟩

instance (P : Partition (Set α)) : Std.Symm P.Rel where
  symm _ _ := fun ⟨t, ht, ha, hb⟩ ↦ ⟨t, ht, hb, ha⟩

instance (P : Partition (Set α)) : IsTrans α P.Rel where
  trans _ _ _ := fun ⟨t, ht, ha, hb⟩ ⟨t', ht', hb', hc⟩ ↦
    ⟨t, ht, ha, by rwa [eq_of_mem_of_mem ht ht' hb hb']⟩

@[symm, grind →] lemma Rel.symm (h : P.Rel x y) : P.Rel y x := symm_of P.Rel h

lemma rel_comm : P.Rel x y ↔ P.Rel y x := ⟨Rel.symm, Rel.symm⟩

@[grind →]
lemma Rel.trans (hxy : P.Rel x y) (hyz : P.Rel y z) : P.Rel x z := trans_of P.Rel hxy hyz

@[grind →]
lemma Rel.left_mem (h : P.Rel x y) : x ∈ P.supp := by
  obtain ⟨t, htP, hxt, -⟩ := h
  exact subset_of_mem htP hxt

@[grind →]
lemma Rel.right_mem (h : P.Rel x y) : y ∈ P.supp := h.symm.left_mem

/-- Any element of a part is related to the representative of that part. -/
lemma rep_rel (ht : t ∈ P) (hx : x ∈ t) : P.Rel x (P.rep ht) := ⟨t, ht, hx, P.rep_mem ht⟩

/-- The relation induced by a partition determines the partition. -/
lemma rel_injective : Function.Injective (Rel : Partition (Set α) → α → α → Prop) :=
  fun _ _ h ↦ le_antisymm (rel_le_iff_le.1 h.le) (rel_le_iff_le.1 h.ge)

@[simp]
lemma rel_inj : P.Rel = Q.Rel ↔ P = Q := rel_injective.eq_iff

/-- A transitive, symmetric relation induces a partition of its self-related elements.
Parts are the sets `{y | r y x}` for each `x` satisfying `r x x`. -/
def ofRel (r : α → α → Prop) [IsTrans α r] [Std.Symm r] : Partition (Set α) :=
  removeBot ((fun x ↦ {y | r y x}) '' {x | r x x}) <| PairwiseDisjoint.sSupIndep <| by
    rintro _ ⟨x, -, rfl⟩ _ ⟨y, -, rfl⟩ hne
    rw [Function.onFun, disjoint_iff_inter_eq_empty]
    ext z
    simp only [id_eq, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro hzx hzy
    refine hne <| Set.ext fun w ↦ ?_
    have hxy : r x y := trans_of r (symm_of r hzx) hzy
    exact ⟨fun hwx ↦ trans_of r hwx hxy, fun hwy ↦ trans_of r hwy (symm_of r hxy)⟩

@[simp]
lemma mem_ofRel_iff (r : α → α → Prop) [IsTrans α r] [Std.Symm r] : s ∈ ofRel r ↔
    ∃ x, r x x ∧ s = {y | r y x} := by
  simp only [ofRel, mem_removeBot, mem_image, mem_ofPred, ne_eq, bot_eq_empty]
  constructor
  · rintro ⟨⟨x, hxx, rfl⟩, -⟩
    exact ⟨x, hxx, rfl⟩
  · rintro ⟨x, hxx, rfl⟩
    exact ⟨⟨x, hxx, rfl⟩, nonempty_iff_ne_empty.mp ⟨x, hxx⟩⟩

@[simp]
lemma rel_ofRel_eq (r : α → α → Prop) [IsTrans α r] [Std.Symm r] : (ofRel r).Rel = r := by
  ext a b
  refine ⟨fun ⟨s, hs, ha, hb⟩ ↦ ?_, fun hab ↦ ⟨{y | r y b}, (mem_ofRel_iff r).mpr ⟨b,
    trans_of r (symm_of r hab) hab, rfl⟩, hab, trans_of r (symm_of r hab) hab⟩⟩
  obtain ⟨x, -, rfl, -⟩ := (mem_ofRel_iff r).1 hs
  exact trans_of r ha (symm_of r hb)

@[simp]
lemma supp_ofRel (r : α → α → Prop) [IsTrans α r] [Std.Symm r] : (ofRel r).supp = {a | r a a} := by
  ext a
  rw [← rel_rfl_iff, rel_ofRel_eq]
  rfl

@[simp]
lemma ofRel_rel_eq (P : Partition (Set α)) : ofRel P.Rel = P :=
  rel_injective (by simp)

end Rel

section partOf

/-- The part of a partition containing a given element. If the element is not in the
support, this is empty. -/
def partOf (P : Partition (Set α)) (a : α) : Set α := {b | P.Rel a b}

lemma partOf_subset : P.partOf x ⊆ P.supp := fun _ ⟨_, ht, _, hyt⟩ ↦ subset_of_mem ht hyt

@[simp, grind =] lemma mem_partOf_iff : x ∈ P.partOf y ↔ P.Rel y x := Iff.rfl

@[grind →]
lemma eq_partOf_of_mem (ht : t ∈ P) (hxt : x ∈ t) : t = P.partOf x := by
  ext y
  exact ⟨(⟨t, ht, hxt, ·⟩), fun ⟨s, hsP, hxs, hys⟩ ↦ (P.eq_of_mem_of_mem ht hsP hxt hxs) ▸ hys⟩

lemma mem_iff_mem_partOf_mem : x ∈ P.supp ↔ x ∈ P.partOf x ∧ P.partOf x ∈ P := by grind

@[grind →]
lemma mem_partOf (hxu : x ∈ P.supp) : x ∈ P.partOf x := (P.mem_iff_mem_partOf_mem.mp hxu).1

@[grind →]
lemma partOf_mem (hxu : x ∈ P.supp) : P.partOf x ∈ P := (P.mem_iff_mem_partOf_mem.mp hxu).2

@[simp]
lemma partOf_rep (hs : s ∈ P) : P.partOf (P.rep hs) = s :=
  eq_partOf_of_mem hs (rep_mem hs) |>.symm

lemma mem_iff_exists_partOf : s ∈ P ↔ ∃ x ∈ P.supp, partOf P x = s :=
  ⟨fun hs ↦ ⟨P.rep hs, rep_mem_supp hs, partOf_rep hs⟩, fun ⟨_, hxu, h⟩ ↦ h ▸ partOf_mem hxu⟩

lemma partOf_nonempty_iff : (P.partOf x).Nonempty ↔ x ∈ P.supp := by
  refine ⟨fun ⟨y, hy⟩ ↦ hy.left_mem, fun h ↦ ?_⟩
  simpa [nonempty_iff_ne_empty] using P.ne_bot_of_mem (partOf_mem h)

@[simp]
lemma partOf_eq_empty_iff : P.partOf x = ∅ ↔ x ∉ P.supp := by
  rw [← partOf_nonempty_iff, not_nonempty_iff_eq_empty]

lemma rel_iff_partOf_eq_partOf_of_mem (P : Partition (Set α)) (hx : x ∈ P.supp) (hy : y ∈ P.supp) :
    P.Rel x y ↔ P.partOf x = P.partOf y := by
  refine ⟨fun ⟨t, htP, hxt, hyt⟩ ↦ eq_partOf_of_mem (P.partOf_mem hx) ?_,
    fun h ↦ ⟨P.partOf x, P.partOf_mem hx, P.mem_partOf hx, h ▸ mem_partOf hy⟩⟩
  rwa [← eq_partOf_of_mem htP hxt]

lemma rel_iff_partOf_eq_partOf (P : Partition (Set α)) :
    P.Rel x y ↔ ∃ (_ : x ∈ P.supp) (_ : y ∈ P.supp), P.partOf x = P.partOf y := by
  grind [rel_iff_partOf_eq_partOf_of_mem]

end partOf

/-! ### Representative functions

See the module docstring for motivation (graph simplification, minors, and why we use an explicit
`IsRepFun` hypothesis rather than a global choice of representatives).
-/

/-- A predicate characterizing when a function `f : α → α` is a representative function for a
partition `P`. A representative function maps each element to a chosen representative in its
equivalence class, is the identity outside the support, and maps related elements to the same
representative. -/
structure IsRepFun (P : Partition (Set α)) (f : α → α) : Prop where
  /-- The function is the identity outside the support. -/
  apply_of_notMem : ∀ ⦃a⦄, a ∉ P.supp → f a = a
  /-- The function maps each element in the support to a related element. -/
  rel_apply : ∀ ⦃a⦄, a ∈ P.supp → P.Rel a (f a)
  /-- The function maps related elements to the same representative. -/
  apply_eq_apply : ∀ ⦃a b⦄, P.Rel a b → f a = f b

attribute [grind →] IsRepFun.apply_of_notMem IsRepFun.rel_apply IsRepFun.apply_eq_apply

namespace IsRepFun

variable {P : Partition (Set α)} {f g : α → α} {a b c : α}

lemma apply_mem (hf : IsRepFun P f) (ha : a ∈ P.supp) : f a ∈ P.supp := (hf.rel_apply ha).right_mem

lemma image_subset (hf : IsRepFun P f) (hs : P.supp ⊆ s) : f '' s ⊆ s := by
  rintro _ ⟨a, haS, rfl⟩
  by_cases ha : a ∈ P.supp
  · exact hs <| hf.apply_mem ha
  exact (hf.apply_of_notMem ha).symm ▸ haS

lemma mapsTo (hf : IsRepFun P f) (hs : P.supp ⊆ s) : Set.MapsTo f s s :=
  fun x h ↦ hf.image_subset hs ⟨x, h, rfl⟩

lemma mapsTo_of_disjoint (hf : IsRepFun P f) (hs : Disjoint P.supp s) : Set.MapsTo f s s :=
  fun _ h ↦ (hf.apply_of_notMem <| hs.notMem_of_mem_right h).symm ▸ h

lemma apply_mem_iff (hf : IsRepFun P f) (hs : P.supp ⊆ s) : f a ∈ s ↔ a ∈ s :=
  hf.mapsTo hs |>.mem_iff <| mapsTo_of_disjoint hf hs.disjoint_compl_right

lemma apply_eq_apply_iff_rel (hf : IsRepFun P f) (ha : a ∈ P.supp) : f a = f b ↔ P.Rel a b :=
  ⟨fun hab ↦ (hf.rel_apply ha).trans (by grind), (hf.apply_eq_apply ·)⟩

lemma apply_eq_apply_iff (hf : IsRepFun P f) : f a = f b ↔ a = b ∨ P.Rel a b := by grind

lemma forall_apply_eq_apply_iff (hf : IsRepFun P f) (a) :
    (∀ (x : α), f a = f x ↔ a = x) ∨ (∀ (x : α), f a = f x ↔ P.Rel a x) := by
  refine (em (a ∈ P.supp)).elim (fun ha ↦ Or.inr fun b ↦ ?_) (fun ha ↦ Or.inl fun b ↦ ?_)
  · rw [hf.apply_eq_apply_iff_rel ha]
  rw [hf.apply_of_notMem ha]
  constructor <;> rintro rfl
  · exact hf.apply_of_notMem <| hf.apply_mem_iff le_rfl |>.not.mp ha
  exact hf.apply_of_notMem ha |>.symm

lemma apply_eq_apply_iff' (hf : IsRepFun P f) :
    f a = f b ↔ (a = b ∧ ∀ c, f a = f c ↔ a = c) ∨ P.Rel a b := by
  obtain h1 | h2 := hf.forall_apply_eq_apply_iff a <;> grind

lemma idem (hf : IsRepFun P f) : f (f a) = f a := by
  obtain (ha | ha) := em (a ∈ P.supp) <;> grind

theorem apply_apply (hf : IsRepFun P f) (hg : IsRepFun P g) (x : α) : f (g x) = f x := by
  obtain (hx | hx) := em (x ∈ P.supp) <;> grind

/-- Any partially defined representative function extends to a complete one. -/
lemma exists_extend_partial (P : Partition (Set α)) (f₀ : t → α)
    (h_notMem : ∀ x : t, x.1 ∉ P.supp → f₀ x = x) (h_mem : ∀ x : t, x.1 ∈ P.supp → P.Rel x (f₀ x))
    (h_eq : ∀ x y : t, P.Rel x y → f₀ x = f₀ y) : ∃ f, IsRepFun P f ∧ ∀ x : t, f x = f₀ x := by
  classical
  set f : α → α := fun a ↦ if ha : a ∈ P.supp then
    (if hb : ∃ b : t, P.Rel a b then f₀ hb.choose else P.rep (P.partOf_mem ha)) else a with hfdef
  refine ⟨f, ⟨fun a ha ↦ by simp [hfdef, ha], fun a ha ↦ ?_, fun a b hab ↦ ?_⟩, fun a ↦ ?_⟩
  · simp only [hfdef, ha, ↓reduceDIte]
    split_ifs with h
    · exact h.choose_spec.trans <| h_mem h.choose h.choose_spec.right_mem
    push Not at h
    exact P.rep_rel (P.partOf_mem ha) (P.mem_partOf ha)
  · simp_rw [hfdef, dif_pos hab.left_mem, dif_pos hab.right_mem]
    split_ifs with h₁ h₂ h₂ <;> grind
  obtain (ha | ha) := em (a.1 ∈ P.supp) |>.symm
  · simp [hfdef, ha, h_notMem _ ha]
  simp only [hfdef, ha, ↓reduceDIte]
  split_ifs with h
  · exact h_eq _ _ h.choose_spec |>.symm
  exact h ⟨a, rel_rfl_iff.mpr ha⟩ |>.elim

/-- For any set `t` containing no two distinct related elements, there is a representative function
equal to the identity on `t`. -/
lemma exists_extend_partial' (P : Partition (Set α))
    (h : ∀ ⦃x y⦄, x ∈ t → y ∈ t → P.Rel x y → x = y) : ∃ f, IsRepFun P f ∧ EqOn f id t := by
  simpa using! exists_extend_partial P (fun x : t ↦ x) (by simp) (by simp) (fun x y ↦ h x.2 y.2)

/-- Every partition has a representative function. -/
lemma nonempty (P : Partition (Set α)) : ∃ f, IsRepFun P f := by
  obtain ⟨f, hf, -⟩ := exists_extend_partial' P (t := ∅) (by simp)
  exact ⟨f, hf⟩

end IsRepFun

end Partition
