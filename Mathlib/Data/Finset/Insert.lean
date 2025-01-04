/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Multiset.FinsetOps

/-!
# Constructing finite sets by adding one element

This file contains the definitions of `{a} : Finset α`, `insert a s : Finset α` and `Finset.cons`,
all ways to construct a `Finset` by adding one element.

## Main declarations

* `Finset.induction_on`: Induction on finsets. To prove a proposition about an arbitrary `Finset α`,
  it suffices to prove it for the empty finset, and to show that if it holds for some `Finset α`,
  then it holds for the finset obtained by inserting a new element.
* `Finset.instSingletonFinset`: Denoted by `{a}`; the finset consisting of one element.
* `insert` and `Finset.cons`: For any `a : α`, `insert s a` returns `s ∪ {a}`. `cons s a h`
  returns the same except that it requires a hypothesis stating that `a` is not already in `s`.
  This does not require decidable equality on the type `α`.

## Tags

finite sets, finset

-/

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen
assert_not_exists Multiset.powerset

assert_not_exists CompleteLattice

assert_not_exists OrderedCommMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*}

namespace Finset

/-! ### Subset and strict subset relations -/

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### singleton -/


section Singleton

variable {s : Finset α} {a b : α}

/-- `{a} : Finset a` is the set `{a}` containing `a` and nothing else.

This differs from `insert a ∅` in that it does not require a `DecidableEq` instance for `α`.
-/
instance : Singleton α (Finset α) :=
  ⟨fun a => ⟨{a}, nodup_singleton a⟩⟩

@[simp]
theorem singleton_val (a : α) : ({a} : Finset α).1 = {a} :=
  rfl

@[simp]
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=
  Multiset.mem_singleton

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : Finset α)) : x = y :=
  mem_singleton.1 h

theorem not_mem_singleton {a b : α} : a ∉ ({b} : Finset α) ↔ a ≠ b :=
  not_congr mem_singleton

theorem mem_singleton_self (a : α) : a ∈ ({a} : Finset α) :=
  -- Porting note: was `Or.inl rfl`
  mem_singleton.mpr rfl

@[simp]
theorem val_eq_singleton_iff {a : α} {s : Finset α} : s.val = {a} ↔ s = {a} := by
  rw [← val_inj]
  rfl

theorem singleton_injective : Injective (singleton : α → Finset α) := fun _a _b h =>
  mem_singleton.1 (h ▸ mem_singleton_self _)

@[simp]
theorem singleton_inj : ({a} : Finset α) = {b} ↔ a = b :=
  singleton_injective.eq_iff

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem singleton_nonempty (a : α) : ({a} : Finset α).Nonempty :=
  ⟨a, mem_singleton_self a⟩

@[simp]
theorem singleton_ne_empty (a : α) : ({a} : Finset α) ≠ ∅ :=
  (singleton_nonempty a).ne_empty

theorem empty_ssubset_singleton : (∅ : Finset α) ⊂ {a} :=
  (singleton_nonempty _).empty_ssubset

@[simp, norm_cast]
theorem coe_singleton (a : α) : (({a} : Finset α) : Set α) = {a} := by
  ext
  simp

@[simp, norm_cast]
theorem coe_eq_singleton {s : Finset α} {a : α} : (s : Set α) = {a} ↔ s = {a} := by
  rw [← coe_singleton, coe_inj]

@[norm_cast]
lemma coe_subset_singleton : (s : Set α) ⊆ {a} ↔ s ⊆ {a} := by rw [← coe_subset, coe_singleton]

@[norm_cast]
lemma singleton_subset_coe : {a} ⊆ (s : Set α) ↔ {a} ⊆ s := by rw [← coe_subset, coe_singleton]

theorem eq_singleton_iff_unique_mem {s : Finset α} {a : α} : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a := by
  constructor <;> intro t
  · rw [t]
    exact ⟨Finset.mem_singleton_self _, fun _ => Finset.mem_singleton.1⟩
  · ext
    rw [Finset.mem_singleton]
    exact ⟨t.right _, fun r => r.symm ▸ t.left⟩

theorem eq_singleton_iff_nonempty_unique_mem {s : Finset α} {a : α} :
    s = {a} ↔ s.Nonempty ∧ ∀ x ∈ s, x = a := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hne, h_uniq⟩
    rw [eq_singleton_iff_unique_mem]
    refine ⟨?_, h_uniq⟩
    rw [← h_uniq hne.choose hne.choose_spec]
    exact hne.choose_spec

theorem nonempty_iff_eq_singleton_default [Unique α] {s : Finset α} :
    s.Nonempty ↔ s = {default} := by
  simp [eq_singleton_iff_nonempty_unique_mem, eq_iff_true_of_subsingleton]

alias ⟨Nonempty.eq_singleton_default, _⟩ := nonempty_iff_eq_singleton_default

theorem singleton_iff_unique_mem (s : Finset α) : (∃ a, s = {a}) ↔ ∃! a, a ∈ s := by
  simp only [eq_singleton_iff_unique_mem, ExistsUnique]

theorem singleton_subset_set_iff {s : Set α} {a : α} : ↑({a} : Finset α) ⊆ s ↔ a ∈ s := by
  rw [coe_singleton, Set.singleton_subset_iff]

@[simp]
theorem singleton_subset_iff {s : Finset α} {a : α} : {a} ⊆ s ↔ a ∈ s :=
  singleton_subset_set_iff

@[simp]
theorem subset_singleton_iff {s : Finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} := by
  rw [← coe_subset, coe_singleton, Set.subset_singleton_iff_eq, coe_eq_empty, coe_eq_singleton]

theorem singleton_subset_singleton : ({a} : Finset α) ⊆ {b} ↔ a = b := by simp

protected theorem Nonempty.subset_singleton_iff {s : Finset α} {a : α} (h : s.Nonempty) :
    s ⊆ {a} ↔ s = {a} :=
  subset_singleton_iff.trans <| or_iff_right h.ne_empty

theorem subset_singleton_iff' {s : Finset α} {a : α} : s ⊆ {a} ↔ ∀ b ∈ s, b = a :=
  forall₂_congr fun _ _ => mem_singleton

@[simp]
theorem ssubset_singleton_iff {s : Finset α} {a : α} : s ⊂ {a} ↔ s = ∅ := by
  rw [← coe_ssubset, coe_singleton, Set.ssubset_singleton_iff, coe_eq_empty]

theorem eq_empty_of_ssubset_singleton {s : Finset α} {x : α} (hs : s ⊂ {x}) : s = ∅ :=
  ssubset_singleton_iff.1 hs

/-- A finset is nontrivial if it has at least two elements. -/
protected abbrev Nontrivial (s : Finset α) : Prop := (s : Set α).Nontrivial

nonrec lemma Nontrivial.nonempty (hs : s.Nontrivial) : s.Nonempty := hs.nonempty

@[simp]
theorem not_nontrivial_empty : ¬ (∅ : Finset α).Nontrivial := by simp [Finset.Nontrivial]

@[simp]
theorem not_nontrivial_singleton : ¬ ({a} : Finset α).Nontrivial := by simp [Finset.Nontrivial]

theorem Nontrivial.ne_singleton (hs : s.Nontrivial) : s ≠ {a} := by
  rintro rfl; exact not_nontrivial_singleton hs

nonrec lemma Nontrivial.exists_ne (hs : s.Nontrivial) (a : α) : ∃ b ∈ s, b ≠ a := hs.exists_ne _

theorem eq_singleton_or_nontrivial (ha : a ∈ s) : s = {a} ∨ s.Nontrivial := by
  rw [← coe_eq_singleton]; exact Set.eq_singleton_or_nontrivial ha

theorem nontrivial_iff_ne_singleton (ha : a ∈ s) : s.Nontrivial ↔ s ≠ {a} :=
  ⟨Nontrivial.ne_singleton, (eq_singleton_or_nontrivial ha).resolve_left⟩

theorem Nonempty.exists_eq_singleton_or_nontrivial : s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial :=
  fun ⟨a, ha⟩ => (eq_singleton_or_nontrivial ha).imp_left <| Exists.intro a

instance instNontrivial [Nonempty α] : Nontrivial (Finset α) :=
  ‹Nonempty α›.elim fun a => ⟨⟨{a}, ∅, singleton_ne_empty _⟩⟩

instance [IsEmpty α] : Unique (Finset α) where
  default := ∅
  uniq _ := eq_empty_of_forall_not_mem isEmptyElim

instance (i : α) : Unique ({i} : Finset α) where
  default := ⟨i, mem_singleton_self i⟩
  uniq j := Subtype.ext <| mem_singleton.mp j.2

@[simp]
lemma default_singleton (i : α) : ((default : ({i} : Finset α)) : α) = i := rfl

instance Nontrivial.instDecidablePred [DecidableEq α] :
    DecidablePred (Finset.Nontrivial (α := α)) :=
  inferInstanceAs (DecidablePred fun s ↦ ∃ a ∈ s, ∃ b ∈ s, a ≠ b)

end Singleton

/-! ### cons -/


section Cons

variable {s t : Finset α} {a b : α}

/-- `cons a s h` is the set `{a} ∪ s` containing `a` and the elements of `s`. It is the same as
`insert a s` when it is defined, but unlike `insert a s` it does not require `DecidableEq α`,
and the union is guaranteed to be disjoint. -/
def cons (a : α) (s : Finset α) (h : a ∉ s) : Finset α :=
  ⟨a ::ₘ s.1, nodup_cons.2 ⟨h, s.2⟩⟩

@[simp]
theorem mem_cons {h} : b ∈ s.cons a h ↔ b = a ∨ b ∈ s :=
  Multiset.mem_cons

theorem mem_cons_of_mem {a b : α} {s : Finset α} {hb : b ∉ s} (ha : a ∈ s) : a ∈ cons b s hb :=
  Multiset.mem_cons_of_mem ha

theorem mem_cons_self (a : α) (s : Finset α) {h} : a ∈ cons a s h :=
  Multiset.mem_cons_self _ _

@[simp]
theorem cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1 :=
  rfl

theorem eq_of_mem_cons_of_not_mem (has : a ∉ s) (h : b ∈ cons a s has) (hb : b ∉ s) : b = a :=
  (mem_cons.1 h).resolve_right hb

theorem mem_of_mem_cons_of_ne {s : Finset α} {a : α} {has} {i : α}
    (hi : i ∈ cons a s has) (hia : i ≠ a) : i ∈ s :=
  (mem_cons.1 hi).resolve_left hia

theorem forall_mem_cons (h : a ∉ s) (p : α → Prop) :
    (∀ x, x ∈ cons a s h → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [mem_cons, or_imp, forall_and, forall_eq]

/-- Useful in proofs by induction. -/
theorem forall_of_forall_cons {p : α → Prop} {h : a ∉ s} (H : ∀ x, x ∈ cons a s h → p x) (x)
    (h : x ∈ s) : p x :=
  H _ <| mem_cons.2 <| Or.inr h

@[simp]
theorem mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) :
    (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 :=
  rfl

@[simp]
theorem cons_empty (a : α) : cons a ∅ (not_mem_empty _) = {a} := rfl

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty :=
  ⟨a, mem_cons.2 <| Or.inl rfl⟩

@[deprecated (since := "2024-09-19")] alias nonempty_cons := cons_nonempty

@[simp] theorem cons_ne_empty (h : a ∉ s) : cons a s h ≠ ∅ := (cons_nonempty _).ne_empty

@[simp]
theorem nonempty_mk {m : Multiset α} {hm} : (⟨m, hm⟩ : Finset α).Nonempty ↔ m ≠ 0 := by
  induction m using Multiset.induction_on <;> simp

@[simp]
theorem coe_cons {a s h} : (@cons α a s h : Set α) = insert a (s : Set α) := by
  ext
  simp

theorem subset_cons (h : a ∉ s) : s ⊆ s.cons a h :=
  Multiset.subset_cons _ _

theorem ssubset_cons (h : a ∉ s) : s ⊂ s.cons a h :=
  Multiset.ssubset_cons h

theorem cons_subset {h : a ∉ s} : s.cons a h ⊆ t ↔ a ∈ t ∧ s ⊆ t :=
  Multiset.cons_subset

@[simp]
theorem cons_subset_cons {hs ht} : s.cons a hs ⊆ t.cons a ht ↔ s ⊆ t := by
  rwa [← coe_subset, coe_cons, coe_cons, Set.insert_subset_insert_iff, coe_subset]

theorem ssubset_iff_exists_cons_subset : s ⊂ t ↔ ∃ (a : _) (h : a ∉ s), s.cons a h ⊆ t := by
  refine ⟨fun h => ?_, fun ⟨a, ha, h⟩ => ssubset_of_ssubset_of_subset (ssubset_cons _) h⟩
  obtain ⟨a, hs, ht⟩ := not_subset.1 h.2
  exact ⟨a, ht, cons_subset.2 ⟨hs, h.subset⟩⟩

theorem cons_swap (hb : b ∉ s) (ha : a ∉ s.cons b hb) :
    (s.cons b hb).cons a ha = (s.cons a fun h ↦ ha (mem_cons.mpr (.inr h))).cons b fun h ↦
      ha (mem_cons.mpr (.inl ((mem_cons.mp h).elim symm (fun h ↦ False.elim (hb h))))) :=
  eq_of_veq <| Multiset.cons_swap a b s.val

/-- Split the added element of cons off a Pi type. -/
@[simps!]
def consPiProd (f : α → Type*) (has : a ∉ s) (x : Π i ∈ cons a s has, f i) : f a × Π i ∈ s, f i :=
  (x a (mem_cons_self a s), fun i hi => x i (mem_cons_of_mem hi))

/-- Combine a product with a pi type to pi of cons. -/
def prodPiCons [DecidableEq α] (f : α → Type*) {a : α} (has : a ∉ s) (x : f a × Π i ∈ s, f i) :
    (Π i ∈ cons a s has, f i) :=
  fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_cons_of_ne hi h)

/-- The equivalence between pi types on cons and the product. -/
def consPiProdEquiv [DecidableEq α] {s : Finset α} (f : α → Type*) {a : α} (has : a ∉ s) :
    (Π i ∈ cons a s has, f i) ≃ f a × Π i ∈ s, f i where
  toFun := consPiProd f has
  invFun := prodPiCons f has
  left_inv _ := by
    ext i _
    dsimp only [prodPiCons, consPiProd]
    by_cases h : i = a
    · rw [dif_pos h]
      subst h
      simp_all only [cast_eq]
    · rw [dif_neg h]
  right_inv _ := by
    ext _ hi
    · simp [prodPiCons]
    · simp only [consPiProd_snd]
      exact dif_neg (ne_of_mem_of_not_mem hi has)

end Cons

/-! ### insert -/

section Insert

variable [DecidableEq α] {s t : Finset α} {a b : α} {f : α → β}

/-- `insert a s` is the set `{a} ∪ s` containing `a` and the elements of `s`. -/
instance : Insert α (Finset α) :=
  ⟨fun a s => ⟨_, s.2.ndinsert a⟩⟩

theorem insert_def (a : α) (s : Finset α) : insert a s = ⟨_, s.2.ndinsert a⟩ :=
  rfl

@[simp]
theorem insert_val (a : α) (s : Finset α) : (insert a s).1 = ndinsert a s.1 :=
  rfl

theorem insert_val' (a : α) (s : Finset α) : (insert a s).1 = dedup (a ::ₘ s.1) := by
  rw [dedup_cons, dedup_eq_self]; rfl

theorem insert_val_of_not_mem {a : α} {s : Finset α} (h : a ∉ s) : (insert a s).1 = a ::ₘ s.1 := by
  rw [insert_val, ndinsert_of_not_mem h]

@[simp]
theorem mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s :=
  mem_ndinsert

theorem mem_insert_self (a : α) (s : Finset α) : a ∈ insert a s :=
  mem_ndinsert_self a s.1

theorem mem_insert_of_mem (h : a ∈ s) : a ∈ insert b s :=
  mem_ndinsert_of_mem h

theorem mem_of_mem_insert_of_ne (h : b ∈ insert a s) : b ≠ a → b ∈ s :=
  (mem_insert.1 h).resolve_left

theorem eq_of_mem_insert_of_not_mem (ha : b ∈ insert a s) (hb : b ∉ s) : b = a :=
  (mem_insert.1 ha).resolve_right hb

/-- A version of `LawfulSingleton.insert_emptyc_eq` that works with `dsimp`. -/
@[simp] lemma insert_empty : insert a (∅ : Finset α) = {a} := rfl

@[simp]
theorem cons_eq_insert (a s h) : @cons α a s h = insert a s :=
  ext fun a => by simp

@[simp, norm_cast]
theorem coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (insert a s : Set α) :=
  Set.ext fun x => by simp only [mem_coe, mem_insert, Set.mem_insert_iff]

theorem mem_insert_coe {s : Finset α} {x y : α} : x ∈ insert y s ↔ x ∈ insert y (s : Set α) := by
  simp

instance : LawfulSingleton α (Finset α) :=
  ⟨fun a => by ext; simp⟩

@[simp]
theorem insert_eq_of_mem (h : a ∈ s) : insert a s = s :=
  eq_of_veq <| ndinsert_of_mem h

@[simp]
theorem insert_eq_self : insert a s = s ↔ a ∈ s :=
  ⟨fun h => h ▸ mem_insert_self _ _, insert_eq_of_mem⟩

theorem insert_ne_self : insert a s ≠ s ↔ a ∉ s :=
  insert_eq_self.not

theorem pair_eq_singleton (a : α) : ({a, a} : Finset α) = {a} :=
  insert_eq_of_mem <| mem_singleton_self _

theorem insert_comm (a b : α) (s : Finset α) : insert a (insert b s) = insert b (insert a s) :=
  ext fun x => by simp only [mem_insert, or_left_comm]

@[deprecated (since := "2024-11-29")] alias Insert.comm := insert_comm

@[norm_cast]
theorem coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a, b} := by
  ext
  simp

@[simp, norm_cast]
theorem coe_eq_pair {s : Finset α} {a b : α} : (s : Set α) = {a, b} ↔ s = {a, b} := by
  rw [← coe_pair, coe_inj]

theorem pair_comm (a b : α) : ({a, b} : Finset α) = {b, a} :=
  insert_comm a b ∅

theorem insert_idem (a : α) (s : Finset α) : insert a (insert a s) = insert a s :=
  ext fun x => by simp only [mem_insert, ← or_assoc, or_self_iff]

@[simp, aesop safe apply (rule_sets := [finsetNonempty])]
theorem insert_nonempty (a : α) (s : Finset α) : (insert a s).Nonempty :=
  ⟨a, mem_insert_self a s⟩

@[simp]
theorem insert_ne_empty (a : α) (s : Finset α) : insert a s ≠ ∅ :=
  (insert_nonempty a s).ne_empty

-- Porting note: explicit universe annotation is no longer required.
instance (i : α) (s : Finset α) : Nonempty ((insert i s : Finset α) : Set α) :=
  (Finset.coe_nonempty.mpr (s.insert_nonempty i)).to_subtype

theorem ne_insert_of_not_mem (s t : Finset α) {a : α} (h : a ∉ s) : s ≠ insert a t := by
  contrapose! h
  simp [h]

theorem insert_subset_iff : insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t := by
  simp only [subset_iff, mem_insert, forall_eq, or_imp, forall_and]

theorem insert_subset (ha : a ∈ t) (hs : s ⊆ t) : insert a s ⊆ t :=
  insert_subset_iff.mpr ⟨ha,hs⟩

@[simp] theorem subset_insert (a : α) (s : Finset α) : s ⊆ insert a s := fun _b => mem_insert_of_mem

@[gcongr]
theorem insert_subset_insert (a : α) {s t : Finset α} (h : s ⊆ t) : insert a s ⊆ insert a t :=
  insert_subset_iff.2 ⟨mem_insert_self _ _, Subset.trans h (subset_insert _ _)⟩

@[simp] lemma insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t := by
  simp_rw [← coe_subset]; simp [-coe_subset, ha]

theorem insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
  ⟨fun h => eq_of_mem_insert_of_not_mem (h ▸ mem_insert_self _ _) ha, congr_arg (insert · s)⟩

theorem insert_inj_on (s : Finset α) : Set.InjOn (fun a => insert a s) sᶜ := fun _ h _ _ =>
  (insert_inj h).1

theorem ssubset_iff : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t := mod_cast @Set.ssubset_iff_insert α s t

theorem ssubset_insert (h : a ∉ s) : s ⊂ insert a s :=
  ssubset_iff.mpr ⟨a, h, Subset.rfl⟩

@[elab_as_elim]
theorem cons_induction {α : Type*} {p : Finset α → Prop} (empty : p ∅)
    (cons : ∀ (a : α) (s : Finset α) (h : a ∉ s), p s → p (cons a s h)) : ∀ s, p s
  | ⟨s, nd⟩ => by
    induction s using Multiset.induction with
    | empty => exact empty
    | cons a s IH =>
      rw [mk_cons nd]
      exact cons a _ _ (IH _)

@[elab_as_elim]
theorem cons_induction_on {α : Type*} {p : Finset α → Prop} (s : Finset α) (h₁ : p ∅)
    (h₂ : ∀ ⦃a : α⦄ {s : Finset α} (h : a ∉ s), p s → p (cons a s h)) : p s :=
  cons_induction h₁ h₂ s

@[elab_as_elim]
protected theorem induction {α : Type*} {p : Finset α → Prop} [DecidableEq α] (empty : p ∅)
    (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : ∀ s, p s :=
  cons_induction empty fun a s ha => (s.cons_eq_insert a ha).symm ▸ insert ha

/-- To prove a proposition about an arbitrary `Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α`,
then it holds for the `Finset` obtained by inserting a new element.
-/
@[elab_as_elim]
protected theorem induction_on {α : Type*} {p : Finset α → Prop} [DecidableEq α] (s : Finset α)
    (empty : p ∅) (insert : ∀ ⦃a : α⦄ {s : Finset α}, a ∉ s → p s → p (insert a s)) : p s :=
  Finset.induction empty insert s

/-- To prove a proposition about `S : Finset α`,
it suffices to prove it for the empty `Finset`,
and to show that if it holds for some `Finset α ⊆ S`,
then it holds for the `Finset` obtained by inserting a new element of `S`.
-/
@[elab_as_elim]
theorem induction_on' {α : Type*} {p : Finset α → Prop} [DecidableEq α] (S : Finset α) (h₁ : p ∅)
    (h₂ : ∀ {a s}, a ∈ S → s ⊆ S → a ∉ s → p s → p (insert a s)) : p S :=
  @Finset.induction_on α (fun T => T ⊆ S → p T) _ S (fun _ => h₁)
    (fun _ _ has hqs hs =>
      let ⟨hS, sS⟩ := Finset.insert_subset_iff.1 hs
      h₂ hS sS has (hqs sS))
    (Finset.Subset.refl S)

/-- To prove a proposition about a nonempty `s : Finset α`, it suffices to show it holds for all
singletons and that if it holds for nonempty `t : Finset α`, then it also holds for the `Finset`
obtained by inserting an element in `t`. -/
@[elab_as_elim]
theorem Nonempty.cons_induction {α : Type*} {p : ∀ s : Finset α, s.Nonempty → Prop}
    (singleton : ∀ a, p {a} (singleton_nonempty _))
    (cons : ∀ a s (h : a ∉ s) (hs), p s hs → p (Finset.cons a s h) (cons_nonempty h))
    {s : Finset α} (hs : s.Nonempty) : p s hs := by
  induction s using Finset.cons_induction with
  | empty => exact (not_nonempty_empty hs).elim
  | cons a t ha h =>
    obtain rfl | ht := t.eq_empty_or_nonempty
    · exact singleton a
    · exact cons a t ha ht (h ht)

-- We use a fresh `α` here to exclude the unneeded `DecidableEq α` instance from the section.
lemma Nonempty.exists_cons_eq {α} {s : Finset α} (hs : s.Nonempty) : ∃ t a ha, cons a t ha = s :=
  hs.cons_induction (fun a ↦ ⟨∅, a, _, cons_empty _⟩) fun _ _ _ _ _ ↦ ⟨_, _, _, rfl⟩

/-- Inserting an element to a finite set is equivalent to the option type. -/
def subtypeInsertEquivOption {t : Finset α} {x : α} (h : x ∉ t) :
    { i // i ∈ insert x t } ≃ Option { i // i ∈ t } where
  toFun y := if h : ↑y = x then none else some ⟨y, (mem_insert.mp y.2).resolve_left h⟩
  invFun y := (y.elim ⟨x, mem_insert_self _ _⟩) fun z => ⟨z, mem_insert_of_mem z.2⟩
  left_inv y := by
    by_cases h : ↑y = x
    · simp only [Subtype.ext_iff, h, Option.elim, dif_pos, Subtype.coe_mk]
    · simp only [h, Option.elim, dif_neg, not_false_iff, Subtype.coe_eta, Subtype.coe_mk]
  right_inv := by
    rintro (_ | y)
    · simp only [Option.elim, dif_pos]
    · have : ↑y ≠ x := by
        rintro ⟨⟩
        exact h y.2
      simp only [this, Option.elim, Subtype.eta, dif_neg, not_false_iff, Subtype.coe_mk]

/-- Split the added element of insert off a Pi type. -/
@[simps!]
def insertPiProd (f : α → Type*) (x : Π i ∈ insert a s, f i) : f a × Π i ∈ s, f i :=
  (x a (mem_insert_self a s), fun i hi => x i (mem_insert_of_mem hi))

/-- Combine a product with a pi type to pi of insert. -/
def prodPiInsert (f : α → Type*) {a : α} (x : f a × Π i ∈ s, f i) : (Π i ∈ insert a s, f i) :=
  fun i hi =>
    if h : i = a then cast (congrArg f h.symm) x.1 else x.2 i (mem_of_mem_insert_of_ne hi h)

/-- The equivalence between pi types on insert and the product. -/
def insertPiProdEquiv [DecidableEq α] {s : Finset α} (f : α → Type*) {a : α} (has : a ∉ s) :
    (Π i ∈ insert a s, f i) ≃ f a × Π i ∈ s, f i where
  toFun := insertPiProd f
  invFun := prodPiInsert f
  left_inv _ := by
    ext i _
    dsimp only [prodPiInsert, insertPiProd]
    by_cases h : i = a
    · rw [dif_pos h]
      subst h
      simp_all only [cast_eq]
    · rw [dif_neg h]
  right_inv _ := by
    ext _ hi
    · simp [prodPiInsert]
    · simp only [insertPiProd_snd]
      exact dif_neg (ne_of_mem_of_not_mem hi has)

-- useful rules for calculations with quantifiers
theorem exists_mem_insert (a : α) (s : Finset α) (p : α → Prop) :
    (∃ x, x ∈ insert a s ∧ p x) ↔ p a ∨ ∃ x, x ∈ s ∧ p x := by
  simp only [mem_insert, or_and_right, exists_or, exists_eq_left]

theorem forall_mem_insert (a : α) (s : Finset α) (p : α → Prop) :
    (∀ x, x ∈ insert a s → p x) ↔ p a ∧ ∀ x, x ∈ s → p x := by
  simp only [mem_insert, or_imp, forall_and, forall_eq]

/-- Useful in proofs by induction. -/
theorem forall_of_forall_insert {p : α → Prop} {a : α} {s : Finset α}
    (H : ∀ x, x ∈ insert a s → p x) (x) (h : x ∈ s) : p x :=
  H _ <| mem_insert_of_mem h

end Insert

end Finset

namespace Multiset

variable [DecidableEq α]

@[simp]
theorem toFinset_zero : toFinset (0 : Multiset α) = ∅ :=
  rfl

@[simp]
theorem toFinset_cons (a : α) (s : Multiset α) : toFinset (a ::ₘ s) = insert a (toFinset s) :=
  Finset.eq_of_veq dedup_cons

@[simp]
theorem toFinset_singleton (a : α) : toFinset ({a} : Multiset α) = {a} := by
  rw [← cons_zero, toFinset_cons, toFinset_zero, LawfulSingleton.insert_emptyc_eq]

end Multiset

namespace List

variable [DecidableEq α] {l : List α} {a : α}

@[simp]
theorem toFinset_nil : toFinset (@nil α) = ∅ :=
  rfl

@[simp]
theorem toFinset_cons : toFinset (a :: l) = insert a (toFinset l) :=
  Finset.eq_of_veq <| by by_cases h : a ∈ l <;> simp [Finset.insert_val', Multiset.dedup_cons, h]

theorem toFinset_replicate_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (List.replicate n a).toFinset = {a} := by
  ext x
  simp [hn, List.mem_replicate]

@[simp]
theorem toFinset_eq_empty_iff (l : List α) : l.toFinset = ∅ ↔ l = nil := by
  cases l <;> simp

@[simp]
theorem toFinset_nonempty_iff (l : List α) : l.toFinset.Nonempty ↔ l ≠ [] := by
  simp [Finset.nonempty_iff_ne_empty]

end List

namespace Finset

section ToList

@[simp]
theorem toList_eq_singleton_iff {a : α} {s : Finset α} : s.toList = [a] ↔ s = {a} := by
  rw [toList, Multiset.toList_eq_singleton_iff, val_eq_singleton_iff]

@[simp]
theorem toList_singleton : ∀ a, ({a} : Finset α).toList = [a] :=
  Multiset.toList_singleton

open scoped List in
theorem toList_cons {a : α} {s : Finset α} (h : a ∉ s) : (cons a s h).toList ~ a :: s.toList :=
  (List.perm_ext_iff_of_nodup (nodup_toList _) (by simp [h, nodup_toList s])).2 fun x => by
    simp only [List.mem_cons, Finset.mem_toList, Finset.mem_cons]

open scoped List in
theorem toList_insert [DecidableEq α] {a : α} {s : Finset α} (h : a ∉ s) :
    (insert a s).toList ~ a :: s.toList :=
  cons_eq_insert _ _ h ▸ toList_cons _

end ToList

section Pairwise

variable {s : Finset α}

theorem pairwise_cons' {a : α} (ha : a ∉ s) (r : β → β → Prop) (f : α → β) :
    Pairwise (r on fun a : s.cons a ha => f a) ↔
    Pairwise (r on fun a : s => f a) ∧ ∀ b ∈ s, r (f a) (f b) ∧ r (f b) (f a) := by
  simp only [pairwise_subtype_iff_pairwise_finset', Finset.coe_cons, Set.pairwise_insert,
    Finset.mem_coe, and_congr_right_iff]
  exact fun _ =>
    ⟨fun h b hb =>
      h b hb <| by
        rintro rfl
        contradiction,
      fun h b hb _ => h b hb⟩

theorem pairwise_cons {a : α} (ha : a ∉ s) (r : α → α → Prop) :
    Pairwise (r on fun a : s.cons a ha => a) ↔
      Pairwise (r on fun a : s => a) ∧ ∀ b ∈ s, r a b ∧ r b a :=
  pairwise_cons' ha r id

end Pairwise

end Finset
