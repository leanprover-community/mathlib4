/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather

! This file was ported from Lean 3 source module data.list.sigma
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Range
import Mathbin.Data.List.Perm

/-!
# Utilities for lists of sigmas

This file includes several ways of interacting with `list (sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `list (sigma β)` behaves like a key-value store.

## Main Definitions

- `list.keys` extracts the list of keys.
- `list.nodupkeys` determines if the store has duplicate keys.
- `list.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `list.kreplace` replaces the first value with a given key by a given value.
- `list.kerase` removes a value.
- `list.kinsert` inserts a value.
- `list.kunion` computes the union of two stores.
- `list.kextract` returns a value with a given key and the rest of the values.
-/


universe u v

namespace List

variable {α : Type u} {β : α → Type v} {l l₁ l₂ : List (Sigma β)}

/-! ### `keys` -/


/-- List of keys from a list of key-value pairs -/
def keys : List (Sigma β) → List α :=
  map Sigma.fst
#align list.keys List.keys

@[simp]
theorem keys_nil : @keys α β [] = [] :=
  rfl
#align list.keys_nil List.keys_nil

@[simp]
theorem keys_cons {s} {l : List (Sigma β)} : (s :: l).keys = s.1 :: l.keys :=
  rfl
#align list.keys_cons List.keys_cons

theorem mem_keys_of_mem {s : Sigma β} {l : List (Sigma β)} : s ∈ l → s.1 ∈ l.keys :=
  mem_map_of_mem Sigma.fst
#align list.mem_keys_of_mem List.mem_keys_of_mem

theorem exists_of_mem_keys {a} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ b : β a, Sigma.mk a b ∈ l :=
  let ⟨⟨a', b'⟩, m, e⟩ := exists_of_mem_map' h
  Eq.recOn e (Exists.intro b' m)
#align list.exists_of_mem_keys List.exists_of_mem_keys

theorem mem_keys {a} {l : List (Sigma β)} : a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l :=
  ⟨exists_of_mem_keys, fun ⟨b, h⟩ => mem_keys_of_mem h⟩
#align list.mem_keys List.mem_keys

theorem not_mem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ b : β a, Sigma.mk a b ∉ l :=
  (not_congr mem_keys).trans not_exists
#align list.not_mem_keys List.not_mem_keys

theorem not_eq_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ s : Sigma β, s ∈ l → a ≠ s.1 :=
  Iff.intro (fun h₁ s h₂ e => absurd (mem_keys_of_mem h₂) (by rwa [e] at h₁)) fun f h₁ =>
    let ⟨b, h₂⟩ := exists_of_mem_keys h₁
    f _ h₂ rfl
#align list.not_eq_key List.not_eq_key

/-! ### `nodupkeys` -/


/-- Determines whether the store uses a key several times. -/
def Nodupkeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup
#align list.nodupkeys List.Nodupkeys

theorem nodupkeys_iff_pairwise {l} : Nodupkeys l ↔ Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  pairwise_map' _
#align list.nodupkeys_iff_pairwise List.nodupkeys_iff_pairwise

theorem Nodupkeys.pairwise_ne {l} (h : Nodupkeys l) :
    Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  nodupkeys_iff_pairwise.1 h
#align list.nodupkeys.pairwise_ne List.Nodupkeys.pairwise_ne

@[simp]
theorem nodupkeys_nil : @Nodupkeys α β [] :=
  pairwise.nil
#align list.nodupkeys_nil List.nodupkeys_nil

@[simp]
theorem nodupkeys_cons {s : Sigma β} {l : List (Sigma β)} :
    Nodupkeys (s :: l) ↔ s.1 ∉ l.keys ∧ Nodupkeys l := by simp [keys, nodupkeys]
#align list.nodupkeys_cons List.nodupkeys_cons

theorem Nodupkeys.eq_of_fst_eq {l : List (Sigma β)} (nd : Nodupkeys l) {s s' : Sigma β} (h : s ∈ l)
    (h' : s' ∈ l) : s.1 = s'.1 → s = s' :=
  @Pairwise.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 → s = s') _
    (fun s s' H h => (H h.symm).symm) (fun x h _ => rfl)
    ((nodupkeys_iff_pairwise.1 nd).imp fun s s' h h' => (h h').elim) _ h _ h'
#align list.nodupkeys.eq_of_fst_eq List.Nodupkeys.eq_of_fst_eq

theorem Nodupkeys.eq_of_mk_mem {a : α} {b b' : β a} {l : List (Sigma β)} (nd : Nodupkeys l)
    (h : Sigma.mk a b ∈ l) (h' : Sigma.mk a b' ∈ l) : b = b' := by
  cases nd.eq_of_fst_eq h h' rfl <;> rfl
#align list.nodupkeys.eq_of_mk_mem List.Nodupkeys.eq_of_mk_mem

theorem nodupkeys_singleton (s : Sigma β) : Nodupkeys [s] :=
  nodup_singleton _
#align list.nodupkeys_singleton List.nodupkeys_singleton

theorem Nodupkeys.sublist {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂) : Nodupkeys l₂ → Nodupkeys l₁ :=
  nodup.sublist <| h.map _
#align list.nodupkeys.sublist List.Nodupkeys.sublist

protected theorem Nodupkeys.nodup {l : List (Sigma β)} : Nodupkeys l → Nodup l :=
  Nodup.of_map _
#align list.nodupkeys.nodup List.Nodupkeys.nodup

theorem perm_nodupkeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : Nodupkeys l₁ ↔ Nodupkeys l₂ :=
  (h.map _).nodup_iff
#align list.perm_nodupkeys List.perm_nodupkeys

theorem nodupkeys_join {L : List (List (Sigma β))} :
    Nodupkeys (join L) ↔ (∀ l ∈ L, Nodupkeys l) ∧ Pairwise Disjoint (L.map keys) :=
  by
  rw [nodupkeys_iff_pairwise, pairwise_join, pairwise_map]
  refine' and_congr (ball_congr fun l h => by simp [nodupkeys_iff_pairwise]) _
  apply iff_of_eq; congr with (l₁ l₂)
  simp [keys, disjoint_iff_ne]
#align list.nodupkeys_join List.nodupkeys_join

theorem nodup_enum_map_fst (l : List α) : (l.enum.map Prod.fst).Nodup := by simp [List.nodup_range]
#align list.nodup_enum_map_fst List.nodup_enum_map_fst

theorem mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup)
    (h : ∀ x, x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ :=
  by
  induction' l₀ with x xs generalizing l₁ <;> cases' l₁ with y ys
  · constructor
  iterate 2 
    first |specialize h x|specialize h y; simp at h
    cases h
  simp at nd₀ nd₁
  classical
    obtain rfl | h' := eq_or_ne x y
    · constructor
      refine' l₀_ih nd₀.2 nd₁.2 fun a => _
      specialize h a
      simp at h
      obtain rfl | h' := eq_or_ne a x
      · exact iff_of_false nd₀.1 nd₁.1
      · simpa [h'] using h
    · trans x :: y :: ys.erase x
      · constructor
        refine' l₀_ih nd₀.2 ((nd₁.2.erase _).cons fun h => nd₁.1 <| mem_of_mem_erase h) fun a => _
        · specialize h a
          simp at h
          obtain rfl | h' := eq_or_ne a x
          · exact iff_of_false nd₀.1 fun h => h.elim h' nd₁.2.not_mem_erase
          · rw [or_iff_right h'] at h
            rw [h, mem_cons_iff]
            exact or_congr_right (mem_erase_of_ne h').symm
      trans y :: x :: ys.erase x
      · constructor
      · constructor
        symm
        apply perm_cons_erase
        specialize h x
        simp [h'] at h
        exact h
#align list.mem_ext List.mem_ext

variable [DecidableEq α]

/-! ### `lookup` -/


/- warning: list.lookup -> List.lookup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : α -> Type.{u2}} [_inst_1 : DecidableEq.{succ u1} α] (a : α), (List.{max u1 u2} (Sigma.{u1, u2} α β)) -> (Option.{u2} (β a))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : BEq.{u1} α], α -> (List.{max u2 u1} (Prod.{u1, u2} α β)) -> (Option.{u2} β)
Case conversion may be inaccurate. Consider using '#align list.lookup List.lookupₓ'. -/
/-- `lookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def lookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else lookup l
#align list.lookup List.lookup

@[simp]
theorem lookup_nil (a : α) : lookup a [] = @none (β a) :=
  rfl
#align list.lookup_nil List.lookup_nil

@[simp]
theorem lookup_cons_eq (l) (a : α) (b : β a) : lookup a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl
#align list.lookup_cons_eq List.lookup_cons_eq

@[simp]
theorem lookup_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → lookup a (s :: l) = lookup a l
  | ⟨a', b⟩, h => dif_neg h.symm
#align list.lookup_cons_ne List.lookup_cons_ne

theorem lookup_is_some {a : α} : ∀ {l : List (Sigma β)}, (lookup a l).isSome ↔ a ∈ l.keys
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simp [h, lookup_is_some]
#align list.lookup_is_some List.lookup_is_some

theorem lookup_eq_none {a : α} {l : List (Sigma β)} : lookup a l = none ↔ a ∉ l.keys := by
  simp [← lookup_is_some, Option.is_none_iff_eq_none]
#align list.lookup_eq_none List.lookup_eq_none

theorem of_mem_lookup {a : α} {b : β a} : ∀ {l : List (Sigma β)}, b ∈ lookup a l → Sigma.mk a b ∈ l
  | ⟨a', b'⟩ :: l, H => by
    by_cases h : a = a'
    · subst a'
      simp at H
      simp [H]
    · simp [h] at H
      exact Or.inr (of_mem_lookup H)
#align list.of_mem_lookup List.of_mem_lookup

theorem mem_lookup {a} {b : β a} {l : List (Sigma β)} (nd : l.Nodupkeys) (h : Sigma.mk a b ∈ l) :
    b ∈ lookup a l :=
  by
  cases' option.is_some_iff_exists.mp (lookup_is_some.mpr (mem_keys_of_mem h)) with b' h'
  cases nd.eq_of_mk_mem h (of_mem_lookup h')
  exact h'
#align list.mem_lookup List.mem_lookup

theorem map_lookup_eq_find (a : α) :
    ∀ l : List (Sigma β), (lookup a l).map (Sigma.mk a) = find? (fun s => a = s.1) l
  | [] => rfl
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simp [h, map_lookup_eq_find]
#align list.map_lookup_eq_find List.map_lookup_eq_find

theorem mem_lookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.Nodupkeys) :
    b ∈ lookup a l ↔ Sigma.mk a b ∈ l :=
  ⟨of_mem_lookup, mem_lookup nd⟩
#align list.mem_lookup_iff List.mem_lookup_iff

theorem perm_lookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.Nodupkeys) (nd₂ : l₂.Nodupkeys)
    (p : l₁ ~ l₂) : lookup a l₁ = lookup a l₂ := by
  ext b <;> simp [mem_lookup_iff, nd₁, nd₂] <;> exact p.mem_iff
#align list.perm_lookup List.perm_lookup

theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodupkeys) (nd₁ : l₁.Nodupkeys)
    (h : ∀ x y, y ∈ l₀.lookup x ↔ y ∈ l₁.lookup x) : l₀ ~ l₁ :=
  mem_ext nd₀.Nodup nd₁.Nodup fun ⟨a, b⟩ => by
    rw [← mem_lookup_iff, ← mem_lookup_iff, h] <;> assumption
#align list.lookup_ext List.lookup_ext

/-! ### `lookup_all` -/


/-- `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
def lookupAll (a : α) : List (Sigma β) → List (β a)
  | [] => []
  | ⟨a', b⟩ :: l => if h : a' = a then Eq.recOn h b :: lookup_all l else lookup_all l
#align list.lookup_all List.lookupAll

@[simp]
theorem lookup_all_nil (a : α) : lookupAll a [] = @nil (β a) :=
  rfl
#align list.lookup_all_nil List.lookup_all_nil

@[simp]
theorem lookup_all_cons_eq (l) (a : α) (b : β a) : lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l :=
  dif_pos rfl
#align list.lookup_all_cons_eq List.lookup_all_cons_eq

@[simp]
theorem lookup_all_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → lookupAll a (s :: l) = lookupAll a l
  | ⟨a', b⟩, h => dif_neg h.symm
#align list.lookup_all_cons_ne List.lookup_all_cons_ne

theorem lookup_all_eq_nil {a : α} :
    ∀ {l : List (Sigma β)}, lookupAll a l = [] ↔ ∀ b : β a, Sigma.mk a b ∉ l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simp [h, lookup_all_eq_nil]
#align list.lookup_all_eq_nil List.lookup_all_eq_nil

theorem head_lookup_all (a : α) : ∀ l : List (Sigma β), head? (lookupAll a l) = lookup a l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a' <;>
      [·
        subst h
        simp, simp [*]]
#align list.head_lookup_all List.head_lookup_all

theorem mem_lookup_all {a : α} {b : β a} :
    ∀ {l : List (Sigma β)}, b ∈ lookupAll a l ↔ Sigma.mk a b ∈ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a' <;>
      [·
        subst h
        simp [*], simp [*]]
#align list.mem_lookup_all List.mem_lookup_all

theorem lookup_all_sublist (a : α) : ∀ l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp
      exact (lookup_all_sublist l).cons2 _ _ _
    · simp [h]
      exact (lookup_all_sublist l).cons _ _ _
#align list.lookup_all_sublist List.lookup_all_sublist

theorem lookup_all_length_le_one (a : α) {l : List (Sigma β)} (h : l.Nodupkeys) :
    length (lookupAll a l) ≤ 1 := by
  have := nodup.sublist ((lookup_all_sublist a l).map _) h <;> rw [map_map] at this <;>
    rwa [← nodup_repeat, ← map_const _ a]
#align list.lookup_all_length_le_one List.lookup_all_length_le_one

theorem lookup_all_eq_lookup (a : α) {l : List (Sigma β)} (h : l.Nodupkeys) :
    lookupAll a l = (lookup a l).toList :=
  by
  rw [← head_lookup_all]
  have := lookup_all_length_le_one a h; revert this
  rcases lookup_all a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;> intro <;> try rfl
  exact absurd this (by decide)
#align list.lookup_all_eq_lookup List.lookup_all_eq_lookup

theorem lookup_all_nodup (a : α) {l : List (Sigma β)} (h : l.Nodupkeys) : (lookupAll a l).Nodup :=
  by rw [lookup_all_eq_lookup a h] <;> apply Option.toList_nodup
#align list.lookup_all_nodup List.lookup_all_nodup

theorem perm_lookup_all (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.Nodupkeys) (nd₂ : l₂.Nodupkeys)
    (p : l₁ ~ l₂) : lookupAll a l₁ = lookupAll a l₂ := by
  simp [lookup_all_eq_lookup, nd₁, nd₂, perm_lookup a nd₁ nd₂ p]
#align list.perm_lookup_all List.perm_lookup_all

/-! ### `kreplace` -/


/-- Replaces the first value with key `a` by `b`. -/
def kreplace (a : α) (b : β a) : List (Sigma β) → List (Sigma β) :=
  lookmap fun s => if a = s.1 then some ⟨a, b⟩ else none
#align list.kreplace List.kreplace

theorem kreplace_of_forall_not (a : α) (b : β a) {l : List (Sigma β)}
    (H : ∀ b : β a, Sigma.mk a b ∉ l) : kreplace a b l = l :=
  lookmap_of_forall_not _ <| by
    rintro ⟨a', b'⟩ h; dsimp; split_ifs
    · subst a'
      exact H _ h; · rfl
#align list.kreplace_of_forall_not List.kreplace_of_forall_not

theorem kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : Nodupkeys l)
    (h : Sigma.mk a b ∈ l) : kreplace a b l = l :=
  by
  refine' (lookmap_congr _).trans (lookmap_id' (Option.guard fun s => a = s.1) _ _)
  · rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    · subst a'
      exact ⟨rfl, heq_of_eq <| nd.eq_of_mk_mem h h'⟩
    · rfl
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    dsimp [Option.guard]
    split_ifs
    · exact id
    · rintro ⟨⟩
#align list.kreplace_self List.kreplace_self

theorem keys_kreplace (a : α) (b : β a) : ∀ l : List (Sigma β), (kreplace a b l).keys = l.keys :=
  lookmap_map_eq _ _ <| by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩ <;> dsimp <;> split_ifs <;> simp (config := { contextual := true }) [h]
#align list.keys_kreplace List.keys_kreplace

theorem kreplace_nodupkeys (a : α) (b : β a) {l : List (Sigma β)} :
    (kreplace a b l).Nodupkeys ↔ l.Nodupkeys := by simp [nodupkeys, keys_kreplace]
#align list.kreplace_nodupkeys List.kreplace_nodupkeys

theorem Perm.kreplace {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.Nodupkeys) :
    l₁ ~ l₂ → kreplace a b l₁ ~ kreplace a b l₂ :=
  perm_lookmap _ <| by
    refine' nd.pairwise_ne.imp _
    intro x y h z h₁ w h₂
    split_ifs  at h₁ h₂ <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim
#align list.perm.kreplace List.Perm.kreplace

/-! ### `kerase` -/


/-- Remove the first pair with the key `a`. -/
def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  erasep fun s => a = s.1
#align list.kerase List.kerase

@[simp]
theorem kerase_nil {a} : @kerase _ β _ a [] = [] :=
  rfl
#align list.kerase_nil List.kerase_nil

@[simp]
theorem kerase_cons_eq {a} {s : Sigma β} {l : List (Sigma β)} (h : a = s.1) :
    kerase a (s :: l) = l := by simp [kerase, h]
#align list.kerase_cons_eq List.kerase_cons_eq

@[simp]
theorem kerase_cons_ne {a} {s : Sigma β} {l : List (Sigma β)} (h : a ≠ s.1) :
    kerase a (s :: l) = s :: kerase a l := by simp [kerase, h]
#align list.kerase_cons_ne List.kerase_cons_ne

@[simp]
theorem kerase_of_not_mem_keys {a} {l : List (Sigma β)} (h : a ∉ l.keys) : kerase a l = l := by
  induction' l with _ _ ih <;> [rfl,
    · simp [not_or] at h
      simp [h.1, ih h.2]]
#align list.kerase_of_not_mem_keys List.kerase_of_not_mem_keys

theorem kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l :=
  eraseP_sublist _
#align list.kerase_sublist List.kerase_sublist

theorem kerase_keys_subset (a) (l : List (Sigma β)) : (kerase a l).keys ⊆ l.keys :=
  ((kerase_sublist a l).map _).Subset
#align list.kerase_keys_subset List.kerase_keys_subset

theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} :
    a₁ ∈ (kerase a₂ l).keys → a₁ ∈ l.keys :=
  @kerase_keys_subset _ _ _ _ _ _
#align list.mem_keys_of_mem_keys_kerase List.mem_keys_of_mem_keys_kerase

theorem exists_of_kerase {a : α} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ (b : β a)(l₁ l₂ : List (Sigma β)),
      a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂ :=
  by
  induction l
  case nil => cases h
  case cons hd tl ih =>
    by_cases e : a = hd.1
    · subst e
      exact ⟨hd.2, [], tl, by simp, by cases hd <;> rfl, by simp⟩
    · simp at h
      cases h
      case inl h => exact absurd h e
      case inr h =>
        rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩
        exact
          ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁, by rw [h₂] <;> rfl, by
            simp [e, h₃]⟩
#align list.exists_of_kerase List.exists_of_kerase

@[simp]
theorem mem_keys_kerase_of_ne {a₁ a₂} {l : List (Sigma β)} (h : a₁ ≠ a₂) :
    a₁ ∈ (kerase a₂ l).keys ↔ a₁ ∈ l.keys :=
  (Iff.intro mem_keys_of_mem_keys_kerase) fun p =>
    if q : a₂ ∈ l.keys then
      match l, kerase a₂ l, exists_of_kerase q, p with
      | _, _, ⟨_, _, _, _, rfl, rfl⟩, p => by simpa [keys, h] using p
    else by simp [q, p]
#align list.mem_keys_kerase_of_ne List.mem_keys_kerase_of_ne

theorem keys_kerase {a} {l : List (Sigma β)} : (kerase a l).keys = l.keys.erase a := by
  rw [keys, kerase, ← erasep_map Sigma.fst l, erase_eq_erasep]
#align list.keys_kerase List.keys_kerase

theorem kerase_kerase {a a'} {l : List (Sigma β)} :
    (kerase a' l).kerase a = (kerase a l).kerase a' :=
  by
  by_cases a = a'
  · subst a'
  induction' l with x xs; · rfl
  · by_cases a' = x.1
    · subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases h' : a = x.1
    · subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    · simp [kerase_cons_ne, *]
#align list.kerase_kerase List.kerase_kerase

theorem Nodupkeys.kerase (a : α) : Nodupkeys l → (kerase a l).Nodupkeys :=
  nodupkeys.sublist <| kerase_sublist _ _
#align list.nodupkeys.kerase List.Nodupkeys.kerase

theorem Perm.kerase {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.Nodupkeys) :
    l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ :=
  Perm.erasep _ <| (nodupkeys_iff_pairwise.1 nd).imp <| by rintro x y h rfl <;> exact h
#align list.perm.kerase List.Perm.kerase

@[simp]
theorem not_mem_keys_kerase (a) {l : List (Sigma β)} (nd : l.Nodupkeys) : a ∉ (kerase a l).keys :=
  by
  induction l
  case nil => simp
  case cons hd tl ih =>
    simp at nd
    by_cases h : a = hd.1
    · subst h
      simp [nd.1]
    · simp [h, ih nd.2]
#align list.not_mem_keys_kerase List.not_mem_keys_kerase

@[simp]
theorem lookup_kerase (a) {l : List (Sigma β)} (nd : l.Nodupkeys) : lookup a (kerase a l) = none :=
  lookup_eq_none.mpr (not_mem_keys_kerase a nd)
#align list.lookup_kerase List.lookup_kerase

@[simp]
theorem lookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a ≠ a') :
    lookup a (kerase a' l) = lookup a l := by
  induction l
  case nil => rfl
  case cons hd tl ih =>
    cases' hd with ah bh
    by_cases h₁ : a = ah <;> by_cases h₂ : a' = ah
    · substs h₁ h₂
      cases Ne.irrefl h
    · subst h₁
      simp [h₂]
    · subst h₂
      simp [h]
    · simp [h₁, h₂, ih]
#align list.lookup_kerase_ne List.lookup_kerase_ne

theorem kerase_append_left {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
  | [], _, h => by cases h
  | s :: l₁, l₂, h₁ =>
    if h₂ : a = s.1 then by simp [h₂]
    else by simp at h₁ <;> cases h₁ <;> [exact absurd h₁ h₂, simp [h₂, kerase_append_left h₁]]
#align list.kerase_append_left List.kerase_append_left

theorem kerase_append_right {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
  | [], _, h => rfl
  | _ :: l₁, l₂, h => by simp [not_or] at h <;> simp [h.1, kerase_append_right h.2]
#align list.kerase_append_right List.kerase_append_right

theorem kerase_comm (a₁ a₂) (l : List (Sigma β)) :
    kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  if h : a₁ = a₂ then by simp [h]
  else
    if ha₁ : a₁ ∈ l.keys then
      if ha₂ : a₂ ∈ l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, a₂_in_l₁_app_l₂ =>
          if h' : a₂ ∈ l₁.keys then by
            simp [kerase_append_left h',
              kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
          else by
            simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
              @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (Ne.symm h)]
      else by simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
    else by simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]
#align list.kerase_comm List.kerase_comm

theorem sizeof_kerase {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)] (x : α)
    (xs : List (Sigma β)) : SizeOf.sizeOf (List.kerase x xs) ≤ SizeOf.sizeOf xs :=
  by
  unfold_wf
  induction' xs with y ys
  · simp
  · by_cases x = y.1 <;> simp [*, List.sizeof]
#align list.sizeof_kerase List.sizeof_kerase

/-! ### `kinsert` -/


/-- Insert the pair `⟨a, b⟩` and erase the first pair with the key `a`. -/
def kinsert (a : α) (b : β a) (l : List (Sigma β)) : List (Sigma β) :=
  ⟨a, b⟩ :: kerase a l
#align list.kinsert List.kinsert

@[simp]
theorem kinsert_def {a} {b : β a} {l : List (Sigma β)} : kinsert a b l = ⟨a, b⟩ :: kerase a l :=
  rfl
#align list.kinsert_def List.kinsert_def

theorem mem_keys_kinsert {a a'} {b' : β a'} {l : List (Sigma β)} :
    a ∈ (kinsert a' b' l).keys ↔ a = a' ∨ a ∈ l.keys := by by_cases h : a = a' <;> simp [h]
#align list.mem_keys_kinsert List.mem_keys_kinsert

theorem kinsert_nodupkeys (a) (b : β a) {l : List (Sigma β)} (nd : l.Nodupkeys) :
    (kinsert a b l).Nodupkeys :=
  nodupkeys_cons.mpr ⟨not_mem_keys_kerase a nd, nd.kerase a⟩
#align list.kinsert_nodupkeys List.kinsert_nodupkeys

theorem Perm.kinsert {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.Nodupkeys) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  (p.kerase nd₁).cons _
#align list.perm.kinsert List.Perm.kinsert

theorem lookup_kinsert {a} {b : β a} (l : List (Sigma β)) : lookup a (kinsert a b l) = some b := by
  simp only [kinsert, lookup_cons_eq]
#align list.lookup_kinsert List.lookup_kinsert

theorem lookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a ≠ a') :
    lookup a (kinsert a' b' l) = lookup a l := by simp [h]
#align list.lookup_kinsert_ne List.lookup_kinsert_ne

/-! ### `kextract` -/


/-- Finds the first entry with a given key `a` and returns its value (as an `option` because there
might be no entry with key `a`) alongside with the rest of the entries. -/
def kextract (a : α) : List (Sigma β) → Option (β a) × List (Sigma β)
  | [] => (none, [])
  | s :: l =>
    if h : s.1 = a then (some (Eq.recOn h s.2), l)
    else
      let (b', l') := kextract l
      (b', s :: l')
#align list.kextract List.kextract

@[simp]
theorem kextract_eq_lookup_kerase (a : α) :
    ∀ l : List (Sigma β), kextract a l = (lookup a l, kerase a l)
  | [] => rfl
  | ⟨a', b⟩ :: l => by
    simp [kextract]; dsimp; split_ifs
    · subst a'
      simp [kerase]
    · simp [kextract, Ne.symm h, kextract_eq_lookup_kerase l, kerase]
#align list.kextract_eq_lookup_kerase List.kextract_eq_lookup_kerase

/-! ### `dedupkeys` -/


/-- Remove entries with duplicate keys from `l : list (sigma β)`. -/
def dedupkeys : List (Sigma β) → List (Sigma β) :=
  List.foldr (fun x => kinsert x.1 x.2) []
#align list.dedupkeys List.dedupkeys

theorem dedupkeys_cons {x : Sigma β} (l : List (Sigma β)) :
    dedupkeys (x :: l) = kinsert x.1 x.2 (dedupkeys l) :=
  rfl
#align list.dedupkeys_cons List.dedupkeys_cons

theorem nodupkeys_dedupkeys (l : List (Sigma β)) : Nodupkeys (dedupkeys l) :=
  by
  dsimp [dedupkeys]
  generalize hl : nil = l'
  have : nodupkeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction' l with x xs
  · apply this
  · cases x
    simp [dedupkeys]
    constructor
    · simp [keys_kerase]
      apply l_ih.not_mem_erase
    · exact l_ih.kerase _
#align list.nodupkeys_dedupkeys List.nodupkeys_dedupkeys

theorem lookup_dedupkeys (a : α) (l : List (Sigma β)) : lookup a (dedupkeys l) = lookup a l :=
  by
  induction l; rfl
  cases' l_hd with a' b
  by_cases a = a'
  · subst a'
    rw [dedupkeys_cons, lookup_kinsert, lookup_cons_eq]
  · rw [dedupkeys_cons, lookup_kinsert_ne h, l_ih, lookup_cons_ne]
    exact h
#align list.lookup_dedupkeys List.lookup_dedupkeys

theorem sizeof_dedupkeys {α} {β : α → Type _} [DecidableEq α] [SizeOf (Sigma β)]
    (xs : List (Sigma β)) : SizeOf.sizeOf (List.dedupkeys xs) ≤ SizeOf.sizeOf xs :=
  by
  unfold_wf
  induction' xs with x xs
  · simp [List.dedupkeys]
  · simp only [dedupkeys_cons, List.sizeof, kinsert_def, add_le_add_iff_left, Sigma.eta]
    trans
    apply sizeof_kerase
    assumption
#align list.sizeof_dedupkeys List.sizeof_dedupkeys

/-! ### `kunion` -/


/-- `kunion l₁ l₂` is the append to l₁ of l₂ after, for each key in l₁, the
first matching pair in l₂ is erased. -/
def kunion : List (Sigma β) → List (Sigma β) → List (Sigma β)
  | [], l₂ => l₂
  | s :: l₁, l₂ => s :: kunion l₁ (kerase s.1 l₂)
#align list.kunion List.kunion

@[simp]
theorem nil_kunion {l : List (Sigma β)} : kunion [] l = l :=
  rfl
#align list.nil_kunion List.nil_kunion

@[simp]
theorem kunion_nil : ∀ {l : List (Sigma β)}, kunion l [] = l
  | [] => rfl
  | _ :: l => by rw [kunion, kerase_nil, kunion_nil]
#align list.kunion_nil List.kunion_nil

@[simp]
theorem kunion_cons {s} {l₁ l₂ : List (Sigma β)} :
    kunion (s :: l₁) l₂ = s :: kunion l₁ (kerase s.1 l₂) :=
  rfl
#align list.kunion_cons List.kunion_cons

@[simp]
theorem mem_keys_kunion {a} {l₁ l₂ : List (Sigma β)} :
    a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys :=
  by
  induction l₁ generalizing l₂
  case nil => simp
  case cons s l₁ ih => by_cases h : a = s.1 <;> [simp [h], simp [h, ih]]
#align list.mem_keys_kunion List.mem_keys_kunion

@[simp]
theorem kunion_kerase {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
  | [], _ => rfl
  | s :: _, l => by by_cases h : a = s.1 <;> simp [h, kerase_comm a s.1 l, kunion_kerase]
#align list.kunion_kerase List.kunion_kerase

theorem Nodupkeys.kunion (nd₁ : l₁.Nodupkeys) (nd₂ : l₂.Nodupkeys) : (kunion l₁ l₂).Nodupkeys :=
  by
  induction l₁ generalizing l₂
  case nil => simp only [nil_kunion, nd₂]
  case cons s l₁ ih =>
    simp at nd₁
    simp [not_or, nd₁.1, nd₂, ih nd₁.2 (nd₂.kerase s.1)]
#align list.nodupkeys.kunion List.Nodupkeys.kunion

theorem Perm.kunion_right {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) (l) : kunion l₁ l ~ kunion l₂ l :=
  by
  induction p generalizing l
  case nil => rfl
  case cons hd tl₁ tl₂ p ih => simp [ih (kerase hd.1 l), perm.cons]
  case swap s₁ s₂ l => simp [kerase_comm, perm.swap]
  case trans l₁ l₂ l₃ p₁₂ p₂₃ ih₁₂ ih₂₃ => exact perm.trans (ih₁₂ l) (ih₂₃ l)
#align list.perm.kunion_right List.Perm.kunion_right

theorem Perm.kunion_left :
    ∀ (l) {l₁ l₂ : List (Sigma β)}, l₁.Nodupkeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂
  | [], _, _, _, p => p
  | s :: l, l₁, l₂, nd₁, p => by simp [((p.kerase nd₁).kunion_left l <| nd₁.kerase s.1).cons s]
#align list.perm.kunion_left List.Perm.kunion_left

theorem Perm.kunion {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.Nodupkeys) (p₁₂ : l₁ ~ l₂)
    (p₃₄ : l₃ ~ l₄) : kunion l₁ l₃ ~ kunion l₂ l₄ :=
  (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)
#align list.perm.kunion List.Perm.kunion

@[simp]
theorem lookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a ∈ l₁.keys) :
    lookup a (kunion l₁ l₂) = lookup a l₁ :=
  by
  induction' l₁ with s _ ih generalizing l₂ <;> simp at h <;> cases h <;> cases' s with a'
  · subst h
    simp
  · rw [kunion_cons]
    by_cases h' : a = a'
    · subst h'
      simp
    · simp [h', ih h]
#align list.lookup_kunion_left List.lookup_kunion_left

@[simp]
theorem lookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) :
    lookup a (kunion l₁ l₂) = lookup a l₂ :=
  by
  induction l₁ generalizing l₂
  case nil => simp
  case cons _ _ ih => simp [not_or] at h; simp [h.1, ih h.2]
#align list.lookup_kunion_right List.lookup_kunion_right

@[simp]
theorem mem_lookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    b ∈ lookup a (kunion l₁ l₂) ↔ b ∈ lookup a l₁ ∨ a ∉ l₁.keys ∧ b ∈ lookup a l₂ :=
  by
  induction l₁ generalizing l₂
  case nil => simp
  case cons s _ ih =>
    cases' s with a'
    by_cases h₁ : a = a'
    · subst h₁
      simp
    · let h₂ := @ih (kerase a' l₂)
      simp [h₁] at h₂
      simp [h₁, h₂]
#align list.mem_lookup_kunion List.mem_lookup_kunion

theorem mem_lookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)}
    (h₁ : b ∈ lookup a (kunion l₁ l₃)) (h₂ : a ∉ keys l₂) :
    b ∈ lookup a (kunion (kunion l₁ l₂) l₃) :=
  match mem_lookup_kunion.mp h₁ with
  | Or.inl h => mem_lookup_kunion.mpr (Or.inl (mem_lookup_kunion.mpr (Or.inl h)))
  | Or.inr h => mem_lookup_kunion.mpr <| Or.inr ⟨mt mem_keys_kunion.mp (not_or.mpr ⟨h.1, h₂⟩), h.2⟩
#align list.mem_lookup_kunion_middle List.mem_lookup_kunion_middle

end List

