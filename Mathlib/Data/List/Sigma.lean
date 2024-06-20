/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Sean Leather
-/
import Mathlib.Data.List.Range
import Mathlib.Data.List.Perm

#align_import data.list.sigma from "leanprover-community/mathlib"@"f808feb6c18afddb25e66a71d317643cf7fb5fbb"

/-!
# Utilities for lists of sigmas

This file includes several ways of interacting with `List (Sigma β)`, treated as a key-value store.

If `α : Type*` and `β : α → Type*`, then we regard `s : Sigma β` as having key `s.1 : α` and value
`s.2 : β s.1`. Hence, `List (Sigma β)` behaves like a key-value store.

## Main Definitions

- `List.keys` extracts the list of keys.
- `List.NodupKeys` determines if the store has duplicate keys.
- `List.lookup`/`lookup_all` accesses the value(s) of a particular key.
- `List.kreplace` replaces the first value with a given key by a given value.
- `List.kerase` removes a value.
- `List.kinsert` inserts a value.
- `List.kunion` computes the union of two stores.
- `List.kextract` returns a value with a given key and the rest of the values.
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
  let ⟨⟨_, b'⟩, m, e⟩ := exists_of_mem_map h
  Eq.recOn e (Exists.intro b' m)
#align list.exists_of_mem_keys List.exists_of_mem_keys

theorem mem_keys {a} {l : List (Sigma β)} : a ∈ l.keys ↔ ∃ b : β a, Sigma.mk a b ∈ l :=
  ⟨exists_of_mem_keys, fun ⟨_, h⟩ => mem_keys_of_mem h⟩
#align list.mem_keys List.mem_keys

theorem not_mem_keys {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ b : β a, Sigma.mk a b ∉ l :=
  (not_congr mem_keys).trans not_exists
#align list.not_mem_keys List.not_mem_keys

theorem not_eq_key {a} {l : List (Sigma β)} : a ∉ l.keys ↔ ∀ s : Sigma β, s ∈ l → a ≠ s.1 :=
  Iff.intro (fun h₁ s h₂ e => absurd (mem_keys_of_mem h₂) (by rwa [e] at h₁)) fun f h₁ =>
    let ⟨b, h₂⟩ := exists_of_mem_keys h₁
    f _ h₂ rfl
#align list.not_eq_key List.not_eq_key

/-! ### `NodupKeys` -/


/-- Determines whether the store uses a key several times. -/
def NodupKeys (l : List (Sigma β)) : Prop :=
  l.keys.Nodup
#align list.nodupkeys List.NodupKeys

theorem nodupKeys_iff_pairwise {l} : NodupKeys l ↔ Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  pairwise_map
#align list.nodupkeys_iff_pairwise List.nodupKeys_iff_pairwise

theorem NodupKeys.pairwise_ne {l} (h : NodupKeys l) :
    Pairwise (fun s s' : Sigma β => s.1 ≠ s'.1) l :=
  nodupKeys_iff_pairwise.1 h
#align list.nodupkeys.pairwise_ne List.NodupKeys.pairwise_ne

@[simp]
theorem nodupKeys_nil : @NodupKeys α β [] :=
  Pairwise.nil
#align list.nodupkeys_nil List.nodupKeys_nil

@[simp]
theorem nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} :
    NodupKeys (s :: l) ↔ s.1 ∉ l.keys ∧ NodupKeys l := by simp [keys, NodupKeys]
#align list.nodupkeys_cons List.nodupKeys_cons

theorem not_mem_keys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    s.1 ∉ l.keys :=
  (nodupKeys_cons.1 h).1
#align list.not_mem_keys_of_nodupkeys_cons List.not_mem_keys_of_nodupKeys_cons

theorem nodupKeys_of_nodupKeys_cons {s : Sigma β} {l : List (Sigma β)} (h : NodupKeys (s :: l)) :
    NodupKeys l :=
  (nodupKeys_cons.1 h).2
#align list.nodupkeys_of_nodupkeys_cons List.nodupKeys_of_nodupKeys_cons

theorem NodupKeys.eq_of_fst_eq {l : List (Sigma β)} (nd : NodupKeys l) {s s' : Sigma β} (h : s ∈ l)
    (h' : s' ∈ l) : s.1 = s'.1 → s = s' :=
  @Pairwise.forall_of_forall _ (fun s s' : Sigma β => s.1 = s'.1 → s = s') _
    (fun _ _ H h => (H h.symm).symm) (fun _ _ _ => rfl)
    ((nodupKeys_iff_pairwise.1 nd).imp fun h h' => (h h').elim) _ h _ h'
#align list.nodupkeys.eq_of_fst_eq List.NodupKeys.eq_of_fst_eq

theorem NodupKeys.eq_of_mk_mem {a : α} {b b' : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b ∈ l) (h' : Sigma.mk a b' ∈ l) : b = b' := by
  cases nd.eq_of_fst_eq h h' rfl; rfl
#align list.nodupkeys.eq_of_mk_mem List.NodupKeys.eq_of_mk_mem

theorem nodupKeys_singleton (s : Sigma β) : NodupKeys [s] :=
  nodup_singleton _
#align list.nodupkeys_singleton List.nodupKeys_singleton

theorem NodupKeys.sublist {l₁ l₂ : List (Sigma β)} (h : l₁ <+ l₂) : NodupKeys l₂ → NodupKeys l₁ :=
  Nodup.sublist <| h.map _
#align list.nodupkeys.sublist List.NodupKeys.sublist

protected theorem NodupKeys.nodup {l : List (Sigma β)} : NodupKeys l → Nodup l :=
  Nodup.of_map _
#align list.nodupkeys.nodup List.NodupKeys.nodup

theorem perm_nodupKeys {l₁ l₂ : List (Sigma β)} (h : l₁ ~ l₂) : NodupKeys l₁ ↔ NodupKeys l₂ :=
  (h.map _).nodup_iff
#align list.perm_nodupkeys List.perm_nodupKeys

theorem nodupKeys_join {L : List (List (Sigma β))} :
    NodupKeys (join L) ↔ (∀ l ∈ L, NodupKeys l) ∧ Pairwise Disjoint (L.map keys) := by
  rw [nodupKeys_iff_pairwise, pairwise_join, pairwise_map]
  refine and_congr (forall₂_congr fun l _ => by simp [nodupKeys_iff_pairwise]) ?_
  apply iff_of_eq; congr with (l₁ l₂)
  simp [keys, disjoint_iff_ne]
#align list.nodupkeys_join List.nodupKeys_join

theorem nodup_enum_map_fst (l : List α) : (l.enum.map Prod.fst).Nodup := by simp [List.nodup_range]
#align list.nodup_enum_map_fst List.nodup_enum_map_fst

theorem mem_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.Nodup) (nd₁ : l₁.Nodup)
    (h : ∀ x, x ∈ l₀ ↔ x ∈ l₁) : l₀ ~ l₁ :=
  (perm_ext_iff_of_nodup nd₀ nd₁).2 h
#align list.mem_ext List.mem_ext

variable [DecidableEq α]

/-! ### `dlookup` -/


-- Porting note: renaming to `dlookup` since `lookup` already exists
/-- `dlookup a l` is the first value in `l` corresponding to the key `a`,
  or `none` if no such element exists. -/
def dlookup (a : α) : List (Sigma β) → Option (β a)
  | [] => none
  | ⟨a', b⟩ :: l => if h : a' = a then some (Eq.recOn h b) else dlookup a l
#align list.lookup List.dlookup

@[simp]
theorem dlookup_nil (a : α) : dlookup a [] = @none (β a) :=
  rfl
#align list.lookup_nil List.dlookup_nil

@[simp]
theorem dlookup_cons_eq (l) (a : α) (b : β a) : dlookup a (⟨a, b⟩ :: l) = some b :=
  dif_pos rfl
#align list.lookup_cons_eq List.dlookup_cons_eq

@[simp]
theorem dlookup_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → dlookup a (s :: l) = dlookup a l
  | ⟨_, _⟩, h => dif_neg h.symm
#align list.lookup_cons_ne List.dlookup_cons_ne

theorem dlookup_isSome {a : α} : ∀ {l : List (Sigma β)}, (dlookup a l).isSome ↔ a ∈ l.keys
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simp [h, dlookup_isSome]
#align list.lookup_is_some List.dlookup_isSome

theorem dlookup_eq_none {a : α} {l : List (Sigma β)} : dlookup a l = none ↔ a ∉ l.keys := by
  simp [← dlookup_isSome, Option.isNone_iff_eq_none]
#align list.lookup_eq_none List.dlookup_eq_none

theorem of_mem_dlookup {a : α} {b : β a} :
    ∀ {l : List (Sigma β)}, b ∈ dlookup a l → Sigma.mk a b ∈ l
  | ⟨a', b'⟩ :: l, H => by
    by_cases h : a = a'
    · subst a'
      simp? at H says simp only [dlookup_cons_eq, Option.mem_def, Option.some.injEq] at H
      simp [H]
    · simp only [ne_eq, h, not_false_iff, dlookup_cons_ne] at H
      simp [of_mem_dlookup H]
#align list.of_mem_lookup List.of_mem_dlookup

theorem mem_dlookup {a} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) (h : Sigma.mk a b ∈ l) :
    b ∈ dlookup a l := by
  cases' Option.isSome_iff_exists.mp (dlookup_isSome.mpr (mem_keys_of_mem h)) with b' h'
  cases nd.eq_of_mk_mem h (of_mem_dlookup h')
  exact h'
#align list.mem_lookup List.mem_dlookup

theorem map_dlookup_eq_find (a : α) :
    ∀ l : List (Sigma β), (dlookup a l).map (Sigma.mk a) = find? (fun s => a = s.1) l
  | [] => rfl
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp
    · simpa [h] using map_dlookup_eq_find a l
#align list.map_lookup_eq_find List.map_dlookup_eq_find

theorem mem_dlookup_iff {a : α} {b : β a} {l : List (Sigma β)} (nd : l.NodupKeys) :
    b ∈ dlookup a l ↔ Sigma.mk a b ∈ l :=
  ⟨of_mem_dlookup, mem_dlookup nd⟩
#align list.mem_lookup_iff List.mem_dlookup_iff

theorem perm_dlookup (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (p : l₁ ~ l₂) : dlookup a l₁ = dlookup a l₂ := by
  ext b; simp only [mem_dlookup_iff nd₁, mem_dlookup_iff nd₂]; exact p.mem_iff
#align list.perm_lookup List.perm_dlookup

theorem lookup_ext {l₀ l₁ : List (Sigma β)} (nd₀ : l₀.NodupKeys) (nd₁ : l₁.NodupKeys)
    (h : ∀ x y, y ∈ l₀.dlookup x ↔ y ∈ l₁.dlookup x) : l₀ ~ l₁ :=
  mem_ext nd₀.nodup nd₁.nodup fun ⟨a, b⟩ => by
    rw [← mem_dlookup_iff, ← mem_dlookup_iff, h] <;> assumption
#align list.lookup_ext List.lookup_ext

/-! ### `lookupAll` -/


/-- `lookup_all a l` is the list of all values in `l` corresponding to the key `a`. -/
def lookupAll (a : α) : List (Sigma β) → List (β a)
  | [] => []
  | ⟨a', b⟩ :: l => if h : a' = a then Eq.recOn h b :: lookupAll a l else lookupAll a l
#align list.lookup_all List.lookupAll

@[simp]
theorem lookupAll_nil (a : α) : lookupAll a [] = @nil (β a) :=
  rfl
#align list.lookup_all_nil List.lookupAll_nil

@[simp]
theorem lookupAll_cons_eq (l) (a : α) (b : β a) : lookupAll a (⟨a, b⟩ :: l) = b :: lookupAll a l :=
  dif_pos rfl
#align list.lookup_all_cons_eq List.lookupAll_cons_eq

@[simp]
theorem lookupAll_cons_ne (l) {a} : ∀ s : Sigma β, a ≠ s.1 → lookupAll a (s :: l) = lookupAll a l
  | ⟨_, _⟩, h => dif_neg h.symm
#align list.lookup_all_cons_ne List.lookupAll_cons_ne

theorem lookupAll_eq_nil {a : α} :
    ∀ {l : List (Sigma β)}, lookupAll a l = [] ↔ ∀ b : β a, Sigma.mk a b ∉ l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst a'
      simp only [lookupAll_cons_eq, mem_cons, Sigma.mk.inj_iff, heq_eq_eq, true_and, not_or,
        false_iff, not_forall, not_and, not_not]
      use b
      simp
    · simp [h, lookupAll_eq_nil]
#align list.lookup_all_eq_nil List.lookupAll_eq_nil

theorem head?_lookupAll (a : α) : ∀ l : List (Sigma β), head? (lookupAll a l) = dlookup a l
  | [] => by simp
  | ⟨a', b⟩ :: l => by
    by_cases h : a = a'
    · subst h; simp
    · rw [lookupAll_cons_ne, dlookup_cons_ne, head?_lookupAll a l] <;> assumption
#align list.head_lookup_all List.head?_lookupAll

theorem mem_lookupAll {a : α} {b : β a} :
    ∀ {l : List (Sigma β)}, b ∈ lookupAll a l ↔ Sigma.mk a b ∈ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp [*, mem_lookupAll]
    · simp [*, mem_lookupAll]
#align list.mem_lookup_all List.mem_lookupAll

theorem lookupAll_sublist (a : α) : ∀ l : List (Sigma β), (lookupAll a l).map (Sigma.mk a) <+ l
  | [] => by simp
  | ⟨a', b'⟩ :: l => by
    by_cases h : a = a'
    · subst h
      simp only [ne_eq, not_true, lookupAll_cons_eq, List.map]
      exact (lookupAll_sublist a l).cons₂ _
    · simp only [ne_eq, h, not_false_iff, lookupAll_cons_ne]
      exact (lookupAll_sublist a l).cons _
#align list.lookup_all_sublist List.lookupAll_sublist

theorem lookupAll_length_le_one (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    length (lookupAll a l) ≤ 1 := by
  have := Nodup.sublist ((lookupAll_sublist a l).map _) h
  rw [map_map] at this
  rwa [← nodup_replicate, ← map_const]
#align list.lookup_all_length_le_one List.lookupAll_length_le_one

theorem lookupAll_eq_dlookup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) :
    lookupAll a l = (dlookup a l).toList := by
  rw [← head?_lookupAll]
  have h1 := lookupAll_length_le_one a h; revert h1
  rcases lookupAll a l with (_ | ⟨b, _ | ⟨c, l⟩⟩) <;> intro h1 <;> try rfl
  exact absurd h1 (by simp)
#align list.lookup_all_eq_lookup List.lookupAll_eq_dlookup

theorem lookupAll_nodup (a : α) {l : List (Sigma β)} (h : l.NodupKeys) : (lookupAll a l).Nodup := by
  (rw [lookupAll_eq_dlookup a h]; apply Option.toList_nodup)
#align list.lookup_all_nodup List.lookupAll_nodup

theorem perm_lookupAll (a : α) {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys)
    (p : l₁ ~ l₂) : lookupAll a l₁ = lookupAll a l₂ := by
  simp [lookupAll_eq_dlookup, nd₁, nd₂, perm_dlookup a nd₁ nd₂ p]
#align list.perm_lookup_all List.perm_lookupAll

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
      exact H _ h
    · rfl
#align list.kreplace_of_forall_not List.kreplace_of_forall_not

theorem kreplace_self {a : α} {b : β a} {l : List (Sigma β)} (nd : NodupKeys l)
    (h : Sigma.mk a b ∈ l) : kreplace a b l = l := by
  refine (lookmap_congr ?_).trans (lookmap_id' (Option.guard fun (s : Sigma β) => a = s.1) ?_ _)
  · rintro ⟨a', b'⟩ h'
    dsimp [Option.guard]
    split_ifs
    · subst a'
      simp [nd.eq_of_mk_mem h h']
    · rfl
  · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
    dsimp [Option.guard]
    split_ifs
    · simp
    · rintro ⟨⟩
#align list.kreplace_self List.kreplace_self

theorem keys_kreplace (a : α) (b : β a) : ∀ l : List (Sigma β), (kreplace a b l).keys = l.keys :=
  lookmap_map_eq _ _ <| by
    rintro ⟨a₁, b₂⟩ ⟨a₂, b₂⟩
    dsimp
    split_ifs with h <;> simp (config := { contextual := true }) [h]
#align list.keys_kreplace List.keys_kreplace

theorem kreplace_nodupKeys (a : α) (b : β a) {l : List (Sigma β)} :
    (kreplace a b l).NodupKeys ↔ l.NodupKeys := by simp [NodupKeys, keys_kreplace]
#align list.kreplace_nodupkeys List.kreplace_nodupKeys

theorem Perm.kreplace {a : α} {b : β a} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ → kreplace a b l₁ ~ kreplace a b l₂ :=
  perm_lookmap _ <| by
    refine nd.pairwise_ne.imp ?_
    intro x y h z h₁ w h₂
    split_ifs at h₁ h₂ with h_2 h_1 <;> cases h₁ <;> cases h₂
    exact (h (h_2.symm.trans h_1)).elim
#align list.perm.kreplace List.Perm.kreplace

/-! ### `kerase` -/


/-- Remove the first pair with the key `a`. -/
def kerase (a : α) : List (Sigma β) → List (Sigma β) :=
  eraseP fun s => a = s.1
#align list.kerase List.kerase

-- Porting note (#10618): removing @[simp], `simp` can prove it
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
  induction' l with _ _ ih <;> [rfl; (simp [not_or] at h; simp [h.1, ih h.2])]
#align list.kerase_of_not_mem_keys List.kerase_of_not_mem_keys

theorem kerase_sublist (a : α) (l : List (Sigma β)) : kerase a l <+ l :=
  eraseP_sublist _
#align list.kerase_sublist List.kerase_sublist

theorem kerase_keys_subset (a) (l : List (Sigma β)) : (kerase a l).keys ⊆ l.keys :=
  ((kerase_sublist a l).map _).subset
#align list.kerase_keys_subset List.kerase_keys_subset

theorem mem_keys_of_mem_keys_kerase {a₁ a₂} {l : List (Sigma β)} :
    a₁ ∈ (kerase a₂ l).keys → a₁ ∈ l.keys :=
  @kerase_keys_subset _ _ _ _ _ _
#align list.mem_keys_of_mem_keys_kerase List.mem_keys_of_mem_keys_kerase

theorem exists_of_kerase {a : α} {l : List (Sigma β)} (h : a ∈ l.keys) :
    ∃ (b : β a) (l₁ l₂ : List (Sigma β)),
      a ∉ l₁.keys ∧ l = l₁ ++ ⟨a, b⟩ :: l₂ ∧ kerase a l = l₁ ++ l₂ := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    by_cases e : a = hd.1
    · subst e
      exact ⟨hd.2, [], tl, by simp, by cases hd; rfl, by simp⟩
    · simp only [keys_cons, mem_cons] at h
      cases' h with h h
      · exact absurd h e
      rcases ih h with ⟨b, tl₁, tl₂, h₁, h₂, h₃⟩
      exact ⟨b, hd :: tl₁, tl₂, not_mem_cons_of_ne_of_not_mem e h₁, by (rw [h₂]; rfl), by
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
  rw [keys, kerase, erase_eq_eraseP, eraseP_map, Function.comp]
  simp only [beq_eq_decide]
  congr
  funext
  simp
#align list.keys_kerase List.keys_kerase

theorem kerase_kerase {a a'} {l : List (Sigma β)} :
    (kerase a' l).kerase a = (kerase a l).kerase a' := by
  by_cases h : a = a'
  · subst a'; rfl
  induction' l with x xs
  · rfl
  · by_cases a' = x.1
    · subst a'
      simp [kerase_cons_ne h, kerase_cons_eq rfl]
    by_cases h' : a = x.1
    · subst a
      simp [kerase_cons_eq rfl, kerase_cons_ne (Ne.symm h)]
    · simp [kerase_cons_ne, *]
#align list.kerase_kerase List.kerase_kerase

theorem NodupKeys.kerase (a : α) : NodupKeys l → (kerase a l).NodupKeys :=
  NodupKeys.sublist <| kerase_sublist _ _
#align list.nodupkeys.kerase List.NodupKeys.kerase

theorem Perm.kerase {a : α} {l₁ l₂ : List (Sigma β)} (nd : l₁.NodupKeys) :
    l₁ ~ l₂ → kerase a l₁ ~ kerase a l₂ := by
  apply Perm.eraseP
  apply (nodupKeys_iff_pairwise.1 nd).imp
  intros; simp_all
#align list.perm.kerase List.Perm.kerase

@[simp]
theorem not_mem_keys_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    a ∉ (kerase a l).keys := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp? at nd says simp only [nodupKeys_cons] at nd
    by_cases h : a = hd.1
    · subst h
      simp [nd.1]
    · simp [h, ih nd.2]
#align list.not_mem_keys_kerase List.not_mem_keys_kerase

@[simp]
theorem dlookup_kerase (a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    dlookup a (kerase a l) = none :=
  dlookup_eq_none.mpr (not_mem_keys_kerase a nd)
#align list.lookup_kerase List.dlookup_kerase

@[simp]
theorem dlookup_kerase_ne {a a'} {l : List (Sigma β)} (h : a ≠ a') :
    dlookup a (kerase a' l) = dlookup a l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases' hd with ah bh
    by_cases h₁ : a = ah <;> by_cases h₂ : a' = ah
    · substs h₁ h₂
      cases Ne.irrefl h
    · subst h₁
      simp [h₂]
    · subst h₂
      simp [h]
    · simp [h₁, h₂, ih]
#align list.lookup_kerase_ne List.dlookup_kerase_ne

theorem kerase_append_left {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∈ l₁.keys → kerase a (l₁ ++ l₂) = kerase a l₁ ++ l₂
  | [], _, h => by cases h
  | s :: l₁, l₂, h₁ => by
    if h₂ : a = s.1 then simp [h₂]
    else simp at h₁; cases' h₁ with h₁ h₁ <;> [exact absurd h₁ h₂; simp [h₂, kerase_append_left h₁]]
#align list.kerase_append_left List.kerase_append_left

theorem kerase_append_right {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, a ∉ l₁.keys → kerase a (l₁ ++ l₂) = l₁ ++ kerase a l₂
  | [], _, _ => rfl
  | _ :: l₁, l₂, h => by
    simp only [keys_cons, mem_cons, not_or] at h
    simp [h.1, kerase_append_right h.2]
#align list.kerase_append_right List.kerase_append_right

theorem kerase_comm (a₁ a₂) (l : List (Sigma β)) :
    kerase a₂ (kerase a₁ l) = kerase a₁ (kerase a₂ l) :=
  if h : a₁ = a₂ then by simp [h]
  else
    if ha₁ : a₁ ∈ l.keys then
      if ha₂ : a₂ ∈ l.keys then
        match l, kerase a₁ l, exists_of_kerase ha₁, ha₂ with
        | _, _, ⟨b₁, l₁, l₂, a₁_nin_l₁, rfl, rfl⟩, _ =>
          if h' : a₂ ∈ l₁.keys then by
            simp [kerase_append_left h',
              kerase_append_right (mt (mem_keys_kerase_of_ne h).mp a₁_nin_l₁)]
          else by
            simp [kerase_append_right h', kerase_append_right a₁_nin_l₁,
              @kerase_cons_ne _ _ _ a₂ ⟨a₁, b₁⟩ _ (Ne.symm h)]
      else by simp [ha₂, mt mem_keys_of_mem_keys_kerase ha₂]
    else by simp [ha₁, mt mem_keys_of_mem_keys_kerase ha₁]
#align list.kerase_comm List.kerase_comm

theorem sizeOf_kerase [DecidableEq α] [SizeOf (Sigma β)] (x : α)
    (xs : List (Sigma β)) : SizeOf.sizeOf (List.kerase x xs) ≤ SizeOf.sizeOf xs := by
  simp only [SizeOf.sizeOf, _sizeOf_1]
  induction' xs with y ys
  · simp
  · by_cases x = y.1 <;> simp [*]
#align list.sizeof_kerase List.sizeOf_kerase

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

theorem kinsert_nodupKeys (a) (b : β a) {l : List (Sigma β)} (nd : l.NodupKeys) :
    (kinsert a b l).NodupKeys :=
  nodupKeys_cons.mpr ⟨not_mem_keys_kerase a nd, nd.kerase a⟩
#align list.kinsert_nodupkeys List.kinsert_nodupKeys

theorem Perm.kinsert {a} {b : β a} {l₁ l₂ : List (Sigma β)} (nd₁ : l₁.NodupKeys) (p : l₁ ~ l₂) :
    kinsert a b l₁ ~ kinsert a b l₂ :=
  (p.kerase nd₁).cons _
#align list.perm.kinsert List.Perm.kinsert

theorem dlookup_kinsert {a} {b : β a} (l : List (Sigma β)) :
    dlookup a (kinsert a b l) = some b := by
  simp only [kinsert, dlookup_cons_eq]
#align list.lookup_kinsert List.dlookup_kinsert

theorem dlookup_kinsert_ne {a a'} {b' : β a'} {l : List (Sigma β)} (h : a ≠ a') :
    dlookup a (kinsert a' b' l) = dlookup a l := by simp [h]
#align list.lookup_kinsert_ne List.dlookup_kinsert_ne

/-! ### `kextract` -/


/-- Finds the first entry with a given key `a` and returns its value (as an `Option` because there
might be no entry with key `a`) alongside with the rest of the entries. -/
def kextract (a : α) : List (Sigma β) → Option (β a) × List (Sigma β)
  | [] => (none, [])
  | s :: l =>
    if h : s.1 = a then (some (Eq.recOn h s.2), l)
    else
      let (b', l') := kextract a l
      (b', s :: l')
#align list.kextract List.kextract

@[simp]
theorem kextract_eq_dlookup_kerase (a : α) :
    ∀ l : List (Sigma β), kextract a l = (dlookup a l, kerase a l)
  | [] => rfl
  | ⟨a', b⟩ :: l => by
    simp only [kextract]; dsimp; split_ifs with h
    · subst a'
      simp [kerase]
    · simp [kextract, Ne.symm h, kextract_eq_dlookup_kerase a l, kerase]
#align list.kextract_eq_lookup_kerase List.kextract_eq_dlookup_kerase

/-! ### `dedupKeys` -/


/-- Remove entries with duplicate keys from `l : List (Sigma β)`. -/
def dedupKeys : List (Sigma β) → List (Sigma β) :=
  List.foldr (fun x => kinsert x.1 x.2) []
#align list.dedupkeys List.dedupKeys

theorem dedupKeys_cons {x : Sigma β} (l : List (Sigma β)) :
    dedupKeys (x :: l) = kinsert x.1 x.2 (dedupKeys l) :=
  rfl
#align list.dedupkeys_cons List.dedupKeys_cons


theorem nodupKeys_dedupKeys (l : List (Sigma β)) : NodupKeys (dedupKeys l) := by
  dsimp [dedupKeys]
  generalize hl : nil = l'
  have : NodupKeys l' := by
    rw [← hl]
    apply nodup_nil
  clear hl
  induction' l with x xs l_ih
  · apply this
  · cases x
    simp only [foldr_cons, kinsert_def, nodupKeys_cons, ne_eq, not_true]
    constructor
    · simp only [keys_kerase]
      apply l_ih.not_mem_erase
    · exact l_ih.kerase _
#align list.nodupkeys_dedupkeys List.nodupKeys_dedupKeys

theorem dlookup_dedupKeys (a : α) (l : List (Sigma β)) : dlookup a (dedupKeys l) = dlookup a l := by
  induction' l with l_hd _ l_ih
  · rfl
  cases' l_hd with a' b
  by_cases h : a = a'
  · subst a'
    rw [dedupKeys_cons, dlookup_kinsert, dlookup_cons_eq]
  · rw [dedupKeys_cons, dlookup_kinsert_ne h, l_ih, dlookup_cons_ne]
    exact h
#align list.lookup_dedupkeys List.dlookup_dedupKeys

theorem sizeOf_dedupKeys [DecidableEq α] [SizeOf (Sigma β)]
    (xs : List (Sigma β)) : SizeOf.sizeOf (dedupKeys xs) ≤ SizeOf.sizeOf xs := by
  simp only [SizeOf.sizeOf, _sizeOf_1]
  induction' xs with x xs
  · simp [dedupKeys]
  · simp only [dedupKeys_cons, kinsert_def, Nat.add_le_add_iff_left, Sigma.eta]
    trans
    · apply sizeOf_kerase
    · assumption
#align list.sizeof_dedupkeys List.sizeOf_dedupKeys

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
    a ∈ (kunion l₁ l₂).keys ↔ a ∈ l₁.keys ∨ a ∈ l₂.keys := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s l₁ ih => by_cases h : a = s.1 <;> [simp [h]; simp [h, ih]]
#align list.mem_keys_kunion List.mem_keys_kunion

@[simp]
theorem kunion_kerase {a} :
    ∀ {l₁ l₂ : List (Sigma β)}, kunion (kerase a l₁) (kerase a l₂) = kerase a (kunion l₁ l₂)
  | [], _ => rfl
  | s :: _, l => by by_cases h : a = s.1 <;> simp [h, kerase_comm a s.1 l, kunion_kerase]
#align list.kunion_kerase List.kunion_kerase

theorem NodupKeys.kunion (nd₁ : l₁.NodupKeys) (nd₂ : l₂.NodupKeys) : (kunion l₁ l₂).NodupKeys := by
  induction l₁ generalizing l₂ with
  | nil => simp only [nil_kunion, nd₂]
  | cons s l₁ ih =>
    simp? at nd₁ says simp only [nodupKeys_cons] at nd₁
    simp [not_or, nd₁.1, nd₂, ih nd₁.2 (nd₂.kerase s.1)]
#align list.nodupkeys.kunion List.NodupKeys.kunion

theorem Perm.kunion_right {l₁ l₂ : List (Sigma β)} (p : l₁ ~ l₂) (l) :
    kunion l₁ l ~ kunion l₂ l := by
  induction p generalizing l with
  | nil => rfl
  | cons hd _ ih =>
    simp [ih (List.kerase _ _), Perm.cons]
  | swap s₁ s₂ l => simp [kerase_comm, Perm.swap]
  | trans _ _ ih₁₂ ih₂₃ => exact Perm.trans (ih₁₂ l) (ih₂₃ l)
#align list.perm.kunion_right List.Perm.kunion_right

theorem Perm.kunion_left :
    ∀ (l) {l₁ l₂ : List (Sigma β)}, l₁.NodupKeys → l₁ ~ l₂ → kunion l l₁ ~ kunion l l₂
  | [], _, _, _, p => p
  | s :: l, _, _, nd₁, p => ((p.kerase nd₁).kunion_left l <| nd₁.kerase s.1).cons s
#align list.perm.kunion_left List.Perm.kunion_left

theorem Perm.kunion {l₁ l₂ l₃ l₄ : List (Sigma β)} (nd₃ : l₃.NodupKeys) (p₁₂ : l₁ ~ l₂)
    (p₃₄ : l₃ ~ l₄) : kunion l₁ l₃ ~ kunion l₂ l₄ :=
  (p₁₂.kunion_right l₃).trans (p₃₄.kunion_left l₂ nd₃)
#align list.perm.kunion List.Perm.kunion

@[simp]
theorem dlookup_kunion_left {a} {l₁ l₂ : List (Sigma β)} (h : a ∈ l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₁ := by
  induction' l₁ with s _ ih generalizing l₂ <;> simp at h; cases' h with h h <;> cases' s with a'
  · subst h
    simp
  · rw [kunion_cons]
    by_cases h' : a = a'
    · subst h'
      simp
    · simp [h', ih h]
#align list.lookup_kunion_left List.dlookup_kunion_left

@[simp]
theorem dlookup_kunion_right {a} {l₁ l₂ : List (Sigma β)} (h : a ∉ l₁.keys) :
    dlookup a (kunion l₁ l₂) = dlookup a l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih => simp_all [not_or]
#align list.lookup_kunion_right List.dlookup_kunion_right

theorem mem_dlookup_kunion {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    b ∈ dlookup a (kunion l₁ l₂) ↔ b ∈ dlookup a l₁ ∨ a ∉ l₁.keys ∧ b ∈ dlookup a l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons s _ ih =>
    cases' s with a'
    by_cases h₁ : a = a'
    · subst h₁
      simp
    · let h₂ := @ih (kerase a' l₂)
      simp? [h₁] at h₂ says
        simp only [Option.mem_def, ne_eq, h₁, not_false_eq_true, dlookup_kerase_ne] at h₂
      simp [h₁, h₂]
#align list.mem_lookup_kunion List.mem_dlookup_kunion

@[simp]
theorem dlookup_kunion_eq_some {a} {b : β a} {l₁ l₂ : List (Sigma β)} :
    dlookup a (kunion l₁ l₂) = some b ↔
      dlookup a l₁ = some b ∨ a ∉ l₁.keys ∧ dlookup a l₂ = some b :=
  mem_dlookup_kunion

theorem mem_dlookup_kunion_middle {a} {b : β a} {l₁ l₂ l₃ : List (Sigma β)}
    (h₁ : b ∈ dlookup a (kunion l₁ l₃)) (h₂ : a ∉ keys l₂) :
    b ∈ dlookup a (kunion (kunion l₁ l₂) l₃) :=
  match mem_dlookup_kunion.mp h₁ with
  | Or.inl h => mem_dlookup_kunion.mpr (Or.inl (mem_dlookup_kunion.mpr (Or.inl h)))
  | Or.inr h => mem_dlookup_kunion.mpr <| Or.inr ⟨mt mem_keys_kunion.mp (not_or.mpr ⟨h.1, h₂⟩), h.2⟩
#align list.mem_lookup_kunion_middle List.mem_dlookup_kunion_middle

end List
