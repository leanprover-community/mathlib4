/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro

! This file was ported from Lean 3 source module data.list.alist
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.Sigma

/-!
# Association Lists

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `sigma`: The elements of the list are of type `sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `alist` structure. This file defines this structure and
provides ways to access, modify, and combine `alist`s.

* `alist.keys` returns a list of keys of the alist.
* `alist.has_mem` returns membership in the set of keys.
* `alist.erase` removes a certain key.
* `alist.insert` adds a key-value mapping to the list.
* `alist.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/


universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-- `alist β` is a key-value map stored as a `list` (i.e. a linked list).
  It is a wrapper around certain `list` functions with the added constraint
  that the list have unique keys. -/
structure Alist (β : α → Type v) : Type max u v where
  entries : List (Sigma β)
  Nodupkeys : entries.Nodupkeys
#align alist Alist

/-- Given `l : list (sigma β)`, create a term of type `alist β` by removing
entries with duplicate keys. -/
def List.toAlist [DecidableEq α] {β : α → Type v} (l : List (Sigma β)) : Alist β
    where
  entries := _
  Nodupkeys := nodupkeys_dedupkeys l
#align list.to_alist List.toAlist

namespace Alist

@[ext]
theorem ext : ∀ {s t : Alist β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩, H => by congr
#align alist.ext Alist.ext

theorem ext_iff {s t : Alist β} : s = t ↔ s.entries = t.entries :=
  ⟨congr_arg _, ext⟩
#align alist.ext_iff Alist.ext_iff

instance [DecidableEq α] [∀ a, DecidableEq (β a)] : DecidableEq (Alist β) := fun xs ys => by
  rw [ext_iff] <;> infer_instance

/-! ### keys -/


/-- The list of keys of an association list. -/
def keys (s : Alist β) : List α :=
  s.entries.keys
#align alist.keys Alist.keys

theorem keys_nodup (s : Alist β) : s.keys.Nodup :=
  s.Nodupkeys
#align alist.keys_nodup Alist.keys_nodup

/-! ### mem -/


/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : Membership α (Alist β) :=
  ⟨fun a s => a ∈ s.keys⟩

theorem mem_keys {a : α} {s : Alist β} : a ∈ s ↔ a ∈ s.keys :=
  Iff.rfl
#align alist.mem_keys Alist.mem_keys

theorem mem_of_perm {a : α} {s₁ s₂ : Alist β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
  (p.map Sigma.fst).mem_iff
#align alist.mem_of_perm Alist.mem_of_perm

/-! ### empty -/


/-- The empty association list. -/
instance : EmptyCollection (Alist β) :=
  ⟨⟨[], nodupkeys_nil⟩⟩

instance : Inhabited (Alist β) :=
  ⟨∅⟩

@[simp]
theorem not_mem_empty (a : α) : a ∉ (∅ : Alist β) :=
  not_mem_nil a
#align alist.not_mem_empty Alist.not_mem_empty

@[simp]
theorem empty_entries : (∅ : Alist β).entries = [] :=
  rfl
#align alist.empty_entries Alist.empty_entries

@[simp]
theorem keys_empty : (∅ : Alist β).keys = [] :=
  rfl
#align alist.keys_empty Alist.keys_empty

/-! ### singleton -/


/-- The singleton association list. -/
def singleton (a : α) (b : β a) : Alist β :=
  ⟨[⟨a, b⟩], nodupkeys_singleton _⟩
#align alist.singleton Alist.singleton

@[simp]
theorem singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk a b] :=
  rfl
#align alist.singleton_entries Alist.singleton_entries

@[simp]
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] :=
  rfl
#align alist.keys_singleton Alist.keys_singleton

/-! ### lookup -/


section

variable [DecidableEq α]

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : Alist β) : Option (β a) :=
  s.entries.lookup a
#align alist.lookup Alist.lookup

@[simp]
theorem lookup_empty (a) : lookup a (∅ : Alist β) = none :=
  rfl
#align alist.lookup_empty Alist.lookup_empty

theorem lookup_is_some {a : α} {s : Alist β} : (s.lookup a).isSome ↔ a ∈ s :=
  lookup_is_some
#align alist.lookup_is_some Alist.lookup_is_some

theorem lookup_eq_none {a : α} {s : Alist β} : lookup a s = none ↔ a ∉ s :=
  lookup_eq_none
#align alist.lookup_eq_none Alist.lookup_eq_none

theorem mem_lookup_iff {a : α} {b : β a} {s : Alist β} :
    b ∈ lookup a s ↔ Sigma.mk a b ∈ s.entries :=
  mem_dlookup_iff s.Nodupkeys
#align alist.mem_lookup_iff Alist.mem_lookup_iff

theorem perm_lookup {a : α} {s₁ s₂ : Alist β} (p : s₁.entries ~ s₂.entries) :
    s₁.lookup a = s₂.lookup a :=
  perm_dlookup _ s₁.Nodupkeys s₂.Nodupkeys p
#align alist.perm_lookup Alist.perm_lookup

instance (a : α) (s : Alist β) : Decidable (a ∈ s) :=
  decidable_of_iff _ lookup_is_some

/-! ### replace -/


/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : Alist β) : Alist β :=
  ⟨kreplace a b s.entries, (kreplace_nodupkeys a b).2 s.Nodupkeys⟩
#align alist.replace Alist.replace

@[simp]
theorem keys_replace (a : α) (b : β a) (s : Alist β) : (replace a b s).keys = s.keys :=
  keys_kreplace _ _ _
#align alist.keys_replace Alist.keys_replace

@[simp]
theorem mem_replace {a a' : α} {b : β a} {s : Alist β} : a' ∈ replace a b s ↔ a' ∈ s := by
  rw [mem_keys, keys_replace, ← mem_keys]
#align alist.mem_replace Alist.mem_replace

theorem perm_replace {a : α} {b : β a} {s₁ s₂ : Alist β} :
    s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
  Perm.kreplace s₁.Nodupkeys
#align alist.perm_replace Alist.perm_replace

end

/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ) (d : δ) (m : Alist β) : δ :=
  m.entries.foldl (fun r a => f r a.1 a.2) d
#align alist.foldl Alist.foldl

/-! ### erase -/


section

variable [DecidableEq α]

/-- Erase a key from the map. If the key is not present, do nothing. -/
def erase (a : α) (s : Alist β) : Alist β :=
  ⟨s.entries.kerase a, s.Nodupkeys.kerase a⟩
#align alist.erase Alist.erase

@[simp]
theorem keys_erase (a : α) (s : Alist β) : (erase a s).keys = s.keys.erase a :=
  keys_kerase
#align alist.keys_erase Alist.keys_erase

@[simp]
theorem mem_erase {a a' : α} {s : Alist β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s := by
  rw [mem_keys, keys_erase, s.keys_nodup.mem_erase_iff, ← mem_keys]
#align alist.mem_erase Alist.mem_erase

theorem perm_erase {a : α} {s₁ s₂ : Alist β} :
    s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
  Perm.kerase s₁.Nodupkeys
#align alist.perm_erase Alist.perm_erase

@[simp]
theorem lookup_erase (a) (s : Alist β) : lookup a (erase a s) = none :=
  dlookup_kerase a s.Nodupkeys
#align alist.lookup_erase Alist.lookup_erase

@[simp]
theorem lookup_erase_ne {a a'} {s : Alist β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  dlookup_kerase_ne h
#align alist.lookup_erase_ne Alist.lookup_erase_ne

theorem erase_erase (a a' : α) (s : Alist β) : (s.erase a).erase a' = (s.erase a').erase a :=
  ext <| kerase_kerase
#align alist.erase_erase Alist.erase_erase

/-! ### insert -/


/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert (a : α) (b : β a) (s : Alist β) : Alist β :=
  ⟨kinsert a b s.entries, kinsert_nodupkeys a b s.Nodupkeys⟩
#align alist.insert Alist.insert

@[simp]
theorem insert_entries {a} {b : β a} {s : Alist β} :
    (insert a b s).entries = Sigma.mk a b :: kerase a s.entries :=
  rfl
#align alist.insert_entries Alist.insert_entries

theorem insert_entries_of_neg {a} {b : β a} {s : Alist β} (h : a ∉ s) :
    (insert a b s).entries = ⟨a, b⟩ :: s.entries := by rw [insert_entries, kerase_of_not_mem_keys h]
#align alist.insert_entries_of_neg Alist.insert_entries_of_neg

@[simp]
theorem insert_empty (a) (b : β a) : insert a b ∅ = singleton a b :=
  rfl
#align alist.insert_empty Alist.insert_empty

@[simp]
theorem mem_insert {a a'} {b' : β a'} (s : Alist β) : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  mem_keys_kinsert
#align alist.mem_insert Alist.mem_insert

@[simp]
theorem keys_insert {a} {b : β a} (s : Alist β) : (insert a b s).keys = a :: s.keys.erase a := by
  simp [insert, keys, keys_kerase]
#align alist.keys_insert Alist.keys_insert

theorem perm_insert {a} {b : β a} {s₁ s₂ : Alist β} (p : s₁.entries ~ s₂.entries) :
    (insert a b s₁).entries ~ (insert a b s₂).entries := by
  simp only [insert_entries] <;> exact p.kinsert s₁.nodupkeys
#align alist.perm_insert Alist.perm_insert

@[simp]
theorem lookup_insert {a} {b : β a} (s : Alist β) : lookup a (insert a b s) = some b := by
  simp only [lookup, insert, lookup_kinsert]
#align alist.lookup_insert Alist.lookup_insert

@[simp]
theorem lookup_insert_ne {a a'} {b' : β a'} {s : Alist β} (h : a ≠ a') :
    lookup a (insert a' b' s) = lookup a s :=
  dlookup_kinsert_ne h
#align alist.lookup_insert_ne Alist.lookup_insert_ne

@[simp]
theorem lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAlist = s.lookup a := by
  rw [List.toAlist, lookup, lookup_dedupkeys]
#align alist.lookup_to_alist Alist.lookup_to_alist

@[simp]
theorem insert_insert {a} {b b' : β a} (s : Alist β) : (s.insert a b).insert a b' = s.insert a b' :=
  by
  ext : 1 <;> simp only [Alist.insert_entries, List.kerase_cons_eq] <;> constructorm*_ ∧ _ <;> rfl
#align alist.insert_insert Alist.insert_insert

theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : Alist β) (h : a ≠ a') :
    ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries := by
  simp only [insert_entries] <;> rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
    [apply perm.swap, exact h, exact h.symm]
#align alist.insert_insert_of_ne Alist.insert_insert_of_ne

@[simp]
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b :=
  ext <| by
    simp only [Alist.insert_entries, List.kerase_cons_eq, and_self_iff, Alist.singleton_entries,
      heq_iff_eq, eq_self_iff_true]
#align alist.insert_singleton_eq Alist.insert_singleton_eq

@[simp]
theorem entries_to_alist (xs : List (Sigma β)) : (List.toAlist xs).entries = dedupkeys xs :=
  rfl
#align alist.entries_to_alist Alist.entries_to_alist

theorem to_alist_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toAlist (⟨a, b⟩ :: xs) = insert a b xs.toAlist :=
  rfl
#align alist.to_alist_cons Alist.to_alist_cons

/-! ### extract -/


/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : Alist β) : Option (β a) × Alist β :=
  have : (kextract a s.entries).2.Nodupkeys := by
    rw [kextract_eq_lookup_kerase] <;> exact s.nodupkeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)
#align alist.extract Alist.extract

@[simp]
theorem extract_eq_lookup_erase (a : α) (s : Alist β) : extract a s = (lookup a s, erase a s) := by
  simp [extract] <;> constructor <;> rfl
#align alist.extract_eq_lookup_erase Alist.extract_eq_lookup_erase

/-! ### union -/


/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : Alist β) : Alist β :=
  ⟨s₁.entries.kunion s₂.entries, s₁.Nodupkeys.kunion s₂.Nodupkeys⟩
#align alist.union Alist.union

instance : Union (Alist β) :=
  ⟨union⟩

@[simp]
theorem union_entries {s₁ s₂ : Alist β} : (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
  rfl
#align alist.union_entries Alist.union_entries

@[simp]
theorem empty_union {s : Alist β} : (∅ : Alist β) ∪ s = s :=
  ext rfl
#align alist.empty_union Alist.empty_union

@[simp]
theorem union_empty {s : Alist β} : s ∪ (∅ : Alist β) = s :=
  ext <| by simp
#align alist.union_empty Alist.union_empty

@[simp]
theorem mem_union {a} {s₁ s₂ : Alist β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  mem_keys_kunion
#align alist.mem_union Alist.mem_union

theorem perm_union {s₁ s₂ s₃ s₄ : Alist β} (p₁₂ : s₁.entries ~ s₂.entries)
    (p₃₄ : s₃.entries ~ s₄.entries) : (s₁ ∪ s₃).entries ~ (s₂ ∪ s₄).entries := by
  simp [p₁₂.kunion s₃.nodupkeys p₃₄]
#align alist.perm_union Alist.perm_union

theorem union_erase (a : α) (s₁ s₂ : Alist β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
  ext kunion_kerase.symm
#align alist.union_erase Alist.union_erase

@[simp]
theorem lookup_union_left {a} {s₁ s₂ : Alist β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  lookup_kunion_left
#align alist.lookup_union_left Alist.lookup_union_left

@[simp]
theorem lookup_union_right {a} {s₁ s₂ : Alist β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  lookup_kunion_right
#align alist.lookup_union_right Alist.lookup_union_right

@[simp]
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : Alist β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  mem_lookup_kunion
#align alist.mem_lookup_union Alist.mem_lookup_union

theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : Alist β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  mem_lookup_kunion_middle
#align alist.mem_lookup_union_middle Alist.mem_lookup_union_middle

theorem insert_union {a} {b : β a} {s₁ s₂ : Alist β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
  by ext <;> simp
#align alist.insert_union Alist.insert_union

theorem union_assoc {s₁ s₂ s₃ : Alist β} : (s₁ ∪ s₂ ∪ s₃).entries ~ (s₁ ∪ (s₂ ∪ s₃)).entries :=
  lookup_ext (Alist.nodupkeys _) (Alist.nodupkeys _)
    (by simp [Decidable.not_or_iff_and_not, or_assoc', and_or_left, and_assoc'])
#align alist.union_assoc Alist.union_assoc

end

/-! ### disjoint -/


/-- Two associative lists are disjoint if they have no common keys. -/
def Disjoint (s₁ s₂ : Alist β) : Prop :=
  ∀ k ∈ s₁.keys, ¬k ∈ s₂.keys
#align alist.disjoint Alist.Disjoint

variable [DecidableEq α]

theorem union_comm_of_disjoint {s₁ s₂ : Alist β} (h : Disjoint s₁ s₂) :
    (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
  lookup_ext (Alist.nodupkeys _) (Alist.nodupkeys _)
    (by
      intros ; simp
      constructor <;> intro h'
      cases h'
      · right
        refine' ⟨_, h'⟩
        apply h
        rw [keys, ← List.dlookup_is_some, h']
        exact rfl
      · left
        rw [h'.2]
      cases h'
      · right
        refine' ⟨_, h'⟩
        intro h''
        apply h _ h''
        rw [keys, ← List.dlookup_is_some, h']
        exact rfl
      · left
        rw [h'.2])
#align alist.union_comm_of_disjoint Alist.union_comm_of_disjoint

end Alist

