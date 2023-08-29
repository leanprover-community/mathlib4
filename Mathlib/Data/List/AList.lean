/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import Mathlib.Data.List.Sigma

#align_import data.list.alist from "leanprover-community/mathlib"@"f808feb6c18afddb25e66a71d317643cf7fb5fbb"

/-!
# Association Lists

This file defines association lists. An association list is a list where every element consists of
a key and a value, and no two entries have the same key. The type of the value is allowed to be
dependent on the type of the key.

This type dependence is implemented using `Sigma`: The elements of the list are of type `Sigma β`,
for some type index `β`.

## Main definitions

Association lists are represented by the `AList` structure. This file defines this structure and
provides ways to access, modify, and combine `AList`s.

* `AList.keys` returns a list of keys of the alist.
* `AList.membership` returns membership in the set of keys.
* `AList.erase` removes a certain key.
* `AList.insert` adds a key-value mapping to the list.
* `AList.union` combines two association lists.

## References

* <https://en.wikipedia.org/wiki/Association_list>

-/


universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-- `AList β` is a key-value map stored as a `List` (i.e. a linked list).
  It is a wrapper around certain `List` functions with the added constraint
  that the list have unique keys. -/
structure AList (β : α → Type v) : Type max u v where
  /-- The underlying `List` of an `AList` -/
  entries : List (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys
#align alist AList

/-- Given `l : List (Sigma β)`, create a term of type `AList β` by removing
entries with duplicate keys. -/
def List.toAList [DecidableEq α] {β : α → Type v} (l : List (Sigma β)) : AList β where
  entries := _
  nodupKeys := nodupKeys_dedupKeys l
#align list.to_alist List.toAList

namespace AList

@[ext]
theorem ext : ∀ {s t : AList β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, _⟩, H => by congr
                               -- 🎉 no goals
#align alist.ext AList.ext

theorem ext_iff {s t : AList β} : s = t ↔ s.entries = t.entries :=
  ⟨congr_arg _, ext⟩
#align alist.ext_iff AList.ext_iff

instance [DecidableEq α] [∀ a, DecidableEq (β a)] : DecidableEq (AList β) := fun xs ys => by
  rw [ext_iff]; infer_instance
  -- ⊢ Decidable (xs.entries = ys.entries)
                -- 🎉 no goals

/-! ### keys -/


/-- The list of keys of an association list. -/
def keys (s : AList β) : List α :=
  s.entries.keys
#align alist.keys AList.keys

theorem keys_nodup (s : AList β) : s.keys.Nodup :=
  s.nodupKeys
#align alist.keys_nodup AList.keys_nodup

/-! ### mem -/


/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : Membership α (AList β) :=
  ⟨fun a s => a ∈ s.keys⟩

theorem mem_keys {a : α} {s : AList β} : a ∈ s ↔ a ∈ s.keys :=
  Iff.rfl
#align alist.mem_keys AList.mem_keys

theorem mem_of_perm {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
  (p.map Sigma.fst).mem_iff
#align alist.mem_of_perm AList.mem_of_perm

/-! ### empty -/


/-- The empty association list. -/
instance : EmptyCollection (AList β) :=
  ⟨⟨[], nodupKeys_nil⟩⟩

instance : Inhabited (AList β) :=
  ⟨∅⟩

@[simp]
theorem not_mem_empty (a : α) : a ∉ (∅ : AList β) :=
  not_mem_nil a
#align alist.not_mem_empty AList.not_mem_empty

@[simp]
theorem empty_entries : (∅ : AList β).entries = [] :=
  rfl
#align alist.empty_entries AList.empty_entries

@[simp]
theorem keys_empty : (∅ : AList β).keys = [] :=
  rfl
#align alist.keys_empty AList.keys_empty

/-! ### singleton -/


/-- The singleton association list. -/
def singleton (a : α) (b : β a) : AList β :=
  ⟨[⟨a, b⟩], nodupKeys_singleton _⟩
#align alist.singleton AList.singleton

@[simp]
theorem singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk a b] :=
  rfl
#align alist.singleton_entries AList.singleton_entries

@[simp]
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] :=
  rfl
#align alist.keys_singleton AList.keys_singleton

/-! ### lookup -/


section

variable [DecidableEq α]

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : AList β) : Option (β a) :=
  s.entries.dlookup a
#align alist.lookup AList.lookup

@[simp]
theorem lookup_empty (a) : lookup a (∅ : AList β) = none :=
  rfl
#align alist.lookup_empty AList.lookup_empty

theorem lookup_isSome {a : α} {s : AList β} : (s.lookup a).isSome ↔ a ∈ s :=
  dlookup_isSome
#align alist.lookup_is_some AList.lookup_isSome

theorem lookup_eq_none {a : α} {s : AList β} : lookup a s = none ↔ a ∉ s :=
  dlookup_eq_none
#align alist.lookup_eq_none AList.lookup_eq_none

theorem mem_lookup_iff {a : α} {b : β a} {s : AList β} :
    b ∈ lookup a s ↔ Sigma.mk a b ∈ s.entries :=
  mem_dlookup_iff s.nodupKeys
#align alist.mem_lookup_iff AList.mem_lookup_iff

theorem perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    s₁.lookup a = s₂.lookup a :=
  perm_dlookup _ s₁.nodupKeys s₂.nodupKeys p
#align alist.perm_lookup AList.perm_lookup

instance (a : α) (s : AList β) : Decidable (a ∈ s) :=
  decidable_of_iff _ lookup_isSome

theorem keys_subset_keys_of_entries_subset_entries
    {s₁ s₂ : AList β} (h : s₁.entries ⊆ s₂.entries) : s₁.keys ⊆ s₂.keys := by
  intro k hk
  -- ⊢ k ∈ keys s₂
  letI : DecidableEq α := Classical.decEq α
  -- ⊢ k ∈ keys s₂
  have := h (mem_lookup_iff.1 (Option.get_mem (lookup_isSome.2 hk)))
  -- ⊢ k ∈ keys s₂
  rw [← mem_lookup_iff, Option.mem_def] at this
  -- ⊢ k ∈ keys s₂
  rw [← mem_keys, ← lookup_isSome, this]
  -- ⊢ Option.isSome (some (Option.get (lookup k s₁) (_ : Option.isSome (lookup k s …
  exact Option.isSome_some
  -- 🎉 no goals

/-! ### replace -/


/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kreplace a b s.entries, (kreplace_nodupKeys a b).2 s.nodupKeys⟩
#align alist.replace AList.replace

@[simp]
theorem keys_replace (a : α) (b : β a) (s : AList β) : (replace a b s).keys = s.keys :=
  keys_kreplace _ _ _
#align alist.keys_replace AList.keys_replace

@[simp]
theorem mem_replace {a a' : α} {b : β a} {s : AList β} : a' ∈ replace a b s ↔ a' ∈ s := by
  rw [mem_keys, keys_replace, ← mem_keys]
  -- 🎉 no goals
#align alist.mem_replace AList.mem_replace

theorem perm_replace {a : α} {b : β a} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
  Perm.kreplace s₁.nodupKeys
#align alist.perm_replace AList.perm_replace

end

/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ) (d : δ) (m : AList β) : δ :=
  m.entries.foldl (fun r a => f r a.1 a.2) d
#align alist.foldl AList.foldl

/-! ### erase -/


section

variable [DecidableEq α]

/-- Erase a key from the map. If the key is not present, do nothing. -/
def erase (a : α) (s : AList β) : AList β :=
  ⟨s.entries.kerase a, s.nodupKeys.kerase a⟩
#align alist.erase AList.erase

@[simp]
theorem keys_erase (a : α) (s : AList β) : (erase a s).keys = s.keys.erase a :=
  keys_kerase
#align alist.keys_erase AList.keys_erase

@[simp]
theorem mem_erase {a a' : α} {s : AList β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s := by
  rw [mem_keys, keys_erase, s.keys_nodup.mem_erase_iff, ← mem_keys]
  -- 🎉 no goals
#align alist.mem_erase AList.mem_erase

theorem perm_erase {a : α} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
  Perm.kerase s₁.nodupKeys
#align alist.perm_erase AList.perm_erase

@[simp]
theorem lookup_erase (a) (s : AList β) : lookup a (erase a s) = none :=
  dlookup_kerase a s.nodupKeys
#align alist.lookup_erase AList.lookup_erase

@[simp]
theorem lookup_erase_ne {a a'} {s : AList β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  dlookup_kerase_ne h
#align alist.lookup_erase_ne AList.lookup_erase_ne

theorem erase_erase (a a' : α) (s : AList β) : (s.erase a).erase a' = (s.erase a').erase a :=
  ext <| kerase_kerase
#align alist.erase_erase AList.erase_erase

/-! ### insert -/


/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kinsert a b s.entries, kinsert_nodupKeys a b s.nodupKeys⟩
#align alist.insert AList.insert

@[simp]
theorem insert_entries {a} {b : β a} {s : AList β} :
    (insert a b s).entries = Sigma.mk a b :: kerase a s.entries :=
  rfl
#align alist.insert_entries AList.insert_entries

theorem insert_entries_of_neg {a} {b : β a} {s : AList β} (h : a ∉ s) :
    (insert a b s).entries = ⟨a, b⟩ :: s.entries := by rw [insert_entries, kerase_of_not_mem_keys h]
                                                       -- 🎉 no goals
#align alist.insert_entries_of_neg AList.insert_entries_of_neg

-- Todo: rename to `insert_of_not_mem`.
theorem insert_of_neg {a} {b : β a} {s : AList β} (h : a ∉ s) :
    insert a b s = ⟨⟨a, b⟩ :: s.entries, nodupKeys_cons.2 ⟨h, s.2⟩⟩ :=
  ext <| insert_entries_of_neg h
#align alist.insert_of_neg AList.insert_of_neg

@[simp]
theorem insert_empty (a) (b : β a) : insert a b ∅ = singleton a b :=
  rfl
#align alist.insert_empty AList.insert_empty

@[simp]
theorem mem_insert {a a'} {b' : β a'} (s : AList β) : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  mem_keys_kinsert
#align alist.mem_insert AList.mem_insert

@[simp]
theorem keys_insert {a} {b : β a} (s : AList β) : (insert a b s).keys = a :: s.keys.erase a := by
  simp [insert, keys, keys_kerase]
  -- 🎉 no goals
#align alist.keys_insert AList.keys_insert

theorem perm_insert {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    (insert a b s₁).entries ~ (insert a b s₂).entries := by
  simp only [insert_entries]; exact p.kinsert s₁.nodupKeys
  -- ⊢ { fst := a, snd := b } :: kerase a s₁.entries ~ { fst := a, snd := b } :: ke …
                              -- 🎉 no goals
#align alist.perm_insert AList.perm_insert

@[simp]
theorem lookup_insert {a} {b : β a} (s : AList β) : lookup a (insert a b s) = some b := by
  simp only [lookup, insert, dlookup_kinsert]
  -- 🎉 no goals
#align alist.lookup_insert AList.lookup_insert

@[simp]
theorem lookup_insert_ne {a a'} {b' : β a'} {s : AList β} (h : a ≠ a') :
    lookup a (insert a' b' s) = lookup a s :=
  dlookup_kinsert_ne h
#align alist.lookup_insert_ne AList.lookup_insert_ne

@[simp]
theorem lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAList = s.dlookup a := by
  rw [List.toAList, lookup, dlookup_dedupKeys]
  -- 🎉 no goals
#align alist.lookup_to_alist AList.lookup_to_alist

@[simp]
theorem insert_insert {a} {b b' : β a} (s : AList β) :
    (s.insert a b).insert a b' = s.insert a b' := by
  ext : 1; simp only [AList.insert_entries, List.kerase_cons_eq]
  -- ⊢ (insert a b' (insert a b s)).entries = (insert a b' s).entries
           -- 🎉 no goals
#align alist.insert_insert AList.insert_insert

theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a ≠ a') :
    ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries := by
  simp only [insert_entries]; rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
  -- ⊢ { fst := a', snd := b' } :: kerase a' ({ fst := a, snd := b } :: kerase a s. …
    [apply Perm.swap; exact h; exact h.symm]
#align alist.insert_insert_of_ne AList.insert_insert_of_ne

@[simp]
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b :=
  ext <| by
    simp only [AList.insert_entries, List.kerase_cons_eq, and_self_iff, AList.singleton_entries,
      heq_iff_eq, eq_self_iff_true]
#align alist.insert_singleton_eq AList.insert_singleton_eq

@[simp]
theorem entries_toAList (xs : List (Sigma β)) : (List.toAList xs).entries = dedupKeys xs :=
  rfl
#align alist.entries_to_alist AList.entries_toAList

theorem toAList_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toAList (⟨a, b⟩ :: xs) = insert a b xs.toAList :=
  rfl
#align alist.to_alist_cons AList.toAList_cons

theorem mk_cons_eq_insert (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).NodupKeys) :
    (⟨c :: l, h⟩ : AList β) = insert c.1 c.2 ⟨l, nodupKeys_of_nodupKeys_cons h⟩ := by
  simpa [insert] using (kerase_of_not_mem_keys <| not_mem_keys_of_nodupKeys_cons h).symm
  -- 🎉 no goals
#align alist.mk_cons_eq_insert AList.mk_cons_eq_insert

/-- Recursion on an `AList`, using `insert`. Use as `induction l using AList.insertRec`. -/
@[elab_as_elim]
def insertRec {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) :
    ∀ l : AList β, C l
  | ⟨[], _⟩ => H0
  | ⟨c :: l, h⟩ => by
    rw [mk_cons_eq_insert]
    -- ⊢ C (insert c.fst c.snd { entries := l, nodupKeys := (_ : NodupKeys l) })
    refine' IH _ _ _ _ (insertRec H0 IH _)
    -- ⊢ ¬c.fst ∈ { entries := l, nodupKeys := (_ : NodupKeys l) }
    exact not_mem_keys_of_nodupKeys_cons h
    -- 🎉 no goals
#align alist.insert_rec AList.insertRec

-- Test that the `induction` tactic works on `insert_rec`.
example (l : AList β) : True := by induction l using AList.insertRec <;> trivial
                                   -- ⊢ True
                                                                         -- 🎉 no goals
                                                                         -- 🎉 no goals

@[simp]
theorem insertRec_empty {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) :
    @insertRec α β _ C H0 IH ∅ = H0 := by
  change @insertRec α β _ C H0 IH ⟨[], _⟩ = H0
  -- ⊢ insertRec H0 IH { entries := [], nodupKeys := (_ : NodupKeys []) } = H0
  rw [insertRec]
  -- 🎉 no goals
#align alist.insert_rec_empty AList.insertRec_empty

theorem insertRec_insert {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) {c : Sigma β}
    {l : AList β} (h : c.1 ∉ l) :
    @insertRec α β _ C H0 IH (l.insert c.1 c.2) = IH c.1 c.2 l h (@insertRec α β _ C H0 IH l) := by
  cases' l with l hl
  -- ⊢ insertRec H0 IH (insert c.fst c.snd { entries := l, nodupKeys := hl }) = IH  …
  suffices HEq (@insertRec α β _ C H0 IH ⟨c :: l, nodupKeys_cons.2 ⟨h, hl⟩⟩)
      (IH c.1 c.2 ⟨l, hl⟩ h (@insertRec α β _ C H0 IH ⟨l, hl⟩)) by
    cases c
    apply eq_of_heq
    convert this <;> rw [insert_of_neg h]
  rw [insertRec]
  -- ⊢ HEq (Eq.mpr (_ : C { entries := c :: l, nodupKeys := (_ : NodupKeys (c :: l) …
  apply cast_heq
  -- 🎉 no goals
#align alist.insert_rec_insert AList.insertRec_insert

theorem insertRec_insert_mk {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) {a : α} (b : β a)
    {l : AList β} (h : a ∉ l) :
    @insertRec α β _ C H0 IH (l.insert a b) = IH a b l h (@insertRec α β _ C H0 IH l) :=
  @insertRec_insert α β _ C H0 IH ⟨a, b⟩ l h
#align alist.recursion_insert_mk AList.insertRec_insert_mk

/-! ### extract -/


/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : AList β) : Option (β a) × AList β :=
  have : (kextract a s.entries).2.NodupKeys := by
    rw [kextract_eq_dlookup_kerase]; exact s.nodupKeys.kerase _
    -- ⊢ NodupKeys (dlookup a s.entries, kerase a s.entries).snd
                                     -- 🎉 no goals
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)
#align alist.extract AList.extract

@[simp]
theorem extract_eq_lookup_erase (a : α) (s : AList β) : extract a s = (lookup a s, erase a s) := by
  simp [extract]; constructor <;> rfl
  -- ⊢ dlookup a s.entries = lookup a s ∧ { entries := kerase a s.entries, nodupKey …
                  -- ⊢ dlookup a s.entries = lookup a s
                                  -- 🎉 no goals
                                  -- 🎉 no goals
#align alist.extract_eq_lookup_erase AList.extract_eq_lookup_erase

/-! ### union -/


/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : AList β) : AList β :=
  ⟨s₁.entries.kunion s₂.entries, s₁.nodupKeys.kunion s₂.nodupKeys⟩
#align alist.union AList.union

instance : Union (AList β) :=
  ⟨union⟩

@[simp]
theorem union_entries {s₁ s₂ : AList β} : (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
  rfl
#align alist.union_entries AList.union_entries

@[simp]
theorem empty_union {s : AList β} : (∅ : AList β) ∪ s = s :=
  ext rfl
#align alist.empty_union AList.empty_union

@[simp]
theorem union_empty {s : AList β} : s ∪ (∅ : AList β) = s :=
  ext <| by simp
            -- 🎉 no goals
#align alist.union_empty AList.union_empty

@[simp]
theorem mem_union {a} {s₁ s₂ : AList β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  mem_keys_kunion
#align alist.mem_union AList.mem_union

theorem perm_union {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries)
    (p₃₄ : s₃.entries ~ s₄.entries) : (s₁ ∪ s₃).entries ~ (s₂ ∪ s₄).entries := by
  simp [p₁₂.kunion s₃.nodupKeys p₃₄]
  -- 🎉 no goals
#align alist.perm_union AList.perm_union

theorem union_erase (a : α) (s₁ s₂ : AList β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
  ext kunion_kerase.symm
#align alist.union_erase AList.union_erase

@[simp]
theorem lookup_union_left {a} {s₁ s₂ : AList β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  dlookup_kunion_left
#align alist.lookup_union_left AList.lookup_union_left

@[simp]
theorem lookup_union_right {a} {s₁ s₂ : AList β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  dlookup_kunion_right
#align alist.lookup_union_right AList.lookup_union_right

--Porting note: removing simp, LHS not in SNF, new theorem added instead.
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  mem_dlookup_kunion
#align alist.mem_lookup_union AList.mem_lookup_union

--Porting note: new theorem, version of `mem_lookup_union` with LHS in simp-normal form
@[simp]
theorem lookup_union_eq_some {a} {b : β a} {s₁ s₂ : AList β} :
    lookup a (s₁ ∪ s₂) = some b ↔ lookup a s₁ = some b ∨ a ∉ s₁ ∧ lookup a s₂ = some b :=
  mem_dlookup_kunion

theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : AList β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  mem_dlookup_kunion_middle
#align alist.mem_lookup_union_middle AList.mem_lookup_union_middle

theorem insert_union {a} {b : β a} {s₁ s₂ : AList β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
  by ext; simp
     -- ⊢ a✝ ∈ get? (insert a b (s₁ ∪ s₂)).entries n✝ ↔ a✝ ∈ get? (insert a b s₁ ∪ s₂) …
          -- 🎉 no goals
#align alist.insert_union AList.insert_union

theorem union_assoc {s₁ s₂ s₃ : AList β} : (s₁ ∪ s₂ ∪ s₃).entries ~ (s₁ ∪ (s₂ ∪ s₃)).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by simp [not_or, or_assoc, and_or_left, and_assoc])
        -- 🎉 no goals
#align alist.union_assoc AList.union_assoc

end

/-! ### disjoint -/


/-- Two associative lists are disjoint if they have no common keys. -/
def Disjoint (s₁ s₂ : AList β) : Prop :=
  ∀ k ∈ s₁.keys, ¬k ∈ s₂.keys
#align alist.disjoint AList.Disjoint

variable [DecidableEq α]

theorem union_comm_of_disjoint {s₁ s₂ : AList β} (h : Disjoint s₁ s₂) :
    (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by
      intros; simp
      -- ⊢ y✝ ∈ dlookup x✝ (s₁ ∪ s₂).entries ↔ y✝ ∈ dlookup x✝ (s₂ ∪ s₁).entries
              -- ⊢ dlookup x✝ s₁.entries = some y✝ ∨ ¬x✝ ∈ List.keys s₁.entries ∧ dlookup x✝ s₂ …
      constructor <;> intro h'
      -- ⊢ dlookup x✝ s₁.entries = some y✝ ∨ ¬x✝ ∈ List.keys s₁.entries ∧ dlookup x✝ s₂ …
                      -- ⊢ dlookup x✝ s₂.entries = some y✝ ∨ ¬x✝ ∈ List.keys s₂.entries ∧ dlookup x✝ s₁ …
                      -- ⊢ dlookup x✝ s₁.entries = some y✝ ∨ ¬x✝ ∈ List.keys s₁.entries ∧ dlookup x✝ s₂ …
      · cases' h' with h' h'
        -- ⊢ dlookup x✝ s₂.entries = some y✝ ∨ ¬x✝ ∈ List.keys s₂.entries ∧ dlookup x✝ s₁ …
        · right
          -- ⊢ ¬x✝ ∈ List.keys s₂.entries ∧ dlookup x✝ s₁.entries = some y✝
          refine' ⟨_, h'⟩
          -- ⊢ ¬x✝ ∈ List.keys s₂.entries
          apply h
          -- ⊢ x✝ ∈ keys s₁
          rw [keys, ← List.dlookup_isSome, h']
          -- ⊢ Option.isSome (some y✝) = true
          exact rfl
          -- 🎉 no goals
        · left
          -- ⊢ dlookup x✝ s₂.entries = some y✝
          rw [h'.2]
          -- 🎉 no goals
      · cases' h' with h' h'
        -- ⊢ dlookup x✝ s₁.entries = some y✝ ∨ ¬x✝ ∈ List.keys s₁.entries ∧ dlookup x✝ s₂ …
        · right
          -- ⊢ ¬x✝ ∈ List.keys s₁.entries ∧ dlookup x✝ s₂.entries = some y✝
          refine' ⟨_, h'⟩
          -- ⊢ ¬x✝ ∈ List.keys s₁.entries
          intro h''
          -- ⊢ False
          apply h _ h''
          -- ⊢ x✝ ∈ keys s₂
          rw [keys, ← List.dlookup_isSome, h']
          -- ⊢ Option.isSome (some y✝) = true
          exact rfl
          -- 🎉 no goals
        · left
          -- ⊢ dlookup x✝ s₁.entries = some y✝
          rw [h'.2])
          -- 🎉 no goals
#align alist.union_comm_of_disjoint AList.union_comm_of_disjoint

end AList
