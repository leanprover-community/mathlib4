/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import Mathlib.Data.List.Sigma

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

variable {α : Type u} {β γ : α → Type v}

/-- `AList β` is a key-value map stored as a `List` (i.e. a linked list).
  It is a wrapper around certain `List` functions with the added constraint
  that the list have unique keys. -/
structure AList (β : α → Type v) : Type max u v where
  /-- The underlying `List` of an `AList` -/
  entries : List (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

/-- Given `l : List (Sigma β)`, create a term of type `AList β` by removing
entries with duplicate keys. -/
def List.toAList [DecidableEq α] {β : α → Type v} (l : List (Sigma β)) : AList β where
  entries := _
  nodupKeys := nodupKeys_dedupKeys l

namespace AList

@[ext]
theorem ext : ∀ {s t : AList β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, _⟩, H => by congr

instance [DecidableEq α] [∀ a, DecidableEq (β a)] : DecidableEq (AList β) := fun xs ys => by
  rw [AList.ext_iff]; infer_instance

/-! ### keys -/


/-- The list of keys of an association list. -/
def keys (s : AList β) : List α :=
  s.entries.keys

theorem keys_nodup (s : AList β) : s.keys.Nodup :=
  s.nodupKeys

@[simp]
theorem keys_mk (l : List (Sigma β)) (h) : (AList.mk l h).keys = l.keys :=
  rfl

/-! ### mem -/


/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : Membership α (AList β) :=
  ⟨fun s a => a ∈ s.keys⟩

theorem mem_keys {a : α} {s : AList β} : a ∈ s ↔ a ∈ s.keys :=
  Iff.rfl

theorem mem_of_perm {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) : a ∈ s₁ ↔ a ∈ s₂ :=
  (p.map Sigma.fst).mem_iff

@[simp]
theorem mem_mk {l : List (Sigma β)} {h} {x : α} : x ∈ AList.mk l h ↔ x ∈ l.keys :=
  .rfl

/-! ### empty -/


/-- The empty association list. -/
instance : EmptyCollection (AList β) :=
  ⟨⟨[], nodupKeys_nil⟩⟩

instance : Inhabited (AList β) :=
  ⟨∅⟩

@[simp]
theorem notMem_empty (a : α) : a ∉ (∅ : AList β) :=
  not_mem_nil

@[deprecated (since := "2025-05-23")] alias not_mem_empty := notMem_empty

@[simp]
theorem empty_entries : (∅ : AList β).entries = [] :=
  rfl

@[simp]
theorem keys_empty : (∅ : AList β).keys = [] :=
  rfl

theorem eq_empty_iff (m : AList β) : m.entries = [] ↔ m = ∅ := by
  apply Iff.intro
  · intro hm; apply ext; simp [hm]
  · intro hm; simp [hm]

/-! ### singleton -/


/-- The singleton association list. -/
def singleton (a : α) (b : β a) : AList β :=
  ⟨[⟨a, b⟩], nodupKeys_singleton _⟩

@[simp]
theorem singleton_entries (a : α) (b : β a) : (singleton a b).entries = [Sigma.mk a b] :=
  rfl

@[simp]
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = [a] :=
  rfl

/-! ### lookup -/


section

variable [DecidableEq α]

/-- Look up the value associated to a key in an association list. -/
def lookup (a : α) (s : AList β) : Option (β a) :=
  s.entries.dlookup a

@[simp]
theorem lookup_empty (a) : lookup a (∅ : AList β) = none :=
  rfl

theorem lookup_isSome {a : α} {s : AList β} : (s.lookup a).isSome ↔ a ∈ s :=
  dlookup_isSome

theorem lookup_eq_none {a : α} {s : AList β} : lookup a s = none ↔ a ∉ s :=
  dlookup_eq_none

theorem mem_lookup_iff {a : α} {b : β a} {s : AList β} :
    b ∈ lookup a s ↔ Sigma.mk a b ∈ s.entries :=
  mem_dlookup_iff s.nodupKeys

theorem perm_lookup {a : α} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    s₁.lookup a = s₂.lookup a :=
  perm_dlookup _ s₁.nodupKeys p

instance (a : α) (s : AList β) : Decidable (a ∈ s) :=
  decidable_of_iff _ lookup_isSome

end

theorem keys_subset_keys_of_entries_subset_entries
    {s₁ s₂ : AList β} (h : s₁.entries ⊆ s₂.entries) : s₁.keys ⊆ s₂.keys := by
  intro k hk
  letI : DecidableEq α := Classical.decEq α
  have := h (mem_lookup_iff.1 (Option.get_mem (lookup_isSome.2 hk)))
  rw [← mem_lookup_iff, Option.mem_def] at this
  rw [← mem_keys, ← lookup_isSome, this]
  exact Option.isSome_some

/-! ### replace -/

section
variable [DecidableEq α]

/-- Replace a key with a given value in an association list.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kreplace a b s.entries, (kreplace_nodupKeys a b).2 s.nodupKeys⟩

@[simp]
theorem keys_replace (a : α) (b : β a) (s : AList β) : (replace a b s).keys = s.keys :=
  keys_kreplace _ _ _

@[simp]
theorem mem_replace {a a' : α} {b : β a} {s : AList β} : a' ∈ replace a b s ↔ a' ∈ s := by
  rw [mem_keys, keys_replace, ← mem_keys]

theorem perm_replace {a : α} {b : β a} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (replace a b s₁).entries ~ (replace a b s₂).entries :=
  Perm.kreplace s₁.nodupKeys

end

/-- Fold a function over the key-value pairs in the map. -/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ) (d : δ) (m : AList β) : δ :=
  m.entries.foldl (fun r a => f r a.1 a.2) d

def foldr {δ : Type w} (f : ∀ a, β a → δ → δ) (d : δ) (m : AList β) : δ :=
  m.entries.foldr (fun a r => f a.1 a.2 r) d


/-! ### erase -/


section

variable [DecidableEq α]

/-- Erase a key from the map. If the key is not present, do nothing. -/
def erase (a : α) (s : AList β) : AList β :=
  ⟨s.entries.kerase a, s.nodupKeys.kerase a⟩

@[simp]
theorem keys_erase (a : α) (s : AList β) : (erase a s).keys = s.keys.erase a :=
  keys_kerase

@[simp]
theorem mem_erase {a a' : α} {s : AList β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s := by
  rw [mem_keys, keys_erase, s.keys_nodup.mem_erase_iff, ← mem_keys]

theorem perm_erase {a : α} {s₁ s₂ : AList β} :
    s₁.entries ~ s₂.entries → (erase a s₁).entries ~ (erase a s₂).entries :=
  Perm.kerase s₁.nodupKeys

@[simp]
theorem lookup_erase (a) (s : AList β) : lookup a (erase a s) = none :=
  dlookup_kerase a s.nodupKeys

@[simp]
theorem lookup_erase_ne {a a'} {s : AList β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  dlookup_kerase_ne h

theorem erase_erase (a a' : α) (s : AList β) : (s.erase a).erase a' = (s.erase a').erase a :=
  ext <| kerase_kerase

/-! ### insert -/


/-- Insert a key-value pair into an association list and erase any existing pair
  with the same key. -/
def insert (a : α) (b : β a) (s : AList β) : AList β :=
  ⟨kinsert a b s.entries, kinsert_nodupKeys a b s.nodupKeys⟩

@[simp]
theorem entries_insert {a} {b : β a} {s : AList β} :
    (insert a b s).entries = Sigma.mk a b :: kerase a s.entries :=
  rfl

theorem entries_insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) :
    (insert a b s).entries = ⟨a, b⟩ :: s.entries := by rw [entries_insert, kerase_of_notMem_keys h]

@[deprecated (since := "2025-05-23")] alias entries_insert_of_not_mem := entries_insert_of_notMem

theorem insert_of_notMem {a} {b : β a} {s : AList β} (h : a ∉ s) :
    insert a b s = ⟨⟨a, b⟩ :: s.entries, nodupKeys_cons.2 ⟨h, s.2⟩⟩ :=
  ext <| entries_insert_of_notMem h

@[deprecated (since := "2025-05-23")] alias insert_of_not_mem := insert_of_notMem

@[simp]
theorem insert_empty (a) (b : β a) : insert a b ∅ = singleton a b :=
  rfl

@[simp]
theorem mem_insert {a a'} {b' : β a'} (s : AList β) : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  mem_keys_kinsert

@[simp]
theorem keys_insert {a} {b : β a} (s : AList β) : (insert a b s).keys = a :: s.keys.erase a := by
  simp [insert, keys, keys_kerase]

theorem perm_insert {a} {b : β a} {s₁ s₂ : AList β} (p : s₁.entries ~ s₂.entries) :
    (insert a b s₁).entries ~ (insert a b s₂).entries := by
  simp only [entries_insert]; exact p.kinsert s₁.nodupKeys

@[simp]
theorem lookup_insert {a} {b : β a} (s : AList β) : lookup a (insert a b s) = some b := by
  simp only [lookup, insert, dlookup_kinsert]

@[simp]
theorem lookup_insert_ne {a a'} {b' : β a'} {s : AList β} (h : a ≠ a') :
    lookup a (insert a' b' s) = lookup a s :=
  dlookup_kinsert_ne h

@[simp] theorem lookup_insert_eq_none {l : AList β} {k k' : α} {v : β k} :
    (l.insert k v).lookup k' = none ↔ (k' ≠ k) ∧ l.lookup k' = none := by
  by_cases h : k' = k
  · subst h; simp
  · simp_all [lookup_insert_ne h]

@[simp]
theorem lookup_to_alist {a} (s : List (Sigma β)) : lookup a s.toAList = s.dlookup a := by
  rw [List.toAList, lookup, dlookup_dedupKeys]

@[simp]
theorem insert_insert {a} {b b' : β a} (s : AList β) :
    (s.insert a b).insert a b' = s.insert a b' := by
  ext : 1; simp only [AList.entries_insert, List.kerase_cons_eq]

theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : AList β) (h : a ≠ a') :
    ((s.insert a b).insert a' b').entries ~ ((s.insert a' b').insert a b).entries := by
  simp only [entries_insert]; rw [kerase_cons_ne, kerase_cons_ne, kerase_comm] <;>
    [apply Perm.swap; exact h; exact h.symm]

@[simp]
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b :=
  ext <| by
    simp only [AList.entries_insert, List.kerase_cons_eq, AList.singleton_entries]

@[simp]
theorem entries_toAList (xs : List (Sigma β)) : (List.toAList xs).entries = dedupKeys xs :=
  rfl

theorem toAList_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toAList (⟨a, b⟩ :: xs) = insert a b xs.toAList :=
  rfl

theorem mk_cons_eq_insert (c : Sigma β) (l : List (Sigma β)) (h : (c :: l).NodupKeys) :
    (⟨c :: l, h⟩ : AList β) = insert c.1 c.2 ⟨l, nodupKeys_of_nodupKeys_cons h⟩ := by
  simpa [insert] using (kerase_of_notMem_keys <| notMem_keys_of_nodupKeys_cons h).symm

/-- Recursion on an `AList`, using `insert`. Use as `induction l`. -/
@[elab_as_elim, induction_eliminator]
def insertRec {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) :
    ∀ l : AList β, C l
  | ⟨[], _⟩ => H0
  | ⟨c :: l, h⟩ => by
    rw [mk_cons_eq_insert]
    refine IH _ _ _ ?_ (insertRec H0 IH _)
    exact notMem_keys_of_nodupKeys_cons h

-- Test that the `induction` tactic works on `insertRec`.
example (l : AList β) : True := by induction l <;> trivial

@[simp]
theorem insertRec_empty {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) :
    @insertRec α β _ C H0 IH ∅ = H0 := by
  change @insertRec α β _ C H0 IH ⟨[], _⟩ = H0
  rw [insertRec]

theorem insertRec_insert {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) {c : Sigma β}
    {l : AList β} (h : c.1 ∉ l) :
    @insertRec α β _ C H0 IH (l.insert c.1 c.2) = IH c.1 c.2 l h (@insertRec α β _ C H0 IH l) := by
  obtain ⟨l, hl⟩ := l
  suffices @insertRec α β _ C H0 IH ⟨c :: l, nodupKeys_cons.2 ⟨h, hl⟩⟩ ≍
      IH c.1 c.2 ⟨l, hl⟩ h (@insertRec α β _ C H0 IH ⟨l, hl⟩) by
    cases c
    apply eq_of_heq
    convert this <;> rw [insert_of_notMem h]
  rw [insertRec]
  apply cast_heq

theorem insertRec_insert_mk {C : AList β → Sort*} (H0 : C ∅)
    (IH : ∀ (a : α) (b : β a) (l : AList β), a ∉ l → C l → C (l.insert a b)) {a : α} (b : β a)
    {l : AList β} (h : a ∉ l) :
    @insertRec α β _ C H0 IH (l.insert a b) = IH a b l h (@insertRec α β _ C H0 IH l) :=
  @insertRec_insert α β _ C H0 IH ⟨a, b⟩ l h

/-! ### extract -/


/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : AList β) : Option (β a) × AList β :=
  have : (kextract a s.entries).2.NodupKeys := by
    rw [kextract_eq_dlookup_kerase]; exact s.nodupKeys.kerase _
  match kextract a s.entries, this with
  | (b, l), h => (b, ⟨l, h⟩)

@[simp]
theorem extract_eq_lookup_erase (a : α) (s : AList β) : extract a s = (lookup a s, erase a s) := by
  simp [extract]; constructor <;> rfl

/-! ### union -/


/-- `s₁ ∪ s₂` is the key-based union of two association lists. It is
left-biased: if there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`.
-/
def union (s₁ s₂ : AList β) : AList β :=
  ⟨s₁.entries.kunion s₂.entries, s₁.nodupKeys.kunion s₂.nodupKeys⟩

instance : Union (AList β) :=
  ⟨union⟩

@[simp]
theorem union_entries {s₁ s₂ : AList β} : (s₁ ∪ s₂).entries = kunion s₁.entries s₂.entries :=
  rfl

@[simp]
theorem empty_union {s : AList β} : (∅ : AList β) ∪ s = s :=
  ext rfl

@[simp]
theorem union_empty {s : AList β} : s ∪ (∅ : AList β) = s :=
  ext <| by simp

@[simp]
theorem mem_union {a} {s₁ s₂ : AList β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  mem_keys_kunion

theorem perm_union {s₁ s₂ s₃ s₄ : AList β} (p₁₂ : s₁.entries ~ s₂.entries)
    (p₃₄ : s₃.entries ~ s₄.entries) : (s₁ ∪ s₃).entries ~ (s₂ ∪ s₄).entries := by
  simp [p₁₂.kunion s₃.nodupKeys p₃₄]

theorem union_erase (a : α) (s₁ s₂ : AList β) : erase a (s₁ ∪ s₂) = erase a s₁ ∪ erase a s₂ :=
  ext kunion_kerase.symm

@[simp]
theorem lookup_union_left {a} {s₁ s₂ : AList β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  dlookup_kunion_left

@[simp]
theorem lookup_union_right {a} {s₁ s₂ : AList β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  dlookup_kunion_right

-- The corresponding lemma in `simp`-normal form is `lookup_union_eq_some`.
theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : AList β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  mem_dlookup_kunion

@[simp]
theorem lookup_union_eq_some {a} {b : β a} {s₁ s₂ : AList β} :
    lookup a (s₁ ∪ s₂) = some b ↔ lookup a s₁ = some b ∨ a ∉ s₁ ∧ lookup a s₂ = some b :=
  mem_dlookup_kunion

@[simp]
theorem lookup_union_eq_none {x : α} {m₁ m₂ : AList β} :
  (m₁ ∪ m₂).lookup x = none ↔ m₁.lookup x = none ∧ m₂.lookup x = none :=
  dlookup_kunion_eq_none

theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : AList β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  mem_dlookup_kunion_middle

theorem insert_union {a} {b : β a} {s₁ s₂ : AList β} :
    insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ := by ext; simp

theorem union_assoc {s₁ s₂ s₃ : AList β} : (s₁ ∪ s₂ ∪ s₃).entries ~ (s₁ ∪ (s₂ ∪ s₃)).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by simp [not_or, or_assoc, and_or_left, and_assoc])


/-! Filter -/

/-- `m.filter_map p` performs two operations on `m`:
(1) It removes the key-value bindings `(x, y)` such that `p x y = None`.
(2) It updates the remaining key-value bindings `(x, y)` to `(x, y')`
where `p x y = Some y'`.
-/
def filter_map (m : AList β) (p : (x : α) → β x → Option (γ x)) : AList γ :=
  m.foldr (fun x y acc =>
    match p x y with
    | some y' => acc.insert x y'
    | none => acc
  ) ∅

/-- `m.filter p` removes the key-value bindings `(x, y)` for which `p x y` is false. -/
def filter (m : AList β) (p : (x : α) → β x → Prop)
  [∀ x y, Decidable (p x y)] : AList β :=
  m.filter_map fun x y => if p x y then some y else none

@[simp]
theorem empty_filter_map {p : (x : α) → β x → Option (γ x)} : AList.filter_map ∅ p = ∅ := by
  simp [filter_map, foldr]

theorem insert_filter_map {m : AList β} {p : (x : α) → β x → Option (γ x)} {x : α} {y : β x} :
  x ∉ m →
  (m.insert x y).filter_map p =
    match p x y with
    | some y' => (m.filter_map p).insert x y'
    | none    => m.filter_map p
:= by
  intros hx_nin_m
  apply ext
  cases (Option.eq_none_or_eq_some (p x y))
  case a.inl hnone =>
    simp [hnone, insert, List.kerase_of_notMem_keys hx_nin_m]
    simp [filter_map, foldr, hnone]
  case a.inr hsome =>
    have ⟨y', hsome'⟩ := hsome
    simp [hsome', insert, List.kerase_of_notMem_keys hx_nin_m]
    simp [filter_map, foldr, hsome']

theorem lookup_filter_map_eq_some
  {m : AList β} {p : (x : α) → β x → Option (γ x)} (x : α) (y' : γ x) :
  (m.filter_map p).lookup x = some y' →
  ∃ y, m.lookup x = some y ∧ p x y = some y'
:= by
  revert x y'
  induction m
  case H0 => intro x y'; simp
  case IH x y m hm ih =>
    intro x' y'
    rw [insert_filter_map hm]
    match (Option.eq_none_or_eq_some (p x y)) with
    | Or.inl hnone =>
      simp [hnone]; intro hy'
      have ⟨z, hz, hp⟩ := ih x' y' hy'
      match Decidable.em (x' = x) with
      | Or.inr hneq => simp [lookup_insert_ne hneq]; exists z
      | Or.inl heq =>
        cases heq
        rw [←lookup_eq_none] at hm
        simp [hm] at *
    | Or.inr ⟨z, hsome⟩ =>
      simp [hsome]
      intro hy'
      match Decidable.em (x' = x) with
      | Or.inr hneq =>
        simp [lookup_insert_ne hneq] at *
        have ⟨z', hz', hp'⟩ := ih x' y' hy'
        exists z'
      | Or.inl heq =>
        cases heq; simp at *
        cases hy'; assumption

theorem lookup_filter_map_eq_none
  {m : AList β} {p : (x : α) → β x → Option (γ x)} (x : α) :
  (m.filter_map p).lookup x = none →
  m.lookup x = none ∨ ∃ y, m.lookup x = some y ∧ p x y = none
:= by
  revert x
  induction m
  case H0 => intro x; simp
  case IH x y m hm ih =>
    intro x'
    rw [insert_filter_map hm]
    match (Option.eq_none_or_eq_some (p x y)) with
    | Or.inl hnone =>
      simp [hnone]
      intro hlkp_x'
      match ih x' hlkp_x' with
      | Or.inl hm_lkp_x' =>
        match Decidable.em (x' = x) with
        | Or.inr hneq => apply Or.inl ⟨hneq, hm_lkp_x'⟩
        | Or.inl heq =>
          cases heq
          apply Or.inr ⟨y, by simp, hnone⟩
      | Or.inr ⟨y', hy', hp'⟩ =>
        apply Or.inr
        match Decidable.em (x' = x) with
        | Or.inr hneq =>
          exists y'; apply And.intro _ hp'
          simp [hneq]; assumption
        | Or.inl heq => cases heq; exists y; simp; assumption
    | Or.inr ⟨z, hsome⟩ =>
      simp [hsome]
      intro hneq hlkp_x'
      match ih x' hlkp_x' with
      | Or.inl hm_lkp_x' => apply Or.inl ⟨hneq, hm_lkp_x'⟩
      | Or.inr ⟨y', hy', hp'⟩ =>
        apply Or.inr ⟨y', by simp [hneq, hy'], hp'⟩

theorem lookup_filter_map_eq_some_iff
  {m : AList β} {p : (x : α) → β x → Option (γ x)} (x : α) (y' : γ x) :
  (m.filter_map p).lookup x = some y' ↔
  ∃ y, m.lookup x = some y ∧ p x y = some y'
:= by
  apply Iff.intro (lookup_filter_map_eq_some x y')
  intro ⟨y, hy, hp⟩
  match ((m.filter_map p).lookup x).eq_none_or_eq_some with
  | Or.inl hnone =>
    match lookup_filter_map_eq_none x hnone with
    | Or.inl hlkp_x_none => simp [hy] at *
    | Or.inr ⟨z, hz, hp⟩ => simp [hy] at *; cases hz; simp [hp] at *
  | Or.inr ⟨z, hsome⟩ =>
    have ⟨z', hz', hp'⟩ := lookup_filter_map_eq_some x z hsome
    simp [hy] at *; cases hz'; simp [hp] at *; cases hp'; assumption

theorem lookup_filter_map_eq_none_iff
  {m : AList β} {p : (x : α) → β x → Option (γ x)} (x : α) :
  (m.filter_map p).lookup x = none ↔
  m.lookup x = none ∨ ∃ y, m.lookup x = some y ∧ p x y = none
:= by
  apply Iff.intro (lookup_filter_map_eq_none x)
  apply ((m.filter_map p).lookup x).eq_none_or_eq_some.elim (fun _ => ·)
  apply flip; intro
  | Or.inl hnone =>
    intro ⟨y, hsome⟩
    have ⟨y', hy', hp'⟩ := lookup_filter_map_eq_some x y hsome
    simp [hnone] at *
  | Or.inr ⟨y, hsome, hp⟩ =>
    intro ⟨y', hsome⟩
    have ⟨z, hz, hp'⟩ := lookup_filter_map_eq_some x y' hsome
    simp [*] at *; cases hz; simp [hp] at *

theorem filter_map_is_permutation_respecting
  {m₁ m₂ : AList β} {p : (x : α) → β x → Option (γ x)} :
  m₁.entries.Perm m₂.entries →
  ∀ x, (m₁.filter_map p).lookup x = (m₂.filter_map p).lookup x
:= by
  intro hperm x
  cases ((m₂.filter_map p).lookup x).eq_none_or_eq_some
  case inl hnone =>
    rw [hnone]
    rw [lookup_filter_map_eq_none_iff] at *
    rw [perm_lookup hperm]
    assumption
  case inr hsome =>
    have ⟨y, hsomey⟩ := hsome
    rw [hsomey]
    rw [lookup_filter_map_eq_some_iff] at *
    rw [perm_lookup hperm]
    assumption


/-! ### merge -/

/-- `merge s₁ s₂ f` computes an association list that contains the same keys
as the union of `s₁` and `s₂`. A key `x` that is both in `s₁` and `s₂` is bound
to `f y₁ y₂` where `(x, y₁) ∈ s₁` and `(x, y₂) ∈ s₂`. The original bindings
(in `s₁` or in `s₂`) are kept for remaining keys.
-/
def merge (m₁ m₂ : AList β) (f : {x : α} → β x → β x → β x) : AList β :=
  (m₁ ∪ m₂).filter_map fun x _ =>
    match m₁.lookup x, m₂.lookup x with
    | some y₁, some y₂ => some (f y₁ y₂)
    | some y₁,    none => some y₁
    |    none, some y₂ => some y₂
    |    none,    none => none

theorem lookup_merge_none {m₁ m₂ : AList β} {f : {x : α} → β x → β x → β x} {x : α} :
  m₁.lookup x = none →
  m₂.lookup x = none →
  (merge m₁ m₂ f).lookup x = none
:= by
  intro hm₁_lkp hm₂_lkp
  simp [merge, lookup_filter_map_eq_none_iff, *]

theorem lookup_merge_eq_none {m₁ m₂ : AList β} {f : {x : α} → β x → β x → β x} {x : α} :
  (merge m₁ m₂ f).lookup x = none →
  m₁.lookup x = none ∧
  m₂.lookup x = none
:= by
  rw [merge, lookup_filter_map_eq_none_iff]
  simp [lookup_union_eq_none]
  intro
  | Or.inl h => exact h
  | Or.inr ⟨⟨y, hlkp⟩, hmatch⟩ =>
    revert hmatch
    apply hlkp.elim
    · intro hsome
      simp [hsome]; cases (m₂.lookup x) <;> simp
    · intro ⟨_, hsome⟩
      simp [hsome]; cases (m₁.lookup x) <;> simp

theorem lookup_merge_some_left {m₁ m₂ : AList β} {f : {x : α} → β x → β x → β x} {x : α} {y : β x} :
  m₁.lookup x = some y →
  m₂.lookup x = none →
  (merge m₁ m₂ f).lookup x = some y
:= by
  intro hm₁_lkp hm₂_lkp
  simp [merge, lookup_filter_map_eq_some_iff, *]

theorem lookup_merge_some_right
  {m₁ m₂ : AList β} {f : {x : α} → β x → β x → β x} {x : α} {y : β x} :
  m₁.lookup x = none →
  m₂.lookup x = some y →
  (merge m₁ m₂ f).lookup x = some y
:= by
  intro hm₁_lkp hm₂_lkp
  simp [merge, lookup_filter_map_eq_some_iff, ←lookup_eq_none, *]

theorem lookup_merge_some_inter
  {m₁ m₂ : AList β} {f : {x : α} → β x → β x → β x} {x : α} {y₁ y₂ : β x} :
  m₁.lookup x = some y₁ →
  m₂.lookup x = some y₂ →
  (merge m₁ m₂ f).lookup x = some (f y₁ y₂)
:= by
  intro hm₁_lkp hm₂_lkp
  simp [merge, lookup_filter_map_eq_some_iff, *]

end


/-! ### disjoint -/

/-- Two associative lists are disjoint if they have no common keys. -/
def Disjoint (s₁ s₂ : AList β) : Prop :=
  ∀ k ∈ s₁.keys, k ∉ s₂.keys

variable [DecidableEq α]

theorem union_comm_of_disjoint {s₁ s₂ : AList β} (h : Disjoint s₁ s₂) :
    (s₁ ∪ s₂).entries ~ (s₂ ∪ s₁).entries :=
  lookup_ext (AList.nodupKeys _) (AList.nodupKeys _)
    (by
      intros; simp only [union_entries, Option.mem_def, dlookup_kunion_eq_some]
      constructor <;> intro h'
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          apply h
          rw [keys, ← List.dlookup_isSome, h']
          exact rfl
        · left
          rw [h'.2]
      · rcases h' with h' | h'
        · right
          refine ⟨?_, h'⟩
          intro h''
          apply h _ h''
          rw [keys, ← List.dlookup_isSome, h']
          exact rfl
        · left
          rw [h'.2])

end AList
