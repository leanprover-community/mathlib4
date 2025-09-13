/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sean Leather, Mario Carneiro
-/
import Mathlib.Data.List.AList
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Part

/-!
# Finite maps over `Multiset`
-/

universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-! ### Multisets of sigma types -/

namespace Multiset

/-- Multiset of keys of an association multiset. -/
def keys (s : Multiset (Sigma β)) : Multiset α :=
  s.map Sigma.fst

@[simp]
theorem coe_keys {l : List (Sigma β)} : keys (l : Multiset (Sigma β)) = (l.keys : Multiset α) :=
  rfl

@[simp]
theorem keys_zero : keys (0 : Multiset (Sigma β)) = 0 := rfl

@[simp]
theorem keys_cons {a : α} {b : β a} {s : Multiset (Sigma β)} :
    keys (⟨a, b⟩ ::ₘ s) = a ::ₘ keys s := by
  simp [keys]

@[simp]
theorem keys_singleton {a : α} {b : β a} : keys ({⟨a, b⟩} : Multiset (Sigma β)) = {a} := rfl

/-- `NodupKeys s` means that `s` has no duplicate keys. -/
def NodupKeys (s : Multiset (Sigma β)) : Prop :=
  Quot.liftOn s List.NodupKeys fun _ _ p => propext <| perm_nodupKeys p

@[simp]
theorem coe_nodupKeys {l : List (Sigma β)} : @NodupKeys α β l ↔ l.NodupKeys :=
  Iff.rfl

lemma nodup_keys {m : Multiset (Σ a, β a)} : m.keys.Nodup ↔ m.NodupKeys := by
  rcases m with ⟨l⟩; rfl

alias ⟨_, NodupKeys.nodup_keys⟩ := nodup_keys

protected lemma NodupKeys.nodup {m : Multiset (Σ a, β a)} (h : m.NodupKeys) : m.Nodup :=
  h.nodup_keys.of_map _

end Multiset

/-! ### Finmap -/

/-- `Finmap β` is the type of finite maps over a multiset. It is effectively
  a quotient of `AList β` by permutation of the underlying list. -/
structure Finmap (β : α → Type v) : Type max u v where
  /-- The underlying `Multiset` of a `Finmap` -/
  entries : Multiset (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

/-- The quotient map from `AList` to `Finmap`. -/
def AList.toFinmap (s : AList β) : Finmap β :=
  ⟨s.entries, s.nodupKeys⟩

local notation:arg "⟦" a "⟧" => AList.toFinmap a

theorem AList.toFinmap_eq {s₁ s₂ : AList β} :
    toFinmap s₁ = toFinmap s₂ ↔ s₁.entries ~ s₂.entries := by
  cases s₁
  cases s₂
  simp [AList.toFinmap]

@[simp]
theorem AList.toFinmap_entries (s : AList β) : ⟦s⟧.entries = s.entries :=
  rfl

/-- Given `l : List (Sigma β)`, create a term of type `Finmap β` by removing
entries with duplicate keys. -/
def List.toFinmap [DecidableEq α] (s : List (Sigma β)) : Finmap β :=
  s.toAList.toFinmap

namespace Finmap

open AList

lemma nodup_entries (f : Finmap β) : f.entries.Nodup := f.nodupKeys.nodup

/-! ### Lifting from AList -/

/-- Lift a permutation-respecting function on `AList` to `Finmap`. -/
def liftOn {γ} (s : Finmap β) (f : AList β → γ)
    (H : ∀ a b : AList β, a.entries ~ b.entries → f a = f b) : γ := by
  refine
    (Quotient.liftOn s.entries
      (fun (l : List (Sigma β)) => (⟨_, fun nd => f ⟨l, nd⟩⟩ : Part γ))
      (fun l₁ l₂ p => Part.ext' (perm_nodupKeys p) ?_) : Part γ).get ?_
  · exact fun h1 h2 => H _ _ p
  · have := s.nodupKeys
    revert this
    rcases s.entries with ⟨l⟩
    exact id

@[simp]
theorem liftOn_toFinmap {γ} (s : AList β) (f : AList β → γ) (H) : liftOn ⟦s⟧ f H = f s := by
  cases s
  rfl

/-- Lift a permutation-respecting function on 2 `AList`s to 2 `Finmap`s. -/
def liftOn₂ {γ} (s₁ s₂ : Finmap β) (f : AList β → AList β → γ)
    (H : ∀ a₁ b₁ a₂ b₂ : AList β,
      a₁.entries ~ a₂.entries → b₁.entries ~ b₂.entries → f a₁ b₁ = f a₂ b₂) : γ :=
  liftOn s₁ (fun l₁ => liftOn s₂ (f l₁) fun _ _ p => H _ _ _ _ (Perm.refl _) p) fun a₁ a₂ p => by
    have H' : f a₁ = f a₂ := funext fun _ => H _ _ _ _ p (Perm.refl _)
    simp only [H']

@[simp]
theorem liftOn₂_toFinmap {γ} (s₁ s₂ : AList β) (f : AList β → AList β → γ) (H) :
    liftOn₂ ⟦s₁⟧ ⟦s₂⟧ f H = f s₁ s₂ := by
      cases s₁; cases s₂; rfl

/-! ### Induction -/

@[elab_as_elim]
theorem induction_on {C : Finmap β → Prop} (s : Finmap β) (H : ∀ a : AList β, C ⟦a⟧) : C s := by
  rcases s with ⟨⟨a⟩, h⟩; exact H ⟨a, h⟩

@[elab_as_elim]
theorem induction_on₂ {C : Finmap β → Finmap β → Prop} (s₁ s₂ : Finmap β)
    (H : ∀ a₁ a₂ : AList β, C ⟦a₁⟧ ⟦a₂⟧) : C s₁ s₂ :=
  induction_on s₁ fun l₁ => induction_on s₂ fun l₂ => H l₁ l₂

@[elab_as_elim]
theorem induction_on₃ {C : Finmap β → Finmap β → Finmap β → Prop} (s₁ s₂ s₃ : Finmap β)
    (H : ∀ a₁ a₂ a₃ : AList β, C ⟦a₁⟧ ⟦a₂⟧ ⟦a₃⟧) : C s₁ s₂ s₃ :=
  induction_on₂ s₁ s₂ fun l₁ l₂ => induction_on s₃ fun l₃ => H l₁ l₂ l₃

/-! ### extensionality -/

@[ext]
theorem ext : ∀ {s t : Finmap β}, s.entries = t.entries → s = t
  | ⟨l₁, h₁⟩, ⟨l₂, _⟩, H => by congr

@[simp]
theorem ext_iff' {s t : Finmap β} : s.entries = t.entries ↔ s = t :=
  Finmap.ext_iff.symm

/-! ### mem -/

/-- The predicate `a ∈ s` means that `s` has a value associated to the key `a`. -/
instance : Membership α (Finmap β) :=
  ⟨fun s a => a ∈ s.entries.keys⟩

theorem mem_def {a : α} {s : Finmap β} : a ∈ s ↔ a ∈ s.entries.keys :=
  Iff.rfl

@[simp]
theorem mem_toFinmap {a : α} {s : AList β} : a ∈ toFinmap s ↔ a ∈ s :=
  Iff.rfl

/-! ### keys -/

/-- The set of keys of a finite map. -/
def keys (s : Finmap β) : Finset α :=
  ⟨s.entries.keys, s.nodupKeys.nodup_keys⟩

@[simp]
theorem keys_val (s : AList β) : (keys ⟦s⟧).val = s.keys :=
  rfl

@[simp]
theorem keys_ext {s₁ s₂ : AList β} : keys ⟦s₁⟧ = keys ⟦s₂⟧ ↔ s₁.keys ~ s₂.keys := by
  simp [keys, AList.keys]

theorem mem_keys {a : α} {s : Finmap β} : a ∈ s.keys ↔ a ∈ s :=
  induction_on s fun _ => AList.mem_keys

/-! ### empty -/

/-- The empty map. -/
instance : EmptyCollection (Finmap β) :=
  ⟨⟨0, nodupKeys_nil⟩⟩

instance : Inhabited (Finmap β) :=
  ⟨∅⟩

@[simp]
theorem empty_toFinmap : (⟦∅⟧ : Finmap β) = ∅ :=
  rfl

@[simp]
theorem toFinmap_nil [DecidableEq α] : ([].toFinmap : Finmap β) = ∅ :=
  rfl

theorem notMem_empty {a : α} : a ∉ (∅ : Finmap β) :=
  Multiset.notMem_zero a

@[deprecated (since := "2025-05-23")] alias not_mem_empty := notMem_empty

@[simp]
theorem keys_empty : (∅ : Finmap β).keys = ∅ :=
  rfl

/-! ### singleton -/

/-- The singleton map. -/
def singleton (a : α) (b : β a) : Finmap β :=
  ⟦AList.singleton a b⟧

@[simp]
theorem keys_singleton (a : α) (b : β a) : (singleton a b).keys = {a} :=
  rfl

@[simp]
theorem mem_singleton (x y : α) (b : β y) : x ∈ singleton y b ↔ x = y := by
  simp [singleton, mem_def]

section

variable [DecidableEq α]

instance decidableEq [∀ a, DecidableEq (β a)] : DecidableEq (Finmap β)
  | _, _ => decidable_of_iff _ Finmap.ext_iff.symm

/-! ### lookup -/

/-- Look up the value associated to a key in a map. -/
def lookup (a : α) (s : Finmap β) : Option (β a) :=
  liftOn s (AList.lookup a) fun _ _ => perm_lookup

@[simp]
theorem lookup_toFinmap (a : α) (s : AList β) : lookup a ⟦s⟧ = s.lookup a :=
  rfl

@[simp]
theorem dlookup_list_toFinmap (a : α) (s : List (Sigma β)) : lookup a s.toFinmap = s.dlookup a := by
  rw [List.toFinmap, lookup_toFinmap, lookup_to_alist]

@[simp]
theorem lookup_empty (a) : lookup a (∅ : Finmap β) = none :=
  rfl

theorem lookup_isSome {a : α} {s : Finmap β} : (s.lookup a).isSome ↔ a ∈ s :=
  induction_on s fun _ => AList.lookup_isSome

theorem lookup_eq_none {a} {s : Finmap β} : lookup a s = none ↔ a ∉ s :=
  induction_on s fun _ => AList.lookup_eq_none

lemma mem_lookup_iff {s : Finmap β} {a : α} {b : β a} :
    b ∈ s.lookup a ↔ Sigma.mk a b ∈ s.entries := by
  rcases s with ⟨⟨l⟩, hl⟩; exact List.mem_dlookup_iff hl

lemma lookup_eq_some_iff {s : Finmap β} {a : α} {b : β a} :
    s.lookup a = b ↔ Sigma.mk a b ∈ s.entries := mem_lookup_iff

@[simp] lemma sigma_keys_lookup (s : Finmap β) :
    s.keys.sigma (fun i => (s.lookup i).toFinset) = ⟨s.entries, s.nodup_entries⟩ := by
  ext x
  have : x ∈ s.entries → x.1 ∈ s.keys := Multiset.mem_map_of_mem _
  simpa [lookup_eq_some_iff]

@[simp]
theorem lookup_singleton_eq {a : α} {b : β a} : (singleton a b).lookup a = some b := by
  rw [singleton, lookup_toFinmap, AList.singleton, AList.lookup, dlookup_cons_eq]

instance (a : α) (s : Finmap β) : Decidable (a ∈ s) :=
  decidable_of_iff _ lookup_isSome

theorem mem_iff {a : α} {s : Finmap β} : a ∈ s ↔ ∃ b, s.lookup a = some b :=
  induction_on s fun s =>
    Iff.trans List.mem_keys <| exists_congr fun _ => (mem_dlookup_iff s.nodupKeys).symm

theorem mem_of_lookup_eq_some {a : α} {b : β a} {s : Finmap β} (h : s.lookup a = some b) : a ∈ s :=
  mem_iff.mpr ⟨_, h⟩

theorem ext_lookup {s₁ s₂ : Finmap β} : (∀ x, s₁.lookup x = s₂.lookup x) → s₁ = s₂ :=
  induction_on₂ s₁ s₂ fun s₁ s₂ h => by
    simp only [AList.lookup, lookup_toFinmap] at h
    rw [AList.toFinmap_eq]
    apply lookup_ext s₁.nodupKeys s₂.nodupKeys
    intro x y
    rw [h]

/-- An equivalence between `Finmap β` and pairs `(keys : Finset α, lookup : ∀ a, Option (β a))` such
that `(lookup a).isSome ↔ a ∈ keys`. -/
@[simps apply_coe_fst apply_coe_snd]
def keysLookupEquiv :
    Finmap β ≃ { f : Finset α × (∀ a, Option (β a)) // ∀ i, (f.2 i).isSome ↔ i ∈ f.1 } where
  toFun s := ⟨(s.keys, fun i => s.lookup i), fun _ => lookup_isSome⟩
  invFun f := mk (f.1.1.sigma fun i => (f.1.2 i).toFinset).val <| by
    refine Multiset.nodup_keys.1 ((Finset.nodup _).map_on ?_)
    simp only [Finset.mem_val, Finset.mem_sigma, Option.mem_toFinset, Option.mem_def]
    rintro ⟨i, x⟩ ⟨_, hx⟩ ⟨j, y⟩ ⟨_, hy⟩ (rfl : i = j)
    simpa using hx.symm.trans hy
  left_inv f := ext <| by simp
  right_inv := fun ⟨(s, f), hf⟩ => by
    dsimp only at hf
    ext
    · simp [keys, Multiset.keys, ← hf, Option.isSome_iff_exists]
    · simp +contextual [lookup_eq_some_iff, ← hf]

@[simp] lemma keysLookupEquiv_symm_apply_keys :
    ∀ f : {f : Finset α × (∀ a, Option (β a)) // ∀ i, (f.2 i).isSome ↔ i ∈ f.1},
      (keysLookupEquiv.symm f).keys = f.1.1 :=
  keysLookupEquiv.surjective.forall.2 fun _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_fst]

@[simp] lemma keysLookupEquiv_symm_apply_lookup :
    ∀ (f : {f : Finset α × (∀ a, Option (β a)) // ∀ i, (f.2 i).isSome ↔ i ∈ f.1}) a,
      (keysLookupEquiv.symm f).lookup a = f.1.2 a :=
  keysLookupEquiv.surjective.forall.2 fun _ _ => by
    simp only [Equiv.symm_apply_apply, keysLookupEquiv_apply_coe_snd]

/-! ### replace -/

/-- Replace a key with a given value in a finite map.
  If the key is not present it does nothing. -/
def replace (a : α) (b : β a) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.replace a b t))
    fun _ _ p => toFinmap_eq.2 <| perm_replace p

@[simp]
theorem replace_toFinmap (a : α) (b : β a) (s : AList β) :
    replace a b ⟦s⟧ = (⟦s.replace a b⟧ : Finmap β) := by
  simp [replace]

@[simp]
theorem keys_replace (a : α) (b : β a) (s : Finmap β) : (replace a b s).keys = s.keys :=
  induction_on s fun s => by simp

@[simp]
theorem mem_replace {a a' : α} {b : β a} {s : Finmap β} : a' ∈ replace a b s ↔ a' ∈ s :=
  induction_on s fun s => by simp

end

/-! ### foldl -/

/-- Fold a commutative function over the key-value pairs in the map -/
def foldl {δ : Type w} (f : δ → ∀ a, β a → δ)
    (H : ∀ d a₁ b₁ a₂ b₂, f (f d a₁ b₁) a₂ b₂ = f (f d a₂ b₂) a₁ b₁) (d : δ) (m : Finmap β) : δ :=
  letI : RightCommutative fun d (s : Sigma β) ↦ f d s.1 s.2 := ⟨fun _ _ _ ↦ H _ _ _ _ _⟩
  m.entries.foldl (fun d s => f d s.1 s.2) d

/-- `any f s` returns `true` iff there exists a value `v` in `s` such that `f v = true`. -/
def any (f : ∀ x, β x → Bool) (s : Finmap β) : Bool :=
  s.foldl (fun x y z => x || f y z)
    (fun _ _ _ _ => by simp_rw [Bool.or_assoc, Bool.or_comm, imp_true_iff]) false

/-- `all f s` returns `true` iff `f v = true` for all values `v` in `s`. -/
def all (f : ∀ x, β x → Bool) (s : Finmap β) : Bool :=
  s.foldl (fun x y z => x && f y z)
    (fun _ _ _ _ => by simp_rw [Bool.and_assoc, Bool.and_comm, imp_true_iff]) true

/-! ### erase -/

section

variable [DecidableEq α]

/-- Erase a key from the map. If the key is not present it does nothing. -/
def erase (a : α) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.erase a t)) fun _ _ p => toFinmap_eq.2 <| perm_erase p

@[simp]
theorem erase_toFinmap (a : α) (s : AList β) : erase a ⟦s⟧ = AList.toFinmap (s.erase a) := by
  simp [erase]

@[simp]
theorem keys_erase_toFinset (a : α) (s : AList β) : keys ⟦s.erase a⟧ = (keys ⟦s⟧).erase a := by
  simp [Finset.erase, keys, AList.erase, keys_kerase]

@[simp]
theorem keys_erase (a : α) (s : Finmap β) : (erase a s).keys = s.keys.erase a :=
  induction_on s fun s => by simp

@[simp]
theorem mem_erase {a a' : α} {s : Finmap β} : a' ∈ erase a s ↔ a' ≠ a ∧ a' ∈ s :=
  induction_on s fun s => by simp

theorem notMem_erase_self {a : α} {s : Finmap β} : a ∉ erase a s := by
  rw [mem_erase, not_and_or, not_not]
  left
  rfl

@[deprecated (since := "2025-05-23")] alias not_mem_erase_self := notMem_erase_self

@[simp]
theorem lookup_erase (a) (s : Finmap β) : lookup a (erase a s) = none :=
  induction_on s <| AList.lookup_erase a

@[simp]
theorem lookup_erase_ne {a a'} {s : Finmap β} (h : a ≠ a') : lookup a (erase a' s) = lookup a s :=
  induction_on s fun _ => AList.lookup_erase_ne h

theorem erase_erase {a a' : α} {s : Finmap β} : erase a (erase a' s) = erase a' (erase a s) :=
  induction_on s fun s => ext (by simp only [AList.erase_erase, erase_toFinmap])

/-! ### sdiff -/

/-- `sdiff s s'` consists of all key-value pairs from `s` and `s'` where the keys are in `s` or
`s'` but not both. -/
def sdiff (s s' : Finmap β) : Finmap β :=
  s'.foldl (fun s x _ => s.erase x) (fun _ _ _ _ _ => erase_erase) s

instance : SDiff (Finmap β) :=
  ⟨sdiff⟩

/-! ### insert -/

/-- Insert a key-value pair into a finite map, replacing any existing pair with
  the same key. -/
def insert (a : α) (b : β a) (s : Finmap β) : Finmap β :=
  (liftOn s fun t => AList.toFinmap (AList.insert a b t)) fun _ _ p =>
    toFinmap_eq.2 <| perm_insert p

@[simp]
theorem insert_toFinmap (a : α) (b : β a) (s : AList β) :
    insert a b (AList.toFinmap s) = AList.toFinmap (s.insert a b) := by
  simp [insert]

theorem entries_insert_of_notMem {a : α} {b : β a} {s : Finmap β} :
    a ∉ s → (insert a b s).entries = ⟨a, b⟩ ::ₘ s.entries :=
  induction_on s fun s h => by
    simp [AList.entries_insert_of_notMem (mt mem_toFinmap.1 h), -entries_insert]

@[deprecated (since := "2025-05-23")] alias entries_insert_of_not_mem := entries_insert_of_notMem

@[simp]
theorem mem_insert {a a' : α} {b' : β a'} {s : Finmap β} : a ∈ insert a' b' s ↔ a = a' ∨ a ∈ s :=
  induction_on s AList.mem_insert

@[simp]
theorem lookup_insert {a} {b : β a} (s : Finmap β) : lookup a (insert a b s) = some b :=
  induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, AList.lookup_insert]

@[simp]
theorem lookup_insert_of_ne {a a'} {b : β a} (s : Finmap β) (h : a' ≠ a) :
    lookup a' (insert a b s) = lookup a' s :=
  induction_on s fun s => by simp only [insert_toFinmap, lookup_toFinmap, lookup_insert_ne h]

@[simp]
theorem insert_insert {a} {b b' : β a} (s : Finmap β) :
    (s.insert a b).insert a b' = s.insert a b' :=
  induction_on s fun s => by simp only [insert_toFinmap, AList.insert_insert]

theorem insert_insert_of_ne {a a'} {b : β a} {b' : β a'} (s : Finmap β) (h : a ≠ a') :
    (s.insert a b).insert a' b' = (s.insert a' b').insert a b :=
  induction_on s fun s => by
    simp only [insert_toFinmap, AList.toFinmap_eq, AList.insert_insert_of_ne _ h]

theorem toFinmap_cons (a : α) (b : β a) (xs : List (Sigma β)) :
    List.toFinmap (⟨a, b⟩ :: xs) = insert a b xs.toFinmap :=
  rfl

theorem mem_list_toFinmap (a : α) (xs : List (Sigma β)) :
    a ∈ xs.toFinmap ↔ ∃ b : β a, Sigma.mk a b ∈ xs := by
  induction xs with
  | nil => simp only [toFinmap_nil, notMem_empty, not_mem_nil, exists_false]
  | cons x xs =>
    obtain ⟨fst_i, snd_i⟩ := x
    simp only [toFinmap_cons, *, exists_or, mem_cons, mem_insert, exists_and_left, Sigma.mk.inj_iff]
    refine (or_congr_left <| and_iff_left_of_imp ?_).symm
    rintro rfl
    simp only [exists_eq, heq_iff_eq]

@[simp]
theorem insert_singleton_eq {a : α} {b b' : β a} : insert a b (singleton a b') = singleton a b := by
  simp only [singleton, Finmap.insert_toFinmap, AList.insert_singleton_eq]

/-! ### extract -/

/-- Erase a key from the map, and return the corresponding value, if found. -/
def extract (a : α) (s : Finmap β) : Option (β a) × Finmap β :=
  (liftOn s fun t => Prod.map id AList.toFinmap (AList.extract a t)) fun s₁ s₂ p => by
    simp [perm_lookup p, toFinmap_eq, perm_erase p]

@[simp]
theorem extract_eq_lookup_erase (a : α) (s : Finmap β) : extract a s = (lookup a s, erase a s) :=
  induction_on s fun s => by simp [extract]

/-! ### union -/

/-- `s₁ ∪ s₂` is the key-based union of two finite maps. It is left-biased: if
there exists an `a ∈ s₁`, `lookup a (s₁ ∪ s₂) = lookup a s₁`. -/
def union (s₁ s₂ : Finmap β) : Finmap β :=
  (liftOn₂ s₁ s₂ fun s₁ s₂ => (AList.toFinmap (s₁ ∪ s₂))) fun _ _ _ _ p₁₃ p₂₄ =>
    toFinmap_eq.mpr <| perm_union p₁₃ p₂₄

instance : Union (Finmap β) :=
  ⟨union⟩

@[simp]
theorem mem_union {a} {s₁ s₂ : Finmap β} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_union

@[simp]
theorem union_toFinmap (s₁ s₂ : AList β) : (toFinmap s₁) ∪ (toFinmap s₂) = toFinmap (s₁ ∪ s₂) := by
  simp [(· ∪ ·), union]

theorem keys_union {s₁ s₂ : Finmap β} : (s₁ ∪ s₂).keys = s₁.keys ∪ s₂.keys :=
  induction_on₂ s₁ s₂ fun s₁ s₂ => Finset.ext <| by simp [keys]

@[simp]
theorem lookup_union_left {a} {s₁ s₂ : Finmap β} : a ∈ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₁ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_left

@[simp]
theorem lookup_union_right {a} {s₁ s₂ : Finmap β} : a ∉ s₁ → lookup a (s₁ ∪ s₂) = lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.lookup_union_right

theorem lookup_union_left_of_not_in {a} {s₁ s₂ : Finmap β} (h : a ∉ s₂) :
    lookup a (s₁ ∪ s₂) = lookup a s₁ := by
  by_cases h' : a ∈ s₁
  · rw [lookup_union_left h']
  · rw [lookup_union_right h', lookup_eq_none.mpr h, lookup_eq_none.mpr h']

/-- `simp`-normal form of `mem_lookup_union` -/
@[simp]
theorem mem_lookup_union' {a} {b : β a} {s₁ s₂ : Finmap β} :
    lookup a (s₁ ∪ s₂) = some b ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

theorem mem_lookup_union {a} {b : β a} {s₁ s₂ : Finmap β} :
    b ∈ lookup a (s₁ ∪ s₂) ↔ b ∈ lookup a s₁ ∨ a ∉ s₁ ∧ b ∈ lookup a s₂ :=
  induction_on₂ s₁ s₂ fun _ _ => AList.mem_lookup_union

theorem mem_lookup_union_middle {a} {b : β a} {s₁ s₂ s₃ : Finmap β} :
    b ∈ lookup a (s₁ ∪ s₃) → a ∉ s₂ → b ∈ lookup a (s₁ ∪ s₂ ∪ s₃) :=
  induction_on₃ s₁ s₂ s₃ fun _ _ _ => AList.mem_lookup_union_middle

theorem insert_union {a} {b : β a} {s₁ s₂ : Finmap β} : insert a b (s₁ ∪ s₂) = insert a b s₁ ∪ s₂ :=
  induction_on₂ s₁ s₂ fun a₁ a₂ => by simp [AList.insert_union]

theorem union_assoc {s₁ s₂ s₃ : Finmap β} : s₁ ∪ s₂ ∪ s₃ = s₁ ∪ (s₂ ∪ s₃) :=
  induction_on₃ s₁ s₂ s₃ fun s₁ s₂ s₃ => by
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_assoc]

@[simp]
theorem empty_union {s₁ : Finmap β} : ∅ ∪ s₁ = s₁ :=
  induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

@[simp]
theorem union_empty {s₁ : Finmap β} : s₁ ∪ ∅ = s₁ :=
  induction_on s₁ fun s₁ => by
    rw [← empty_toFinmap]
    simp [-empty_toFinmap, union_toFinmap]

theorem erase_union_singleton (a : α) (b : β a) (s : Finmap β) (h : s.lookup a = some b) :
    s.erase a ∪ singleton a b = s :=
  ext_lookup fun x => by
    by_cases h' : x = a
    · subst a
      rw [lookup_union_right notMem_erase_self, lookup_singleton_eq, h]
    · have : x ∉ singleton a b := by rwa [mem_singleton]
      rw [lookup_union_left_of_not_in this, lookup_erase_ne h']

end

/-! ### Disjoint -/

/-- `Disjoint s₁ s₂` holds if `s₁` and `s₂` have no keys in common. -/
def Disjoint (s₁ s₂ : Finmap β) : Prop :=
  ∀ x ∈ s₁, x ∉ s₂

theorem disjoint_empty (x : Finmap β) : Disjoint ∅ x :=
  nofun

@[symm]
theorem Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjoint y x := fun p hy hx => h p hx hy

theorem Disjoint.symm_iff (x y : Finmap β) : Disjoint x y ↔ Disjoint y x :=
  ⟨Disjoint.symm x y, Disjoint.symm y x⟩

section

variable [DecidableEq α]

instance : DecidableRel (@Disjoint α β) := fun x y => by dsimp only [Disjoint]; infer_instance

theorem disjoint_union_left (x y z : Finmap β) :
    Disjoint (x ∪ y) z ↔ Disjoint x z ∧ Disjoint y z := by
  simp [Disjoint, Finmap.mem_union, or_imp, forall_and]

theorem disjoint_union_right (x y z : Finmap β) :
    Disjoint x (y ∪ z) ↔ Disjoint x y ∧ Disjoint x z := by
  rw [Disjoint.symm_iff, disjoint_union_left, Disjoint.symm_iff _ x, Disjoint.symm_iff _ x]

theorem union_comm_of_disjoint {s₁ s₂ : Finmap β} : Disjoint s₁ s₂ → s₁ ∪ s₂ = s₂ ∪ s₁ :=
  induction_on₂ s₁ s₂ fun s₁ s₂ => by
    intro h
    simp only [AList.toFinmap_eq, union_toFinmap, AList.union_comm_of_disjoint h]

theorem union_cancel {s₁ s₂ s₃ : Finmap β} (h : Disjoint s₁ s₃) (h' : Disjoint s₂ s₃) :
    s₁ ∪ s₃ = s₂ ∪ s₃ ↔ s₁ = s₂ :=
  ⟨fun h'' => by
    apply ext_lookup
    intro x
    have : (s₁ ∪ s₃).lookup x = (s₂ ∪ s₃).lookup x := h'' ▸ rfl
    by_cases hs₁ : x ∈ s₁
    · rwa [lookup_union_left hs₁, lookup_union_left_of_not_in (h _ hs₁)] at this
    · by_cases hs₂ : x ∈ s₂
      · rwa [lookup_union_left_of_not_in (h' _ hs₂), lookup_union_left hs₂] at this
      · rw [lookup_eq_none.mpr hs₁, lookup_eq_none.mpr hs₂], fun h => h ▸ rfl⟩

end

end Finmap
