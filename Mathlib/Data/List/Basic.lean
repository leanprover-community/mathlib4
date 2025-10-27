/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Control.Basic
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Monad
import Mathlib.Logic.OpClass
import Mathlib.Logic.Unique
import Mathlib.Tactic.Common

/-!
# Basic properties of lists
-/

assert_not_exists Lattice
assert_not_exists Monoid
assert_not_exists Preorder
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

/-- There is only one list of an empty type -/
instance uniqueOfIsEmpty [IsEmpty α] : Unique (List α) :=
  { instInhabitedList with
    uniq := fun l =>
      match l with
      | [] => rfl
      | a :: _ => isEmptyElim a }

instance : Std.LawfulIdentity (α := List α) Append.append [] where
  left_id := nil_append
  right_id := append_nil

instance : Std.Associative (α := List α) Append.append where
  assoc := append_assoc

@[simp] theorem cons_injective {a : α} : Injective (cons a) := fun _ _ => tail_eq_of_cons_eq

theorem singleton_injective : Injective fun a : α => [a] := fun _ _ h => (cons_eq_cons.1 h).1

theorem set_of_mem_cons (l : List α) (a : α) : { x | x ∈ a :: l } = insert a { x | x ∈ l } :=
  Set.ext fun _ => mem_cons

/-! ### mem -/

theorem _root_.Decidable.List.eq_or_ne_mem_of_mem [DecidableEq α]
    {a b : α} {l : List α} (h : a ∈ b :: l) : a = b ∨ a ≠ b ∧ a ∈ l := by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact ((List.mem_cons.1 h).elim Or.inl (fun h => Or.inr ⟨hab, h⟩))

lemma mem_pair {a b c : α} : a ∈ [b, c] ↔ a = b ∨ a = c := by
  rw [mem_cons, mem_singleton]


-- The simpNF linter says that the LHS can be simplified via `List.mem_map`.
-- However this is a higher priority lemma.
-- It seems the side condition `hf` is not applied by `simpNF`.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
    f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem⟩

@[simp]
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff {f : α → α}
    (hf : Function.Involutive f) (x : α) (l : List α) : (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩

theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
    a ∈ map f l ↔ f a ∈ l := by rw [mem_map, hf.exists_mem_and_apply_eq_iff]

/-! ### length -/

alias ⟨_, length_pos_of_ne_nil⟩ := length_pos_iff

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

theorem exists_of_length_succ {n} : ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
  | [], H => absurd H.symm <| succ_ne_zero n
  | h :: t, _ => ⟨h, t, rfl⟩

@[simp] lemma length_injective_iff : Injective (List.length : List α → ℕ) ↔ Subsingleton α := by
  constructor
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intro hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    · next ih _ _ =>
      congr
      · subsingleton
      · apply ih; simpa using hl

@[simp default + 1] -- Raise priority above `length_injective_iff`.
lemma length_injective [Subsingleton α] : Injective (length : List α → ℕ) :=
  length_injective_iff.mpr inferInstance

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩

theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] :=
  ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩

/-! ### set-theoretic notation of lists -/

instance instSingletonList : Singleton α (List α) := ⟨fun x => [x]⟩

instance [DecidableEq α] : Insert α (List α) := ⟨List.insert⟩

instance [DecidableEq α] : LawfulSingleton α (List α) :=
  { insert_empty_eq := fun x =>
      show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg not_mem_nil }

theorem singleton_eq (x : α) : ({x} : List α) = [x] :=
  rfl

theorem insert_neg [DecidableEq α] {x : α} {l : List α} (h : x ∉ l) :
    Insert.insert x l = x :: l :=
  insert_of_not_mem h

theorem insert_pos [DecidableEq α] {x : α} {l : List α} (h : x ∈ l) : Insert.insert x l = l :=
  insert_of_mem h

theorem doubleton_eq [DecidableEq α] {x y : α} (h : x ≠ y) : ({x, y} : List α) = [x, y] := by
  rw [insert_neg, singleton_eq]
  rwa [singleton_eq, mem_singleton]

/-! ### bounded quantifiers over lists -/

theorem forall_mem_of_forall_mem_cons {p : α → Prop} {a : α} {l : List α} (h : ∀ x ∈ a :: l, p x) :
    ∀ x ∈ l, p x := (forall_mem_cons.1 h).2

theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ x ∈ a :: l, p x :=
  ⟨a, mem_cons_self, h⟩

theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ l, p x) →
    ∃ x ∈ a :: l, p x :=
  fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩

theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ a :: l, p x) →
    p a ∨ ∃ x ∈ l, p x := by grind

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x := by grind

/-! ### list subset -/

theorem cons_subset_of_subset_of_mem {a : α} {l m : List α}
    (ainm : a ∈ m) (lsubm : l ⊆ m) : a::l ⊆ m :=
  cons_subset.2 ⟨ainm, lsubm⟩

theorem append_subset_of_subset_of_subset {l₁ l₂ l : List α} (l₁subl : l₁ ⊆ l) (l₂subl : l₂ ⊆ l) :
    l₁ ++ l₂ ⊆ l :=
  fun _ h ↦ (mem_append.1 h).elim (@l₁subl _) (@l₂subl _)

theorem map_subset_iff {l₁ l₂ : List α} (f : α → β) (h : Injective f) :
    map f l₁ ⊆ map f l₂ ↔ l₁ ⊆ l₂ := by
  refine ⟨?_, map_subset f⟩; intro h2 x hx
  rcases mem_map.1 (h2 (mem_map_of_mem hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'

/-! ### append -/

theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl

theorem append_right_injective (s : List α) : Injective fun t ↦ s ++ t :=
  fun _ _ ↦ append_cancel_left

theorem append_left_injective (t : List α) : Injective fun s ↦ s ++ t :=
  fun _ _ ↦ append_cancel_right

/-! ### replicate -/

theorem eq_replicate_length {a : α} : ∀ {l : List α}, l = replicate l.length a ↔ ∀ b ∈ l, b = a
  | [] => by simp
  | (b :: l) => by simp [eq_replicate_length, replicate_succ]

theorem replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ replicate n a := by
  rw [replicate_append_replicate]

theorem replicate_subset_singleton (n) (a : α) : replicate n a ⊆ [a] := fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)

theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a := by
  simp only [eq_replicate_iff, subset_def, mem_singleton, exists_eq_left']

theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (@replicate α n) :=
  fun _ _ h => (eq_replicate_iff.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩

theorem replicate_right_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective hn).eq_iff

theorem replicate_right_inj' {a b : α} : ∀ {n},
    replicate n a = replicate n b ↔ n = 0 ∨ a = b
  | 0 => by simp
  | n + 1 => (replicate_right_inj n.succ_ne_zero).trans <| by simp only [n.succ_ne_zero, false_or]

theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (length_replicate (n := ·))

theorem replicate_left_inj {a : α} {n m : ℕ} : replicate n a = replicate m a ↔ n = m :=
  (replicate_left_injective a).eq_iff

@[simp]
theorem head?_flatten_replicate {n : ℕ} (h : n ≠ 0) (l : List α) :
    (List.replicate n l).flatten.head? = l.head? := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
  induction l <;> simp [replicate]

@[simp]
theorem getLast?_flatten_replicate {n : ℕ} (h : n ≠ 0) (l : List α) :
    (List.replicate n l).flatten.getLast? = l.getLast? := by
  rw [← List.head?_reverse, ← List.head?_reverse, List.reverse_flatten, List.map_replicate,
  List.reverse_replicate, head?_flatten_replicate h]

/-! ### pure -/

theorem mem_pure (x y : α) : x ∈ (pure y : List α) ↔ x = y := by simp

/-! ### bind -/

@[simp]
theorem bind_eq_flatMap {α β} (f : α → List β) (l : List α) : l >>= f = l.flatMap f :=
  rfl

/-! ### concat -/

/-! ### reverse -/

theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]

theorem reverse_concat' (l : List α) (a : α) : (l ++ [a]).reverse = a :: l.reverse := by
  rw [reverse_append]; rfl

@[simp]
theorem reverse_singleton (a : α) : reverse [a] = [a] :=
  rfl

@[simp]
theorem reverse_involutive : Involutive (@reverse α) :=
  reverse_reverse

@[simp]
theorem reverse_injective : Injective (@reverse α) :=
  reverse_involutive.injective

theorem reverse_surjective : Surjective (@reverse α) :=
  reverse_involutive.surjective

theorem reverse_bijective : Bijective (@reverse α) :=
  reverse_involutive.bijective

theorem concat_eq_reverse_cons (a : α) (l : List α) : concat l a = reverse (a :: reverse l) := by
  simp only [concat_eq_append, reverse_cons, reverse_reverse]

theorem map_reverseAux (f : α → β) (l₁ l₂ : List α) :
    map f (reverseAux l₁ l₂) = reverseAux (map f l₁) (map f l₂) := by
  simp only [reverseAux_eq, map_append, map_reverse]

-- TODO: Rename `List.reverse_perm` to `List.reverse_perm_self`
@[simp] lemma reverse_perm' : l₁.reverse ~ l₂ ↔ l₁ ~ l₂ where
  mp := l₁.reverse_perm.symm.trans
  mpr := l₁.reverse_perm.trans

@[simp] lemma perm_reverse : l₁ ~ l₂.reverse ↔ l₁ ~ l₂ where
  mp hl := hl.trans l₂.reverse_perm
  mpr hl := hl.trans l₂.reverse_perm.symm

/-! ### getLast -/

attribute [simp] getLast_cons

theorem getLast_append_singleton {a : α} (l : List α) :
    getLast (l ++ [a]) (append_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = a := by
  simp

theorem getLast_append_of_right_ne_nil (l₁ l₂ : List α) (h : l₂ ≠ []) :
    getLast (l₁ ++ l₂) (append_ne_nil_of_right_ne_nil l₁ h) = getLast l₂ h := by
  induction l₁ with grind

theorem getLast_concat' {a : α} (l : List α) : getLast (concat l a) (by simp) = a := by
  simp

@[simp]
theorem getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a := rfl

theorem dropLast_append_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [_], _ => rfl
  | a :: b :: l, h => by
    rw [dropLast_cons₂, cons_append, getLast_cons (cons_ne_nil _ _)]
    congr
    exact dropLast_append_getLast (cons_ne_nil b l)

theorem getLast_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
    getLast l₁ h₁ = getLast l₂ h₂ := by subst l₁; rfl

theorem getLast_replicate_succ (m : ℕ) (a : α) :
    (replicate (m + 1) a).getLast (ne_nil_of_length_eq_add_one length_replicate) = a := by
  simp only [replicate_succ']
  exact getLast_append_singleton _

/-! ### getLast? -/

theorem mem_getLast?_eq_getLast : ∀ {l : List α} {x : α}, x ∈ l.getLast? → ∃ h, x = getLast l h
  | [], x, hx
  | [a], x, hx
  | a :: b :: l, x, hx => by grind

theorem getLast?_eq_getLast_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.getLast? = some (l.getLast h)
  | [], h => (h rfl).elim
  | [_], _ => rfl
  | _ :: b :: l, _ => @getLast?_eq_getLast_of_ne_nil (b :: l) (cons_ne_nil _ _)

theorem mem_getLast?_cons {x y : α} : ∀ {l : List α}, x ∈ l.getLast? → x ∈ (y :: l).getLast?
  | [], _ => by contradiction
  | _ :: _, h => h

theorem dropLast_append_getLast? : ∀ {l : List α}, ∀ a ∈ l.getLast?, dropLast l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [getLast?_cons_cons] at hc
    rw [dropLast_cons₂, cons_append, dropLast_append_getLast? _ hc]

theorem getLastI_eq_getLast? [Inhabited α] : ∀ l : List α, l.getLastI = l.getLast?.iget
  | [] => by simp [getLastI]
  | [_] => rfl
  | [_, _] => rfl
  | [_, _, _] => rfl
  | _ :: _ :: c :: l => by simp [getLastI, getLastI_eq_getLast? (c :: l)]

theorem getLast?_append_cons :
    ∀ (l₁ : List α) (a : α) (l₂ : List α), getLast? (l₁ ++ a :: l₂) = getLast? (a :: l₂)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, getLast?_cons_cons,
    ← cons_append, getLast?_append_cons (c :: l₁)]

theorem getLast?_append_of_ne_nil (l₁ : List α) :
    ∀ {l₂ : List α} (_ : l₂ ≠ []), getLast? (l₁ ++ l₂) = getLast? l₂
  | [], hl₂ => by contradiction
  | b :: l₂, _ => getLast?_append_cons l₁ b l₂

theorem mem_getLast?_append_of_mem_getLast? {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.getLast?) :
    x ∈ (l₁ ++ l₂).getLast? := by grind

/-! ### head(!?) and tail -/

@[simp]
theorem head!_nil [Inhabited α] : ([] : List α).head! = default := rfl

@[deprecated cons_head_tail (since := "2025-08-15")]
theorem head_cons_tail (x : List α) (h : x ≠ []) : x.head h :: x.tail = x := by simp

theorem head_eq_getElem_zero {l : List α} (hl : l ≠ []) :
    l.head hl = l[0]'(length_pos_iff.2 hl) :=
  (getElem_zero _).symm

theorem head!_eq_head? [Inhabited α] (l : List α) : head! l = (head? l).iget := by cases l <;> rfl

theorem surjective_head! [Inhabited α] : Surjective (@head! α _) := fun x => ⟨[x], rfl⟩

theorem surjective_head? : Surjective (@head? α) :=
  Option.forall.2 ⟨⟨[], rfl⟩, fun x => ⟨[x], rfl⟩⟩

theorem surjective_tail : Surjective (@tail α)
  | [] => ⟨[], rfl⟩
  | a :: l => ⟨a :: a :: l, rfl⟩

theorem eq_cons_of_mem_head? {x : α} : ∀ {l : List α}, x ∈ l.head? → l = x :: tail l
  | [], h => (Option.not_mem_none _ h).elim
  | a :: l, h => by
    simp only [head?, Option.mem_def, Option.some_inj] at h
    exact h ▸ rfl

@[simp] theorem head!_cons [Inhabited α] (a : α) (l : List α) : head! (a :: l) = a := rfl

@[simp]
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
    head! (s ++ t) = head! s := by
  induction s
  · contradiction
  · rfl

theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x ∈ s.head?) :
    x ∈ (s ++ t).head? := by
  grind [Option.mem_def]

theorem head?_append_of_ne_nil :
    ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []), head? (l₁ ++ l₂) = head? l₁
  | _ :: _, _, _ => rfl

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
    tail (l ++ [a]) = tail l ++ [a] := by grind

theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ head? l → a :: tail l = l
  | [], a, h => by contradiction
  | b :: l, a, h => by
    have : b = a := by simpa using h
    simp [this]

theorem head!_mem_head? [Inhabited α] : ∀ {l : List α}, l ≠ [] → head! l ∈ head? l
  | [], h => by contradiction
  | _ :: _, _ => rfl

theorem cons_head!_tail [Inhabited α] {l : List α} (h : l ≠ []) : head! l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)

theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  have h' : l.head! ∈ l.head! :: l.tail := mem_cons_self
  rwa [cons_head!_tail h] at h'

theorem get_eq_getElem? (l : List α) (i : Fin l.length) :
    l.get i = l[i]?.get (by simp) := by
  simp

theorem exists_mem_iff_getElem {l : List α} {p : α → Prop} :
    (∃ x ∈ l, p x) ↔ ∃ (i : ℕ) (_ : i < l.length), p l[i] := by
  simp only [mem_iff_getElem]
  exact ⟨fun ⟨_x, ⟨i, hi, hix⟩, hxp⟩ ↦ ⟨i, hi, hix ▸ hxp⟩, fun ⟨i, hi, hp⟩ ↦ ⟨_, ⟨i, hi, rfl⟩, hp⟩⟩

theorem forall_mem_iff_getElem {l : List α} {p : α → Prop} :
    (∀ x ∈ l, p x) ↔ ∀ (i : ℕ) (_ : i < l.length), p l[i] := by
  simp [mem_iff_getElem, @forall_swap α]

@[simp]
theorem get_surjective_iff {l : List α} : l.get.Surjective ↔ (∀ x, x ∈ l) :=
  forall_congr' fun _ ↦ mem_iff_get.symm

@[simp]
theorem getElem_fin_surjective_iff {l : List α} :
    (fun (n : Fin l.length) ↦ l[n.val]).Surjective ↔ (∀ x, x ∈ l) :=
  get_surjective_iff

@[simp]
theorem getElem?_surjective_iff {l : List α} : (fun (n : ℕ) ↦ l[n]?).Surjective ↔ (∀ x, x ∈ l) := by
  refine ⟨fun h x ↦ mem_iff_getElem?.mpr <| h x, fun h x ↦ ?_⟩
  cases x with
  | none => exact ⟨l.length, getElem?_eq_none <| Nat.le_refl _⟩
  | some x => exact mem_iff_getElem?.mp <| h x

theorem get_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length := (by simp only [length_tail] at h; cutsat)) :
    l.tail.get ⟨i, h⟩ = l.get ⟨i + 1, h'⟩ := by
  simp

/-! ### sublists -/

attribute [refl] List.Sublist.refl

theorem Sublist.cons_cons {l₁ l₂ : List α} (a : α) (s : l₁ <+ l₂) : a :: l₁ <+ a :: l₂ :=
  Sublist.cons₂ _ s

lemma cons_sublist_cons' {a b : α} : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂ := by
  grind

theorem sublist_cons_of_sublist (a : α) (h : l₁ <+ l₂) : l₁ <+ a :: l₂ := h.cons _

@[simp] lemma sublist_singleton {l : List α} {a : α} : l <+ [a] ↔ l = [] ∨ l = [a] := by
  constructor <;> rintro (_ | _) <;> aesop

theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le

/-- If the first element of two lists are different, then a sublist relation can be reduced. -/
theorem Sublist.of_cons_of_ne {a b} (h₁ : a ≠ b) (h₂ : a :: l₁ <+ b :: l₂) : a :: l₁ <+ l₂ :=
  match h₁, h₂ with
  | _, .cons _ h => h

/-! ### indexOf -/

section IndexOf

variable [DecidableEq α]

theorem idxOf_cons_eq {a b : α} (l : List α) : b = a → idxOf a (b :: l) = 0
  | e => by rw [← e]; exact idxOf_cons_self

@[simp]
theorem idxOf_cons_ne {a b : α} (l : List α) : b ≠ a → idxOf a (b :: l) = succ (idxOf a l)
  | h => by simp only [idxOf_cons, Bool.cond_eq_ite, beq_iff_eq, if_neg h]

theorem idxOf_eq_length_iff {a : α} {l : List α} : idxOf a l = length l ↔ a ∉ l := by
  grind

@[simp]
theorem idxOf_of_notMem {l : List α} {a : α} : a ∉ l → idxOf a l = length l :=
  idxOf_eq_length_iff.2

@[deprecated (since := "2025-05-23")] alias idxOf_of_not_mem := idxOf_of_notMem

theorem idxOf_append_of_mem {a : α} (h : a ∈ l₁) : idxOf a (l₁ ++ l₂) = idxOf a l₁ := by grind

theorem idxOf_append_of_notMem {a : α} (h : a ∉ l₁) :
    idxOf a (l₁ ++ l₂) = l₁.length + idxOf a l₂ := by grind

@[deprecated (since := "2025-05-23")] alias idxOf_append_of_not_mem := idxOf_append_of_notMem

end IndexOf

/-! ### nth element -/

section deprecated

theorem getElem?_length (l : List α) : l[l.length]? = none := getElem?_eq_none (Nat.le_refl _)

/-- A version of `getElem_map` that can be used for rewriting. -/
theorem getElem_map_rev (f : α → β) {l} {n : Nat} {h : n < l.length} :
    f l[n] = (map f l)[n]'((l.length_map f).symm ▸ h) := Eq.symm (getElem_map _)

theorem get_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.get ⟨l.length - 1, h⟩ = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
  (getLast_eq_getElem _).symm

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  rw [drop_eq_getElem_cons h, take, take]
  simp

theorem ext_getElem?' {l₁ l₂ : List α} (h' : ∀ n < max l₁.length l₂.length, l₁[n]? = l₂[n]?) :
    l₁ = l₂ := by
  apply ext_getElem?
  grind

theorem ext_get_iff {l₁ l₂ : List α} :
    l₁ = l₂ ↔ l₁.length = l₂.length ∧ ∀ n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩ := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ _ ↦ rfl⟩
  · intro ⟨h₁, h₂⟩
    exact ext_get h₁ h₂

theorem ext_getElem?_iff' {l₁ l₂ : List α} : l₁ = l₂ ↔
    ∀ n < max l₁.length l₂.length, l₁[n]? = l₂[n]? :=
  ⟨by rintro rfl _ _; rfl, ext_getElem?'⟩

/-- If two lists `l₁` and `l₂` are the same length and `l₁[n]! = l₂[n]!` for all `n`,
then the lists are equal. -/
theorem ext_getElem! [Inhabited α] (hl : length l₁ = length l₂) (h : ∀ n : ℕ, l₁[n]! = l₂[n]!) :
    l₁ = l₂ :=
  ext_getElem hl fun n h₁ h₂ ↦ by simpa only [← getElem!_pos] using h n

@[simp]
theorem getElem_idxOf [DecidableEq α] {a : α} : ∀ {l : List α} (h : idxOf a l < l.length),
    l[idxOf a l] = a
  | b :: l, h => by
    by_cases h' : b = a <;>
    simp [h', getElem_idxOf]

-- This is incorrectly named and should be `get_idxOf`;
-- this already exists, so will require a deprecation dance.
theorem idxOf_get [DecidableEq α] {a : α} {l : List α} (h) : get l ⟨idxOf a l, h⟩ = a := by
  simp

@[simp]
theorem getElem?_idxOf [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    l[idxOf a l]? = some a := by
  rw [getElem?_eq_getElem (idxOf_lt_length_iff.2 h), getElem_idxOf]

theorem idxOf_inj [DecidableEq α] {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    idxOf x l = idxOf y l ↔ x = y :=
  ⟨fun h => by
    have x_eq_y :
        get l ⟨idxOf x l, idxOf_lt_length_iff.2 hx⟩ =
        get l ⟨idxOf y l, idxOf_lt_length_iff.2 hy⟩ := by
      simp only [h]
    simp only [idxOf_get] at x_eq_y; exact x_eq_y, fun h => by subst h; rfl⟩

theorem get_reverse' (l : List α) (n) (hn') :
    l.reverse.get n = l.get ⟨l.length - 1 - n, hn'⟩ := by
  simp

theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) : l = [l.get ⟨0, by omega⟩] := by
  refine ext_get (by convert h) (by grind)

end deprecated

theorem getElem_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a)[j] = l[j]'(by simpa using hj) := by
  simp [h]

/-! ### map -/

-- `List.map_const` (the version with `Function.const` instead of a lambda) is already tagged
-- `simp` in Core
-- TODO: Upstream the tagging to Core?
attribute [simp] map_const'

theorem flatMap_pure_eq_map (f : α → β) (l : List α) : l.flatMap (pure ∘ f) = map f l :=
  .symm <| map_eq_flatMap ..

theorem flatMap_congr {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g :=
  (congr_arg List.flatten <| map_congr_left h :)

theorem infix_flatMap_of_mem {a : α} {as : List α} (h : a ∈ as) (f : α → List α) :
    f a <:+: as.flatMap f :=
  infix_of_mem_flatten (mem_map_of_mem h)

@[simp]
theorem map_eq_map {α β} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl

/-- A single `List.map` of a composition of functions is equal to
composing a `List.map` with another `List.map`, fully applied.
This is the reverse direction of `List.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  map_map.symm

/-- Composing a `List.map` with another `List.map` is equal to
a single `List.map` of composed functions.
-/
@[simp]
theorem map_comp_map (g : β → γ) (f : α → β) : map g ∘ map f = map (g ∘ f) := by
  ext l; rw [comp_map, Function.comp_apply]

section map_bijectivity

theorem _root_.Function.LeftInverse.list_map {f : α → β} {g : β → α} (h : LeftInverse f g) :
    LeftInverse (map f) (map g)
  | [] => by simp_rw [map_nil]
  | x :: xs => by simp_rw [map_cons, h x, h.list_map xs]

nonrec theorem _root_.Function.RightInverse.list_map {f : α → β} {g : β → α}
    (h : RightInverse f g) : RightInverse (map f) (map g) :=
  h.list_map

nonrec theorem _root_.Function.Involutive.list_map {f : α → α}
    (h : Involutive f) : Involutive (map f) :=
  Function.LeftInverse.list_map h

@[simp]
theorem map_leftInverse_iff {f : α → β} {g : β → α} :
    LeftInverse (map f) (map g) ↔ LeftInverse f g :=
  ⟨fun h x => by injection h [x], (·.list_map)⟩

@[simp]
theorem map_rightInverse_iff {f : α → β} {g : β → α} :
    RightInverse (map f) (map g) ↔ RightInverse f g := map_leftInverse_iff

@[simp]
theorem map_involutive_iff {f : α → α} :
    Involutive (map f) ↔ Involutive f := map_leftInverse_iff

theorem _root_.Function.Injective.list_map {f : α → β} (h : Injective f) :
    Injective (map f)
  | [], [], _ => rfl
  | x :: xs, y :: ys, hxy => by
    injection hxy with hxy hxys
    rw [h hxy, h.list_map hxys]

@[simp]
theorem map_injective_iff {f : α → β} : Injective (map f) ↔ Injective f := by
  refine ⟨fun h x y hxy => ?_, (·.list_map)⟩
  suffices [x] = [y] by simpa using this
  apply h
  simp [hxy]

theorem _root_.Function.Surjective.list_map {f : α → β} (h : Surjective f) :
    Surjective (map f) :=
  let ⟨_, h⟩ := h.hasRightInverse; h.list_map.surjective

@[simp]
theorem map_surjective_iff {f : α → β} : Surjective (map f) ↔ Surjective f := by
  refine ⟨fun h x => ?_, (·.list_map)⟩
  let ⟨[y], hxy⟩ := h [x]
  exact ⟨_, List.singleton_injective hxy⟩

theorem _root_.Function.Bijective.list_map {f : α → β} (h : Bijective f) : Bijective (map f) :=
  ⟨h.1.list_map, h.2.list_map⟩

@[simp]
theorem map_bijective_iff {f : α → β} : Bijective (map f) ↔ Bijective f := by
  simp_rw [Function.Bijective, map_injective_iff, map_surjective_iff]

end map_bijectivity

theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (const α b₂) l) :
    b₁ = b₂ := by rw [map_const] at h; exact eq_of_mem_replicate h

/-- `eq_nil_or_concat` in simp normal form -/
lemma eq_nil_or_concat' (l : List α) : l = [] ∨ ∃ L b, l = L ++ [b] := by
  simpa using l.eq_nil_or_concat

/-! ### foldl, foldr -/

theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
    foldl f a l = foldl g a l := by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin, H a hd mem_cons_self]

theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction l with | nil => rfl | cons hd tl ih => ?_
  simp only [mem_cons, or_imp, forall_and, forall_eq] at H
  simp only [foldr, ih H.2, H.1]

theorem foldl_concat
    (f : β → α → β) (b : β) (x : α) (xs : List α) :
    List.foldl f b (xs ++ [x]) = f (List.foldl f b xs) x := by
  simp only [List.foldl_append, List.foldl]

theorem foldr_concat
    (f : α → β → β) (b : β) (x : α) (xs : List α) :
    List.foldr f b (xs ++ [x]) = (List.foldr f (f x b) xs) := by
  simp only [List.foldr_append, List.foldr]

theorem foldl_fixed' {f : α → β → α} {a : α} (hf : ∀ b, f a b = a) : ∀ l : List β, foldl f a l = a
  | [] => rfl
  | b :: l => by rw [foldl_cons, hf b, foldl_fixed' hf l]

theorem foldr_fixed' {f : α → β → β} {b : β} (hf : ∀ a, f a b = b) : ∀ l : List α, foldr f b l = b
  | [] => rfl
  | a :: l => by rw [foldr_cons, foldr_fixed' hf l, hf a]

@[simp]
theorem foldl_fixed {a : α} : ∀ l : List β, foldl (fun a _ => a) a l = a :=
  foldl_fixed' fun _ => rfl

@[simp]
theorem foldr_fixed {b : β} : ∀ l : List α, foldr (fun _ b => b) b l = b :=
  foldr_fixed' fun _ => rfl

@[deprecated foldr_cons_nil (since := "2025-02-10")]
theorem foldr_eta (l : List α) : foldr cons [] l = l := foldr_cons_nil

theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  simp

theorem foldl_hom₂ (l : List ι) (f : α → β → γ) (op₁ : α → ι → α) (op₂ : β → ι → β)
    (op₃ : γ → ι → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ a i) (op₂ b i) = op₃ (f a b) i) :
    foldl op₃ (f a b) l = f (foldl op₁ a l) (foldl op₂ b l) :=
  Eq.symm <| by
    revert a b
    induction l <;> intros <;> [rfl; simp only [*, foldl]]

theorem foldr_hom₂ (l : List ι) (f : α → β → γ) (op₁ : ι → α → α) (op₂ : ι → β → β)
    (op₃ : ι → γ → γ) (a : α) (b : β) (h : ∀ a b i, f (op₁ i a) (op₂ i b) = op₃ i (f a b)) :
    foldr op₃ (f a b) l = f (foldr op₁ a l) (foldr op₂ b l) := by
  revert a
  induction l <;> intros <;> [rfl; simp only [*, foldr]]

theorem injective_foldl_comp {l : List (α → α)} {f : α → α}
    (hl : ∀ f ∈ l, Function.Injective f) (hf : Function.Injective f) :
    Function.Injective (@List.foldl (α → α) (α → α) Function.comp f l) := by
  induction l generalizing f with
  | nil => exact hf
  | cons lh lt l_ih =>
    apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ mem_cons_self

/-- Consider two lists `l₁` and `l₂` with designated elements `a₁` and `a₂` somewhere in them:
`l₁ = x₁ ++ [a₁] ++ z₁` and `l₂ = x₂ ++ [a₂] ++ z₂`.
Assume the designated element `a₂` is present in neither `x₁` nor `z₁`.
We conclude that the lists are equal (`l₁ = l₂`) if and only if their respective parts are equal
(`x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂`). -/
lemma append_cons_inj_of_notMem {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α}
    (notin_x : a₂ ∉ x₁) (notin_z : a₂ ∉ z₁) :
    x₁ ++ a₁ :: z₁ = x₂ ++ a₂ :: z₂ ↔ x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂ := by
  constructor
  · simp only [append_eq_append_iff, cons_eq_append_iff, cons_eq_cons]
    rintro (⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩ |
      ⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩) <;> simp_all
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

@[deprecated (since := "2025-05-23")] alias append_cons_inj_of_not_mem := append_cons_inj_of_notMem

section FoldlEqFoldr

-- foldl and foldr coincide when f is commutative and associative
variable {f : α → α → α}

theorem foldl1_eq_foldr1 [hassoc : Std.Associative f] :
    ∀ a b l, foldl f a (l ++ [b]) = foldr f b (a :: l)
  | _, _, nil => rfl
  | a, b, c :: l => by
    simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 _ _ l]
    rw [hassoc.assoc]

theorem foldl_eq_of_comm_of_assoc [hcomm : Std.Commutative f] [hassoc : Std.Associative f] :
    ∀ a b l, foldl f a (b :: l) = f b (foldl f a l)
  | a, b, nil => hcomm.comm a b
  | a, b, c :: l => by
    simp only [foldl_cons]
    have : RightCommutative f := inferInstance
    rw [← foldl_eq_of_comm_of_assoc .., this.right_comm, foldl_cons]

theorem foldl_eq_foldr [Std.Commutative f] [Std.Associative f] :
    ∀ a l, foldl f a l = foldr f a l
  | _, nil => rfl
  | a, b :: l => by
    simp only [foldr_cons, foldl_eq_of_comm_of_assoc]
    rw [foldl_eq_foldr a l]

end FoldlEqFoldr

section FoldlEqFoldr'

variable {f : α → β → α}
variable (hf : ∀ a b c, f (f a b) c = f (f a c) b)

include hf

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b :: l) = f (foldl f a l) b
  | _, _, [] => rfl
  | a, b, c :: l => by rw [foldl, foldl, foldl, ← foldl_eq_of_comm' .., foldl, hf]

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
  | _, [] => rfl
  | a, b :: l => by rw [foldl_eq_of_comm' hf, foldr, foldl_eq_foldr' ..]; rfl

end FoldlEqFoldr'

section FoldlEqFoldr'

variable {f : α → β → β}

theorem foldr_eq_of_comm' (hf : ∀ a b c, f a (f b c) = f b (f a c)) :
    ∀ a b l, foldr f a (b :: l) = foldr f (f b a) l
  | _, _, [] => rfl
  | a, b, c :: l => by rw [foldr, foldr, foldr, hf, ← foldr_eq_of_comm' hf ..]; rfl

end FoldlEqFoldr'

section

variable {op : α → α → α} [ha : Std.Associative op]

/-- Notation for `op a b`. -/
local notation a " ⋆ " b => op a b

-- Setting `priority := high` means that Lean will prefer this notation to the identical one
-- for `Seq.seq`
/-- Notation for `foldl op a l`. -/
local notation l " <*> " a => foldl op a l

theorem foldl_op_eq_op_foldr_assoc :
    ∀ {l : List α} {a₁ a₂}, ((l <*> a₁) ⋆ a₂) = a₁ ⋆ l.foldr (· ⋆ ·) a₂
  | [], _, _ => rfl
  | a :: l, a₁, a₂ => by
    simp only [foldl_cons, foldr_cons, foldl_assoc, ha.assoc]; rw [foldl_op_eq_op_foldr_assoc]

variable [hc : Std.Commutative op]

theorem foldl_assoc_comm_cons {l : List α} {a₁ a₂} : ((a₁ :: l) <*> a₂) = a₁ ⋆ l <*> a₂ := by
  rw [foldl_cons, hc.comm, foldl_assoc]

end

/-! ### foldlM, foldrM, mapM -/

section FoldlMFoldrM

variable {m : Type v → Type w} [Monad m]

variable [LawfulMonad m]

theorem foldrM_eq_foldr (f : α → β → m β) (b l) :
    foldrM f b l = foldr (fun a mb => mb >>= f a) (pure b) l := by induction l <;> simp [*]

theorem foldlM_eq_foldl (f : β → α → m β) (b l) :
    List.foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l := by
  suffices h :
    ∀ mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
    by simp [← h (pure b)]
  induction l with
  | nil => simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ← l_ih, functor_norm]

end FoldlMFoldrM

/-! ### intersperse -/

@[deprecated (since := "2025-02-07")] alias intersperse_singleton := intersperse_single
@[deprecated (since := "2025-02-07")] alias intersperse_cons_cons := intersperse_cons₂

/-! ### map for partial functions -/

@[deprecated "Deprecated without replacement." (since := "2025-02-07")]
theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) :
    SizeOf.sizeOf x < SizeOf.sizeOf l := by
  induction l with | nil => ?_ | cons h t ih => ?_ <;> cases hx <;> rw [cons.sizeOf_spec]
  · cutsat
  · specialize ih ‹_›
    cutsat

/-! ### filter -/

theorem length_eq_length_filter_add {l : List (α)} (f : α → Bool) :
    l.length = (l.filter f).length + (l.filter (!f ·)).length := by
  simp_rw [← List.countP_eq_length_filter, l.length_eq_countP_add_countP f, Bool.not_eq_true,
    Bool.decide_eq_false]

/-! ### filterMap -/

theorem filterMap_eq_flatMap_toList (f : α → Option β) (l : List α) :
    l.filterMap f = l.flatMap fun a ↦ (f a).toList := by
  induction l with | nil => ?_ | cons a l ih => ?_ <;> simp [filterMap_cons]
  rcases f a <;> simp [ih]

theorem filterMap_congr {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l <;> simp_all [filterMap_cons]

theorem filterMap_eq_map_iff_forall_eq_some {f : α → Option β} {g : α → β} {l : List α} :
    l.filterMap f = l.map g ↔ ∀ x ∈ l, f x = some (g x) where
  mp := by
    induction l with | nil => simp | cons a l ih => ?_
    rcases ha : f a with - | b
    · intro h
      have : (filterMap f l).length = l.length + 1 := by grind
      grind
    · simp +contextual [ha, ih]
  mpr h := Eq.trans (filterMap_congr <| by simpa) (congr_fun filterMap_eq_map _)

/-! ### filter -/

section Filter

variable {p : α → Bool}

theorem filter_singleton {a : α} : [a].filter p = bif p a then [a] else [] :=
  rfl

theorem filter_eq_foldr (p : α → Bool) (l : List α) :
    filter p l = foldr (fun a out => bif p a then a :: out else out) [] l := by
  induction l <;> simp [*, filter]; rfl

#adaptation_note /-- nightly-2024-07-27
This has to be temporarily renamed to avoid an unintentional collision.
The prime should be removed at nightly-2024-07-27. -/
@[simp]
theorem filter_subset' (l : List α) : filter p l ⊆ l :=
  filter_sublist.subset

theorem of_mem_filter {a : α} {l} (h : a ∈ filter p l) : p a := (mem_filter.1 h).2

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset' l h

theorem mem_filter_of_mem {a : α} {l} (h₁ : a ∈ l) (h₂ : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨h₁, h₂⟩

variable (p)

theorem monotone_filter_right (l : List α) ⦃p q : α → Bool⦄
    (h : ∀ a, p a → q a) : l.filter p <+ l.filter q := by
  induction l with grind

lemma map_filter {f : α → β} (hf : Injective f) (l : List α)
    [DecidablePred fun b => ∃ a, p a ∧ f a = b] :
    (l.filter p).map f = (l.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [comp_def, filter_map, hf.eq_iff]

lemma filter_attach' (l : List α) (p : {a // a ∈ l} → Bool) [DecidableEq α] :
    l.attach.filter p =
      (l.filter fun x => ∃ h, p ⟨x, h⟩).attach.map (Subtype.map id fun _ => mem_of_mem_filter) := by
  classical
  refine map_injective_iff.2 Subtype.coe_injective ?_
  simp [comp_def, map_filter _ Subtype.coe_injective]

lemma filter_attach (l : List α) (p : α → Bool) :
    (l.attach.filter fun x => p x : List {x // x ∈ l}) =
      (l.filter p).attach.map (Subtype.map id fun _ => mem_of_mem_filter) :=
  map_injective_iff.2 Subtype.coe_injective <| by
    simp_rw [map_map, comp_def, Subtype.map, id, ← Function.comp_apply (g := Subtype.val),
      ← filter_map, attach_map_subtype_val]

lemma filter_comm (q) (l : List α) : filter p (filter q l) = filter q (filter p l) := by
  simp [Bool.and_comm]

@[simp]
theorem filter_true (l : List α) :
    filter (fun _ => true) l = l := by induction l <;> simp [*, filter]

@[simp]
theorem filter_false (l : List α) :
    filter (fun _ => false) l = [] := by induction l <;> simp [*, filter]

end Filter

/-! ### eraseP -/

section eraseP

variable {p : α → Bool}

-- Cannot be @[simp] because `a` cannot be inferred by `simp`.
theorem length_eraseP_add_one {l : List α} {a} (al : a ∈ l) (pa : p a) :
    (l.eraseP p).length + 1 = l.length := by grind

end eraseP

/-! ### erase -/

section Erase

variable [DecidableEq α]

-- @[simp] -- removed because LHS is not in simp normal form
theorem length_erase_add_one {a : α} {l : List α} (h : a ∈ l) :
    (l.erase a).length + 1 = l.length := by
  rw [erase_eq_eraseP, length_eraseP_add_one h (decide_eq_true rfl)]

theorem map_erase [DecidableEq β] {f : α → β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) := by
  have this : (a == ·) = (f a == f ·) := by ext b; simp [finj.eq_iff]
  rw [erase_eq_eraseP, erase_eq_eraseP, eraseP_map, this]; rfl

theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]

theorem erase_getElem [DecidableEq ι] {l : List ι} {i : ℕ} (hi : i < l.length) :
    Perm (l.erase l[i]) (l.eraseIdx i) := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH => cases i with grind

theorem length_eraseIdx_add_one {l : List ι} {i : ℕ} (h : i < l.length) :
    (l.eraseIdx i).length + 1 = l.length := by grind

end Erase

/-! ### diff -/

section Diff

variable [DecidableEq α]

@[simp]
theorem map_diff [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

@[deprecated (since := "2025-04-10")]
alias erase_diff_erase_sublist_of_sublist := Sublist.erase_diff_erase_sublist

end Diff

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

theorem choose_spec (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property

theorem choose_mem (hp : ∃ a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1

theorem choose_property (hp : ∃ a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2

end Choose

/-! ### Forall -/

section Forall

variable {p q : α → Prop} {l : List α}

@[simp]
theorem forall_cons (p : α → Prop) (x : α) : ∀ l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l
  | [] => (and_iff_left_of_imp fun _ ↦ trivial).symm
  | _ :: _ => Iff.rfl

@[simp]
theorem forall_append {p : α → Prop} : ∀ {xs ys : List α},
    Forall p (xs ++ ys) ↔ Forall p xs ∧ Forall p ys
  | [] => by simp
  | _ :: _ => by simp [forall_append, and_assoc]

theorem forall_iff_forall_mem : ∀ {l : List α}, Forall p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [forall_mem_cons, forall_cons, forall_iff_forall_mem]

theorem Forall.imp (h : ∀ x, p x → q x) : ∀ {l : List α}, Forall p l → Forall q l
  | [] => id
  | x :: l => by
    simp only [forall_cons, and_imp]
    rw [← and_imp]
    exact And.imp (h x) (Forall.imp h)

@[simp]
theorem forall_map_iff {p : β → Prop} (f : α → β) : Forall p (l.map f) ↔ Forall (p ∘ f) l := by
  induction l <;> simp [*]

instance (p : α → Prop) [DecidablePred p] : DecidablePred (Forall p) := fun _ =>
  decidable_of_iff' _ forall_iff_forall_mem

end Forall

/-! ### Miscellaneous lemmas -/

theorem get_attach (l : List α) (i) :
    (l.attach.get i).1 = l.get ⟨i, length_attach (l := l) ▸ i.2⟩ := by simp

section Disjoint

/-- The images of disjoint lists under a partially defined map are disjoint -/
theorem disjoint_pmap {p : α → Prop} {f : ∀ a : α, p a → β} {s t : List α}
    (hs : ∀ a ∈ s, p a) (ht : ∀ a ∈ t, p a)
    (hf : ∀ (a a' : α) (ha : p a) (ha' : p a'), f a ha = f a' ha' → a = a')
    (h : Disjoint s t) :
    Disjoint (s.pmap f hs) (t.pmap f ht) := by
  simp only [Disjoint, mem_pmap]
  rintro b ⟨a, ha, rfl⟩ ⟨a', ha', ha''⟩
  apply h ha
  rwa [hf a a' (hs a ha) (ht a' ha') ha''.symm]

/-- The images of disjoint lists under an injective map are disjoint -/
theorem disjoint_map {f : α → β} {s t : List α} (hf : Function.Injective f)
    (h : Disjoint s t) : Disjoint (s.map f) (t.map f) := by
  rw [← pmap_eq_map (fun _ _ ↦ trivial), ← pmap_eq_map (fun _ _ ↦ trivial)]
  exact disjoint_pmap _ _ (fun _ _ _ _ h' ↦ hf h') h

alias Disjoint.map := disjoint_map

theorem Disjoint.of_map {f : α → β} {s t : List α} (h : Disjoint (s.map f) (t.map f)) :
    Disjoint s t := fun _a has hat ↦
  h (mem_map_of_mem has) (mem_map_of_mem hat)

theorem Disjoint.map_iff {f : α → β} {s t : List α} (hf : Function.Injective f) :
    Disjoint (s.map f) (t.map f) ↔ Disjoint s t :=
  ⟨fun h ↦ h.of_map, fun h ↦ h.map hf⟩

theorem Perm.disjoint_left {l₁ l₂ l : List α} (p : List.Perm l₁ l₂) :
    Disjoint l₁ l ↔ Disjoint l₂ l := by
  simp_rw [List.disjoint_left, p.mem_iff]

theorem Perm.disjoint_right {l₁ l₂ l : List α} (p : List.Perm l₁ l₂) :
    Disjoint l l₁ ↔ Disjoint l l₂ := by
  simp_rw [List.disjoint_right, p.mem_iff]

@[simp]
theorem disjoint_reverse_left {l₁ l₂ : List α} : Disjoint l₁.reverse l₂ ↔ Disjoint l₁ l₂ :=
  reverse_perm _ |>.disjoint_left

@[simp]
theorem disjoint_reverse_right {l₁ l₂ : List α} : Disjoint l₁ l₂.reverse ↔ Disjoint l₁ l₂ :=
  reverse_perm _ |>.disjoint_right

end Disjoint

section lookup
variable [BEq α] [LawfulBEq α]

lemma lookup_graph (f : α → β) {a : α} {as : List α} (h : a ∈ as) :
    lookup a (as.map fun x => (x, f x)) = some (f a) := by
  induction as with grind

end lookup

section range'

@[simp]
lemma range'_0 (a b : ℕ) : range' a b 0 = replicate b a := by
  induction b with
  | zero => simp
  | succ b ih => simp [range'_succ, ih, replicate_succ]

lemma left_le_of_mem_range' {a b s x : ℕ} (hx : x ∈ List.range' a b s) : a ≤ x := by
  obtain ⟨i, _, rfl⟩ := List.mem_range'.mp hx
  exact le_add_right a (s * i)

end range'

end List
