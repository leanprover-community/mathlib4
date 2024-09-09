/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.Nat.Defs
import Mathlib.Data.Option.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.List.Monad
import Mathlib.Logic.Unique
import Mathlib.Order.Basic
import Mathlib.Tactic.Common

/-!
# Basic properties of lists
-/

assert_not_exists Set.range
assert_not_exists GroupWithZero
assert_not_exists Ring
assert_not_exists Lattice

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

/-- `≤` implies not `>` for lists. -/
@[deprecated (since := "2024-07-27")]
theorem le_eq_not_gt [LT α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬l₂ < l₁ := fun _ _ => rfl

@[deprecated (since := "2024-06-07")] alias toArray_data := Array.data_toArray

-- Porting note: Delete this attribute
-- attribute [inline] List.head!

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

theorem singleton_inj {a b : α} : [a] = [b] ↔ a = b :=
  singleton_injective.eq_iff

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

@[deprecated (since := "2024-03-23")] alias mem_split := append_of_mem

-- The simpNF linter says that the LHS can be simplified via `List.mem_map`.
-- However this is a higher priority lemma.
-- https://github.com/leanprover/std4/issues/207
@[simp 1100, nolint simpNF]
theorem mem_map_of_injective {f : α → β} (H : Injective f) {a : α} {l : List α} :
    f a ∈ map f l ↔ a ∈ l :=
  ⟨fun m => let ⟨_, m', e⟩ := exists_of_mem_map m; H e ▸ m', mem_map_of_mem _⟩

@[simp]
theorem _root_.Function.Involutive.exists_mem_and_apply_eq_iff {f : α → α}
    (hf : Function.Involutive f) (x : α) (l : List α) : (∃ y : α, y ∈ l ∧ f y = x) ↔ f x ∈ l :=
  ⟨by rintro ⟨y, h, rfl⟩; rwa [hf y], fun h => ⟨f x, h, hf _⟩⟩

theorem mem_map_of_involutive {f : α → α} (hf : Involutive f) {a : α} {l : List α} :
    a ∈ map f l ↔ f a ∈ l := by rw [mem_map, hf.exists_mem_and_apply_eq_iff]

/-! ### length -/

alias ⟨_, length_pos_of_ne_nil⟩ := length_pos

theorem length_pos_iff_ne_nil {l : List α} : 0 < length l ↔ l ≠ [] :=
  ⟨ne_nil_of_length_pos, length_pos_of_ne_nil⟩

theorem exists_of_length_succ {n} : ∀ l : List α, l.length = n + 1 → ∃ h t, l = h :: t
  | [], H => absurd H.symm <| succ_ne_zero n
  | h :: t, _ => ⟨h, t, rfl⟩

@[simp] lemma length_injective_iff : Injective (List.length : List α → ℕ) ↔ Subsingleton α := by
  constructor
  · intro h; refine ⟨fun x y => ?_⟩; (suffices [x] = [y] by simpa using this); apply h; rfl
  · intros hα l1 l2 hl
    induction l1 generalizing l2 <;> cases l2
    · rfl
    · cases hl
    · cases hl
    · next ih _ _ =>
      congr
      · subsingleton
      · apply ih; simpa using hl

@[simp default+1] -- Porting note: this used to be just @[simp]
lemma length_injective [Subsingleton α] : Injective (length : List α → ℕ) :=
  length_injective_iff.mpr inferInstance

theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b, l = [a, b] :=
  ⟨fun _ => let [a, b] := l; ⟨a, b, rfl⟩, fun ⟨_, _, e⟩ => e ▸ rfl⟩

theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c, l = [a, b, c] :=
  ⟨fun _ => let [a, b, c] := l; ⟨a, b, c, rfl⟩, fun ⟨_, _, _, e⟩ => e ▸ rfl⟩

/-! ### set-theoretic notation of lists -/

instance instSingletonList : Singleton α (List α) := ⟨fun x => [x]⟩

instance [DecidableEq α] : Insert α (List α) := ⟨List.insert⟩

instance [DecidableEq α] : LawfulSingleton α (List α) :=
  { insert_emptyc_eq := fun x =>
      show (if x ∈ ([] : List α) then [] else [x]) = [x] from if_neg (not_mem_nil _) }

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

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of {p : α → Prop} {a : α} (l : List α) (h : p a) : ∃ x ∈ a :: l, p x :=
  ⟨a, mem_cons_self _ _, h⟩

-- Porting note: bExists in Lean3 and And in Lean4
theorem exists_mem_cons_of_exists {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ l, p x) →
    ∃ x ∈ a :: l, p x :=
  fun ⟨x, xl, px⟩ => ⟨x, mem_cons_of_mem _ xl, px⟩

-- Porting note: bExists in Lean3 and And in Lean4
theorem or_exists_of_exists_mem_cons {p : α → Prop} {a : α} {l : List α} : (∃ x ∈ a :: l, p x) →
    p a ∨ ∃ x ∈ l, p x :=
  fun ⟨x, xal, px⟩ =>
    Or.elim (eq_or_mem_of_mem_cons xal) (fun h : x = a => by rw [← h]; left; exact px)
      fun h : x ∈ l => Or.inr ⟨x, h, px⟩

theorem exists_mem_cons_iff (p : α → Prop) (a : α) (l : List α) :
    (∃ x ∈ a :: l, p x) ↔ p a ∨ ∃ x ∈ l, p x :=
  Iff.intro or_exists_of_exists_mem_cons fun h =>
    Or.elim h (exists_mem_cons_of l) exists_mem_cons_of_exists

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
  rcases mem_map.1 (h2 (mem_map_of_mem f hx)) with ⟨x', hx', hxx'⟩
  cases h hxx'; exact hx'

/-! ### append -/

theorem append_eq_has_append {L₁ L₂ : List α} : List.append L₁ L₂ = L₁ ++ L₂ :=
  rfl

@[deprecated (since := "2024-03-24")] alias append_eq_cons_iff := append_eq_cons

@[deprecated (since := "2024-03-24")] alias cons_eq_append_iff := cons_eq_append

@[deprecated (since := "2024-01-18")] alias append_left_cancel := append_cancel_left

@[deprecated (since := "2024-01-18")] alias append_right_cancel := append_cancel_right

theorem append_right_injective (s : List α) : Injective fun t ↦ s ++ t :=
  fun _ _ ↦ append_cancel_left

theorem append_left_injective (t : List α) : Injective fun s ↦ s ++ t :=
  fun _ _ ↦ append_cancel_right

/-! ### replicate -/

theorem eq_replicate_length {a : α} : ∀ {l : List α}, l = replicate l.length a ↔ ∀ b ∈ l, b = a
  | [] => by simp
  | (b :: l) => by simp [eq_replicate_length, replicate_succ]

theorem replicate_add (m n) (a : α) : replicate (m + n) a = replicate m a ++ replicate n a := by
  rw [append_replicate_replicate]

theorem replicate_succ' (n) (a : α) : replicate (n + 1) a = replicate n a ++ [a] :=
  replicate_add n 1 a

theorem replicate_subset_singleton (n) (a : α) : replicate n a ⊆ [a] := fun _ h =>
  mem_singleton.2 (eq_of_mem_replicate h)

theorem subset_singleton_iff {a : α} {L : List α} : L ⊆ [a] ↔ ∃ n, L = replicate n a := by
  simp only [eq_replicate, subset_def, mem_singleton, exists_eq_left']

theorem replicate_right_injective {n : ℕ} (hn : n ≠ 0) : Injective (@replicate α n) :=
  fun _ _ h => (eq_replicate.1 h).2 _ <| mem_replicate.2 ⟨hn, rfl⟩

theorem replicate_right_inj {a b : α} {n : ℕ} (hn : n ≠ 0) :
    replicate n a = replicate n b ↔ a = b :=
  (replicate_right_injective hn).eq_iff

theorem replicate_right_inj' {a b : α} : ∀ {n},
    replicate n a = replicate n b ↔ n = 0 ∨ a = b
  | 0 => by simp
  | n + 1 => (replicate_right_inj n.succ_ne_zero).trans <| by simp only [n.succ_ne_zero, false_or]

theorem replicate_left_injective (a : α) : Injective (replicate · a) :=
  LeftInverse.injective (length_replicate · a)

theorem replicate_left_inj {a : α} {n m : ℕ} : replicate n a = replicate m a ↔ n = m :=
  (replicate_left_injective a).eq_iff

/-! ### pure -/

theorem mem_pure (x y : α) : x ∈ (pure y : List α) ↔ x = y := by simp

/-! ### bind -/

@[simp]
theorem bind_eq_bind {α β} (f : α → List β) (l : List α) : l >>= f = l.bind f :=
  rfl

/-! ### concat -/

/-! ### reverse -/

theorem reverse_cons' (a : α) (l : List α) : reverse (a :: l) = concat (reverse l) a := by
  simp only [reverse_cons, concat_eq_append]

theorem reverse_concat' (l : List α) (a : α) : (l ++ [a]).reverse = a :: l.reverse := by
  rw [reverse_append]; rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
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

/-! ### empty -/

@[deprecated (since := "2024-08-15")] alias isEmpty_iff_eq_nil := isEmpty_iff

/-! ### getLast -/

attribute [simp] getLast_cons

theorem getLast_append_singleton {a : α} (l : List α) :
    getLast (l ++ [a]) (append_ne_nil_of_right_ne_nil l (cons_ne_nil a _)) = a := by
  simp [getLast_append]

-- Porting note: name should be fixed upstream
theorem getLast_append' (l₁ l₂ : List α) (h : l₂ ≠ []) :
    getLast (l₁ ++ l₂) (append_ne_nil_of_right_ne_nil l₁ h) = getLast l₂ h := by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => simp only [cons_append]; rw [List.getLast_cons]; exact ih

theorem getLast_concat' {a : α} (l : List α) : getLast (concat l a) (concat_ne_nil a l) = a := by
  simp

@[simp]
theorem getLast_singleton' (a : α) : getLast [a] (cons_ne_nil a []) = a := rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem getLast_cons_cons (a₁ a₂ : α) (l : List α) :
    getLast (a₁ :: a₂ :: l) (cons_ne_nil _ _) = getLast (a₂ :: l) (cons_ne_nil a₂ l) :=
  rfl

theorem dropLast_append_getLast : ∀ {l : List α} (h : l ≠ []), dropLast l ++ [getLast l h] = l
  | [], h => absurd rfl h
  | [a], h => rfl
  | a :: b :: l, h => by
    rw [dropLast_cons₂, cons_append, getLast_cons (cons_ne_nil _ _)]
    congr
    exact dropLast_append_getLast (cons_ne_nil b l)

theorem getLast_congr {l₁ l₂ : List α} (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) (h₃ : l₁ = l₂) :
    getLast l₁ h₁ = getLast l₂ h₂ := by subst l₁; rfl

theorem getLast_replicate_succ (m : ℕ) (a : α) :
    (replicate (m + 1) a).getLast (ne_nil_of_length_eq_add_one (length_replicate _ _)) = a := by
  simp only [replicate_succ']
  exact getLast_append_singleton _

/-- If the last element of `l` does not satisfy `p`, then it is also the last element of
`l.filter p`. -/
lemma getLast_filter {p : α → Bool} :
    ∀ (l : List α) (hlp : l.filter p ≠ []), p (l.getLast (hlp <| ·.symm ▸ rfl)) = true →
      (l.filter p).getLast hlp = l.getLast (hlp <| ·.symm ▸ rfl)
  | [a], h, h' => by rw [List.getLast_singleton'] at h'; simp [List.filter_cons, h']
  | a :: b :: as, h, h' => by
    rw [List.getLast_cons_cons] at h' ⊢
    simp only [List.filter_cons (x := a)] at h ⊢
    obtain ha | ha := Bool.eq_false_or_eq_true (p a)
    · simp only [ha, ite_true]
      rw [getLast_cons, getLast_filter (b :: as) _ h']
      exact ne_nil_of_mem <| mem_filter.2 ⟨getLast_mem _, h'⟩
    · simp only [ha, cond_false] at h ⊢
      exact getLast_filter (b :: as) h h'

/-! ### getLast? -/

-- This is a duplicate of `getLast?_eq_none_iff`.
-- We should remove one of them.
theorem getLast?_eq_none : ∀ {l : List α}, getLast? l = none ↔ l = []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@getLast?_eq_none (b :: l)]

@[deprecated (since := "2024-06-20")] alias getLast?_isNone := getLast?_eq_none

@[simp]
theorem getLast?_isSome : ∀ {l : List α}, l.getLast?.isSome ↔ l ≠ []
  | [] => by simp
  | [a] => by simp
  | a :: b :: l => by simp [@getLast?_isSome (b :: l)]

theorem mem_getLast?_eq_getLast : ∀ {l : List α} {x : α}, x ∈ l.getLast? → ∃ h, x = getLast l h
  | [], x, hx => False.elim <| by simp at hx
  | [a], x, hx =>
    have : a = x := by simpa using hx
    this ▸ ⟨cons_ne_nil a [], rfl⟩
  | a :: b :: l, x, hx => by
    rw [getLast?_cons_cons] at hx
    rcases mem_getLast?_eq_getLast hx with ⟨_, h₂⟩
    use cons_ne_nil _ _
    assumption

theorem getLast?_eq_getLast_of_ne_nil : ∀ {l : List α} (h : l ≠ []), l.getLast? = some (l.getLast h)
  | [], h => (h rfl).elim
  | [_], _ => rfl
  | _ :: b :: l, _ => @getLast?_eq_getLast_of_ne_nil (b :: l) (cons_ne_nil _ _)

theorem mem_getLast?_cons {x y : α} : ∀ {l : List α}, x ∈ l.getLast? → x ∈ (y :: l).getLast?
  | [], _ => by contradiction
  | _ :: _, h => h

theorem mem_of_mem_getLast? {l : List α} {a : α} (ha : a ∈ l.getLast?) : a ∈ l :=
  let ⟨_, h₂⟩ := mem_getLast?_eq_getLast ha
  h₂.symm ▸ getLast_mem _

theorem dropLast_append_getLast? : ∀ {l : List α}, ∀ a ∈ l.getLast?, dropLast l ++ [a] = l
  | [], a, ha => (Option.not_mem_none a ha).elim
  | [a], _, rfl => rfl
  | a :: b :: l, c, hc => by
    rw [getLast?_cons_cons] at hc
    rw [dropLast_cons₂, cons_append, dropLast_append_getLast? _ hc]

theorem getLastI_eq_getLast? [Inhabited α] : ∀ l : List α, l.getLastI = l.getLast?.iget
  | [] => by simp [getLastI, Inhabited.default]
  | [a] => rfl
  | [a, b] => rfl
  | [a, b, c] => rfl
  | _ :: _ :: c :: l => by simp [getLastI, getLastI_eq_getLast? (c :: l)]

#adaptation_note /-- 2024-07-10: removed `@[simp]` since the LHS simplifies using the simp set. -/
theorem getLast?_append_cons :
    ∀ (l₁ : List α) (a : α) (l₂ : List α), getLast? (l₁ ++ a :: l₂) = getLast? (a :: l₂)
  | [], a, l₂ => rfl
  | [b], a, l₂ => rfl
  | b :: c :: l₁, a, l₂ => by rw [cons_append, cons_append, getLast?_cons_cons,
    ← cons_append, getLast?_append_cons (c :: l₁)]

theorem getLast?_append_of_ne_nil (l₁ : List α) :
    ∀ {l₂ : List α} (_ : l₂ ≠ []), getLast? (l₁ ++ l₂) = getLast? l₂
  | [], hl₂ => by contradiction
  | b :: l₂, _ => getLast?_append_cons l₁ b l₂

theorem mem_getLast?_append_of_mem_getLast? {l₁ l₂ : List α} {x : α} (h : x ∈ l₂.getLast?) :
    x ∈ (l₁ ++ l₂).getLast? := by
  cases l₂
  · contradiction
  · rw [List.getLast?_append_cons]
    exact h

/-! ### head(!?) and tail -/

@[simp]
theorem head!_nil [Inhabited α] : ([] : List α).head! = default := rfl

@[simp] theorem head_cons_tail (x : List α) (h : x ≠ []) : x.head h :: x.tail = x := by
  cases x <;> simp at h ⊢

theorem head_eq_getElem_zero {l : List α} (hl : l ≠ []) :
    l.head hl = l[0]'(length_pos.2 hl) :=
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

theorem mem_of_mem_head? {x : α} {l : List α} (h : x ∈ l.head?) : x ∈ l :=
  (eq_cons_of_mem_head? h).symm ▸ mem_cons_self _ _

@[simp] theorem head!_cons [Inhabited α] (a : α) (l : List α) : head! (a :: l) = a := rfl

@[simp]
theorem head!_append [Inhabited α] (t : List α) {s : List α} (h : s ≠ []) :
    head! (s ++ t) = head! s := by
  induction s
  · contradiction
  · rfl

theorem mem_head?_append_of_mem_head? {s t : List α} {x : α} (h : x ∈ s.head?) :
    x ∈ (s ++ t).head? := by
  cases s
  · contradiction
  · exact h

theorem head?_append_of_ne_nil :
    ∀ (l₁ : List α) {l₂ : List α} (_ : l₁ ≠ []), head? (l₁ ++ l₂) = head? l₁
  | _ :: _, _, _ => rfl

theorem tail_append_singleton_of_ne_nil {a : α} {l : List α} (h : l ≠ nil) :
    tail (l ++ [a]) = tail l ++ [a] := by
  induction l
  · contradiction
  · rw [tail, cons_append, tail]

theorem cons_head?_tail : ∀ {l : List α} {a : α}, a ∈ head? l → a :: tail l = l
  | [], a, h => by contradiction
  | b :: l, a, h => by
    simp? at h says simp only [head?_cons, Option.mem_def, Option.some.injEq] at h
    simp [h]

theorem head!_mem_head? [Inhabited α] : ∀ {l : List α}, l ≠ [] → head! l ∈ head? l
  | [], h => by contradiction
  | a :: l, _ => rfl

theorem cons_head!_tail [Inhabited α] {l : List α} (h : l ≠ []) : head! l :: tail l = l :=
  cons_head?_tail (head!_mem_head? h)

theorem head!_mem_self [Inhabited α] {l : List α} (h : l ≠ nil) : l.head! ∈ l := by
  have h' := mem_cons_self l.head! l.tail
  rwa [cons_head!_tail h] at h'

theorem get_eq_get? (l : List α) (i : Fin l.length) :
    l.get i = (l.get? i).get (by simp [getElem?_eq_getElem]) := by
  simp

theorem getElem_cons {l : List α} {a : α} {n : ℕ} (h : n < (a :: l).length) :
    (a :: l)[n] = if hn : n = 0 then a else l[n - 1]'(by rw [length_cons] at h; omega) := by
  cases n <;> simp

theorem get_tail (l : List α) (i) (h : i < l.tail.length)
    (h' : i + 1 < l.length := (by simp only [length_tail] at h; omega)) :
    l.tail.get ⟨i, h⟩ = l.get ⟨i + 1, h'⟩ := by
  cases l <;> [cases h; rfl]

@[deprecated (since := "2024-08-22")]
theorem get_cons {l : List α} {a : α} {n} (hl) :
    (a :: l).get ⟨n, hl⟩ = if hn : n = 0 then a else
      l.get ⟨n - 1, by contrapose! hl; rw [length_cons]; omega⟩ :=
  getElem_cons hl

theorem modifyHead_modifyHead (l : List α) (f g : α → α) :
    (l.modifyHead f).modifyHead g = l.modifyHead (g ∘ f) := by cases l <;> simp

/-! ### Induction from the right -/

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
def reverseRecOn {motive : List α → Sort*} (l : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) : motive l :=
  match h : reverse l with
  | [] => cast (congr_arg motive <| by simpa using congr(reverse $h.symm)) <|
      nil
  | head :: tail =>
    cast (congr_arg motive <| by simpa using congr(reverse $h.symm)) <|
      append_singleton _ head <| reverseRecOn (reverse tail) nil append_singleton
termination_by l.length
decreasing_by
  simp_wf
  rw [← length_reverse l, h, length_cons]
  simp [Nat.lt_succ]

@[simp]
theorem reverseRecOn_nil {motive : List α → Sort*} (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    reverseRecOn [] nil append_singleton = nil := reverseRecOn.eq_1 ..

-- `unusedHavesSuffices` is getting confused by the unfolding of `reverseRecOn`
@[simp, nolint unusedHavesSuffices]
theorem reverseRecOn_concat {motive : List α → Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : ∀ (l : List α) (a : α), motive l → motive (l ++ [a])) :
    reverseRecOn (motive := motive) (xs ++ [x]) nil append_singleton =
      append_singleton _ _ (reverseRecOn (motive := motive) xs nil append_singleton) := by
  suffices ∀ ys (h : reverse (reverse xs) = ys),
      reverseRecOn (motive := motive) (xs ++ [x]) nil append_singleton =
        cast (by simp [(reverse_reverse _).symm.trans h])
          (append_singleton _ x (reverseRecOn (motive := motive) ys nil append_singleton)) by
    exact this _ (reverse_reverse xs)
  intros ys hy
  conv_lhs => unfold reverseRecOn
  split
  next h => simp at h
  next heq =>
    revert heq
    simp only [reverse_append, reverse_cons, reverse_nil, nil_append, singleton_append, cons.injEq]
    rintro ⟨rfl, rfl⟩
    subst ys
    rfl

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
@[elab_as_elim]
def bidirectionalRec {motive : List α → Sort*} (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) :
    ∀ l, motive l
  | [] => nil
  | [a] => singleton a
  | a :: b :: l =>
    let l' := dropLast (b :: l)
    let b' := getLast (b :: l) (cons_ne_nil _ _)
    cast (by rw [← dropLast_append_getLast (cons_ne_nil b l)]) <|
      cons_append a l' b' (bidirectionalRec nil singleton cons_append l')
termination_by l => l.length

@[simp]
theorem bidirectionalRec_nil {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) :
    bidirectionalRec nil singleton cons_append [] = nil := bidirectionalRec.eq_1 ..


@[simp]
theorem bidirectionalRec_singleton {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b]))) (a : α) :
    bidirectionalRec nil singleton cons_append [a] = singleton a := by
  simp [bidirectionalRec]

@[simp]
theorem bidirectionalRec_cons_append {motive : List α → Sort*}
    (nil : motive []) (singleton : ∀ a : α, motive [a])
    (cons_append : ∀ (a : α) (l : List α) (b : α), motive l → motive (a :: (l ++ [b])))
    (a : α) (l : List α) (b : α) :
    bidirectionalRec nil singleton cons_append (a :: (l ++ [b])) =
      cons_append a l b (bidirectionalRec nil singleton cons_append l) := by
  conv_lhs => unfold bidirectionalRec
  cases l with
  | nil => rfl
  | cons x xs =>
  simp only [List.cons_append]
  dsimp only [← List.cons_append]
  suffices ∀ (ys init : List α) (hinit : init = ys) (last : α) (hlast : last = b),
      (cons_append a init last
        (bidirectionalRec nil singleton cons_append init)) =
      cast (congr_arg motive <| by simp [hinit, hlast])
        (cons_append a ys b (bidirectionalRec nil singleton cons_append ys)) by
    rw [this (x :: xs) _ (by rw [dropLast_append_cons, dropLast_single, append_nil]) _ (by simp)]
    simp
  rintro ys init rfl last rfl
  rfl

/-- Like `bidirectionalRec`, but with the list parameter placed first. -/
@[elab_as_elim]
abbrev bidirectionalRecOn {C : List α → Sort*} (l : List α) (H0 : C []) (H1 : ∀ a : α, C [a])
    (Hn : ∀ (a : α) (l : List α) (b : α), C l → C (a :: (l ++ [b]))) : C l :=
  bidirectionalRec H0 H1 Hn l

/-! ### sublists -/

attribute [refl] List.Sublist.refl

theorem Sublist.cons_cons {l₁ l₂ : List α} (a : α) (s : l₁ <+ l₂) : a :: l₁ <+ a :: l₂ :=
  Sublist.cons₂ _ s

lemma cons_sublist_cons' {a b : α} : a :: l₁ <+ b :: l₂ ↔ a :: l₁ <+ l₂ ∨ a = b ∧ l₁ <+ l₂ := by
  constructor
  · rintro (_ | _)
    · exact Or.inl ‹_›
    · exact Or.inr ⟨rfl, ‹_›⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact h.cons _
    · rwa [cons_sublist_cons]

theorem sublist_cons_of_sublist (a : α) (h : l₁ <+ l₂) : l₁ <+ a :: l₂ := h.cons _

@[deprecated (since := "2024-04-07")]
theorem sublist_of_cons_sublist_cons {a} (h : a :: l₁ <+ a :: l₂) : l₁ <+ l₂ := h.of_cons_cons

@[deprecated (since := "2024-04-07")] alias cons_sublist_cons_iff := cons_sublist_cons

-- Porting note: this lemma seems to have been renamed on the occasion of its move to Batteries
alias sublist_nil_iff_eq_nil := sublist_nil

@[simp] lemma sublist_singleton {l : List α} {a : α} : l <+ [a] ↔ l = [] ∨ l = [a] := by
  constructor <;> rintro (_ | _) <;> aesop

theorem Sublist.antisymm (s₁ : l₁ <+ l₂) (s₂ : l₂ <+ l₁) : l₁ = l₂ :=
  s₁.eq_of_length_le s₂.length_le

instance decidableSublist [DecidableEq α] : ∀ l₁ l₂ : List α, Decidable (l₁ <+ l₂)
  | [], _ => isTrue <| nil_sublist _
  | _ :: _, [] => isFalse fun h => List.noConfusion <| eq_nil_of_sublist_nil h
  | a :: l₁, b :: l₂ =>
    if h : a = b then
      @decidable_of_decidable_of_iff _ _ (decidableSublist l₁ l₂) <| h ▸ cons_sublist_cons.symm
    else
      @decidable_of_decidable_of_iff _ _ (decidableSublist (a :: l₁) l₂)
        ⟨sublist_cons_of_sublist _, fun s =>
          match a, l₁, s, h with
          | _, _, Sublist.cons _ s', h => s'
          | _, _, Sublist.cons₂ t _, h => absurd rfl h⟩

/-! ### indexOf -/

section IndexOf

variable [DecidableEq α]

/-
  Porting note: The following proofs were simpler prior to the port. These proofs use the low-level
  `findIdx.go`.
  * `indexOf_cons_self`
  * `indexOf_cons_eq`
  * `indexOf_cons_ne`
  * `indexOf_cons`

  The ported versions of the earlier proofs are given in comments.
-/

-- indexOf_cons_eq _ rfl
@[simp]
theorem indexOf_cons_self (a : α) (l : List α) : indexOf a (a :: l) = 0 := by
  rw [indexOf, findIdx_cons, beq_self_eq_true, cond]

-- fun e => if_pos e
theorem indexOf_cons_eq {a b : α} (l : List α) : b = a → indexOf a (b :: l) = 0
  | e => by rw [← e]; exact indexOf_cons_self b l

-- fun n => if_neg n
@[simp]
theorem indexOf_cons_ne {a b : α} (l : List α) : b ≠ a → indexOf a (b :: l) = succ (indexOf a l)
  | h => by simp only [indexOf, findIdx_cons, Bool.cond_eq_ite, beq_iff_eq, h, ite_false]

theorem indexOf_eq_length {a : α} {l : List α} : indexOf a l = length l ↔ a ∉ l := by
  induction' l with b l ih
  · exact iff_of_true rfl (not_mem_nil _)
  simp only [length, mem_cons, indexOf_cons, eq_comm]
  rw [cond_eq_if]
  split_ifs with h <;> simp at h
  · exact iff_of_false (by rintro ⟨⟩) fun H => H <| Or.inl h.symm
  · simp only [Ne.symm h, false_or_iff]
    rw [← ih]
    exact succ_inj'

@[simp]
theorem indexOf_of_not_mem {l : List α} {a : α} : a ∉ l → indexOf a l = length l :=
  indexOf_eq_length.2

theorem indexOf_le_length {a : α} {l : List α} : indexOf a l ≤ length l := by
  induction' l with b l ih; · rfl
  simp only [length, indexOf_cons, cond_eq_if, beq_iff_eq]
  by_cases h : b = a
  · rw [if_pos h]; exact Nat.zero_le _
  · rw [if_neg h]; exact succ_le_succ ih

theorem indexOf_lt_length {a} {l : List α} : indexOf a l < length l ↔ a ∈ l :=
  ⟨fun h => Decidable.by_contradiction fun al => Nat.ne_of_lt h <| indexOf_eq_length.2 al,
   fun al => (lt_of_le_of_ne indexOf_le_length) fun h => indexOf_eq_length.1 h al⟩

theorem indexOf_append_of_mem {a : α} (h : a ∈ l₁) : indexOf a (l₁ ++ l₂) = indexOf a l₁ := by
  induction' l₁ with d₁ t₁ ih
  · exfalso
    exact not_mem_nil a h
  rw [List.cons_append]
  by_cases hh : d₁ = a
  · iterate 2 rw [indexOf_cons_eq _ hh]
  rw [indexOf_cons_ne _ hh, indexOf_cons_ne _ hh, ih (mem_of_ne_of_mem (Ne.symm hh) h)]

theorem indexOf_append_of_not_mem {a : α} (h : a ∉ l₁) :
    indexOf a (l₁ ++ l₂) = l₁.length + indexOf a l₂ := by
  induction' l₁ with d₁ t₁ ih
  · rw [List.nil_append, List.length, Nat.zero_add]
  rw [List.cons_append, indexOf_cons_ne _ (ne_of_not_mem_cons h).symm, List.length,
    ih (not_mem_of_not_mem_cons h), Nat.succ_add]

end IndexOf

/-! ### nth element -/

section deprecated
set_option linter.deprecated false

@[simp]
theorem getElem?_length (l : List α) : l[l.length]? = none := getElem?_len_le le_rfl

@[deprecated getElem?_length (since := "2024-06-12")]
theorem get?_length (l : List α) : l.get? l.length = none := get?_len_le le_rfl

@[deprecated (since := "2024-05-03")] alias get?_injective := get?_inj

/-- A version of `getElem_map` that can be used for rewriting. -/
theorem getElem_map_rev (f : α → β) {l} {n : Nat} {h : n < l.length} :
    f l[n] = (map f l)[n]'((l.length_map f).symm ▸ h) := Eq.symm (getElem_map _)

/-- A version of `get_map` that can be used for rewriting. -/
@[deprecated getElem_map_rev (since := "2024-06-12")]
theorem get_map_rev (f : α → β) {l n} :
    f (get l n) = get (map f l) ⟨n.1, (l.length_map f).symm ▸ n.2⟩ := Eq.symm (get_map _)

theorem get_length_sub_one {l : List α} (h : l.length - 1 < l.length) :
    l.get ⟨l.length - 1, h⟩ = l.getLast (by rintro rfl; exact Nat.lt_irrefl 0 h) :=
  (getLast_eq_get l _).symm

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  rw [drop_eq_get_cons h, take, take]

theorem ext_get?' {l₁ l₂ : List α} (h' : ∀ n < max l₁.length l₂.length, l₁.get? n = l₂.get? n) :
    l₁ = l₂ := by
  apply ext
  intro n
  rcases Nat.lt_or_ge n <| max l₁.length l₂.length with hn | hn
  · exact h' n hn
  · simp_all [Nat.max_le, getElem?_eq_none]

theorem ext_get?_iff {l₁ l₂ : List α} : l₁ = l₂ ↔ ∀ n, l₁.get? n = l₂.get? n :=
  ⟨by rintro rfl _; rfl, ext_get?⟩

theorem ext_get_iff {l₁ l₂ : List α} :
    l₁ = l₂ ↔ l₁.length = l₂.length ∧ ∀ n h₁ h₂, get l₁ ⟨n, h₁⟩ = get l₂ ⟨n, h₂⟩ := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ _ ↦ rfl⟩
  · intro ⟨h₁, h₂⟩
    exact ext_get h₁ h₂

theorem ext_get?_iff' {l₁ l₂ : List α} : l₁ = l₂ ↔
    ∀ n < max l₁.length l₂.length, l₁.get? n = l₂.get? n :=
  ⟨by rintro rfl _ _; rfl, ext_get?'⟩

@[simp]
theorem getElem_indexOf [DecidableEq α] {a : α} : ∀ {l : List α} (h : indexOf a l < l.length),
    l[indexOf a l] = a
  | b :: l, h => by
    by_cases h' : b = a <;>
    simp [h', if_pos, if_false, getElem_indexOf]

-- This is incorrectly named and should be `get_indexOf`;
-- this already exists, so will require a deprecation dance.
theorem indexOf_get [DecidableEq α] {a : α} {l : List α} (h) : get l ⟨indexOf a l, h⟩ = a := by
  simp

@[simp]
theorem getElem?_indexOf [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    l[indexOf a l]? = some a := by rw [getElem?_eq_getElem, getElem_indexOf (indexOf_lt_length.2 h)]

-- This is incorrectly named and should be `get?_indexOf`;
-- this already exists, so will require a deprecation dance.
theorem indexOf_get? [DecidableEq α] {a : α} {l : List α} (h : a ∈ l) :
    get? l (indexOf a l) = some a := by simp [h]

@[deprecated (since := "2023-01-05")]
theorem get_reverse_aux₁ :
    ∀ (l r : List α) (i h1 h2), get (reverseAux l r) ⟨i + length l, h1⟩ = get r ⟨i, h2⟩
  | [], r, i => fun h1 _ => rfl
  | a :: l, r, i => by
    rw [show i + length (a :: l) = i + 1 + length l from Nat.add_right_comm i (length l) 1]
    exact fun h1 h2 => get_reverse_aux₁ l (a :: r) (i + 1) h1 (succ_lt_succ h2)

theorem indexOf_inj [DecidableEq α] {l : List α} {x y : α} (hx : x ∈ l) (hy : y ∈ l) :
    indexOf x l = indexOf y l ↔ x = y :=
  ⟨fun h => by
    have x_eq_y :
        get l ⟨indexOf x l, indexOf_lt_length.2 hx⟩ =
        get l ⟨indexOf y l, indexOf_lt_length.2 hy⟩ := by
      simp only [h]
    simp only [indexOf_get] at x_eq_y; exact x_eq_y, fun h => by subst h; rfl⟩

@[deprecated (since := "2024-08-15")]
theorem getElem_reverse_aux₂ :
    ∀ (l r : List α) (i : Nat) (h1) (h2),
      (reverseAux l r)[length l - 1 - i]'h1 = l[i]'h2
  | [], r, i, h1, h2 => absurd h2 (Nat.not_lt_zero _)
  | a :: l, r, 0, h1, _ => by
    have aux := get_reverse_aux₁ l (a :: r) 0
    rw [Nat.zero_add] at aux
    exact aux _ (zero_lt_succ _)
  | a :: l, r, i + 1, h1, h2 => by
    have aux := getElem_reverse_aux₂ l (a :: r) i
    have heq : length (a :: l) - 1 - (i + 1) = length l - 1 - i := by rw [length]; omega
    rw [← heq] at aux
    apply aux

@[deprecated (since := "2024-06-12")]
theorem get_reverse_aux₂ (l r : List α) (i : Nat) (h1) (h2) :
    get (reverseAux l r) ⟨length l - 1 - i, h1⟩ = get l ⟨i, h2⟩ := by
  simp only [get_eq_getElem, h2, getElem_reverse_aux₂]

@[deprecated getElem_reverse (since := "2024-06-12")]
theorem get_reverse (l : List α) (i : Nat) (h1 h2) :
    get (reverse l) ⟨length l - 1 - i, h1⟩ = get l ⟨i, h2⟩ :=
  get_reverse_aux₂ _ _ _ _ _

theorem get_reverse' (l : List α) (n) (hn') :
    l.reverse.get n = l.get ⟨l.length - 1 - n, hn'⟩ := by
  rw [eq_comm]
  convert get_reverse l.reverse n (by simpa) n.2 using 1
  simp

theorem eq_cons_of_length_one {l : List α} (h : l.length = 1) : l = [l.get ⟨0, by omega⟩] := by
  refine ext_get (by convert h) fun n h₁ h₂ => ?_
  simp only [get_singleton]
  congr
  omega

end deprecated

theorem modifyNthTail_modifyNthTail {f g : List α → List α} (m : ℕ) :
    ∀ (n) (l : List α),
      (l.modifyNthTail f n).modifyNthTail g (m + n) =
        l.modifyNthTail (fun l => (f l).modifyNthTail g m) n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => congr_arg (List.cons a) (modifyNthTail_modifyNthTail m n l)

theorem modifyNthTail_modifyNthTail_le {f g : List α → List α} (m n : ℕ) (l : List α)
    (h : n ≤ m) :
    (l.modifyNthTail f n).modifyNthTail g m =
      l.modifyNthTail (fun l => (f l).modifyNthTail g (m - n)) n := by
  rcases Nat.exists_eq_add_of_le h with ⟨m, rfl⟩
  rw [Nat.add_comm, modifyNthTail_modifyNthTail, Nat.add_sub_cancel]

theorem modifyNthTail_modifyNthTail_same {f g : List α → List α} (n : ℕ) (l : List α) :
    (l.modifyNthTail f n).modifyNthTail g n = l.modifyNthTail (g ∘ f) n := by
  rw [modifyNthTail_modifyNthTail_le n n l (le_refl n), Nat.sub_self]; rfl

@[deprecated (since := "2024-05-04")] alias removeNth_eq_nthTail := eraseIdx_eq_modifyNthTail

theorem modifyNth_eq_set (f : α → α) :
    ∀ (n) (l : List α), modifyNth f n l = ((fun a => set l n (f a)) <$> l[n]?).getD l
  | 0, l => by cases l <;> simp
  | n + 1, [] => rfl
  | n + 1, b :: l =>
    (congr_arg (cons b) (modifyNth_eq_set f n l)).trans <| by cases h : l[n]? <;> simp [h]

theorem length_modifyNthTail (f : List α → List α) (H : ∀ l, length (f l) = length l) :
    ∀ n l, length (modifyNthTail f n l) = length l
  | 0, _ => H _
  | _ + 1, [] => rfl
  | _ + 1, _ :: _ => @congr_arg _ _ _ _ (· + 1) (length_modifyNthTail _ H _ _)

-- Porting note: Duplicate of `modify_get?_length`
-- (but with a substantially better name?)
-- @[simp]
theorem length_modifyNth (f : α → α) : ∀ n l, length (modifyNth f n l) = length l :=
  modify_get?_length f

@[simp]
theorem getElem_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a)[j] = l[j]'(by simpa using hj) := by
  rw [← Option.some_inj, ← List.getElem?_eq_getElem, List.getElem?_set_ne h,
    List.getElem?_eq_getElem]

@[deprecated getElem_set_of_ne (since := "2024-06-12")]
theorem get_set_of_ne {l : List α} {i j : ℕ} (h : i ≠ j) (a : α)
    (hj : j < (l.set i a).length) :
    (l.set i a).get ⟨j, hj⟩ = l.get ⟨j, by simpa using hj⟩ := by
  simp [getElem_set_of_ne, h]

/-! ### map -/

@[deprecated (since := "2024-06-21")] alias map_congr := map_congr_left

theorem bind_pure_eq_map (f : α → β) (l : List α) : l.bind (pure ∘ f) = map f l :=
  .symm <| map_eq_bind ..

set_option linter.deprecated false in
@[deprecated bind_pure_eq_map (since := "2024-03-24")]
theorem bind_ret_eq_map (f : α → β) (l : List α) : l.bind (List.ret ∘ f) = map f l :=
  bind_pure_eq_map f l

theorem bind_congr {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    List.bind l f = List.bind l g :=
  (congr_arg List.join <| map_congr_left h : _)

theorem infix_bind_of_mem {a : α} {as : List α} (h : a ∈ as) (f : α → List α) :
    f a <:+: as.bind f :=
  List.infix_of_mem_join (List.mem_map_of_mem f h)

@[simp]
theorem map_eq_map {α β} (f : α → β) (l : List α) : f <$> l = map f l :=
  rfl

@[simp]
theorem map_tail (f : α → β) (l) : map f (tail l) = tail (map f l) := by cases l <;> rfl

/-- A single `List.map` of a composition of functions is equal to
composing a `List.map` with another `List.map`, fully applied.
This is the reverse direction of `List.map_map`.
-/
theorem comp_map (h : β → γ) (g : α → β) (l : List α) : map (h ∘ g) l = map h (map g l) :=
  (map_map _ _ _).symm

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

/-! ### zipWith -/

theorem nil_zipWith (f : α → β → γ) (l : List β) : zipWith f [] l = [] := by cases l <;> rfl

theorem zipWith_nil (f : α → β → γ) (l : List α) : zipWith f l [] = [] := by cases l <;> rfl

@[simp]
theorem zipWith_flip (f : α → β → γ) : ∀ as bs, zipWith (flip f) bs as = zipWith f as bs
  | [], [] => rfl
  | [], b :: bs => rfl
  | a :: as, [] => rfl
  | a :: as, b :: bs => by
    simp! [zipWith_flip]
    rfl

/-! ### take, drop -/

theorem cons_getElem_drop_succ {l : List α} {n : Nat} {h : n < l.length} :
    l[n] :: l.drop (n + 1) = l.drop n :=
  (drop_eq_getElem_cons h).symm

theorem cons_get_drop_succ {l : List α} {n} :
    l.get n :: l.drop (n.1 + 1) = l.drop n.1 :=
  (drop_eq_getElem_cons n.2).symm

section TakeI

variable [Inhabited α]

@[simp]
theorem takeI_length : ∀ n l, length (@takeI α _ n l) = n
  | 0, _ => rfl
  | _ + 1, _ => congr_arg succ (takeI_length _ _)

@[simp]
theorem takeI_nil : ∀ n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | _ + 1 => congr_arg (cons _) (takeI_nil _)

theorem takeI_eq_take : ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l
  | 0, _, _ => rfl
  | _ + 1, _ :: _, h => congr_arg (cons _) <| takeI_eq_take <| le_of_succ_le_succ h

@[simp]
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)

theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply takeI_left

end TakeI

/- Porting note: in mathlib3 we just had `take` and `take'`. Now we have `take`, `takeI`, and
  `takeD`. The following section replicates the theorems above but for `takeD`. -/
section TakeD

@[simp]
theorem takeD_length : ∀ n l a, length (@takeD α n l a) = n
  | 0, _, _ => rfl
  | _ + 1, _, _ => congr_arg succ (takeD_length _ _ _)

-- `takeD_nil` is already in batteries

theorem takeD_eq_take : ∀ {n} {l : List α} a, n ≤ length l → takeD n l a = take n l
  | 0, _, _, _ => rfl
  | _ + 1, _ :: _, a, h => congr_arg (cons _) <| takeD_eq_take a <| le_of_succ_le_succ h

@[simp]
theorem takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁ :=
  (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans (take_left _ _)

theorem takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ l₂) a = l₁ := by
  rw [← h]; apply takeD_left

end TakeD

/-! ### foldl, foldr -/

theorem foldl_ext (f g : α → β → α) (a : α) {l : List β} (H : ∀ a : α, ∀ b ∈ l, f a b = g a b) :
    foldl f a l = foldl g a l := by
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih =>
    unfold foldl
    rw [ih _ fun a b bin => H a b <| mem_cons_of_mem _ bin, H a hd (mem_cons_self _ _)]

theorem foldr_ext (f g : α → β → β) (b : β) {l : List α} (H : ∀ a ∈ l, ∀ b : β, f a b = g a b) :
    foldr f b l = foldr g b l := by
  induction' l with hd tl ih; · rfl
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

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem foldr_eta : ∀ l : List α, foldr cons [] l = l := by
  simp only [foldr_cons_eq_append, append_nil, forall_const]

theorem reverse_foldl {l : List α} : reverse (foldl (fun t h => h :: t) [] l) = l := by
  rw [← foldr_reverse]; simp only [foldr_cons_eq_append, append_nil, reverse_reverse]

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
  induction' l with lh lt l_ih generalizing f
  · exact hf
  · apply l_ih fun _ h => hl _ (List.mem_cons_of_mem _ h)
    apply Function.Injective.comp hf
    apply hl _ (List.mem_cons_self _ _)

/-- Consider two lists `l₁` and `l₂` with designated elements `a₁` and `a₂` somewhere in them:
`l₁ = x₁ ++ [a₁] ++ z₁` and `l₂ = x₂ ++ [a₂] ++ z₂`.
Assume the designated element `a₂` is present in neither `x₁` nor `z₁`.
We conclude that the lists are equal (`l₁ = l₂`) if and only if their respective parts are equal
(`x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂`). -/
lemma append_cons_inj_of_not_mem {x₁ x₂ z₁ z₂ : List α} {a₁ a₂ : α}
    (notin_x : a₂ ∉ x₁) (notin_z : a₂ ∉ z₁) :
    x₁ ++ a₁ :: z₁ = x₂ ++ a₂ :: z₂ ↔ x₁ = x₂ ∧ a₁ = a₂ ∧ z₁ = z₂ := by
  constructor
  · simp only [append_eq_append_iff, cons_eq_append, cons_eq_cons]
    rintro (⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩ |
      ⟨c, rfl, ⟨rfl, rfl, rfl⟩ | ⟨d, rfl, rfl⟩⟩) <;> simp_all
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

section Scanl

variable {f : β → α → β} {b : β} {a : α} {l : List α}

theorem length_scanl : ∀ a l, length (scanl f a l) = l.length + 1
  | a, [] => rfl
  | a, x :: l => by
    rw [scanl, length_cons, length_cons, ← succ_eq_add_one, congr_arg succ]
    exact length_scanl _ _

@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl

@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := by
  simp only [scanl, eq_self_iff_true, singleton_append, and_self_iff]

@[simp]
theorem getElem?_scanl_zero : (scanl f b l)[0]? = some b := by
  cases l
  · simp [scanl_nil]
  · simp [scanl_cons, singleton_append]

@[deprecated getElem?_scanl_zero (since := "2024-06-12")]
theorem get?_zero_scanl : (scanl f b l).get? 0 = some b := by
  simp [getElem?_scanl_zero]

@[simp]
theorem getElem_scanl_zero {h : 0 < (scanl f b l).length} : (scanl f b l)[0] = b := by
  cases l
  · simp [scanl_nil]
  · simp [scanl_cons, singleton_append]

@[deprecated getElem_scanl_zero (since := "2024-06-12")]
theorem get_zero_scanl {h : 0 < (scanl f b l).length} : (scanl f b l).get ⟨0, h⟩ = b := by
  simp [getElem_scanl_zero]

theorem get?_succ_scanl {i : ℕ} : (scanl f b l).get? (i + 1) =
    ((scanl f b l).get? i).bind fun x => (l.get? i).map fun y => f x y := by
  induction' l with hd tl hl generalizing b i
  · symm
    simp only [Option.bind_eq_none', get?, forall₂_true_iff, not_false_iff, Option.map_none',
      scanl_nil, Option.not_mem_none, forall_true_iff]
  · simp only [scanl_cons, singleton_append]
    cases i
    · simp
    · simp only [hl, get?]

theorem getElem_succ_scanl {i : ℕ} (h : i + 1 < (scanl f b l).length) :
    (scanl f b l)[i + 1] =
      f ((scanl f b l)[i]'(Nat.lt_of_succ_lt h))
        (l[i]'(Nat.lt_of_succ_lt_succ (h.trans_eq (length_scanl b l)))) := by
  induction i generalizing b l with
  | zero =>
    cases l
    · simp only [length, zero_eq, lt_self_iff_false] at h
    · simp
  | succ i hi =>
    cases l
    · simp only [length] at h
      exact absurd h (by omega)
    · simp_rw [scanl_cons]
      rw [getElem_append_right']
      · simp only [length, Nat.zero_add 1, succ_add_sub_one, hi]; rfl
      · simp only [length_singleton]; omega

@[deprecated getElem_succ_scanl (since := "2024-08-22")]
theorem get_succ_scanl {i : ℕ} {h : i + 1 < (scanl f b l).length} :
    (scanl f b l).get ⟨i + 1, h⟩ =
      f ((scanl f b l).get ⟨i, Nat.lt_of_succ_lt h⟩)
        (l.get ⟨i, Nat.lt_of_succ_lt_succ (lt_of_lt_of_le h (le_of_eq (length_scanl b l)))⟩) :=
  getElem_succ_scanl h

end Scanl

-- scanr
@[simp]
theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl

@[simp]
theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, foldr, cons.injEq, and_true]
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih => simp only [foldr, ih]

section FoldlEqFoldr

-- foldl and foldr coincide when f is commutative and associative
variable {f : α → α → α}

theorem foldl1_eq_foldr1 (hassoc : Associative f) :
    ∀ a b l, foldl f a (l ++ [b]) = foldr f b (a :: l)
  | a, b, nil => rfl
  | a, b, c :: l => by
    simp only [cons_append, foldl_cons, foldr_cons, foldl1_eq_foldr1 hassoc _ _ l]; rw [hassoc]

theorem foldl_eq_of_comm_of_assoc (hcomm : Commutative f) (hassoc : Associative f) :
    ∀ a b l, foldl f a (b :: l) = f b (foldl f a l)
  | a, b, nil => hcomm a b
  | a, b, c :: l => by
    simp only [foldl_cons]
    rw [← foldl_eq_of_comm_of_assoc hcomm hassoc .., right_comm _ hcomm hassoc]; rfl

theorem foldl_eq_foldr (hcomm : Commutative f) (hassoc : Associative f) :
    ∀ a l, foldl f a l = foldr f a l
  | a, nil => rfl
  | a, b :: l => by
    simp only [foldr_cons, foldl_eq_of_comm_of_assoc hcomm hassoc]
    rw [foldl_eq_foldr hcomm hassoc a l]

end FoldlEqFoldr

section FoldlEqFoldlr'

variable {f : α → β → α}
variable (hf : ∀ a b c, f (f a b) c = f (f a c) b)

include hf

theorem foldl_eq_of_comm' : ∀ a b l, foldl f a (b :: l) = f (foldl f a l) b
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldl, foldl, foldl, ← foldl_eq_of_comm' .., foldl, hf]

theorem foldl_eq_foldr' : ∀ a l, foldl f a l = foldr (flip f) a l
  | a, [] => rfl
  | a, b :: l => by rw [foldl_eq_of_comm' hf, foldr, foldl_eq_foldr' ..]; rfl

end FoldlEqFoldlr'

section FoldlEqFoldlr'

variable {f : α → β → β}

theorem foldr_eq_of_comm' (hf : ∀ a b c, f a (f b c) = f b (f a c)) :
    ∀ a b l, foldr f a (b :: l) = foldr f (f b a) l
  | a, b, [] => rfl
  | a, b, c :: l => by rw [foldr, foldr, foldr, hf, ← foldr_eq_of_comm' hf ..]; rfl

end FoldlEqFoldlr'

section

variable {op : α → α → α} [ha : Std.Associative op]

/-- Notation for `op a b`. -/
local notation a " ⋆ " b => op a b

/-- Notation for `foldl op a l`. -/
local notation l " <*> " a => foldl op a l

theorem foldl_assoc : ∀ {l : List α} {a₁ a₂}, (l <*> a₁ ⋆ a₂) = a₁ ⋆ l <*> a₂
  | [], a₁, a₂ => rfl
  | a :: l, a₁, a₂ =>
    calc
      ((a :: l) <*> a₁ ⋆ a₂) = l <*> a₁ ⋆ a₂ ⋆ a := by simp only [foldl_cons, ha.assoc]
      _ = a₁ ⋆ (a :: l) <*> a₂ := by rw [foldl_assoc, foldl_cons]

theorem foldl_op_eq_op_foldr_assoc :
    ∀ {l : List α} {a₁ a₂}, ((l <*> a₁) ⋆ a₂) = a₁ ⋆ l.foldr (· ⋆ ·) a₂
  | [], a₁, a₂ => rfl
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

attribute [simp] mapM mapM'

theorem foldlM_eq_foldl (f : β → α → m β) (b l) :
    List.foldlM f b l = foldl (fun mb a => mb >>= fun b => f b a) (pure b) l := by
  suffices h :
    ∀ mb : m β, (mb >>= fun b => List.foldlM f b l) = foldl (fun mb a => mb >>= fun b => f b a) mb l
    by simp [← h (pure b)]
  induction l with
  | nil => intro; simp
  | cons _ _ l_ih => intro; simp only [List.foldlM, foldl, ← l_ih, functor_norm]

end FoldlMFoldrM

/-! ### intersperse -/

@[simp]
theorem intersperse_singleton (a b : α) : intersperse a [b] = [b] :=
  rfl

@[simp]
theorem intersperse_cons_cons (a b c : α) (tl : List α) :
    intersperse a (b :: c :: tl) = b :: a :: intersperse a (c :: tl) :=
  rfl

/-! ### splitAt and splitOn -/

section SplitAtOn

variable (p : α → Bool) (xs ys : List α) (ls : List (List α)) (f : List α → List α)

attribute [simp] splitAt_eq

@[deprecated (since := "2024-08-17")] alias splitAt_eq_take_drop := splitAt_eq

@[simp]
theorem splitOn_nil [DecidableEq α] (a : α) : [].splitOn a = [[]] :=
  rfl

@[simp]
theorem splitOnP_nil : [].splitOnP p = [[]] :=
  rfl

theorem splitOnP.go_ne_nil (xs acc : List α) : splitOnP.go p xs acc ≠ [] := by
  induction xs generalizing acc <;> simp [go]; split <;> simp [*]

theorem splitOnP.go_acc (xs acc : List α) :
    splitOnP.go p xs acc = modifyHead (acc.reverse ++ ·) (splitOnP p xs) := by
  induction xs generalizing acc with
  | nil => simp only [go, modifyHead, splitOnP_nil, append_nil]
  | cons hd tl ih =>
    simp only [splitOnP, go]; split
    · simp only [modifyHead, reverse_nil, append_nil]
    · rw [ih [hd], modifyHead_modifyHead, ih]
      congr; funext x; simp only [reverse_cons, append_assoc]; rfl

theorem splitOnP_ne_nil (xs : List α) : xs.splitOnP p ≠ [] := splitOnP.go_ne_nil _ _ _

@[simp]
theorem splitOnP_cons (x : α) (xs : List α) :
    (x :: xs).splitOnP p =
      if p x then [] :: xs.splitOnP p else (xs.splitOnP p).modifyHead (cons x) := by
  rw [splitOnP, splitOnP.go]; split <;> [rfl; simp [splitOnP.go_acc]]

/-- The original list `L` can be recovered by joining the lists produced by `splitOnP p L`,
interspersed with the elements `L.filter p`. -/
theorem splitOnP_spec (as : List α) :
    join (zipWith (· ++ ·) (splitOnP p as) (((as.filter p).map fun x => [x]) ++ [[]])) = as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    rw [splitOnP_cons, filter]
    by_cases h : p a
    · rw [if_pos h, h, map, cons_append, zipWith, nil_append, join, cons_append, cons_inj_right]
      exact ih
    · rw [if_neg h, eq_false_of_ne_true h, join_zipWith (splitOnP_ne_nil _ _)
        (append_ne_nil_of_right_ne_nil _ (cons_ne_nil [] [])), cons_inj_right]
      exact ih
where
  join_zipWith {xs ys : List (List α)} {a : α} (hxs : xs ≠ []) (hys : ys ≠ []) :
      join (zipWith (fun x x_1 ↦ x ++ x_1) (modifyHead (cons a) xs) ys) =
        a :: join (zipWith (fun x x_1 ↦ x ++ x_1) xs ys) := by
    cases xs with | nil => contradiction | cons =>
      cases ys with | nil => contradiction | cons => rfl

/-- If no element satisfies `p` in the list `xs`, then `xs.splitOnP p = [xs]` -/
theorem splitOnP_eq_single (h : ∀ x ∈ xs, ¬p x) : xs.splitOnP p = [xs] := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    simp only [splitOnP_cons, h hd (mem_cons_self hd tl), if_neg]
    rw [ih <| forall_mem_of_forall_mem_cons h]
    rfl

/-- When a list of the form `[...xs, sep, ...as]` is split on `p`, the first element is `xs`,
  assuming no element in `xs` satisfies `p` but `sep` does satisfy `p` -/
theorem splitOnP_first (h : ∀ x ∈ xs, ¬p x) (sep : α) (hsep : p sep) (as : List α) :
    (xs ++ sep :: as).splitOnP p = xs :: as.splitOnP p := by
  induction xs with
  | nil => simp [hsep]
  | cons hd tl ih => simp [h hd _, ih <| forall_mem_of_forall_mem_cons h]

/-- `intercalate [x]` is the left inverse of `splitOn x`  -/
theorem intercalate_splitOn (x : α) [DecidableEq α] : [x].intercalate (xs.splitOn x) = xs := by
  simp only [intercalate, splitOn]
  induction' xs with hd tl ih; · simp [join]
  cases' h' : splitOnP (· == x) tl with hd' tl'; · exact (splitOnP_ne_nil _ tl h').elim
  rw [h'] at ih
  rw [splitOnP_cons]
  split_ifs with h
  · rw [beq_iff_eq] at h
    subst h
    simp [ih, join, h']
  cases tl' <;> simpa [join, h'] using ih

/-- `splitOn x` is the left inverse of `intercalate [x]`, on the domain
  consisting of each nonempty list of lists `ls` whose elements do not contain `x`  -/
theorem splitOn_intercalate [DecidableEq α] (x : α) (hx : ∀ l ∈ ls, x ∉ l) (hls : ls ≠ []) :
    ([x].intercalate ls).splitOn x = ls := by
  simp only [intercalate]
  induction' ls with hd tl ih; · contradiction
  cases tl
  · suffices hd.splitOn x = [hd] by simpa [join]
    refine splitOnP_eq_single _ _ ?_
    intro y hy H
    rw [eq_of_beq H] at hy
    refine hx hd ?_ hy
    simp
  · simp only [intersperse_cons_cons, singleton_append, join]
    specialize ih _ _
    · intro l hl
      apply hx l
      simp only [mem_cons] at hl ⊢
      exact Or.inr hl
    · exact List.noConfusion
    have := splitOnP_first (· == x) hd ?h x (beq_self_eq_true _)
    case h =>
      intro y hy H
      rw [eq_of_beq H] at hy
      exact hx hd (.head _) hy
    simp only [splitOn] at ih ⊢
    rw [this, ih]

end SplitAtOn

/-! ### modifyLast -/

section ModifyLast

theorem modifyLast.go_append_one (f : α → α) (a : α) (tl : List α) (r : Array α) :
    modifyLast.go f (tl ++ [a]) r = (r.toListAppend <| modifyLast.go f (tl ++ [a]) #[]) := by
  cases tl with
  | nil =>
    simp only [nil_append, modifyLast.go]; rfl
  | cons hd tl =>
    simp only [cons_append]
    rw [modifyLast.go, modifyLast.go]
    case x_3 | x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_append_one _ _ tl _, modifyLast.go_append_one _ _ tl (Array.push #[] hd)]
    simp only [Array.toListAppend_eq, Array.push_data, Array.data_toArray, nil_append, append_assoc]

theorem modifyLast_append_one (f : α → α) (a : α) (l : List α) :
    modifyLast f (l ++ [a]) = l ++ [f a] := by
  cases l with
  | nil =>
    simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq, Array.data_toArray]
  | cons _ tl =>
    simp only [cons_append, modifyLast]
    rw [modifyLast.go]
    case x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_append_one, Array.toListAppend_eq, Array.push_data, Array.data_toArray,
      nil_append, cons_append, nil_append, cons_inj_right]
    exact modifyLast_append_one _ _ tl

theorem modifyLast_append (f : α → α) (l₁ l₂ : List α) (_ : l₂ ≠ []) :
    modifyLast f (l₁ ++ l₂) = l₁ ++ modifyLast f l₂ := by
  cases l₂ with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil => exact modifyLast_append_one _ hd _
    | cons hd' tl' =>
      rw [append_cons, ← nil_append (hd :: hd' :: tl'), append_cons [], nil_append,
        modifyLast_append _ (l₁ ++ [hd]) (hd' :: tl') _, modifyLast_append _ [hd] (hd' :: tl') _,
        append_assoc]
      all_goals { exact cons_ne_nil _ _ }

end ModifyLast

/-! ### map for partial functions -/

theorem sizeOf_lt_sizeOf_of_mem [SizeOf α] {x : α} {l : List α} (hx : x ∈ l) :
    SizeOf.sizeOf x < SizeOf.sizeOf l := by
  induction' l with h t ih <;> cases hx <;> rw [cons.sizeOf_spec]
  · omega
  · specialize ih ‹_›
    omega

@[deprecated attach_map_coe (since := "2024-07-29")] alias attach_map_coe' := attach_map_coe
@[deprecated attach_map_val (since := "2024-07-29")] alias attach_map_val' := attach_map_val

/-! ### find -/

section find?

variable {p : α → Bool} {l : List α} {a : α}

@[deprecated (since := "2024-05-05")] alias find?_mem := mem_of_find?_eq_some

end find?

/-! ### lookmap -/

section Lookmap

variable (f : α → Option α)

/- Porting note: need a helper theorem for lookmap.go. -/
theorem lookmap.go_append (l : List α) (acc : Array α) :
    lookmap.go f l acc = acc.toListAppend (lookmap f l) := by
  cases l with
  | nil => rfl
  | cons hd tl =>
    rw [lookmap, go, go]
    cases f hd with
    | none => simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.push_data]; rfl
    | some a => rfl

@[simp]
theorem lookmap_nil : [].lookmap f = [] :=
  rfl

@[simp]
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) :
    (a :: l).lookmap f = a :: l.lookmap f := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, Array.data_toArray, nil_append]
  rw [lookmap.go_append, h]; rfl

@[simp]
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) :
    (a :: l).lookmap f = b :: l := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, Array.data_toArray, nil_append]
  rw [h]

theorem lookmap_some : ∀ l : List α, l.lookmap some = l
  | [] => rfl
  | _ :: _ => rfl

theorem lookmap_none : ∀ l : List α, (l.lookmap fun _ => none) = l
  | [] => rfl
  | a :: l => (lookmap_cons_none _ l rfl).trans (congr_arg (cons a) (lookmap_none l))

theorem lookmap_congr {f g : α → Option α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
  | [], _ => rfl
  | a :: l, H => by
    cases' forall_mem_cons.1 H with H₁ H₂
    cases' h : g a with b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]

theorem lookmap_of_forall_not {l : List α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)

theorem lookmap_map_eq (g : α → β) (h : ∀ (a), ∀ b ∈ f a, g a = g b) :
    ∀ l : List α, map g (l.lookmap f) = map g l
  | [] => rfl
  | a :: l => by
    cases' h' : f a with b
    · simpa [h'] using lookmap_map_eq _ h l
    · simp [lookmap_cons_some _ _ h', h _ _ h']

theorem lookmap_id' (h : ∀ (a), ∀ b ∈ f a, a = b) (l : List α) : l.lookmap f = l := by
  rw [← map_id (l.lookmap f), lookmap_map_eq, map_id]; exact h

theorem length_lookmap (l : List α) : length (l.lookmap f) = length l := by
  rw [← length_map, lookmap_map_eq _ fun _ => (), length_map]; simp

end Lookmap

/-! ### filter -/

theorem length_eq_length_filter_add {l : List (α)} (f : α → Bool) :
    l.length = (l.filter f).length + (l.filter (! f ·)).length := by
  simp_rw [← List.countP_eq_length_filter, l.length_eq_countP_add_countP f, Bool.not_eq_true,
    Bool.decide_eq_false]

/-! ### filterMap -/

-- Later porting note (at time of this lemma moving to Batteries):
-- removing attribute `nolint simpNF`
attribute [simp 1100] filterMap_cons_none

-- Later porting note (at time of this lemma moving to Batteries):
-- removing attribute `nolint simpNF`
attribute [simp 1100] filterMap_cons_some

theorem filterMap_eq_bind_toList (f : α → Option β) (l : List α) :
    l.filterMap f = l.bind fun a ↦ (f a).toList := by
  induction' l with a l ih <;> simp [filterMap_cons]
  rcases f a <;> simp [ih]

theorem filterMap_congr {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction' l with a l ih <;> simp [filterMap_cons]
  simp [ih (fun x hx ↦ h x (List.mem_cons_of_mem a hx))]
  cases' hfa : f a with b
  · have : g a = none := Eq.symm (by simpa [hfa] using h a (by simp))
    simp [this]
  · have : g a = some b := Eq.symm (by simpa [hfa] using h a (by simp))
    simp [this]

theorem filterMap_eq_map_iff_forall_eq_some {f : α → Option β} {g : α → β} {l : List α} :
    l.filterMap f = l.map g ↔ ∀ x ∈ l, f x = some (g x) where
  mp := by
    induction' l with a l ih
    · simp
    cases' ha : f a with b <;> simp [ha, filterMap_cons]
    · intro h
      simpa [show (filterMap f l).length = l.length + 1 from by simp[h], Nat.add_one_le_iff]
        using List.length_filterMap_le f l
    · rintro rfl h
      exact ⟨rfl, ih h⟩
  mpr h := Eq.trans (filterMap_congr <| by simpa) (congr_fun (List.filterMap_eq_map _) _)

/-! ### filter -/

section Filter

-- Porting note: Lemmas for `filter` are stated in terms of `p : α → Bool`
-- rather than `p : α → Prop` with `DecidablePred p`, since `filter` itself is.
-- Likewise, `if` sometimes becomes `bif`.
variable {p : α → Bool}

theorem filter_singleton {a : α} : [a].filter p = bif p a then [a] else [] :=
  rfl

theorem filter_eq_foldr (p : α → Bool) (l : List α) :
    filter p l = foldr (fun a out => bif p a then a :: out else out) [] l := by
  induction l <;> simp [*, filter]; rfl

#adaptation_note
/--
This has to be temporarily renamed to avoid an unintentional collision.
The prime should be removed at nightly-2024-07-27.
-/
@[simp]
theorem filter_subset' (l : List α) : filter p l ⊆ l :=
  (filter_sublist l).subset

theorem of_mem_filter {a : α} {l} (h : a ∈ filter p l) : p a := (mem_filter.1 h).2

theorem mem_of_mem_filter {a : α} {l} (h : a ∈ filter p l) : a ∈ l :=
  filter_subset' l h

theorem mem_filter_of_mem {a : α} {l} (h₁ : a ∈ l) (h₂ : p a) : a ∈ filter p l :=
  mem_filter.2 ⟨h₁, h₂⟩

theorem monotone_filter_left (p : α → Bool) ⦃l l' : List α⦄ (h : l ⊆ l') :
    filter p l ⊆ filter p l' := by
  intro x hx
  rw [mem_filter] at hx ⊢
  exact ⟨h hx.left, hx.right⟩

variable (p)

theorem monotone_filter_right (l : List α) ⦃p q : α → Bool⦄
    (h : ∀ a, p a → q a) : l.filter p <+ l.filter q := by
  induction' l with hd tl IH
  · rfl
  · by_cases hp : p hd
    · rw [filter_cons_of_pos hp, filter_cons_of_pos (h _ hp)]
      exact IH.cons_cons hd
    · rw [filter_cons_of_neg hp]
      by_cases hq : q hd
      · rw [filter_cons_of_pos hq]
        exact sublist_cons_of_sublist hd IH
      · rw [filter_cons_of_neg hq]
        exact IH

-- TODO rename to `map_filter` when the deprecated `map_filter` is removed from Lean.
lemma map_filter' {f : α → β} (hf : Injective f) (l : List α)
    [DecidablePred fun b => ∃ a, p a ∧ f a = b] :
    (l.filter p).map f = (l.map f).filter fun b => ∃ a, p a ∧ f a = b := by
  simp [comp_def, filter_map, hf.eq_iff]

lemma filter_attach' (l : List α) (p : {a // a ∈ l} → Bool) [DecidableEq α] :
    l.attach.filter p =
      (l.filter fun x => ∃ h, p ⟨x, h⟩).attach.map (Subtype.map id fun x => mem_of_mem_filter) := by
  classical
  refine map_injective_iff.2 Subtype.coe_injective ?_
  simp [comp_def, map_filter' _ Subtype.coe_injective]

-- Porting note: `Lean.Internal.coeM` forces us to type-ascript `{x // x ∈ l}`
lemma filter_attach (l : List α) (p : α → Bool) :
    (l.attach.filter fun x => p x : List {x // x ∈ l}) =
      (l.filter p).attach.map (Subtype.map id fun x => mem_of_mem_filter) :=
  map_injective_iff.2 Subtype.coe_injective <| by
    simp_rw [map_map, comp_def, Subtype.map, id, ← Function.comp_apply (g := Subtype.val),
      ← filter_map, attach_map_subtype_val]

lemma filter_comm (q) (l : List α) : filter p (filter q l) = filter q (filter p l) := by
  simp [and_comm]

@[simp]
theorem filter_true (l : List α) :
    filter (fun _ => true) l = l := by induction l <;> simp [*, filter]

@[simp]
theorem filter_false (l : List α) :
    filter (fun _ => false) l = [] := by induction l <;> simp [*, filter]

/- Porting note: need a helper theorem for span.loop. -/
theorem span.loop_eq_take_drop :
    ∀ l₁ l₂ : List α, span.loop p l₁ l₂ = (l₂.reverse ++ takeWhile p l₁, dropWhile p l₁)
  | [], l₂ => by simp [span.loop, takeWhile, dropWhile]
  | (a :: l), l₂ => by
    cases hp : p a <;> simp [hp, span.loop, span.loop_eq_take_drop, takeWhile, dropWhile]

@[simp]
theorem span_eq_take_drop (l : List α) : span p l = (takeWhile p l, dropWhile p l) := by
  simpa using span.loop_eq_take_drop p l []

theorem dropWhile_get_zero_not (l : List α) (hl : 0 < (l.dropWhile p).length) :
    ¬p ((l.dropWhile p).get ⟨0, hl⟩) := by
  induction' l with hd tl IH
  · cases hl
  · simp only [dropWhile]
    by_cases hp : p hd
    · simp_all only [get_eq_getElem]
      apply IH
      simp_all only [dropWhile_cons_of_pos]
    · simp [hp]

@[deprecated (since := "2024-08-19")] alias nthLe_cons := getElem_cons
@[deprecated (since := "2024-08-19")] alias dropWhile_nthLe_zero_not := dropWhile_get_zero_not

variable {p} {l : List α}

@[simp]
theorem dropWhile_eq_nil_iff : dropWhile p l = [] ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp [dropWhile]
  · by_cases hp : p x <;> simp [hp, IH]

@[simp]
theorem takeWhile_eq_self_iff : takeWhile p l = l ↔ ∀ x ∈ l, p x := by
  induction' l with x xs IH
  · simp
  · by_cases hp : p x <;> simp [hp, IH]

@[simp]
theorem takeWhile_eq_nil_iff : takeWhile p l = [] ↔ ∀ hl : 0 < l.length, ¬p (l.get ⟨0, hl⟩) := by
  induction' l with x xs IH
  · simp only [takeWhile_nil, Bool.not_eq_true, true_iff]
    intro h
    simp at h
  · by_cases hp : p x <;> simp [hp, IH]

theorem mem_takeWhile_imp {x : α} (hx : x ∈ takeWhile p l) : p x := by
  induction l with simp [takeWhile] at hx
  | cons hd tl IH =>
    cases hp : p hd
    · simp [hp] at hx
    · rw [hp, mem_cons] at hx
      rcases hx with (rfl | hx)
      · exact hp
      · exact IH hx

theorem takeWhile_takeWhile (p q : α → Bool) (l : List α) :
    takeWhile p (takeWhile q l) = takeWhile (fun a => p a ∧ q a) l := by
  induction' l with hd tl IH
  · simp
  · by_cases hp : p hd <;> by_cases hq : q hd <;> simp [takeWhile, hp, hq, IH]

theorem takeWhile_idem : takeWhile p (takeWhile p l) = takeWhile p l := by
  simp_rw [takeWhile_takeWhile, and_self_iff, Bool.decide_coe]

end Filter

/-! ### erasep -/

section eraseP

variable {p : α → Bool}

@[simp]
theorem length_eraseP_add_one {l : List α} {a} (al : a ∈ l) (pa : p a) :
    (l.eraseP p).length + 1 = l.length := by
  let ⟨_, l₁, l₂, _, _, h₁, h₂⟩ := exists_of_eraseP al pa
  rw [h₂, h₁, length_append, length_append]
  rfl

end eraseP

/-! ### erase -/

section Erase

variable [DecidableEq α]

@[simp] theorem length_erase_add_one {a : α} {l : List α} (h : a ∈ l) :
    (l.erase a).length + 1 = l.length := by
  rw [erase_eq_eraseP, length_eraseP_add_one h (decide_eq_true rfl)]

theorem map_erase [DecidableEq β] {f : α → β} (finj : Injective f) {a : α} (l : List α) :
    map f (l.erase a) = (map f l).erase (f a) := by
  have this : (a == ·) = (f a == f ·) := by ext b; simp [beq_eq_decide, finj.eq_iff]
  rw [erase_eq_eraseP, erase_eq_eraseP, eraseP_map, this]; rfl

theorem map_foldl_erase [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (foldl List.erase l₁ l₂) = foldl (fun l a => l.erase (f a)) (map f l₁) l₂ := by
  induction l₂ generalizing l₁ <;> [rfl; simp only [foldl_cons, map_erase finj, *]]

theorem erase_getElem [DecidableEq ι] {l : List ι} {i : ℕ} (hi : i < l.length) :
    Perm (l.erase l[i]) (l.eraseIdx i) := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH =>
    cases i with
    | zero => simp
    | succ i =>
      have hi' : i < l.length := by simpa using hi
      if ha : a = l[i] then
        simpa [ha] using .trans (perm_cons_erase (l.getElem_mem i _)) (.cons _ (IH hi'))
      else
        simpa [ha] using IH hi'

@[deprecated erase_getElem (since := "2024-08-03")]
theorem erase_get [DecidableEq ι] {l : List ι} (i : Fin l.length) :
    Perm (l.erase (l.get i)) (l.eraseIdx ↑i) :=
  erase_getElem i.isLt

theorem length_eraseIdx_add_one {l : List ι} {i : ℕ} (h : i < l.length) :
    (l.eraseIdx i).length + 1 = l.length := calc
  (l.eraseIdx i).length + 1
  _ = (l.take i ++ l.drop (i + 1)).length + 1         := by rw [eraseIdx_eq_take_drop_succ]
  _ = (l.take i).length + (l.drop (i + 1)).length + 1 := by rw [length_append]
  _ = i + (l.drop (i + 1)).length + 1                 := by rw [length_take_of_le (le_of_lt h)]
  _ = i + (l.length - (i + 1)) + 1                    := by rw [length_drop]
  _ = (i + 1) + (l.length - (i + 1))                  := by omega
  _ = l.length                                        := Nat.add_sub_cancel' (succ_le_of_lt h)


end Erase

/-! ### diff -/

section Diff

variable [DecidableEq α]

@[simp]
theorem map_diff [DecidableEq β] {f : α → β} (finj : Injective f) {l₁ l₂ : List α} :
    map f (l₁.diff l₂) = (map f l₁).diff (map f l₂) := by
  simp only [diff_eq_foldl, foldl_map, map_foldl_erase finj]

theorem erase_diff_erase_sublist_of_sublist {a : α} :
    ∀ {l₁ l₂ : List α}, l₁ <+ l₂ → (l₂.erase a).diff (l₁.erase a) <+ l₂.diff l₁
  | [], l₂, _ => erase_sublist _ _
  | b :: l₁, l₂, h =>
    if heq : b = a then by simp only [heq, erase_cons_head, diff_cons]; rfl
    else by
      simp only [erase_cons_head b l₁, erase_cons_tail (not_beq_of_ne heq),
        diff_cons ((List.erase l₂ a)) (List.erase l₁ a) b, diff_cons l₂ l₁ b, erase_comm a b l₂]
      have h' := h.erase b
      rw [erase_cons_head] at h'
      exact @erase_diff_erase_sublist_of_sublist _ l₁ (l₂.erase b) h'

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

/-! ### map₂Left' -/

section Map₂Left'

-- The definitional equalities for `map₂Left'` can already be used by the
-- simplifier because `map₂Left'` is marked `@[simp]`.
@[simp]
theorem map₂Left'_nil_right (f : α → Option β → γ) (as) :
    map₂Left' f as [] = (as.map fun a => f a none, []) := by cases as <;> rfl

end Map₂Left'

/-! ### map₂Right' -/

section Map₂Right'

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂Right'_nil_left : map₂Right' f [] bs = (bs.map (f none), []) := by cases bs <;> rfl

@[simp]
theorem map₂Right'_nil_right : map₂Right' f as [] = ([], as) :=
  rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem map₂Right'_nil_cons : map₂Right' f [] (b :: bs) = (f none b :: bs.map (f none), []) :=
  rfl

@[simp]
theorem map₂Right'_cons_cons :
    map₂Right' f (a :: as) (b :: bs) =
      let r := map₂Right' f as bs
      (f (some a) b :: r.fst, r.snd) :=
  rfl

end Map₂Right'

/-! ### zipLeft' -/

section ZipLeft'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipLeft'_nil_right : zipLeft' as ([] : List β) = (as.map fun a => (a, none), []) := by
  cases as <;> rfl

@[simp]
theorem zipLeft'_nil_left : zipLeft' ([] : List α) bs = ([], bs) :=
  rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem zipLeft'_cons_nil :
    zipLeft' (a :: as) ([] : List β) = ((a, none) :: as.map fun a => (a, none), []) :=
  rfl

@[simp]
theorem zipLeft'_cons_cons :
    zipLeft' (a :: as) (b :: bs) =
      let r := zipLeft' as bs
      ((a, some b) :: r.fst, r.snd) :=
  rfl

end ZipLeft'

/-! ### zipRight' -/

section ZipRight'

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipRight'_nil_left : zipRight' ([] : List α) bs = (bs.map fun b => (none, b), []) := by
  cases bs <;> rfl

@[simp]
theorem zipRight'_nil_right : zipRight' as ([] : List β) = ([], as) :=
  rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem zipRight'_nil_cons :
    zipRight' ([] : List α) (b :: bs) = ((none, b) :: bs.map fun b => (none, b), []) :=
  rfl

@[simp]
theorem zipRight'_cons_cons :
    zipRight' (a :: as) (b :: bs) =
      let r := zipRight' as bs
      ((some a, b) :: r.fst, r.snd) :=
  rfl

end ZipRight'

/-! ### map₂Left -/

section Map₂Left

variable (f : α → Option β → γ) (as : List α)

-- The definitional equalities for `map₂Left` can already be used by the
-- simplifier because `map₂Left` is marked `@[simp]`.
@[simp]
theorem map₂Left_nil_right : map₂Left f as [] = as.map fun a => f a none := by cases as <;> rfl

theorem map₂Left_eq_map₂Left' : ∀ as bs, map₂Left f as bs = (map₂Left' f as bs).fst
  | [], _ => by simp
  | a :: as, [] => by simp
  | a :: as, b :: bs => by simp [map₂Left_eq_map₂Left']

theorem map₂Left_eq_zipWith :
    ∀ as bs, length as ≤ length bs → map₂Left f as bs = zipWith (fun a b => f a (some b)) as bs
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp
  | a :: as, [], h => by
    simp at h
  | a :: as, b :: bs, h => by
    simp only [length_cons, succ_le_succ_iff] at h
    simp [h, map₂Left_eq_zipWith]

end Map₂Left

/-! ### map₂Right -/

section Map₂Right

variable (f : Option α → β → γ) (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem map₂Right_nil_left : map₂Right f [] bs = bs.map (f none) := by cases bs <;> rfl

@[simp]
theorem map₂Right_nil_right : map₂Right f as [] = [] :=
  rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem map₂Right_nil_cons : map₂Right f [] (b :: bs) = f none b :: bs.map (f none) :=
  rfl

@[simp]
theorem map₂Right_cons_cons :
    map₂Right f (a :: as) (b :: bs) = f (some a) b :: map₂Right f as bs :=
  rfl

theorem map₂Right_eq_map₂Right' : map₂Right f as bs = (map₂Right' f as bs).fst := by
  simp only [map₂Right, map₂Right', map₂Left_eq_map₂Left']

theorem map₂Right_eq_zipWith (h : length bs ≤ length as) :
    map₂Right f as bs = zipWith (fun a b => f (some a) b) as bs := by
  have : (fun a b => flip f a (some b)) = flip fun a b => f (some a) b := rfl
  simp only [map₂Right, map₂Left_eq_zipWith, zipWith_flip, *]

end Map₂Right

/-! ### zipLeft -/

section ZipLeft

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipLeft_nil_right : zipLeft as ([] : List β) = as.map fun a => (a, none) := by
  cases as <;> rfl

@[simp]
theorem zipLeft_nil_left : zipLeft ([] : List α) bs = [] :=
  rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem zipLeft_cons_nil :
    zipLeft (a :: as) ([] : List β) = (a, none) :: as.map fun a => (a, none) :=
  rfl

@[simp]
theorem zipLeft_cons_cons : zipLeft (a :: as) (b :: bs) = (a, some b) :: zipLeft as bs :=
  rfl

-- Porting note: arguments explicit for recursion
theorem zipLeft_eq_zipLeft' (as : List α) (bs : List β) : zipLeft as bs = (zipLeft' as bs).fst := by
  rw [zipLeft, zipLeft']
  cases as with
  | nil => rfl
  | cons _ atl =>
    cases bs with
    | nil => rfl
    | cons _ btl =>
      rw [zipWithLeft, zipWithLeft', cons_inj_right]
      exact @zipLeft_eq_zipLeft' atl btl

end ZipLeft

/-! ### zipRight -/

section ZipRight

variable (a : α) (as : List α) (b : β) (bs : List β)

@[simp]
theorem zipRight_nil_left : zipRight ([] : List α) bs = bs.map fun b => (none, b) := by
  cases bs <;> rfl

@[simp]
theorem zipRight_nil_right : zipRight as ([] : List β) = [] :=
  rfl

-- Porting note (#10618): simp can prove this
-- @[simp]
theorem zipRight_nil_cons :
    zipRight ([] : List α) (b :: bs) = (none, b) :: bs.map fun b => (none, b) :=
  rfl

@[simp]
theorem zipRight_cons_cons : zipRight (a :: as) (b :: bs) = (some a, b) :: zipRight as bs :=
  rfl

theorem zipRight_eq_zipRight' : zipRight as bs = (zipRight' as bs).fst := by
  induction as generalizing bs <;> cases bs <;> simp [*]

end ZipRight

/-! ### Forall -/

section Forall

variable {p q : α → Prop} {l : List α}

@[simp]
theorem forall_cons (p : α → Prop) (x : α) : ∀ l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l
  | [] => (and_true_iff _).symm
  | _ :: _ => Iff.rfl

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

@[simp]
theorem getElem_attach (L : List α) (i : Nat) (h : i < L.attach.length) :
    L.attach[i].1 = L[i]'(length_attach L ▸ h) :=
  calc
    L.attach[i].1 = (L.attach.map Subtype.val)[i]'(by simpa using h) := by
      rw [getElem_map]
    _ = L[i]'_ := by congr 2; simp

theorem get_attach (L : List α) (i) :
    (L.attach.get i).1 = L.get ⟨i, length_attach L ▸ i.2⟩ := by simp

@[simp 1100]
theorem mem_map_swap (x : α) (y : β) (xs : List (α × β)) :
    (y, x) ∈ map Prod.swap xs ↔ (x, y) ∈ xs := by
  induction' xs with x xs xs_ih
  · simp only [not_mem_nil, map_nil]
  · cases' x with a b
    simp only [mem_cons, Prod.mk.inj_iff, map, Prod.swap_prod_mk, Prod.exists, xs_ih, and_comm]

theorem dropSlice_eq (xs : List α) (n m : ℕ) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs
  · cases xs <;> simp [dropSlice]
  · cases xs <;> simp [dropSlice, *, Nat.succ_add]

@[simp]
theorem length_dropSlice (i j : ℕ) (xs : List α) :
    (List.dropSlice i j xs).length = xs.length - min j (xs.length - i) := by
  induction xs generalizing i j with
  | nil => simp
  | cons x xs xs_ih =>
    cases i <;> simp only [List.dropSlice]
    · cases j with
      | zero => simp
      | succ n => simp_all [xs_ih]; omega
    · simp [xs_ih]; omega

theorem length_dropSlice_lt (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    (List.dropSlice i j xs).length < xs.length := by
  simp; omega

set_option linter.deprecated false in
@[deprecated (since := "2024-07-25")]
theorem sizeOf_dropSlice_lt [SizeOf α] (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    SizeOf.sizeOf (List.dropSlice i j xs) < SizeOf.sizeOf xs := by
  induction xs generalizing i j hj with
  | nil => cases hi
  | cons x xs xs_ih =>
    cases i <;> simp only [List.dropSlice]
    · cases j with
      | zero => contradiction
      | succ n =>
        dsimp only [drop]; apply lt_of_le_of_lt (drop_sizeOf_le xs n)
        simp only [cons.sizeOf_spec]; omega
    · simp only [cons.sizeOf_spec, Nat.add_lt_add_iff_left]
      apply xs_ih _ j hj
      apply lt_of_succ_lt_succ hi

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
  rw [← pmap_eq_map _ _ _ (fun _ _ ↦ trivial), ← pmap_eq_map _ _ _ (fun _ _ ↦ trivial)]
  exact disjoint_pmap _ _ (fun _ _ _ _ h' ↦ hf h') h


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

variable {α β : Type*} [BEq α] [LawfulBEq α]

lemma lookup_graph (f : α → β) {a : α} {as : List α} (h : a ∈ as) :
    lookup a (as.map fun x => (x, f x)) = some (f a) := by
  induction' as with a' as ih
  · exact (List.not_mem_nil _ h).elim
  · by_cases ha : a = a'
    · simp [ha, lookup_cons]
    · simpa [lookup_cons, beq_false_of_ne ha] using ih (List.mem_of_ne_of_mem ha h)

end lookup

end List

set_option linter.style.longFile 2700
