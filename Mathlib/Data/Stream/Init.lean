/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Stream.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences
-/

open Nat Function Option

namespace Stream'

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}
variable (m n : ℕ) (x y : List α) (a b : Stream' α)

instance [Inhabited α] : Inhabited (Stream' α) :=
  ⟨Stream'.const default⟩

@[simp] protected theorem eta (s : Stream' α) : head s :: tail s = s :=
  funext fun i => by cases i <;> rfl

/-- Alias for `Stream'.eta` to match `List` API. -/
alias cons_head_tail := Stream'.eta

@[ext]
protected theorem ext {s₁ s₂ : Stream' α} : (∀ n, get s₁ n = get s₂ n) → s₁ = s₂ :=
  fun h => funext h

@[simp]
theorem get_zero_cons (a : α) (s : Stream' α) : get (a::s) 0 = a :=
  rfl

@[simp]
theorem head_cons (a : α) (s : Stream' α) : head (a::s) = a :=
  rfl

@[simp]
theorem tail_cons (a : α) (s : Stream' α) : tail (a::s) = s :=
  rfl

@[simp]
theorem get_drop (n m : ℕ) (s : Stream' α) : get (drop m s) n = get s (m + n) := by
  rw [Nat.add_comm]
  rfl

theorem tail_eq_drop (s : Stream' α) : tail s = drop 1 s :=
  rfl

@[simp]
theorem drop_drop (n m : ℕ) (s : Stream' α) : drop n (drop m s) = drop (m + n) s := by
  ext; simp [Nat.add_assoc]

@[simp] theorem get_tail {n : ℕ} {s : Stream' α} : s.tail.get n = s.get (n + 1) := rfl

@[simp] theorem tail_drop' {i : ℕ} {s : Stream' α} : tail (drop i s) = s.drop (i + 1) := by
  ext; simp [Nat.add_comm, Nat.add_left_comm]

@[simp] theorem drop_tail' {i : ℕ} {s : Stream' α} : drop i (tail s) = s.drop (i + 1) := rfl

theorem tail_drop (n : ℕ) (s : Stream' α) : tail (drop n s) = drop n (tail s) := by simp

theorem get_succ (n : ℕ) (s : Stream' α) : get s (succ n) = get (tail s) n :=
  rfl

@[simp]
theorem get_succ_cons (n : ℕ) (s : Stream' α) (x : α) : get (x :: s) n.succ = get s n :=
  rfl

@[simp] lemma get_cons_append_zero {a : α} {x : List α} {s : Stream' α} :
    (a :: x ++ₛ s).get 0 = a := rfl

@[simp] lemma append_eq_cons {a : α} {as : Stream' α} : [a] ++ₛ as = a :: as := rfl

@[simp] theorem drop_zero {s : Stream' α} : s.drop 0 = s := rfl

theorem drop_succ (n : ℕ) (s : Stream' α) : drop (succ n) s = drop n (tail s) :=
  rfl

theorem head_drop (a : Stream' α) (n : ℕ) : (a.drop n).head = a.get n := by simp

theorem cons_injective2 : Function.Injective2 (cons : α → Stream' α → Stream' α) := fun x y s t h =>
  ⟨by rw [← get_zero_cons x s, h, get_zero_cons],
    Stream'.ext fun n => by rw [← get_succ_cons n _ x, h, get_succ_cons]⟩

theorem cons_injective_left (s : Stream' α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _

theorem cons_injective_right (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

theorem all_def (p : α → Prop) (s : Stream' α) : All p s = ∀ n, p (get s n) :=
  rfl

theorem any_def (p : α → Prop) (s : Stream' α) : Any p s = ∃ n, p (get s n) :=
  rfl

@[simp]
theorem mem_cons (a : α) (s : Stream' α) : a ∈ a::s :=
  Exists.intro 0 rfl

theorem mem_cons_of_mem {a : α} {s : Stream' α} (b : α) : a ∈ s → a ∈ b::s := fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [get_succ, tail_cons, h])

theorem eq_or_mem_of_mem_cons {a b : α} {s : Stream' α} : (a ∈ b::s) → a = b ∨ a ∈ s :=
    fun ⟨n, h⟩ => by
  rcases n with - | n'
  · left
    exact h
  · right
    rw [get_succ, tail_cons] at h
    exact ⟨n', h⟩

theorem mem_of_get_eq {n : ℕ} {s : Stream' α} {a : α} : a = get s n → a ∈ s := fun h =>
  Exists.intro n h

theorem mem_iff_exists_get_eq {s : Stream' α} {a : α} : a ∈ s ↔ ∃ n, a = s.get n where
  mp := by simp [Membership.mem, any_def]
  mpr h := mem_of_get_eq h.choose_spec

section Map

variable (f : α → β)

theorem drop_map (n : ℕ) (s : Stream' α) : drop n (map f s) = map f (drop n s) :=
  Stream'.ext fun _ => rfl

@[simp]
theorem get_map (n : ℕ) (s : Stream' α) : get (map f s) n = f (get s n) :=
  rfl

theorem tail_map (s : Stream' α) : tail (map f s) = map f (tail s) := rfl

@[simp]
theorem head_map (s : Stream' α) : head (map f s) = f (head s) :=
  rfl

theorem map_eq (s : Stream' α) : map f s = f (head s)::map f (tail s) := by
  rw [← Stream'.eta (map f s), tail_map, head_map]

theorem map_cons (a : α) (s : Stream' α) : map f (a::s) = f a::map f s := by
  rw [← Stream'.eta (map f (a::s)), map_eq]; rfl

@[simp]
theorem map_id (s : Stream' α) : map id s = s :=
  rfl

@[simp]
theorem map_map (g : β → δ) (f : α → β) (s : Stream' α) : map g (map f s) = map (g ∘ f) s :=
  rfl

@[simp]
theorem map_tail (s : Stream' α) : map f (tail s) = tail (map f s) :=
  rfl

theorem mem_map {a : α} {s : Stream' α} : a ∈ s → f a ∈ map f s := fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])

theorem exists_of_mem_map {f} {b : β} {s : Stream' α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩

end Map

section Zip

variable (f : α → β → δ)

theorem drop_zip (n : ℕ) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  Stream'.ext fun _ => rfl

@[simp]
theorem get_zip (n : ℕ) (s₁ : Stream' α) (s₂ : Stream' β) :
    get (zip f s₁ s₂) n = f (get s₁ n) (get s₂ n) :=
  rfl

theorem head_zip (s₁ : Stream' α) (s₂ : Stream' β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl

theorem tail_zip (s₁ : Stream' α) (s₂ : Stream' β) :
    tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl

theorem zip_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zip f s₁ s₂ = f (head s₁) (head s₂)::zip f (tail s₁) (tail s₂) := by
  rw [← Stream'.eta (zip f s₁ s₂)]; rfl

@[simp]
theorem get_enum (s : Stream' α) (n : ℕ) : get (enum s) n = (n, s.get n) :=
  rfl

theorem enum_eq_zip (s : Stream' α) : enum s = zip Prod.mk nats s :=
  rfl

end Zip

@[simp]
theorem mem_const (a : α) : a ∈ const a :=
  Exists.intro 0 rfl

theorem const_eq (a : α) : const a = a::const a := by
  apply Stream'.ext; intro n
  cases n <;> rfl

@[simp]
theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a::const a) = const a by rwa [← const_eq] at this
  rfl

@[simp]
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl

@[simp]
theorem get_const (n : ℕ) (a : α) : get (const a) n = a :=
  rfl

@[simp]
theorem drop_const (n : ℕ) (a : α) : drop n (const a) = const a :=
  Stream'.ext fun _ => rfl

@[simp]
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl

theorem get_succ_iterate' (n : ℕ) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = f (get (iterate f a) n) := rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  ext n
  rw [get_tail]
  induction n with
  | zero => rfl
  | succ n ih => rw [get_succ_iterate', ih, get_succ_iterate']

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a::iterate f (f a) := by
  rw [← Stream'.eta (iterate f a)]
  rw [tail_iterate]; rfl

@[simp]
theorem get_zero_iterate (f : α → α) (a : α) : get (iterate f a) 0 = a :=
  rfl

theorem get_succ_iterate (n : ℕ) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = get (iterate f (f a)) n := by rw [get_succ, tail_iterate]

section Bisim

variable (R : Stream' α → Stream' α → Prop)

/-- equivalence relation -/
local infixl:50 " ~ " => R

/-- Streams `s₁` and `s₂` are defined to be bisimulations if
their heads are equal and tails are bisimulations. -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ →
      head s₁ = head s₂ ∧ tail s₁ ~ tail s₂

theorem get_of_bisim (bisim : IsBisimulation R) {s₁ s₂} :
    ∀ n, s₁ ~ s₂ → get s₁ n = get s₂ n ∧ drop (n + 1) s₁ ~ drop (n + 1) s₂
  | 0, h => bisim h
  | n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => get_of_bisim bisim n trel

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} : s₁ ~ s₂ → s₁ = s₂ := fun r =>
  Stream'.ext fun n => And.left (get_of_bisim R bisim n r)

end Bisim

theorem bisim_simple (s₁ s₂ : Stream' α) :
    head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by grind)
    (And.intro hh (And.intro ht₁ ht₂))

theorem coinduction {s₁ s₂ : Stream' α} :
    head s₁ = head s₂ →
      (∀ (β : Type u) (fr : Stream' α → β),
      fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂ :=
  fun hh ht =>
  eq_of_bisim
    (fun s₁ s₂ =>
      head s₁ = head s₂ ∧
        ∀ (β : Type u) (fr : Stream' α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂))
    (fun s₁ s₂ h =>
      have h₁ : head s₁ = head s₂ := And.left h
      have h₂ : head (tail s₁) = head (tail s₂) := And.right h α (@head α) h₁
      have h₃ :
        ∀ (β : Type u) (fr : Stream' α → β),
          fr (tail s₁) = fr (tail s₂) → fr (tail (tail s₁)) = fr (tail (tail s₂)) :=
        fun β fr => And.right h β fun s => fr (tail s)
      And.intro h₁ (And.intro h₂ h₃))
    (And.intro hh ht)

@[simp]
theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction rfl fun β fr ch => by rw [tail_iterate, tail_const]; exact ch

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold map iterate get
    rw [map, get] at ih
    rw [iterate]
    exact congrArg f ih

section Corec

theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a :: corec f g (g a) := by
  rw [corec_def, map_eq, head_iterate, tail_iterate]; rfl

theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_def, map_id, iterate_id]

theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl

end Corec

section Corec'

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 :: corec' f (f a).2 :=
  corec_eq _ _ _

end Corec'

theorem unfolds_eq (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a :: unfolds g f (f a) := by
  unfold unfolds; rw [corec_eq]

theorem get_unfolds_head_tail (n : ℕ) (s : Stream' α) : get (unfolds head tail s) n = get s n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, get_succ, unfolds_eq, tail_cons, ih]

theorem unfolds_head_eq : ∀ s : Stream' α, unfolds head tail s = s := fun s =>
  Stream'.ext fun n => get_unfolds_head_tail n s

theorem interleave_eq (s₁ s₂ : Stream' α) : s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂) := by
  let t := tail s₁ ⋈ tail s₂
  change s₁ ⋈ s₂ = head s₁::head s₂::t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl

theorem tail_interleave (s₁ s₂ : Stream' α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  unfold interleave corecOn; rw [corec_eq]; rfl

theorem interleave_tail_tail (s₁ s₂ : Stream' α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [interleave_eq s₁ s₂]; rfl

theorem get_interleave_left : ∀ (n : ℕ) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n) = get s₁ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n))) = get s₁ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons]
    rw [get_interleave_left n (tail s₁) (tail s₂)]
    rfl

theorem get_interleave_right : ∀ (n : ℕ) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n + 1) = get s₂ n
  | 0, _, _ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = get s₂ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons,
      get_interleave_right n (tail s₁) (tail s₂)]
    rfl

theorem mem_interleave_left {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])

theorem mem_interleave_right {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])

theorem odd_eq (s : Stream' α) : odd s = even (tail s) :=
  rfl

@[simp]
theorem head_even (s : Stream' α) : head (even s) = head s :=
  rfl

theorem tail_even (s : Stream' α) : tail (even s) = even (tail (tail s)) := by
  unfold even
  rw [corec_eq]
  rfl

theorem even_cons_cons (a₁ a₂ : α) (s : Stream' α) : even (a₁::a₂::s) = a₁::even s := by
  unfold even
  rw [corec_eq]; rfl

theorem even_tail (s : Stream' α) : even (tail s) = odd s :=
  rfl

theorem even_interleave (s₁ s₂ : Stream' α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)

theorem interleave_even_odd (s₁ : Stream' α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rfl
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl

theorem get_even : ∀ (n : ℕ) (s : Stream' α), get (even s) n = get s (2 * n)
  | 0, _ => rfl
  | succ n, s => by
    change get (even s) (succ n) = get s (succ (succ (2 * n)))
    rw [get_succ, get_succ, tail_even, get_even n]; rfl

theorem get_odd : ∀ (n : ℕ) (s : Stream' α), get (odd s) n = get s (2 * n + 1) := fun n s => by
  rw [odd_eq, get_even]; rfl

theorem mem_of_mem_even (a : α) (s : Stream' α) : a ∈ even s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])

theorem mem_of_mem_odd (a : α) (s : Stream' α) : a ∈ odd s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])

@[simp] theorem nil_append_stream (s : Stream' α) : appendStream' [] s = s :=
  rfl

theorem cons_append_stream (a : α) (l : List α) (s : Stream' α) :
    appendStream' (a::l) s = a::appendStream' l s :=
  rfl

@[simp] theorem append_append_stream : ∀ (l₁ l₂ : List α) (s : Stream' α),
    l₁ ++ l₂ ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
  | [], _, _ => rfl
  | List.cons a l₁, l₂, s => by
    rw [List.cons_append, cons_append_stream, cons_append_stream, append_append_stream l₁]

lemma get_append_left (h : n < x.length) : (x ++ₛ a).get n = x[n] := by
  induction x generalizing n with
  | nil => simp at h
  | cons b x ih =>
    rcases n with (_ | n)
    · simp
    · simp [ih n (by simpa using h), cons_append_stream]

@[simp] lemma get_append_right : (x ++ₛ a).get (x.length + n) = a.get n := by
  induction x <;> simp [Nat.succ_add, *, cons_append_stream]

@[simp] lemma get_append_length : (x ++ₛ a).get x.length = a.get 0 := get_append_right 0 x a

lemma append_right_injective (h : x ++ₛ a = x ++ₛ b) : a = b := by
  ext n; replace h := congr_arg (fun a ↦ a.get (x.length + n)) h; simpa using h

@[simp] lemma append_right_inj : x ++ₛ a = x ++ₛ b ↔ a = b :=
  ⟨append_right_injective x a b, by simp +contextual⟩

lemma append_left_injective (h : x ++ₛ a = y ++ₛ b) (hl : x.length = y.length) : x = y := by
  apply List.ext_getElem hl
  intros
  rw [← get_append_left, ← get_append_left, h]

theorem map_append_stream (f : α → β) :
    ∀ (l : List α) (s : Stream' α), map f (l ++ₛ s) = List.map f l ++ₛ map f s
  | [], _ => rfl
  | List.cons a l, s => by
    rw [cons_append_stream, List.map_cons, map_cons, cons_append_stream, map_append_stream f l]

theorem drop_append_stream : ∀ (l : List α) (s : Stream' α), drop l.length (l ++ₛ s) = s
  | [], s => rfl
  | List.cons a l, s => by
    rw [List.length_cons, drop_succ, cons_append_stream, tail_cons, drop_append_stream l s]

theorem append_stream_head_tail (s : Stream' α) : [head s] ++ₛ tail s = s := by
  simp

theorem mem_append_stream_right : ∀ {a : α} (l : List α) {s : Stream' α}, a ∈ s → a ∈ l ++ₛ s
  | _, [], _, h => h
  | a, List.cons _ l, s, h =>
    have ih : a ∈ l ++ₛ s := mem_append_stream_right l h
    mem_cons_of_mem _ ih

theorem mem_append_stream_left : ∀ {a : α} {l : List α} (s : Stream' α), a ∈ l → a ∈ l ++ₛ s
  | _, [], _, h => absurd h List.not_mem_nil
  | a, List.cons b l, s, h =>
    Or.elim (List.eq_or_mem_of_mem_cons h) (fun aeqb : a = b => Exists.intro 0 aeqb)
      fun ainl : a ∈ l => mem_cons_of_mem b (mem_append_stream_left s ainl)

@[simp]
theorem take_zero (s : Stream' α) : take 0 s = [] :=
  rfl

-- This lemma used to be simp, but we removed it from the simp set because:
-- 1) It duplicates the (often large) `s` term, resulting in large tactic states.
-- 2) It conflicts with the very useful `dropLast_take` lemma below (causing nonconfluence).
theorem take_succ (n : ℕ) (s : Stream' α) : take (succ n) s = head s::take n (tail s) :=
  rfl

@[simp] theorem take_succ_cons {a : α} (n : ℕ) (s : Stream' α) :
    take (n+1) (a::s) = a :: take n s := rfl

theorem take_succ' {s : Stream' α} : ∀ n, s.take (n+1) = s.take n ++ [s.get n]
  | 0 => rfl
  | n+1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, get_tail]

@[simp]
theorem length_take (n : ℕ) (s : Stream' α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]

@[simp]
theorem take_take {s : Stream' α} : ∀ {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [Nat.min_zero, List.take_zero, take_zero]
  | m, 0 => by rw [Nat.zero_min, take_zero, List.take_nil]
  | m+1, n+1 => by rw [take_succ, List.take_succ_cons, Nat.succ_min_succ, take_succ, take_take]

@[simp] theorem concat_take_get {n : ℕ} {s : Stream' α} : s.take n ++ [s.get n] = s.take (n + 1) :=
  (take_succ' n).symm

theorem getElem?_take {s : Stream' α} : ∀ {k n}, k < n → (s.take n)[k]? = s.get k
  | 0, _+1, _ => by simp only [length_take, zero_lt_succ, List.getElem?_eq_getElem]; rfl
  | k+1, n+1, h => by
    rw [take_succ, List.getElem?_cons_succ, getElem?_take (Nat.lt_of_succ_lt_succ h), get_succ]

theorem getElem?_take_succ (n : ℕ) (s : Stream' α) :
    (take (succ n) s)[n]? = some (get s n) :=
  getElem?_take (Nat.lt_succ_self n)

@[simp] theorem dropLast_take {n : ℕ} {xs : Stream' α} :
    (Stream'.take n xs).dropLast = Stream'.take (n-1) xs := by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp]
theorem append_take_drop (n : ℕ) (s : Stream' α) : appendStream' (take n s) (drop n s) = s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Stream'.eta]

lemma append_take : x ++ (a.take n) = (x ++ₛ a).take (x.length + n) := by
  induction x <;> simp [take, Nat.add_comm, cons_append_stream, *]

@[simp] lemma take_get (h : m < (a.take n).length) : (a.take n)[m] = a.get m := by
  nth_rw 2 [← append_take_drop n a]; rw [get_append_left]

theorem take_append_of_le_length (h : n ≤ x.length) :
    (x ++ₛ a).take n = x.take n := by
  apply List.ext_getElem (by simp [h])
  intro _ _ _; rw [List.getElem_take, take_get, get_append_left]

lemma take_add : a.take (m + n) = a.take m ++ (a.drop m).take n := by
  apply append_left_injective _ _ (a.drop (m + n)) ((a.drop m).drop n) <;>
    simp [- drop_drop]

@[gcongr] lemma take_prefix_take_left (h : m ≤ n) : a.take m <+: a.take n := by
  rw [(by simp [h] : a.take m = (a.take n).take m)]
  apply List.take_prefix

@[simp] lemma take_prefix : a.take m <+: a.take n ↔ m ≤ n :=
  ⟨fun h ↦ by simpa using h.length_le, take_prefix_take_left m n a⟩

lemma map_take (f : α → β) : (a.take n).map f = (a.map f).take n := by
  apply List.ext_getElem <;> simp

lemma take_drop : (a.drop m).take n = (a.take (m + n)).drop m := by
  apply List.ext_getElem <;> simp

lemma drop_append_of_le_length (h : n ≤ x.length) :
    (x ++ₛ a).drop n = x.drop n ++ₛ a := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h
  ext k; rcases lt_or_ge k m with _ | hk
  · rw [get_drop, get_append_left, get_append_left, List.getElem_drop]; simpa [hm]
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hm' : m = (x.drop n).length := by simp [hm]
    simp_rw [get_drop, ← Nat.add_assoc, ← hm, get_append_right, hm', get_append_right]

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : Stream' α) (h : ∀ n : ℕ, take n s₁ = take n s₂) : s₁ = s₂ := by
  ext n
  induction n with
  | zero => simpa [take] using h 1
  | succ n =>
    have h₁ : some (get s₁ (succ n)) = some (get s₂ (succ n)) := by
      rw [← getElem?_take_succ, ← getElem?_take_succ, h (succ (succ n))]
    injection h₁

protected theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleG (a, a₁::l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl

theorem cycle_eq : ∀ (l : List α) (h : l ≠ []), cycle l h = l ++ₛ cycle l h
  | [], h => absurd rfl h
  | List.cons a l, _ =>
    have gen (l' a') : corec Stream'.cycleF Stream'.cycleG (a', l', a, l) =
        (a'::l') ++ₛ corec Stream'.cycleF Stream'.cycleG (a, l, a, l) := by
      induction l' generalizing a' with
      | nil => rw [corec_eq]; rfl
      | cons a₁ l₁ ih => rw [corec_eq, Stream'.cycle_g_cons, ih a₁]; rfl
    gen l a

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_stream_left _ ainl

@[simp]
theorem cycle_singleton (a : α) : cycle [a] (by simp) = const a :=
  coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]

theorem tails_eq (s : Stream' α) : tails s = tail s::tails (tail s) := by
  unfold tails; rw [corec_eq]; rfl

@[simp]
theorem get_tails (n : ℕ) (s : Stream' α) : get (tails s) n = drop n (tail s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, drop_succ, tails_eq, tail_cons, ih]

theorem tails_eq_iterate (s : Stream' α) : tails s = iterate tail (tail s) :=
  rfl

theorem inits_core_eq (l : List α) (s : Stream' α) :
    initsCore l s = l::initsCore (l ++ [head s]) (tail s) := by
    unfold initsCore corecOn
    rw [corec_eq]

theorem tail_inits (s : Stream' α) :
    tail (inits s) = initsCore [head s, head (tail s)] (tail (tail s)) := by
    unfold inits
    rw [inits_core_eq]; rfl

theorem inits_tail (s : Stream' α) : inits (tail s) = initsCore [head (tail s)] (tail (tail s)) :=
  rfl

theorem cons_get_inits_core (a : α) (n : ℕ) (l : List α) (s : Stream' α) :
    (a :: get (initsCore l s) n) = get (initsCore (a :: l) s) n := by
  induction n generalizing l s with
  | zero => rfl
  | succ n ih =>
    rw [get_succ, inits_core_eq, tail_cons, ih, inits_core_eq (a :: l) s]
    rfl

@[simp]
theorem get_inits (n : ℕ) (s : Stream' α) : get (inits s) n = take (succ n) s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [get_succ, take_succ, ← ih, tail_inits, inits_tail, cons_get_inits_core]

theorem inits_eq (s : Stream' α) :
    inits s = [head s]::map (List.cons (head s)) (inits (tail s)) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  · rw [get_inits, get_succ, tail_cons, get_map, get_inits]
    rfl

theorem zip_inits_tails (s : Stream' α) : zip appendStream' (inits s) (tails s) = const s := by
  apply Stream'.ext; intro n
  rw [get_zip, get_inits, get_tails, get_const, take_succ, cons_append_stream, append_take_drop,
    Stream'.eta]

theorem identity (s : Stream' α) : pure id ⊛ s = s :=
  rfl

theorem composition (g : Stream' (β → δ)) (f : Stream' (α → β)) (s : Stream' α) :
    pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
  rfl

theorem homomorphism (f : α → β) (a : α) : pure f ⊛ pure a = pure (f a) :=
  rfl

theorem interchange (fs : Stream' (α → β)) (a : α) :
    fs ⊛ pure a = (pure fun f : α → β => f a) ⊛ fs :=
  rfl

theorem map_eq_apply (f : α → β) (s : Stream' α) : map f s = pure f ⊛ s :=
  rfl

theorem get_nats (n : ℕ) : get nats n = n :=
  rfl

theorem nats_eq : nats = cons 0 (map succ nats) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  rw [get_succ]; rfl

end Stream'
