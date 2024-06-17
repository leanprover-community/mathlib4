/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Stream.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Init.Data.List.Basic
import Mathlib.Data.List.Basic

#align_import data.stream.init from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences

Porting note:
This file used to be in the core library. It was moved to `mathlib` and renamed to `init` to avoid
name clashes.  -/

set_option autoImplicit true

open Nat Function Option

namespace Stream'

variable {α : Type u} {β : Type v} {δ : Type w}

instance [Inhabited α] : Inhabited (Stream' α) :=
  ⟨Stream'.const default⟩

protected theorem eta (s : Stream' α) : (head s::tail s) = s :=
  funext fun i => by cases i <;> rfl
#align stream.eta Stream'.eta

@[ext]
protected theorem ext {s₁ s₂ : Stream' α} : (∀ n, get s₁ n = get s₂ n) → s₁ = s₂ :=
  fun h => funext h
#align stream.ext Stream'.ext

@[simp]
theorem get_zero_cons (a : α) (s : Stream' α) : get (a::s) 0 = a :=
  rfl
#align stream.nth_zero_cons Stream'.get_zero_cons

@[simp]
theorem head_cons (a : α) (s : Stream' α) : head (a::s) = a :=
  rfl
#align stream.head_cons Stream'.head_cons

@[simp]
theorem tail_cons (a : α) (s : Stream' α) : tail (a::s) = s :=
  rfl
#align stream.tail_cons Stream'.tail_cons

@[simp]
theorem get_drop (n m : Nat) (s : Stream' α) : get (drop m s) n = get s (n + m) :=
  rfl
#align stream.nth_drop Stream'.get_drop

theorem tail_eq_drop (s : Stream' α) : tail s = drop 1 s :=
  rfl
#align stream.tail_eq_drop Stream'.tail_eq_drop

@[simp]
theorem drop_drop (n m : Nat) (s : Stream' α) : drop n (drop m s) = drop (n + m) s := by
  ext; simp [Nat.add_assoc]
#align stream.drop_drop Stream'.drop_drop

@[simp] theorem get_tail {s : Stream' α} : s.tail.get n = s.get (n + 1) := rfl

@[simp] theorem tail_drop' {s : Stream' α} : tail (drop i s) = s.drop (i+1) := by
  ext; simp [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm]

@[simp] theorem drop_tail' {s : Stream' α} : drop i (tail s) = s.drop (i+1) := rfl

theorem tail_drop (n : Nat) (s : Stream' α) : tail (drop n s) = drop n (tail s) := by simp
#align stream.tail_drop Stream'.tail_drop

theorem get_succ (n : Nat) (s : Stream' α) : get s (succ n) = get (tail s) n :=
  rfl
#align stream.nth_succ Stream'.get_succ

@[simp]
theorem get_succ_cons (n : Nat) (s : Stream' α) (x : α) : get (x::s) n.succ = get s n :=
  rfl
#align stream.nth_succ_cons Stream'.get_succ_cons

@[simp] theorem drop_zero {s : Stream' α} : s.drop 0 = s := rfl

theorem drop_succ (n : Nat) (s : Stream' α) : drop (succ n) s = drop n (tail s) :=
  rfl
#align stream.drop_succ Stream'.drop_succ

theorem head_drop (a : Stream' α) (n : ℕ) : (a.drop n).head = a.get n := by simp
#align stream.head_drop Stream'.head_drop

theorem cons_injective2 : Function.Injective2 (cons : α → Stream' α → Stream' α) := fun x y s t h =>
  ⟨by rw [← get_zero_cons x s, h, get_zero_cons],
    Stream'.ext fun n => by rw [← get_succ_cons n _ x, h, get_succ_cons]⟩
#align stream.cons_injective2 Stream'.cons_injective2

theorem cons_injective_left (s : Stream' α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _
#align stream.cons_injective_left Stream'.cons_injective_left

theorem cons_injective_right (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _
#align stream.cons_injective_right Stream'.cons_injective_right

theorem all_def (p : α → Prop) (s : Stream' α) : All p s = ∀ n, p (get s n) :=
  rfl
#align stream.all_def Stream'.all_def

theorem any_def (p : α → Prop) (s : Stream' α) : Any p s = ∃ n, p (get s n) :=
  rfl
#align stream.any_def Stream'.any_def

@[simp]
theorem mem_cons (a : α) (s : Stream' α) : a ∈ a::s :=
  Exists.intro 0 rfl
#align stream.mem_cons Stream'.mem_cons

theorem mem_cons_of_mem {a : α} {s : Stream' α} (b : α) : a ∈ s → a ∈ b::s := fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [get_succ, tail_cons, h])
#align stream.mem_cons_of_mem Stream'.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} {s : Stream' α} : (a ∈ b::s) → a = b ∨ a ∈ s :=
    fun ⟨n, h⟩ => by
  cases' n with n'
  · left
    exact h
  · right
    rw [get_succ, tail_cons] at h
    exact ⟨n', h⟩
#align stream.eq_or_mem_of_mem_cons Stream'.eq_or_mem_of_mem_cons

theorem mem_of_get_eq {n : Nat} {s : Stream' α} {a : α} : a = get s n → a ∈ s := fun h =>
  Exists.intro n h
#align stream.mem_of_nth_eq Stream'.mem_of_get_eq

section Map

variable (f : α → β)

theorem drop_map (n : Nat) (s : Stream' α) : drop n (map f s) = map f (drop n s) :=
  Stream'.ext fun _ => rfl
#align stream.drop_map Stream'.drop_map

@[simp]
theorem get_map (n : Nat) (s : Stream' α) : get (map f s) n = f (get s n) :=
  rfl
#align stream.nth_map Stream'.get_map

theorem tail_map (s : Stream' α) : tail (map f s) = map f (tail s) := rfl
#align stream.tail_map Stream'.tail_map

@[simp]
theorem head_map (s : Stream' α) : head (map f s) = f (head s) :=
  rfl
#align stream.head_map Stream'.head_map

theorem map_eq (s : Stream' α) : map f s = f (head s)::map f (tail s) := by
  rw [← Stream'.eta (map f s), tail_map, head_map]
#align stream.map_eq Stream'.map_eq

theorem map_cons (a : α) (s : Stream' α) : map f (a::s) = f a::map f s := by
  rw [← Stream'.eta (map f (a::s)), map_eq]; rfl
#align stream.map_cons Stream'.map_cons

@[simp]
theorem map_id (s : Stream' α) : map id s = s :=
  rfl
#align stream.map_id Stream'.map_id

@[simp]
theorem map_map (g : β → δ) (f : α → β) (s : Stream' α) : map g (map f s) = map (g ∘ f) s :=
  rfl
#align stream.map_map Stream'.map_map

@[simp]
theorem map_tail (s : Stream' α) : map f (tail s) = tail (map f s) :=
  rfl
#align stream.map_tail Stream'.map_tail

theorem mem_map {a : α} {s : Stream' α} : a ∈ s → f a ∈ map f s := fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])
#align stream.mem_map Stream'.mem_map

theorem exists_of_mem_map {f} {b : β} {s : Stream' α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩
#align stream.exists_of_mem_map Stream'.exists_of_mem_map

end Map

section Zip

variable (f : α → β → δ)

theorem drop_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  Stream'.ext fun _ => rfl
#align stream.drop_zip Stream'.drop_zip

@[simp]
theorem get_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    get (zip f s₁ s₂) n = f (get s₁ n) (get s₂ n) :=
  rfl
#align stream.nth_zip Stream'.get_zip

theorem head_zip (s₁ : Stream' α) (s₂ : Stream' β) : head (zip f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl
#align stream.head_zip Stream'.head_zip

theorem tail_zip (s₁ : Stream' α) (s₂ : Stream' β) :
    tail (zip f s₁ s₂) = zip f (tail s₁) (tail s₂) :=
  rfl
#align stream.tail_zip Stream'.tail_zip

theorem zip_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zip f s₁ s₂ = f (head s₁) (head s₂)::zip f (tail s₁) (tail s₂) := by
  rw [← Stream'.eta (zip f s₁ s₂)]; rfl
#align stream.zip_eq Stream'.zip_eq

@[simp]
theorem get_enum (s : Stream' α) (n : ℕ) : get (enum s) n = (n, s.get n) :=
  rfl
#align stream.nth_enum Stream'.get_enum

theorem enum_eq_zip (s : Stream' α) : enum s = zip Prod.mk nats s :=
  rfl
#align stream.enum_eq_zip Stream'.enum_eq_zip

end Zip

@[simp]
theorem mem_const (a : α) : a ∈ const a :=
  Exists.intro 0 rfl
#align stream.mem_const Stream'.mem_const

theorem const_eq (a : α) : const a = a::const a := by
  apply Stream'.ext; intro n
  cases n <;> rfl
#align stream.const_eq Stream'.const_eq

@[simp]
theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a::const a) = const a by rwa [← const_eq] at this
  rfl
#align stream.tail_const Stream'.tail_const

@[simp]
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl
#align stream.map_const Stream'.map_const

@[simp]
theorem get_const (n : Nat) (a : α) : get (const a) n = a :=
  rfl
#align stream.nth_const Stream'.get_const

@[simp]
theorem drop_const (n : Nat) (a : α) : drop n (const a) = const a :=
  Stream'.ext fun _ => rfl
#align stream.drop_const Stream'.drop_const

@[simp]
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl
#align stream.head_iterate Stream'.head_iterate

theorem get_succ_iterate' (n : Nat) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = f (get (iterate f a) n) := rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  ext n
  rw [get_tail]
  induction' n with n' ih
  · rfl
  · rw [get_succ_iterate', ih, get_succ_iterate']
#align stream.tail_iterate Stream'.tail_iterate

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a::iterate f (f a) := by
  rw [← Stream'.eta (iterate f a)]
  rw [tail_iterate]; rfl
#align stream.iterate_eq Stream'.iterate_eq

@[simp]
theorem get_zero_iterate (f : α → α) (a : α) : get (iterate f a) 0 = a :=
  rfl
#align stream.nth_zero_iterate Stream'.get_zero_iterate

theorem get_succ_iterate (n : Nat) (f : α → α) (a : α) :
    get (iterate f a) (succ n) = get (iterate f (f a)) n := by rw [get_succ, tail_iterate]
#align stream.nth_succ_iterate Stream'.get_succ_iterate

section Bisim

variable (R : Stream' α → Stream' α → Prop)

/-- equivalence relation -/
local infixl:50 " ~ " => R

/-- Streams `s₁` and `s₂` are defined to be bisimulations if
their heads are equal and tails are bisimulations. -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ →
      head s₁ = head s₂ ∧ tail s₁ ~ tail s₂
#align stream.is_bisimulation Stream'.IsBisimulation

theorem get_of_bisim (bisim : IsBisimulation R) :
    ∀ {s₁ s₂} (n), s₁ ~ s₂ → get s₁ n = get s₂ n ∧ drop (n + 1) s₁ ~ drop (n + 1) s₂
  | _, _, 0, h => bisim h
  | _, _, n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => get_of_bisim bisim n trel
#align stream.nth_of_bisim Stream'.get_of_bisim

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ := fun r =>
  Stream'.ext fun n => And.left (get_of_bisim R bisim n r)
#align stream.eq_of_bisim Stream'.eq_of_bisim

end Bisim

theorem bisim_simple (s₁ s₂ : Stream' α) :
    head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by
      constructor
      · exact h₁
      rw [← h₂, ← h₃]
      (repeat' constructor) <;> assumption)
    (And.intro hh (And.intro ht₁ ht₂))
#align stream.bisim_simple Stream'.bisim_simple

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
#align stream.coinduction Stream'.coinduction

@[simp]
theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction rfl fun β fr ch => by rw [tail_iterate, tail_const]; exact ch
#align stream.iterate_id Stream'.iterate_id

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  funext n
  induction' n with n' ih
  · rfl
  · unfold map iterate get
    rw [map, get] at ih
    rw [iterate]
    exact congrArg f ih
#align stream.map_iterate Stream'.map_iterate

section Corec

theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl
#align stream.corec_def Stream'.corec_def

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a::corec f g (g a) := by
  rw [corec_def, map_eq, head_iterate, tail_iterate]; rfl
#align stream.corec_eq Stream'.corec_eq

theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_def, map_id, iterate_id]
#align stream.corec_id_id_eq_const Stream'.corec_id_id_eq_const

theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl
#align stream.corec_id_f_eq_iterate Stream'.corec_id_f_eq_iterate

end Corec

section Corec'

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1::corec' f (f a).2 :=
  corec_eq _ _ _
#align stream.corec'_eq Stream'.corec'_eq

end Corec'

theorem unfolds_eq (g : α → β) (f : α → α) (a : α) : unfolds g f a = g a::unfolds g f (f a) := by
  unfold unfolds; rw [corec_eq]
#align stream.unfolds_eq Stream'.unfolds_eq

theorem get_unfolds_head_tail : ∀ (n : Nat) (s : Stream' α),
    get (unfolds head tail s) n = get s n := by
  intro n; induction' n with n' ih
  · intro s
    rfl
  · intro s
    rw [get_succ, get_succ, unfolds_eq, tail_cons, ih]
#align stream.nth_unfolds_head_tail Stream'.get_unfolds_head_tail

theorem unfolds_head_eq : ∀ s : Stream' α, unfolds head tail s = s := fun s =>
  Stream'.ext fun n => get_unfolds_head_tail n s
#align stream.unfolds_head_eq Stream'.unfolds_head_eq

theorem interleave_eq (s₁ s₂ : Stream' α) : s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂) := by
  let t := tail s₁ ⋈ tail s₂
  show s₁ ⋈ s₂ = head s₁::head s₂::t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl
#align stream.interleave_eq Stream'.interleave_eq

theorem tail_interleave (s₁ s₂ : Stream' α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  unfold interleave corecOn; rw [corec_eq]; rfl
#align stream.tail_interleave Stream'.tail_interleave

theorem interleave_tail_tail (s₁ s₂ : Stream' α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [interleave_eq s₁ s₂]; rfl
#align stream.interleave_tail_tail Stream'.interleave_tail_tail

theorem get_interleave_left : ∀ (n : Nat) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n) = get s₁ n
  | 0, s₁, s₂ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n))) = get s₁ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons]
    rw [get_interleave_left n (tail s₁) (tail s₂)]
    rfl
#align stream.nth_interleave_left Stream'.get_interleave_left

theorem get_interleave_right : ∀ (n : Nat) (s₁ s₂ : Stream' α),
    get (s₁ ⋈ s₂) (2 * n + 1) = get s₂ n
  | 0, s₁, s₂ => rfl
  | n + 1, s₁, s₂ => by
    change get (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = get s₂ (succ n)
    rw [get_succ, get_succ, interleave_eq, tail_cons, tail_cons,
      get_interleave_right n (tail s₁) (tail s₂)]
    rfl
#align stream.nth_interleave_right Stream'.get_interleave_right

theorem mem_interleave_left {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])
#align stream.mem_interleave_left Stream'.mem_interleave_left

theorem mem_interleave_right {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])
#align stream.mem_interleave_right Stream'.mem_interleave_right

theorem odd_eq (s : Stream' α) : odd s = even (tail s) :=
  rfl
#align stream.odd_eq Stream'.odd_eq

@[simp]
theorem head_even (s : Stream' α) : head (even s) = head s :=
  rfl
#align stream.head_even Stream'.head_even

theorem tail_even (s : Stream' α) : tail (even s) = even (tail (tail s)) := by
  unfold even
  rw [corec_eq]
  rfl
#align stream.tail_even Stream'.tail_even

theorem even_cons_cons (a₁ a₂ : α) (s : Stream' α) : even (a₁::a₂::s) = a₁::even s := by
  unfold even
  rw [corec_eq]; rfl
#align stream.even_cons_cons Stream'.even_cons_cons

theorem even_tail (s : Stream' α) : even (tail s) = odd s :=
  rfl
#align stream.even_tail Stream'.even_tail

theorem even_interleave (s₁ s₂ : Stream' α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      constructor
      · rfl
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
    (Exists.intro s₂ rfl)
#align stream.even_interleave Stream'.even_interleave

theorem interleave_even_odd (s₁ : Stream' α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      · rfl
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
    rfl
#align stream.interleave_even_odd Stream'.interleave_even_odd

theorem get_even : ∀ (n : Nat) (s : Stream' α), get (even s) n = get s (2 * n)
  | 0, s => rfl
  | succ n, s => by
    change get (even s) (succ n) = get s (succ (succ (2 * n)))
    rw [get_succ, get_succ, tail_even, get_even n]; rfl
#align stream.nth_even Stream'.get_even

theorem get_odd : ∀ (n : Nat) (s : Stream' α), get (odd s) n = get s (2 * n + 1) := fun n s => by
  rw [odd_eq, get_even]; rfl
#align stream.nth_odd Stream'.get_odd

theorem mem_of_mem_even (a : α) (s : Stream' α) : a ∈ even s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])
#align stream.mem_of_mem_even Stream'.mem_of_mem_even

theorem mem_of_mem_odd (a : α) (s : Stream' α) : a ∈ odd s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])
#align stream.mem_of_mem_odd Stream'.mem_of_mem_odd

theorem nil_append_stream (s : Stream' α) : appendStream' [] s = s :=
  rfl
#align stream.nil_append_stream Stream'.nil_append_stream

theorem cons_append_stream (a : α) (l : List α) (s : Stream' α) :
    appendStream' (a::l) s = a::appendStream' l s :=
  rfl
#align stream.cons_append_stream Stream'.cons_append_stream

theorem append_append_stream : ∀ (l₁ l₂ : List α) (s : Stream' α),
    l₁ ++ l₂ ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
  | [], l₂, s => rfl
  | List.cons a l₁, l₂, s => by
    rw [List.cons_append, cons_append_stream, cons_append_stream, append_append_stream l₁]
#align stream.append_append_stream Stream'.append_append_stream

theorem map_append_stream (f : α → β) :
    ∀ (l : List α) (s : Stream' α), map f (l ++ₛ s) = List.map f l ++ₛ map f s
  | [], s => rfl
  | List.cons a l, s => by
    rw [cons_append_stream, List.map_cons, map_cons, cons_append_stream, map_append_stream f l]
#align stream.map_append_stream Stream'.map_append_stream

theorem drop_append_stream : ∀ (l : List α) (s : Stream' α), drop l.length (l ++ₛ s) = s
  | [], s => by rfl
  | List.cons a l, s => by
    rw [List.length_cons, drop_succ, cons_append_stream, tail_cons, drop_append_stream l s]
#align stream.drop_append_stream Stream'.drop_append_stream

theorem append_stream_head_tail (s : Stream' α) : [head s] ++ₛ tail s = s := by
  rw [cons_append_stream, nil_append_stream, Stream'.eta]
#align stream.append_stream_head_tail Stream'.append_stream_head_tail

theorem mem_append_stream_right : ∀ {a : α} (l : List α) {s : Stream' α}, a ∈ s → a ∈ l ++ₛ s
  | _, [], _, h => h
  | a, List.cons _ l, s, h =>
    have ih : a ∈ l ++ₛ s := mem_append_stream_right l h
    mem_cons_of_mem _ ih
#align stream.mem_append_stream_right Stream'.mem_append_stream_right

theorem mem_append_stream_left : ∀ {a : α} {l : List α} (s : Stream' α), a ∈ l → a ∈ l ++ₛ s
  | _, [], _, h => absurd h (List.not_mem_nil _)
  | a, List.cons b l, s, h =>
    Or.elim (List.eq_or_mem_of_mem_cons h) (fun aeqb : a = b => Exists.intro 0 aeqb)
      fun ainl : a ∈ l => mem_cons_of_mem b (mem_append_stream_left s ainl)
#align stream.mem_append_stream_left Stream'.mem_append_stream_left

@[simp]
theorem take_zero (s : Stream' α) : take 0 s = [] :=
  rfl
#align stream.take_zero Stream'.take_zero

-- This lemma used to be simp, but we removed it from the simp set because:
-- 1) It duplicates the (often large) `s` term, resulting in large tactic states.
-- 2) It conflicts with the very useful `dropLast_take` lemma below (causing nonconfluence).
theorem take_succ (n : Nat) (s : Stream' α) : take (succ n) s = head s::take n (tail s) :=
  rfl
#align stream.take_succ Stream'.take_succ

@[simp] theorem take_succ_cons (n : Nat) (s : Stream' α) : take (n+1) (a::s) = a :: take n s := rfl

theorem take_succ' {s : Stream' α} : ∀ n, s.take (n+1) = s.take n ++ [s.get n]
  | 0 => rfl
  | n+1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, get_tail]

@[simp]
theorem length_take (n : ℕ) (s : Stream' α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]
#align stream.length_take Stream'.length_take

@[simp]
theorem take_take {s : Stream' α} : ∀ {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [Nat.min_zero, List.take_zero, take_zero]
  | m, 0 => by rw [Nat.zero_min, take_zero, List.take_nil]
  | m+1, n+1 => by rw [take_succ, List.take_cons, Nat.succ_min_succ, take_succ, take_take]

@[simp] theorem concat_take_get {s : Stream' α} : s.take n ++ [s.get n] = s.take (n+1) :=
  (take_succ' n).symm

theorem get?_take {s : Stream' α} : ∀ {k n}, k < n → (s.take n).get? k = s.get k
  | 0, n+1, _ => rfl
  | k+1, n+1, h => by rw [take_succ, List.get?, get?_take (Nat.lt_of_succ_lt_succ h), get_succ]

theorem get?_take_succ (n : Nat) (s : Stream' α) :
    List.get? (take (succ n) s) n = some (get s n) :=
  get?_take (Nat.lt_succ_self n)
#align stream.nth_take_succ Stream'.get?_take_succ

@[simp] theorem dropLast_take {xs : Stream' α} :
    (Stream'.take n xs).dropLast = Stream'.take (n-1) xs := by
  cases n with
  | zero => simp
  | succ n => rw [take_succ', List.dropLast_concat, Nat.add_one_sub_one]

@[simp]
theorem append_take_drop : ∀ (n : Nat) (s : Stream' α),
    appendStream' (take n s) (drop n s) = s := by
  intro n
  induction' n with n' ih
  · intro s
    rfl
  · intro s
    rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Stream'.eta]
#align stream.append_take_drop Stream'.append_take_drop

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : Stream' α) : (∀ n : Nat, take n s₁ = take n s₂) → s₁ = s₂ := by
  intro h; apply Stream'.ext; intro n
  induction' n with n _
  · have aux := h 1
    simp? [take] at aux says
      simp only [take, List.cons.injEq, and_true] at aux
    exact aux
  · have h₁ : some (get s₁ (succ n)) = some (get s₂ (succ n)) := by
      rw [← get?_take_succ, ← get?_take_succ, h (succ (succ n))]
    injection h₁
#align stream.take_theorem Stream'.take_theorem

protected theorem cycle_g_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleG (a, a₁::l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl
#align stream.cycle_g_cons Stream'.cycle_g_cons

theorem cycle_eq : ∀ (l : List α) (h : l ≠ []), cycle l h = l ++ₛ cycle l h
  | [], h => absurd rfl h
  | List.cons a l, _ =>
    have gen : ∀ l' a', corec Stream'.cycleF Stream'.cycleG (a', l', a, l) =
        (a'::l') ++ₛ corec Stream'.cycleF Stream'.cycleG (a, l, a, l) := by
      intro l'
      induction' l' with a₁ l₁ ih
      · intros
        rw [corec_eq]
        rfl
      · intros
        rw [corec_eq, Stream'.cycle_g_cons, ih a₁]
        rfl
    gen l a
#align stream.cycle_eq Stream'.cycle_eq

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_stream_left _ ainl
#align stream.mem_cycle Stream'.mem_cycle

@[simp]
theorem cycle_singleton (a : α) : cycle [a] (by simp) = const a :=
  coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]
#align stream.cycle_singleton Stream'.cycle_singleton

theorem tails_eq (s : Stream' α) : tails s = tail s::tails (tail s) := by
  unfold tails; rw [corec_eq]; rfl
#align stream.tails_eq Stream'.tails_eq

@[simp]
theorem get_tails : ∀ (n : Nat) (s : Stream' α), get (tails s) n = drop n (tail s) := by
  intro n; induction' n with n' ih
  · intros
    rfl
  · intro s
    rw [get_succ, drop_succ, tails_eq, tail_cons, ih]
#align stream.nth_tails Stream'.get_tails

theorem tails_eq_iterate (s : Stream' α) : tails s = iterate tail (tail s) :=
  rfl
#align stream.tails_eq_iterate Stream'.tails_eq_iterate

theorem inits_core_eq (l : List α) (s : Stream' α) :
    initsCore l s = l::initsCore (l ++ [head s]) (tail s) := by
    unfold initsCore corecOn
    rw [corec_eq]
#align stream.inits_core_eq Stream'.inits_core_eq

theorem tail_inits (s : Stream' α) :
    tail (inits s) = initsCore [head s, head (tail s)] (tail (tail s)) := by
    unfold inits
    rw [inits_core_eq]; rfl
#align stream.tail_inits Stream'.tail_inits

theorem inits_tail (s : Stream' α) : inits (tail s) = initsCore [head (tail s)] (tail (tail s)) :=
  rfl
#align stream.inits_tail Stream'.inits_tail

theorem cons_get_inits_core :
    ∀ (a : α) (n : Nat) (l : List α) (s : Stream' α),
      (a::get (initsCore l s) n) = get (initsCore (a::l) s) n := by
  intro a n
  induction' n with n' ih
  · intros
    rfl
  · intro l s
    rw [get_succ, inits_core_eq, tail_cons, ih, inits_core_eq (a::l) s]
    rfl
#align stream.cons_nth_inits_core Stream'.cons_get_inits_core

@[simp]
theorem get_inits : ∀ (n : Nat) (s : Stream' α), get (inits s) n = take (succ n) s := by
  intro n; induction' n with n' ih
  · intros
    rfl
  · intros
    rw [get_succ, take_succ, ← ih, tail_inits, inits_tail, cons_get_inits_core]
#align stream.nth_inits Stream'.get_inits

theorem inits_eq (s : Stream' α) :
    inits s = [head s]::map (List.cons (head s)) (inits (tail s)) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  · rw [get_inits, get_succ, tail_cons, get_map, get_inits]
    rfl
#align stream.inits_eq Stream'.inits_eq

theorem zip_inits_tails (s : Stream' α) : zip appendStream' (inits s) (tails s) = const s := by
  apply Stream'.ext; intro n
  rw [get_zip, get_inits, get_tails, get_const, take_succ, cons_append_stream, append_take_drop,
    Stream'.eta]
#align stream.zip_inits_tails Stream'.zip_inits_tails

theorem identity (s : Stream' α) : pure id ⊛ s = s :=
  rfl
#align stream.identity Stream'.identity

theorem composition (g : Stream' (β → δ)) (f : Stream' (α → β)) (s : Stream' α) :
    pure comp ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
  rfl
#align stream.composition Stream'.composition

theorem homomorphism (f : α → β) (a : α) : pure f ⊛ pure a = pure (f a) :=
  rfl
#align stream.homomorphism Stream'.homomorphism

theorem interchange (fs : Stream' (α → β)) (a : α) :
    fs ⊛ pure a = (pure fun f : α → β => f a) ⊛ fs :=
  rfl
#align stream.interchange Stream'.interchange

theorem map_eq_apply (f : α → β) (s : Stream' α) : map f s = pure f ⊛ s :=
  rfl
#align stream.map_eq_apply Stream'.map_eq_apply

theorem get_nats (n : Nat) : get nats n = n :=
  rfl
#align stream.nth_nats Stream'.get_nats

theorem nats_eq : nats = cons 0 (map succ nats) := by
  apply Stream'.ext; intro n
  cases n
  · rfl
  rw [get_succ]; rfl
#align stream.nats_eq Stream'.nats_eq

end Stream'
