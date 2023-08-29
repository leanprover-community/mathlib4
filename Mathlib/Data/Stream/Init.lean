/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Tactic.Ext
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
                     -- ⊢ (head s :: tail s) zero = s zero
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align stream.eta Stream'.eta

@[ext]
protected theorem ext {s₁ s₂ : Stream' α} : (∀ n, nth s₁ n = nth s₂ n) → s₁ = s₂ :=
  fun h => funext h
#align stream.ext Stream'.ext

@[simp]
theorem nth_zero_cons (a : α) (s : Stream' α) : nth (a::s) 0 = a :=
  rfl
#align stream.nth_zero_cons Stream'.nth_zero_cons

@[simp]
theorem head_cons (a : α) (s : Stream' α) : head (a::s) = a :=
  rfl
#align stream.head_cons Stream'.head_cons

@[simp]
theorem tail_cons (a : α) (s : Stream' α) : tail (a::s) = s :=
  rfl
#align stream.tail_cons Stream'.tail_cons

@[simp]
theorem nth_drop (n m : Nat) (s : Stream' α) : nth (drop m s) n = nth s (n + m) :=
  rfl
#align stream.nth_drop Stream'.nth_drop

theorem tail_eq_drop (s : Stream' α) : tail s = drop 1 s :=
  rfl
#align stream.tail_eq_drop Stream'.tail_eq_drop

@[simp]
theorem drop_drop (n m : Nat) (s : Stream' α) : drop n (drop m s) = drop (n + m) s := by
  ext; simp [Nat.add_assoc]
  -- ⊢ nth (drop n (drop m s)) n✝ = nth (drop (n + m) s) n✝
       -- 🎉 no goals
#align stream.drop_drop Stream'.drop_drop

@[simp] theorem nth_tail {s : Stream' α} : s.tail.nth n = s.nth (n + 1) := rfl

@[simp] theorem tail_drop' {s : Stream' α} : tail (drop i s) = s.drop (i+1) := by
  ext; simp [add_comm, add_assoc, add_left_comm]
  -- ⊢ nth (tail (drop i s)) n✝ = nth (drop (i + 1) s) n✝
       -- 🎉 no goals

@[simp] theorem drop_tail' {s : Stream' α} : drop i (tail s) = s.drop (i+1) := rfl

theorem tail_drop (n : Nat) (s : Stream' α) : tail (drop n s) = drop n (tail s) := by simp
                                                                                      -- 🎉 no goals
#align stream.tail_drop Stream'.tail_drop

theorem nth_succ (n : Nat) (s : Stream' α) : nth s (succ n) = nth (tail s) n :=
  rfl
#align stream.nth_succ Stream'.nth_succ

@[simp]
theorem nth_succ_cons (n : Nat) (s : Stream' α) (x : α) : nth (x::s) n.succ = nth s n :=
  rfl
#align stream.nth_succ_cons Stream'.nth_succ_cons

@[simp] theorem drop_zero {s : Stream' α} : s.drop 0 = s := rfl

theorem drop_succ (n : Nat) (s : Stream' α) : drop (succ n) s = drop n (tail s) :=
  rfl
#align stream.drop_succ Stream'.drop_succ

theorem head_drop (a : Stream' α) (n : ℕ) : (a.drop n).head = a.nth n := by simp
                                                                            -- 🎉 no goals
#align stream.head_drop Stream'.head_drop

theorem cons_injective2 : Function.Injective2 (cons : α → Stream' α → Stream' α) := fun x y s t h =>
  ⟨by rw [← nth_zero_cons x s, h, nth_zero_cons],
      -- 🎉 no goals
    Stream'.ext fun n => by rw [← nth_succ_cons n _ x, h, nth_succ_cons]⟩
                            -- 🎉 no goals
#align stream.cons_injective2 Stream'.cons_injective2

theorem cons_injective_left (s : Stream' α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _
#align stream.cons_injective_left Stream'.cons_injective_left

theorem cons_injective_right (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _
#align stream.cons_injective_right Stream'.cons_injective_right

theorem all_def (p : α → Prop) (s : Stream' α) : All p s = ∀ n, p (nth s n) :=
  rfl
#align stream.all_def Stream'.all_def

theorem any_def (p : α → Prop) (s : Stream' α) : Any p s = ∃ n, p (nth s n) :=
  rfl
#align stream.any_def Stream'.any_def

@[simp]
theorem mem_cons (a : α) (s : Stream' α) : a ∈ a::s :=
  Exists.intro 0 rfl
#align stream.mem_cons Stream'.mem_cons

theorem mem_cons_of_mem {a : α} {s : Stream' α} (b : α) : a ∈ s → a ∈ b::s := fun ⟨n, h⟩ =>
  Exists.intro (succ n) (by rw [nth_succ, tail_cons, h])
                            -- 🎉 no goals
#align stream.mem_cons_of_mem Stream'.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} {s : Stream' α} : (a ∈ b::s) → a = b ∨ a ∈ s :=
    fun ⟨n, h⟩ => by
  cases' n with n'
  -- ⊢ a = b ∨ a ∈ s
  · left
    -- ⊢ a = b
    exact h
    -- 🎉 no goals
  · right
    -- ⊢ a ∈ s
    rw [nth_succ, tail_cons] at h
    -- ⊢ a ∈ s
    exact ⟨n', h⟩
    -- 🎉 no goals
#align stream.eq_or_mem_of_mem_cons Stream'.eq_or_mem_of_mem_cons

theorem mem_of_nth_eq {n : Nat} {s : Stream' α} {a : α} : a = nth s n → a ∈ s := fun h =>
  Exists.intro n h
#align stream.mem_of_nth_eq Stream'.mem_of_nth_eq

section Map

variable (f : α → β)

theorem drop_map (n : Nat) (s : Stream' α) : drop n (map f s) = map f (drop n s) :=
  Stream'.ext fun _ => rfl
#align stream.drop_map Stream'.drop_map

@[simp]
theorem nth_map (n : Nat) (s : Stream' α) : nth (map f s) n = f (nth s n) :=
  rfl
#align stream.nth_map Stream'.nth_map

theorem tail_map (s : Stream' α) : tail (map f s) = map f (tail s) := rfl
#align stream.tail_map Stream'.tail_map

@[simp]
theorem head_map (s : Stream' α) : head (map f s) = f (head s) :=
  rfl
#align stream.head_map Stream'.head_map

theorem map_eq (s : Stream' α) : map f s = f (head s)::map f (tail s) := by
  rw [← Stream'.eta (map f s), tail_map, head_map]
  -- 🎉 no goals
#align stream.map_eq Stream'.map_eq

theorem map_cons (a : α) (s : Stream' α) : map f (a::s) = f a::map f s := by
  rw [← Stream'.eta (map f (a::s)), map_eq]; rfl
  -- ⊢ head (f (head (a :: s)) :: map f (tail (a :: s))) :: tail (f (head (a :: s)) …
                                             -- 🎉 no goals
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
  Exists.intro n (by rw [nth_map, h])
                     -- 🎉 no goals
#align stream.mem_map Stream'.mem_map

theorem exists_of_mem_map {f} {b : β} {s : Stream' α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨nth s n, ⟨n, rfl⟩, h.symm⟩
#align stream.exists_of_mem_map Stream'.exists_of_mem_map

end Map

section Zip

variable (f : α → β → δ)

theorem drop_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zip f s₁ s₂) = zip f (drop n s₁) (drop n s₂) :=
  Stream'.ext fun _ => rfl
#align stream.drop_zip Stream'.drop_zip

@[simp]
theorem nth_zip (n : Nat) (s₁ : Stream' α) (s₂ : Stream' β) :
    nth (zip f s₁ s₂) n = f (nth s₁ n) (nth s₂ n) :=
  rfl
#align stream.nth_zip Stream'.nth_zip

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
  -- ⊢ head (zip f s₁ s₂) :: tail (zip f s₁ s₂) = f (head s₁) (head s₂) :: zip f (t …
                                    -- 🎉 no goals
#align stream.zip_eq Stream'.zip_eq

@[simp]
theorem nth_enum (s : Stream' α) (n : ℕ) : nth (enum s) n = (n, s.nth n) :=
  rfl
#align stream.nth_enum Stream'.nth_enum

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
  -- ⊢ ∀ (n : ℕ), nth (const a) n = nth (a :: const a) n
                     -- ⊢ nth (const a) n = nth (a :: const a) n
  cases n <;> rfl
  -- ⊢ nth (const a) zero = nth (a :: const a) zero
              -- 🎉 no goals
              -- 🎉 no goals
#align stream.const_eq Stream'.const_eq

@[simp]
theorem tail_const (a : α) : tail (const a) = const a :=
  suffices tail (a::const a) = const a by rwa [← const_eq] at this
                                          -- 🎉 no goals
  rfl
#align stream.tail_const Stream'.tail_const

@[simp]
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl
#align stream.map_const Stream'.map_const

@[simp]
theorem nth_const (n : Nat) (a : α) : nth (const a) n = a :=
  rfl
#align stream.nth_const Stream'.nth_const

@[simp]
theorem drop_const (n : Nat) (a : α) : drop n (const a) = const a :=
  Stream'.ext fun _ => rfl
#align stream.drop_const Stream'.drop_const

@[simp]
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl
#align stream.head_iterate Stream'.head_iterate

theorem nth_succ_iterate' (n : Nat) (f : α → α) (a : α) :
    nth (iterate f a) (succ n) = f (nth (iterate f a) n) := rfl

theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) := by
  ext n
  -- ⊢ nth (tail (iterate f a)) n = nth (iterate f (f a)) n
  rw [nth_tail]
  -- ⊢ nth (iterate f a) (n + 1) = nth (iterate f (f a)) n
  induction' n with n' ih
  -- ⊢ nth (iterate f a) (zero + 1) = nth (iterate f (f a)) zero
  · rfl
    -- 🎉 no goals
  · rw [nth_succ_iterate', ih, nth_succ_iterate']
    -- 🎉 no goals
#align stream.tail_iterate Stream'.tail_iterate

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a::iterate f (f a) := by
  rw [← Stream'.eta (iterate f a)]
  -- ⊢ head (iterate f a) :: tail (iterate f a) = a :: iterate f (f a)
  rw [tail_iterate]; rfl
  -- ⊢ head (iterate f a) :: iterate f (f a) = a :: iterate f (f a)
                     -- 🎉 no goals
#align stream.iterate_eq Stream'.iterate_eq

@[simp]
theorem nth_zero_iterate (f : α → α) (a : α) : nth (iterate f a) 0 = a :=
  rfl
#align stream.nth_zero_iterate Stream'.nth_zero_iterate

theorem nth_succ_iterate (n : Nat) (f : α → α) (a : α) :
    nth (iterate f a) (succ n) = nth (iterate f (f a)) n := by rw [nth_succ, tail_iterate]
                                                               -- 🎉 no goals
#align stream.nth_succ_iterate Stream'.nth_succ_iterate

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

theorem nth_of_bisim (bisim : IsBisimulation R) :
    ∀ {s₁ s₂} (n), s₁ ~ s₂ → nth s₁ n = nth s₂ n ∧ drop (n + 1) s₁ ~ drop (n + 1) s₂
  | _, _, 0, h => bisim h
  | _, _, n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => nth_of_bisim bisim n trel
#align stream.nth_of_bisim Stream'.nth_of_bisim

-- If two streams are bisimilar, then they are equal
theorem eq_of_bisim (bisim : IsBisimulation R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ := fun r =>
  Stream'.ext fun n => And.left (nth_of_bisim R bisim n r)
#align stream.eq_of_bisim Stream'.eq_of_bisim

end Bisim

theorem bisim_simple (s₁ s₂ : Stream' α) :
    head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by
      constructor; exact h₁; rw [← h₂, ← h₃]
      -- ⊢ head s₁ = head s₂
                   -- ⊢ (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂) (tail s₁) (ta …
                             -- ⊢ (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂) s₁ s₂
      (repeat' constructor) <;> assumption)
                                -- 🎉 no goals
                                -- 🎉 no goals
                                -- 🎉 no goals
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
                                    -- ⊢ fr (iterate id (id a)) = fr (const a)
                                                                   -- 🎉 no goals
#align stream.iterate_id Stream'.iterate_id

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  funext n
  -- ⊢ iterate f (f a) n = map f (iterate f a) n
  induction' n with n' ih
  -- ⊢ iterate f (f a) zero = map f (iterate f a) zero
  · rfl
    -- 🎉 no goals
  · unfold map iterate nth
    -- ⊢ f (iterate f (f a) n') = f (iterate f a (succ n'))
    rw [map, nth] at ih
    -- ⊢ f (iterate f (f a) n') = f (iterate f a (succ n'))
    rw [iterate]
    -- ⊢ f (iterate f (f a) n') = f (f (iterate f a n'))
    exact congrArg f ih
    -- 🎉 no goals
#align stream.map_iterate Stream'.map_iterate

section Corec

theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl
#align stream.corec_def Stream'.corec_def

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a::corec f g (g a) := by
  rw [corec_def, map_eq, head_iterate, tail_iterate]; rfl
  -- ⊢ f a :: map f (iterate g (g a)) = f a :: corec f g (g a)
                                                      -- 🎉 no goals
#align stream.corec_eq Stream'.corec_eq

theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  rw [corec_def, map_id, iterate_id]
  -- 🎉 no goals
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
  -- ⊢ corec g f a = g a :: corec g f (f a)
                  -- 🎉 no goals
#align stream.unfolds_eq Stream'.unfolds_eq

theorem nth_unfolds_head_tail : ∀ (n : Nat) (s : Stream' α),
    nth (unfolds head tail s) n = nth s n := by
  intro n; induction' n with n' ih
  -- ⊢ ∀ (s : Stream' α), nth (unfolds head tail s) n = nth s n
           -- ⊢ ∀ (s : Stream' α), nth (unfolds head tail s) zero = nth s zero
  · intro s
    -- ⊢ nth (unfolds head tail s) zero = nth s zero
    rfl
    -- 🎉 no goals
  · intro s
    -- ⊢ nth (unfolds head tail s) (succ n') = nth s (succ n')
    rw [nth_succ, nth_succ, unfolds_eq, tail_cons, ih]
    -- 🎉 no goals
#align stream.nth_unfolds_head_tail Stream'.nth_unfolds_head_tail

theorem unfolds_head_eq : ∀ s : Stream' α, unfolds head tail s = s := fun s =>
  Stream'.ext fun n => nth_unfolds_head_tail n s
#align stream.unfolds_head_eq Stream'.unfolds_head_eq

theorem interleave_eq (s₁ s₂ : Stream' α) : s₁ ⋈ s₂ = head s₁::head s₂::(tail s₁ ⋈ tail s₂) := by
  let t := tail s₁ ⋈ tail s₂
  -- ⊢ s₁ ⋈ s₂ = head s₁ :: head s₂ :: (tail s₁ ⋈ tail s₂)
  show s₁ ⋈ s₂ = head s₁::head s₂::t
  -- ⊢ s₁ ⋈ s₂ = head s₁ :: head s₂ :: t
  unfold interleave; unfold corecOn; rw [corec_eq]; dsimp; rw [corec_eq]; rfl
  -- ⊢ (corecOn (s₁, s₂)
                     -- ⊢ corec
                                     -- ⊢ (match (s₁, s₂) with
                                                    -- ⊢ head s₁ :: corec (fun x => head x.fst) (fun x => (x.snd, tail x.fst)) (s₂, t …
                                                           -- ⊢ head s₁ :: head (s₂, tail s₁).fst :: corec (fun x => head x.fst) (fun x => ( …
                                                                          -- 🎉 no goals
#align stream.interleave_eq Stream'.interleave_eq

theorem tail_interleave (s₁ s₂ : Stream' α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  unfold interleave corecOn; rw [corec_eq]; rfl
  -- ⊢ tail
                             -- ⊢ tail
                                            -- 🎉 no goals
#align stream.tail_interleave Stream'.tail_interleave

theorem interleave_tail_tail (s₁ s₂ : Stream' α) : tail s₁ ⋈ tail s₂ = tail (tail (s₁ ⋈ s₂)) := by
  rw [interleave_eq s₁ s₂]; rfl
  -- ⊢ tail s₁ ⋈ tail s₂ = tail (tail (head s₁ :: head s₂ :: (tail s₁ ⋈ tail s₂)))
                            -- 🎉 no goals
#align stream.interleave_tail_tail Stream'.interleave_tail_tail

theorem nth_interleave_left : ∀ (n : Nat) (s₁ s₂ : Stream' α),
    nth (s₁ ⋈ s₂) (2 * n) = nth s₁ n
  | 0, s₁, s₂ => rfl
  | n + 1, s₁, s₂ => by
    change nth (s₁ ⋈ s₂) (succ (succ (2 * n))) = nth s₁ (succ n)
    -- ⊢ nth (s₁ ⋈ s₂) (succ (succ (2 * n))) = nth s₁ (succ n)
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons]
    -- ⊢ nth (tail s₁ ⋈ tail s₂) (2 * n) = nth s₁ (succ n)
    have : n < succ n := Nat.lt_succ_self n
    -- ⊢ nth (tail s₁ ⋈ tail s₂) (2 * n) = nth s₁ (succ n)
    rw [nth_interleave_left n (tail s₁) (tail s₂)]
    -- ⊢ nth (tail s₁) n = nth s₁ (succ n)
    rfl
    -- 🎉 no goals
#align stream.nth_interleave_left Stream'.nth_interleave_left

theorem nth_interleave_right : ∀ (n : Nat) (s₁ s₂ : Stream' α),
    nth (s₁ ⋈ s₂) (2 * n + 1) = nth s₂ n
  | 0, s₁, s₂ => rfl
  | n + 1, s₁, s₂ => by
    change nth (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = nth s₂ (succ n)
    -- ⊢ nth (s₁ ⋈ s₂) (succ (succ (2 * n + 1))) = nth s₂ (succ n)
    rw [nth_succ, nth_succ, interleave_eq, tail_cons, tail_cons,
      nth_interleave_right n (tail s₁) (tail s₂)]
    rfl
    -- 🎉 no goals
#align stream.nth_interleave_right Stream'.nth_interleave_right

theorem mem_interleave_left {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, nth_interleave_left])
                                         -- 🎉 no goals
#align stream.mem_interleave_left Stream'.mem_interleave_left

theorem mem_interleave_right {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, nth_interleave_right])
                                             -- 🎉 no goals
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
  -- ⊢ tail (corec (fun s => head s) (fun s => tail (tail s)) s) = corec (fun s =>  …
  rw [corec_eq]
  -- ⊢ tail (head s :: corec (fun s => head s) (fun s => tail (tail s)) (tail (tail …
  rfl
  -- 🎉 no goals
#align stream.tail_even Stream'.tail_even

theorem even_cons_cons (a₁ a₂ : α) (s : Stream' α) : even (a₁::a₂::s) = a₁::even s := by
  unfold even
  -- ⊢ corec (fun s => head s) (fun s => tail (tail s)) (a₁ :: a₂ :: s) = a₁ :: cor …
  rw [corec_eq]; rfl
  -- ⊢ head (a₁ :: a₂ :: s) :: corec (fun s => head s) (fun s => tail (tail s)) (ta …
                 -- 🎉 no goals
#align stream.even_cons_cons Stream'.even_cons_cons

theorem even_tail (s : Stream' α) : even (tail s) = odd s :=
  rfl
#align stream.even_tail Stream'.even_tail

theorem even_interleave (s₁ s₂ : Stream' α) : even (s₁ ⋈ s₂) = s₁ :=
  eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    (fun s₁' s₁ ⟨s₂, h₁⟩ => by
      rw [h₁]
      -- ⊢ head (even (s₁ ⋈ s₂)) = head s₁ ∧ (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂)) …
      constructor
      -- ⊢ head (even (s₁ ⋈ s₂)) = head s₁
      · rfl
        -- 🎉 no goals
      · exact ⟨tail s₂, by rw [interleave_eq, even_cons_cons, tail_cons]⟩)
        -- 🎉 no goals
    (Exists.intro s₂ rfl)
#align stream.even_interleave Stream'.even_interleave

theorem interleave_even_odd (s₁ : Stream' α) : even s₁ ⋈ odd s₁ = s₁ :=
  eq_of_bisim (fun s' s => s' = even s ⋈ odd s)
    (fun s' s (h : s' = even s ⋈ odd s) => by
      rw [h]; constructor
      -- ⊢ head (even s ⋈ odd s) = head s ∧ (fun s' s => s' = even s ⋈ odd s) (tail (ev …
              -- ⊢ head (even s ⋈ odd s) = head s
      · rfl
        -- 🎉 no goals
      · simp [odd_eq, odd_eq, tail_interleave, tail_even])
        -- 🎉 no goals
    rfl
#align stream.interleave_even_odd Stream'.interleave_even_odd

theorem nth_even : ∀ (n : Nat) (s : Stream' α), nth (even s) n = nth s (2 * n)
  | 0, s => rfl
  | succ n, s => by
    change nth (even s) (succ n) = nth s (succ (succ (2 * n)))
    -- ⊢ nth (even s) (succ n) = nth s (succ (succ (2 * n)))
    rw [nth_succ, nth_succ, tail_even, nth_even n]; rfl
    -- ⊢ nth (tail (tail s)) (2 * n) = nth (tail s) (2 * n + 1)
                                                    -- 🎉 no goals
#align stream.nth_even Stream'.nth_even

theorem nth_odd : ∀ (n : Nat) (s : Stream' α), nth (odd s) n = nth s (2 * n + 1) := fun n s => by
  rw [odd_eq, nth_even]; rfl
  -- ⊢ nth (tail s) (2 * n) = nth s (2 * n + 1)
                         -- 🎉 no goals
#align stream.nth_odd Stream'.nth_odd

theorem mem_of_mem_even (a : α) (s : Stream' α) : a ∈ even s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, nth_even])
                           -- 🎉 no goals
#align stream.mem_of_mem_even Stream'.mem_of_mem_even

theorem mem_of_mem_odd (a : α) (s : Stream' α) : a ∈ odd s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, nth_odd])
                               -- 🎉 no goals
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
    -- 🎉 no goals
#align stream.append_append_stream Stream'.append_append_stream

theorem map_append_stream (f : α → β) :
    ∀ (l : List α) (s : Stream' α), map f (l ++ₛ s) = List.map f l ++ₛ map f s
  | [], s => rfl
  | List.cons a l, s => by
    rw [cons_append_stream, List.map_cons, map_cons, cons_append_stream, map_append_stream f l]
    -- 🎉 no goals
#align stream.map_append_stream Stream'.map_append_stream

theorem drop_append_stream : ∀ (l : List α) (s : Stream' α), drop l.length (l ++ₛ s) = s
  | [], s => by rfl
                -- 🎉 no goals
  | List.cons a l, s => by
    rw [List.length_cons, drop_succ, cons_append_stream, tail_cons, drop_append_stream l s]
    -- 🎉 no goals
#align stream.drop_append_stream Stream'.drop_append_stream

theorem append_stream_head_tail (s : Stream' α) : [head s] ++ₛ tail s = s := by
  rw [cons_append_stream, nil_append_stream, Stream'.eta]
  -- 🎉 no goals
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

theorem take_succ' {s : Stream' α} : ∀ n, s.take (n+1) = s.take n ++ [s.nth n]
  | 0 => rfl
  | n+1 => by rw [take_succ, take_succ' n, ← List.cons_append, ← take_succ, nth_tail]
              -- 🎉 no goals

@[simp]
theorem length_take (n : ℕ) (s : Stream' α) : (take n s).length = n := by
  induction n generalizing s <;> simp [*, take_succ]
  -- ⊢ List.length (take zero s) = zero
                                 -- 🎉 no goals
                                 -- 🎉 no goals
#align stream.length_take Stream'.length_take

@[simp]
theorem take_take {s : Stream' α} : ∀ {m n}, (s.take n).take m = s.take (min n m)
  | 0, n => by rw [min_zero, List.take_zero, take_zero]
               -- 🎉 no goals
  | m, 0 => by rw [zero_min, take_zero, List.take_nil]
               -- 🎉 no goals
  | m+1, n+1 => by rw [take_succ, List.take_cons, Nat.min_succ_succ, take_succ, take_take]
                   -- 🎉 no goals

@[simp] theorem concat_take_nth {s : Stream' α} : s.take n ++ [s.nth n] = s.take (n+1) :=
  (take_succ' n).symm

theorem get?_take {s : Stream' α} : ∀ {k n}, k < n → (s.take n).get? k = s.nth k
  | 0, n+1, _ => rfl
  | k+1, n+1, h => by rw [take_succ, List.get?, get?_take (Nat.lt_of_succ_lt_succ h), nth_succ]
                      -- 🎉 no goals

theorem get?_take_succ (n : Nat) (s : Stream' α) :
    List.get? (take (succ n) s) n = some (nth s n) :=
  get?_take (Nat.lt_succ_self n)
#align stream.nth_take_succ Stream'.get?_take_succ

@[simp] theorem dropLast_take {xs : Stream' α} :
    (Stream'.take n xs).dropLast = Stream'.take (n-1) xs := by
  cases n; case zero => simp
  -- ⊢ List.dropLast (take zero xs) = take (zero - 1) xs
           -- ⊢ List.dropLast (take (succ n✝) xs) = take (succ n✝ - 1) xs
           -- 🎉 no goals
  case succ n => rw [take_succ', List.dropLast_concat, Nat.succ_sub_one]
  -- 🎉 no goals
  -- 🎉 no goals

@[simp]
theorem append_take_drop : ∀ (n : Nat) (s : Stream' α),
    appendStream' (take n s) (drop n s) = s := by
  intro n
  -- ⊢ ∀ (s : Stream' α), take n s ++ₛ drop n s = s
  induction' n with n' ih
  -- ⊢ ∀ (s : Stream' α), take zero s ++ₛ drop zero s = s
  · intro s
    -- ⊢ take zero s ++ₛ drop zero s = s
    rfl
    -- 🎉 no goals
  · intro s
    -- ⊢ take (succ n') s ++ₛ drop (succ n') s = s
    rw [take_succ, drop_succ, cons_append_stream, ih (tail s), Stream'.eta]
    -- 🎉 no goals
#align stream.append_take_drop Stream'.append_take_drop

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : Stream' α) : (∀ n : Nat, take n s₁ = take n s₂) → s₁ = s₂ := by
  intro h; apply Stream'.ext; intro n
  -- ⊢ s₁ = s₂
           -- ⊢ ∀ (n : ℕ), nth s₁ n = nth s₂ n
                              -- ⊢ nth s₁ n = nth s₂ n
  induction' n with n _
  -- ⊢ nth s₁ zero = nth s₂ zero
  · have aux := h 1
    -- ⊢ nth s₁ zero = nth s₂ zero
    simp [take] at aux
    -- ⊢ nth s₁ zero = nth s₂ zero
    exact aux
    -- 🎉 no goals
  · have h₁ : some (nth s₁ (succ n)) = some (nth s₂ (succ n)) := by
      rw [← get?_take_succ, ← get?_take_succ, h (succ (succ n))]
    injection h₁
    -- 🎉 no goals
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
      -- ⊢ ∀ (a' : α), corec Stream'.cycleF Stream'.cycleG (a', l', a, l) = a' :: l' ++ …
      induction' l' with a₁ l₁ ih
      -- ⊢ ∀ (a' : α), corec Stream'.cycleF Stream'.cycleG (a', [], a, l) = [a'] ++ₛ co …
      · intros
        -- ⊢ corec Stream'.cycleF Stream'.cycleG (a'✝, [], a, l) = [a'✝] ++ₛ corec Stream …
        rw [corec_eq]
        -- ⊢ Stream'.cycleF (a'✝, [], a, l) :: corec Stream'.cycleF Stream'.cycleG (Strea …
        rfl
        -- 🎉 no goals
      · intros
        -- ⊢ corec Stream'.cycleF Stream'.cycleG (a'✝, a₁ :: l₁, a, l) = a'✝ :: a₁ :: l₁  …
        rw [corec_eq, Stream'.cycle_g_cons, ih a₁]
        -- ⊢ Stream'.cycleF (a'✝, a₁ :: l₁, a, l) :: (a₁ :: l₁ ++ₛ corec Stream'.cycleF S …
        rfl
        -- 🎉 no goals
    gen l a
#align stream.cycle_eq Stream'.cycle_eq

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_stream_left _ ainl
  -- ⊢ a ∈ l ++ₛ cycle l h
                 -- 🎉 no goals
#align stream.mem_cycle Stream'.mem_cycle

@[simp]
theorem cycle_singleton (a : α) : cycle [a] (by simp) = const a :=
                                                -- 🎉 no goals
  coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]
                                    -- 🎉 no goals
#align stream.cycle_singleton Stream'.cycle_singleton

theorem tails_eq (s : Stream' α) : tails s = tail s::tails (tail s) := by
  unfold tails; rw [corec_eq]; rfl
  -- ⊢ corec id tail (tail s) = tail s :: corec id tail (tail (tail s))
                -- ⊢ id (tail s) :: corec id tail (tail (tail s)) = tail s :: corec id tail (tail …
                               -- 🎉 no goals
#align stream.tails_eq Stream'.tails_eq

@[simp]
theorem nth_tails : ∀ (n : Nat) (s : Stream' α), nth (tails s) n = drop n (tail s) := by
  intro n; induction' n with n' ih
  -- ⊢ ∀ (s : Stream' α), nth (tails s) n = drop n (tail s)
           -- ⊢ ∀ (s : Stream' α), nth (tails s) zero = drop zero (tail s)
  · intros
    -- ⊢ nth (tails s✝) zero = drop zero (tail s✝)
    rfl
    -- 🎉 no goals
  · intro s
    -- ⊢ nth (tails s) (succ n') = drop (succ n') (tail s)
    rw [nth_succ, drop_succ, tails_eq, tail_cons, ih]
    -- 🎉 no goals
#align stream.nth_tails Stream'.nth_tails

theorem tails_eq_iterate (s : Stream' α) : tails s = iterate tail (tail s) :=
  rfl
#align stream.tails_eq_iterate Stream'.tails_eq_iterate

theorem inits_core_eq (l : List α) (s : Stream' α) :
    initsCore l s = l::initsCore (l ++ [head s]) (tail s) := by
    unfold initsCore corecOn
    -- ⊢ corec
    rw [corec_eq]
    -- 🎉 no goals
#align stream.inits_core_eq Stream'.inits_core_eq

theorem tail_inits (s : Stream' α) :
    tail (inits s) = initsCore [head s, head (tail s)] (tail (tail s)) := by
    unfold inits
    -- ⊢ tail (initsCore [head s] (tail s)) = initsCore [head s, head (tail s)] (tail …
    rw [inits_core_eq]; rfl
    -- ⊢ tail ([head s] :: initsCore ([head s] ++ [head (tail s)]) (tail (tail s))) = …
                        -- 🎉 no goals
#align stream.tail_inits Stream'.tail_inits

theorem inits_tail (s : Stream' α) : inits (tail s) = initsCore [head (tail s)] (tail (tail s)) :=
  rfl
#align stream.inits_tail Stream'.inits_tail

theorem cons_nth_inits_core :
    ∀ (a : α) (n : Nat) (l : List α) (s : Stream' α),
      (a::nth (initsCore l s) n) = nth (initsCore (a::l) s) n := by
  intro a n
  -- ⊢ ∀ (l : List α) (s : Stream' α), a :: nth (initsCore l s) n = nth (initsCore  …
  induction' n with n' ih
  -- ⊢ ∀ (l : List α) (s : Stream' α), a :: nth (initsCore l s) zero = nth (initsCo …
  · intros
    -- ⊢ a :: nth (initsCore l✝ s✝) zero = nth (initsCore (a :: l✝) s✝) zero
    rfl
    -- 🎉 no goals
  · intro l s
    -- ⊢ a :: nth (initsCore l s) (succ n') = nth (initsCore (a :: l) s) (succ n')
    rw [nth_succ, inits_core_eq, tail_cons, ih, inits_core_eq (a::l) s]
    -- ⊢ nth (initsCore (a :: (l ++ [head s])) (tail s)) n' = nth ((a :: l) :: initsC …
    rfl
    -- 🎉 no goals
#align stream.cons_nth_inits_core Stream'.cons_nth_inits_core

@[simp]
theorem nth_inits : ∀ (n : Nat) (s : Stream' α), nth (inits s) n = take (succ n) s := by
  intro n; induction' n with n' ih
  -- ⊢ ∀ (s : Stream' α), nth (inits s) n = take (succ n) s
           -- ⊢ ∀ (s : Stream' α), nth (inits s) zero = take (succ zero) s
  · intros
    -- ⊢ nth (inits s✝) zero = take (succ zero) s✝
    rfl
    -- 🎉 no goals
  · intros
    -- ⊢ nth (inits s✝) (succ n') = take (succ (succ n')) s✝
    rw [nth_succ, take_succ, ← ih, tail_inits, inits_tail, cons_nth_inits_core]
    -- 🎉 no goals
#align stream.nth_inits Stream'.nth_inits

theorem inits_eq (s : Stream' α) :
    inits s = [head s]::map (List.cons (head s)) (inits (tail s)) := by
  apply Stream'.ext; intro n
  -- ⊢ ∀ (n : ℕ), nth (inits s) n = nth ([head s] :: map (List.cons (head s)) (init …
                     -- ⊢ nth (inits s) n = nth ([head s] :: map (List.cons (head s)) (inits (tail s)) …
  cases n
  -- ⊢ nth (inits s) zero = nth ([head s] :: map (List.cons (head s)) (inits (tail  …
  · rfl
    -- 🎉 no goals
  · rw [nth_inits, nth_succ, tail_cons, nth_map, nth_inits]
    -- ⊢ take (succ (succ n✝)) s = head s :: take (succ n✝) (tail s)
    rfl
    -- 🎉 no goals
#align stream.inits_eq Stream'.inits_eq

theorem zip_inits_tails (s : Stream' α) : zip appendStream' (inits s) (tails s) = const s := by
  apply Stream'.ext; intro n
  -- ⊢ ∀ (n : ℕ), nth (zip appendStream' (inits s) (tails s)) n = nth (const s) n
                     -- ⊢ nth (zip appendStream' (inits s) (tails s)) n = nth (const s) n
  rw [nth_zip, nth_inits, nth_tails, nth_const, take_succ, cons_append_stream, append_take_drop,
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

theorem nth_nats (n : Nat) : nth nats n = n :=
  rfl
#align stream.nth_nats Stream'.nth_nats

theorem nats_eq : nats = cons 0 (map succ nats) := by
  apply Stream'.ext; intro n
  -- ⊢ ∀ (n : ℕ), nth nats n = nth (0 :: map succ nats) n
                     -- ⊢ nth nats n = nth (0 :: map succ nats) n
  cases n; rfl; rw [nth_succ]; rfl
  -- ⊢ nth nats zero = nth (0 :: map succ nats) zero
           -- ⊢ nth nats (succ n✝) = nth (0 :: map succ nats) (succ n✝)
                -- ⊢ nth (tail nats) n✝ = nth (0 :: map succ nats) (succ n✝)
                               -- 🎉 no goals
#align stream.nats_eq Stream'.nats_eq

end Stream'
