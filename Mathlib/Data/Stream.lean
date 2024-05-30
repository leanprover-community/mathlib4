/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.SuccPred

#align_import data.stream.defs from "leanprover-community/mathlib"@"39af7d3bf61a98e928812dbc3e16f4ea8b795ca3"
#align_import data.stream.init from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is an infinite list with elements of `α` where all elements after the first
are computed on-demand. (This is logically sound because `Stream' α` is dealed as `ℕ → α` in the
kernel.) In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.

## Main definitions

Given a type `α`:

* `Stream' α` : the type of streams whose elements have type `α`
-/

open Nat Function Option List

universe u v w

/-- This type is used to represent infinite list in the runtime. -/
unsafe inductive Stream'Impl (α : Type u)
  /-- Prepend an element to a thunk of an infinite list. -/
  | cons (head : α) (tail : Thunk (Stream'Impl α)) : Stream'Impl α

namespace Stream'Impl

variable {α : Type u} {β : Type v} {δ : Type w}

/-- Destructor for `Stream'Impl α`. -/
@[inline]
unsafe def dest : Stream'Impl α → α × Stream'Impl α
  | cons a t => (a, Thunk.get t)

/-- Corecursor for the stream. -/
@[specialize]
unsafe def corec' (f : α → β × α) (a : α) : Stream'Impl β :=
  match f a with
  | (a, b) => cons a ⟨fun _ => corec' f b⟩

/-- Corecursor where it is possible to return a fully formed value at any point of the
computation. -/
@[specialize]
unsafe def corec'' (f : β → Stream'Impl α ⊕ α × β) (b : β) : Stream'Impl α :=
  match f b with
  | Sum.inl c => c
  | Sum.inr (a, b) => cons a ⟨fun _ => corec'' f b⟩

end Stream'Impl

open Stream'Impl

/-- A stream `Stream' α` is an infinite list of elements of `α`.
This type has special support in the runtime. -/
@[opaque_repr]
structure Stream' (α : Type u) where
  /-- Convert a `ℕ → α` into a `Stream' α`. Consider using other functions like `corec` before
  use this. -/
  mk ::
  /-- Get the `n`-th element of a stream. -/
  get : ℕ → α
#align stream Stream'
#align stream.nth Stream'.get

namespace Stream'

variable {α : Type u} {β : Type v} {δ : Type w}

@[ext]
protected theorem ext {s₁ s₂ : Stream' α} (h : ∀ n, get s₁ n = get s₂ n) : s₁ = s₂ :=
  congr_arg mk (funext h)
#align stream.ext Stream'.ext

/-- Prepend an element to a stream. -/
@[inline]
unsafe def consUnsafe (a : α) (s : Stream' α) : Stream' α :=
  unsafeCast (cons a (Thunk.pure (unsafeCast s)))

@[inherit_doc consUnsafe, implemented_by consUnsafe]
def cons (a : α) (s : Stream' α) : Stream' α where
  get
  | 0 => a
  | n + 1 => get s n
#align stream.cons Stream'.cons

@[inherit_doc cons]
infixr:67 " ::ₛ " => cons

@[simp]
theorem get_zero_cons (a : α) (s : Stream' α) : get (a ::ₛ s) 0 = a :=
  rfl
#align stream.nth_zero_cons Stream'.get_zero_cons

@[simp]
theorem get_succ_cons (n : ℕ) (s : Stream' α) (x : α) : get (x ::ₛ s) (n + 1) = get s n :=
  rfl
#align stream.nth_succ_cons Stream'.get_succ_cons

/-- Head of a stream: `Stream'.head (h ::ₛ t) := h`. -/
noncomputable def head (s : Stream' α) : α :=
  get s 0
#align stream.head Stream'.head

theorem get_zero (s : Stream' α) : get s 0 = head s :=
  rfl

@[simp]
theorem head_mk (f : ℕ → α) : head (mk f) = f 0 :=
  rfl

@[simp]
theorem head_cons (a : α) (s : Stream' α) : head (a ::ₛ s) = a :=
  rfl
#align stream.head_cons Stream'.head_cons

/-- Tail of a stream: `Stream'.tail (h ::ₛ t) := t`. -/
noncomputable def tail (s : Stream' α) : Stream' α where
  get i := get s (i + 1)
#align stream.tail Stream'.tail

/-- Destructor for a stream: `Stream'.dest (h ::ₛ t) := (h, t)`. -/
@[inline]
unsafe def destUnsafe (s : Stream' α) : α × Stream' α :=
  unsafeCast (dest (unsafeCast s) : α × Stream'Impl α)

@[inherit_doc destUnsafe, implemented_by destUnsafe, simp]
def dest (s : Stream' α) : α × Stream' α :=
  (head s, tail s)

@[higher_order dest_fst']
theorem dest_fst (s : Stream' α) : Prod.fst (dest s) = head s :=
  rfl

@[higher_order dest_snd']
theorem dest_snd (s : Stream' α) : Prod.snd (dest s) = tail s :=
  rfl

attribute [simp] dest_fst' dest_snd'

@[inherit_doc head, inline]
def headComputable (s : Stream' α) : α :=
  Prod.fst (dest s)

@[csimp]
theorem head_eq_headComputable : @head.{u} = @headComputable.{u} :=
  rfl

@[inherit_doc tail, inline]
def tailComputable (s : Stream' α) : Stream' α :=
  Prod.snd (dest s)

@[csimp]
theorem tail_eq_tailComputable : @tail.{u} = @tailComputable.{u} :=
  rfl

protected theorem eta (s : Stream' α) : head s ::ₛ tail s = s := by
  ext (_ | n) <;> rfl
#align stream.eta Stream'.eta

theorem get_succ (s : Stream' α) (n : ℕ) : get s (n + 1) = get (tail s) n :=
  rfl
#align stream.nth_succ Stream'.get_succ

@[simp]
theorem tail_cons (a : α) (s : Stream' α) : tail (a ::ₛ s) = s :=
  rfl
#align stream.tail_cons Stream'.tail_cons

theorem dest_cons (a : α) (s : Stream' α) : dest (a ::ₛ s) = (a, s) :=
  rfl

theorem cons_injective2 : Function.Injective2 (cons : α → Stream' α → Stream' α) := by
  intro a₁ a₂ s₁ s₂ h
  constructor
  · simpa using congr_arg head h
  · simpa using congr_arg tail h
#align stream.cons_injective2 Stream'.cons_injective2

@[simp]
theorem cons_eq_cons {a₁ a₂ : α} {s₁ s₂ : Stream' α} : a₁ ::ₛ s₁ = a₂ ::ₛ s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  cons_injective2.eq_iff

theorem dest_eq_cons {s : Stream' α} {a s'} (hs : dest s = (a, s')) : s = a ::ₛ s' := by
  simp at hs
  rw [← Stream'.eta s, hs.left, hs.right]

/-- Recursion principle for sequences, compare with `List.recOn`. -/
@[elab_as_elim]
def recOn' {C : Stream' α → Sort v} (s : Stream' α) (cons : ∀ x s, C (x ::ₛ s)) : C s :=
  match H : dest s with
  | (a, s') => cast (congr_arg C (dest_eq_cons H)).symm (cons a s')

theorem dest_injective : Injective (dest : Stream' α → α × Stream' α) := by
  intro s₁ s₂ hs
  cases s₂ using recOn' with
  | cons a s₂ => rw [dest_cons] at hs; exact dest_eq_cons hs

theorem cons_injective_left (s : Stream' α) : Function.Injective (· ::ₛ s) :=
  cons_injective2.left _
#align stream.cons_injective_left Stream'.cons_injective_left

theorem cons_injective_right (x : α) : Function.Injective (x ::ₛ ·) :=
  cons_injective2.right _
#align stream.cons_injective_right Stream'.cons_injective_right

@[inherit_doc get, simp]
def getComputable (s : Stream' α) : ℕ → α
  | 0     => head s
  | n + 1 => getComputable (tail s) n

@[csimp]
theorem get_eq_getComputable : @get.{u} = @getComputable.{u} := by
  funext α s n
  induction n generalizing s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, ← hn]

/-- The implemention of `Stream'.casesOn`. -/
@[inline]
protected def casesOnComputable {α : Type u} {motive : Stream' α → Sort*}
    (s : Stream' α) (mk : (get : ℕ → α) → motive (mk get)) : motive s :=
  mk (get s)

@[csimp]
theorem casesOn_eq_casesOnComputable :
    @Stream'.casesOn.{v, u} = @Stream'.casesOnComputable.{v, u} :=
  rfl

instance : GetElem (Stream' α) ℕ α (fun _ _ => True) where
  getElem s n _ := get s n

@[simp]
theorem getElem_eq_get (s : Stream' α) (n : ℕ) (h : True) : s[n]'h = get s n :=
  rfl

/-- Drop first `n` elements of a stream. -/
def drop : ℕ → Stream' α → Stream' α
  | 0    , s => s
  | n + 1, s => drop n (tail s)
#align stream.drop Stream'.drop

section Drop

@[simp]
theorem drop_zero (s : Stream' α) : drop 0 s = s :=
  rfl

@[simp]
theorem drop_succ (n : ℕ) (s : Stream' α) : drop (n + 1) s = drop n (tail s) :=
  rfl
#align stream.drop_succ Stream'.drop_succ

@[simp]
theorem head_drop (n : ℕ) (s : Stream' α) : head (drop n s) = get s n := by
  induction n generalizing s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, hn]
#align stream.head_drop Stream'.head_drop

theorem tail_eq_drop (s : Stream' α) : tail s = drop 1 s :=
  rfl
#align stream.tail_eq_drop Stream'.tail_eq_drop

@[simp]
theorem tail_drop (n : ℕ) (s : Stream' α) : tail (drop n s) = drop n (tail s) := by
  induction n generalizing s with
  | zero => simp
  | succ n hn => simp [hn]

@[simp]
theorem get_drop (n m : ℕ) (s : Stream' α) : get (drop m s) n = get s (m + n) := by
  induction n generalizing s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, hn, ← Nat.add_assoc]
#align stream.nth_drop Stream'.get_drop

@[simp]
theorem drop_drop (n m : ℕ) (s : Stream' α) : drop m (drop n s) = drop (m + n) s := by
  ext; simp [← Nat.add_assoc, Nat.add_comm n m]
#align stream.drop_drop Stream'.drop_drop

end Drop

section Bisim

variable (R : Stream' α → Stream' α → Prop)

/-- Streams `s₁` and `s₂` are defined to be bisimulations if
their heads are equal and tails are bisimulations. -/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, R s₁ s₂ → head s₁ = head s₂ ∧ R (tail s₁) (tail s₂)
#align stream.is_bisimulation Stream'.IsBisimulation

theorem get_of_bisim (bisim : IsBisimulation R) :
    ∀ {s₁ s₂} (n), R s₁ s₂ → get s₁ n = get s₂ n ∧ R (drop (n + 1) s₁) (drop (n + 1) s₂)
  | _, _, 0, h =>
    match bisim h with
    | ⟨hl, hr⟩ => ⟨hl, hr⟩
  | _, _, n + 1, h =>
    match bisim h with
    | ⟨_, trel⟩ => get_of_bisim bisim n trel
#align stream.nth_of_bisim Stream'.get_of_bisim

/-- If two streams are bisimilar, then they are equal. -/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : R s₁ s₂) : s₁ = s₂ :=
  Stream'.ext fun n => And.left (get_of_bisim R bisim n r)
#align stream.eq_of_bisim Stream'.eq_of_bisim

end Bisim

theorem bisim_simple (s₁ s₂ : Stream' α) :
    head s₁ = head s₂ → s₁ = tail s₁ → s₂ = tail s₂ → s₁ = s₂ := fun hh ht₁ ht₂ =>
  eq_of_bisim (fun s₁ s₂ => head s₁ = head s₂ ∧ s₁ = tail s₁ ∧ s₂ = tail s₂)
    (fun s₁ s₂ ⟨h₁, h₂, h₃⟩ => by
      constructor
      · exact h₁
      · rw [← h₂, ← h₃]; (repeat' constructor) <;> assumption)
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

/-- Proposition saying that all elements of a stream satisfy a predicate. -/
def All (p : α → Prop) (s : Stream' α) :=
  ∀ n, p (get s n)
#align stream.all Stream'.All

theorem all_def (p : α → Prop) (s : Stream' α) : All p s = ∀ n, p (get s n) :=
  rfl
#align stream.all_def Stream'.all_def

/-- Proposition saying that at least one element of a stream satisfies a predicate. -/
def Any (p : α → Prop) (s : Stream' α) :=
  ∃ n, p (get s n)
#align stream.any Stream'.Any

theorem any_def (p : α → Prop) (s : Stream' α) : Any p s = ∃ n, p (get s n) :=
  rfl
#align stream.any_def Stream'.any_def

/-- `a ∈ s` means that `a = Stream'.get s n` for some `n`. -/
instance : Membership α (Stream' α) :=
  ⟨fun a s => Any (Eq a) s⟩

theorem mem_cons_self (a : α) (s : Stream' α) : a ∈ a ::ₛ s :=
  Exists.intro 0 rfl
#align stream.mem_cons Stream'.mem_cons_self

theorem mem_cons_of_mem {a : α} {s : Stream' α} (b : α) : a ∈ s → a ∈ b ::ₛ s := fun ⟨n, h⟩ =>
  Exists.intro (n + 1) (by rw [get_succ, tail_cons, h])
#align stream.mem_cons_of_mem Stream'.mem_cons_of_mem

theorem eq_or_mem_of_mem_cons {a b : α} {s : Stream' α} : a ∈ b ::ₛ s → a = b ∨ a ∈ s := by
  rintro ⟨n, h⟩
  cases n with
  | zero =>
    left
    exact h
  | succ n' =>
    right
    rw [get_succ, tail_cons] at h
    exact ⟨n', h⟩
#align stream.eq_or_mem_of_mem_cons Stream'.eq_or_mem_of_mem_cons

@[simp]
theorem mem_cons {a b : α} {s : Stream' α} : a ∈ b ::ₛ s ↔ a = b ∨ a ∈ s := by
  constructor
  · exact eq_or_mem_of_mem_cons
  · rintro (rfl | _)
    · apply mem_cons_self
    · apply mem_cons_of_mem
      assumption

@[simp]
theorem mem_get (n : ℕ) (s : Stream' α) : get s n ∈ s :=
  Exists.intro n rfl

theorem mem_def (a : α) (s : Stream' α) : (a ∈ s) = Any (a = ·) s :=
  rfl

theorem mem_of_get_eq {n : ℕ} {s : Stream' α} {a : α} : a = get s n → a ∈ s := fun h =>
  Exists.intro n h
#align stream.mem_of_nth_eq Stream'.mem_of_get_eq

/-- Apply a function `f` to all elements of a stream `s`. -/
noncomputable def map (f : α → β) (s : Stream' α) : Stream' β where
  get n := f (get s n)
#align stream.map Stream'.map

section Map

variable (f : α → β)

@[simp]
theorem head_map (s : Stream' α) : head (map f s) = f (head s) :=
  rfl
#align stream.head_map Stream'.head_map

@[simp]
theorem tail_map (s : Stream' α) : tail (map f s) = map f (tail s) :=
  rfl
#align stream.tail_map Stream'.tail_map

@[simp]
theorem get_map (n : ℕ) (s : Stream' α) : get (map f s) n = f (get s n) :=
  rfl
#align stream.nth_map Stream'.get_map

@[simp]
theorem drop_map (n : ℕ) (s : Stream' α) : drop n (map f s) = map f (drop n s) := by
  ext; simp
#align stream.drop_map Stream'.drop_map

theorem map_eq (s : Stream' α) : map f s = f (head s) ::ₛ map f (tail s) := by
  apply dest_eq_cons
  simp
#align stream.map_eq Stream'.map_eq

@[simp]
theorem map_cons (a : α) (s : Stream' α) : map f (a ::ₛ s) = f a ::ₛ map f s := by
  apply dest_eq_cons
  simp
#align stream.map_cons Stream'.map_cons

@[simp]
theorem map_id (s : Stream' α) : map id s = s :=
  rfl
#align stream.map_id Stream'.map_id

@[simp]
theorem map_map (g : β → δ) (f : α → β) (s : Stream' α) : map g (map f s) = map (g ∘ f) s :=
  rfl
#align stream.map_map Stream'.map_map

theorem map_tail (s : Stream' α) : map f (tail s) = tail (map f s) :=
  rfl
#align stream.map_tail Stream'.map_tail

theorem map_injective {f : α → β} (hf : Injective f) : Injective (map f) := by
  intro s₁ s₂ hs
  ext1 n
  replace hs := congr_arg (fun s => get s n) hs
  simp only [get_map] at hs
  exact hf hs

theorem mem_map_of_mem {a : α} {s : Stream' α} : a ∈ s → f a ∈ map f s := fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])
#align stream.mem_map Stream'.mem_map_of_mem

theorem exists_of_mem_map {b : β} {f} {s : Stream' α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩
#align stream.exists_of_mem_map Stream'.exists_of_mem_map

theorem map_congr {f g : α → β} {s : Stream' α} : (∀ a ∈ s, f a = g a) → map f s = map g s :=
  fun h => Stream'.ext fun n => h (get s n) (mem_get n s)

theorem mem_map {b : β} {f} {s : Stream' α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b := by
  constructor
  · exact exists_of_mem_map
  · rintro ⟨a, _, rfl⟩
    apply mem_map_of_mem
    assumption

end Map

/-- Iterates of a function as a stream. -/
noncomputable def iterate (f : α → α) (a : α) : Stream' α where
  get n := f^[n] a
#align stream.iterate Stream'.iterate

section Iterate

@[simp]
theorem get_iterate (f : α → α) (a : α) (n : ℕ) : get (iterate f a) n = f^[n] a :=
  rfl

@[simp]
theorem head_iterate (f : α → α) (a : α) : head (iterate f a) = a :=
  rfl
#align stream.head_iterate Stream'.head_iterate

@[simp]
theorem tail_iterate (f : α → α) (a : α) : tail (iterate f a) = iterate f (f a) :=
  rfl
#align stream.tail_iterate Stream'.tail_iterate

theorem iterate_eq (f : α → α) (a : α) : iterate f a = a ::ₛ iterate f (f a) := by
  apply dest_eq_cons
  simp
#align stream.iterate_eq Stream'.iterate_eq

theorem get_zero_iterate (f : α → α) (a : α) : get (iterate f a) 0 = a :=
  rfl
#align stream.nth_zero_iterate Stream'.get_zero_iterate

theorem get_succ_iterate (f : α → α) (a : α) (n : ℕ) :
    get (iterate f a) (n + 1) = get (iterate f (f a)) n :=
  rfl
#align stream.nth_succ_iterate Stream'.get_succ_iterate

theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = map f (iterate f a) := by
  ext n
  simp [← iterate_succ_apply']
#align stream.map_iterate Stream'.map_iterate

end Iterate

/-- Corecursor for the stream. -/
noncomputable def corec (f : α → β) (g : α → α) (a : α) : Stream' β :=
  map f (iterate g a)
#align stream.corec Stream'.corec

section Corec

theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
  rfl
#align stream.corec_def Stream'.corec_def

@[simp]
theorem get_corec (f : α → β) (g : α → α) (a : α) (n : ℕ) : get (corec f g a) n = f (g^[n] a) := by
  simp [corec_def]

@[simp]
theorem head_corec (f : α → β) (g : α → α) (a : α) : head (corec f g a) = f a :=
  rfl

@[simp]
theorem tail_corec (f : α → β) (g : α → α) (a : α) : tail (corec f g a) = corec f g (g a) :=
  rfl

theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a ::ₛ corec f g (g a) := by
  apply dest_eq_cons
  simp
#align stream.corec_eq Stream'.corec_eq
#align stream.unfolds_eq Stream'.corec_eq

@[simp]
theorem corec_id_f (f : α → α) (a : α) : corec id f a = iterate f a :=
  rfl
#align stream.corec_id_f_eq_iterate Stream'.corec_id_f

theorem corec_head_tail (s : Stream' α) : corec head tail s = s := by
  refine eq_of_bisim (fun s₁ s₂ => s₁ = corec head tail s₂) ?_ rfl; clear s
  rintro _ s rfl
  simp
#align stream.unfolds_head_eq Stream'.corec_head_tail

end Corec

@[inherit_doc corec, inline]
unsafe def corec'Unsafe (f : α → β × α) (a : α) : Stream' β :=
  unsafeCast (corec' f a)

@[inherit_doc corec'Unsafe, implemented_by corec'Unsafe]
def corec' (f : α → β × α) : α → Stream' β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)
#align stream.corec' Stream'.corec'

section Corec'

@[simp]
theorem head_corec' (f : α → β × α) (a : α) : head (corec' f a) = (f a).1 :=
  rfl

@[simp]
theorem tail_corec' (f : α → β × α) (a : α) : tail (corec' f a) = corec' f (f a).2 :=
  rfl

theorem corec'_eq (f : α → β × α) (a : α) : corec' f a = (f a).1 ::ₛ corec' f (f a).2 :=
  corec_eq _ _ _
#align stream.corec'_eq Stream'.corec'_eq

theorem corec'_dest (s : Stream' α) : corec' dest s = s :=
  corec_head_tail s

end Corec'

@[inherit_doc corec, inline]
def corecComputable (f : α → β) (g : α → α) : α → Stream' β :=
  corec' (fun a => (f a, g a))

@[csimp]
theorem corec_eq_corecComputable : @corec.{u, v} = @corecComputable.{u, v} :=
  rfl

@[inherit_doc map, inline]
def mapComputable (f : α → β) : Stream' α → Stream' β :=
  corec (f ∘ head) tail

@[csimp]
theorem map_eq_mapComputable : @map.{u, v} = @mapComputable.{u, v} := by
  funext α β f s
  conv_lhs => rw [← corec_head_tail s]
  rfl

@[inherit_doc iterate, inline]
def iterateComputable (f : α → α) : α → Stream' α :=
  corec id f

@[csimp]
theorem iterate_eq_iterateComputable : @iterate.{u} = @iterateComputable.{u} :=
  rfl

@[inherit_doc mk, inline, simp]
def mkComputable (f : ℕ → α) : Stream' α :=
  corec f succ 0

@[csimp]
theorem mk_eq_mkComputable : @mk.{u} = @mkComputable.{u} := by
  funext α f
  ext n
  simp [Nat.succ_iterate]

/-- The stream of natural numbers from `n` :
- `head (iota n) = n`
- `tail (iota n) = iota (n + 1)` -/
def iota : ℕ → Stream' ℕ :=
  iterate Nat.succ

/-- The stream of natural numbers. -/
def nats : Stream' ℕ :=
  iota 0
#align stream.nats Stream'.nats

section Iota

@[simp]
theorem head_iota (n : ℕ) : head (iota n) = n :=
  head_iterate _ _

@[simp]
theorem head_nats : head nats = 0 :=
  head_iota 0

@[simp]
theorem tail_iota (n : ℕ) : tail (iota n) = iota (n + 1) :=
  tail_iterate _ _

@[simp]
theorem tail_nats : tail nats = iota 1 :=
  tail_iota 0

@[simp]
theorem get_iota (m n : ℕ) : get (iota m) n = m + n := by
  simp [iota, Nat.succ_iterate]

@[simp]
theorem get_nats (n : ℕ) : get nats n = n := by
  simp [nats]
#align stream.nth_nats Stream'.get_nats

theorem iota_eq (n : ℕ) : iota n = n ::ₛ iota (n + 1) := by
  apply dest_eq_cons
  simp

theorem nats_eq : nats = 0 ::ₛ iota 1 :=
  iota_eq 0
#align stream.nats_eq Stream'.nats_eq

end Iota

/-- Zip two streams using a binary operation:
- `get (zipWith f s₁ s₂) n = f (get s₁ n) (get s₂ n)` -/
def zipWith (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ where
  get n := f (get s₁ n) (get s₂ n)
#align stream.zip Stream'.zipWith

section ZipWith

variable (f : α → β → δ)

@[simp]
theorem get_zipWith (s₁ : Stream' α) (s₂ : Stream' β) (n : ℕ) :
    get (zipWith f s₁ s₂) n = f (get s₁ n) (get s₂ n) :=
  rfl
#align stream.nth_zip Stream'.get_zipWith

@[simp]
theorem drop_zipWith (n : ℕ) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zipWith f s₁ s₂) = zipWith f (drop n s₁) (drop n s₂) := by
  ext m
  simp
#align stream.drop_zip Stream'.drop_zipWith

@[simp]
theorem head_zipWith (s₁ : Stream' α) (s₂ : Stream' β) :
    head (zipWith f s₁ s₂) = f (head s₁) (head s₂) :=
  rfl
#align stream.head_zip Stream'.head_zipWith

@[simp]
theorem tail_zipWith (s₁ : Stream' α) (s₂ : Stream' β) :
    tail (zipWith f s₁ s₂) = zipWith f (tail s₁) (tail s₂) :=
  rfl
#align stream.tail_zip Stream'.tail_zipWith

theorem zipWith_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zipWith f s₁ s₂ = f (head s₁) (head s₂) ::ₛ zipWith f (tail s₁) (tail s₂) := by
  apply dest_eq_cons
  simp
#align stream.zip_eq Stream'.zipWith_eq

@[simp]
theorem zipWith_cons (a : α) (s₁ : Stream' α) (b : β) (s₂ : Stream' β) :
    zipWith f (a ::ₛ s₁) (b ::ₛ s₂) = f a b ::ₛ zipWith f s₁ s₂ := by
  apply dest_eq_cons
  simp

end ZipWith

@[inherit_doc zipWith, inline, simp]
def zipWithComputable (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ :=
  corec (fun (s₁, s₂) => f (head s₁) (head s₂)) (fun (s₁, s₂) => (tail s₁, tail s₂)) (s₁, s₂)

@[csimp]
theorem zipWith_eq_zipWithComputable : @zipWith.{u, v, w} = @zipWithComputable.{u, v, w} := by
  funext α β δ f s₁ s₂
  refine eq_of_bisim
    (fun t₁ t₂ => ∃ s₁ s₂, t₁ = zipWith f s₁ s₂ ∧ t₂ = zipWithComputable f s₁ s₂)
    ?_ ⟨s₁, s₂, rfl, rfl⟩; clear s₁ s₂
  rintro _ _ ⟨s₁, s₂, rfl, rfl⟩
  constructor
  · simp
  · use tail s₁, tail s₂
    simp

/-- Zip two streams:
- `get (zip s₁ s₂) n = (get s₁ n, get s₂ n)` -/
def zip : Stream' α → Stream' β → Stream' (α × β) :=
  zipWith Prod.mk

/-- Like `enum` but it allows you to specify the initial index. -/
def enumFrom (n : ℕ) (s : Stream' α) : Stream' (ℕ × α) :=
  zip (iota n) s

/-- Enumerate a stream by tagging each element with its index. -/
def enum (s : Stream' α) : Stream' (ℕ × α) :=
  enumFrom 0 s
#align stream.enum Stream'.enum

section Zip

@[simp]
theorem get_zip (s₁ : Stream' α) (s₂ : Stream' β) (n : ℕ) :
    get (zip s₁ s₂) n = (get s₁ n, get s₂ n) :=
  get_zipWith Prod.mk s₁ s₂ n

@[simp]
theorem drop_zip (n : ℕ) (s₁ : Stream' α) (s₂ : Stream' β) :
    drop n (zip s₁ s₂) = zip (drop n s₁) (drop n s₂) :=
  drop_zipWith Prod.mk n s₁ s₂

@[simp]
theorem head_zip (s₁ : Stream' α) (s₂ : Stream' β) : head (zip s₁ s₂) = (head s₁, head s₂) :=
  head_zipWith Prod.mk s₁ s₂

@[simp]
theorem tail_zip (s₁ : Stream' α) (s₂ : Stream' β) : tail (zip s₁ s₂) = zip (tail s₁) (tail s₂) :=
  tail_zipWith Prod.mk s₁ s₂

theorem zip_eq (s₁ : Stream' α) (s₂ : Stream' β) :
    zip s₁ s₂ = (head s₁, head s₂) ::ₛ zip (tail s₁) (tail s₂) :=
  zipWith_eq Prod.mk s₁ s₂

@[simp]
theorem zip_cons (a : α) (s₁ : Stream' α) (b : β) (s₂ : Stream' β) :
    zip (a ::ₛ s₁) (b ::ₛ s₂) = (a, b) ::ₛ zip s₁ s₂ :=
  zipWith_cons Prod.mk a s₁ b s₂

theorem enum_eq_zip (s : Stream' α) : enum s = zip nats s :=
  rfl
#align stream.enum_eq_zip Stream'.enum_eq_zip

@[simp]
theorem head_enumFrom (n : ℕ) (s : Stream' α) : head (enumFrom n s) = (n, head s) :=
  head_zip (iota n) s

@[simp]
theorem head_enum (s : Stream' α) : head (enum s) = (0, head s) :=
  head_enumFrom 0 s

@[simp]
theorem tail_enumFrom (n : ℕ) (s : Stream' α) : tail (enumFrom n s) = enumFrom (n + 1) (tail s) :=
  tail_zip (iota n) s

@[simp]
theorem tail_enum (s : Stream' α) : tail (enum s) = enumFrom 1 (tail s) :=
  tail_enumFrom 0 s

@[simp]
theorem get_enumFrom (m : ℕ) (s : Stream' α) (n : ℕ) :
    get (enumFrom m s) n = (m + n, s.get n) := by
  simp [enumFrom]

@[simp]
theorem get_enum (s : Stream' α) (n : ℕ) : get (enum s) n = (n, s.get n) := by
  simp [enum]
#align stream.nth_enum Stream'.get_enum

end Zip

/-- The constant stream: `get (const a) n = a`. -/
def const (a : α) : Stream' α where
  get _ := a
#align stream.const Stream'.const

section Const

@[simp]
theorem head_const (a : α) : head (const a) = a :=
  rfl

@[simp]
theorem tail_const (a : α) : tail (const a) = const a :=
  rfl
#align stream.tail_const Stream'.tail_const

theorem const_eq (a : α) : const a = a ::ₛ const a := by
  apply dest_eq_cons
  simp
#align stream.const_eq Stream'.const_eq

@[simp]
theorem map_const (f : α → β) (a : α) : map f (const a) = const (f a) :=
  rfl
#align stream.map_const Stream'.map_const

@[simp]
theorem map_funConst (a : α) (s : Stream' β) : map (Function.const β a) s = const a :=
  rfl

@[simp]
theorem get_const (n : ℕ) (a : α) : get (const a) n = a :=
  rfl
#align stream.nth_const Stream'.get_const

theorem mem_const_self (a : α) : a ∈ const a :=
  Exists.intro 0 rfl
#align stream.mem_const Stream'.mem_const_self

theorem eq_of_mem_const {a b : α} (h : a ∈ const b) : b = a := by
  rcases h with ⟨_, rfl⟩
  rfl

@[simp]
theorem mem_const {a b : α} : a ∈ const b ↔ b = a := by
  constructor
  · exact eq_of_mem_const
  · rintro rfl
    apply mem_const_self

@[simp]
theorem drop_const (n : ℕ) (a : α) : drop n (const a) = const a := by
  ext; simp
#align stream.drop_const Stream'.drop_const

@[simp]
theorem iterate_id (a : α) : iterate id a = const a := by
  ext; simp
#align stream.iterate_id Stream'.iterate_id

theorem corec_id_id_eq_const (a : α) : corec id id a = const a := by
  simp
#align stream.corec_id_id_eq_const Stream'.corec_id_id_eq_const

@[simp]
theorem zipWith_const_left (f : α → β → δ) (a : α) (s₂ : Stream' β) :
    zipWith f (const a) s₂ = map (f a) s₂ := by
  ext1; simp

@[simp]
theorem zipWith_const_right (f : α → β → δ) (s₁ : Stream' α) (b : β) :
    zipWith f s₁ (const b) = map (f · b) s₁ := by
  ext1; simp

theorem zipWith_const (f : α → β → δ) (a : α) (b : β) :
    zipWith f (const a) (const b) = const (f a b) := by
  simp

@[simp]
theorem zip_const_left (a : α) (s₂ : Stream' β) :
    zip (const a) s₂ = map (Prod.mk a) s₂ := by
  ext1; simp

@[simp]
theorem zip_const_right (s₁ : Stream' α) (b : β) :
    zip s₁ (const b) = map ((·, b)) s₁ := by
  ext1; simp

theorem zip_const (a : α) (b : β) :
    zip  (const a) (const b) = const (a, b) := by
  simp

end Const

@[inherit_doc const, simp]
def constComputable (a : α) : Stream' α :=
  corec (Function.const Unit a) id ()

@[csimp]
theorem const_eq_constComputable : @const.{u} = @constComputable.{u} := by
  funext α a
  ext n
  simp

instance [Inhabited α] : Inhabited (Stream' α) :=
  ⟨Stream'.const default⟩

instance : Functor Stream' where
  map f s := map f s
  mapConst a _ := const a

instance : LawfulFunctor Stream' where
  map_const {_ _} := funext₂ fun a s => Eq.symm (map_funConst a s)
  id_map s := map_id s
  comp_map f g s := Eq.symm (map_map g f s)

@[simp]
theorem map_eq_map {α β : Type u} (f : α → β) : Functor.map f = map f :=
  rfl

@[simp]
theorem mapConst_eq_const {α β : Type u} (a : α) (s : Stream' β) : Functor.mapConst a s = const a :=
  rfl

@[inherit_doc corec]
abbrev corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a
#align stream.corec_on Stream'.corecOn

-- Porting note: this `#align` should be elsewhere but idk where
#align state StateM

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)
#align stream.corec_state Stream'.corecState

#align stream.unfolds Stream'.corec

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corec (fun (s₁, _) => head s₁) (fun (s₁, s₂) => (s₂, tail s₁)) (s₁, s₂)
#align stream.interleave Stream'.interleave

@[inherit_doc interleave]
infixl:65 " ⋈ " => interleave

@[simp]
theorem head_interleave (s₁ s₂ : Stream' α) : head (s₁ ⋈ s₂) = head s₁ := by
  simp [interleave]

@[simp]
theorem tail_interleave (s₁ s₂ : Stream' α) : tail (s₁ ⋈ s₂) = s₂ ⋈ tail s₁ := by
  simp [interleave]
#align stream.tail_interleave Stream'.tail_interleave

theorem interleave_eq (s₁ s₂ : Stream' α) :
    s₁ ⋈ s₂ = head s₁ ::ₛ head s₂ ::ₛ (tail s₁ ⋈ tail s₂) := by
  apply dest_eq_cons
  simp
  apply dest_eq_cons
  simp
#align stream.interleave_eq Stream'.interleave_eq

theorem tail_tail_interleave (s₁ s₂ : Stream' α) : tail (tail (s₁ ⋈ s₂)) = tail s₁ ⋈ tail s₂ := by
  simp
#align stream.interleave_tail_tail Stream'.tail_tail_interleave

theorem get_interleave_left (n : ℕ) (s₁ s₂ : Stream' α) : get (s₁ ⋈ s₂) (2 * n) = get s₁ n := by
  induction n generalizing s₁ s₂ with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, Nat.mul_add, hn]
#align stream.nth_interleave_left Stream'.get_interleave_left

theorem get_interleave_right (n : ℕ) (s₁ s₂ : Stream' α) :
    get (s₁ ⋈ s₂) (2 * n + 1) = get s₂ n := by
  simp [get_succ, get_interleave_left]
#align stream.nth_interleave_right Stream'.get_interleave_right

theorem mem_interleave_left {a : α} {s₁ : Stream' α} (s₂ : Stream' α) : a ∈ s₁ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n) (by rw [h, get_interleave_left])
#align stream.mem_interleave_left Stream'.mem_interleave_left

theorem mem_interleave_right {a : α} (s₁ : Stream' α) {s₂ : Stream' α} : a ∈ s₂ → a ∈ s₁ ⋈ s₂ :=
  fun ⟨n, h⟩ => Exists.intro (2 * n + 1) (by rw [h, get_interleave_right])
#align stream.mem_interleave_right Stream'.mem_interleave_right

@[simp]
theorem mem_interleave {a : α} {s₁ : Stream' α} {s₂ : Stream' α} :
    a ∈ s₁ ⋈ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ := by
  constructor
  · rintro ⟨n, rfl⟩
    rcases n.even_or_odd' with ⟨k, rfl | rfl⟩ <;> simp [get_interleave_left, get_interleave_right]
  · rintro (h | h)
    · exact mem_interleave_left s₂ h
    · exact mem_interleave_right s₁ h

/-- Elements of a stream with even indices. -/
def even (s : Stream' α) : Stream' α :=
  corec (fun s => head s) (fun s => tail (tail s)) s
#align stream.even Stream'.even

/-- Elements of a stream with odd indices. -/
def odd (s : Stream' α) : Stream' α :=
  even (tail s)
#align stream.odd Stream'.odd

theorem odd_eq (s : Stream' α) : odd s = even (tail s) :=
  rfl
#align stream.odd_eq Stream'.odd_eq

theorem even_tail (s : Stream' α) : even (tail s) = odd s :=
  rfl
#align stream.even_tail Stream'.even_tail

@[simp]
theorem head_even (s : Stream' α) : head (even s) = head s :=
  rfl
#align stream.head_even Stream'.head_even

@[simp]
theorem tail_even (s : Stream' α) : tail (even s) = even (tail (tail s)) := by
  simp [even]
#align stream.tail_even Stream'.tail_even

theorem even_cons_cons (a₁ a₂ : α) (s : Stream' α) : even (a₁ ::ₛ a₂ ::ₛ s) = a₁ ::ₛ even s := by
  apply dest_eq_cons
  simp
#align stream.even_cons_cons Stream'.even_cons_cons

@[simp]
theorem even_interleave (s₁ s₂ : Stream' α) : even (s₁ ⋈ s₂) = s₁ := by
  refine eq_of_bisim (fun s₁' s₁ => ∃ s₂, s₁' = even (s₁ ⋈ s₂))
    ?_ ⟨s₂, rfl⟩; clear s₁ s₂
  rintro _ s₂ ⟨s₁, rfl⟩
  constructor
  · simp
  · use tail s₁
    simp
#align stream.even_interleave Stream'.even_interleave

@[simp]
theorem interleave_even_odd (s : Stream' α) : even s ⋈ odd s = s := by
  refine eq_of_bisim (fun s₁ s₂ => s₁ = even s₂ ⋈ odd s₂)
    ?_ rfl; clear s
  rintro _ s rfl
  simp [odd_eq]
#align stream.interleave_even_odd Stream'.interleave_even_odd

@[simp]
theorem get_even (n : ℕ) (s : Stream' α) : get (even s) n = get s (2 * n) := by
  induction n generalizing s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, Nat.mul_add, hn]
#align stream.nth_even Stream'.get_even

theorem get_odd (n : ℕ) (s : Stream' α) : get (odd s) n = get s (2 * n + 1) := by
  simp [get_succ, odd_eq]
#align stream.nth_odd Stream'.get_odd

theorem mem_of_mem_even (a : α) (s : Stream' α) : a ∈ even s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n) (by rw [h, get_even])
#align stream.mem_of_mem_even Stream'.mem_of_mem_even

theorem mem_of_mem_odd (a : α) (s : Stream' α) : a ∈ odd s → a ∈ s := fun ⟨n, h⟩ =>
  Exists.intro (2 * n + 1) (by rw [h, get_odd])
#align stream.mem_of_mem_odd Stream'.mem_of_mem_odd

/-- Append a stream to a list. -/
def hAppend : List α → Stream' α → Stream' α
  | []    , s => s
  | a :: l, s => a ::ₛ hAppend l s
#align stream.append_stream Stream'.hAppend

instance : HAppend (List α) (Stream' α) (Stream' α) where
  hAppend := hAppend

@[simp]
theorem nil_append (s : Stream' α) : ([] : List α) ++ s = s :=
  rfl
#align stream.nil_append_stream Stream'.nil_append

@[simp]
theorem cons_append (a : α) (l : List α) (s : Stream' α) :
    a :: l ++ s = a ::ₛ (l ++ s) :=
  rfl
#align stream.cons_append_stream Stream'.cons_append

@[simp]
theorem append_append (l₁ l₂ : List α) (s : Stream' α) : l₁ ++ l₂ ++ s = l₁ ++ (l₂ ++ s) := by
  induction l₁ with
  | nil => simp
  | cons a l₁ hl₁ => simp [hl₁]
#align stream.append_append_stream Stream'.append_append

@[simp]
theorem map_append (f : α → β) (l : List α) (s : Stream' α) :
    map f (l ++ s) = List.map f l ++ map f s := by
  induction l with
  | nil => simp
  | cons a l hl => simp [hl]
#align stream.map_append_stream Stream'.map_append

theorem drop_append' (l : List α) (s : Stream' α) : drop (length l) (l ++ s) = s := by
  induction l with
  | nil => simp
  | cons _ l hl => simp [hl]
#align stream.drop_append_stream Stream'.drop_append'

@[simp]
theorem drop_append : ∀ {n : ℕ} {l : List α} (s : Stream' α), n = length l → drop n (l ++ s) = s
  | _, l, s, rfl => drop_append' l s

theorem append_head_tail (s : Stream' α) : [head s] ++ tail s = s := by
  simp [Stream'.eta]
#align stream.append_stream_head_tail Stream'.append_head_tail

theorem mem_append_right {a : α} (l : List α) {s : Stream' α} (h : a ∈ s) : a ∈ l ++ s := by
  induction l with
  | nil => simp [h]
  | cons b l hl => simp [hl]
#align stream.mem_append_stream_right Stream'.mem_append_right

theorem mem_append_left {a : α} {l : List α} (s : Stream' α) (h : a ∈ l) : a ∈ l ++ s := by
  induction l with
  | nil => simp at h
  | cons b l hl =>
    simp at h ⊢
    exact Or.imp_right hl h
#align stream.mem_append_stream_left Stream'.mem_append_left

@[simp]
theorem mem_append {a : α} {l : List α} {s : Stream' α} : a ∈ l ++ s ↔ a ∈ l ∨ a ∈ s := by
  constructor
  · intro h
    induction l with
    | nil          => right; simpa using h
    | cons b l' ih =>
      simp at h
      rcases h with rfl | h
      · left; exact List.mem_cons_self a l'
      · rcases ih h with ih' | ih'
        · left; exact List.mem_cons_of_mem b ih'
        · right; exact ih'
  · rintro (h | h)
    exact mem_append_left s h
    exact mem_append_right l h

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream' α → List α
  | 0    , _ => []
  | n + 1, s => head s :: take n (tail s)
#align stream.take Stream'.take

@[simp]
theorem take_zero (s : Stream' α) : take 0 s = [] :=
  rfl
#align stream.take_zero Stream'.take_zero

-- The priority of this lemma is lower than `dropLast_take` lemma below.
@[simp default-100]
theorem take_succ (n : ℕ) (s : Stream' α) : take (n + 1) s = head s :: take n (tail s) :=
  rfl
#align stream.take_succ Stream'.take_succ

/-- Tail recursive version of `take`. -/
@[inline, simp]
def takeTR (n : ℕ) (s : Stream' α) : List α :=
  go s n (Array.mkEmpty n)
where
  /-- Auxiliary for `takeTR`: `takeTR.go s n acc = Array.data acc ++ take n s`. -/
  @[specialize, simp]
  go (s : Stream' α) (n : ℕ) (acc : Array α) : List α :=
    match n with
    | 0     => Array.data acc
    | n + 1 => go (tail s) n (Array.push acc (head s))

@[csimp] theorem take_eq_takeTR : @take = @takeTR := by
  funext α n s
  suffices ∀ acc, takeTR.go s n acc = acc.data ++ take n s from
    (this #[]).symm
  intro acc
  induction n generalizing s acc with
  | zero => simp
  | succ n hn => simp [hn]

theorem take_append' (l : List α) (s : Stream' α) : take (length l) (l ++ s) = l := by
  induction l with
  | nil => simp
  | cons a l hl => simp [hl]

@[simp]
theorem take_append : ∀ {n : ℕ} {l : List α} (s : Stream' α), n = length l → take n (l ++ s) = l
  | _, l, s, rfl => take_append' l s

theorem take_succ_cons (n : ℕ) (a : α) (s : Stream' α) :
    take (n + 1) (a ::ₛ s) = a :: take n s :=
  rfl

@[simp]
theorem concat_take_get (n : ℕ) (s : Stream' α) : take n s ++ [get s n] = take (n + 1) s := by
  induction n generalizing s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, hn]

theorem take_succ' (n : ℕ) (s : Stream' α) : take (n + 1) s = take n s ++ [get s n] :=
  Eq.symm (concat_take_get n s)

@[simp]
theorem length_take (n : ℕ) (s : Stream' α) : length (take n s) = n := by
  induction n generalizing s with
  | zero => simp
  | succ n hn => simp [hn]
#align stream.length_take Stream'.length_take

@[simp]
theorem take_take : ∀ (m n) (s : Stream' α), List.take m (take n s) = take (min n m) s
  | 0    , n    , s => by simp
  | m    , 0    , s => by simp
  | m + 1, n + 1, s => by simp [Nat.succ_min_succ, take_take m n (tail s)]

theorem get?_take (s : Stream' α) : ∀ {k n}, k < n → get? (take n s) k = get s k
  | 0    , n + 1, _ => rfl
  | k + 1, n + 1, h => by
    rw [take_succ, List.get?, get?_take (tail s) (Nat.lt_of_succ_lt_succ h), get_succ]

theorem get?_take_succ (n : ℕ) (s : Stream' α) :
    List.get? (take (n + 1) s) n = some (get s n) :=
  get?_take s (Nat.lt_succ_self n)
#align stream.nth_take_succ Stream'.get?_take_succ

@[simp]
theorem get_take (s : Stream' α) {k n} (h : k < length (take n s)) :
    List.get (take n s) ⟨k, h⟩ = get s k :=
  Option.some.inj <| by rw [← List.get?_eq_get, get?_take s (length_take n s ▸ h)]

@[simp]
theorem take_const (n : ℕ) (a : α) : take n (const a) = replicate n a := by
  refine List.ext_get ?_ fun m hm₁ hm₂ => ?_ <;> simp

@[simp]
theorem dropLast_take (n : ℕ) (xs : Stream' α) :
    dropLast (take n xs) = take (n - 1) xs := by
  cases n with
  | zero => simp
  | succ n => simp [take_succ', - concat_take_get]

@[simp]
theorem append_take_drop (n : ℕ) (s : Stream' α) : take n s ++ drop n s = s := by
  induction n generalizing s with
  | zero => simp
  | succ n hn => simp [hn, Stream'.eta]
#align stream.append_take_drop Stream'.append_take_drop

@[simp]
theorem take_map (n : ℕ) (f : α → β) (s : Stream' α) :
    take n (map f s) = List.map f (take n s) := by
  conv_lhs => rw [← append_take_drop n s]
  simp [- append_take_drop]

-- Take theorem reduces a proof of equality of infinite streams to an
-- induction over all their finite approximations.
theorem take_theorem (s₁ s₂ : Stream' α) (h : ∀ n : ℕ, take n s₁ = take n s₂) : s₁ = s₂ := by
  ext n
  replace h := congr_arg (fun l => List.get? l n) (h (n + 1))
  simpa [get?_take_succ, - take_succ] using h
#align stream.take_theorem Stream'.take_theorem

@[simp]
theorem take_nats (n : ℕ) : take n nats = List.range n := by
  refine List.ext_get ?_ fun m hm₁ hm₂ => ?_ <;> simp

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v
#align stream.cycle_f Stream'.cycleF

@[simp]
protected theorem cycleF_nil (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleF (a₁, l₁, a₀, l₀) = a₁ :=
  rfl

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleG : α × List α × α × List α → α × List α × α × List α
  | (_, []      , v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, v₂ :: l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)
#align stream.cycle_g Stream'.cycleG

/-- Interpret a nonempty list as a cyclic stream. -/
def cycle : ∀ l : List α, l ≠ [] → Stream' α
  | []    , h => absurd rfl h
  | a :: l, _ => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)
#align stream.cycle Stream'.cycle

@[simp]
protected theorem cycleG_nil (a : α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleG (a, [], a₀, l₀) = (a₀, l₀, a₀, l₀) :=
  rfl

@[simp]
protected theorem cycleG_cons (a : α) (a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
    Stream'.cycleG (a, a₁ :: l₁, a₀, l₀) = (a₁, l₁, a₀, l₀) :=
  rfl
#align stream.cycle_g_cons Stream'.cycleG_cons

theorem cycle_eq : ∀ (l : List α) (h : l ≠ []), cycle l h = l ++ cycle l h
  | [], h => absurd rfl h
  | a :: l, _ =>
    have gen : ∀ a' l', corec Stream'.cycleF Stream'.cycleG (a', l', a, l) =
        a' :: l' ++ corec Stream'.cycleF Stream'.cycleG (a, l, a, l) := by
      intro a' l'
      induction l' generalizing a' with
      | nil =>
        simp
        apply dest_eq_cons
        simp
      | cons a' l' hl' =>
        simp
        apply dest_eq_cons
        simp
        apply dest_eq_cons
        simp [hl']
    gen a l
#align stream.cycle_eq Stream'.cycle_eq

theorem mem_cycle {a : α} {l : List α} : ∀ h : l ≠ [], a ∈ l → a ∈ cycle l h := fun h ainl => by
  rw [cycle_eq]; exact mem_append_left _ ainl
#align stream.mem_cycle Stream'.mem_cycle

@[simp]
theorem cycle_singleton (a : α) {h : [a] ≠ []} : cycle [a] h = const a :=
  coinduction rfl fun β fr ch => by rwa [cycle_eq, const_eq]
#align stream.cycle_singleton Stream'.cycle_singleton

/-- Tails of a stream, starting with `s`. -/
def tails (s : Stream' α) : Stream' (Stream' α) :=
  iterate tail s
#align stream.tails Stream'.tails

theorem tails_eq_iterate (s : Stream' α) : tails s = iterate tail s :=
  rfl
#align stream.tails_eq_iterate Stream'.tails_eq_iterate

@[simp]
theorem head_tails (s : Stream' α) : head (tails s) = s :=
  head_iterate tail s

@[simp]
theorem tail_tails (s : Stream' α) : tail (tails s) = tails (tail s) :=
  tail_iterate tail s

theorem tails_eq (s : Stream' α) : tails s = s ::ₛ tails (tail s) := by
  apply dest_eq_cons
  simp
#align stream.tails_eq Stream'.tails_eq

@[simp]
theorem get_tails (n : ℕ) (s : Stream' α) : get (tails s) n = drop n s := by
  induction n generalizing s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, hn]
#align stream.nth_tails Stream'.get_tails

/-- An auxiliary definition for `inits`. -/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corec (fun (a, _) => a) (fun (l', s') => (l' ++ [head s'], tail s')) (l, s)
#align stream.inits_core Stream'.initsCore

/-- Initial segments of a stream. -/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [] s
#align stream.inits Stream'.inits

@[simp]
theorem head_initsCore (l : List α) (s : Stream' α) : head (initsCore l s) = l := by
  simp [initsCore]

@[simp]
theorem tail_initsCore (l : List α) (s : Stream' α) :
    tail (initsCore l s) = initsCore (l ++ [head s]) (tail s) := by
  simp [initsCore]

theorem initsCore_eq (l : List α) (s : Stream' α) :
    initsCore l s = l ::ₛ initsCore (l ++ [head s]) (tail s) := by
  apply dest_eq_cons
  simp
#align stream.inits_core_eq Stream'.initsCore_eq

#noalign stream.tail_inits

#noalign stream.inits_tail

@[simp]
theorem cons_get_initsCore (a : α) (n : ℕ) (l : List α) (s : Stream' α) :
    get (initsCore (a :: l) s) n = a :: get (initsCore l s) n := by
  induction n generalizing l s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, hn]
#align stream.cons_nth_inits_core Stream'.cons_get_initsCore

@[simp]
theorem get_inits (n : ℕ) (s : Stream' α) : get (inits s) n = take n s := by
  unfold inits
  induction n generalizing s with
  | zero => simp [get_zero]
  | succ n hn => simp [get_succ, hn]
#align stream.nth_inits Stream'.get_inits

theorem inits_eq (s : Stream' α) :
    inits s = [] ::ₛ map (head s :: ·) (inits (tail s)) := by
  apply dest_eq_cons
  simp [inits]
  ext1 n
  simp
#align stream.inits_eq Stream'.inits_eq

theorem zipWith_append_inits_tails (s : Stream' α) :
    zipWith (· ++ ·) (inits s) (tails s) = const s := by
  ext1 n
  simp
#align stream.zip_inits_tails Stream'.zipWith_append_inits_tails

#align stream.pure Stream'.const

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Stream' (α → β)) (s : Stream' α) : Stream' β :=
  zipWith id f s
#align stream.apply Stream'.apply

@[inherit_doc apply]
infixl:75 " ⊛ " => apply
-- Porting note: "input as \o*" was here but doesn't work for the above notation

@[simp]
theorem identity (s : Stream' α) : const id ⊛ s = s :=
  rfl
#align stream.identity Stream'.identity

@[simp]
theorem composition (g : Stream' (β → δ)) (f : Stream' (α → β)) (s : Stream' α) :
    map comp g ⊛ f ⊛ s = g ⊛ (f ⊛ s) :=
  rfl
#align stream.composition Stream'.composition

@[simp]
theorem homomorphism (f : α → β) (a : α) : const f ⊛ const a = const (f a) :=
  rfl
#align stream.homomorphism Stream'.homomorphism

@[simp default-100]
theorem interchange (fs : Stream' (α → β)) (a : α) :
    fs ⊛ const a = const (eval a) ⊛ fs :=
  rfl
#align stream.interchange Stream'.interchange

theorem const_apply (f : α → β) (s : Stream' α) : const f ⊛ s = map f s :=
  rfl
#align stream.map_eq_apply Stream'.const_apply

/-- Corecursor where it is possible to return a fully formed value at any point of the
computation. -/
@[inline]
unsafe def corec''Unsafe (f : β → Stream' α ⊕ α × β) (b : β) : Stream' α :=
  unsafeCast (corec'' (unsafeCast f) b : Stream'Impl α)

@[inherit_doc corec''Unsafe, implemented_by corec''Unsafe]
def corec'' (f : β → Stream' α ⊕ α × β) (b : β) : Stream' α :=
  corec'
    (Sum.elim (Prod.map id Sum.inl ∘ dest) (Prod.map id Sum.inr) ∘
      Sum.elim Sum.inl f)
    (Sum.inr b)

theorem dest_corec'' (f : β → Stream' α ⊕ α × β) (b : β) :
    dest (corec'' f b) = Sum.elim dest (Prod.map id (corec'' f)) (f b) := by
  unfold corec''; simp
  rcases f b with (s' | ⟨a, b⟩) <;> simp
  refine eq_of_bisim
    (fun s₁ s₂ =>
      s₁ = corec'
        (Sum.elim (Prod.map id Sum.inl ∘ dest) (Prod.map id Sum.inr) ∘
          Sum.elim Sum.inl f)
        (Sum.inl s₂))
    ?_ rfl; clear s'
  rintro _ s rfl
  simp

@[simp]
theorem head_corec'' (f : β → Stream' α ⊕ α × β) (b : β) :
    head (corec'' f b) = Sum.elim head Prod.fst (f b) := by
  simpa [← comp_apply (f := Prod.fst), Sum.comp_elim, Prod.map_fst', - comp_apply]
    using congr_arg Prod.fst (dest_corec'' f b)

@[simp]
theorem tail_corec'' (f : β → Stream' α ⊕ α × β) (b : β) :
    tail (corec'' f b) = Sum.elim tail (corec'' f ∘ Prod.snd) (f b) := by
  simpa [← comp_apply (f := Prod.snd), Sum.comp_elim, Prod.map_snd', - comp_apply]
    using congr_arg Prod.snd (dest_corec'' f b)

end Stream'
