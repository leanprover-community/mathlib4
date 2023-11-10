/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Nat.SuccPred
import Mathlib.Init.Data.List.Basic
import Mathlib.Data.List.Basic

#align_import data.stream.defs from "leanprover-community/mathlib"@"39af7d3bf61a98e928812dbc3e16f4ea8b795ca3"

/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is a lazy infinite list with elements of `α` where all elements after the first
are computed on-demand. (This is logically sound because `Stream' α` is dealed as `ℕ → α` in the
kernel.) In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.

## Main definitions

Given a type `α` and a function `f : ℕ → α`:

* `Stream' α` : the type of streams whose elements have type `α`
-/

set_option autoImplicit true

open Nat Function Option

/-- A stream `Stream' α` is an infinite sequence of elements of `α`.
This type has special support in the runtime. -/
@[opaque_repr]
structure Stream' (α : Type u) where
  /-- Convert a `ℕ → α` into an `Stream' α`. Consider using other functions like `corec` before
  use this. -/
  mk ::
  /-- Get the `n`-th element of a stream, or convert an `Stream' α` into a `ℕ → α`. -/
  get : ℕ → α
#align stream Stream'
#align stream.nth Stream'.get

namespace Stream'

variable {α : Type u} {β : Type v} {δ : Type w}

/-- This function will cast a value of type `Stream' α` to type `α × Thunk (Stream' α)`, and is a
no-op in the compiler. -/
@[inline]
unsafe def destCast : Stream' α → α × Thunk (Stream' α) :=
  unsafeCast

/-- This function will cast a value of type `α × Thunk (Stream' α)` to type `Stream' α`, and is a
no-op in the compiler. -/
@[inline]
unsafe def consCast : α × Thunk (Stream' α) → Stream' α :=
  unsafeCast

@[ext]
protected theorem ext {s₁ s₂ : Stream' α} (h : ∀ n, get s₁ n = get s₂ n) : s₁ = s₂ :=
  congr_arg mk (funext h)
#align stream.ext Stream'.ext

/-- Prepend an element to a stream. -/
@[inline]
unsafe def consUnsafe (a : α) (s : Stream' α) : Stream' α :=
  consCast (a, Thunk.pure s)

@[inherit_doc consUnsafe, implemented_by consUnsafe]
def cons (a : α) (s : Stream' α) : Stream' α where
  get
  | 0 => a
  | n + 1 => get s n
#align stream.cons Stream'.cons

@[inherit_doc cons]
infixr:67 " ::ₛ " => cons

theorem get_zero_cons (a : α) (s : Stream' α) : get (a ::ₛ s) 0 = a :=
  rfl
#align stream.nth_zero_cons Stream'.get_zero_cons

/-- Head of a stream: `Stream'.head (h ::ₛ t) := h`. -/
@[inline]
unsafe def headUnsafe (s : Stream' α) : α :=
  (destCast s).1

@[inherit_doc headUnsafe, implemented_by headUnsafe]
def head (s : Stream' α) : α :=
  get s 0
#align stream.head Stream'.head

@[simp]
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
@[inline]
unsafe def tailUnsafe (s : Stream' α) : Stream' α :=
  Thunk.get (destCast s).2

@[inherit_doc tailUnsafe, implemented_by tailUnsafe]
def tail (s : Stream' α) : Stream' α where
  get i := get s (i + 1)
#align stream.tail Stream'.tail

protected theorem eta (s : Stream' α) : head s ::ₛ tail s = s := by
  ext (_ | n) <;> rfl
#align stream.eta Stream'.eta

@[simp]
theorem get_succ (s : Stream' α) (n : ℕ) : get s (n + 1) = get (tail s) n :=
  rfl
#align stream.nth_succ Stream'.get_succ

theorem get_succ_cons (n : ℕ) (s : Stream' α) (x : α) : get (x ::ₛ s) (n + 1) = get s n :=
  rfl
#align stream.nth_succ_cons Stream'.get_succ_cons

@[simp]
theorem tail_cons (a : α) (s : Stream' α) : tail (a ::ₛ s) = s :=
  rfl
#align stream.tail_cons Stream'.tail_cons

theorem cons_injective2 : Function.Injective2 (cons : α → Stream' α → Stream' α) := by
  intro a₁ a₂ s₁ s₂ h
  constructor
  · simpa using congr_arg head h
  · simpa using congr_arg tail h
#align stream.cons_injective2 Stream'.cons_injective2

theorem cons_eq_cons {a₁ a₂ : α} {s₁ s₂ : Stream' α} : a₁ ::ₛ s₁ = a₂ ::ₛ s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  cons_injective2.eq_iff

@[simp]
theorem eq_cons_iff {s : Stream' α} {a s'} : s = a ::ₛ s' ↔ head s = a ∧ tail s = s' := by
  rw [← Stream'.eta s, cons_eq_cons]
  simp

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
  | zero => simp
  | succ n hn => simp [← hn]

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
  | zero => simp
  | succ n hn => simp [hn]
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
  induction n using Nat.recAux generalizing s with
  | zero => simp
  | succ n hn => simp [hn, ← Nat.add_assoc]
#align stream.nth_drop Stream'.get_drop

@[simp]
theorem drop_drop (n m : ℕ) (s : Stream' α) : drop m (drop n s) = drop (n + m) s := by
  ext; simp [Nat.add_assoc]
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
  | _, _, 0, h => bisim h
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
      constructor; exact h₁; rw [← h₂, ← h₃]
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
  cases n using Nat.casesAuxOn with
  | zero =>
    left
    exact h
  | succ n' =>
    right
    rw [get_succ, tail_cons] at h
    exact ⟨n', h⟩
#align stream.eq_or_mem_of_mem_cons Stream'.eq_or_mem_of_mem_cons

@[simp]
theorem mem_cons : a ∈ b ::ₛ s ↔ a = b ∨ a ∈ s := by
  constructor
  · exact eq_or_mem_of_mem_cons
  · rintro (rfl | _)
    · apply mem_cons_self
    · apply mem_cons_of_mem
      assumption

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
  simp
#align stream.map_eq Stream'.map_eq

@[simp]
theorem map_cons (a : α) (s : Stream' α) : map f (a ::ₛ s) = f a ::ₛ map f s := by
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

theorem mem_map_of_mem {a : α} {s : Stream' α} : a ∈ s → f a ∈ map f s := fun ⟨n, h⟩ =>
  Exists.intro n (by rw [get_map, h])
#align stream.mem_map Stream'.mem_map_of_mem

theorem exists_of_mem_map {b : β} {f} {s : Stream' α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
  fun ⟨n, h⟩ => ⟨get s n, ⟨n, rfl⟩, h.symm⟩
#align stream.exists_of_mem_map Stream'.exists_of_mem_map

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
#align lazy_list.iterates Stream'.iterate

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

@[inherit_doc corec, specialize]
unsafe def corec'Unsafe (f : α → β × α) (a : α) : Stream' β :=
  match f a with
  | (b, a) => consCast (b, Thunk.mk fun _ => corec'Unsafe f a)

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
- `Stream'.head (Stream'.iota n) = n`
- `Stream'.tail (Stream'.iota n) = Stream'.iota (n + 1)` -/
def iota : ℕ → Stream' ℕ :=
  iterate Nat.succ
#align lazy_list.iota Stream'.iota

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
  simp

theorem nats_eq : nats = 0 ::ₛ iota 1 :=
  iota_eq 0
#align stream.nats_eq Stream'.nats_eq

end Iota

/-- Zip two streams using a binary operation:
- `Stream'.head (Stream'.zipWith f s₁ s₂) = f (Stream'.head s₁) (Stream'.head s₂)`
- `Stream'.tail (Stream'.zipWith f s₁ s₂) =
   Stream'.zipWith f (Stream'.tail s₁) (Stream'.tail s₂)` -/
noncomputable def zipWith (f : α → β → δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ where
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
  simp
#align stream.zip_eq Stream'.zipWith_eq

@[simp]
theorem zipWith_cons (a : α) (s₁ : Stream' α) (b : β) (s₂ : Stream' β) :
    zipWith f (a ::ₛ s₁) (b ::ₛ s₂) = f a b ::ₛ zipWith f s₁ s₂ := by
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
- `Stream'.head (Stream'.zip s₁ s₂) = (Stream'.head s₁, Stream'.head s₂)`
- `Stream'.tail (Stream'.zip s₁ s₂) = Stream'.zip (Stream'.tail s₁) (Stream'.tail s₂)` -/
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
theorem tail_enumFrom (n : ℕ) (s : Stream' α) : tail (enumFrom n s) = enumFrom (n + 1) (tail s) :=
  tail_zip (iota n) s

@[simp]
theorem get_enumFrom (m : ℕ) (s : Stream' α) (n : ℕ) :
    get (enumFrom m s) n = (m + n, s.get n) := by
  simp [enumFrom]

@[simp]
theorem get_enum (s : Stream' α) (n : ℕ) : get (enum s) n = (n, s.get n) := by
  simp [enum]
#align stream.nth_enum Stream'.get_enum

end Zip

/-- The constant stream: `Stream'.get n (Stream'.const a) = a`. -/
def const (a : α) : Stream' α where
  get _ := a
#align stream.const Stream'.const

instance [Inhabited α] : Inhabited (Stream' α) :=
  ⟨Stream'.const default⟩

instance : Functor Stream' where
  map f s := map f s
  mapConst a _ := const a

instance : Pure Stream' where
  pure a := const a

@[simp]
theorem map_eq_map {α β : Type u} (f : α → β) : Functor.map f = map f :=
  rfl

@[simp]
theorem mapConst_eq_const {α β : Type u} (a : α) (s : Stream' β) : Functor.mapConst a s = const a :=
  rfl

abbrev corecOn (a : α) (f : α → β) (g : α → α) : Stream' β :=
  corec f g a
#align stream.corec_on Stream'.corecOn

-- porting note: this `#align` should be elsewhere but idk where
#align state StateM

/-- Use a state monad to generate a stream through corecursion -/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)
#align stream.corec_state Stream'.corecState

#align stream.unfolds Stream'.corec

/-- Interleave two streams. -/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corecOn (s₁, s₂) (fun (s₁, _) => head s₁) (fun (s₁, s₂) => (s₂, tail s₁))
#align stream.interleave Stream'.interleave

infixl:65 " ⋈ " => interleave

/-- Elements of a stream with even indices. -/
def even (s : Stream' α) : Stream' α :=
  corec (fun s => head s) (fun s => tail (tail s)) s
#align stream.even Stream'.even

/-- Elements of a stream with odd indices. -/
def odd (s : Stream' α) : Stream' α :=
  even (tail s)
#align stream.odd Stream'.odd

/-- Append a stream to a list. -/
def appendList : List α → Stream' α → Stream' α
  | []    , s => s
  | a :: l, s => a ::ₛ appendList l s
#align stream.append_stream Stream'.appendList

instance : HAppend (List α) (Stream' α) (Stream' α) where
  hAppend := appendList

/-- `take n s` returns a list of the `n` first elements of stream `s` -/
def take : ℕ → Stream' α → List α
  | 0    , _ => []
  | n + 1, s => head s :: take n (tail s)
#align stream.take Stream'.take

/-- An auxiliary definition for `Stream'.cycle` corecursive def -/
protected def cycleF : α × List α × α × List α → α
  | (v, _, _, _) => v
#align stream.cycle_f Stream'.cycleF

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

/-- Tails of a stream, starting with `Stream'.tail s`. -/
def tails (s : Stream' α) : Stream' (Stream' α) :=
  corec id tail (tail s)
#align stream.tails Stream'.tails

/-- An auxiliary definition for `Stream'.inits`. -/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corecOn (l, s) (fun (a, _) => a) (fun (l', s') => (l' ++ [head s'], tail s'))
#align stream.inits_core Stream'.initsCore

/-- Nonempty initial segments of a stream. -/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [head s] (tail s)
#align stream.inits Stream'.inits

#align stream.pure Stream'.const

@[simp]
theorem pure_eq_const {a : α} : (Pure.pure a : Stream' α) = const a :=
  rfl

/-- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value. -/
def apply (f : Stream' (α → β)) (s : Stream' α) : Stream' β where
  get n := get f n (get s n)
#align stream.apply Stream'.apply

infixl:75 " ⊛ " => apply
-- PORTING NOTE: "input as \o*" was here but doesn't work for the above notation

end Stream'
