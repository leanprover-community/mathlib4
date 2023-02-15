/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro

! This file was ported from Lean 3 source module init.data.array.basic
! leanprover-community/lean commit 7cb84a2a93c1e2d37b3ad5017fc5372973dbb9fb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/

import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.Bool.Basic
import Mathlib.Init.Data.Bool.Lemmas
import Mathlib.Init.IteSimp
import Init.Data.Format.Basic

universe u v w

/-- In the VM, d_array is implemented as a persistent array. -/
structure DArray (n : Nat) (α : Fin n → Type u) where
  data : ∀ i : Fin n, α i
#align d_array DArray

namespace DArray

variable {n : Nat} {α : Fin n → Type u} {α' : Fin n → Type v} {β : Type w}

/-- The empty array. -/
def nil {α} : DArray 0 α where data := fun ⟨x, h⟩ => absurd h (Nat.not_lt_zero x)
#align d_array.nil DArray.nil

/-- `read a i` reads the `i`th member of `a`. Has builtin VM implementation. -/
def read (a : DArray n α) (i : Fin n) : α i :=
  a.data i
#align d_array.read DArray.read

/-- `write a i v` sets the `i`th member of `a` to be `v`. Has builtin VM implementation. -/
def write (a : DArray n α) (i : Fin n) (v : α i) : DArray n α
    where data j := if h : i = j then Eq.recOn h v else a.read j
#align d_array.write DArray.write

def iterateAux (a : DArray n α) (f : ∀ i : Fin n, α i → β → β) : ∀ i : Nat, i ≤ n → β → β
  | 0, _, b => b
  | j + 1, h, b =>
    let i : Fin n := ⟨j, h⟩
    f i (a.read i) (iterateAux a f j (le_of_lt h) b)
#align d_array.iterate_aux DArray.iterateAux

/-- Fold over the elements of the given array in ascending order. Has builtin VM implementation. -/
def iterate (a : DArray n α) (b : β) (f : ∀ i : Fin n, α i → β → β) : β :=
  iterateAux a f n (le_refl _) b
#align d_array.iterate DArray.iterate

/-- Map the array. Has builtin VM implementation. -/
def foreach (a : DArray n α) (f : ∀ i : Fin n, α i → α' i) : DArray n α' :=
  ⟨fun i => f _ (a.read i)⟩
#align d_array.foreach DArray.foreach

def map (f : ∀ i : Fin n, α i → α' i) (a : DArray n α) : DArray n α' :=
  foreach a f
#align d_array.map DArray.map

def map₂ {α'' : Fin n → Type w} (f : ∀ i : Fin n, α i → α' i → α'' i) (a : DArray n α)
    (b : DArray n α') : DArray n α'' :=
  foreach b fun i => f i (a.read i)
#align d_array.map₂ DArray.map₂

def foldl (a : DArray n α) (b : β) (f : ∀ i : Fin n, α i → β → β) : β :=
  iterate a b f
#align d_array.foldl DArray.foldl

def revIterateAux (a : DArray n α) (f : ∀ i : Fin n, α i → β → β) : ∀ i : Nat, i ≤ n → β → β
  | 0, _, b => b
  | j + 1, h, b =>
    let i : Fin n := ⟨j, h⟩
    revIterateAux a f j (le_of_lt h) (f i (a.read i) b)
#align d_array.rev_iterate_aux DArray.revIterateAux

def revIterate (a : DArray n α) (b : β) (f : ∀ i : Fin n, α i → β → β) : β :=
  revIterateAux a f n (le_refl _) b
#align d_array.rev_iterate DArray.revIterate

@[simp]
theorem read_write (a : DArray n α) (i : Fin n) (v : α i) : read (write a i v) i = v := by
  simp [read, write]
#align d_array.read_write DArray.read_write

@[simp]
theorem read_write_of_ne (a : DArray n α) {i j : Fin n} (v : α i) :
    i ≠ j → read (write a i v) j = read a j := by
    intro h
    simp [read, write, h]
#align d_array.read_write_of_ne DArray.read_write_of_ne

protected theorem ext {a b : DArray n α} (h : ∀ i, read a i = read b i) : a = b := by
  cases a
  cases b
  congr
  exact funext h
#align d_array.ext DArray.ext

protected theorem ext' {a b : DArray n α}
    (h : ∀ (i : Nat) (h : i < n), read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b := by
    cases a
    cases b
    congr ; funext i; cases i; apply h
#align d_array.ext' DArray.ext'

protected def beqAux [∀ i, DecidableEq (α i)] (a b : DArray n α) : ∀ i : Nat, i ≤ n → Bool
  | 0, _ => true
  | i + 1, h => if a.read ⟨i, h⟩ = b.read ⟨i, h⟩ then DArray.beqAux a b i (le_of_lt h) else false
#align d_array.beq_aux DArray.beqAux

/-- Boolean element-wise equality check. -/
protected def beq [∀ i, DecidableEq (α i)] (a b : DArray n α) : Bool :=
  DArray.beqAux a b n (le_refl _)
#align d_array.beq DArray.beq

theorem of_beqAux_eq_true [∀ i, DecidableEq (α i)] {a b : DArray n α} :
    ∀ (i : Nat) (h : i ≤ n),
      DArray.beqAux a b i h = true →
        ∀ (j : Nat) (h' : j < i), a.read ⟨j, lt_of_lt_of_le h' h⟩ = b.read ⟨j, lt_of_lt_of_le h' h⟩
  | 0, h₁, _, j, h₃ => absurd h₃ (Nat.not_lt_zero _)
  | i + 1, h₁, h₂, j, h₃ =>
    by
    have h₂' : read a ⟨i, h₁⟩ = read b ⟨i, h₁⟩ ∧ DArray.beqAux a b i _ = true :=
      by
      simp [DArray.beqAux] at h₂
      assumption
    have h₁' : i ≤ n := le_of_lt h₁
    have ih :
      ∀ (j : Nat) (h' : j < i),
        a.read ⟨j, lt_of_lt_of_le h' h₁'⟩ = b.read ⟨j, lt_of_lt_of_le h' h₁'⟩ :=
      of_beqAux_eq_true i h₁' h₂'.2
    by_cases hji : j = i
    · subst hji
      exact h₂'.1
    · have j_lt_i : j < i := lt_of_le_of_ne (Nat.le_of_lt_succ h₃) hji
      exact ih j j_lt_i
#align d_array.of_beq_aux_eq_tt DArray.of_beqAux_eq_true

theorem of_beq_eq_true [∀ i, DecidableEq (α i)] {a b : DArray n α} :
    DArray.beq a b = true → a = b := by
  unfold DArray.beq
  intro h
  have : ∀ (j : Nat) (h : j < n), a.read ⟨j, h⟩ = b.read ⟨j, h⟩ := of_beqAux_eq_true n (le_refl _) h
  apply DArray.ext' this
#align d_array.of_beq_eq_tt DArray.of_beq_eq_true

theorem of_beqAux_eq_false [∀ i, DecidableEq (α i)] {a b : DArray n α} :
    ∀ (i : Nat) (h : i ≤ n),
      DArray.beqAux a b i h = false →
        ∃ (j : Nat)(h' : j < i), a.read ⟨j, lt_of_lt_of_le h' h⟩ ≠ b.read ⟨j, lt_of_lt_of_le h' h⟩
  | 0, h₁, h₂ => by simp [DArray.beqAux] at h₂
  | i + 1, h₁, h₂ =>
    by
    have h₂' : read a ⟨i, h₁⟩ ≠ read b ⟨i, h₁⟩ ∨ DArray.beqAux a b i _ = false :=
      by
      simp [DArray.beqAux] at h₂
      assumption
    cases' h₂' with h h
    · exists i
      exists Nat.lt_succ_self _
    · have h₁' : i ≤ n := le_of_lt h₁
      have ih :
        ∃ (j : Nat)(h' : j < i),
          a.read ⟨j, lt_of_lt_of_le h' h₁'⟩ ≠ b.read ⟨j, lt_of_lt_of_le h' h₁'⟩ :=
        of_beqAux_eq_false i h₁' h
      cases' ih with j ih
      cases' ih with h' ih
      exists j
      exists Nat.lt_succ_of_lt h'
#align d_array.of_beq_aux_eq_ff DArray.of_beqAux_eq_false

theorem of_beq_eq_false [∀ i, DecidableEq (α i)] {a b : DArray n α} :
    DArray.beq a b = false → a ≠ b := by
  unfold DArray.beq
  intro h hne
  have : ∃ (j : Nat)(h' : j < n), a.read ⟨j, h'⟩ ≠ b.read ⟨j, h'⟩ :=
    of_beqAux_eq_false n (le_refl _) h
  cases' this with j this'
  cases' this' with h' this''
  subst hne
  contradiction
#align d_array.of_beq_eq_ff DArray.of_beq_eq_false

instance [∀ i, DecidableEq (α i)] : DecidableEq (DArray n α) := fun a b =>
  if h : DArray.beq a b = true then isTrue (of_beq_eq_true h)
  else isFalse (of_beq_eq_false (Bool.eq_false_of_not_eq_true h))

end DArray

/-- A non-dependent array (see `d_array`). Implemented in the VM as a persistent array.  -/
def Array' (n : Nat) (α : Type u) : Type u :=
  DArray n fun _ => α
#align array Array'

/--
`mk_array n v` creates a new array of length `n` where each element is `v`. Has builtin VM implementation. -/
def mkArray' {α} (n) (v : α) : Array' n α where data _ := v
#align mk_array mkArray'

namespace Array'

variable {n : Nat} {α : Type u} {β : Type v}

def nil {α} : Array' 0 α :=
  DArray.nil
#align array.nil Array'.nil

@[inline]
def read (a : Array' n α) (i : Fin n) : α :=
  DArray.read a i
#align array.read Array'.read

@[inline]
def write (a : Array' n α) (i : Fin n) (v : α) : Array' n α :=
  DArray.write a i v
#align array.write Array'.write

/-- Fold array starting from 0, folder function includes an index argument. -/
@[inline]
def iterate (a : Array' n α) (b : β) (f : Fin n → α → β → β) : β :=
  DArray.iterate a b f
#align array.iterate Array'.iterate

/-- Map each element of the given array with an index argument. -/
@[inline]
def foreach (a : Array' n α) (f : Fin n → α → β) : Array' n β :=
  DArray.foreach a f
#align array.foreach Array'.foreach

@[inline]
def map₂ (f : α → α → α) (a b : Array' n α) : Array' n α :=
  foreach b fun i => f (a.read i)
#align array.map₂ Array'.map₂

@[inline]
def foldl (a : Array' n α) (b : β) (f : α → β → β) : β :=
  iterate a b fun _ => f
#align array.foldl Array'.foldl

def revList (a : Array' n α) : List α :=
  a.foldl [] (· :: ·)
#align array.rev_list Array'.revList

def revIterate (a : Array' n α) (b : β) (f : Fin n → α → β → β) : β :=
  DArray.revIterate a b f
#align array.rev_iterate Array'.revIterate

def revFoldl (a : Array' n α) (b : β) (f : α → β → β) : β :=
  revIterate a b fun _ => f
#align array.rev_foldl Array'.revFoldl

def toList (a : Array' n α) : List α :=
  a.revFoldl [] (· :: ·)
#align array.to_list Array'.toList

theorem push_back_idx {j n} (h₁ : j < n + 1) (h₂ : j ≠ n) : j < n :=
  Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h₁) h₂
#align array.push_back_idx Array'.push_back_idx

/-- `push_back a v` pushes value `v` to the end of the array. Has builtin VM implementation. -/
def pushBack (a : Array' n α) (v : α) : Array' (n + 1) α
    where data := fun ⟨j, h₁⟩ => if h₂ : j = n then v else a.read ⟨j, push_back_idx h₁ h₂⟩
#align array.push_back Array'.pushBack

theorem pop_back_idx {j n} (h : j < n) : j < n + 1 :=
  Nat.lt.step h
#align array.pop_back_idx Array'.pop_back_idx

/-- Discard _last_ element in the array. Has builtin VM implementation. -/
def popBack (a : Array' (n + 1) α) : Array' n α
    where data := fun ⟨j, h⟩ => a.read ⟨j, pop_back_idx h⟩
#align array.pop_back Array'.popBack

/-- Auxilliary function for monadically mapping a function over an array. -/
@[inline]
def mmapCore {β : Type v} {m : Type v → Type w} [Monad m] (a : Array' n α) (f : α → m β) :
    ∀ i ≤ n, m (Array' i β)
  | 0, _ => pure DArray.nil
  | i + 1, h => do
    let bs ← mmapCore a f i (le_of_lt h)
    let b ← f (a.read ⟨i, h⟩)
    pure $ pushBack bs b
#align array.mmap_core Array'.mmapCore

/-- Monadically map a function over the array. -/
@[inline]
def mmap {β : Type v} {m} [Monad m] (a : Array' n α) (f : α → m β) : m (Array' n β) :=
  a.mmapCore f _ (le_refl _)
#align array.mmap Array'.mmap

/-- Map a function over the array. -/
@[inline]
def map {β : Type v} (a : Array' n α) (f : α → β) : Array' n β :=
  DArray.foreach a (λ _ e => f e)
#align array.map Array'.map

protected def Mem (v : α) (a : Array' n α) : Prop :=
  ∃ i : Fin n, read a i = v
#align array.mem Array'.Mem

instance : Membership α (Array' n α) :=
  ⟨Array'.Mem⟩

theorem read_mem (a : Array' n α) (i) : read a i ∈ a :=
  Exists.intro i rfl
#align array.read_mem Array'.read_mem

instance [Repr α] : Repr (Array' n α) where
  reprPrec (a : Array' n α) (_ : Nat) := repr (toList a)

unsafe instance [Std.ToFormat α] : Std.ToFormat (Array' n α) where
  format (a : Array' n α) := Std.format (toList a)

/- Porting note: This is related to tactics-/
/--unsafe instance [has_to_tactic_format α] : has_to_tactic_format (Array' n α) :=
  ⟨tactic.pp ∘ toList⟩
--/
@[simp]
theorem read_write (a : Array' n α) (i : Fin n) (v : α) : read (write a i v) i = v :=
  DArray.read_write a i v
#align array.read_write Array'.read_write

@[simp]
theorem read_write_of_ne (a : Array' n α) {i j : Fin n} (v : α) :
    i ≠ j → read (write a i v) j = read a j :=
  DArray.read_write_of_ne a v
#align array.read_write_of_ne Array'.read_write_of_ne

def read' [Inhabited β] (a : Array' n β) (i : Nat) : β :=
  if h : i < n then a.read ⟨i, h⟩ else default
#align array.read' Array'.read'

def write' (a : Array' n α) (i : Nat) (v : α) : Array' n α :=
  if h : i < n then a.write ⟨i, h⟩ v else a
#align array.write' Array'.write'

theorem read_eq_read' [Inhabited α] (a : Array' n α) {i : Nat} (h : i < n) :
    read a ⟨i, h⟩ = read' a i := by simp [read', h]
#align array.read_eq_read' Array'.read_eq_read'

theorem write_eq_write' (a : Array' n α) {i : Nat} (h : i < n) (v : α) :
    write a ⟨i, h⟩ v = write' a i v := by simp [write', h]
#align array.write_eq_write' Array'.write_eq_write'

protected theorem ext {a b : Array' n α} (h : ∀ i, read a i = read b i) : a = b :=
  DArray.ext h
#align array.ext Array'.ext

protected theorem ext' {a b : Array' n α}
    (h : ∀ (i : Nat) (h : i < n), read a ⟨i, h⟩ = read b ⟨i, h⟩) : a = b :=
  DArray.ext' h
#align array.ext' Array'.ext'

instance [DecidableEq α] : DecidableEq (Array' n α) := by unfold Array'; infer_instance

end Array'
