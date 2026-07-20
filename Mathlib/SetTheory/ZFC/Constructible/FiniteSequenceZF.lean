/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Ordinals

/-!
# Finite sequences as ZF sets

This file gives a small, structural encoding of finite lists of `ZFSet`s.
The payload is a chain of Kuratowski ordered pairs terminated by the empty
set.  The public sequence code also stores the von Neumann ordinal coding of
the list length.

The construction is deliberately recursive.  In particular, it does not use
an external image and therefore its constructibility proof only needs the
already established closure of `L` under ordered pairs.
-/

@[expose] public section

universe u

namespace Constructible

namespace FiniteSequenceZF

/-- The von Neumann code of a natural number. -/
noncomputable def natCode (n : Nat) : ZFSet.{u} :=
  (n : Ordinal.{u}).toZFSet

/-- Every natural-number code is constructible. -/
theorem natCode_mem_L (n : Nat) : (natCode n : ZFSet.{u}) ∈ L := by
  simpa only [natCode] using
    (ordinal_toZFSet_mem_L (n : Ordinal.{u}))

/-- Natural-number codes are injective. -/
theorem natCode_injective :
    Function.Injective (natCode : Nat → ZFSet.{u}) := by
  intro m n h
  have hOrdinal : (m : Ordinal.{u}) = (n : Ordinal.{u}) :=
    Ordinal.toZFSet_injective h
  exact_mod_cast hOrdinal

@[simp]
theorem natCode_inj {m n : Nat} :
    (natCode m : ZFSet.{u}) = natCode n ↔ m = n :=
  natCode_injective.eq_iff

/--
The structural payload of a finite sequence.  The empty set is the terminator
and a cons cell is the ordered pair of its head and encoded tail.
-/
def listCode : List ZFSet.{u} → ZFSet.{u}
  | [] => ∅
  | x :: xs => ZFSet.pair x (listCode xs)

@[simp]
theorem listCode_nil : listCode ([] : List ZFSet.{u}) = ∅ :=
  rfl

@[simp]
theorem listCode_cons (x : ZFSet.{u}) (xs : List ZFSet.{u}) :
    listCode (x :: xs) = ZFSet.pair x (listCode xs) :=
  rfl

/-- A cons cell cannot be confused with the empty-list terminator. -/
theorem listCode_cons_ne_empty (x : ZFSet.{u}) (xs : List ZFSet.{u}) :
    listCode (x :: xs) ≠ ∅ := by
  intro h
  have hx : ({x} : ZFSet.{u}) ∈ listCode (x :: xs) := by
    simp [listCode, ZFSet.pair]
  rw [h] at hx
  exact ZFSet.notMem_empty _ hx

/-- The structural list encoding is injective. -/
theorem listCode_injective :
    Function.Injective (listCode : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          exact (listCode_cons_ne_empty y ys h.symm).elim
  | cons x xs ih =>
      cases ys with
      | nil =>
          exact (listCode_cons_ne_empty x xs h).elim
      | cons y ys =>
          rcases ZFSet.pair_inj.mp h with ⟨hxy, htail⟩
          subst y
          have hxs : xs = ys := ih htail
          subst ys
          rfl

@[simp]
theorem listCode_inj {xs ys : List ZFSet.{u}} :
    listCode xs = listCode ys ↔ xs = ys :=
  listCode_injective.eq_iff

/-- The code records both the length and the structural list payload. -/
noncomputable def sequenceCode (xs : List ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair (natCode xs.length) (listCode xs)

/-- Equality of sequence codes recovers equality of the original lists. -/
theorem sequenceCode_injective :
    Function.Injective (sequenceCode : List ZFSet.{u} → ZFSet.{u}) := by
  intro xs ys h
  apply listCode_injective
  exact (ZFSet.pair_inj.mp h).2

@[simp]
theorem sequenceCode_inj {xs ys : List ZFSet.{u}} :
    sequenceCode xs = sequenceCode ys ↔ xs = ys :=
  sequenceCode_injective.eq_iff

/-- Structural list codes are constructible when all entries are. -/
theorem listCode_mem_L {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ L) : listCode xs ∈ L := by
  induction xs with
  | nil =>
      exact empty_mem_L
  | cons x xs ih =>
      apply orderedPair_mem_L
      · exact hxs x (by simp)
      · apply ih
        intro y hy
        exact hxs y (by simp [hy])

/-- A finite sequence of constructible entries has a constructible code. -/
theorem sequenceCode_mem_L {xs : List ZFSet.{u}}
    (hxs : ∀ x ∈ xs, x ∈ L) : sequenceCode xs ∈ L := by
  exact orderedPair_mem_L (natCode_mem_L xs.length) (listCode_mem_L hxs)

end FiniteSequenceZF

end Constructible
