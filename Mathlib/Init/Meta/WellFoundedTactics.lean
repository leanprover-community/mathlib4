/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

! This file was ported from Lean 3 source module init.meta.well_founded_tactics
! leanprover-community/lean commit 855e5b74e3a52a40552e8f067169d747d48743fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
prelude
import Mathlib.Init.Data.Nat.Lemmas

-- Porting note: extremely partial port!

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_of_zero_lt_left (a b : Nat) (h : 0 < b) : a < a + b :=
  show a + 0 < a + b by
    apply Nat.add_lt_add_left
    assumption
#align nat.lt_add_of_zero_lt_left Nat.lt_add_of_zero_lt_left

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.zero_lt_one_add (a : Nat) : 0 < 1 + a :=
  suffices 0 < a + 1 by
    simp [Nat.add_comm]
    assumption
  Nat.zero_lt_succ _
#align nat.zero_lt_one_add Nat.zero_lt_one_add

#align nat.lt_add_right Nat.lt_add_right

-- TODO(Leo): move this lemma, or delete it after we add algebraic normalizer.
theorem Nat.lt_add_left (a b c : Nat) : a < b → a < c + b := fun h =>
  lt_of_lt_of_le h (Nat.le_add_left _ _)
#align nat.lt_add_left Nat.lt_add_left

protected def PSum.Alt.sizeof.{u, v} {α : Type u} {β : Type v} [SizeOf α] [SizeOf β] : PSum α β → ℕ
  | PSum.inl a => SizeOf.sizeOf a
  | PSum.inr b => SizeOf.sizeOf b
#align psum.alt.sizeof PSum.Alt.sizeof

@[reducible]
protected def PSum.hasSizeofAlt.{u, v} (α : Type u) (β : Type v) [SizeOf α] [SizeOf β] :
    SizeOf (PSum α β) :=
  ⟨PSum.Alt.sizeof⟩
#align psum.has_sizeof_alt PSum.hasSizeofAlt
