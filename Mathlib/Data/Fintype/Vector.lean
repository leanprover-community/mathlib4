/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.vector
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Sym.Basic

/-!
# `Vector α n` and `Sym α n` are fintypes when `α` is.
-/

variable {α : Type _}

instance Vector.fintype [Fintype α] {n : ℕ} : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align vector.fintype Vector.fintype

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) := by
  refine @Quotient.fintype _ _ _ ?_
  -- Porting note: had to build the instance manually
  intros x y
  apply List.decidablePerm

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm
