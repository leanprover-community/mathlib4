/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.vector
! leanprover-community/mathlib commit 1126441d6bccf98c81214a0780c73d499f6721fe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Pi
import Mathbin.Data.Sym.Basic

/-!
# `vector α n` and `sym α n` are fintypes when `α` is.
-/


variable {α : Type _}

instance Vector.fintype [Fintype α] {n : ℕ} : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align vector.fintype Vector.fintype

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) :=
  Quotient.fintype _

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm

