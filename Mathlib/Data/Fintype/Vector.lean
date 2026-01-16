/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Sym.Basic

/-!
# `Vector α n` and `Sym α n` are fintypes when `α` is.
-/

@[expose] public section

open List (Vector)

variable {α : Type*}

instance Vector.fintype [Fintype α] {n : ℕ} : Fintype (List.Vector α n) :=
  Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) :=
  Quotient.fintype _

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm
