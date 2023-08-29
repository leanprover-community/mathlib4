/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Sym.Basic

#align_import data.fintype.vector from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# `Vector α n` and `Sym α n` are fintypes when `α` is.
-/

variable {α : Type*}

instance Vector.fintype [Fintype α] {n : ℕ} : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align vector.fintype Vector.fintype

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) := by
  refine @Quotient.fintype _ _ _ ?_
  -- ⊢ DecidableRel fun x x_1 => x ≈ x_1
  -- Porting note: had to build the instance manually
  intros x y
  -- ⊢ Decidable ((fun x x_1 => x ≈ x_1) x y)
  apply List.decidablePerm
  -- 🎉 no goals

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm
