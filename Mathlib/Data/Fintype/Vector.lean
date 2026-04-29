/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Sym.Basic

/-!
# `Vector α n` and `Sym α n` are fintypes when `α` is.
-/

public section

open List (Vector)

variable {α : Type*}

namespace List.Vector

instance [Finite α] {n : ℕ} : Finite (List.Vector α n) :=
  Finite.of_equiv _ (Equiv.vectorEquivFin _ _).symm

instance [Fintype α] {n : ℕ} : Fintype (List.Vector α n) :=
  fast_instance% Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm

end List.Vector

namespace Sym.Sym'

instance [Finite α] {n : ℕ} : Finite (Sym.Sym' α n) :=
  inferInstanceAs <| Finite (Quotient _)

instance instFintype [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) :=
  inferInstanceAs <| Fintype (Quotient _)

end Sym.Sym'

namespace Sym

instance [Finite α] {n : ℕ} : Finite (Sym α n) :=
  Finite.of_equiv _ Sym.symEquivSym'.symm

instance instFintype [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  fast_instance% Fintype.ofEquiv _ Sym.symEquivSym'.symm

end Sym
