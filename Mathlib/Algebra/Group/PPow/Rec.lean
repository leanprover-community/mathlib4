/-
Copyright (c) 2026 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Data.PNat.Notation
public import Mathlib.Tactic.ToAdditive

/-!
# Exponentiation by `ℕ+` via repeated self-multiplication

Implementation detail to help defined `ℕ+`-indexed powers on semigroups.
-/

@[expose] public section

universe u

open PNat

variable {M : Type u}

/-- The fundamental power operation in a semigroup. `ppowRec n a = a*a*...*a` n times.
Use instead `a ^ n`,  which has better definitional behavior. -/
def ppowRec [Mul M] (n : ℕ+) (x : M) : M :=
  PNat.recOn n x (fun _ y => y * x)

/-- The fundamental scalar multipication in an additive semigroup. `psmulRec n a = a+a+...+a` n
times.  Use instead `a ^ n`,  which has better definitional behavior. -/
def psmulRec [Add M] (n : ℕ+) (x : M) : M :=
  PNat.recOn n x (fun _ y => y + x)

attribute [to_additive existing] ppowRec

variable [Mul M]

@[to_additive (attr := simp)]
lemma ppowRec_one (x : M) : ppowRec 1 x = x := PNat.recOn_one _ _

@[to_additive]
lemma ppowRec_succ (n : ℕ+) (x : M) : ppowRec (n + 1) x = ppowRec n x * x :=
  PNat.recOn_succ _ _ _

-- helper lemma before Semigroup is defined
lemma ppowRec_succ'_of_assoc (n : ℕ+) (x : M) (h : ∀ x y z : M, (x * y) * z = x * (y * z)) :
    ppowRec (n + 1) x = x * ppowRec n x := by
  induction n with
  | one => rfl
  | succ n IH => rw [ppowRec_succ n, ppowRec_succ, IH, h]
