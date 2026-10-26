/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Cast.Defs

/-!
# Polynomial arithmetic on coefficient lists
-/

@[expose] public section

namespace Mathlib.Tactic.RealRootCount.CoeffList

variable {R : Type*}

/-- Sum of coefficient lists. -/
def add [Add R] [Zero R] (p q : List R) : List R :=
  List.zipWithAll (fun a b => a.getD 0 + b.getD 0) p q

/-- Negation of a coefficient list. -/
def neg [Neg R] (l : List R) : List R := l.map (- ·)

/-- Product of coefficient lists. -/
def mul [Semiring R] : List R → List R → List R
  | [], _ => []
  | c :: p, q => add (q.map (c * ·)) (0 :: mul p q)

/-- Derivative of a coefficient list. -/
def derivative [Semiring R] (l : List R) : List R :=
  (List.range (l.length - 1)).map fun i => ((i + 1 : ℕ) : R) * l.getD (i + 1) 0

/-- Evaluation of a coefficient list, by Horner's rule. -/
def eval [Semiring R] (x : R) (l : List R) : R := l.foldr (fun c acc => c + x * acc) 0

/-- The last entry of a coefficient list: the leading coefficient when it is nonzero. -/
def lead [Zero R] (l : List R) : R := l.getLastD 0

end Mathlib.Tactic.RealRootCount.CoeffList
