
/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Tactic.Module

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List Mathlib.Tactic.Module

namespace Mathlib.Tactic.Algebra

-- /-- This definition is copied from Mathlib.Tactic.Module.NF --
--   perhaps we should just reuse that code. -/
-- def NF (R : Type*) (M : Type*) := List (R × M)

variable {u v : Level}

def ExProd (A : Q(Type v)) :=
  List (Q($A) × ℕ)

-- def ExProd.le {A : Q(Type v)} : ExProd A → ExProd A → Prop
-- | a :: l, [] =>
  -- sorry

-- instance {A : Q(Type v)} : LE (ExProd A) where
--   le := ExProd.le

abbrev qNF (R : Q(Type u)) (A : Q(Type v)) :=
  List ((Q($R) × ExProd A))

namespace qNF

end qNF


end Mathlib.Tactic.Algebra
