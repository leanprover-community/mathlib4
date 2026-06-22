/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.PNat.Notation

/-!
# Instances for `ℕ+`-indexed powers on semigroups

Declared in a separate file to bootstrap the algebra hierarchy without
requiring instances on `ℕ+`, which are usually inferred via inheriting from `ℕ`.
-/

public section

variable {M : Type*}

instance Semigroup.instPow [Semigroup M] : Pow M ℕ+ where
  pow x n := Semigroup.ppow n n.property x

instance AddSemigroup.instSMul [AddSemigroup M] : SMul ℕ+ M where
  smul n x := AddSemigroup.psmul n n.property x

attribute [to_additive existing AddSemigroup.instSMul] Semigroup.instPow

@[to_additive (attr := simp)]
lemma ppow_one [Semigroup M] (x : M) : x ^ (1 : ℕ+) = x :=
  Semigroup.ppow_one _
