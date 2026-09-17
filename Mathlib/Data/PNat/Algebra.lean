/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.PNat.Notation

/-!
# Algebraic lemmas for positive natural numbers
-/

@[expose] public section

deriving instance Mul, Distrib, AddLeftCancelSemigroup, AddRightCancelSemigroup,
  AddCommSemigroup, CommMonoid for PNat

namespace PNat

open Nat

@[simp, norm_cast]
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl

/-- `PNat.coe` promoted to a `MonoidHom`. -/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := Coe.coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]
theorem coe_coeMonoidHom : (coeMonoidHom : ℕ+ → ℕ) = (↑) :=
  rfl

@[simp, norm_cast]
theorem pow_coe (m : ℕ+) (n : ℕ) : ↑(m ^ n) = (m : ℕ) ^ n :=
  rfl

end PNat
