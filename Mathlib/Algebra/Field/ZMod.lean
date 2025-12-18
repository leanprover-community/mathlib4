/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# `ZMod p` is a field
-/

@[expose] public section

namespace ZMod
variable (p : ℕ) [hp : Fact p.Prime]

set_option backward.privateInPublic true in
private theorem mul_inv_cancel_aux (a : ZMod p) (h : a ≠ 0) : a * a⁻¹ = 1 := by
  obtain ⟨k, rfl⟩ := natCast_zmod_surjective a
  apply coe_mul_inv_eq_one
  apply Nat.Coprime.symm
  rwa [Nat.Prime.coprime_iff_not_dvd Fact.out, ← CharP.cast_eq_zero_iff (ZMod p)]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Field structure on `ZMod p` if `p` is prime. -/
instance : Field (ZMod p) where
  mul_inv_cancel := mul_inv_cancel_aux p
  inv_zero := inv_zero p
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- `ZMod p` is an integral domain when `p` is prime. -/
instance : IsDomain (ZMod p) := by constructor

end ZMod
