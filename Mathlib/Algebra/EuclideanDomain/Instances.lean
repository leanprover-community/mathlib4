/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Ring.Lemmas
import Mathlib.Init.Data.Int.Order
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Order.Basic
import Mathlib.Data.Int.Order.Basic

#align_import algebra.euclidean_domain.instances from "leanprover-community/mathlib"@"e1bccd6e40ae78370f01659715d3c948716e3b7e"

/-!
# Instances for Euclidean domains
* `Int.euclideanDomain`: shows that `ℤ` is a Euclidean domain.
* `Field.toEuclideanDomain`: shows that any field is a Euclidean domain.
-/

instance Int.euclideanDomain : EuclideanDomain ℤ :=
  { inferInstanceAs (CommRing Int), inferInstanceAs (Nontrivial Int) with
    add := (· + ·), mul := (· * ·), one := 1, zero := 0,
    neg := Neg.neg,
    quotient := (· / ·), quotient_zero := Int.ediv_zero, remainder := (· % ·),
    quotient_mul_add_remainder_eq := Int.ediv_add_emod,
    r := fun a b => a.natAbs < b.natAbs,
    r_wellFounded := (measure natAbs).wf
    remainder_lt := fun a b b0 => Int.ofNat_lt.1 <| by
      rw [Int.natAbs_of_nonneg (Int.emod_nonneg _ b0), ← Int.abs_eq_natAbs]
      -- ⊢ a % b < |b|
      exact Int.emod_lt _ b0
      -- 🎉 no goals
    mul_left_not_lt := fun a b b0 =>
      not_lt_of_ge <| by
        rw [← mul_one a.natAbs, Int.natAbs_mul]
        -- ⊢ natAbs a * natAbs b ≥ natAbs a * 1
        rw [←Int.natAbs_pos] at b0
        -- ⊢ natAbs a * natAbs b ≥ natAbs a * 1
        exact Nat.mul_le_mul_of_nonneg_left b0 }
        -- 🎉 no goals

-- see Note [lower instance priority]
instance (priority := 100) Field.toEuclideanDomain {K : Type*} [Field K] : EuclideanDomain K :=
{ toCommRing := Field.toCommRing
  quotient := (· / ·), remainder := fun a b => a - a * b / b, quotient_zero := div_zero,
  quotient_mul_add_remainder_eq := fun a b => by
    by_cases h : b = 0 <;> simp [h, mul_div_cancel']
    -- ⊢ b * (fun x x_1 => x / x_1) a b + (fun a b => a - a * b / b) a b = a
                           -- 🎉 no goals
                           -- 🎉 no goals
  r := fun a b => a = 0 ∧ b ≠ 0,
  r_wellFounded :=
    WellFounded.intro fun a =>
      (Acc.intro _) fun b ⟨hb, _⟩ => (Acc.intro _) fun c ⟨_, hnb⟩ => False.elim <| hnb hb,
  remainder_lt := fun a b hnb => by simp [hnb],
                                    -- 🎉 no goals
  mul_left_not_lt := fun a b hnb ⟨hab, hna⟩ => Or.casesOn (mul_eq_zero.1 hab) hna hnb }
#align field.to_euclidean_domain Field.toEuclideanDomain
