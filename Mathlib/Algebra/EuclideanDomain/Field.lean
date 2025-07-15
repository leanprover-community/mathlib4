/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import Mathlib.Algebra.EuclideanDomain.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Instances for Euclidean domains
* `Field.toEuclideanDomain`: shows that any field is a Euclidean domain.
-/

namespace Field

variable {K : Type*} [Field K]

-- see Note [lower instance priority]
instance (priority := 100) toEuclideanDomain : EuclideanDomain K :=
{ toCommRing := toCommRing
  quotient := (· / ·), remainder := fun a b => a - a * b / b, quotient_zero := div_zero,
  quotient_mul_add_remainder_eq := fun a b => by
    by_cases h : b = 0 <;> simp [h, mul_div_cancel₀]
  r := fun a b => a = 0 ∧ b ≠ 0,
  r_wellFounded :=
    WellFounded.intro fun _ =>
      (Acc.intro _) fun _ ⟨hb, _⟩ => (Acc.intro _) fun _ ⟨_, hnb⟩ => False.elim <| hnb hb,
  remainder_lt := fun a b hnb => by simp [hnb],
  mul_left_not_lt := fun _ _ hnb ⟨hab, hna⟩ => Or.casesOn (mul_eq_zero.1 hab) hna hnb }

@[simp]
protected theorem mod_eq (a b : K) : a % b = a - a * b / b := rfl

@[simp]
protected theorem gcd_eq [DecidableEq K] (a b : K) :
    EuclideanDomain.gcd a b = if a = 0 then b else a := by
  unfold EuclideanDomain.gcd
  split_ifs <;> simp [*, Field.mod_eq]

protected theorem gcd_zero_eq [DecidableEq K] (b : K) :
    EuclideanDomain.gcd 0 b = b := by
  rw [Field.gcd_eq, if_pos rfl]

protected theorem gcd_eq_of_ne [DecidableEq K] {a : K} (ha : a ≠ 0) (b : K) :
    EuclideanDomain.gcd a b = a := by
  rw [Field.gcd_eq, if_neg ha]

end Field
