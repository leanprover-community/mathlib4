import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.MkIffOfInductiveProp

class IsAddTorsionFree (M : Type*) [AddMonoid M] : Prop where
  eq_zero_of_nsmul_eq_zero (x : M) (n : ℕ) : n • x = 0 → n ≠ 0 → x = 0

@[to_additive, mk_iff]
class IsMulTorsionFree (M : Type*) [Monoid M] : Prop where
  eq_one_of_pow_eq_one (x : M) (n : ℕ) : x ^ n = 1 → n ≠ 0 → x = 1

attribute [to_additive] isMulTorsionFree_iff

@[to_additive]
instance (priority := 100) IsMulTorsionFree.of_subsingleton
    (M : Type*) [Monoid M] [Subsingleton M] : IsMulTorsionFree M where
  eq_one_of_pow_eq_one _ _ _ _ := Subsingleton.elim _ _

variable {M : Type*} [Monoid M] [IsMulTorsionFree M] {x : M} {n : ℕ}

@[to_additive]
theorem eq_one_of_pow_eq_one (hxn : x ^ n = 1) (hn : n ≠ 0) : x = 1 :=
  IsMulTorsionFree.eq_one_of_pow_eq_one x n hxn hn

@[to_additive, simp]
theorem pow_eq_one_iff : x ^ n = 1 ↔ x = 1 ∨ n = 0 := by
  if hn : n = 0 then simp [hn]
  else if hx : x = 1 then simp [*]
  else simp [*, mt (eq_one_of_pow_eq_one · hn)]

@[to_additive nsmul_eq_zero_iff_right]
theorem pow_eq_one_iff_left (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by simp [hn]
