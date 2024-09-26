import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.MkIffOfInductiveProp

class AddMonoid.IsTorsionFree (M : Type*) [AddMonoid M] : Prop where
  nsmul_ne_zero (x : M) (n : ℕ) (hx : x ≠ 0) (hn : 0 < n) : n • x ≠ 0

@[to_additive, mk_iff]
class Monoid.IsTorsionFree (M : Type*) [Monoid M] : Prop where
  pow_ne_one (x : M) (n : ℕ) (hx : x ≠ 1) (hn : 0 < n) : x ^ n ≠ 1

attribute [to_additive] Monoid.isTorsionFree_iff

@[to_additive]
instance (priority := 100) Monoid.IsTorsionFree.of_subsingleton
    (M : Type*) [Monoid M] [Subsingleton M] : IsTorsionFree M where
  pow_ne_one _ _ := absurd (Subsingleton.elim _ _)

section Monoid

variable {M : Type*} [Monoid M] [Monoid.IsTorsionFree M] {x : M} {n : ℕ}

@[to_additive]
theorem pow_ne_one (hx : x ≠ 1) (hn : n ≠ 0) : x ^ n ≠ 1 :=
  Monoid.IsTorsionFree.pow_ne_one x n hx (Nat.pos_iff_ne_zero.2 hn)

@[to_additive, simp]
theorem pow_eq_one_iff : x ^ n = 1 ↔ x = 1 ∨ n = 0 := by
  if hn : n = 0 then simp [hn]
  else if hx : x = 1 then simp [*]
  else simp [pow_ne_one, *]

@[to_additive nsmul_eq_zero_iff_right]
theorem pow_eq_one_iff_left (hn : n ≠ 0) : x ^ n = 1 ↔ x = 1 := by simp [hn]

end Monoid
