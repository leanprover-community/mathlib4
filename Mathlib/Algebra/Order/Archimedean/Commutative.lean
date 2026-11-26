/-
Copyright (c) 2026 Ishan Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ishan Singh
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Archimedean.Defs

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.GroupTheory.GroupAction.Ring

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Archimedean ordered rings are commutative

This file proves that multiplication in an Archimedean linearly ordered (non-unital,
non-associative) ring is commutative. For division rings this is a theorem of Hilbert: an
Archimedean ordered division ring is a field. The proof given here is a short division-free
argument, not Hilbert's.

The statement fails for semirings: in a non-commutative linearly ordered division ring, the
elements `a` with `1 ≤ a ≤ n` for some natural number `n`, together with `0`, form a
non-commutative Archimedean strictly ordered semiring.

## Main declarations

* `Archimedean.isMulCommutative`: an Archimedean linearly ordered ring is commutative.
* `Archimedean.field`: the `Field` structure on an Archimedean linearly ordered division ring.

## References

* D. Hilbert, _Grundlagen der Geometrie_, Teubner, 1899, §32
-/

@[expose] public section

/-- In an Archimedean linearly ordered ring, `a * b ≤ b * a` for positive `a`. -/
private theorem mul_le_mul_comm_of_pos {R : Type*} [NonUnitalNonAssocRing R] [LinearOrder R]
    [IsOrderedAddMonoid R] [PosMulMono R] [Archimedean R] {a : R} (ha : 0 < a) (b : R) :
    a * b ≤ b * a := by
  by_contra! h
  -- Choose `n` with `a * a < n • (a * b - b * a)` and write `n • b = k • a + r` with `0 ≤ r < a`.
  -- Then `n • (a * b - b * a) = a * r - r * a ≤ a * r ≤ a * a`, a contradiction.
  obtain ⟨n, hn⟩ := exists_lt_nsmul (sub_pos.2 h) (a * a)
  obtain ⟨k, ⟨hk, hk'⟩, -⟩ := existsUnique_zsmul_near_of_pos' ha (n • b)
  refine hn.not_ge ?_
  calc n • (a * b - b * a)
    _ = a * (n • b - k • a) - (n • b - k • a) * a := by
      simp [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, nsmul_sub]
    _ ≤ a * (n • b - k • a) := sub_le_self _ (mul_nonneg hk ha.le)
    _ ≤ a * a := mul_le_mul_of_nonneg_left hk'.le ha.le

/-- An Archimedean linearly ordered ring is commutative. Neither a unit nor associativity of
multiplication is assumed, and only left multiplication by nonnegative elements is assumed to be
monotone (`PosMulMono`).

This is not an instance, since it would be tried in every failing search for `IsMulCommutative`.
After `have := Archimedean.isMulCommutative R`, use `mul_comm'` for the equation `a * b = b * a`,
and `open scoped IsMulCommutative` to get the `CommRing` instance of a unital ring. See
`Archimedean.field` for division rings. -/
theorem Archimedean.isMulCommutative (R : Type*) [NonUnitalNonAssocRing R] [LinearOrder R]
    [IsOrderedAddMonoid R] [PosMulMono R] [Archimedean R] : IsMulCommutative R := by
  have comm {a : R} (ha : 0 < a) (b : R) : a * b = b * a :=
    (mul_le_mul_comm_of_pos ha b).antisymm <| by simpa using mul_le_mul_comm_of_pos ha (-b)
  refine .of_comm fun a b ↦ ?_
  obtain ha | rfl | ha := lt_trichotomy a 0
  · simpa using comm (neg_pos.2 ha) b
  · simp
  · exact comm ha b

/-- An Archimedean linearly ordered division ring is a field.

This is not an instance, since it would make every search for a `Field` instance look for an
order. -/
@[instance_reducible]
def Archimedean.field (K : Type*) [DivisionRing K] [LinearOrder K] [IsOrderedRing K]
    [Archimedean K] : Field K where
  mul_comm := (Archimedean.isMulCommutative K).is_comm.comm
