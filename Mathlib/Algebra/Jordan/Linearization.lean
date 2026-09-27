/-
Copyright (c) 2026 LIU Yaohua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LIU Yaohua
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Ring.Associator
import Lean.Elab.Tactic.Grind

/-!
# Linearization of the commutative Jordan identity

In a commutative Jordan ring, the Jordan identity `a * b * (a * a) = a * (b * (a * a))`
can be restated as the vanishing of the associator: `associator a b (a * a) = 0`.

This file derives the standard first linearization of this identity by substituting
`a ↦ a ± c` and combining. The resulting identity expresses a relation among associators
with mixed arguments, and is a standard tool for subsequent multi-variable manipulations
(e.g. Peirce decompositions, triple product identities).

## Main results

* `IsCommJordan.four_nsmul_associator_mul_add` : the first linearization in arbitrary
  characteristic: `4 • associator a b (a * c) + 2 • associator c b (a * a) = 0`.
* `IsCommJordan.associator_mul_add` : when `A` is 2-torsion-free (`IsSMulRegular A 2`),
  this simplifies to `2 • associator a b (a * c) + associator c b (a * a) = 0`.
* `two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add` : a two-variable
  linearization identity for left multiplication operators.
* `two_nsmul_lie_lmul_lmul_add_add_eq_zero` : the corresponding three-variable
  operator-valued linearization.

## References

* [McCrimmon, *A Taste of Jordan Algebras*][mccrimmon2004], Proposition 1.8.5 (JAX2')
-/

public section

local notation "L" => AddMonoid.End.mulLeft

section OperatorLinearization

variable {A : Type*} [NonUnitalNonAssocCommRing A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-!
The endomorphisms on an additive monoid `AddMonoid.End` form a `Ring`, and this may be equipped
with a Lie Bracket via `Ring.bracket`.
-/

set_option backward.isDefEq.respectTransparency false in
theorem two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add [IsCommJordan A] (a b : A) :
    2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (b * a)⁆) = ⁅L (a * a), L b⁆ + ⁅L (b * b), L a⁆ := by
  suffices 2 • ⁅L a, L (a * b)⁆ + 2 • ⁅L b, L (b * a)⁆ + ⁅L b, L (a * a)⁆ + ⁅L a, L (b * b)⁆ = 0 by
    rwa [← sub_eq_zero, ← sub_sub, sub_eq_add_neg, sub_eq_add_neg, lie_skew, lie_skew, nsmul_add]
  convert (commute_lmul_lmul_sq (a + b)).lie_eq
  simp only [add_mul, mul_add, map_add, lie_add, add_lie, mul_comm b a,
    (commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq, zero_add, add_zero, two_smul]
  abel

-- Porting note: the monolithic `calc`-based proof of `two_nsmul_lie_lmul_lmul_add_add_eq_zero`
-- has had four auxiliary parts `aux{0,1,2,3}` split off from it.
private theorem aux0 {a b c : A} : ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ =
    ⁅L a + L b + L c, L (a * a) + L (b * b) + L (c * c) +
    2 • L (a * b) + 2 • L (c * a) + 2 • L (b * c)⁆ := by
  rw [add_mul, add_mul]
  iterate 6 rw [mul_add]
  iterate 10 rw [map_add]
  rw [mul_comm b a, mul_comm c a, mul_comm c b]
  iterate 3 rw [two_smul]
  simp only [add_lie]
  abel_nf

set_option backward.isDefEq.respectTransparency false in
private theorem aux1 {a b c : A} :
    ⁅L a + L b + L c, L (a * a) + L (b * b) + L (c * c) +
    2 • L (a * b) + 2 • L (c * a) + 2 • L (b * c)⁆
    =
    ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
    ⁅L a, 2 • L (a * b)⁆ + ⁅L a, 2 • L (c * a)⁆ + ⁅L a, 2 • L (b * c)⁆ +
    (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
    ⁅L b, 2 • L (a * b)⁆ + ⁅L b, 2 • L (c * a)⁆ + ⁅L b, 2 • L (b * c)⁆) +
    (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
    ⁅L c, 2 • L (a * b)⁆ + ⁅L c, 2 • L (c * a)⁆ + ⁅L c, 2 • L (b * c)⁆) := by
  rw [add_lie, add_lie]
  iterate 15 rw [lie_add]

variable [IsCommJordan A]

set_option backward.isDefEq.respectTransparency false in
private theorem aux2 {a b c : A} :
    ⁅L a, L (a * a)⁆ + ⁅L a, L (b * b)⁆ + ⁅L a, L (c * c)⁆ +
    ⁅L a, 2 • L (a * b)⁆ + ⁅L a, 2 • L (c * a)⁆ + ⁅L a, 2 • L (b * c)⁆ +
    (⁅L b, L (a * a)⁆ + ⁅L b, L (b * b)⁆ + ⁅L b, L (c * c)⁆ +
    ⁅L b, 2 • L (a * b)⁆ + ⁅L b, 2 • L (c * a)⁆ + ⁅L b, 2 • L (b * c)⁆) +
    (⁅L c, L (a * a)⁆ + ⁅L c, L (b * b)⁆ + ⁅L c, L (c * c)⁆ +
    ⁅L c, 2 • L (a * b)⁆ + ⁅L c, 2 • L (c * a)⁆ + ⁅L c, 2 • L (b * c)⁆)
    =
    ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ + 2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
    (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ + 2 • (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
    (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ + 2 • (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
    (2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆) := by
  rw [(commute_lmul_lmul_sq a).lie_eq, (commute_lmul_lmul_sq b).lie_eq,
    (commute_lmul_lmul_sq c).lie_eq, zero_add, add_zero, add_zero]
  simp only [lie_nsmul]
  abel

private theorem aux3 {a b c : A} :
    ⁅L a, L (b * b)⁆ + ⁅L b, L (a * a)⁆ + 2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (a * b)⁆) +
    (⁅L a, L (c * c)⁆ + ⁅L c, L (a * a)⁆ + 2 • (⁅L a, L (c * a)⁆ + ⁅L c, L (c * a)⁆)) +
    (⁅L b, L (c * c)⁆ + ⁅L c, L (b * b)⁆ + 2 • (⁅L b, L (b * c)⁆ + ⁅L c, L (b * c)⁆)) +
    (2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆)
    =
    2 • ⁅L a, L (b * c)⁆ + 2 • ⁅L b, L (c * a)⁆ + 2 • ⁅L c, L (a * b)⁆ := by
  rw [add_eq_right]
  nth_rw 2 [mul_comm a b]
  nth_rw 1 [mul_comm c a]
  nth_rw 2 [mul_comm b c]
  iterate 3 rw [two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add]
  iterate 2 rw [← lie_skew (L (a * a)), ← lie_skew (L (b * b)), ← lie_skew (L (c * c))]
  abel

theorem two_nsmul_lie_lmul_lmul_add_add_eq_zero (a b c : A) :
    2 • (⁅L a, L (b * c)⁆ + ⁅L b, L (c * a)⁆ + ⁅L c, L (a * b)⁆) = 0 := by
  symm
  calc
    0 = ⁅L (a + b + c), L ((a + b + c) * (a + b + c))⁆ := by
      rw [(commute_lmul_lmul_sq (a + b + c)).lie_eq]
    _ = _ := by rw [aux0, aux1, aux2, aux3, nsmul_add, nsmul_add]

end OperatorLinearization

namespace IsCommJordan

variable {A : Type*} [NonUnitalNonAssocCommRing A] [IsCommJordan A]

/-- First linearization of the commutative Jordan identity -/
theorem four_nsmul_associator_mul_add (a b c : A) :
    4 • associator a b (a * c) + 2 • associator c b (a * a) = 0 := by
  grind [associator_apply, add_mul, mul_add, sub_mul, mul_sub, mul_comm c a,
    lmul_comm_rmul_rmul a b, lmul_comm_rmul_rmul c b,
    lmul_comm_rmul_rmul (a + c) b, lmul_comm_rmul_rmul (a - c) b]

/-- A simplified form of the first linearization of the commutative Jordan
identity for 2-torsion-free rings -/
theorem associator_mul_add (hreg : IsSMulRegular A 2) (a b c : A) :
    2 • associator a b (a * c) + associator c b (a * a) = 0 := by
  apply hreg
  · simpa [smul_smul] using four_nsmul_associator_mul_add a b c

end IsCommJordan
