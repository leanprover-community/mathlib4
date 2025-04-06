/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Jordan rings

Let `A` be a non-unital, non-associative ring. Then `A` is said to be a (commutative, linear) Jordan
ring if the multiplication is commutative and satisfies a weak associativity law known as the
Jordan Identity: for all `a` and `b` in `A`,
```
(a * b) * a^2 = a * (b * a^2)
```
i.e. the operators of multiplication by `a` and `a^2` commute.

A more general concept of a (non-commutative) Jordan ring can also be defined, as a
(non-commutative, non-associative) ring `A` where, for each `a` in `A`, the operators of left and
right multiplication by `a` and `a^2` commute.

Every associative algebra can be equipped with a symmetrized multiplication (characterized by
`SymAlg.sym_mul_sym`) making it into a commutative Jordan algebra (`IsCommJordan`).
Jordan algebras arising this way are said to be special.

A real Jordan algebra `A` can be introduced by
```lean
variable {A : Type*} [NonUnitalNonAssocCommRing A] [Module ℝ A] [SMulCommClass ℝ A A]
  [IsScalarTower ℝ A A] [IsCommJordan A]
```

## Main results

- `two_nsmul_lie_lmul_lmul_add_add_eq_zero` : Linearisation of the commutative Jordan axiom

## Implementation notes

We shall primarily be interested in linear Jordan algebras (i.e. over rings of characteristic not
two) leaving quadratic algebras to those better versed in that theory.

The conventional way to linearise the Jordan axiom is to equate coefficients (more formally, assume
that the axiom holds in all field extensions). For simplicity we use brute force algebraic expansion
and substitution instead.

## Motivation

Every Jordan algebra `A` has a triple product defined, for `a` `b` and `c` in `A` by
$$
{a\,b\,c} = (a * b) * c - (a * c) * b + a * (b * c).
$$
Via this triple product Jordan algebras are related to a number of other mathematical structures:
Jordan triples, partial Jordan triples, Jordan pairs and quadratic Jordan algebras. In addition to
their considerable algebraic interest ([mccrimmon2004]) these structures have been shown to have
deep connections to mathematical physics, functional analysis and differential geometry. For more
information about these connections the interested reader is referred to [alfsenshultz2003],
[chu2012], [friedmanscarr2005], [iordanescu2003] and [upmeier1987].

There are also exceptional Jordan algebras which can be shown not to be the symmetrization of any
associative algebra. The 3x3 matrices of octonions is the canonical example.

Non-commutative Jordan algebras have connections to the Vidav-Palmer theorem
[cabreragarciarodriguezpalacios2014].

## References

* [Cabrera García and Rodríguez Palacios, Non-associative normed algebras. Volume 1]
  [cabreragarciarodriguezpalacios2014]
* [Hanche-Olsen and Størmer, Jordan Operator Algebras][hancheolsenstormer1984]
* [McCrimmon, A taste of Jordan algebras][mccrimmon2004]

-/


variable (A : Type*)

/-- A (non-commutative) Jordan multiplication. -/
class IsJordan [Mul A] : Prop where
  lmul_comm_rmul : ∀ a b : A, a * b * a = a * (b * a)
  lmul_lmul_comm_lmul : ∀ a b : A, a * a * (a * b) = a * (a * a * b)
  lmul_lmul_comm_rmul : ∀ a b : A, a * a * (b * a) = a * a * b * a
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))
  rmul_comm_rmul_rmul : ∀ a b : A, b * a * (a * a) = b * (a * a) * a

/-- A commutative Jordan multiplication -/
class IsCommJordan [CommMagma A] : Prop where
  lmul_comm_rmul_rmul : ∀ a b : A, a * b * (a * a) = a * (b * (a * a))

-- see Note [lower instance priority]
/-- A (commutative) Jordan multiplication is also a Jordan multiplication -/
instance (priority := 100) IsCommJordan.toIsJordan [CommMagma A] [IsCommJordan A] : IsJordan A where
  lmul_comm_rmul a b := by rw [mul_comm, mul_comm a b]
  lmul_lmul_comm_lmul a b := by
    rw [mul_comm (a * a) (a * b), IsCommJordan.lmul_comm_rmul_rmul,
      mul_comm b (a * a)]
  lmul_comm_rmul_rmul := IsCommJordan.lmul_comm_rmul_rmul
  lmul_lmul_comm_rmul a b := by
    rw [mul_comm (a * a) (b * a), mul_comm b a,
      IsCommJordan.lmul_comm_rmul_rmul, mul_comm, mul_comm b (a * a)]
  rmul_comm_rmul_rmul a b := by
    rw [mul_comm b a, IsCommJordan.lmul_comm_rmul_rmul, mul_comm]

-- see Note [lower instance priority]
/-- Semigroup multiplication satisfies the (non-commutative) Jordan axioms -/
instance (priority := 100) Semigroup.isJordan [Semigroup A] : IsJordan A where
  lmul_comm_rmul a b := by rw [mul_assoc]
  lmul_lmul_comm_lmul a b := by rw [mul_assoc, mul_assoc]
  lmul_comm_rmul_rmul a b := by rw [mul_assoc]
  lmul_lmul_comm_rmul a b := by rw [← mul_assoc]
  rmul_comm_rmul_rmul a b := by rw [← mul_assoc, ← mul_assoc]

-- see Note [lower instance priority]
instance (priority := 100) CommSemigroup.isCommJordan [CommSemigroup A] : IsCommJordan A where
  lmul_comm_rmul_rmul _ _ := mul_assoc _ _ _

local notation "L" => AddMonoid.End.mulLeft

local notation "R" => AddMonoid.End.mulRight

/-!
The Jordan axioms can be expressed in terms of commuting multiplication operators.
-/


section Commute

variable {A} [NonUnitalNonAssocRing A] [IsJordan A]

@[simp]
theorem commute_lmul_rmul (a : A) : Commute (L a) (R a) :=
  AddMonoidHom.ext fun _ => (IsJordan.lmul_comm_rmul _ _).symm

@[simp]
theorem commute_lmul_lmul_sq (a : A) : Commute (L a) (L (a * a)) :=
  AddMonoidHom.ext fun _ => (IsJordan.lmul_lmul_comm_lmul _ _).symm

@[simp]
theorem commute_lmul_rmul_sq (a : A) : Commute (L a) (R (a * a)) :=
  AddMonoidHom.ext fun _ => (IsJordan.lmul_comm_rmul_rmul _ _).symm

@[simp]
theorem commute_lmul_sq_rmul (a : A) : Commute (L (a * a)) (R a) :=
  AddMonoidHom.ext fun _ => IsJordan.lmul_lmul_comm_rmul _ _

@[simp]
theorem commute_rmul_rmul_sq (a : A) : Commute (R a) (R (a * a)) :=
  AddMonoidHom.ext fun _ => (IsJordan.rmul_comm_rmul_rmul _ _).symm

end Commute

variable {A} [NonUnitalNonAssocCommRing A]

/-!
The endomorphisms on an additive monoid `AddMonoid.End` form a `Ring`, and this may be equipped
with a Lie Bracket via `Ring.bracket`.
-/

theorem two_nsmul_lie_lmul_lmul_add_eq_lie_lmul_lmul_add [IsCommJordan A] (a b : A) :
    2 • (⁅L a, L (a * b)⁆ + ⁅L b, L (b * a)⁆) = ⁅L (a * a), L b⁆ + ⁅L (b * b), L a⁆ := by
  suffices 2 • ⁅L a, L (a * b)⁆ + 2 • ⁅L b, L (b * a)⁆ + ⁅L b, L (a * a)⁆ + ⁅L a, L (b * b)⁆ = 0 by
    rwa [← sub_eq_zero, ← sub_sub, sub_eq_add_neg, sub_eq_add_neg, lie_skew, lie_skew, nsmul_add]
  convert (commute_lmul_lmul_sq (a + b)).lie_eq using 1
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
  simp only [lie_add, add_lie, commute_lmul_lmul_sq, zero_add, add_zero]
  abel

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
  -- Porting note: was `nth_rw` instead of `conv_lhs`
  conv_lhs => enter [1, 1, 2, 2, 2]; rw [mul_comm a b]
  conv_lhs => enter [1, 2, 2, 2, 1]; rw [mul_comm c a]
  conv_lhs => enter [   2, 2, 2, 2]; rw [mul_comm b c]
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
