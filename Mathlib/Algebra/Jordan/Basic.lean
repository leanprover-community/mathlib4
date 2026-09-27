/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Algebra.Lie.OfAssociative

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

public section


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
