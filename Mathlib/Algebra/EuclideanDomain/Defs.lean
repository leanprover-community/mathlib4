/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin, Mario Carneiro
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

#align_import algebra.euclidean_domain.defs from "leanprover-community/mathlib"@"ee7b9f9a9ac2a8d9f04ea39bbfe6b1a3be053b38"

/-!
# Euclidean domains

This file introduces Euclidean domains and provides the extended Euclidean algorithm. To be precise,
a slightly more general version is provided which is sometimes called a transfinite Euclidean domain
and differs in the fact that the degree function need not take values in `ℕ` but can take values in
any well-ordered set. Transfinite Euclidean domains were introduced by Motzkin and examples which
don't satisfy the classical notion were provided independently by Hiblot and Nagata.

## Main definitions

* `EuclideanDomain`: Defines Euclidean domain with functions `quotient` and `remainder`. Instances
  of `Div` and `Mod` are provided, so that one can write `a = b * (a / b) + a % b`.
* `gcd`: defines the greatest common divisors of two elements of a Euclidean domain.
* `xgcd`: given two elements `a b : R`, `xgcd a b` defines the pair `(x, y)` such that
  `x * a + y * b = gcd a b`.
* `lcm`: defines the lowest common multiple of two elements `a` and `b` of a Euclidean domain as
  `a * b / (gcd a b)`

## Main statements

See `Algebra.EuclideanDomain.Basic` for most of the theorems about Euclidean domains,
including Bézout's lemma.

See `Algebra.EuclideanDomain.Instances` for the fact that `ℤ` is a Euclidean domain,
as is any field.

## Notation

`≺` denotes the well founded relation on the Euclidean domain, e.g. in the example of the polynomial
ring over a field, `p ≺ q` for polynomials `p` and `q` if and only if the degree of `p` is less than
the degree of `q`.

## Implementation details

Instead of working with a valuation, `EuclideanDomain` is implemented with the existence of a well
founded relation `r` on the integral domain `R`, which in the example of `ℤ` would correspond to
setting `i ≺ j` for integers `i` and `j` if the absolute value of `i` is smaller than the absolute
value of `j`.

## References

* [Th. Motzkin, *The Euclidean algorithm*][MR32592]
* [J.-J. Hiblot, *Des anneaux euclidiens dont le plus petit algorithme n'est pas à valeurs finies*]
  [MR399081]
* [M. Nagata, *On Euclid algorithm*][MR541021]


## Tags

Euclidean domain, transfinite Euclidean domain, Bézout's lemma
-/


universe u

/-- A `EuclideanDomain` is a non-trivial commutative ring with a division and a remainder,
  satisfying `b * (a / b) + a % b = a`.
  The definition of a Euclidean domain usually includes a valuation function `R → ℕ`.
  This definition is slightly generalised to include a well founded relation
  `r` with the property that `r (a % b) b`, instead of a valuation.  -/
class EuclideanDomain (R : Type u) extends CommRing R, Nontrivial R where
  /-- A division function (denoted `/`) on `R`.
    This satisfies the property `b * (a / b) + a % b = a`, where `%` denotes `remainder`. -/
  protected quotient : R → R → R
  /-- Division by zero should always give zero by convention. -/
  protected quotient_zero : ∀ a, quotient a 0 = 0
  /-- A remainder function (denoted `%`) on `R`.
    This satisfies the property `b * (a / b) + a % b = a`, where `/` denotes `quotient`. -/
  protected remainder : R → R → R
  /-- The property that links the quotient and remainder functions.
    This allows us to compute GCDs and LCMs. -/
  protected quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
  /-- A well-founded relation on `R`, satisfying `r (a % b) b`.
    This ensures that the GCD algorithm always terminates. -/
  protected r : R → R → Prop
  /-- The relation `r` must be well-founded.
    This ensures that the GCD algorithm always terminates. -/
  r_wellFounded : WellFounded r
  /-- The relation `r` satisfies `r (a % b) b`. -/
  protected remainder_lt : ∀ (a) {b}, b ≠ 0 → r (remainder a b) b
  /-- An additional constraint on `r`. -/
  mul_left_not_lt : ∀ (a) {b}, b ≠ 0 → ¬r (a * b) a
#align euclidean_domain EuclideanDomain
#align euclidean_domain.quotient EuclideanDomain.quotient
#align euclidean_domain.quotient_zero EuclideanDomain.quotient_zero
#align euclidean_domain.remainder EuclideanDomain.remainder
#align euclidean_domain.quotient_mul_add_remainder_eq EuclideanDomain.quotient_mul_add_remainder_eq
#align euclidean_domain.r EuclideanDomain.r
#align euclidean_domain.r_well_founded EuclideanDomain.r_wellFounded
#align euclidean_domain.remainder_lt EuclideanDomain.remainder_lt
#align euclidean_domain.mul_left_not_lt EuclideanDomain.mul_left_not_lt

namespace EuclideanDomain

variable {R : Type u} [EuclideanDomain R]

/-- Abbreviated notation for the well-founded relation `r` in a Euclidean domain. -/
local infixl:50 " ≺ " => EuclideanDomain.r

local instance wellFoundedRelation : WellFoundedRelation R where
  wf := r_wellFounded

-- see Note [lower instance priority]
instance (priority := 70) : Div R :=
  ⟨EuclideanDomain.quotient⟩

-- see Note [lower instance priority]
instance (priority := 70) : Mod R :=
  ⟨EuclideanDomain.remainder⟩

theorem div_add_mod (a b : R) : b * (a / b) + a % b = a :=
  EuclideanDomain.quotient_mul_add_remainder_eq _ _
#align euclidean_domain.div_add_mod EuclideanDomain.div_add_mod

theorem mod_add_div (a b : R) : a % b + b * (a / b) = a :=
  (add_comm _ _).trans (div_add_mod _ _)
#align euclidean_domain.mod_add_div EuclideanDomain.mod_add_div

theorem mod_add_div' (m k : R) : m % k + m / k * k = m := by
  rw [mul_comm]
  exact mod_add_div _ _
#align euclidean_domain.mod_add_div' EuclideanDomain.mod_add_div'

theorem div_add_mod' (m k : R) : m / k * k + m % k = m := by
  rw [mul_comm]
  exact div_add_mod _ _
#align euclidean_domain.div_add_mod' EuclideanDomain.div_add_mod'

theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) :=
  calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]
#align euclidean_domain.mod_eq_sub_mul_div EuclideanDomain.mod_eq_sub_mul_div

theorem mod_lt : ∀ (a) {b : R}, b ≠ 0 → a % b ≺ b :=
  EuclideanDomain.remainder_lt
#align euclidean_domain.mod_lt EuclideanDomain.mod_lt

theorem mul_right_not_lt {a : R} (b) (h : a ≠ 0) : ¬a * b ≺ b := by
  rw [mul_comm]
  exact mul_left_not_lt b h
#align euclidean_domain.mul_right_not_lt EuclideanDomain.mul_right_not_lt

@[simp]
theorem mod_zero (a : R) : a % 0 = a := by simpa only [zero_mul, zero_add] using div_add_mod a 0
#align euclidean_domain.mod_zero EuclideanDomain.mod_zero

theorem lt_one (a : R) : a ≺ (1 : R) → a = 0 :=
  haveI := Classical.dec
  not_imp_not.1 fun h => by simpa only [one_mul] using mul_left_not_lt 1 h
#align euclidean_domain.lt_one EuclideanDomain.lt_one

theorem val_dvd_le : ∀ a b : R, b ∣ a → a ≠ 0 → ¬a ≺ b
  | _, b, ⟨d, rfl⟩, ha => mul_left_not_lt b (mt (by rintro rfl; exact mul_zero _) ha)
#align euclidean_domain.val_dvd_le EuclideanDomain.val_dvd_le

@[simp]
theorem div_zero (a : R) : a / 0 = 0 :=
  EuclideanDomain.quotient_zero a
#align euclidean_domain.div_zero EuclideanDomain.div_zero

section

open scoped Classical

@[elab_as_elim]
theorem GCD.induction {P : R → R → Prop} (a b : R) (H0 : ∀ x, P 0 x)
    (H1 : ∀ a b, a ≠ 0 → P (b % a) a → P a b) : P a b :=
  if a0 : a = 0 then by
    -- Porting note: required for hygiene, the equation compiler introduces a dummy variable `x`
    -- See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/unnecessarily.20tombstoned.20argument/near/314573315
    change P a b
    exact a0.symm ▸ H0 b
  else
    have _ := mod_lt b a0
    H1 _ _ a0 (GCD.induction (b % a) a H0 H1)
termination_by a
#align euclidean_domain.gcd.induction EuclideanDomain.GCD.induction

end

section GCD

variable [DecidableEq R]

/-- `gcd a b` is a (non-unique) element such that `gcd a b ∣ a` `gcd a b ∣ b`, and for
  any element `c` such that `c ∣ a` and `c ∣ b`, then `c ∣ gcd a b` -/
def gcd (a b : R) : R :=
  if a0 : a = 0 then b
  else
    have _ := mod_lt b a0
    gcd (b % a) a
termination_by a
#align euclidean_domain.gcd EuclideanDomain.gcd

@[simp]
theorem gcd_zero_left (a : R) : gcd 0 a = a := by
  rw [gcd]
  exact if_pos rfl
#align euclidean_domain.gcd_zero_left EuclideanDomain.gcd_zero_left

/-- An implementation of the extended GCD algorithm.
At each step we are computing a triple `(r, s, t)`, where `r` is the next value of the GCD
algorithm, to compute the greatest common divisor of the input (say `x` and `y`), and `s` and `t`
are the coefficients in front of `x` and `y` to obtain `r` (i.e. `r = s * x + t * y`).
The function `xgcdAux` takes in two triples, and from these recursively computes the next triple:
```
xgcdAux (r, s, t) (r', s', t') = xgcdAux (r' % r, s' - (r' / r) * s, t' - (r' / r) * t) (r, s, t)
```
-/
def xgcdAux (r s t r' s' t' : R) : R × R × R :=
  if _hr : r = 0 then (r', s', t')
  else
    let q := r' / r
    have _ := mod_lt r' _hr
    xgcdAux (r' % r) (s' - q * s) (t' - q * t) r s t
termination_by r
#align euclidean_domain.xgcd_aux EuclideanDomain.xgcdAux

@[simp]
theorem xgcd_zero_left {s t r' s' t' : R} : xgcdAux 0 s t r' s' t' = (r', s', t') := by
  unfold xgcdAux
  exact if_pos rfl
#align euclidean_domain.xgcd_zero_left EuclideanDomain.xgcd_zero_left

theorem xgcdAux_rec {r s t r' s' t' : R} (h : r ≠ 0) :
    xgcdAux r s t r' s' t' = xgcdAux (r' % r) (s' - r' / r * s) (t' - r' / r * t) r s t := by
  conv =>
    lhs
    rw [xgcdAux]
  exact if_neg h
#align euclidean_domain.xgcd_aux_rec EuclideanDomain.xgcdAux_rec

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : R) : R × R :=
  (xgcdAux x 1 0 y 0 1).2
#align euclidean_domain.xgcd EuclideanDomain.xgcd

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcdA (x y : R) : R :=
  (xgcd x y).1
#align euclidean_domain.gcd_a EuclideanDomain.gcdA

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcdB (x y : R) : R :=
  (xgcd x y).2
#align euclidean_domain.gcd_b EuclideanDomain.gcdB

@[simp]
theorem gcdA_zero_left {s : R} : gcdA 0 s = 0 := by
  unfold gcdA
  rw [xgcd, xgcd_zero_left]
#align euclidean_domain.gcd_a_zero_left EuclideanDomain.gcdA_zero_left

@[simp]
theorem gcdB_zero_left {s : R} : gcdB 0 s = 1 := by
  unfold gcdB
  rw [xgcd, xgcd_zero_left]
#align euclidean_domain.gcd_b_zero_left EuclideanDomain.gcdB_zero_left

theorem xgcd_val (x y : R) : xgcd x y = (gcdA x y, gcdB x y) :=
  rfl
#align euclidean_domain.xgcd_val EuclideanDomain.xgcd_val

end GCD

section LCM

variable [DecidableEq R]

/-- `lcm a b` is a (non-unique) element such that `a ∣ lcm a b` `b ∣ lcm a b`, and for
  any element `c` such that `a ∣ c` and `b ∣ c`, then `lcm a b ∣ c` -/
def lcm (x y : R) : R :=
  x * y / gcd x y
#align euclidean_domain.lcm EuclideanDomain.lcm

end LCM

end EuclideanDomain
