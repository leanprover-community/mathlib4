/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Real.Star
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The Clauser-Horne-Shimony-Holt inequality and Tsirelson's inequality.

We establish a version of the Clauser-Horne-Shimony-Holt (CHSH) inequality
(which is a generalization of Bell's inequality).
This is a foundational result which implies that
quantum mechanics is not a local hidden variable theory.

As usually stated the CHSH inequality requires substantial language from physics and probability,
but it is possible to give a statement that is purely about ordered \*-algebras.
We do that here, to avoid as many practical and logical dependencies as possible.
Since the algebra of observables of any quantum system is an ordered \*-algebra
(in particular a von Neumann algebra) this is a strict generalization of the usual statement.

Let `R` be a \*-ring.

A CHSH tuple in `R` consists of
* four elements `A₀ A₁ B₀ B₁ : R`, such that
* each `Aᵢ` and `Bⱼ` is a self-adjoint involution, and
* the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that the four elements are observables (hence self-adjoint)
that take values ±1 (hence involutions), and that the `Aᵢ` are spacelike separated from the `Bⱼ`
(and hence commute).

The CHSH inequality says that when `R` is an ordered \*-ring
(that is, a \*-ring which is ordered, and for every `r : R`, `0 ≤ star r * r`),
which is moreover *commutative*, we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`

On the other hand, Tsirelson's inequality says that for any ordered \*-ring we have
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2√2`

(A caveat: in the commutative case we need 2⁻¹ in the ring,
and in the noncommutative case we need √2 and √2⁻¹.
To keep things simple we just assume our rings are ℝ-algebras.)

The proofs I've seen in the literature either
assume a significant framework for quantum mechanics,
or assume the ring is a C⋆-algebra.
In the C⋆-algebra case,
the order structure is completely determined by the \*-algebra structure:
`0 ≤ A` iff there exists some `B` so `A = star B * B`.
There's a nice proof of both bounds in this setting at
https://en.wikipedia.org/wiki/Tsirelson%27s_bound
The proof given here is purely algebraic.

## Future work

One can show that Tsirelson's inequality is tight.
In the \*-ring of n-by-n complex matrices, if `A ≤ λ I` for some `λ : ℝ`,
then every eigenvalue has absolute value at most `λ`.
There is a CHSH tuple in 4-by-4 matrices such that
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁` has `2√2` as an eigenvalue.

## References

* [Clauser, Horne, Shimony, Holt,
  *Proposed experiment to test local hidden-variable theories*][zbMATH06785026]
* [Bell, *On the Einstein Podolsky Rosen Paradox*][MR3790629]
* [Tsirelson, *Quantum generalizations of Bell's inequality*][MR577178]

-/

@[expose] public section


universe u

/-- A CHSH tuple in a \*-monoid consists of 4 self-adjoint involutions `A₀ A₁ B₀ B₁` such that
the `Aᵢ` commute with the `Bⱼ`.

The physical interpretation is that `A₀` and `A₁` are a pair of Boolean observables which
are spacelike separated from another pair `B₀` and `B₁` of Boolean observables.
-/
structure IsCHSHTuple {R} [Monoid R] [StarMul R] (A₀ A₁ B₀ B₁ : R) : Prop where
  A₀_inv : A₀ ^ 2 = 1
  A₁_inv : A₁ ^ 2 = 1
  B₀_inv : B₀ ^ 2 = 1
  B₁_inv : B₁ ^ 2 = 1
  A₀_sa : star A₀ = A₀
  A₁_sa : star A₁ = A₁
  B₀_sa : star B₀ = B₀
  B₁_sa : star B₁ = B₁
  A₀B₀_commutes : A₀ * B₀ = B₀ * A₀
  A₀B₁_commutes : A₀ * B₁ = B₁ * A₀
  A₁B₀_commutes : A₁ * B₀ = B₀ * A₁
  A₁B₁_commutes : A₁ * B₁ = B₁ * A₁

variable {R : Type u}

theorem CHSH_id [CommRing R] {A₀ A₁ B₀ B₁ : R} (A₀_inv : A₀ ^ 2 = 1) (A₁_inv : A₁ ^ 2 = 1)
    (B₀_inv : B₀ ^ 2 = 1) (B₁_inv : B₁ ^ 2 = 1) :
    (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) =
      4 * (2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁) := by
  grind

/-- Given a CHSH tuple (A₀, A₁, B₀, B₁) in a *commutative* ordered \*-algebra over ℝ,
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2`.

(We could work over ℤ[⅟2] if we wanted to!)
-/
theorem CHSH_inequality_of_comm [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2 := by
  let P := 2 - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁
  have i₁ : 0 ≤ P := by
    have idem : P * P = 4 * P := CHSH_id T.A₀_inv T.A₁_inv T.B₀_inv T.B₁_inv
    have idem' : P = (1 / 4 : ℝ) • (P * P) := by
      have h : 4 * P = (4 : ℝ) • P := by simp [map_ofNat, Algebra.smul_def]
      rw [idem, h, ← mul_smul]
      simp
    have sa : star P = P := by
      dsimp [P]
      simp only [star_add, star_sub, star_mul, star_ofNat, T.A₀_sa, T.A₁_sa, T.B₀_sa,
        T.B₁_sa, mul_comm B₀, mul_comm B₁]
    simpa only [← idem', sa]
      using smul_nonneg (by simp : (0 : ℝ) ≤ 1 / 4) (star_mul_self_nonneg P)
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add] using i₁

/-!
We now prove some rather specialized lemmas in preparation for the Tsirelson inequality,
which we hide in a namespace as they are unlikely to be useful elsewhere.
-/


namespace TsirelsonInequality

/-!
Before proving Tsirelson's bound,
we prepare some easy lemmas about √2.
-/

theorem sqrt_two_inv_mul_self : (√2)⁻¹ * (√2)⁻¹ = (2⁻¹ : ℝ) := by
  rw [← mul_inv]
  simp

end TsirelsonInequality

open TsirelsonInequality

/-- In a noncommutative ordered \*-algebra over ℝ,
Tsirelson's bound for a CHSH tuple (A₀, A₁, B₀, B₁) is
`A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ 2^(3/2) • 1`.

We prove this by providing an explicit sum-of-squares decomposition
of the difference.

(We could work over `ℤ[2^(1/2), 2^(-1/2)]` if we really wanted to!)
-/
theorem tsirelson_inequality [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [Algebra ℝ R] [IsOrderedModule ℝ R] [StarModule ℝ R]
    (A₀ A₁ B₀ B₁ : R) (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ ≤ √2 ^ 3 • (1 : R) := by
  -- abel will create `ℤ` multiplication. We will `simp` them away to `ℝ` multiplication.
  have M : ∀ (m : ℤ) (a : ℝ) (x : R), m • a • x = ((m : ℝ) * a) • x := fun m a x => by
    rw [← Int.cast_smul_eq_zsmul ℝ, ← mul_smul]
  let P := (√2)⁻¹ • (A₁ + A₀) - B₀
  let Q := (√2)⁻¹ • (A₁ - A₀) + B₁
  have w : √2 ^ 3 • (1 : R) - A₀ * B₀ - A₀ * B₁ - A₁ * B₀ + A₁ * B₁ = (√2)⁻¹ • (P ^ 2 + Q ^ 2) := by
    dsimp [P, Q]
    -- distribute out all the powers and products appearing on the RHS
    simp only [sq, sub_mul, mul_sub, add_mul, mul_add, smul_add, smul_sub]
    -- pull all coefficients out to the front, and combine `√2`s where possible
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, ← mul_smul, sqrt_two_inv_mul_self]
    -- replace Aᵢ * Aᵢ = 1 and Bᵢ * Bᵢ = 1
    simp only [← sq, T.A₀_inv, T.A₁_inv, T.B₀_inv, T.B₁_inv]
    -- move Aᵢ to the left of Bᵢ
    simp only [← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]
    -- collect terms, simplify coefficients, and collect terms again:
    abel_nf
    -- all terms coincide, but the last one. Simplify all other terms
    simp only [M]
    simp only [neg_mul, mul_inv_cancel_of_invertible, add_assoc, add_comm,
      add_left_comm, one_smul, Int.cast_neg, neg_smul, Int.cast_ofNat, ← add_smul]
    grind
  have pos : 0 ≤ (√2)⁻¹ • (P ^ 2 + Q ^ 2) := by
    have P_sa : star P = P := by
      simp only [P, star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₀_sa]
    have Q_sa : star Q = Q := by
      simp only [Q, star_smul, star_add, star_sub, star_id_of_comm, T.A₀_sa, T.A₁_sa, T.B₁_sa]
    have P2_nonneg : 0 ≤ P ^ 2 := by simpa only [P_sa, sq] using star_mul_self_nonneg P
    have Q2_nonneg : 0 ≤ Q ^ 2 := by simpa only [Q_sa, sq] using star_mul_self_nonneg Q
    positivity
  apply le_of_sub_nonneg
  simpa only [sub_add_eq_sub_sub, ← sub_add, w, Nat.cast_zero] using pos
