/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey
-/
module Counterexamples.JacobianConjecture

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormDet

/-!
# A counterexample to the Jacobian conjecture

The Jacobian conjecture asserts that a polynomial map `F : 𝔸ⁿ → 𝔸ⁿ` over a field of
characteristic zero whose Jacobian determinant is a nonzero constant admits an inverse which is
again a polynomial map. This file exhibits an explicit polynomial map in dimension `3` whose
Jacobian determinant is the constant `-2` and which is nevertheless not injective, so the
conjecture is false.

The polynomial map `F = (P, Q, R) : 𝔸³ → 𝔸³` is defined over `ℚ` by
```
P = (1 + xy)³·z + y²·(1 + xy)·(4 + 3xy)
Q = y + 3x·(1 + xy)²·z + 3x·y²·(4 + 3xy)
R = 2x − 3x²·y − x³·z
```
where `x = X 0`, `y = X 1`, `z = X 2`.

## Main statements

* `Keller.jacobian_det` : the formal Jacobian determinant `det (pderiv j (F i))` equals the
  constant polynomial `-2`, an identity in `MvPolynomial (Fin 3) ℚ` (hence over every field of
  characteristic zero, as all coefficients are rational).
* `Keller.keller_not_injective` : the induced evaluation map on `ℚ³` is not injective; concretely
  the three distinct rational points `(0, 0, -1/4)`, `(1, -3/2, 13/2)`, `(-1, 3/2, 13/2)` all map
  to `(-1/4, 0, 0)`.
* `Keller.not_jacobianConjecture` : the conjecture itself, stated as `Keller.JacobianConjecture`,
  is false over `ℚ`. A map with a unit Jacobian determinant which is not injective on points can
  have no compositional inverse.
* `Keller.keller_not_injective_C` : the same collision transferred to `ℂ` via `algebraMap ℚ ℂ`.

A nonzero constant Jacobian together with a non-injective map is exactly a Keller map that is not
a polynomial automorphism.

## References

The polynomial map is the dimension-`3` counterexample announced by Levent Alpöge, crediting
Akhil Mathew, in *A counterexample to the Jacobian conjecture* (2026), Theorem 3.1. This file
certifies the algebraic identity of Theorem 3.1 and the rational (hence characteristic-zero)
fiber collision. It does not verify the preprint's global-geometry sections, the
behaviour-at-infinity and properness analysis, or the stabilization to dimensions `n > 3`.

The statement `JacobianConjecture` below is aligned with the formulation used by the
`formal-conjectures` project, in `FormalConjectures/Wikipedia/JacobianConjecture.lean`
(`google-deepmind/formal-conjectures`, PR #4474, merged 2026-07-26). The correspondence is
recorded in detail before the statement. Only the shape of the statement is taken from there; the
proofs below are independent.

Several formalizations of this counterexample were written independently in the days following
the announcement, and are collected in the Lean Zulip thread
https://leanprover.zulipchat.com/#narrow/channel/583339-AI-authored-projects/topic/Counterexample.20to.20the.20Jacobean.20conjecture
The verification adapted in this file is at https://github.com/jyh/jacobian-verify
-/

open MvPolynomial

namespace Counterexample.Keller

/-! ### The polynomials `P`, `Q`, `R` over `ℚ` -/

/-- First coordinate `P = (1 + xy)³·z + y²·(1 + xy)·(4 + 3xy)`. -/
noncomputable def P : MvPolynomial (Fin 3) ℚ :=
  (1 + X 0 * X 1) ^ 3 * X 2 + X 1 ^ 2 * (1 + X 0 * X 1) * (4 + 3 * (X 0 * X 1))

/-- Second coordinate `Q = y + 3x·(1 + xy)²·z + 3x·y²·(4 + 3xy)`. -/
noncomputable def Q : MvPolynomial (Fin 3) ℚ :=
  X 1 + 3 * X 0 * (1 + X 0 * X 1) ^ 2 * X 2 + 3 * X 0 * X 1 ^ 2 * (4 + 3 * (X 0 * X 1))

/-- Third coordinate `R = 2x − 3x²·y − x³·z`. -/
noncomputable def R : MvPolynomial (Fin 3) ℚ :=
  2 * X 0 - 3 * X 0 ^ 2 * X 1 - X 0 ^ 3 * X 2

/-- The map `F = (P, Q, R)` as a vector of polynomials. -/
noncomputable def F : Fin 3 → MvPolynomial (Fin 3) ℚ := ![P, Q, R]

/-! ### The formal Jacobian and `det = -2` -/

/-- The formal Jacobian matrix `J i j = ∂ F i / ∂ x_j = pderiv j (F i)`. -/
noncomputable def J : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℚ) :=
  fun i j => pderiv j (F i)

/-- A derivation annihilates a numeral `≥ 2`: numerals appear as `OfNat.ofNat n`, not as
`Nat.cast n`, so `Derivation.map_natCast` needs the `Nat.cast_ofNat` bridge to apply. -/
private theorem pderiv_ofNat (i : Fin 3) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (OfNat.ofNat n : MvPolynomial (Fin 3) ℚ) = 0 := by
  rw [← Nat.cast_ofNat (R := MvPolynomial (Fin 3) ℚ) (n := n)]
  exact (pderiv i).map_natCast _

/-- **Theorem 3.1, first identity.** The formal Jacobian determinant of `F` is the constant
polynomial `-2`. This is an identity in `MvPolynomial (Fin 3) ℚ`, verified by expanding the nine
partial derivatives and evaluating the determinant with `eval_det`. -/
theorem jacobian_det : J.det = C (-2) := by
  have hC : (C (-2 : ℚ) : MvPolynomial (Fin 3) ℚ) = -2 := by
    rw [map_neg, _root_.map_ofNat]
  -- The six off-diagonal partials `∂ x_i / ∂ x_j` (`i ≠ j`) vanish; supplied explicitly so
  -- `simp` need not discharge the `Fin` inequality side-goals of `pderiv_X_of_ne`.
  have h01 : pderiv 0 (X 1 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h02 : pderiv 0 (X 2 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h10 : pderiv 1 (X 0 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h12 : pderiv 1 (X 2 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h20 : pderiv 2 (X 0 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  have h21 : pderiv 2 (X 1 : MvPolynomial (Fin 3) ℚ) = 0 := pderiv_X_of_ne (by decide)
  -- The scalar constants `2, 3, 4` occurring in `P, Q, R` also have zero derivative
  -- (instantiated at the literals so `simp` keys on them, unlike the generic `pderiv_ofNat`).
  have n2 : ∀ i : Fin 3, pderiv i (2 : MvPolynomial (Fin 3) ℚ) = 0 := fun i => pderiv_ofNat i 2
  have n3 : ∀ i : Fin 3, pderiv i (3 : MvPolynomial (Fin 3) ℚ) = 0 := fun i => pderiv_ofNat i 3
  have n4 : ∀ i : Fin 3, pderiv i (4 : MvPolynomial (Fin 3) ℚ) = 0 := fun i => pderiv_ofNat i 4
  rw [hC, Matrix.eta_fin_three J]
  -- Reduce each matrix entry `J i j` to `pderiv j` of the concrete coordinate, then push every
  -- `pderiv` through the ring structure down to `pderiv _ (X _)`.
  simp only [J, F, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, P, Q, R,
    map_add, map_sub, pderiv_mul, pderiv_pow, pderiv_one,
    pderiv_X_self, h01, h02, h10, h12, h20, h21, n2, n3, n4]
  eval_det

/-! ### The fiber collision over `ℚ` -/

/-- The evaluation map `ℚ³ → ℚ³` induced by `F`. -/
noncomputable def Fmap (p : Fin 3 → ℚ) : Fin 3 → ℚ := fun i => eval p (F i)

/-- `F(0, 0, -1/4) = (-1/4, 0, 0)`. -/
theorem eval_point0 : Fmap ![0, 0, -1/4] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [Fmap, F, P, Q, R]

/-- `F(1, -3/2, 13/2) = (-1/4, 0, 0)`. -/
theorem eval_point1 : Fmap ![1, -3/2, 13/2] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [Fmap, F, P, Q, R] <;> norm_num

/-- `F(-1, 3/2, 13/2) = (-1/4, 0, 0)`. -/
theorem eval_point2 : Fmap ![-1, 3/2, 13/2] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [Fmap, F, P, Q, R] <;> norm_num

/-- The three witness points are pairwise distinct (they already differ in the `x`-coordinate:
`0`, `1`, `-1`). -/
theorem points_pairwise_distinct :
    (![0, 0, -1/4] : Fin 3 → ℚ) ≠ ![1, -3/2, 13/2] ∧
    (![0, 0, -1/4] : Fin 3 → ℚ) ≠ ![-1, 3/2, 13/2] ∧
    (![1, -3/2, 13/2] : Fin 3 → ℚ) ≠ ![-1, 3/2, 13/2] := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;> exact absurd (congrFun h 0) (by norm_num)

/-! ### Packaging: not injective, and the headline statement -/

/-- **Theorem 3.1, second identity (consequence).** The map `F` is not injective on `ℚ³`: the two
distinct points `(0, 0, -1/4)` and `(1, -3/2, 13/2)` share the image `(-1/4, 0, 0)`. -/
theorem keller_not_injective : ¬ Function.Injective Fmap := by
  intro h
  have hEq : Fmap ![0, 0, -1/4] = Fmap ![1, -3/2, 13/2] := by
    rw [eval_point0, eval_point1]
  have hpts := h hEq
  have := congrFun hpts 0
  norm_num at this

/-- **The counterexample to the Jacobian conjecture (Theorem 3.1).**

`F` has constant nonzero formal Jacobian determinant (`= C (-2)`) yet is not injective as a map
`ℚ³ → ℚ³`, hence is not a polynomial automorphism. Since all data is rational, the same statement
holds over every field of characteristic zero. -/
theorem jacobian_conjecture_counterexample :
    J.det = C (-2) ∧ ¬ Function.Injective Fmap :=
  ⟨jacobian_det, keller_not_injective⟩

/-! ### The conjecture as a statement, and its refutation

The definitions below spell out the Jacobian conjecture itself, in the formulation used by the
`formal-conjectures` project (see the module docstring). Term by term, the correspondence with
that formulation is:

* `RegularFunction k σ τ` is `τ → MvPolynomial σ k`: a `τ`-tuple of polynomials in the variables
  indexed by `σ`. Same.
* `Jacobian f` is `Matrix.of fun i j => pderiv i (f j)`. Same. Note that this is the transpose of
  `J` above, which uses the convention `J i j = pderiv j (F i)`; `Matrix.det_transpose` makes the
  two determinants equal, so the hypothesis below is the one intended.
* `comp f g` is `fun i => bind₁ f (g i)`, that is, substitution of `f` into `g`. Same. In this
  diagrammatic order `f.comp g` applies `f` first, so it is the *second* conjunct `f.comp g = id`
  that exhibits `g` as a left inverse of `f` on points, and that is the conjunct used below.
* `id k σ` is `MvPolynomial.X`. Same.
* The hypothesis is `IsUnit f.Jacobian.det`, a unit in `MvPolynomial σ k` rather than the value
  `1`. Same. Over a field this is equivalent to the determinant being a nonzero constant.
* The conclusion is the existence of a two-sided compositional inverse. Same.

Two differences, both deliberate. First, `σ` carries `[DecidableEq σ]` here, where the reference
formulation supplies that instance through `open Classical`; the two determinants agree, so the
statement below is implied by the reference one and refuting it refutes the reference one.
Second, the reference quantifies over every field of characteristic zero, while
`not_jacobianConjecture` refutes the statement at `k := ℚ`. One field suffices to refute a claim
made about all of them.
-/

section Statement

variable {k : Type*} [CommRing k] {σ τ ι : Type*}

variable (k σ τ) in
/-- The type of regular functions from `k^σ` to `k^τ`: a `τ`-indexed tuple of polynomials in the
variables indexed by `σ`. -/
abbrev RegularFunction := τ → MvPolynomial σ k

namespace RegularFunction

/-- The Jacobian matrix of a regular function, viewed as a matrix of polynomials: the entry in
row `i` and column `j` is the partial derivative of the `j`-th component with respect to the
`i`-th variable. -/
noncomputable def Jacobian (f : RegularFunction k σ τ) : Matrix σ τ (MvPolynomial σ k) :=
  Matrix.of fun i j => pderiv i (f j)

/-- Composition of regular functions, by substitution. In this diagrammatic order `f.comp g` is
the map that applies `f` first and then `g`. -/
noncomputable def comp (f : RegularFunction k σ τ) (g : RegularFunction k τ ι) :
    RegularFunction k σ ι :=
  fun i => bind₁ f (g i)

variable (k σ) in
/-- The identity regular function, whose components are the coordinate variables. -/
noncomputable def id : RegularFunction k σ σ := X

end RegularFunction

-- `CharZero k` does not appear in the statement, but the conjecture is only ever asserted in
-- characteristic zero: over a field of characteristic `p` the Artin-Schreier map `x ↦ x - x ^ p`
-- has Jacobian determinant `1` and no polynomial inverse, so the statement below already fails
-- there for reasons unrelated to the question at hand.
/-- The **Jacobian conjecture** over a field `k` of characteristic zero: every polynomial self-map
of `k^σ` whose Jacobian determinant is a unit admits a two-sided inverse which is again a
polynomial map. This is false; see `not_jacobianConjecture`. -/
@[nolint unusedArguments]
def JacobianConjecture (k : Type*) [Field k] [CharZero k] : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (f : RegularFunction k σ σ),
    IsUnit f.Jacobian.det →
      ∃ g : RegularFunction k σ σ,
        g.comp f = RegularFunction.id k σ ∧ f.comp g = RegularFunction.id k σ

/-- The Jacobian of `F` in the packaging of `RegularFunction` is the transpose of `J`, which uses
the opposite index convention. -/
theorem jacobian_eq_transpose : RegularFunction.Jacobian F = J.transpose := rfl

/-- The Jacobian determinant of `F` is a unit of `MvPolynomial (Fin 3) ℚ`, since it is the
constant `-2` and `C` is a ring homomorphism. This is the hypothesis of the conjecture. -/
theorem isUnit_jacobian_det : IsUnit (RegularFunction.Jacobian F).det := by
  rw [jacobian_eq_transpose, Matrix.det_transpose, jacobian_det]
  exact (isUnit_iff_ne_zero.mpr (by norm_num)).map C

/-- **The Jacobian conjecture is false over `ℚ`.** Were `F` to admit a compositional inverse `G`,
then `bind₁ F (G i) = X i` for each `i`, and evaluating that identity at a point `p` would recover
`p` from `Fmap p`, making `Fmap` injective. It is not (`keller_not_injective`). -/
theorem not_jacobianConjecture : ¬ JacobianConjecture ℚ := by
  intro hJC
  -- Only the second conjunct is used: `F.comp G = id` is the one that inverts `F` on points.
  obtain ⟨G, -, hFG⟩ := hJC (Fin 3) F isUnit_jacobian_det
  have hcomp : ∀ i, bind₁ F (G i) = (X i : MvPolynomial (Fin 3) ℚ) := fun i => congrFun hFG i
  have key : ∀ p : Fin 3 → ℚ, (fun i => eval (Fmap p) (G i)) = p := by
    intro p
    funext i
    have h : aeval p (bind₁ F (G i)) = p i := by rw [hcomp i, aeval_X]
    rwa [aeval_bind₁] at h
  refine keller_not_injective fun p q hpq => ?_
  exact (key p).symm.trans (by rw [hpq]; exact key q)

end Statement

/-! ### The same counterexample over `ℂ` -/

/-- The coordinates of `F` pushed to `ℂ` coefficients via `algebraMap ℚ ℂ` and
`MvPolynomial.map`. -/
noncomputable def Fℂ : Fin 3 → MvPolynomial (Fin 3) ℂ := fun i => map (algebraMap ℚ ℂ) (F i)

/-- The induced evaluation map `ℂ³ → ℂ³`. -/
noncomputable def FmapC (p : Fin 3 → ℂ) : Fin 3 → ℂ := fun i => eval p (Fℂ i)

/-- `F(0, 0, -1/4) = (-1/4, 0, 0)` over `ℂ`. -/
theorem evalC_point0 : FmapC ![0, 0, -1/4] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [FmapC, Fℂ, F, P, Q, R]

/-- `F(1, -3/2, 13/2) = (-1/4, 0, 0)` over `ℂ`. -/
theorem evalC_point1 : FmapC ![1, -3/2, 13/2] = ![-1/4, 0, 0] := by
  funext i
  fin_cases i <;> simp [FmapC, Fℂ, F, P, Q, R] <;> norm_num

/-- The `ℂ`-map is not injective: the two distinct points `(0, 0, -1/4)` and `(1, -3/2, 13/2)` in
`ℂ³` share the image `(-1/4, 0, 0)`. This transfers the characteristic-zero counterexample to the
algebraically closed field `ℂ`. -/
theorem keller_not_injective_C : ¬ Function.Injective FmapC := by
  intro h
  have hEq : FmapC ![0, 0, -1/4] = FmapC ![1, -3/2, 13/2] := by
    rw [evalC_point0, evalC_point1]
  have hpts := h hEq
  have := congrFun hpts 0
  norm_num at this

end Counterexample.Keller
