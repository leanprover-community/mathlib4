/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
import Mathlib.Tactic.Qify
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DiophantineApproximation
import Mathlib.NumberTheory.Zsqrtd.Basic

#align_import number_theory.pell from "leanprover-community/mathlib"@"7ad820c4997738e2f542f8a20f32911f52020e26"

/-!
# Pell's Equation

*Pell's Equation* is the equation $x^2 - d y^2 = 1$, where $d$ is a positive integer
that is not a square, and one is interested in solutions in integers $x$ and $y$.

In this file, we aim at providing all of the essential theory of Pell's Equation for general $d$
(as opposed to the contents of `NumberTheory.PellMatiyasevic`, which is specific to the case
$d = a^2 - 1$ for some $a > 1$).

We begin by defining a type `Pell.Solution₁ d` for solutions of the equation,
show that it has a natural structure as an abelian group, and prove some basic
properties.

We then prove the following

**Theorem.** Let $d$ be a positive integer that is not a square. Then the equation
$x^2 - d y^2 = 1$ has a nontrivial (i.e., with $y \ne 0$) solution in integers.

See `Pell.exists_of_not_isSquare` and `Pell.Solution₁.exists_nontrivial_of_not_isSquare`.

We then define the *fundamental solution* to be the solution
with smallest $x$ among all solutions satisfying $x > 1$ and $y > 0$.
We show that every solution is a power (in the sense of the group structure mentioned above)
of the fundamental solution up to a (common) sign,
see `Pell.IsFundamental.eq_zpow_or_neg_zpow`, and that a (positive) solution has this property
if and only if it is fundamental, see `Pell.pos_generator_iff_fundamental`.

## References

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
   (Section 17.5)][IrelandRosen1990]

## Tags

Pell's equation

## TODO

* Extend to `x ^ 2 - d * y ^ 2 = -1` and further generalizations.
* Connect solutions to the continued fraction expansion of `√d`.
-/


namespace Pell

/-!
### Group structure of the solution set

We define a structure of a commutative multiplicative group with distributive negation
on the set of all solutions to the Pell equation `x^2 - d*y^2 = 1`.

The type of such solutions is `Pell.Solution₁ d`. It corresponds to a pair of integers `x` and `y`
and a proof that `(x, y)` is indeed a solution.

The multiplication is given by `(x, y) * (x', y') = (x*y' + d*y*y', x*y' + y*x')`.
This is obtained by mapping `(x, y)` to `x + y*√d` and multiplying the results.
In fact, we define `Pell.Solution₁ d` to be `↥(unitary (ℤ√d))` and transport
the "commutative group with distributive negation" structure from `↥(unitary (ℤ√d))`.

We then set up an API for `Pell.Solution₁ d`.
-/


open Zsqrtd

/-- An element of `ℤ√d` has norm one (i.e., `a.re^2 - d*a.im^2 = 1`) if and only if
it is contained in the submonoid of unitary elements.

TODO: merge this result with `Pell.isPell_iff_mem_unitary`. -/
theorem is_pell_solution_iff_mem_unitary {d : ℤ} {a : ℤ√d} :
    a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a ∈ unitary (ℤ√d) := by
  rw [← norm_eq_one_iff_mem_unitary, norm_def, sq, sq, ← mul_assoc]
  -- 🎉 no goals
#align pell.is_pell_solution_iff_mem_unitary Pell.is_pell_solution_iff_mem_unitary

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.
/-- `Pell.Solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 1`.
We define this in terms of elements of `ℤ√d` of norm one.
-/
def Solution₁ (d : ℤ) : Type :=
  ↥(unitary (ℤ√d))
#align pell.solution₁ Pell.Solution₁

namespace Solution₁

variable {d : ℤ}

-- Porting note(https://github.com/leanprover-community/mathlib4/issues/5020): manual deriving

instance instCommGroup : CommGroup (Solution₁ d) :=
  inferInstanceAs (CommGroup (unitary (ℤ√d)))
#align pell.solution₁.comm_group Pell.Solution₁.instCommGroup

instance instHasDistribNeg : HasDistribNeg (Solution₁ d) :=
  inferInstanceAs (HasDistribNeg (unitary (ℤ√d)))
#align pell.solution₁.has_distrib_neg Pell.Solution₁.instHasDistribNeg

instance instInhabited : Inhabited (Solution₁ d) :=
  inferInstanceAs (Inhabited (unitary (ℤ√d)))
#align pell.solution₁.inhabited Pell.Solution₁.instInhabited

instance : Coe (Solution₁ d) (ℤ√d) where coe := Subtype.val

/-- The `x` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def x (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).re
#align pell.solution₁.x Pell.Solution₁.x

/-- The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def y (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).im
#align pell.solution₁.y Pell.Solution₁.y

/-- The proof that `a` is a solution to the Pell equation `x^2 - d*y^2 = 1` -/
theorem prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
  is_pell_solution_iff_mem_unitary.mpr a.property
#align pell.solution₁.prop Pell.Solution₁.prop

/-- An alternative form of the equation, suitable for rewriting `x^2`. -/
theorem prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by rw [← a.prop]; ring
                                                                   -- ⊢ Solution₁.x a ^ 2 = Solution₁.x a ^ 2 - d * Solution₁.y a ^ 2 + d * Solution …
                                                                                  -- 🎉 no goals
#align pell.solution₁.prop_x Pell.Solution₁.prop_x

/-- An alternative form of the equation, suitable for rewriting `d * y^2`. -/
theorem prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by rw [← a.prop]; ring
                                                                   -- ⊢ d * Solution₁.y a ^ 2 = Solution₁.x a ^ 2 - (Solution₁.x a ^ 2 - d * Solutio …
                                                                                  -- 🎉 no goals
#align pell.solution₁.prop_y Pell.Solution₁.prop_y

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
theorem ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
  Subtype.ext <| ext.mpr ⟨hx, hy⟩
#align pell.solution₁.ext Pell.Solution₁.ext

/-- Construct a solution from `x`, `y` and a proof that the equation is satisfied. -/
def mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : Solution₁ d where
  val := ⟨x, y⟩
  property := is_pell_solution_iff_mem_unitary.mp prop
#align pell.solution₁.mk Pell.Solution₁.mk

@[simp]
theorem x_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x :=
  rfl
#align pell.solution₁.x_mk Pell.Solution₁.x_mk

@[simp]
theorem y_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y :=
  rfl
#align pell.solution₁.y_mk Pell.Solution₁.y_mk

@[simp]
theorem coe_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : ℤ√d) = ⟨x, y⟩ :=
  Zsqrtd.ext.mpr ⟨x_mk x y prop, y_mk x y prop⟩
#align pell.solution₁.coe_mk Pell.Solution₁.coe_mk

@[simp]
theorem x_one : (1 : Solution₁ d).x = 1 :=
  rfl
#align pell.solution₁.x_one Pell.Solution₁.x_one

@[simp]
theorem y_one : (1 : Solution₁ d).y = 0 :=
  rfl
#align pell.solution₁.y_one Pell.Solution₁.y_one

@[simp]
theorem x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) := by
  rw [← mul_assoc]
  -- ⊢ Solution₁.x (a * b) = Solution₁.x a * Solution₁.x b + d * Solution₁.y a * So …
  rfl
  -- 🎉 no goals
#align pell.solution₁.x_mul Pell.Solution₁.x_mul

@[simp]
theorem y_mul (a b : Solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x :=
  rfl
#align pell.solution₁.y_mul Pell.Solution₁.y_mul

@[simp]
theorem x_inv (a : Solution₁ d) : a⁻¹.x = a.x :=
  rfl
#align pell.solution₁.x_inv Pell.Solution₁.x_inv

@[simp]
theorem y_inv (a : Solution₁ d) : a⁻¹.y = -a.y :=
  rfl
#align pell.solution₁.y_inv Pell.Solution₁.y_inv

@[simp]
theorem x_neg (a : Solution₁ d) : (-a).x = -a.x :=
  rfl
#align pell.solution₁.x_neg Pell.Solution₁.x_neg

@[simp]
theorem y_neg (a : Solution₁ d) : (-a).y = -a.y :=
  rfl
#align pell.solution₁.y_neg Pell.Solution₁.y_neg

/-- When `d` is negative, then `x` or `y` must be zero in a solution. -/
theorem eq_zero_of_d_neg (h₀ : d < 0) (a : Solution₁ d) : a.x = 0 ∨ a.y = 0 := by
  have h := a.prop
  -- ⊢ Solution₁.x a = 0 ∨ Solution₁.y a = 0
  contrapose! h
  -- ⊢ Solution₁.x a ^ 2 - d * Solution₁.y a ^ 2 ≠ 1
  have h1 := sq_pos_of_ne_zero a.x h.1
  -- ⊢ Solution₁.x a ^ 2 - d * Solution₁.y a ^ 2 ≠ 1
  have h2 := sq_pos_of_ne_zero a.y h.2
  -- ⊢ Solution₁.x a ^ 2 - d * Solution₁.y a ^ 2 ≠ 1
  -- Porting note: added this to help `nlinarith`
  obtain ⟨d', rfl⟩ : ∃ d', d = -d' := ⟨-d, by exact Iff.mp neg_eq_iff_eq_neg rfl⟩
  -- ⊢ Solution₁.x a ^ 2 - -d' * Solution₁.y a ^ 2 ≠ 1
  nlinarith
  -- 🎉 no goals
#align pell.solution₁.eq_zero_of_d_neg Pell.Solution₁.eq_zero_of_d_neg

/-- A solution has `x ≠ 0`. -/
theorem x_ne_zero (h₀ : 0 ≤ d) (a : Solution₁ d) : a.x ≠ 0 := by
  intro hx
  -- ⊢ False
  have h : 0 ≤ d * a.y ^ 2 := mul_nonneg h₀ (sq_nonneg _)
  -- ⊢ False
  rw [a.prop_y, hx, sq, zero_mul, zero_sub] at h
  -- ⊢ False
  exact not_le.mpr (neg_one_lt_zero : (-1 : ℤ) < 0) h
  -- 🎉 no goals
#align pell.solution₁.x_ne_zero Pell.Solution₁.x_ne_zero

/-- A solution with `x > 1` must have `y ≠ 0`. -/
theorem y_ne_zero_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : a.y ≠ 0 := by
  intro hy
  -- ⊢ False
  have prop := a.prop
  -- ⊢ False
  rw [hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero] at prop
  -- ⊢ False
  exact lt_irrefl _ (((one_lt_sq_iff <| zero_le_one.trans ha.le).mpr ha).trans_eq prop)
  -- 🎉 no goals
#align pell.solution₁.y_ne_zero_of_one_lt_x Pell.Solution₁.y_ne_zero_of_one_lt_x

/-- If a solution has `x > 1`, then `d` is positive. -/
theorem d_pos_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : 0 < d := by
  refine' pos_of_mul_pos_left _ (sq_nonneg a.y)
  -- ⊢ 0 < d * Solution₁.y a ^ 2
  rw [a.prop_y, sub_pos]
  -- ⊢ 1 < Solution₁.x a ^ 2
  exact one_lt_pow ha two_ne_zero
  -- 🎉 no goals
#align pell.solution₁.d_pos_of_one_lt_x Pell.Solution₁.d_pos_of_one_lt_x

/-- If a solution has `x > 1`, then `d` is not a square. -/
theorem d_nonsquare_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : ¬IsSquare d := by
  have hp := a.prop
  -- ⊢ ¬IsSquare d
  rintro ⟨b, rfl⟩
  -- ⊢ False
  simp_rw [← sq, ← mul_pow, sq_sub_sq, Int.mul_eq_one_iff_eq_one_or_neg_one] at hp
  -- ⊢ False
  rcases hp with (⟨hp₁, hp₂⟩ | ⟨hp₁, hp₂⟩) <;> linarith [ha, hp₁, hp₂]
  -- ⊢ False
                                               -- 🎉 no goals
                                               -- 🎉 no goals
#align pell.solution₁.d_nonsquare_of_one_lt_x Pell.Solution₁.d_nonsquare_of_one_lt_x

/-- A solution with `x = 1` is trivial. -/
theorem eq_one_of_x_eq_one (h₀ : d ≠ 0) {a : Solution₁ d} (ha : a.x = 1) : a = 1 := by
  have prop := a.prop_y
  -- ⊢ a = 1
  rw [ha, one_pow, sub_self, mul_eq_zero, or_iff_right h₀, sq_eq_zero_iff] at prop
  -- ⊢ a = 1
  exact ext ha prop
  -- 🎉 no goals
#align pell.solution₁.eq_one_of_x_eq_one Pell.Solution₁.eq_one_of_x_eq_one

/-- A solution is `1` or `-1` if and only if `y = 0`. -/
theorem eq_one_or_neg_one_iff_y_eq_zero {a : Solution₁ d} : a = 1 ∨ a = -1 ↔ a.y = 0 := by
  refine' ⟨fun H => H.elim (fun h => by simp [h]) fun h => by simp [h], fun H => _⟩
  -- ⊢ a = 1 ∨ a = -1
  have prop := a.prop
  -- ⊢ a = 1 ∨ a = -1
  rw [H, sq (0 : ℤ), mul_zero, mul_zero, sub_zero, sq_eq_one_iff] at prop
  -- ⊢ a = 1 ∨ a = -1
  exact prop.imp (fun h => ext h H) fun h => ext h H
  -- 🎉 no goals
#align pell.solution₁.eq_one_or_neg_one_iff_y_eq_zero Pell.Solution₁.eq_one_or_neg_one_iff_y_eq_zero

/-- The set of solutions with `x > 0` is closed under multiplication. -/
theorem x_mul_pos {a b : Solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x) : 0 < (a * b).x := by
  simp only [x_mul]
  -- ⊢ 0 < Solution₁.x a * Solution₁.x b + d * (Solution₁.y a * Solution₁.y b)
  refine' neg_lt_iff_pos_add'.mp (abs_lt.mp _).1
  -- ⊢ |d * (Solution₁.y a * Solution₁.y b)| < Solution₁.x a * Solution₁.x b
  rw [← abs_of_pos ha, ← abs_of_pos hb, ← abs_mul, ← sq_lt_sq, mul_pow a.x, a.prop_x, b.prop_x, ←
    sub_pos]
  ring_nf
  -- ⊢ 0 < 1 + d * Solution₁.y a ^ 2 + d * Solution₁.y b ^ 2
  cases' le_or_lt 0 d with h h
  -- ⊢ 0 < 1 + d * Solution₁.y a ^ 2 + d * Solution₁.y b ^ 2
  · positivity
    -- 🎉 no goals
  · rw [(eq_zero_of_d_neg h a).resolve_left ha.ne', (eq_zero_of_d_neg h b).resolve_left hb.ne']
    -- ⊢ 0 < 1 + d * 0 ^ 2 + d * 0 ^ 2
    -- Porting note: was
    -- rw [zero_pow two_pos, zero_add, zero_mul, zero_add]
    -- exact one_pos
    -- but this relied on the exact output of `ring_nf`
    simp
    -- 🎉 no goals
#align pell.solution₁.x_mul_pos Pell.Solution₁.x_mul_pos

/-- The set of solutions with `x` and `y` positive is closed under multiplication. -/
theorem y_mul_pos {a b : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x)
    (hby : 0 < b.y) : 0 < (a * b).y := by
  simp only [y_mul]
  -- ⊢ 0 < Solution₁.x a * Solution₁.y b + Solution₁.y a * Solution₁.x b
  positivity
  -- 🎉 no goals
#align pell.solution₁.y_mul_pos Pell.Solution₁.y_mul_pos

/-- If `(x, y)` is a solution with `x` positive, then all its powers with natural exponents
have positive `x`. -/
theorem x_pow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : ℕ) : 0 < (a ^ n).x := by
  induction' n with n ih
  -- ⊢ 0 < Solution₁.x (a ^ Nat.zero)
  · simp only [Nat.zero_eq, pow_zero, x_one, zero_lt_one]
    -- 🎉 no goals
  · rw [pow_succ]
    -- ⊢ 0 < Solution₁.x (a * a ^ n)
    exact x_mul_pos hax ih
    -- 🎉 no goals
#align pell.solution₁.x_pow_pos Pell.Solution₁.x_pow_pos

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
natural exponents have positive `y`. -/
theorem y_pow_succ_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : ℕ) :
    0 < (a ^ n.succ).y := by
  induction' n with n ih
  -- ⊢ 0 < Solution₁.y (a ^ Nat.succ Nat.zero)
  · simp only [Nat.zero_eq, ← Nat.one_eq_succ_zero, hay, pow_one]
    -- 🎉 no goals
  · rw [pow_succ]
    -- ⊢ 0 < Solution₁.y (a * a ^ (n + 1))
    exact y_mul_pos hax hay (x_pow_pos hax _) ih
    -- 🎉 no goals
#align pell.solution₁.y_pow_succ_pos Pell.Solution₁.y_pow_succ_pos

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
exponents have positive `y`. -/
theorem y_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : ℤ} (hn : 0 < n) :
    0 < (a ^ n).y := by
  lift n to ℕ using hn.le
  -- ⊢ 0 < Solution₁.y (a ^ ↑n)
  norm_cast at hn ⊢
  -- ⊢ 0 < Solution₁.y (a ^ n)
  rw [← Nat.succ_pred_eq_of_pos hn]
  -- ⊢ 0 < Solution₁.y (a ^ Nat.succ (Nat.pred n))
  exact y_pow_succ_pos hax hay _
  -- 🎉 no goals
#align pell.solution₁.y_zpow_pos Pell.Solution₁.y_zpow_pos

/-- If `(x, y)` is a solution with `x` positive, then all its powers have positive `x`. -/
theorem x_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : ℤ) : 0 < (a ^ n).x := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_coe, zpow_ofNat]
    exact x_pow_pos hax n
  | negSucc n =>
    rw [zpow_negSucc]
    exact x_pow_pos hax (n + 1)
#align pell.solution₁.x_zpow_pos Pell.Solution₁.x_zpow_pos

/-- If `(x, y)` is a solution with `x` and `y` positive, then the `y` component of any power
has the same sign as the exponent. -/
theorem sign_y_zpow_eq_sign_of_x_pos_of_y_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
    (n : ℤ) : (a ^ n).y.sign = n.sign := by
  rcases n with ((_ | n) | n)
  · rfl
    -- 🎉 no goals
  · rw [Int.ofNat_eq_coe, zpow_ofNat]
    -- ⊢ Int.sign (Solution₁.y (a ^ Nat.succ n)) = Int.sign ↑(Nat.succ n)
    exact Int.sign_eq_one_of_pos (y_pow_succ_pos hax hay n)
    -- 🎉 no goals
  · rw [zpow_negSucc]
    -- ⊢ Int.sign (Solution₁.y (a ^ (n + 1))⁻¹) = Int.sign (Int.negSucc n)
    exact Int.sign_eq_neg_one_of_neg (neg_neg_of_pos (y_pow_succ_pos hax hay n))
    -- 🎉 no goals
#align pell.solution₁.sign_y_zpow_eq_sign_of_x_pos_of_y_pos Pell.Solution₁.sign_y_zpow_eq_sign_of_x_pos_of_y_pos

/-- If `a` is any solution, then one of `a`, `a⁻¹`, `-a`, `-a⁻¹` has
positive `x` and nonnegative `y`. -/
theorem exists_pos_variant (h₀ : 0 < d) (a : Solution₁ d) :
    ∃ b : Solution₁ d, 0 < b.x ∧ 0 ≤ b.y ∧ a ∈ ({b, b⁻¹, -b, -b⁻¹} : Set (Solution₁ d)) := by
  refine'
        (lt_or_gt_of_ne (a.x_ne_zero h₀.le)).elim
          ((le_total 0 a.y).elim (fun hy hx => ⟨-a⁻¹, _, _, _⟩) fun hy hx => ⟨-a, _, _, _⟩)
          ((le_total 0 a.y).elim (fun hy hx => ⟨a, hx, hy, _⟩) fun hy hx => ⟨a⁻¹, hx, _, _⟩) <;>
      simp only [neg_neg, inv_inv, neg_inv, Set.mem_insert_iff, Set.mem_singleton_iff, true_or_iff,
        eq_self_iff_true, x_neg, x_inv, y_neg, y_inv, neg_pos, neg_nonneg, or_true_iff] <;>
    assumption
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
    -- 🎉 no goals
#align pell.solution₁.exists_pos_variant Pell.Solution₁.exists_pos_variant

end Solution₁

section Existence

/-!
### Existence of nontrivial solutions
-/


variable {d : ℤ}

open Set Real

/-- If `d` is a positive integer that is not a square, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0 := by
  let ξ : ℝ := sqrt d
  -- ⊢ ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0
  have hξ : Irrational ξ := by
    refine' irrational_nrt_of_notint_nrt 2 d (sq_sqrt <| Int.cast_nonneg.mpr h₀.le) _ two_pos
    rintro ⟨x, hx⟩
    refine' hd ⟨x, @Int.cast_injective ℝ _ _ d (x * x) _⟩
    rw [← sq_sqrt <| Int.cast_nonneg.mpr h₀.le, Int.cast_mul, ← hx, sq]
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1)
  -- ⊢ ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0
  have hM : {q : ℚ | |q.1 ^ 2 - d * (q.2 : ℤ) ^ 2| < M}.Infinite := by
    refine' Infinite.mono (fun q h => _) (infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ)
    have h0 : 0 < (q.2 : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr q.pos) 2
    have h1 : (q.num : ℝ) / (q.den : ℝ) = q := by exact_mod_cast q.num_div_den
    rw [mem_setOf, abs_sub_comm, ← @Int.cast_lt ℝ, ← div_lt_div_right (abs_pos_of_pos h0)]
    push_cast
    rw [← abs_div, abs_sq, sub_div, mul_div_cancel _ h0.ne', ← div_pow, h1, ←
      sq_sqrt (Int.cast_pos.mpr h₀).le, sq_sub_sq, abs_mul, ← mul_one_div]
    refine' mul_lt_mul'' (((abs_add ξ q).trans _).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _)
    rw [two_mul, add_assoc, add_le_add_iff_left, ← sub_le_iff_le_add']
    rw [mem_setOf, abs_sub_comm] at h
    refine' (abs_sub_abs_le_abs_sub (q : ℝ) ξ).trans (h.le.trans _)
    rw [div_le_one h0, one_le_sq_iff_one_le_abs, Nat.abs_cast, Nat.one_le_cast]
    exact q.pos
  obtain ⟨m, hm⟩ : ∃ m : ℤ, {q : ℚ | q.1 ^ 2 - d * (q.den : ℤ) ^ 2 = m}.Infinite := by
    contrapose! hM
    simp only [not_infinite] at hM ⊢
    refine' (congr_arg _ (ext fun x => _)).mp (Finite.biUnion (finite_Ioo (-M) M) fun m _ => hM m)
    simp only [abs_lt, mem_setOf, mem_Ioo, mem_iUnion, exists_prop, exists_eq_right']
  have hm₀ : m ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hm.nonempty
    rw [mem_setOf, sub_eq_zero, mul_comm] at hq
    obtain ⟨a, ha⟩ := (Int.pow_dvd_pow_iff two_pos).mp ⟨d, hq⟩
    rw [ha, mul_pow, mul_right_inj' (pow_pos (Int.coe_nat_pos.mpr q.pos) 2).ne'] at hq
    exact hd ⟨a, sq a ▸ hq.symm⟩
  haveI := neZero_iff.mpr (Int.natAbs_ne_zero.mpr hm₀)
  -- ⊢ ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0
  let f : ℚ → ZMod m.natAbs × ZMod m.natAbs := fun q => (q.num, q.den)
  -- ⊢ ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0
  obtain ⟨q₁, h₁ : q₁.num ^ 2 - d * (q₁.den : ℤ) ^ 2 = m,
      q₂, h₂ : q₂.num ^ 2 - d * (q₂.den : ℤ) ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_mapsTo (mapsTo_univ f _) finite_univ
  obtain ⟨hq1 : (q₁.num : ZMod m.natAbs) = q₂.num, hq2 : (q₁.den : ZMod m.natAbs) = q₂.den⟩ :=
    Prod.ext_iff.mp hqf
  have hd₁ : m ∣ q₁.num * q₂.num - d * (q₁.den * q₂.den) := by
    rw [← Int.natAbs_dvd, ← ZMod.int_cast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq1, hq2, ← sq, ← sq]
    norm_cast
    rw [ZMod.int_cast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd, Nat.cast_pow, ← h₂]
  have hd₂ : m ∣ q₁.num * q₂.den - q₂.num * q₁.den := by
    rw [← Int.natAbs_dvd, ← ZMod.int_cast_eq_int_cast_iff_dvd_sub]
    push_cast
    rw [hq1, hq2]
  replace hm₀ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm₀
  -- ⊢ ∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0
  refine' ⟨(q₁.num * q₂.num - d * (q₁.den * q₂.den)) / m, (q₁.num * q₂.den - q₂.num * q₁.den) / m,
      _, _⟩
  · qify [hd₁, hd₂]
    -- ⊢ ((↑q₁.num * ↑q₂.num - ↑d * (↑q₁.den * ↑q₂.den)) / ↑m) ^ 2 - ↑d * ((↑q₁.num * …
    field_simp [hm₀]
    -- ⊢ (↑q₁.num * ↑q₂.num - ↑d * (↑q₁.den * ↑q₂.den)) ^ 2 - ↑d * (↑q₁.num * ↑q₂.den …
    norm_cast
    -- ⊢ (q₁.num * q₂.num - d * ↑(q₁.den * q₂.den)) ^ 2 - d * (q₁.num * ↑q₂.den - q₂. …
    conv_rhs =>
      rw [sq]
      congr
      · rw [← h₁]
      · rw [← h₂]
    push_cast
    -- ⊢ (q₁.num * q₂.num - d * (↑q₁.den * ↑q₂.den)) ^ 2 - d * (q₁.num * ↑q₂.den - q₂ …
    ring
    -- 🎉 no goals
  · qify [hd₂]
    -- ⊢ (↑q₁.num * ↑q₂.den - ↑q₂.num * ↑q₁.den) / ↑m ≠ 0
    refine' div_ne_zero_iff.mpr ⟨_, hm₀⟩
    -- ⊢ ↑q₁.num * ↑q₂.den - ↑q₂.num * ↑q₁.den ≠ 0
    exact_mod_cast mt sub_eq_zero.mp (mt Rat.eq_iff_mul_eq_mul.mpr hne)
    -- 🎉 no goals
#align pell.exists_of_not_is_square Pell.exists_of_not_isSquare

/-- If `d` is a positive integer, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1` if and only if `d` is not a square. -/
theorem exists_iff_not_isSquare (h₀ : 0 < d) :
    (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) ↔ ¬IsSquare d := by
  refine' ⟨_, exists_of_not_isSquare h₀⟩
  -- ⊢ (∃ x y, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) → ¬IsSquare d
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  -- ⊢ False
  rw [← sq, ← mul_pow, sq_sub_sq] at hxy
  -- ⊢ False
  simpa [hy, mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy
  -- 🎉 no goals
#align pell.exists_iff_not_is_square Pell.exists_iff_not_isSquare

namespace Solution₁

/-- If `d` is a positive integer that is not a square, then there exists a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_nontrivial_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, a ≠ 1 ∧ a ≠ -1 := by
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_isSquare h₀ hd
  -- ⊢ ∃ a, a ≠ 1 ∧ a ≠ -1
  refine' ⟨mk x y prop, fun H => _, fun H => _⟩ <;> apply_fun Solution₁.y at H <;>
  -- ⊢ False
                                                    -- ⊢ False
                                                    -- ⊢ False
    simp [hy] at H
    -- 🎉 no goals
    -- 🎉 no goals
#align pell.solution₁.exists_nontrivial_of_not_is_square Pell.Solution₁.exists_nontrivial_of_not_isSquare

/-- If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`. -/
theorem exists_pos_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, 1 < a.x ∧ 0 < a.y := by
  obtain ⟨x, y, h, hy⟩ := exists_of_not_isSquare h₀ hd
  -- ⊢ ∃ a, 1 < Solution₁.x a ∧ 0 < Solution₁.y a
  refine' ⟨mk |x| |y| (by rwa [sq_abs, sq_abs]), _, abs_pos.mpr hy⟩
  -- ⊢ 1 < Solution₁.x (mk |x| |y| (_ : |x| ^ 2 - d * |y| ^ 2 = 1))
  rw [x_mk, ← one_lt_sq_iff_one_lt_abs, eq_add_of_sub_eq h, lt_add_iff_pos_right]
  -- ⊢ 0 < d * y ^ 2
  exact mul_pos h₀ (sq_pos_of_ne_zero y hy)
  -- 🎉 no goals
#align pell.solution₁.exists_pos_of_not_is_square Pell.Solution₁.exists_pos_of_not_isSquare

end Solution₁

end Existence

/-! ### Fundamental solutions

We define the notion of a *fundamental solution* of Pell's equation and
show that it exists and is unique (when `d` is positive and non-square)
and generates the group of solutions up to sign.
-/


variable {d : ℤ}

/-- We define a solution to be *fundamental* if it has `x > 1` and `y > 0`
and its `x` is the smallest possible among solutions with `x > 1`. -/
def IsFundamental (a : Solution₁ d) : Prop :=
  1 < a.x ∧ 0 < a.y ∧ ∀ {b : Solution₁ d}, 1 < b.x → a.x ≤ b.x
#align pell.is_fundamental Pell.IsFundamental

namespace IsFundamental

open Solution₁

/-- A fundamental solution has positive `x`. -/
theorem x_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < a.x :=
  zero_lt_one.trans h.1
#align pell.is_fundamental.x_pos Pell.IsFundamental.x_pos

/-- If a fundamental solution exists, then `d` must be positive. -/
theorem d_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < d :=
  d_pos_of_one_lt_x h.1
#align pell.is_fundamental.d_pos Pell.IsFundamental.d_pos

/-- If a fundamental solution exists, then `d` must be a non-square. -/
theorem d_nonsquare {a : Solution₁ d} (h : IsFundamental a) : ¬IsSquare d :=
  d_nonsquare_of_one_lt_x h.1
#align pell.is_fundamental.d_nonsquare Pell.IsFundamental.d_nonsquare

/-- If there is a fundamental solution, it is unique. -/
theorem subsingleton {a b : Solution₁ d} (ha : IsFundamental a) (hb : IsFundamental b) : a = b := by
  have hx := le_antisymm (ha.2.2 hb.1) (hb.2.2 ha.1)
  -- ⊢ a = b
  refine' Solution₁.ext hx _
  -- ⊢ Solution₁.y a = Solution₁.y b
  have : d * a.y ^ 2 = d * b.y ^ 2 := by rw [a.prop_y, b.prop_y, hx]
  -- ⊢ Solution₁.y a = Solution₁.y b
  exact (sq_eq_sq ha.2.1.le hb.2.1.le).mp (Int.eq_of_mul_eq_mul_left ha.d_pos.ne' this)
  -- 🎉 no goals
#align pell.is_fundamental.subsingleton Pell.IsFundamental.subsingleton

/-- If `d` is positive and not a square, then a fundamental solution exists. -/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, IsFundamental a := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_pos_of_not_isSquare h₀ hd
  -- ⊢ ∃ a, IsFundamental a
  -- convert to `x : ℕ` to be able to use `Nat.find`
  have P : ∃ x' : ℕ, 1 < x' ∧ ∃ y' : ℤ, 0 < y' ∧ (x' : ℤ) ^ 2 - d * y' ^ 2 = 1 := by
    have hax := a.prop
    lift a.x to ℕ using by positivity with ax
    norm_cast at ha₁
    exact ⟨ax, ha₁, a.y, ha₂, hax⟩
  classical
  -- to avoid having to show that the predicate is decidable
  let x₁ := Nat.find P
  obtain ⟨hx, y₁, hy₀, hy₁⟩ := Nat.find_spec P
  refine' ⟨mk x₁ y₁ hy₁, by rw [x_mk]; exact_mod_cast hx, hy₀, fun {b} hb => _⟩
  rw [x_mk]
  have hb' := (Int.toNat_of_nonneg <| zero_le_one.trans hb.le).symm
  have hb'' := hb
  rw [hb'] at hb ⊢
  norm_cast at hb ⊢
  refine' Nat.find_min' P ⟨hb, |b.y|, abs_pos.mpr <| y_ne_zero_of_one_lt_x hb'', _⟩
  rw [← hb', sq_abs]
  exact b.prop
#align pell.is_fundamental.exists_of_not_is_square Pell.IsFundamental.exists_of_not_isSquare

/-- The map sending an integer `n` to the `y`-coordinate of `a^n` for a fundamental
solution `a` is stritcly increasing. -/
theorem y_strictMono {a : Solution₁ d} (h : IsFundamental a) :
    StrictMono fun n : ℤ => (a ^ n).y := by
  have H : ∀ n : ℤ, 0 ≤ n → (a ^ n).y < (a ^ (n + 1)).y := by
    intro n hn
    rw [← sub_pos, zpow_add, zpow_one, y_mul, add_sub_assoc]
    rw [show (a ^ n).y * a.x - (a ^ n).y = (a ^ n).y * (a.x - 1) by ring]
    refine'
      add_pos_of_pos_of_nonneg (mul_pos (x_zpow_pos h.x_pos _) h.2.1)
        (mul_nonneg _ (by rw [sub_nonneg]; exact h.1.le))
    rcases hn.eq_or_lt with (rfl | hn)
    · simp only [zpow_zero, y_one]
    · exact (y_zpow_pos h.x_pos h.2.1 hn).le
  refine' strictMono_int_of_lt_succ fun n => _
  -- ⊢ Solution₁.y (a ^ n) < Solution₁.y (a ^ (n + 1))
  cases' le_or_lt 0 n with hn hn
  -- ⊢ Solution₁.y (a ^ n) < Solution₁.y (a ^ (n + 1))
  · exact H n hn
    -- 🎉 no goals
  · let m : ℤ := -n - 1
    -- ⊢ Solution₁.y (a ^ n) < Solution₁.y (a ^ (n + 1))
    have hm : n = -m - 1 := by simp only [neg_sub, sub_neg_eq_add, add_tsub_cancel_left]
    -- ⊢ Solution₁.y (a ^ n) < Solution₁.y (a ^ (n + 1))
    rw [hm, sub_add_cancel, ← neg_add', zpow_neg, zpow_neg, y_inv, y_inv, neg_lt_neg_iff]
    -- ⊢ Solution₁.y (a ^ m) < Solution₁.y (a ^ (m + 1))
    exact H _ (by linarith [hn])
    -- 🎉 no goals
#align pell.is_fundamental.y_strict_mono Pell.IsFundamental.y_strictMono

/-- If `a` is a fundamental solution, then `(a^m).y < (a^n).y` if and only if `m < n`. -/
theorem zpow_y_lt_iff_lt {a : Solution₁ d} (h : IsFundamental a) (m n : ℤ) :
    (a ^ m).y < (a ^ n).y ↔ m < n := by
  refine' ⟨fun H => _, fun H => h.y_strictMono H⟩
  -- ⊢ m < n
  contrapose! H
  -- ⊢ Solution₁.y (a ^ n) ≤ Solution₁.y (a ^ m)
  exact h.y_strictMono.monotone H
  -- 🎉 no goals
#align pell.is_fundamental.zpow_y_lt_iff_lt Pell.IsFundamental.zpow_y_lt_iff_lt

/-- The `n`th power of a fundamental solution is trivial if and only if `n = 0`. -/
theorem zpow_eq_one_iff {a : Solution₁ d} (h : IsFundamental a) (n : ℤ) : a ^ n = 1 ↔ n = 0 := by
  rw [← zpow_zero a]
  -- ⊢ a ^ n = a ^ 0 ↔ n = 0
  exact ⟨fun H => h.y_strictMono.injective (congr_arg Solution₁.y H), fun H => H ▸ rfl⟩
  -- 🎉 no goals
#align pell.is_fundamental.zpow_eq_one_iff Pell.IsFundamental.zpow_eq_one_iff

/-- A power of a fundamental solution is never equal to the negative of a power of this
fundamental solution. -/
theorem zpow_ne_neg_zpow {a : Solution₁ d} (h : IsFundamental a) {n n' : ℤ} : a ^ n ≠ -a ^ n' := by
  intro hf
  -- ⊢ False
  apply_fun Solution₁.x at hf
  -- ⊢ False
  have H := x_zpow_pos h.x_pos n
  -- ⊢ False
  rw [hf, x_neg, lt_neg, neg_zero] at H
  -- ⊢ False
  exact lt_irrefl _ ((x_zpow_pos h.x_pos n').trans H)
  -- 🎉 no goals
#align pell.is_fundamental.zpow_ne_neg_zpow Pell.IsFundamental.zpow_ne_neg_zpow

/-- The `x`-coordinate of a fundamental solution is a lower bound for the `x`-coordinate
of any positive solution. -/
theorem x_le_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x) :
    a₁.x ≤ a.x :=
  h.2.2 hax
#align pell.is_fundamental.x_le_x Pell.IsFundamental.x_le_x

/-- The `y`-coordinate of a fundamental solution is a lower bound for the `y`-coordinate
of any positive solution. -/
theorem y_le_y {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : a₁.y ≤ a.y := by
  have H : d * (a₁.y ^ 2 - a.y ^ 2) = a₁.x ^ 2 - a.x ^ 2 := by rw [a.prop_x, a₁.prop_x]; ring
  -- ⊢ Solution₁.y a₁ ≤ Solution₁.y a
  rw [← abs_of_pos hay, ← abs_of_pos h.2.1, ← sq_le_sq, ← mul_le_mul_left h.d_pos, ← sub_nonpos, ←
    mul_sub, H, sub_nonpos, sq_le_sq, abs_of_pos (zero_lt_one.trans h.1),
    abs_of_pos (zero_lt_one.trans hax)]
  exact h.x_le_x hax
  -- 🎉 no goals
#align pell.is_fundamental.y_le_y Pell.IsFundamental.y_le_y

-- helper lemma for the next three results
theorem x_mul_y_le_y_mul_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d}
    (hax : 1 < a.x) (hay : 0 < a.y) : a.x * a₁.y ≤ a.y * a₁.x := by
  rw [← abs_of_pos <| zero_lt_one.trans hax, ← abs_of_pos hay, ← abs_of_pos h.x_pos, ←
    abs_of_pos h.2.1, ← abs_mul, ← abs_mul, ← sq_le_sq, mul_pow, mul_pow, a.prop_x, a₁.prop_x, ←
    sub_nonneg]
  ring_nf
  -- ⊢ 0 ≤ Solution₁.y a ^ 2 - Solution₁.y a₁ ^ 2
  rw [sub_nonneg, sq_le_sq, abs_of_pos hay, abs_of_pos h.2.1]
  -- ⊢ Solution₁.y a₁ ≤ Solution₁.y a
  exact h.y_le_y hax hay
  -- 🎉 no goals
#align pell.is_fundamental.x_mul_y_le_y_mul_x Pell.IsFundamental.x_mul_y_le_y_mul_x

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `y`-coordinate remains nonnegative. -/
theorem mul_inv_y_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 ≤ (a * a₁⁻¹).y := by
  simpa only [y_inv, mul_neg, y_mul, le_neg_add_iff_add_le, add_zero] using
    h.x_mul_y_le_y_mul_x hax hay
#align pell.is_fundamental.mul_inv_y_nonneg Pell.IsFundamental.mul_inv_y_nonneg

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate stays positive. -/
theorem mul_inv_x_pos {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 < (a * a₁⁻¹).x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, lt_add_neg_iff_add_lt, zero_add]
  -- ⊢ d * (Solution₁.y a * Solution₁.y a₁) < Solution₁.x a * Solution₁.x a₁
  refine' (mul_lt_mul_left <| zero_lt_one.trans hax).mp _
  -- ⊢ Solution₁.x a * (d * (Solution₁.y a * Solution₁.y a₁)) < Solution₁.x a * (So …
  rw [(by ring : a.x * (d * (a.y * a₁.y)) = d * a.y * (a.x * a₁.y))]
  -- ⊢ d * Solution₁.y a * (Solution₁.x a * Solution₁.y a₁) < Solution₁.x a * (Solu …
  refine' ((mul_le_mul_left <| mul_pos h.d_pos hay).mpr <| x_mul_y_le_y_mul_x h hax hay).trans_lt _
  -- ⊢ d * Solution₁.y a * (Solution₁.y a * Solution₁.x a₁) < Solution₁.x a * (Solu …
  rw [← mul_assoc, mul_assoc d, ← sq, a.prop_y, ← sub_pos]
  -- ⊢ 0 < Solution₁.x a * (Solution₁.x a * Solution₁.x a₁) - (Solution₁.x a ^ 2 -  …
  ring_nf
  -- ⊢ 0 < Solution₁.x a₁
  exact zero_lt_one.trans h.1
  -- 🎉 no goals
#align pell.is_fundamental.mul_inv_x_pos Pell.IsFundamental.mul_inv_x_pos

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate decreases. -/
theorem mul_inv_x_lt_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : (a * a₁⁻¹).x < a.x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, add_neg_lt_iff_le_add']
  -- ⊢ Solution₁.x a * Solution₁.x a₁ < d * (Solution₁.y a * Solution₁.y a₁) + Solu …
  refine' (mul_lt_mul_left h.2.1).mp _
  -- ⊢ Solution₁.y a₁ * (Solution₁.x a * Solution₁.x a₁) < Solution₁.y a₁ * (d * (S …
  rw [(by ring : a₁.y * (a.x * a₁.x) = a.x * a₁.y * a₁.x)]
  -- ⊢ Solution₁.x a * Solution₁.y a₁ * Solution₁.x a₁ < Solution₁.y a₁ * (d * (Sol …
  refine'
    ((mul_le_mul_right <| zero_lt_one.trans h.1).mpr <| x_mul_y_le_y_mul_x h hax hay).trans_lt _
  rw [mul_assoc, ← sq, a₁.prop_x, ← sub_neg]
  -- ⊢ Solution₁.y a * (1 + d * Solution₁.y a₁ ^ 2) - Solution₁.y a₁ * (d * (Soluti …
  -- Porting note: was `ring_nf`
  suffices a.y - a.x * a₁.y < 0 by convert this using 1; ring
  -- ⊢ Solution₁.y a - Solution₁.x a * Solution₁.y a₁ < 0
  rw [sub_neg, ← abs_of_pos hay, ← abs_of_pos h.2.1, ← abs_of_pos <| zero_lt_one.trans hax, ←
    abs_mul, ← sq_lt_sq, mul_pow, a.prop_x]
  calc
    a.y ^ 2 = 1 * a.y ^ 2 := (one_mul _).symm
    _ ≤ d * a.y ^ 2 := ((mul_le_mul_right <| sq_pos_of_pos hay).mpr h.d_pos)
    _ < d * a.y ^ 2 + 1 := (lt_add_one _)
    _ = (1 + d * a.y ^ 2) * 1 := by rw [add_comm, mul_one]
    _ ≤ (1 + d * a.y ^ 2) * a₁.y ^ 2 :=
      (mul_le_mul_left (by have := h.d_pos; positivity)).mpr (sq_pos_of_pos h.2.1)
#align pell.is_fundamental.mul_inv_x_lt_x Pell.IsFundamental.mul_inv_x_lt_x

/-- Any nonnegative solution is a power with nonnegative exponent of a fundamental solution. -/
theorem eq_pow_of_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 0 < a.x)
    (hay : 0 ≤ a.y) : ∃ n : ℕ, a = a₁ ^ n := by
  lift a.x to ℕ using hax.le with ax hax'
  -- ⊢ ∃ n, a = a₁ ^ n
  -- Porting note: added
  clear hax
  -- ⊢ ∃ n, a = a₁ ^ n
  induction' ax using Nat.strong_induction_on with x ih generalizing a
  -- ⊢ ∃ n, a = a₁ ^ n
  cases' hay.eq_or_lt with hy hy
  -- ⊢ ∃ n, a = a₁ ^ n
  · -- case 1: `a = 1`
    refine' ⟨0, _⟩
    -- ⊢ a = a₁ ^ 0
    simp only [pow_zero]
    -- ⊢ a = 1
    ext <;> simp only [x_one, y_one]
    -- ⊢ Solution₁.x a = Solution₁.x 1
            -- ⊢ Solution₁.x a = 1
            -- ⊢ Solution₁.y a = 0
    · have prop := a.prop
      -- ⊢ Solution₁.x a = 1
      rw [← hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero,
        sq_eq_one_iff] at prop
      refine' prop.resolve_right fun hf => _
      -- ⊢ False
      have := (hax.trans_eq hax').le.trans_eq hf
      -- ⊢ False
      norm_num at this
      -- 🎉 no goals
    · exact hy.symm
      -- 🎉 no goals
  · -- case 2: `a ≥ a₁`
    have hx₁ : 1 < a.x := by nlinarith [a.prop, h.d_pos]
    -- ⊢ ∃ n, a = a₁ ^ n
    have hxx₁ := h.mul_inv_x_pos hx₁ hy
    -- ⊢ ∃ n, a = a₁ ^ n
    have hxx₂ := h.mul_inv_x_lt_x hx₁ hy
    -- ⊢ ∃ n, a = a₁ ^ n
    have hyy := h.mul_inv_y_nonneg hx₁ hy
    -- ⊢ ∃ n, a = a₁ ^ n
    lift (a * a₁⁻¹).x to ℕ using hxx₁.le with x' hx'
    -- ⊢ ∃ n, a = a₁ ^ n
    -- Porting note: `ih` has its arguments in a different order compared to lean 3.
    obtain ⟨n, hn⟩ := ih x' (by exact_mod_cast hxx₂.trans_eq hax'.symm) hyy hx' hxx₁
    -- ⊢ ∃ n, a = a₁ ^ n
    exact ⟨n + 1, by rw [pow_succ, ← hn, mul_comm a, ← mul_assoc, mul_inv_self, one_mul]⟩
    -- 🎉 no goals
#align pell.is_fundamental.eq_pow_of_nonneg Pell.IsFundamental.eq_pow_of_nonneg

/-- Every solution is, up to a sign, a power of a given fundamental solution. -/
theorem eq_zpow_or_neg_zpow {a₁ : Solution₁ d} (h : IsFundamental a₁) (a : Solution₁ d) :
    ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨b, hbx, hby, hb⟩ := exists_pos_variant h.d_pos a
  -- ⊢ ∃ n, a = a₁ ^ n ∨ a = -a₁ ^ n
  obtain ⟨n, hn⟩ := h.eq_pow_of_nonneg hbx hby
  -- ⊢ ∃ n, a = a₁ ^ n ∨ a = -a₁ ^ n
  rcases hb with (rfl | rfl | rfl | hb)
  · exact ⟨n, Or.inl (by exact_mod_cast hn)⟩
    -- 🎉 no goals
  · exact ⟨-n, Or.inl (by simp [hn])⟩
    -- 🎉 no goals
  · exact ⟨n, Or.inr (by simp [hn])⟩
    -- 🎉 no goals
  · rw [Set.mem_singleton_iff] at hb
    -- ⊢ ∃ n, a = a₁ ^ n ∨ a = -a₁ ^ n
    rw [hb]
    -- ⊢ ∃ n, -b⁻¹ = a₁ ^ n ∨ -b⁻¹ = -a₁ ^ n
    exact ⟨-n, Or.inr (by simp [hn])⟩
    -- 🎉 no goals
#align pell.is_fundamental.eq_zpow_or_neg_zpow Pell.IsFundamental.eq_zpow_or_neg_zpow

end IsFundamental

open Solution₁ IsFundamental

/-- When `d` is positive and not a square, then the group of solutions to the Pell equation
`x^2 - d*y^2 = 1` has a unique positive generator (up to sign). -/
theorem existsUnique_pos_generator (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃! a₁ : Solution₁ d,
      1 < a₁.x ∧ 0 < a₁.y ∧ ∀ a : Solution₁ d, ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  -- ⊢ ∃! a₁, 1 < Solution₁.x a₁ ∧ 0 < Solution₁.y a₁ ∧ ∀ (a : Solution₁ d), ∃ n, a …
  refine' ⟨a₁, ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩, fun a (H : 1 < _ ∧ _) => _⟩
  -- ⊢ a = a₁
  obtain ⟨Hx, Hy, H⟩ := H
  -- ⊢ a = a₁
  obtain ⟨n₁, hn₁⟩ := H a₁
  -- ⊢ a = a₁
  obtain ⟨n₂, hn₂⟩ := ha₁.eq_zpow_or_neg_zpow a
  -- ⊢ a = a₁
  rcases hn₂ with (rfl | rfl)
  -- ⊢ a₁ ^ n₂ = a₁
  · rw [← zpow_mul, eq_comm, @eq_comm _ a₁, ← mul_inv_eq_one, ← @mul_inv_eq_one _ _ _ a₁, ←
      zpow_neg_one, neg_mul, ← zpow_add, ← sub_eq_add_neg] at hn₁
    cases' hn₁ with hn₁ hn₁
    -- ⊢ a₁ ^ n₂ = a₁
    · rcases Int.isUnit_iff.mp
          (isUnit_of_mul_eq_one _ _ <|
            sub_eq_zero.mp <| (ha₁.zpow_eq_one_iff (n₂ * n₁ - 1)).mp hn₁) with
        (rfl | rfl)
      · rw [zpow_one]
        -- 🎉 no goals
      · rw [zpow_neg_one, y_inv, lt_neg, neg_zero] at Hy
        -- ⊢ a₁ ^ (-1) = a₁
        exact False.elim (lt_irrefl _ <| ha₁.2.1.trans Hy)
        -- 🎉 no goals
    · rw [← zpow_zero a₁, eq_comm] at hn₁
      -- ⊢ a₁ ^ n₂ = a₁
      exact False.elim (ha₁.zpow_ne_neg_zpow hn₁)
      -- 🎉 no goals
  · rw [x_neg, lt_neg] at Hx
    -- ⊢ -a₁ ^ n₂ = a₁
    have := (x_zpow_pos (zero_lt_one.trans ha₁.1) n₂).trans Hx
    -- ⊢ -a₁ ^ n₂ = a₁
    norm_num at this
    -- 🎉 no goals
#align pell.exists_unique_pos_generator Pell.existsUnique_pos_generator

/-- A positive solution is a generator (up to sign) of the group of all solutions to the
Pell equation `x^2 - d*y^2 = 1` if and only if it is a fundamental solution. -/
theorem pos_generator_iff_fundamental (a : Solution₁ d) :
    (1 < a.x ∧ 0 < a.y ∧ ∀ b : Solution₁ d, ∃ n : ℤ, b = a ^ n ∨ b = -a ^ n) ↔ IsFundamental a := by
  refine' ⟨fun h => _, fun H => ⟨H.1, H.2.1, H.eq_zpow_or_neg_zpow⟩⟩
  -- ⊢ IsFundamental a
  have h₀ := d_pos_of_one_lt_x h.1
  -- ⊢ IsFundamental a
  have hd := d_nonsquare_of_one_lt_x h.1
  -- ⊢ IsFundamental a
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  -- ⊢ IsFundamental a
  obtain ⟨b, -, hb₂⟩ := existsUnique_pos_generator h₀ hd
  -- ⊢ IsFundamental a
  rwa [hb₂ a h, ← hb₂ a₁ ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩]
  -- 🎉 no goals
#align pell.pos_generator_iff_fundamental Pell.pos_generator_iff_fundamental

end Pell
