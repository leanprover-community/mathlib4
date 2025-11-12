/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Geißer, Michael Stoll
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic.Qify

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

* [K. Ireland, M. Rosen, *A classical introduction to modern number theory* (Section 17.5)]
  [IrelandRosen1990]

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


open CharZero Zsqrtd

/-- An element of `ℤ√d` has norm one (i.e., `a.re^2 - d*a.im^2 = 1`) if and only if
it is contained in the submonoid of unitary elements.

TODO: merge this result with `Pell.isPell_iff_mem_unitary`. -/
theorem is_pell_solution_iff_mem_unitary {d : ℤ} {a : ℤ√d} :
    a.re ^ 2 - d * a.im ^ 2 = 1 ↔ a ∈ unitary (ℤ√d) := by
  rw [← norm_eq_one_iff_mem_unitary, norm_def, sq, sq, ← mul_assoc]

-- We use `solution₁ d` to allow for a more general structure `solution d m` that
-- encodes solutions to `x^2 - d*y^2 = m` to be added later.
/-- `Pell.Solution₁ d` is the type of solutions to the Pell equation `x^2 - d*y^2 = 1`.
We define this in terms of elements of `ℤ√d` of norm one.
-/
def Solution₁ (d : ℤ) : Type :=
  ↥(unitary (ℤ√d))

namespace Solution₁

variable {d : ℤ}

instance instCommGroup : CommGroup (Solution₁ d) :=
  inferInstanceAs (CommGroup (unitary (ℤ√d)))

instance instHasDistribNeg : HasDistribNeg (Solution₁ d) :=
  inferInstanceAs (HasDistribNeg (unitary (ℤ√d)))

instance instInhabited : Inhabited (Solution₁ d) :=
  inferInstanceAs (Inhabited (unitary (ℤ√d)))

instance : Coe (Solution₁ d) (ℤ√d) where coe := Subtype.val

/-- The `x` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def x (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).re

/-- The `y` component of a solution to the Pell equation `x^2 - d*y^2 = 1` -/
protected def y (a : Solution₁ d) : ℤ :=
  (a : ℤ√d).im

/-- The proof that `a` is a solution to the Pell equation `x^2 - d*y^2 = 1` -/
theorem prop (a : Solution₁ d) : a.x ^ 2 - d * a.y ^ 2 = 1 :=
  is_pell_solution_iff_mem_unitary.mpr a.property

/-- An alternative form of the equation, suitable for rewriting `x^2`. -/
theorem prop_x (a : Solution₁ d) : a.x ^ 2 = 1 + d * a.y ^ 2 := by rw [← a.prop]; ring

/-- An alternative form of the equation, suitable for rewriting `d * y^2`. -/
theorem prop_y (a : Solution₁ d) : d * a.y ^ 2 = a.x ^ 2 - 1 := by rw [← a.prop]; ring

/-- Two solutions are equal if their `x` and `y` components are equal. -/
@[ext]
theorem ext {a b : Solution₁ d} (hx : a.x = b.x) (hy : a.y = b.y) : a = b :=
  Subtype.ext <| Zsqrtd.ext hx hy

/-- Construct a solution from `x`, `y` and a proof that the equation is satisfied. -/
def mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : Solution₁ d where
  val := ⟨x, y⟩
  property := is_pell_solution_iff_mem_unitary.mp prop

@[simp]
theorem x_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).x = x :=
  rfl

@[simp]
theorem y_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (mk x y prop).y = y :=
  rfl

@[simp]
theorem coe_mk (x y : ℤ) (prop : x ^ 2 - d * y ^ 2 = 1) : (↑(mk x y prop) : ℤ√d) = ⟨x, y⟩ :=
  Zsqrtd.ext (x_mk x y prop) (y_mk x y prop)

@[simp]
theorem x_one : (1 : Solution₁ d).x = 1 :=
  rfl

@[simp]
theorem y_one : (1 : Solution₁ d).y = 0 :=
  rfl

@[simp]
theorem x_mul (a b : Solution₁ d) : (a * b).x = a.x * b.x + d * (a.y * b.y) := by
  rw [← mul_assoc]
  rfl

@[simp]
theorem y_mul (a b : Solution₁ d) : (a * b).y = a.x * b.y + a.y * b.x :=
  rfl

@[simp]
theorem x_inv (a : Solution₁ d) : a⁻¹.x = a.x :=
  rfl

@[simp]
theorem y_inv (a : Solution₁ d) : a⁻¹.y = -a.y :=
  rfl

@[simp]
theorem x_neg (a : Solution₁ d) : (-a).x = -a.x :=
  rfl

@[simp]
theorem y_neg (a : Solution₁ d) : (-a).y = -a.y :=
  rfl

/-- When `d` is negative, then `x` or `y` must be zero in a solution. -/
theorem eq_zero_of_d_neg (h₀ : d < 0) (a : Solution₁ d) : a.x = 0 ∨ a.y = 0 := by
  have h := a.prop
  contrapose! h
  have h1 := sq_pos_of_ne_zero h.1
  have h2 := sq_pos_of_ne_zero h.2
  nlinarith

/-- A solution has `x ≠ 0`. -/
theorem x_ne_zero (h₀ : 0 ≤ d) (a : Solution₁ d) : a.x ≠ 0 := by
  intro hx
  have h : 0 ≤ d * a.y ^ 2 := mul_nonneg h₀ (sq_nonneg _)
  rw [a.prop_y, hx, sq, zero_mul, zero_sub] at h
  exact not_le.mpr (neg_one_lt_zero : (-1 : ℤ) < 0) h

/-- A solution with `x > 1` must have `y ≠ 0`. -/
theorem y_ne_zero_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : a.y ≠ 0 := by
  intro hy
  have prop := a.prop
  rw [hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero] at prop
  exact lt_irrefl _ (((one_lt_sq_iff₀ <| zero_le_one.trans ha.le).mpr ha).trans_eq prop)

/-- If a solution has `x > 1`, then `d` is positive. -/
theorem d_pos_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : 0 < d := by
  refine pos_of_mul_pos_left ?_ (sq_nonneg a.y)
  rw [a.prop_y, sub_pos]
  exact one_lt_pow₀ ha two_ne_zero

/-- If a solution has `x > 1`, then `d` is not a square. -/
theorem d_nonsquare_of_one_lt_x {a : Solution₁ d} (ha : 1 < a.x) : ¬IsSquare d := by
  have hp := a.prop
  rintro ⟨b, rfl⟩
  simp_rw [← sq, ← mul_pow, sq_sub_sq, Int.mul_eq_one_iff_eq_one_or_neg_one] at hp
  cutsat

/-- A solution with `x = 1` is trivial. -/
theorem eq_one_of_x_eq_one (h₀ : d ≠ 0) {a : Solution₁ d} (ha : a.x = 1) : a = 1 := by
  have prop := a.prop_y
  rw [ha, one_pow, sub_self, mul_eq_zero, or_iff_right h₀, sq_eq_zero_iff] at prop
  exact ext ha prop

/-- A solution is `1` or `-1` if and only if `y = 0`. -/
theorem eq_one_or_neg_one_iff_y_eq_zero {a : Solution₁ d} : a = 1 ∨ a = -1 ↔ a.y = 0 := by
  refine ⟨fun H => H.elim (fun h => by simp [h]) fun h => by simp [h], fun H => ?_⟩
  have prop := a.prop
  rw [H, sq (0 : ℤ), mul_zero, mul_zero, sub_zero, sq_eq_one_iff] at prop
  exact prop.imp (fun h => ext h H) fun h => ext h H

/-- The set of solutions with `x > 0` is closed under multiplication. -/
theorem x_mul_pos {a b : Solution₁ d} (ha : 0 < a.x) (hb : 0 < b.x) : 0 < (a * b).x := by
  simp only [x_mul]
  refine neg_lt_iff_pos_add'.mp (abs_lt.mp ?_).1
  rw [← abs_of_pos ha, ← abs_of_pos hb, ← abs_mul, ← sq_lt_sq, mul_pow a.x, a.prop_x, b.prop_x, ←
    sub_pos]
  ring_nf
  rcases le_or_gt 0 d with h | h
  · positivity
  · rw [(eq_zero_of_d_neg h a).resolve_left ha.ne', (eq_zero_of_d_neg h b).resolve_left hb.ne']
    simp

/-- The set of solutions with `x` and `y` positive is closed under multiplication. -/
theorem y_mul_pos {a b : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (hbx : 0 < b.x)
    (hby : 0 < b.y) : 0 < (a * b).y := by
  simp only [y_mul]
  positivity

/-- If `(x, y)` is a solution with `x` positive, then all its powers with natural exponents
have positive `x`. -/
theorem x_pow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : ℕ) : 0 < (a ^ n).x := by
  induction n with
  | zero => simp only [pow_zero, x_one, zero_lt_one]
  | succ n ih => rw [pow_succ]; exact x_mul_pos ih hax

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
natural exponents have positive `y`. -/
theorem y_pow_succ_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) (n : ℕ) :
    0 < (a ^ n.succ).y := by
  induction n with
  | zero => simp only [pow_one, hay]
  | succ n ih => rw [pow_succ']; exact y_mul_pos hax hay (x_pow_pos hax _) ih

/-- If `(x, y)` is a solution with `x` and `y` positive, then all its powers with positive
exponents have positive `y`. -/
theorem y_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) {n : ℤ} (hn : 0 < n) :
    0 < (a ^ n).y := by
  lift n to ℕ using hn.le
  norm_cast at hn ⊢
  rw [← Nat.succ_pred_eq_of_pos hn]
  exact y_pow_succ_pos hax hay _

/-- If `(x, y)` is a solution with `x` positive, then all its powers have positive `x`. -/
theorem x_zpow_pos {a : Solution₁ d} (hax : 0 < a.x) (n : ℤ) : 0 < (a ^ n).x := by
  cases n with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact x_pow_pos hax n
  | negSucc n =>
    rw [zpow_negSucc]
    exact x_pow_pos hax (n + 1)

/-- If `(x, y)` is a solution with `x` and `y` positive, then the `y` component of any power
has the same sign as the exponent. -/
theorem sign_y_zpow_eq_sign_of_x_pos_of_y_pos {a : Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y)
    (n : ℤ) : (a ^ n).y.sign = n.sign := by
  rcases n with ((_ | n) | n)
  · rfl
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact Int.sign_eq_one_of_pos (y_pow_succ_pos hax hay n)
  · rw [zpow_negSucc]
    exact Int.sign_eq_neg_one_of_neg (neg_neg_of_pos (y_pow_succ_pos hax hay n))

/-- If `a` is any solution, then one of `a`, `a⁻¹`, `-a`, `-a⁻¹` has
positive `x` and nonnegative `y`. -/
theorem exists_pos_variant (h₀ : 0 < d) (a : Solution₁ d) :
    ∃ b : Solution₁ d, 0 < b.x ∧ 0 ≤ b.y ∧ a ∈ ({b, b⁻¹, -b, -b⁻¹} : Set (Solution₁ d)) := by
  refine
        (lt_or_gt_of_ne (a.x_ne_zero h₀.le)).elim
          ((le_total 0 a.y).elim (fun hy hx => ⟨-a⁻¹, ?_, ?_, ?_⟩) fun hy hx => ⟨-a, ?_, ?_, ?_⟩)
          ((le_total 0 a.y).elim (fun hy hx => ⟨a, hx, hy, ?_⟩) fun hy hx => ⟨a⁻¹, hx, ?_, ?_⟩) <;>
      simp only [neg_neg, inv_inv, neg_inv, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
        x_neg, x_inv, y_neg, y_inv, neg_pos, neg_nonneg, or_true] <;>
    assumption

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
  let ξ : ℝ := √d
  have hξ : Irrational ξ := by
    refine irrational_nrt_of_notint_nrt 2 d (sq_sqrt <| Int.cast_nonneg.mpr h₀.le) ?_ two_pos
    rintro ⟨x, hx⟩
    refine hd ⟨x, @Int.cast_injective ℝ _ _ d (x * x) ?_⟩
    rw [← sq_sqrt <| Int.cast_nonneg.mpr h₀.le, Int.cast_mul, ← hx, sq]
  obtain ⟨M, hM₁⟩ := exists_int_gt (2 * |ξ| + 1)
  have hM : {q : ℚ | |q.1 ^ 2 - d * (q.2 : ℤ) ^ 2| < M}.Infinite := by
    refine Infinite.mono (fun q h => ?_) (infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hξ)
    have h0 : 0 < (q.2 : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr q.pos) 2
    have h1 : (q.num : ℝ) / (q.den : ℝ) = q := mod_cast q.num_div_den
    rw [mem_setOf, abs_sub_comm, ← @Int.cast_lt ℝ,
      ← div_lt_div_iff_of_pos_right (abs_pos_of_pos h0)]
    push_cast
    rw [← abs_div, abs_sq, sub_div, mul_div_cancel_right₀ _ h0.ne', ← div_pow, h1, ←
      sq_sqrt (Int.cast_pos.mpr h₀).le, sq_sub_sq, abs_mul, ← mul_one_div]
    refine mul_lt_mul'' (((abs_add_le ξ q).trans ?_).trans_lt hM₁) h (abs_nonneg _) (abs_nonneg _)
    rw [two_mul, add_assoc, add_le_add_iff_left, ← sub_le_iff_le_add']
    rw [mem_setOf, abs_sub_comm] at h
    refine (abs_sub_abs_le_abs_sub (q : ℝ) ξ).trans (h.le.trans ?_)
    rw [div_le_one h0, one_le_sq_iff_one_le_abs, Nat.abs_cast, Nat.one_le_cast]
    exact q.pos
  obtain ⟨m, hm⟩ : ∃ m : ℤ, {q : ℚ | q.1 ^ 2 - d * (q.den : ℤ) ^ 2 = m}.Infinite := by
    contrapose! hM
    simp only [not_infinite] at hM ⊢
    refine (congr_arg _ (ext fun x => ?_)).mp (Finite.biUnion (finite_Ioo (-M) M) fun m _ => hM m)
    simp only [abs_lt, mem_setOf, mem_Ioo, mem_iUnion, exists_prop, exists_eq_right']
  have hm₀ : m ≠ 0 := by
    rintro rfl
    obtain ⟨q, hq⟩ := hm.nonempty
    rw [mem_setOf, sub_eq_zero, mul_comm] at hq
    obtain ⟨a, ha⟩ := (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨d, hq⟩
    rw [ha, mul_pow, mul_right_inj' (pow_pos (Int.natCast_pos.mpr q.pos) 2).ne'] at hq
    exact hd ⟨a, sq a ▸ hq.symm⟩
  haveI := neZero_iff.mpr (Int.natAbs_ne_zero.mpr hm₀)
  let f : ℚ → ZMod m.natAbs × ZMod m.natAbs := fun q => (q.num, q.den)
  obtain ⟨q₁, h₁ : q₁.num ^ 2 - d * (q₁.den : ℤ) ^ 2 = m,
      q₂, h₂ : q₂.num ^ 2 - d * (q₂.den : ℤ) ^ 2 = m, hne, hqf⟩ :=
    hm.exists_ne_map_eq_of_mapsTo (mapsTo_univ f _) finite_univ
  obtain ⟨hq1 : (q₁.num : ZMod m.natAbs) = q₂.num, hq2 : (q₁.den : ZMod m.natAbs) = q₂.den⟩ :=
    Prod.ext_iff.mp hqf
  have hd₁ : m ∣ q₁.num * q₂.num - d * (q₁.den * q₂.den) := by
    rw [← Int.natAbs_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq1, hq2, ← sq, ← sq]
    norm_cast
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natAbs_dvd, Nat.cast_pow, ← h₂]
  have hd₂ : m ∣ q₁.num * q₂.den - q₂.num * q₁.den := by
    rw [← Int.natAbs_dvd, ← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hq1, hq2]
  replace hm₀ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm₀
  refine ⟨(q₁.num * q₂.num - d * (q₁.den * q₂.den)) / m, (q₁.num * q₂.den - q₂.num * q₁.den) / m,
      ?_, ?_⟩
  · qify [hd₁, hd₂]
    field_simp
    norm_cast
    grind
  · qify [hd₂]
    refine div_ne_zero_iff.mpr ⟨?_, hm₀⟩
    exact mod_cast mt sub_eq_zero.mp (mt Rat.eq_iff_mul_eq_mul.mpr hne)

/-- If `d` is a positive integer, then there is a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1` if and only if `d` is not a square. -/
theorem exists_iff_not_isSquare (h₀ : 0 < d) :
    (∃ x y : ℤ, x ^ 2 - d * y ^ 2 = 1 ∧ y ≠ 0) ↔ ¬IsSquare d := by
  refine ⟨?_, exists_of_not_isSquare h₀⟩
  rintro ⟨x, y, hxy, hy⟩ ⟨a, rfl⟩
  rw [← sq, ← mul_pow, sq_sub_sq] at hxy
  simpa [hy, mul_self_pos.mp h₀, sub_eq_add_neg, eq_neg_self_iff] using Int.eq_of_mul_eq_one hxy

namespace Solution₁

/-- If `d` is a positive integer that is not a square, then there exists a nontrivial solution
to the Pell equation `x^2 - d*y^2 = 1`. -/
theorem exists_nontrivial_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, a ≠ 1 ∧ a ≠ -1 := by
  obtain ⟨x, y, prop, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk x y prop, fun H => ?_, fun H => ?_⟩ <;> apply_fun Solution₁.y at H <;>
    simp [hy] at H

/-- If `d` is a positive integer that is not a square, then there exists a solution
to the Pell equation `x^2 - d*y^2 = 1` with `x > 1` and `y > 0`. -/
theorem exists_pos_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, 1 < a.x ∧ 0 < a.y := by
  obtain ⟨x, y, h, hy⟩ := exists_of_not_isSquare h₀ hd
  refine ⟨mk |x| |y| (by rwa [sq_abs, sq_abs]), ?_, abs_pos.mpr hy⟩
  rw [x_mk, ← one_lt_sq_iff_one_lt_abs, eq_add_of_sub_eq h, lt_add_iff_pos_right]
  exact mul_pos h₀ (sq_pos_of_ne_zero hy)

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

namespace IsFundamental

open Solution₁

/-- A fundamental solution has positive `x`. -/
theorem x_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < a.x :=
  zero_lt_one.trans h.1

/-- If a fundamental solution exists, then `d` must be positive. -/
theorem d_pos {a : Solution₁ d} (h : IsFundamental a) : 0 < d :=
  d_pos_of_one_lt_x h.1

/-- If a fundamental solution exists, then `d` must be a non-square. -/
theorem d_nonsquare {a : Solution₁ d} (h : IsFundamental a) : ¬IsSquare d :=
  d_nonsquare_of_one_lt_x h.1

/-- If there is a fundamental solution, it is unique. -/
theorem subsingleton {a b : Solution₁ d} (ha : IsFundamental a) (hb : IsFundamental b) : a = b := by
  have hx := le_antisymm (ha.2.2 hb.1) (hb.2.2 ha.1)
  refine Solution₁.ext hx ?_
  have : d * a.y ^ 2 = d * b.y ^ 2 := by rw [a.prop_y, b.prop_y, hx]
  exact (sq_eq_sq₀ ha.2.1.le hb.2.1.le).mp (Int.eq_of_mul_eq_mul_left ha.d_pos.ne' this)

/-- If `d` is positive and not a square, then a fundamental solution exists. -/
theorem exists_of_not_isSquare (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃ a : Solution₁ d, IsFundamental a := by
  obtain ⟨a, ha₁, ha₂⟩ := exists_pos_of_not_isSquare h₀ hd
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
  refine ⟨mk x₁ y₁ hy₁, by rw [x_mk]; exact mod_cast hx, hy₀, fun {b} hb => ?_⟩
  rw [x_mk]
  have hb' := (Int.toNat_of_nonneg <| zero_le_one.trans hb.le).symm
  have hb'' := hb
  rw [hb'] at hb ⊢
  norm_cast at hb ⊢
  refine Nat.find_min' P ⟨hb, |b.y|, abs_pos.mpr <| y_ne_zero_of_one_lt_x hb'', ?_⟩
  rw [← hb', sq_abs]
  exact b.prop

/-- The map sending an integer `n` to the `y`-coordinate of `a^n` for a fundamental
solution `a` is strictly increasing. -/
theorem y_strictMono {a : Solution₁ d} (h : IsFundamental a) :
    StrictMono fun n : ℤ => (a ^ n).y := by
  have H : ∀ n : ℤ, 0 ≤ n → (a ^ n).y < (a ^ (n + 1)).y := by
    intro n hn
    rw [← sub_pos, zpow_add, zpow_one, y_mul, add_sub_assoc]
    rw [show (a ^ n).y * a.x - (a ^ n).y = (a ^ n).y * (a.x - 1) by ring]
    refine
      add_pos_of_pos_of_nonneg (mul_pos (x_zpow_pos h.x_pos _) h.2.1)
        (mul_nonneg ?_ (by rw [sub_nonneg]; exact h.1.le))
    rcases hn.eq_or_lt with (rfl | hn)
    · simp only [zpow_zero, y_one, le_refl]
    · exact (y_zpow_pos h.x_pos h.2.1 hn).le
  refine strictMono_int_of_lt_succ fun n => ?_
  rcases le_or_gt 0 n with hn | hn
  · exact H n hn
  · let m : ℤ := -n - 1
    have hm : n = -m - 1 := by simp only [m, neg_sub, sub_neg_eq_add, add_tsub_cancel_left]
    rw [hm, sub_add_cancel, ← neg_add', zpow_neg, zpow_neg, y_inv, y_inv, neg_lt_neg_iff]
    exact H _ (by cutsat)

/-- If `a` is a fundamental solution, then `(a^m).y < (a^n).y` if and only if `m < n`. -/
theorem zpow_y_lt_iff_lt {a : Solution₁ d} (h : IsFundamental a) (m n : ℤ) :
    (a ^ m).y < (a ^ n).y ↔ m < n := by
  refine ⟨fun H => ?_, fun H => h.y_strictMono H⟩
  contrapose! H
  exact h.y_strictMono.monotone H

/-- The `n`th power of a fundamental solution is trivial if and only if `n = 0`. -/
theorem zpow_eq_one_iff {a : Solution₁ d} (h : IsFundamental a) (n : ℤ) : a ^ n = 1 ↔ n = 0 := by
  rw [← zpow_zero a]
  exact ⟨fun H => h.y_strictMono.injective (congr_arg Solution₁.y H), fun H => H ▸ rfl⟩

/-- A power of a fundamental solution is never equal to the negative of a power of this
fundamental solution. -/
theorem zpow_ne_neg_zpow {a : Solution₁ d} (h : IsFundamental a) {n n' : ℤ} : a ^ n ≠ -a ^ n' := by
  intro hf
  apply_fun Solution₁.x at hf
  have H := x_zpow_pos h.x_pos n
  rw [hf, x_neg, lt_neg, neg_zero] at H
  exact lt_irrefl _ ((x_zpow_pos h.x_pos n').trans H)

/-- The `x`-coordinate of a fundamental solution is a lower bound for the `x`-coordinate
of any positive solution. -/
theorem x_le_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x) :
    a₁.x ≤ a.x :=
  h.2.2 hax

/-- The `y`-coordinate of a fundamental solution is a lower bound for the `y`-coordinate
of any positive solution. -/
theorem y_le_y {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : a₁.y ≤ a.y := by
  have H : d * (a₁.y ^ 2 - a.y ^ 2) = a₁.x ^ 2 - a.x ^ 2 := by rw [a.prop_x, a₁.prop_x]; ring
  rw [← abs_of_pos hay, ← abs_of_pos h.2.1, ← sq_le_sq, ← mul_le_mul_iff_right₀ h.d_pos,
    ← sub_nonpos, ← mul_sub, H, sub_nonpos, sq_le_sq, abs_of_pos (zero_lt_one.trans h.1),
    abs_of_pos (zero_lt_one.trans hax)]
  exact h.x_le_x hax

-- helper lemma for the next three results
theorem x_mul_y_le_y_mul_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d}
    (hax : 1 < a.x) (hay : 0 < a.y) : a.x * a₁.y ≤ a.y * a₁.x := by
  rw [← abs_of_pos <| zero_lt_one.trans hax, ← abs_of_pos hay, ← abs_of_pos h.x_pos, ←
    abs_of_pos h.2.1, ← abs_mul, ← abs_mul, ← sq_le_sq, mul_pow, mul_pow, a.prop_x, a₁.prop_x, ←
    sub_nonneg]
  ring_nf
  rw [sub_nonneg, sq_le_sq, abs_of_pos hay, abs_of_pos h.2.1]
  exact h.y_le_y hax hay

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `y`-coordinate remains nonnegative. -/
theorem mul_inv_y_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 ≤ (a * a₁⁻¹).y := by
  simpa only [y_inv, mul_neg, y_mul, le_neg_add_iff_add_le, add_zero] using
    h.x_mul_y_le_y_mul_x hax hay

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate stays positive. -/
theorem mul_inv_x_pos {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : 0 < (a * a₁⁻¹).x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, lt_add_neg_iff_add_lt, zero_add]
  refine lt_of_mul_lt_mul_left ?_ <| zero_le_one.trans hax.le
  calc a.x * (d * (a.y * a₁.y))
    _ = d * a.y * (a.x * a₁.y) := by ring
    _ ≤ d * a.y * (a.y * a₁.x) := by have := x_mul_y_le_y_mul_x h hax hay; have := h.d_pos; gcongr
    _ = (a.x ^ 2 - 1) * a₁.x := by rw [← a.prop_y]; ring
    _ < a.x * (a.x * a₁.x) := by linarith [h.1]

/-- If we multiply a positive solution with the inverse of a fundamental solution,
the `x`-coordinate decreases. -/
theorem mul_inv_x_lt_x {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 1 < a.x)
    (hay : 0 < a.y) : (a * a₁⁻¹).x < a.x := by
  simp only [x_mul, x_inv, y_inv, mul_neg, add_neg_lt_iff_le_add']
  refine lt_of_mul_lt_mul_left ?_ h.2.1.le
  calc a₁.y * (a.x * a₁.x)
    _ = a.x * a₁.y * a₁.x := by ring
    _ ≤ a.y * a₁.x * a₁.x := by have := h.1; have := x_mul_y_le_y_mul_x h hax hay; gcongr
  rw [mul_assoc, ← sq, a₁.prop_x, ← sub_neg]
  suffices a.y - a.x * a₁.y < 0 by convert this using 1; ring
  rw [sub_neg, ← abs_of_pos hay, ← abs_of_pos h.2.1, ← abs_of_pos <| zero_lt_one.trans hax, ←
    abs_mul, ← sq_lt_sq, mul_pow, a.prop_x]
  calc
    a.y ^ 2 = 1 * a.y ^ 2 := (one_mul _).symm
    _ ≤ d * a.y ^ 2 := (mul_le_mul_iff_left₀ <| sq_pos_of_pos hay).mpr h.d_pos
    _ < d * a.y ^ 2 + 1 := lt_add_one _
    _ = (1 + d * a.y ^ 2) * 1 := by rw [add_comm, mul_one]
    _ ≤ (1 + d * a.y ^ 2) * a₁.y ^ 2 :=
      (mul_le_mul_iff_right₀ (by have := h.d_pos; positivity)).mpr (sq_pos_of_pos h.2.1)

/-- Any nonnegative solution is a power with nonnegative exponent of a fundamental solution. -/
theorem eq_pow_of_nonneg {a₁ : Solution₁ d} (h : IsFundamental a₁) {a : Solution₁ d} (hax : 0 < a.x)
    (hay : 0 ≤ a.y) : ∃ n : ℕ, a = a₁ ^ n := by
  lift a.x to ℕ using hax.le with ax hax'
  induction ax using Nat.strong_induction_on generalizing a with | h x ih =>
  rcases hay.eq_or_lt with hy | hy
  · -- case 1: `a = 1`
    refine ⟨0, ?_⟩
    simp only [pow_zero]
    ext <;> simp only [x_one, y_one]
    · have prop := a.prop
      rw [← hy, sq (0 : ℤ), zero_mul, mul_zero, sub_zero,
        sq_eq_one_iff] at prop
      refine prop.resolve_right fun hf => ?_
      have := (hax.trans_eq hax').le.trans_eq hf
      norm_num at this
    · exact hy.symm
  · -- case 2: `a ≥ a₁`
    have hx₁ : 1 < a.x := by nlinarith [a.prop, h.d_pos]
    have hxx₁ := h.mul_inv_x_pos hx₁ hy
    have hxx₂ := h.mul_inv_x_lt_x hx₁ hy
    have hyy := h.mul_inv_y_nonneg hx₁ hy
    lift (a * a₁⁻¹).x to ℕ using hxx₁.le with x' hx'
    obtain ⟨n, hn⟩ := ih x' (mod_cast hxx₂.trans_eq hax'.symm) hyy hx' hxx₁
    exact ⟨n + 1, by rw [pow_succ', ← hn, mul_comm a, ← mul_assoc, mul_inv_cancel, one_mul]⟩

/-- Every solution is, up to a sign, a power of a given fundamental solution. -/
theorem eq_zpow_or_neg_zpow {a₁ : Solution₁ d} (h : IsFundamental a₁) (a : Solution₁ d) :
    ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨b, hbx, hby, hb⟩ := exists_pos_variant h.d_pos a
  obtain ⟨n, hn⟩ := h.eq_pow_of_nonneg hbx hby
  rcases hb with (rfl | rfl | rfl | hb)
  · exact ⟨n, Or.inl (mod_cast hn)⟩
  · exact ⟨-n, Or.inl (by simp [hn])⟩
  · exact ⟨n, Or.inr (by simp [hn])⟩
  · rw [Set.mem_singleton_iff] at hb
    rw [hb]
    exact ⟨-n, Or.inr (by simp [hn])⟩

end IsFundamental

open Solution₁ IsFundamental

/-- When `d` is positive and not a square, then the group of solutions to the Pell equation
`x^2 - d*y^2 = 1` has a unique positive generator (up to sign). -/
theorem existsUnique_pos_generator (h₀ : 0 < d) (hd : ¬IsSquare d) :
    ∃! a₁ : Solution₁ d,
      1 < a₁.x ∧ 0 < a₁.y ∧ ∀ a : Solution₁ d, ∃ n : ℤ, a = a₁ ^ n ∨ a = -a₁ ^ n := by
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  refine ⟨a₁, ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩, fun a (H : 1 < _ ∧ _) => ?_⟩
  obtain ⟨Hx, Hy, H⟩ := H
  obtain ⟨n₁, hn₁⟩ := H a₁
  obtain ⟨n₂, hn₂⟩ := ha₁.eq_zpow_or_neg_zpow a
  rcases hn₂ with (rfl | rfl)
  · rw [← zpow_mul, eq_comm, @eq_comm _ a₁, ← mul_inv_eq_one, ← @mul_inv_eq_one _ _ _ a₁, ←
      zpow_neg_one, neg_mul, ← zpow_add, ← sub_eq_add_neg] at hn₁
    rcases hn₁ with hn₁ | hn₁
    · rcases Int.isUnit_iff.mp
          (isUnit_of_mul_eq_one _ _ <|
            sub_eq_zero.mp <| (ha₁.zpow_eq_one_iff (n₂ * n₁ - 1)).mp hn₁) with
        (rfl | rfl)
      · rw [zpow_one]
      · rw [zpow_neg_one, y_inv, lt_neg, neg_zero] at Hy
        exact False.elim (lt_irrefl _ <| ha₁.2.1.trans Hy)
    · rw [← zpow_zero a₁, eq_comm] at hn₁
      exact False.elim (ha₁.zpow_ne_neg_zpow hn₁)
  · rw [x_neg, lt_neg] at Hx
    have := (x_zpow_pos (zero_lt_one.trans ha₁.1) n₂).trans Hx
    norm_num at this

/-- A positive solution is a generator (up to sign) of the group of all solutions to the
Pell equation `x^2 - d*y^2 = 1` if and only if it is a fundamental solution. -/
theorem pos_generator_iff_fundamental (a : Solution₁ d) :
    (1 < a.x ∧ 0 < a.y ∧ ∀ b : Solution₁ d, ∃ n : ℤ, b = a ^ n ∨ b = -a ^ n) ↔ IsFundamental a := by
  refine ⟨fun h => ?_, fun H => ⟨H.1, H.2.1, H.eq_zpow_or_neg_zpow⟩⟩
  have h₀ := d_pos_of_one_lt_x h.1
  have hd := d_nonsquare_of_one_lt_x h.1
  obtain ⟨a₁, ha₁⟩ := IsFundamental.exists_of_not_isSquare h₀ hd
  obtain ⟨b, -, hb₂⟩ := existsUnique_pos_generator h₀ hd
  rwa [hb₂ a h, ← hb₂ a₁ ⟨ha₁.1, ha₁.2.1, ha₁.eq_zpow_or_neg_zpow⟩]

end Pell
