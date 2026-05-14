/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Data.Real.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike

/-!
# Factorization of monic polynomials of given degree

This file contains two main results:

* `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_one_isMonicOfDegree`
  shows that a monic polynomial of positive degree over an algebraically closed field
  can be written as a monic polynomial of degree 1 times another monic factor.

* `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree`
  shows that a monic polynomial of degree at least two over `ℝ` can be written as
  a monic polynomial of degree two times another monic factor.
-/

public section

namespace Polynomial.IsMonicOfDegree

/-- If `f : F[X]` is monic of degree `≥ 1` and `F` is an algebraically closed field,
then `f = f₁ * f₂` with `f₁` monic of degree `1` and `f₂` monic of degree `f.natDegree - 1`. -/
lemma eq_isMonicOfDegree_one_mul_isMonicOfDegree {F : Type*} [Field F]
    [IsAlgClosed F] {f : F[X]} {n : ℕ} (hf : IsMonicOfDegree f (n + 1)) :
    ∃ f₁ f₂ : F[X], IsMonicOfDegree f₁ 1 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ :=
    exists_monic_irreducible_factor f <| not_isUnit_of_natDegree_pos f <|
      by grind [IsMonicOfDegree.natDegree_eq]
  rw [hf₂, add_comm] at hf
  have hf₁ : IsMonicOfDegree f₁ 1 :=
    ⟨natDegree_eq_of_degree_eq_some <| IsAlgClosed.degree_eq_one_of_irreducible F hf₁i, hf₁m⟩
  exact ⟨f₁, f₂, hf₁, hf₁.of_mul_left hf, hf₂⟩

/-- If `f : ℝ[X]` is monic of positive degree, then `f = f₁ * f₂` with `f₁` monic
of degree `1` or `2`.

This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
-- TODO: generalize to real closed fields when they are available.
lemma eq_isMonicOfDegree_one_or_two_mul {f : ℝ[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 1)) :
    ∃ f₁ f₂ : ℝ[X], (IsMonicOfDegree f₁ 1 ∨ IsMonicOfDegree f₁ 2) ∧ f = f₁ * f₂ := by
  obtain ⟨f₁, hm, hirr, f₂, hf₂⟩ :=
    exists_monic_irreducible_factor f <| not_isUnit_of_natDegree_pos f <|
      by grind [IsMonicOfDegree.natDegree_eq]
  refine ⟨f₁, f₂, ?_, hf₂⟩
  have help {P : ℕ → Prop} {m : ℕ} (hm₀ : 0 < m) (hm₂ : m ≤ 2) (h : P m) : P 1 ∨ P 2 := by
    interval_cases m <;> tauto
  exact help hirr.natDegree_pos hirr.natDegree_le_two <| IsMonicOfDegree.mk rfl hm

/-- If `f : ℝ[X]` is monic of degree `≥ 2`, then `f = f₁ * f₂` with `f₁` monic of degree `2`
and `f₂` monic of degree `f.natDegree - 2`.

This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
-- TODO: generalize to real closed fields when they are available.
lemma eq_isMonicOfDegree_two_mul_isMonicOfDegree {f : ℝ[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 2)) :
    ∃ f₁ f₂ : ℝ[X], IsMonicOfDegree f₁ 2 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨g₁, g₂, hd₁ | hd₂, h⟩ := hf.eq_isMonicOfDegree_one_or_two_mul
  all_goals rw [h, add_comm] at hf
  · have hg₂ := of_mul_left hd₁ <| (show 2 + n = 1 + (n + 1) by lia) ▸ hf
    obtain ⟨p₁, p₂, hp₁ | hp₂, h'⟩ := hg₂.eq_isMonicOfDegree_one_or_two_mul
    · rw [h', ← mul_assoc] at h hf
      exact ⟨g₁ * p₁, p₂, hd₁.mul hp₁, (hd₁.mul hp₁).of_mul_left hf, h⟩
    · rw [h', mul_left_comm] at h hf
      exact ⟨p₁, g₁ * p₂, hp₂, of_mul_left hp₂ hf, h⟩
  · exact ⟨g₁, g₂, hd₂, of_mul_left hd₂ hf, h⟩

end Polynomial.IsMonicOfDegree
