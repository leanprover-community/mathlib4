/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Factorization of monic poynomials of given degree

This file contains two main results:

* `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_one_isMonicOfDegree`
  shows that a monic polynomial of positive degree over an algebraically closed field
  can be written as a monic polynomial of degree 1 times another monic factor.

* `Polynomial.IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree`
  shows that a monic polynomial of degree at least two over `ℝ` can be written as
  a monic polynomial of degree two times another monic factor.
-/

namespace Polynomial

/-- If `f : F[X]` is monic of degree `≥ 1` and `F` is an algebraically closed field,
then `f = f₁ * f₂` with `f₁` monic of degree `1` and `f₂` monic of degree `f.natDegree - 1`. -/
lemma IsMonicOfDegree.eq_mul_isMonicOfDegree_one_isMonicOfDegree {F : Type*} [Field F]
    [IsAlgClosed F] {f : F[X]} {n : ℕ} (hf : IsMonicOfDegree f (n + 1)) :
    ∃ f₁ f₂ : F[X], IsMonicOfDegree f₁ 1 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨f₁, hf₁m, hf₁i, f₂, hf₂⟩ :=
    exists_monic_irreducible_factor f <| not_isUnit_of_natDegree_pos f <|
      by grind [IsMonicOfDegree.natDegree_eq]
  rw [hf₂, add_comm] at hf
  have hf₁ : IsMonicOfDegree f₁ 1 :=
    ⟨natDegree_eq_of_degree_eq_some <| IsAlgClosed.degree_eq_one_of_irreducible F hf₁i, hf₁m⟩
  exact ⟨f₁, f₂, hf₁, hf₁.of_mul_left hf, hf₂⟩

/-- If `f : ℝ[X]` is monic of degree `≥ 2`, then `f = f₁ * f₂` with `f₁` monic of degree `2`
and `f₂` monic of degree `f.natDegree - 2`.

This relies on the fact that irreducible polynomials over `ℝ` have degree at most `2`. -/
-- TODO: generalize to real closed fields when they are available.
lemma IsMonicOfDegree.eq_mul_isMonicOfDegree_two_isMonicOfDegree {f : ℝ[X]} {n : ℕ}
    (hf : IsMonicOfDegree f (n + 2)) :
    ∃ f₁ f₂ : ℝ[X], IsMonicOfDegree f₁ 2 ∧ IsMonicOfDegree f₂ n ∧ f = f₁ * f₂ := by
  obtain ⟨g, hgm, hgi, f₁, hf₁⟩ :=
    exists_monic_irreducible_factor f <| not_isUnit_of_natDegree_pos f <|
      by grind [IsMonicOfDegree.natDegree_eq]
  rw [hf₁, add_comm] at hf
  have hdegpos := hgi.natDegree_pos
  have hdegle := hgi.natDegree_le_two
  have hg : IsMonicOfDegree g g.natDegree := ⟨rfl, hgm⟩
  set m := g.natDegree
  interval_cases m -- `m = 1` or `m = 2`
  · have hf₁' : f₁.natDegree = n + 1 :=
      hg.of_mul_left ((show 2 + n = 1 + (n + 1) by omega) ▸ hf) |>.natDegree_eq
    obtain ⟨g₁, hgm₁, hgi₁, f₂, hf₂⟩ :=
      exists_monic_irreducible_factor f₁ <| not_isUnit_of_natDegree_pos f₁ <| by omega
    have hdeg₁pos := hgi₁.natDegree_pos
    have hdeg₁le := hgi₁.natDegree_le_two
    have hg₁ : IsMonicOfDegree g₁ g₁.natDegree := ⟨rfl, hgm₁⟩
    set m₁ := g₁.natDegree
    interval_cases m₁ -- `m₁ = 1` or `m₁ = 2`
    · rw [hf₂, ← mul_assoc] at hf₁ hf
      exact ⟨g * g₁, f₂, hg.mul hg₁, (hg.mul hg₁).of_mul_left hf, hf₁⟩
    · rw [hf₂, mul_left_comm] at hf₁ hf
      exact ⟨g₁, g * f₂, hg₁, hg₁.of_mul_left hf, hf₁⟩
  · exact ⟨g, f₁, hg, hg.of_mul_left hf, hf₁⟩

end Polynomial
