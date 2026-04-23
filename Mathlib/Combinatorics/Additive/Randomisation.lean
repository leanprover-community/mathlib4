/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Combinatorics.Additive.Dissociation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Randomising by a function of dissociated support

This file proves that a function from a finite abelian group can be randomised by a function of
dissociated support.

Precisely, for `G` a finite abelian group and two functions `c : AddChar G ℂ → ℝ` and
`d : AddChar G ℂ → ℝ` such that `{ψ | d ψ ≠ 0}` is dissociated, the product of the `c ψ` over `ψ` is
the same as the average over `a` of the product of the `c ψ + Re (d ψ * ψ a)`.
-/

public section

open Finset
open scoped BigOperators ComplexConjugate

variable {G : Type*} [Fintype G] [AddCommGroup G] {p : ℕ}

/-- One can randomise by a function of dissociated support. -/
lemma AddDissociated.randomisation (c : AddChar G ℂ → ℝ) (d : AddChar G ℂ → ℂ)
    (hcd : AddDissociated {ψ | d ψ ≠ 0}) : 𝔼 a, ∏ ψ, (c ψ + (d ψ * ψ a).re) = ∏ ψ, c ψ := by
  refine Complex.ofReal_injective ?_
  push_cast
  calc
    _ = ∑ t, (𝔼 a, ∏ ψ ∈ t, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ ∈ tᶜ, (c ψ : ℂ) := by
        simp_rw [expect_mul, ← expect_sum_comm, ← Fintype.prod_add, add_comm,
          Complex.re_eq_add_conj]
    _ = (𝔼 a, ∏ ψ ∈ ∅, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ ∈ ∅ᶜ, (c ψ : ℂ) :=
        Fintype.sum_eq_single ∅ fun t ht ↦ mul_eq_zero_of_left ?_ _
    _ = ∏ ψ, (c ψ : ℂ) := by simp
  simp only [map_mul, prod_div_distrib, prod_add, prod_const, ← expect_div, expect_sum_comm,
    div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero,
    false_and, or_false]
  refine sum_eq_zero fun u _ ↦ ?_
  calc
    𝔼 a, (∏ ψ ∈ u, d ψ * ψ a) * ∏ ψ ∈ t \ u, conj (d ψ) * conj (ψ a)
      = ((∏ ψ ∈ u, d ψ) * ∏ ψ ∈ t \ u, conj (d ψ)) * 𝔼 a, (∑ ψ ∈ u, ψ - ∑ ψ ∈ t \ u, ψ) a := by
        simp_rw [mul_expect, AddChar.sub_apply, AddChar.sum_apply, mul_mul_mul_comm,
          ← prod_mul_distrib, AddChar.map_neg_eq_conj]
    _ = 0 := ?_
  rw [mul_eq_zero, AddChar.expect_eq_zero_iff_ne_zero, sub_ne_zero, or_iff_not_imp_left, ← Ne,
    mul_ne_zero_iff, prod_ne_zero_iff, prod_ne_zero_iff]
  exact fun h ↦ hcd.ne h.1 (by simpa only [map_ne_zero] using h.2)
    (sdiff_ne_right.2 <| .inl ht).symm
