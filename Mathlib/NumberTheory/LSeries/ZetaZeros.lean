/-
Copyright (c) 2026 Huanyu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Huanyu Zheng
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.NhdsWithin

/-!
# Discreteness of the zeros of the Riemann zeta function

We show that the zeros of the Riemann zeta function form a discrete subset of `ℂ`,
so that in particular any compact subset of `ℂ` contains only finitely many zeros.

## Main declarations

* `riemannZetaZeros`: The zeros of Riemann zeta function.

## Main results

* `isClosed_riemannZetaZeros`: `riemannZetaZeros` is closed.

* `isDiscrete_riemannZetaZeros`: `riemannZetaZeros` is discrete.

* `IsCompact.inter_riemannZetaZeros_finite`: for any compact set `S : Set ℂ`, the intersection
  `S ∩ riemannZetaZeros` is finite.
-/

@[expose] public section

/-- The zeros of Riemann's ζ-function. -/
def riemannZetaZeros : Set ℂ := riemannZeta ⁻¹' {0}

lemma mem_riemannZetaZeros {z : ℂ} :
    z ∈ riemannZetaZeros ↔ riemannZeta z = 0 := .rfl

/-- The complement of the zero set of `riemannZeta` is codiscrete within `{1}ᶜ`. -/
private lemma riemannZetaZeros_codiscreteWithin_compl_one :
    riemannZetaZerosᶜ ∈ Filter.codiscreteWithin {1}ᶜ := by
  refine analyticOn_riemannZeta.preimage_zero_mem_codiscreteWithin (x := 2) ?_ (by simp) ?_
  · exact riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  · exact isConnected_compl_singleton_of_one_lt_rank (by simp) 1

/-- The complement of the zero set of `riemannZeta` is codiscrete. -/
private lemma compl_riemannZetaZeros_mem_codiscrete :
    riemannZetaZerosᶜ ∈ Filter.codiscrete ℂ := by
  have := riemannZetaZeros_codiscreteWithin_compl_one
  simp only [mem_codiscreteWithin, Set.mem_compl_iff, Set.mem_singleton_iff, sdiff_compl,
    Set.inf_eq_inter, Filter.disjoint_principal_right, mem_codiscrete, compl_compl] at this ⊢
  intro x
  rcases eq_or_ne x 1 with rfl | hx
  · exact riemannZeta_eventually_ne_zero_nhds_one.filter_mono nhdsWithin_le_nhds
  · exact Filter.mem_of_superset (this x hx)
      (by grind [riemannZeta_one_ne_zero, mem_riemannZetaZeros])

lemma isClosed_riemannZetaZeros : IsClosed riemannZetaZeros :=
  by simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).1

lemma isDiscrete_riemannZetaZeros : IsDiscrete riemannZetaZeros :=
  by simpa using (mem_codiscrete'.mp compl_riemannZetaZeros_mem_codiscrete).2

/-- Any compact subset of `ℂ` contains only finitely many zeros of the Riemann zeta function. -/
lemma IsCompact.inter_riemannZetaZeros_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ riemannZetaZeros).Finite := by
  apply (hS.inter_right isClosed_riemannZetaZeros).finite
  exact isDiscrete_riemannZetaZeros.mono Set.inter_subset_right

open Filter in
lemma tendsto_riemannZeta_cofinite_cocompact :
    Tendsto ((↑) : riemannZetaZeros → ℂ) cofinite (cocompact ℂ) :=
  isClosed_riemannZetaZeros.tendsto_coe_cofinite_of_isDiscrete isDiscrete_riemannZetaZeros

end
