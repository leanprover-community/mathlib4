/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fisher--Rao metric and Cramer--Rao bound (finite case)

Defines the Fisher--Rao inner product on the open probability simplex
and the classical Cramer--Rao lower bound on estimator variance,
for finite sample spaces. All definitions reuse Mathlib primitives
(Finset.sum, div, sq). The Cramer--Rao proof is Cauchy--Schwarz
on the weighted inner product -- the same obstruction kernel as
Robertson--Schrodinger (E01_Cauchy_Gram_01).

## Main definitions

* `OpenSimplex` — a point on the open probability simplex
* `OpenSimplex.fisherRaoInner` — the Fisher--Rao inner product g_p(u,v)
* `fisherInfo` — classical Fisher information I(θ) for a parametric family
* `cramerRao` — the Cramer--Rao lower bound Var(T) ≥ 1/I(θ)

## References

* C. R. Rao, *Information and the accuracy attainable in the estimation
  of statistical parameters*, Bull. Calcutta Math. Soc. 37, 81--91 (1945)
* H. Cramer, *Mathematical Methods of Statistics*, Princeton (1946)
-/

@[expose] public section

noncomputable section

open Finset BigOperators

variable {α : Type*} [Fintype α]

namespace FisherRao

/-! ## I. Open probability simplex -/

/-- A point on the open probability simplex: strictly positive weights summing to 1. -/
structure OpenSimplex (α : Type*) [Fintype α] where
  val : α → ℝ
  pos : ∀ i, 0 < val i
  sum_one : ∑ i : α, val i = 1

namespace OpenSimplex

variable (p : OpenSimplex α)

/-- Every coordinate is nonzero (convenience lemma). -/
theorem val_ne_zero (i : α) : p.val i ≠ 0 := ne_of_gt (p.pos i)

/-- Every coordinate is nonneg (convenience lemma). -/
theorem val_nonneg (i : α) : 0 ≤ p.val i := le_of_lt (p.pos i)

/-! ## II. Fisher--Rao inner product -/

/-- The Fisher--Rao inner product at p ∈ Δ°(α).
    `g_p(u, v) = Σᵢ uᵢ vᵢ / pᵢ` -/
def fisherRaoInner (u v : α → ℝ) : ℝ :=
  ∑ i : α, u i * v i / p.val i

/-- The Fisher--Rao quadratic form (squared norm). -/
def fisherRaoSq (u : α → ℝ) : ℝ := p.fisherRaoInner u u

/-- g_p(u, u) ≥ 0 for all u. -/
theorem fisherRaoSq_nonneg (u : α → ℝ) : 0 ≤ p.fisherRaoSq u := by
  apply Finset.sum_nonneg
  intro i _
  apply div_nonneg
  · exact mul_self_nonneg (u i)
  · exact p.val_nonneg i

/-- g_p(u, u) = 0 ↔ u = 0 (positive definiteness). -/
theorem fisherRaoSq_eq_zero_iff (u : α → ℝ) :
    p.fisherRaoSq u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ u i * u i / p.val i := by
      intro i _
      exact div_nonneg (mul_self_nonneg _) (p.val_nonneg i)
    have hall := Finset.sum_eq_zero_iff_of_nonneg hnn |>.mp h
    ext i
    simp only [Pi.zero_apply]
    have hi := hall i (Finset.mem_univ i)
    rcases div_eq_zero_iff.mp hi with hmul | habs
    · exact mul_self_eq_zero.mp hmul
    · exact absurd habs (p.val_ne_zero i)
  · intro h
    simp [fisherRaoSq, fisherRaoInner, h]

/-- Symmetry: g_p(u, v) = g_p(v, u). -/
theorem fisherRaoInner_comm (u v : α → ℝ) :
    p.fisherRaoInner u v = p.fisherRaoInner v u := by
  simp only [fisherRaoInner]
  congr 1; ext i; ring

/-- Cauchy--Schwarz for the Fisher--Rao inner product:
    g_p(u, v)² ≤ g_p(u, u) · g_p(v, v).
    This is the same Cauchy--Schwarz kernel used in Robertson. -/
theorem fisherRaoInner_sub_smul (u v : α → ℝ) (t : ℝ) :
    p.fisherRaoSq (fun i => u i - t * v i) =
      p.fisherRaoSq u - 2 * t * p.fisherRaoInner u v +
        t ^ 2 * p.fisherRaoSq v := by
  simp only [fisherRaoSq, fisherRaoInner]
  rw [show (∑ i : α, (u i - t * v i) * (u i - t * v i) / p.val i) =
    (∑ i : α, u i * u i / p.val i) - 2 * t * (∑ i : α, u i * v i / p.val i) +
      t ^ 2 * (∑ i : α, v i * v i / p.val i) from by
    rw [Finset.mul_sum, Finset.mul_sum]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _; ring]

theorem fisherRao_cauchy_schwarz (u v : α → ℝ) :
    p.fisherRaoInner u v ^ 2 ≤ p.fisherRaoSq u * p.fisherRaoSq v := by
  by_cases hv : p.fisherRaoSq v = 0
  · rw [p.fisherRaoSq_eq_zero_iff] at hv
    simp [fisherRaoInner, fisherRaoSq, hv]
  · have hvpos : 0 < p.fisherRaoSq v :=
      lt_of_le_of_ne (p.fisherRaoSq_nonneg v) (Ne.symm hv)
    set t := p.fisherRaoInner u v / p.fisherRaoSq v with ht_def
    have key := p.fisherRaoSq_nonneg (fun i => u i - t * v i)
    rw [p.fisherRaoInner_sub_smul u v t] at key
    have ht2 : t * p.fisherRaoInner u v =
        p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v := by
      rw [ht_def]; field_simp
    have ht3 : t ^ 2 * p.fisherRaoSq v =
        p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v := by
      rw [ht_def]; field_simp
    rw [show 2 * t * p.fisherRaoInner u v =
        2 * (p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v) from by
      linarith [ht2]] at key
    rw [ht3] at key
    have h1 : p.fisherRaoInner u v ^ 2 / p.fisherRaoSq v ≤ p.fisherRaoSq u :=
      by linarith
    rwa [div_le_iff₀ hvpos] at h1

end OpenSimplex

/-! ## III. Classical Fisher information -/

/-- Classical Fisher information for a 1-parameter discrete family
    θ ↦ p(·|θ), given as I(θ) = Σᵢ (∂pᵢ/∂θ)² / pᵢ(θ).
    This equals the Fisher--Rao squared norm of the score tangent vector. -/
def fisherInfo (p : α → ℝ) (dp : α → ℝ) : ℝ :=
  ∑ i : α, dp i ^ 2 / p i

/-- Fisher information is nonneg. -/
theorem fisherInfo_nonneg (p dp : α → ℝ) (hpos : ∀ i, 0 < p i) :
    0 ≤ fisherInfo p dp := by
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (sq_nonneg _) (le_of_lt (hpos i))

/-- Fisher information equals the Fisher--Rao squared norm of the
    derivative vector: I(θ) = ‖dp/dθ‖²_FR. -/
theorem fisherInfo_eq_fisherRaoSq (q : OpenSimplex α) (dp : α → ℝ) :
    fisherInfo q.val dp = q.fisherRaoSq dp := by
  simp only [fisherInfo, OpenSimplex.fisherRaoSq, OpenSimplex.fisherRaoInner]
  congr 1; ext i; ring

/-! ## IV. Cramer--Rao lower bound -/

/-- Weighted expectation E_p[f] = Σᵢ f(i) p(i). -/
def expect (p : α → ℝ) (f : α → ℝ) : ℝ :=
  ∑ i : α, f i * p i

/-- Weighted variance Var_p(f) = E_p[(f - E_p[f])²]. -/
def variance (p : α → ℝ) (f : α → ℝ) : ℝ :=
  expect p (fun i => (f i - expect p f) ^ 2)

/-- **Cramer--Rao lower bound.** For a parametric family with
    all pᵢ > 0 and an estimator T satisfying the unbiasedness
    derivative condition Σᵢ T(i) · (∂pᵢ/∂θ) = 1, we have

      Var_p(T) ≥ 1 / I(θ)

    where I(θ) = fisherInfo p dp. The proof is a single application
    of Cauchy--Schwarz on the Fisher--Rao inner product to the pair
    (T - E[T], dp/p), exactly as in Robertson (E01_Cauchy_Gram_01). -/
theorem cramerRao (p dp : α → ℝ) (T : α → ℝ)
    (hpos : ∀ i, 0 < p i)
    (hsum : ∑ i : α, p i = 1)
    (hdsum : ∑ i : α, dp i = 0)
    (hunbiased : ∑ i : α, T i * dp i = 1)
    (hI : 0 < fisherInfo p dp) :
    1 / fisherInfo p dp ≤ variance p T := by
  let q : OpenSimplex α := ⟨p, hpos, hsum⟩
  let a : α → ℝ := fun i => (T i - expect p T) * p i
  have cs := q.fisherRao_cauchy_schwarz a dp
  have hpne : ∀ i, p i ≠ 0 := fun i => ne_of_gt (hpos i)
  have inner_eq : q.fisherRaoInner a dp = 1 := by
    simp only [OpenSimplex.fisherRaoInner, a]
    conv => lhs; arg 2; ext i; rw [show ((T i - expect p T) * p i) * dp i / p i =
        (T i - expect p T) * dp i from by field_simp [hpne i]]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hdsum, mul_zero, sub_zero]
    exact hunbiased
  have sq_u_eq : q.fisherRaoSq a = variance p T := by
    simp only [OpenSimplex.fisherRaoSq, OpenSimplex.fisherRaoInner, variance, expect, a]
    apply Finset.sum_congr rfl; intro i _
    simp only [q]; field_simp [hpne i]
  have sq_v_eq : q.fisherRaoSq dp = fisherInfo p dp := by
    simp only [OpenSimplex.fisherRaoSq, OpenSimplex.fisherRaoInner, fisherInfo]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [inner_eq, sq_u_eq, sq_v_eq] at cs
  rw [one_pow] at cs
  rwa [div_le_iff₀ hI]

end FisherRao

