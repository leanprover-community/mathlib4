/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SetLike

/-!
# Independence of Gaussian processes

This file contains properties about independence of Gaussian processes. More precisely, we prove
different versions of the following statement: if some stochastic processes are jointly Gaussian,
then they are independent if their marginals are uncorrelated.

## Main statements

* `iIndepFun_of_covariance_eq_zero`: Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$
  are jointly Gaussian. Then they are independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$
  and $s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $\mathrm{Cov}(X^{t_1}_{s_1}, X^{t_2}_{s_2} = 0$.

* `indepFun_of_covariance_eq_zero`: Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$
  that are jointly Gaussian are independent if for all $s \in S$ and $t \in T$,
  $\mathrm{Cov}(X_s, Y_t) = 0$.

## Implementation note

To talk about the joint process of two processes `X : S → Ω → E` and `Y : T → Ω → E`,
we consider the process `Sum.elim X Y : S ⊕ T → Ω → E`, where `S ⊕ T` is
the disjoint union of `S` and `T`, `Sum S T`.

Similarly, the joint process of a family of stochastic processes `X : (t : T) → (s : S t) → Ω → E`
is the process `(p : (t : T) × S t) ↦ X p.1 p.2`, where `(t : T) × S t` is the type of dependent
pairs `Sigma`.

## Tags

Gaussian process, independence
-/

public section

open MeasureTheory InnerProductSpace Finset
open scoped ENNReal NNReal RealInnerProductSpace

namespace ProbabilityTheory.IsGaussianProcess

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E]

section iIndepFun

variable {S : T → Type*} {X : (t : T) → (s : S t) → Ω → E}

/-- Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are uncorrelated. -/
lemma iIndepFun_of_covariance_strongDual [NormedSpace ℝ E]
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (mX : ∀ t s, AEMeasurable (X t s) P)
    (h : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (L₁ L₂ : StrongDual ℝ E),
      cov[L₁ ∘ X t₁ s₁, L₂ ∘ X t₂ s₂; P] = 0) :
    iIndepFun (fun t ω s ↦ X t s ω) P := by
  have := hX.isProbabilityMeasure
  classical
  refine iIndepFun.iIndepFun_process₀ mX fun I J ↦
    HasGaussianLaw.iIndepFun_of_covariance_strongDual ?_ fun i j hij L₁ L₂ ↦ ?_
  · let L : (I.sigma (fun i ↦ if hi : i ∈ I then J ⟨i, hi⟩ else ∅) → E) →L[ℝ] (i : I) → J i → E :=
      { toFun x i j := x ⟨⟨i, j⟩, by simp⟩
        map_add' x y := by ext; simp
        map_smul' c x := by ext; simp
        cont := by fun_prop }
    exact (hX.hasGaussianLaw _).map L
  have h1 : L₁ ∘ (fun ω k ↦ X i k ω) = ∑ k : J i, (L₁ ∘L .single ℝ _ k) ∘ X i k := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₁.sum_comp_single]
  have h2 : L₂ ∘ (fun ω k ↦ X j k ω) = ∑ k : J j, (L₂ ∘L .single ℝ _ k) ∘ X j k := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₂.sum_comp_single]
  rw [h1, h2, covariance_sum_sum]
  · exact sum_eq_zero fun _ _ ↦ sum_eq_zero fun _ _ ↦ h i j (by simpa) ..
  · exact fun k ↦ ((hX.hasGaussianLaw_eval ⟨i, k⟩).map _).memLp_two
  · exact fun k ↦ ((hX.hasGaussianLaw_eval ⟨j, k⟩).map _).memLp_two

/-- Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are uncorrelated. -/
lemma iIndepFun_of_covariance_inner [InnerProductSpace ℝ E]
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (mX : ∀ t s, AEMeasurable (X t s) P)
    (h : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂) (x y : E),
      cov[fun ω ↦ ⟪x, X t₁ s₁ ω⟫, fun ω ↦ ⟪y, X t₂ s₂ ω⟫; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  hX.iIndepFun_of_covariance_strongDual mX fun t₁ t₂ ht s₁ s₂ L₁ L₂ ↦ by
    simpa using h t₁ t₂ ht s₁ s₂ ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)

/-- Assume that the processes $((X^t_s)_{s \in S_t})_{t \in T}$ are jointly Gaussian. Then they are
independent if for all $t_1, t_2 \in T$ with $t_1 \ne t_2$ and
$s_1 \in S_{t_1}$, $s_2 \in S_{t_2}$, $X^{t_1}_{s_1}$ and $X^{t_2}_{s_2}$ are uncorrelated. -/
lemma iIndepFun_of_covariance_eq_zero {X : (t : T) → (s : S t) → Ω → ℝ}
    (hX : IsGaussianProcess (fun (p : (t : T) × S t) ω ↦ X p.1 p.2 ω) P)
    (mX : ∀ t s, AEMeasurable (X t s) P)
    (h : ∀ t₁ t₂, t₁ ≠ t₂ → ∀ (s₁ : S t₁) (s₂ : S t₂), cov[X t₁ s₁, X t₂ s₂; P] = 0) :
    ProbabilityTheory.iIndepFun (fun t ω s ↦ X t s ω) P :=
  hX.iIndepFun_of_covariance_inner mX fun _ _ h' _ _ _ _ ↦ by
    simp [covariance_mul_const_left, covariance_mul_const_right, h _ _ h']

end iIndepFun

section IndepFun

variable {S : Type*} {X : S → Ω → E} {Y : T → Ω → E}

/-- Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrelated. -/
lemma indepFun_of_covariance_strongDual [NormedSpace ℝ E]
    (hXY : IsGaussianProcess (Sum.elim X Y) P)
    (mX : ∀ s, AEMeasurable (X s) P) (mY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ s t (L₁ L₂ : StrongDual ℝ E), cov[L₁ ∘ X s, L₂ ∘ Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P := by
  have := hXY.isProbabilityMeasure
  refine IndepFun.process_indepFun_process₀ mX mY fun I J ↦
    HasGaussianLaw.indepFun_of_covariance_strongDual ?_ fun L₁ L₂ ↦ ?_
  · let L : (I.disjSum J → E) →L[ℝ] (I → E) × (J → E) :=
      { toFun x := (fun s ↦ x ⟨Sum.inl s, inl_mem_disjSum.2 s.2⟩,
          fun t ↦ x ⟨Sum.inr t, inr_mem_disjSum.2 t.2⟩)
        map_add' x y := by ext <;> simp
        map_smul' c x := by ext <;> simp }
    exact (hXY.hasGaussianLaw _).map L
  classical
  have h1 : L₁ ∘ (fun ω i ↦ X i ω) = ∑ i : I, (L₁ ∘L .single ℝ _ i) ∘ X i := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₁.sum_comp_single]
  have h2 : L₂ ∘ (fun ω j ↦ Y j ω) = ∑ j : J, (L₂ ∘L .single ℝ _ j) ∘ Y j := by
    ext; simp [-ContinuousLinearMap.coe_comp', ← L₂.sum_comp_single]
  rw [h1, h2, covariance_sum_sum]
  · exact sum_eq_zero fun i _ ↦ sum_eq_zero fun j _ ↦ h ..
  · exact fun s ↦ ((hXY.hasGaussianLaw_eval (.inl s)).map _).memLp_two
  · exact fun t ↦ ((hXY.hasGaussianLaw_eval (.inr t)).map _).memLp_two

/-- Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrelated. -/
lemma indepFun_of_covariance_inner [InnerProductSpace ℝ E]
    (hXY : IsGaussianProcess (Sum.elim X Y) P)
    (mX : ∀ s, AEMeasurable (X s) P) (mY : ∀ t, AEMeasurable (Y t) P)
    (h : ∀ s t x y, cov[fun ω ↦ ⟪x, X s ω⟫, fun ω ↦ ⟪y, Y t ω⟫; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  hXY.indepFun_of_covariance_strongDual mX mY fun s t L₁ L₂ ↦ by
    simpa using h s t ((toDual ℝ E).symm L₁) ((toDual ℝ E).symm L₂)

/-- Two Gaussian processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ that are jointly Gaussian
are independent if for all $s \in S$ and $t \in T$, $X_s$ and $Y_t$ are uncorrelated. -/
lemma indepFun_of_covariance_eq_zero {X : S → Ω → ℝ} {Y : T → Ω → ℝ}
    (hXY : IsGaussianProcess (Sum.elim X Y) P) (mX : ∀ s, AEMeasurable (X s) P)
    (mY : ∀ t, AEMeasurable (Y t) P) (h : ∀ s t, cov[X s, Y t; P] = 0) :
    IndepFun (fun ω s ↦ X s ω) (fun ω t ↦ Y t ω) P :=
  hXY.indepFun_of_covariance_inner mX mY fun _ _ _ _ ↦ by
    simp [covariance_mul_const_left, covariance_mul_const_right, h]

end IndepFun

end ProbabilityTheory.IsGaussianProcess
