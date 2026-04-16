/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation

/-!
# Order properties of `CFC.rpow`

This file shows that `a ↦ a ^ p` is monotone for `p ∈ [0, 1]`, where `a` is an element of a
C⋆-algebra. The proof makes use of the integral representation of `rpow` in
`Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation`.

## Main declarations

+ `CFC.monotone_nnrpow`, `CFC.monotone_rpow`: `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`
+ `CFC.monotone_sqrt`: `CFC.sqrt` is operator monotone

## TODO

+ Show operator concavity of `rpow` over `Icc 0 1`
+ Show that `rpow` over `Icc (-1) 0` is operator antitone and operator convex
+ Show operator convexity of `rpow` over `Icc 1 2`

## References

+ [carlen2010] Eric A. Carlen, "Trace inequalities and quantum entropies: An introductory course"
  (see Lemma 2.8)
-/

public section

open Set
open scoped NNReal

namespace CFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Real MeasureTheory

/-- This is an intermediate result; use the more general `CFC.monotone_nnrpow` instead. -/
private lemma monotoneOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo 0 1) :
    MonotoneOn (fun a : A => a ^ p) (Ici 0) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  have h₃' : (Ici 0).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine MonotoneOn.congr ?_ h₃'.symm
  refine integral_monotoneOn_of_integrand_ae ?_ fun a ha => (hμ a ha).1
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact monotoneOn_cfcₙ_rpowIntegrand₀₁ hp ht

/-- `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`. -/
lemma monotone_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) :
    Monotone (fun a : A => a ^ p) := by
  intro a b hab
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have hIcc : Icc (0 : ℝ≥0) 1 = Ioo 0 1 ∪ {0} ∪ {1} := by ext; simp
    rw [hIcc] at hp
    obtain (hp | hp) | hp := hp
    · exact monotoneOn_nnrpow_Ioo hp ha hb hab
    · simp_all [mem_singleton_iff]
    · simp_all [mem_singleton_iff, nnrpow_one a, nnrpow_one b]
  · have : a ^ p = 0 := cfcₙ_apply_of_not_predicate a ha
    simp [this]

/-- `CFC.sqrt` is operator monotone. -/
lemma monotone_sqrt : Monotone (sqrt : A → A) := by
  intro a b hab
  rw [CFC.sqrt_eq_nnrpow a, CFC.sqrt_eq_nnrpow b]
  refine (monotone_nnrpow (A := A) ?_) hab
  constructor <;> norm_num

@[gcongr]
lemma nnrpow_le_nnrpow {p : ℝ≥0} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
    a ^ p ≤ b ^ p := monotone_nnrpow hp hab

@[gcongr]
lemma sqrt_le_sqrt (a b : A) (hab : a ≤ b) : sqrt a ≤ sqrt b :=
  monotone_sqrt hab

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- `a ↦ a ^ p` is operator monotone for `p ∈ [0,1]`. -/
lemma monotone_rpow {p : ℝ} (hp : p ∈ Icc 0 1) : Monotone (fun a : A => a ^ p) := by
  let q : ℝ≥0 := ⟨p, hp.1⟩
  change Monotone (fun a : A => a ^ (q : ℝ))
  cases (zero_le q).lt_or_eq' with
  | inl hq =>
    simp_rw [← CFC.nnrpow_eq_rpow hq]
    exact monotone_nnrpow hp
  | inr hq =>
    simp only [hq, NNReal.coe_zero]
    intro a b hab
    by_cases ha : 0 ≤ a
    · have hb : 0 ≤ b := ha.trans hab
      simp [CFC.rpow_zero a, CFC.rpow_zero b]
    · have : a ^ (0 : ℝ) = 0 := cfc_apply_of_not_predicate a ha
      simp [this]

@[gcongr]
lemma rpow_le_rpow {p : ℝ} (hp : p ∈ Icc 0 1) {a b : A} (hab : a ≤ b) :
    a ^ p ≤ b ^ p := monotone_rpow hp hab

end UnitalCStarAlgebra

end CFC
