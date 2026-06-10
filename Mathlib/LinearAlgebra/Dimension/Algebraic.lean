/-
Copyright (c) 2026 Albert Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Albert Smith
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Algebraic.Basic

import Mathlib.RingTheory.Algebraic.Integral

/-!
# Rank theorems for algebraic extensions

This file generalises some `Module.rank` theorems from fields to domains,
assuming certain extensions are algebraic.

## Main results

Let $S$ be a faithful algebraic $R$-algebra.

- `Algebra.IsAlgebraic.lift_rank_mul_lift_rank` and variants: Tower law for a $S$-module $M$.
-/

public section

universe u v w

open Algebra Cardinal Module
open Module (rank)
open scoped nonZeroDivisors

namespace Algebra.IsAlgebraic

variable
  (R : Type u) (S : Type v) [CommRing R] [CommRing S] [NoZeroDivisors R] [NoZeroDivisors S]
  [Algebra R S] [FaithfulSMul R S] [Algebra.IsAlgebraic R S]

section Tower

variable (M : Type w) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- **Tower law over domains**: if `R` and `S` have no zero divisors, `S` is a faithful algebraic
`R`-algebra, and `M` is a `S`-module, then
$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$.

See `Algebra.IsAlgebraic.rank_mul_rank` for a non–universe polymorphic version, and
`_root_.lift_rank_mul_lift_rank` for when all your modules are free. -/
theorem lift_rank_mul_lift_rank :
    lift.{w} (rank R S) * lift.{v} (rank S M) = lift.{v} (rank R M) := by
  nontriviality R using Module.subsingleton R S
  nontriviality S using Module.subsingleton S M
  have _ : IsDomain S := {}
  letI R' := FractionRing R
  letI S' := FractionRing S
  let M' := LocalizedModule S⁰ M
  let f : M →ₗ[S] M' := LocalizedModule.mkLinearMap ..
  let _ : Algebra R' S' := FractionRing.liftAlgebra ..
  let _ : Module R' M' := .restrictScalars _ S' M'
  have _ : IsScalarTower R' S' M' := .restrictScalars ..
  have _ : IsScalarTower R R' M' := .to₁₂₄ (P := S') ..
  have h₂ : IsBaseChange S' f := IsLocalizedModule.isBaseChange S⁰ _ f
  have h₁ : IsBaseChange R' (f.restrictScalars R) := by
    suffices IsLocalizedModule (algebraMapSubmonoid S R⁰) f from
      this.restrictScalars.isBaseChange R⁰ _ _
    rwa [isLocalizedModule_iff_isBaseChange _ (A := S')]
  rw [← lift_umax.{w, v}, ← Algebra.IsAlgebraic.rank_fractionRing, ← h₂.lift_rank_eq,
    ← h₁.lift_rank_eq, ← lift_umax.{v, w}, lift_id'.{w, v}, lift_id'.{w, v},
     ← lift_id'.{v, w} (rank S' M'),← lift_id'.{v, w} (rank R' M'), _root_.lift_rank_mul_lift_rank]

/-- **Tower law over domains**: if `R` and `S` have no zero divisors, `S` is a faithful algebraic
`R`-algebra, and `M` is a `S`-module, then
$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$.

See `Algebra.IsAlgebraic.lift_rank_mul_lift_rank` for a universe polymorphic version, and
`_root_.rank_mul_rank` for when all your modules are free. -/
theorem rank_mul_rank
  (M : Type v) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] :
    rank R S * rank S M = rank R M := by
  convert! lift_rank_mul_lift_rank R S M <;> rw [lift_id]

/-- **Tower law over domains**: if `R` and `S` have no zero divisors, `S` is a faithful algebraic
`R`-algebra, and `M` is a `S`-module, then
$\operatorname{rank}_R(S) * \operatorname{rank}_S(M) = \operatorname{rank}_R(M)$.

See `Module.finrank_mul_finrank` for when all your modules are free. -/
theorem finrank_mul_finrank :
    finrank R S * finrank S M = finrank R M := by
  simp_rw [finrank]
  rw [← toNat_lift.{w} (rank R S), ← toNat_lift.{v} (rank S M), ← toNat_mul,
    lift_rank_mul_lift_rank, toNat_lift]

end Tower

end Algebra.IsAlgebraic
