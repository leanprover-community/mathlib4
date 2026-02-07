/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivation

/-!
# Universe testing file

This file makes some definitions and tracks how long they take to unify and typecheck.
It is a demonstration of how brittle universe normalisation is currently.

-/

@[expose] public section

open Algebra Module
open scoped TensorProduct

universe t u v

variable (R : Type u) [CommRing R]

suppress_compilation

section MvPolynomial

set_option trace.profiler.useHeartbeats true
set_option trace.profiler.threshold 1
set_option trace.profiler true

/-- Mathlib version

[Elab.command] [110108964.000000]

[Elab.async] [54944425.000000] Lean.addDecl ▼
  [Kernel] [54944372.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialEquiv1._proof_2]
[Elab.async] [57170005.000000] Lean.addDecl ▼
  [Kernel] [57169938.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialEquiv1._proof_1]

Summary: elaboration 110M, typechecking 111M.

-/
def KaehlerDifferential.mvPolynomialEquiv1 (σ : Type*) :
    Ω[MvPolynomial σ R⁄R] ≃ₗ[MvPolynomial σ R] σ →₀ MvPolynomial σ R where
  __ := (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x ↦ D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; rw [map_zero, map_zero]
    | add => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_add] at *; simp only [*]
    | single a b => simp [-map_smul]
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [map_zero, map_zero, map_zero]
    | add => simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at *; simp only [*]
    | single a b =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Finsupp.linearCombination_single,
        map_smul, Derivation.liftKaehlerDifferential_comp_D]
      congr 1
      induction a using MvPolynomial.induction_on
      · simp only [MvPolynomial.derivation_C, map_zero]
      · simp only [map_add, *]
      · simp [*]

/-- Type* -> Type t

[Elab.command] [23172005.000000]

[Elab.async] [127387.000000] Lean.addDecl ▼
  [Kernel] [127313.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialEquiv2]

Summary: elaboration 23M, typechecking <1M
-/
def KaehlerDifferential.mvPolynomialEquiv2 (σ : Type t) :
    Ω[MvPolynomial σ R⁄R] ≃ₗ[MvPolynomial σ R] σ →₀ MvPolynomial σ R where
  __ := (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x ↦ D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; rw [map_zero, map_zero]
    | add => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_add] at *; simp only [*]
    | single a b => simp [-map_smul]
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [map_zero, map_zero, map_zero]
    | add => simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at *; simp only [*]
    | single a b =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Finsupp.linearCombination_single,
        map_smul, Derivation.liftKaehlerDifferential_comp_D]
      congr 1
      induction a using MvPolynomial.induction_on
      · simp only [MvPolynomial.derivation_C, map_zero]
      · simp only [map_add, *]
      · simp [*]

/-- Type* -> Type v

[Elab.command] [109835621.000000]

[Elab.async] [2785827.000000] Lean.addDecl ▼
  [Kernel] [2785767.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialEquiv3]

Summary:

Elaboration 110M, typechecking 3M
-/
def KaehlerDifferential.mvPolynomialEquiv3 (σ : Type v) :
    Ω[MvPolynomial σ R⁄R] ≃ₗ[MvPolynomial σ R] σ →₀ MvPolynomial σ R where
  __ := (MvPolynomial.mkDerivation _ (Finsupp.single · 1)).liftKaehlerDifferential
  invFun := Finsupp.linearCombination (α := σ) _ (fun x ↦ D _ _ (MvPolynomial.X x))
  right_inv := by
    intro x
    induction x using Finsupp.induction_linear with
    | zero => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]; rw [map_zero, map_zero]
    | add => simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, map_add] at *; simp only [*]
    | single a b => simp [-map_smul]
  left_inv := by
    intro x
    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x
    induction x using Finsupp.induction_linear with
    | zero =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [map_zero, map_zero, map_zero]
    | add => simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom] at *; simp only [*]
    | single a b =>
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Finsupp.linearCombination_single,
        map_smul, Derivation.liftKaehlerDifferential_comp_D]
      congr 1
      induction a using MvPolynomial.induction_on
      · simp only [MvPolynomial.derivation_C, map_zero]
      · simp only [map_add, *]
      · simp [*]

-- summary: mvPolynomialEquiv2 is the quickest (quick elaboration, quick typechecking),
-- then mvPolynomialEquiv3 (slow elaboration, quick typechecking)
-- then mvPolynomialEquiv1 (slow elaboration, slow typechecking)

-- next we'll do mvPolynomialBasis with the same three universe
-- choices (unspecified, before u, after u) and also try
-- all three choices when defining the term, so we have
-- 9 declarations here.

-- The conclusion of the below experiment is that it is highly
-- advised to keep the same universe choices (unspecified, before u, after u)
-- in the declaration and its value; making any changes can be
-- very costly.

/-- [Elab.command] [830145.000000]

[Elab.async] [28350.000000] Lean.addDecl ▼
  [Kernel] [28290.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis11]
-/
def KaehlerDifferential.mvPolynomialBasis11 (σ) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv1 R σ⟩

-- Remark: 11 is very fast, but uses the very slow mvPolynomialEquiv1

/-- [Elab.command] [1788517.000000]

[Elab.async] [4061517.000000] Lean.addDecl ▼
  [Kernel] [4061453.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis12]
-/
def KaehlerDifferential.mvPolynomialBasis12 (σ : Type t) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv1 R σ⟩

-- Remark: that was bad. Elaboration 2M, typechecking 8M

/-- [Elab.command] [654070.000000]

[Elab.async] [28352.000000] Lean.addDecl ▼
  [Kernel] [28290.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis13]
-/
def KaehlerDifferential.mvPolynomialBasis13 (σ : Type v) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv1 R σ⟩

-- Remark: 13 is very fast, but uses the very slow mvPolynomialEquiv1.
-- It is the one of two very fast one which use different universe choices.

/-- [Elab.command] [38246963.000000]

[Elab.async] [4044786.000000] Lean.addDecl ▼
  [Kernel] [4044722.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis21]
-/
def KaehlerDifferential.mvPolynomialBasis21 (σ) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv2 R σ⟩

-- Remark: another disaster. Elaboration 38M (the worst of the lot). Ironically
-- this one is using the fastest mvPolynomialEquiv.

/-- [Elab.command] [702468.000000]

[Elab.async] [23088.000000] Lean.addDecl ▼
  [Kernel] [23026.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis22]

-/
def KaehlerDifferential.mvPolynomialBasis22 (σ : Type t) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv2 R σ⟩

-- Remark: The above is the optimal one. It uses mvPolynomialEquiv2 (the fastest mvPolynomialEquiv)
-- and remains fast both in typechecking (<0.1M) and elaboration (<1M).

/-- [Elab.command] [1743009.000000]

Elab.async] [4044789.000000] Lean.addDecl ▼
  [Kernel] [4044723.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis23]
-/
def KaehlerDifferential.mvPolynomialBasis23 (σ : Type v) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv2 R σ⟩

-- that was horrible typechecking

/-- [Elab.command] [830157.000000]

[Elab.async] [28360.000000] Lean.addDecl ▼
  [Kernel] [28298.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis31]
-/
def KaehlerDifferential.mvPolynomialBasis31 (σ) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv3 R σ⟩

-- 31 was the other fast one which uses different universe choices. Note
-- that it uses Equiv3 which has bad elaboration

/-- [Elab.command] [1788413.000000]

[Elab.async] [4061523.000000] Lean.addDecl ▼
  [Kernel] [4061457.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis32]
-/
def KaehlerDifferential.mvPolynomialBasis32 (σ : Type t) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv3 R σ⟩

-- That was horrible

/-- [Elab.command] [654062.000000]

  [Elab.async] [28359.000000] Lean.addDecl ▼
  [Kernel] [28295.000000] ✅️ typechecking declarations [KaehlerDifferential.mvPolynomialBasis33]
-/
def KaehlerDifferential.mvPolynomialBasis33 (σ : Type v) :
    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=
  ⟨mvPolynomialEquiv3 R σ⟩

-- this is not bad at all, but it uses Equiv3 which has bad elaboration
