/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Tactic.Contrapose
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# Quotients of powers of principal ideals

This file deals with taking quotients of powers of principal ideals.

## Main definitions and results

* `Ideal.quotEquivPowQuotPowSucc`: for a principal ideal `I`, `R ⧸ I ≃ₗ[R] I ^ n ⧸ I ^ (n + 1)`

## Implementation details

At site of usage, calling `LinearEquiv.toEquiv` can cause timeouts in the search for a complex
synthesis like `Module 𝒪[K] 𝓀[k]`, so the plain equiv versions are provided.

These equivs are defined here as opposed to in the quotients file since they cannot be
formed as ring equivs.

-/

@[expose] public section


namespace Ideal

section IsPrincipal

variable {R : Type*} [CommRing R] [IsDomain R] {I : Ideal R}

/-- For a principal ideal `I`, `R ⧸ I ≃ₗ[R] I ^ n ⧸ I ^ (n + 1)`. To convert into a form
that uses the ideal of `R ⧸ I ^ (n + 1)`, compose with
`Ideal.powQuotPowSuccLinearEquivMapMkPowSuccPow`. -/
noncomputable
def quotEquivPowQuotPowSucc (h : I.IsPrincipal) (h' : I ≠ ⊥) (n : ℕ) :
    (R ⧸ I) ≃ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) := by
  let f : (I ^ n : Ideal R) →ₗ[R] (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
    Submodule.mkQ _
  let ϖ := h.principal.choose
  have hI : I = Ideal.span {ϖ} := h.principal.choose_spec
  have hϖ : ϖ ^ n ∈ I ^ n := hI ▸ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)
  let g : R →ₗ[R] (I ^ n : Ideal R) := (LinearMap.mulRight R ϖ ^ n).codRestrict _ fun x ↦ by
    simp only [LinearMap.pow_mulRight, LinearMap.mulRight_apply]
    -- TODO: change argument of Ideal.pow_mem_of_mem
    exact Ideal.mul_mem_left _ _ hϖ
  have : I = LinearMap.ker (f.comp g) := by
    ext x
    simp only [LinearMap.codRestrict, LinearMap.pow_mulRight, LinearMap.mulRight_apply,
      LinearMap.mem_ker, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul,
      f, g]
    constructor <;> intro hx
    · exact Submodule.mul_mem_mul hx hϖ
    · rw [← pow_succ', hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
      obtain ⟨y, hy⟩ := hx
      rw [mul_comm, pow_succ, mul_assoc, mul_right_inj' (pow_ne_zero _ _)] at hy
      · rw [hI, Ideal.mem_span_singleton]
        exact ⟨y, hy⟩
      · contrapose h'
        rw [hI, h', Ideal.span_singleton_eq_bot]
  let e : (R ⧸ I) ≃ₗ[R] R ⧸ (LinearMap.ker (f.comp g)) :=
    Submodule.quotEquivOfEq I (LinearMap.ker (f ∘ₗ g)) this
  refine e.trans ((f.comp g).quotKerEquivOfSurjective ?_)
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨x, hx⟩
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
  refine hx.imp ?_
  simp [g, LinearMap.codRestrict, eq_comm, mul_comm]

/-- For a principal ideal `I`, `R ⧸ I ≃ I ^ n ⧸ I ^ (n + 1)`. Supplied as a plain equiv to bypass
typeclass synthesis issues on complex `Module` goals.  To convert into a form
that uses the ideal of `R ⧸ I ^ (n + 1)`, compose with
`Ideal.powQuotPowSuccEquivMapMkPowSuccPow`. -/
noncomputable
def quotEquivPowQuotPowSuccEquiv (h : I.IsPrincipal) (h' : I ≠ ⊥) (n : ℕ) :
    (R ⧸ I) ≃ (I ^ n : Ideal R) ⧸ (I • ⊤ : Submodule R (I ^ n : Ideal R)) :=
  quotEquivPowQuotPowSucc h h' n

end IsPrincipal

end Ideal
