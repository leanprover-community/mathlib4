/-
Copyright (c) 2025 Lavendula. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lavendula
-/

import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Multivariate Polynomial Ring Properties about irreducibility.

This file contains theorems about the structure of multivariate polynomial rings over a field,
focusing on irreducibility and principal ideal domain properties.

The proofs utilize polynomial ring isomorphisms and properties of principal ideal rings.
-/

open MvPolynomial Ideal

variable (R : Type*) [Field R]
variable (σ : Type*) [Fintype σ] [DecidableEq σ]

section Irreducible

theorem MvPolynomial.irreducible_X (R : Type*) [Field R] {σ : Type*} [Fintype σ] [DecidableEq σ]
(i : σ) : Irreducible (X i : MvPolynomial σ R) := by
  let remaining_vars : Finset σ := Finset.univ.erase i
  let e : σ ≃ Option remaining_vars := by
    letI : Fintype remaining_vars := Finset.fintypeCoeSort remaining_vars
    refine
    { toFun :=
    fun x => if h : x = i then none else some ⟨x, Finset.mem_erase.mpr ⟨h, Finset.mem_univ _⟩⟩
      invFun := fun o => o.elim i (↑)
      left_inv := by
        intro x
        dsimp
        by_cases h : x = i
        · simp [h]
        · simp only [h, dite_false]
          rw [Option.elim_some]
      right_inv := by
        intro o
        cases o with
        | none => simp
        | some val =>
          simp
          exact (Finset.mem_erase.mp val.2).1 }
  let φ : MvPolynomial σ R ≃ₐ[R] MvPolynomial (Option remaining_vars) R := renameEquiv R e
  let ψ : MvPolynomial (Option remaining_vars) R ≃ₐ[R] Polynomial (MvPolynomial remaining_vars R) :=
  optionEquivLeft R remaining_vars
  let iso := φ.trans ψ
  have h_iso: iso (X i) = Polynomial.X := by
    rw [AlgEquiv.trans_apply, renameEquiv_apply, rename_X]
    have e_i_eq_none : e i = none := by
      simp [e]
    rw [e_i_eq_none, optionEquivLeft_X_none]
  have : Irreducible (iso (X i)) := by
    rw [h_iso]
    exact Polynomial.irreducible_X
  exact (MulEquiv.irreducible_iff iso).mp this

theorem mvPolynomial_not_pid_of_card_ge_two (h : 2 ≤ Fintype.card σ) :
¬ IsPrincipalIdealRing (MvPolynomial σ R) := by
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h
  intro hPID
  let xi : MvPolynomial σ R := X i
  have xi_irr : Irreducible xi := MvPolynomial.irreducible_X R i
  let I := Ideal.span ({xi} : Set (MvPolynomial σ R))
  have hmax: IsMaximal (I) :=
    PrincipalIdealRing.isMaximal_of_irreducible xi_irr
  have not_mem : X j ∉ I := by
    intro h'
    rw [mem_span_singleton, X_dvd_X] at h'
    exact hij h'
  have : I + Ideal.span {X j} = ⊤ :=
    hmax.out.sup_eq_top_iff.mpr (mt I.span_singleton_le_iff_mem.mp not_mem)
  rw [Ideal.eq_top_iff_one] at this
  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp this
  obtain ⟨p, rfl⟩ := mem_span_singleton.mp hp
  obtain ⟨q, rfl⟩ := mem_span_singleton.mp hq
  apply_fun (eval fun _ ↦ 0) at hpq
  simp [xi] at hpq

end Irreducible
