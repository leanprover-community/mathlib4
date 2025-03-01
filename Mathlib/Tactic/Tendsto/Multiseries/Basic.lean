/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Defs
import Mathlib.Tactic.Tendsto.Multiseries.Basis

/-!
# TODO
-/

namespace TendstoTactic

namespace PreMS

open Stream'

/-- Multiseries representing constant. -/
def const (basis : Basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => c
  | List.cons _ basis_tl =>
    .cons (0, const basis_tl c) .nil

/-- Neutral element for addition. It is `0 : ℝ` for empty basis and `[]` otherwise. -/
def zero (basis) : PreMS basis :=
  match basis with
  | [] => 0
  | List.cons _ _ => .nil

/-- This instance is needed to create instance for `AddCommMonoid (PreMS basis)`, which is
necessary for using `abel` tactic in our proofs. -/
instance instZero {basis : Basis} : Zero (PreMS basis) where
  zero := zero basis

/-- This instance is copy of the previous. But without it `Zero (PreMS (basis_hd :: basis_tl))` can
not be inferred. -/
instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Zero (PreMS (basis_hd :: basis_tl)) :=
  instZero

@[simp]
theorem noConfusion_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd : ℝ × PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    (Seq.cons hd tl) ≠ (0 : PreMS (basis_hd :: basis_tl)) := by
  rw [show (0 : PreMS (basis_hd :: basis_tl)) = Seq.nil by rfl]
  simp

@[simp]
theorem noConfusion_zero_symm {basis_hd : ℝ → ℝ} {basis_tl : Basis} {hd : ℝ × PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    (0 : PreMS (basis_hd :: basis_tl)) ≠ (Seq.cons hd tl) := by
  exact noConfusion_zero.symm

/-- Neutral element for multiplication. -/
def one (basis : Basis) : PreMS basis :=
  const basis 1

/-- Multiseries representing `basis[n]`. -/
def monomial (basis : Basis) (n : ℕ) : PreMS basis :=
  match n, basis with
  | 0, [] => default
  | 0, List.cons _ _ => .cons (1, one _) .nil
  | _ + 1, [] => default
  | m + 1, List.cons _ basis_tl => .cons (0, monomial basis_tl m) .nil

/-- Constants are well-ordered. -/
theorem const_WellOrdered {c : ℝ} {basis : Basis} :
    (const basis c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    simp [const]
    apply WellOrdered.cons
    · exact const_WellOrdered
    · simp [leadingExp, Ne.bot_lt] -- may be `Ne.bot_lt` should be simp lemma?
    · apply WellOrdered.nil

/-- Zero is well-ordered. -/
theorem zero_WellOrdered {basis : Basis} : (0 : PreMS basis).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons => exact WellOrdered.nil

/-- `one` is wellOrdered. -/
theorem one_WellOrdered {basis : Basis} : (one basis).WellOrdered := by
  simp [one]
  apply const_WellOrdered

-- TODO : move it
/-- Constant multiseries approximates constant function. -/
theorem const_Approximates {c : ℝ} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (const basis c).Approximates (fun _ ↦ c) := by
  cases basis with
  | nil => simp [Approximates, const]
  | cons basis_hd basis_tl =>
    simp [const]
    have ih : (const basis_tl c).Approximates (fun _ ↦ c) := by
      apply const_Approximates h_basis.tail
    apply Approximates.cons _ ih
    · apply const_majorated
      apply basis_tendsto_top h_basis
      simp
    · apply Approximates.nil
      simp
      rfl

-- TODO : move it
/-- `zero` approximates zero functions. -/
theorem zero_Approximates {basis : Basis} :
    (zero basis).Approximates (fun _ ↦ 0) := by
  cases basis with
  | nil => simp [Approximates, zero]
  | cons =>
    simp [zero]
    exact Approximates.nil (by rfl)

/-- `one` approximates unit function. -/
theorem one_Approximates {basis : Basis} (h_wo : WellFormedBasis basis) :
    (one basis).Approximates (fun _ ↦ 1) :=
  const_Approximates h_wo

/-- `monomial` is well-ordered. -/
theorem monomial_WellOrdered {basis : Basis} {n : ℕ} : (monomial basis n).WellOrdered := by
  cases basis with
  | nil =>
    cases n with
    | zero =>
      simp [monomial]
      constructor
    | succ m =>
      simp [monomial, default]
      apply zero_WellOrdered
  | cons basis_hd basis_tl =>
    cases n with
    | zero =>
      simp [monomial]
      apply WellOrdered.cons
      · exact const_WellOrdered
      · simp [leadingExp, Ne.bot_lt]
      · exact WellOrdered.nil
    | succ m =>
      simp [monomial]
      apply WellOrdered.cons
      · exact monomial_WellOrdered
      · simp [leadingExp, Ne.bot_lt]
      · exact WellOrdered.nil

/-- `monomial` approximates monomial function. -/
theorem monomial_Approximates {basis : Basis} {n : ℕ} (h : n < basis.length)
    (h_basis : WellFormedBasis basis) : (monomial basis n).Approximates basis[n] := by
  cases basis with
  | nil =>
    simp at h
  | cons basis_hd basis_tl =>
    cases n with
    | zero =>
      simp [monomial]
      apply Approximates.cons (fun _ ↦ 1)
      · exact one_Approximates h_basis.tail
      · nth_rw 1 [show basis_hd = fun x ↦ (basis_hd x)^(1 : ℝ) by ext x; simp]
        apply PreMS.majorated_self
        apply basis_tendsto_top h_basis
        simp
      · simp
        apply Approximates.nil
        rfl
    | succ m =>
      simp [monomial]
      apply Approximates.cons
      · apply monomial_Approximates
        · simpa using h
        · exact h_basis.tail
      · apply basis_tail_majorated_head h_basis
        apply List.getElem_mem
      · simp
        apply Approximates.nil
        rfl

end PreMS

end TendstoTactic
