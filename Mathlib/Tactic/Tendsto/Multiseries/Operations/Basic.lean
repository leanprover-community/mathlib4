/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.Multiseries.Basis

/-!
# Basic operations for multiseries: multiplication by constant and negation

-/

namespace TendstoTactic

namespace PreMS

open Stream' Seq

def mulConst {basis : Basis} (ms : PreMS basis) (c : ℝ) : PreMS basis :=
  match basis with
  | [] => ms * c
  | List.cons _ _ =>
    Seq.map (fun (exp, coef) => (exp, mulConst coef c)) ms

def neg {basis : Basis} (ms : PreMS basis) : PreMS basis :=
  ms.mulConst (-1)

instance instNeg {basis : Basis} : Neg (PreMS basis) where
  neg := neg

instance {basis_hd : ℝ → ℝ} {basis_tl : Basis} : Neg (PreMS (basis_hd :: basis_tl)) := instNeg

-------------------- theorems

open Filter Asymptotics

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

theorem zero_WellOrdered {basis : Basis} : (0 : PreMS basis).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons => exact WellOrdered.nil

-- TODO : move it
theorem const_Approximates_const {c : ℝ} {basis : Basis} (h_wo : MS.WellOrderedBasis basis) :
    (const basis c).Approximates (fun _ ↦ c) := by
  cases basis with
  | nil => simp [Approximates, const]
  | cons basis_hd basis_tl =>
    simp [const]
    have ih : (const basis_tl c).Approximates (fun _ ↦ c) := by
      apply const_Approximates_const (MS.WellOrderedBasis_tail h_wo)
    apply Approximates.cons _ ih
    · apply const_majorated
      apply MS.basis_tendsto_top h_wo
      simp
    · apply Approximates.nil
      simp
      rfl

-- TODO : move it
theorem zero_Approximates_zero {basis : Basis} :
    (zero basis).Approximates (fun _ ↦ 0) := by
  cases basis with
  | nil => simp [Approximates, zero]
  | cons =>
    simp [zero]
    exact Approximates.nil (by rfl)

theorem one_Approximates_one {basis : Basis} (h_wo : MS.WellOrderedBasis basis) :
    (one basis).Approximates (fun _ ↦ 1) :=
  const_Approximates_const h_wo

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

theorem monomial_Approximates {basis : Basis} {n : ℕ} (h : n < basis.length)
    (h_wo : MS.WellOrderedBasis basis) : (monomial basis n).Approximates basis[n] := by
  cases basis with
  | nil =>
    simp at h
  | cons basis_hd basis_tl =>
    cases n with
    | zero =>
      simp [monomial]
      apply Approximates.cons (fun _ ↦ 1)
      · exact one_Approximates_one (MS.WellOrderedBasis_tail h_wo)
      · nth_rw 1 [show basis_hd = fun x ↦ (basis_hd x)^(1 : ℝ) by ext x; simp]
        apply PreMS.majorated_self
        apply MS.basis_tendsto_top h_wo
        simp
      · simp
        apply Approximates.nil
        rfl
    | succ m =>
      simp [monomial]
      apply Approximates.cons
      · apply monomial_Approximates
        · simpa using h
        · exact MS.WellOrderedBasis_tail h_wo
      · apply MS.basis_tail_majorated_head h_wo
        apply List.getElem_mem
      · simp
        apply Approximates.nil
        rfl

@[simp]
theorem mulConst_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    mulConst (basis := basis_hd :: basis_tl) Seq.nil c = Seq.nil := by
  simp [mulConst]

@[simp]
theorem mulConst_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    mulConst (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl) c =
    Seq.cons (exp, coef.mulConst c) (tl.mulConst c) := by
  simp [mulConst]

@[simp]
theorem mulConst_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)}
    {c : ℝ} :
    (mulConst X c).leadingExp = X.leadingExp := by
  cases X <;> simp [mulConst]

@[simp]
theorem const_mulConst {basis : Basis} {x y : ℝ} :
    (const basis x).mulConst y = const basis (x * y) := by
  cases basis with
  | nil => simp [mulConst, const]
  | cons =>
    simp [mulConst, const]
    congr
    apply const_mulConst

theorem mulConst_WellOrdered {basis : Basis} {ms : PreMS basis} {c : ℝ}
    (h_wo : ms.WellOrdered) : (ms.mulConst c).WellOrdered := by
  cases basis with
  | nil => constructor
  | cons basis_hd basis_tl =>
    let motive : (PreMS (basis_hd :: basis_tl)) → Prop := fun ms' =>
      ∃ (X : PreMS (basis_hd :: basis_tl)), ms' = X.mulConst c ∧ X.WellOrdered
    apply WellOrdered.coind motive
    · simp [motive]
      use ms
    · intro ms ih
      simp [motive] at ih
      obtain ⟨X, h_ms_eq, hX_wo⟩ := ih
      subst h_ms_eq
      cases' X with exp coef tl
      · left
        simp [mulConst]
      · obtain ⟨hX_coef_wo, hX_comp, hX_tl_wo⟩ := WellOrdered_cons hX_wo
        right
        use exp, coef.mulConst c, mulConst (basis := basis_hd :: basis_tl) tl c
        constructor
        · simp [mulConst]
        constructor
        · exact mulConst_WellOrdered hX_coef_wo
        constructor
        · simpa
        simp [motive]
        use tl

theorem mulConst_Approximates {basis : Basis} {ms : PreMS basis} {c : ℝ} {F : ℝ → ℝ}
    (h_approx : ms.Approximates F) :
    (ms.mulConst c).Approximates (fun x ↦ F x * c) := by
  cases basis with
  | nil =>
    simp [Approximates, mulConst] at *
    apply EventuallyEq.mul h_approx
    rfl
  | cons basis_hd basis_tl =>
    let motive : (ℝ → ℝ) → (PreMS (basis_hd :: basis_tl)) → Prop := fun f ms' =>
      ∃ (X : PreMS (basis_hd :: basis_tl)) (fX : ℝ → ℝ),
        ms' = X.mulConst c ∧ f =ᶠ[atTop] (fun x ↦ fX x * c) ∧
        X.Approximates fX
    apply Approximates.coind motive
    · simp only [motive]
      use ms, F
    · intro f ms ih
      simp only [motive] at ih
      obtain ⟨X, fX, h_ms_eq, hf_eq, hX_approx⟩ := ih
      cases' X with X_exp X_coef X_tl
      · left
        apply Approximates_nil at hX_approx
        simp [mulConst] at h_ms_eq
        constructor
        · exact h_ms_eq
        trans
        · exact hf_eq
        conv =>
          rhs
          ext x
          simp
          rw [← zero_mul c]
        apply EventuallyEq.mul hX_approx
        rfl
      · obtain ⟨XC, hX_coef, hX_maj, hX_tl⟩ := Approximates_cons hX_approx
        right
        simp [mulConst] at h_ms_eq
        use ?_, ?_, ?_, fun x ↦ XC x * c
        constructor
        · exact h_ms_eq
        constructor
        · exact mulConst_Approximates hX_coef
        constructor
        · apply majorated_of_EventuallyEq hf_eq
          exact mul_const_majorated hX_maj
        simp only [motive]
        use X_tl, fun x ↦ fX x - basis_hd x ^ X_exp * XC x
        constructor
        · rfl
        constructor
        · apply eventuallyEq_iff_sub.mpr
          eta_expand
          simp
          ring_nf!
          apply eventuallyEq_iff_sub.mp
          conv => rhs; ext; rw [mul_comm]
          exact hf_eq
        · exact hX_tl

@[simp]
theorem neg_leadingExp {basis_hd : ℝ → ℝ} {basis_tl : Basis} {X : PreMS (basis_hd :: basis_tl)} :
    X.neg.leadingExp = X.leadingExp := by
  simp [neg]

theorem neg_WellOrdered {basis : Basis} {ms : PreMS basis}
    (h_wo : ms.WellOrdered) : ms.neg.WellOrdered :=
  mulConst_WellOrdered h_wo

theorem neg_Approximates {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_approx : ms.Approximates F) : ms.neg.Approximates (-F) := by
  rw [← mul_neg_one]
  eta_expand
  simp only [Pi.one_apply, Pi.neg_apply, Pi.mul_apply]
  apply mulConst_Approximates h_approx

@[simp]
theorem neg_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    neg (basis := basis_hd :: basis_tl) Seq.nil = Seq.nil := by
  simp [neg]

@[simp]
theorem neg_cons {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : PreMS basis_tl} {tl : PreMS (basis_hd :: basis_tl)} :
    neg (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl) =
    Seq.cons (exp, coef.neg) tl.neg := by
  simp [neg]

end PreMS

-- def MS.monomial (basis : Basis) (n : ℕ) (h : n < basis.length)
--     (h_basis : MS.WellOrderedBasis basis) : MS where
--   basis := basis
--   val := PreMS.monomial basis n
--   F := basis[n]
--   h_wo := PreMS.monomial_WellOrdered
--   h_approx := PreMS.monomial_Approximates h h_basis

-- def MS.neg (x : MS) : MS where
--   basis := x.basis
--   val := x.val.neg
--   F := -x.F
--   h_wo := PreMS.neg_WellOrdered x.h_wo
--   h_approx := PreMS.neg_Approximates x.h_approx

end TendstoTactic
