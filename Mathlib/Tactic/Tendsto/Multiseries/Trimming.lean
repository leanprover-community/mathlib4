/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Basic

/-!
# Trimming of multiseries
-/

namespace TendstoTactic

namespace PreMS

open Filter Topology Stream'

/-- We call multiseries `Trimmed` if it is either constant, `[]` or `cons (exp, coef) tl` where
coef is trimmed and is not zero. Intuitively, when multiseries is trimmed, it guarantees that
leading term of multiseries is main asymptotics of the function, approximated by multiseries. -/
inductive Trimmed : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} : Trimmed (basis := []) c
| nil {basis_hd} {basis_tl} : Trimmed (basis := basis_hd :: basis_tl) Seq.nil
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
  {tl : PreMS (basis_hd :: basis_tl)} (h_trimmed : coef.Trimmed)
  (h_ne_zero : coef ≠ zero _) :
  Trimmed (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)

/-- If `cons (exp, coef) tl` is trimmed it means that `coef` is trimmed and is not zero. -/
theorem Trimmed_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)}
    (h : Trimmed (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)) :
    coef.Trimmed ∧ coef ≠ zero _ := by
  apply h.casesOn (motive := fun {basis : Basis} (a : PreMS basis) (_ : a.Trimmed) =>
    (h_basis : basis = basis_hd :: basis_tl) → (a = h_basis ▸ (Seq.cons (exp, coef) tl)) →
      coef.Trimmed ∧ coef ≠ zero _)
  · intro _ h_basis
    simp at h_basis
  · intro _ _ h_basis h
    simp only [List.cons.injEq] at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp at h
  · intro _ _ exp coef tl h_trimmed h_ne_zero h_basis h
    simp only [List.cons.injEq] at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp only [Seq.cons_eq_cons, Prod.mk.injEq] at h
    rw [← h.1.2]
    exact ⟨h_trimmed, h_ne_zero⟩
  · rfl
  · rfl

theorem const_Trimmed {basis : Basis} {c : ℝ} (hc : c ≠ 0) : (PreMS.const basis c).Trimmed := by
  cases' basis with basis_hd basis_tl
  · constructor
  simp only [const]
  constructor
  · exact const_Trimmed hc
  cases basis_tl <;> simp [const, zero, hc]

theorem monomial_rpow_Trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) (r : ℝ) :
    (PreMS.monomial_rpow basis n r).Trimmed := by
  cases' basis with basis_hd basis_tl
  · constructor
  cases' n with n
  · constructor
    · simp only [one]
      exact const_Trimmed (by simp)
    · cases basis_tl <;> simp [one, zero, const]
  · constructor
    · apply monomial_rpow_Trimmed
      simpa using h
    · cases basis_tl
      · simp at h
      cases n <;> simp [monomial_rpow, zero]

theorem monomial_Trimmed {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (PreMS.monomial basis n).Trimmed :=
  monomial_rpow_Trimmed h 1

theorem extendBasisEnd_ne_zero {basis : Basis} {b : ℝ → ℝ} {ms : PreMS basis}
    (h : ms ≠ zero _) : ms.extendBasisEnd b ≠ zero _ := by
  cases' basis with basis_hd basis_tl
  · simp [extendBasisEnd, zero, const]
  cases' ms with exp coef tl
  · simp [zero] at h
  simp [extendBasisEnd, zero]

theorem extendBasisEnd_Trimmed {basis_hd : ℝ → ℝ} {basis_tl : Basis} {b : ℝ → ℝ}
    {ms : PreMS (basis_hd :: basis_tl)}
    (h_trimmed : ms.Trimmed) : (ms.extendBasisEnd b).Trimmed := by
  cases' ms with exp coef tl
  · constructor
  simp only [List.cons_append, extendBasisEnd, List.append_eq, Seq.map_cons]
  constructor
  · cases' basis_tl with basis_tl_hd basis_tl_tl
    · simp only [List.nil_append, extendBasisEnd, const]
      constructor
      · exact (Trimmed_cons h_trimmed).left
      · exact (Trimmed_cons h_trimmed).right
    · exact extendBasisEnd_Trimmed (Trimmed_cons h_trimmed).left
  · cases' basis_tl with basis_tl_hd basis_tl_tl
    · simp [extendBasisEnd, const, zero]
    · exact extendBasisEnd_ne_zero (Trimmed_cons h_trimmed).right

theorem extendBasisMiddle_Trimmed {left right_tl : Basis} {right_hd b : ℝ → ℝ}
    {ms : PreMS (left ++ right_hd :: right_tl)}
    (h_trimmed : ms.Trimmed) (h_ne_zero : ms ≠ zero _) : (ms.extendBasisMiddle b).Trimmed := by
  -- sorry
  cases' left with left_hd left_tl
  · cases' ms with exp coef tl
    · simp [zero] at h_ne_zero
    simp only [List.nil_append, extendBasisMiddle]
    constructor
    · exact h_trimmed
    · simp [zero]
  · cases' ms with exp coef tl
    · simp [zero] at h_ne_zero
    simp only [List.cons_append, extendBasisMiddle, List.append_eq, Seq.map_cons]
    apply Trimmed_cons at h_trimmed
    constructor
    · exact extendBasisMiddle_Trimmed h_trimmed.left h_trimmed.right
    · cases' left_tl with left_tl_hd left_tl_tl
      · simp [extendBasisMiddle, zero]
      · cases' coef with coef_exp coef_coef coef_tl
        · simp [zero] at h_trimmed
        simp [extendBasisMiddle, zero]

-- TODO: Where should I put it? Trimming is not needed here.
/-- If `f` can be approximated by multiseries with negative leading exponent, then
it tends to zero. -/
theorem neg_leadingExp_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_neg : ms.leadingExp < 0) (h_approx : ms.Approximates f) :
    Tendsto f atTop (𝓝 0) := by
    cases' ms with exp coef tl
    · apply Approximates_nil at h_approx
      apply Tendsto.congr' h_approx.symm
      apply tendsto_const_nhds
    · obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
      simp only [leadingExp_cons, WithBot.coe_lt_zero] at h_neg
      apply majorated_tendsto_zero_of_neg h_neg h_maj

end PreMS

end TendstoTactic
