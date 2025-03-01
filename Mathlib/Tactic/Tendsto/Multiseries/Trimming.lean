/-
Copyright (c) 2024 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Basic

/-!
# Trimming of multiseries
-/

namespace TendstoTactic

namespace PreMS

open Stream'

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
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp at h
  · intro _ _ exp coef tl h_trimmed h_ne_zero h_basis h
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp [Seq.cons_eq_cons] at h
    rw [← h.1.2]
    exact ⟨h_trimmed, h_ne_zero⟩
  · rfl
  · rfl

-- TODO: Where should I put it? Trimming is not needed here.
/-- If `f` can be approximated by multiseries with negative leading exponent, then
it tends to zero. -/
theorem neg_leadingExp_tendsto_zero {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} {f : ℝ → ℝ}
    (h_neg : ms.leadingExp < 0) (h_approx : ms.Approximates f) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
    cases' ms with exp coef tl
    · apply Approximates_nil at h_approx
      apply Filter.Tendsto.congr' h_approx.symm
      apply tendsto_const_nhds
    · obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
      simp at h_neg
      apply majorated_tendsto_zero_of_neg h_neg h_maj

end PreMS

end TendstoTactic
