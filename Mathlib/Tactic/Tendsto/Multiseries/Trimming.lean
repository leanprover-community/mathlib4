/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.Multiseries.Basic

/-!
# Trimming of multiseries
-/

namespace TendstoTactic

namespace PreMS

open Stream'

/-- We call multiseries `ms` flat zero if `ms` is either zero constant (with empty basis)
or `[]`. There are non-flat zeros, e.g. `[(1, []), (0, [])]` corresponding to polynomial 0x + 0. -/
inductive FlatZero : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} (h : c = 0) : FlatZero (basis := []) c
| nil {basis_hd} {basis_tl} : FlatZero (basis := basis_hd :: basis_tl) Seq.nil

/-- `cons (exp, coef) tl` can not be `FlatZero`. -/
theorem FlatZero_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    ¬(FlatZero (basis := (basis_hd :: basis_tl)) (Seq.cons (exp, coef) tl)) := by
  intro h
  let motive : {basis : Basis} → (a : PreMS basis) → a.FlatZero → Prop := fun {basis} a _ =>
    match basis with
    | [] => True
    | List.cons hd tl => a = .nil
  have := h.casesOn (motive := motive) (by simp [motive]) (by simp [motive])
  simp [motive] at this

theorem zero_FlatZero {basis : Basis} : FlatZero (zero basis) := by
  cases basis <;> constructor
  rfl

/-- Positive constant is not `FlatZero`. -/
theorem pos_not_FlatZero {x : PreMS []} (h_pos : 0 < x) : ¬ PreMS.FlatZero x := by
  intro h_zero
  cases h_zero
  linarith

/-- Negative constant is not `FlatZero`. -/
theorem neg_not_FlatZero {x : PreMS []} (h_neg : x < 0) : ¬ PreMS.FlatZero x := by
  intro h_zero
  cases h_zero
  linarith

/-- We call multiseries `Trimmed` if it is either constant, `[]` or `cons (exp, coef) tl` where
coef is trimmed and is not flat zero. Intuitively, when multiseries is trimmed, it guarantees that
leading term of multiseries is main asymptotics of the function, approximated by multiseries. -/
inductive Trimmed : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} : Trimmed (basis := []) c
| nil {basis_hd} {basis_tl} : Trimmed (basis := basis_hd :: basis_tl) Seq.nil
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
  {tl : PreMS (basis_hd :: basis_tl)} (h_trimmed : coef.Trimmed)
  (h_ne_flat_zero : ¬ coef.FlatZero) :
  Trimmed (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)

/-- If `cons (exp, coef) tl` is trimmed it means that `coef` is trimmed and is not flat zero. -/
theorem Trimmed_cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)}
    (h : Trimmed (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)) :
    coef.Trimmed ∧ ¬ coef.FlatZero := by
  apply h.casesOn (motive := fun {basis : Basis} (a : PreMS basis) (_ : a.Trimmed) =>
    (h_basis : basis = basis_hd :: basis_tl) → (a = h_basis ▸ (Seq.cons (exp, coef) tl)) →
      coef.Trimmed ∧ ¬ coef.FlatZero)
  · intro _ h_basis
    simp at h_basis
  · intro _ _ h_basis h
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp at h
  · intro _ _ exp coef tl h_trimmed h_ne_flat_zero h_basis h
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp [Seq.cons_eq_cons] at h
    rw [← h.1.2]
    exact ⟨h_trimmed, h_ne_flat_zero⟩
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
