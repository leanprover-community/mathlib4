/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Tendsto.TendstoM
import Mathlib.Tactic.Tendsto.Multiseries.Basic

/-!
# Trimming of multiseries
-/

namespace TendstoTactic

namespace PreMS

open Stream' Seq

inductive FlatZero : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} (h : c = 0) : FlatZero (basis := []) c
| nil {basis_hd} {basis_tl} : FlatZero (basis := basis_hd :: basis_tl) Seq.nil

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

inductive Trimmed : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} : Trimmed (basis := []) c
| nil {basis_hd} {basis_tl} : Trimmed (basis := basis_hd :: basis_tl) Seq.nil
| cons {basis_hd} {basis_tl} {exp : ℝ} {coef : PreMS basis_tl}
  {tl : PreMS (basis_hd :: basis_tl)} (h_trimmed : coef.Trimmed)
  (h_ne_flat_zero : ¬ coef.FlatZero) :
  Trimmed (basis := basis_hd :: basis_tl) (Seq.cons (exp, coef) tl)

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

def HasNegativeLeading {basis : Basis} (ms : PreMS basis) : Prop :=
  match basis with
  | [] => False
  | List.cons _ _ => ms.leadingExp < 0

def PartiallyTrimmed {basis : Basis} (ms : PreMS basis) : Prop :=
  ms.HasNegativeLeading ∨ ms.Trimmed

-- may be put in another file?
theorem HasNegativeLeading_tendsto_zero {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_neg : ms.HasNegativeLeading) (h_approx : ms.Approximates F) :
    Filter.Tendsto F Filter.atTop (nhds 0) := by
  cases basis with
  | nil => simp [HasNegativeLeading] at h_neg
  | cons =>
    simp [HasNegativeLeading] at h_neg
    cases' ms with exp coef tl
    · apply Approximates_nil at h_approx
      apply Filter.Tendsto.congr' h_approx.symm
      apply tendsto_const_nhds
    · simp at h_neg
      obtain ⟨_, _, h_maj, _⟩ := Approximates_cons h_approx
      apply majorated_tendsto_zero_of_neg h_neg h_maj

namespace Trimming

theorem PreMS.Approximates_sub_zero {basis : Basis} {ms : PreMS basis} {F C : ℝ → ℝ}
    (h_approx : ms.Approximates (F - C)) (hC : C =ᶠ[Filter.atTop] 0) :
    ms.Approximates F := by
  apply PreMS.Approximates_of_EventuallyEq _ h_approx
  have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ F) hC
  simpa using this

structure PreMS.TrimmingResult {basis : Basis} (ms : PreMS basis) where
  result : PreMS basis
  h_wo : ms.WellOrdered → result.WellOrdered
  h_approx : ∀ F, ms.Approximates F → result.Approximates F
  h_trimmed : result.Trimmed

def maxUnfoldingSteps : ℕ := 20

-- def PreMS.trim {basis : Basis} (ms : PreMS basis) (stepsLeft := maxUnfoldingSteps) :
--     Option (PreMS.TrimmingResult ms) :=
--   match stepsLeft with
--   | 0 => .none
--   | stepsLeftNext + 1 => do
--     match basis with
--     | [] => .some {
--         result := ms
--         h_wo := by simp [PreMS.WellOrdered]
--         h_approx := by simp
--         h_trimmed := by constructor
--       }
--     | List.cons basis_hd basis_tl =>
--       match h_destruct : destruct ms with
--       | .none => .some {
--           result := .nil
--           h_wo := by rw [Stream'.Seq.destruct_eq_nil h_destruct]; simp [PreMS.WellOrdered]
--           h_approx := by rw [Stream'.Seq.destruct_eq_nil h_destruct]; simp
--           h_trimmed := by constructor
--         }
--       | .some ((exp, coef), tl) => sorry

-- def asd
--       ms.casesOn (motive := fun x ↦ TendstoM (TrimmingResult (basis := basis_hd :: basis_tl) x))
--         (nil := do return {
--           result := .nil
--           h_wo := by simp [PreMS.WellOrdered]
--           h_approx := by simp
--           h_trimmed := by constructor
--         })
--         (cons := fun (exp, coef) tl => do
--           let coef_trimmed ← PreMS.trim coef stepsLeftNext
--           match basis_tl with
--           | [] =>
--             match ← TendstoTactic.runOracle coef with
--             | .zero h_c_zero =>
--               let tl_trimmed ← PreMS.trim tl stepsLeftNext
--               return {
--                 result := tl_trimmed.result
--                 h_wo := by
--                   intro h_wo
--                   apply WellOrdered_cons at h_wo
--                   exact tl_trimmed.h_wo h_wo.right.right
--                 h_approx := by
--                   intro F h_approx
--                   obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
--                   simp [Approximates] at h_coef
--                   subst h_c_zero
--                   apply tl_trimmed.h_approx
--                   apply Approximates_sub_zero h_tl
--                   have := Filter.EventuallyEq.mul
--                     (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ exp)) h_coef
--                   simpa using this
--                 h_trimmed := tl_trimmed.h_trimmed
--               }
--             | .pos h_c_pos => return {
--                 result := .cons (exp, coef_trimmed.result) tl
--                 h_wo := by
--                   intro h_wo
--                   apply WellOrdered_cons at h_wo
--                   apply WellOrdered.cons
--                   · apply coef_trimmed.h_wo
--                     exact h_wo.left
--                   · exact h_wo.right.left
--                   · exact h_wo.right.right
--                 h_approx := by
--                   intro F h_approx
--                   obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
--                   apply PreMS.Approximates.cons C
--                   · exact coef_trimmed.h_approx _ h_coef
--                   · exact h_maj
--                   · exact h_tl
--                 h_trimmed := by
--                   constructor
--                   · exact coef_trimmed.h_trimmed
--                   · intro h
--                     cases h with | const h =>
--                     have : coef = 0 := by
--                       have : Approximates (fun x ↦ coef) [] coef_trimmed.result := by
--                         apply coef_trimmed.h_approx (fun _ ↦ coef)
--                         simp [Approximates]
--                       rw [h] at this
--                       simp [Approximates, Filter.EventuallyEq] at this
--                       obtain ⟨w, this⟩ := this
--                       specialize this (w + 1)
--                       apply this
--                       linarith
--                     linarith
--               }
--             | .neg h_c_neg => return { -- copypaste from pos
--                 result := .cons (exp, coef_trimmed.result) tl
--                 h_wo := by
--                   intro h_wo
--                   apply WellOrdered_cons at h_wo
--                   apply WellOrdered.cons
--                   · apply coef_trimmed.h_wo
--                     exact h_wo.left
--                   · exact h_wo.right.left
--                   · exact h_wo.right.right
--                 h_approx := by
--                   intro F h_approx
--                   obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
--                   apply PreMS.Approximates.cons C
--                   · exact coef_trimmed.h_approx _ h_coef
--                   · exact h_maj
--                   · exact h_tl
--                 h_trimmed := by
--                   -- simp [PreMS.Trimmed]
--                   constructor
--                   · exact coef_trimmed.h_trimmed
--                   · intro h
--                     cases h with | const h =>
--                     have : coef = 0 := by
--                       have : Approximates (fun x ↦ coef) [] coef_trimmed.result := by
--                         apply coef_trimmed.h_approx (fun _ ↦ coef)
--                         simp [Approximates]
--                       rw [h] at this
--                       simp [Approximates, Filter.EventuallyEq] at this
--                       obtain ⟨w, this⟩ := this
--                       specialize this (w + 1)
--                       apply this
--                       linarith
--                     linarith
--               }
--           | basis_tl_hd :: basis_tl_tl =>
--             coef_trimmed.result.casesOn (motive := fun x => coef_trimmed.result = x →
--                 TendstoM (TrimmingResult (basis := basis_hd :: basis_tl_hd :: basis_tl_tl)
--                 (CoList.cons (exp, coef) tl)))
--               (nil := fun h_coef_trimmed => do
--                 let tl_trimmed ← PreMS.trim tl stepsLeftNext
--                 return {
--                   result := tl_trimmed.result
--                   h_wo := by
--                     intro h_wo
--                     apply WellOrdered_cons at h_wo
--                     exact tl_trimmed.h_wo h_wo.right.right
--                   h_approx := by
--                     intro F h_approx
--                     obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
--                     -- simp [Approximates] at h_coef
--                     -- subst h_c_zero
--                     apply tl_trimmed.h_approx
--                     apply Approximates_sub_zero h_tl
--                     have hC : C =ᶠ[Filter.atTop] 0 := by
--                       have := h_coef_trimmed ▸ coef_trimmed.h_approx C h_coef
--                       exact Approximates_nil this
--                     have := Filter.EventuallyEq.mul
--                       (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ exp)) hC
--                     simpa using this
--                   h_trimmed := tl_trimmed.h_trimmed
--                 }
--               )
--               (cons := fun (tl_exp, tl_coef) tl_tl => fun h_coef_trimmed => do
--                 return {
--                   result := .cons (exp, coef_trimmed.result) tl
--                   h_wo := by
--                     intro h_wo
--                     apply WellOrdered_cons at h_wo
--                     apply WellOrdered.cons
--                     · apply coef_trimmed.h_wo
--                       exact h_wo.left
--                     · exact h_wo.right.left
--                     · exact h_wo.right.right
--                   h_approx := by
--                     intro F h_approx
--                     obtain ⟨C, h_coef, h_maj, h_tl⟩ := Approximates_cons h_approx
--                     apply PreMS.Approximates.cons C
--                     · exact coef_trimmed.h_approx _ h_coef
--                     · exact h_maj
--                     · exact h_tl
--                   h_trimmed := by
--                     constructor
--                     · exact coef_trimmed.h_trimmed
--                     · rw [h_coef_trimmed]
--                       apply FlatZero_cons
--                 }
--               )
--               (by rfl)
--         )

end Trimming

end PreMS

open PreMS.Trimming

-- def MS.Trimmed (ms : MS) : Prop :=
--   ms.val.Trimmed

-- structure MS.TrimmingResult (ms : MS) where
--   result : MS
--   h_eq_basis : ms.basis = result.basis
--   h_eq_F : ms.F = result.F
--   h_trimmed : result.Trimmed

-- def MS.trim (ms : MS) : TendstoM <| MS.TrimmingResult ms := do
--   let r ← PreMS.trim ms.val
--   return {
--     result := {
--       val := r.result
--       basis := ms.basis
--       F := ms.F
--       h_wo := r.h_wo ms.h_wo
--       h_approx := r.h_approx _ ms.h_approx
--     }
--     h_eq_basis := by rfl
--     h_eq_F := by rfl
--     h_trimmed := r.h_trimmed
--   }

end TendstoTactic
