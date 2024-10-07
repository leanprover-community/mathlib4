import Mathlib.Tactic.Tendsto.TendstoM
import Mathlib.Tactic.Tendsto.Multiseries.Basic

namespace TendstoTactic

namespace PreMS

-- make basis explicit if further you will always have to specify it

inductive isFlatZero : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} (h : c = 0) : isFlatZero (basis := []) c
| nil {basis_hd : _} {basis_tl : _} : isFlatZero (basis := basis_hd :: basis_tl) CoList.nil

theorem isFlatZero_cons {basis_hd : _} {basis_tl : _} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)} :
    ¬(isFlatZero (basis := (basis_hd :: basis_tl)) (CoList.cons (deg, coef) tl)) := by
  intro h
  let motive : {basis : Basis} → (a : PreMS basis) → a.isFlatZero → Prop := fun {basis} a _ =>
    match basis with
    | [] => True
    | hd :: tl => a = .nil
  have := h.casesOn (motive := motive) (by simp [motive]) (by simp [motive])
  simp [motive] at this

inductive isTrimmed : {basis : Basis} → PreMS basis → Prop
| const {c : ℝ} : isTrimmed (basis := []) c
| nil {basis_hd : _} {basis_tl : _} : isTrimmed (basis := basis_hd :: basis_tl) CoList.nil
| cons {basis_hd : _} {basis_tl : _} {deg : ℝ} {coef : PreMS basis_tl}
  {tl : PreMS (basis_hd :: basis_tl)} (h_trimmed : coef.isTrimmed)
  (h_ne_flat_zero : ¬ coef.isFlatZero) :
  isTrimmed (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl)

theorem isTrimmed_cons {basis_hd : _} {basis_tl : _} {deg : ℝ} {coef : PreMS basis_tl}
    {tl : PreMS (basis_hd :: basis_tl)}
    (h : isTrimmed (basis := basis_hd :: basis_tl) (CoList.cons (deg, coef) tl)) :
    coef.isTrimmed ∧ ¬ coef.isFlatZero := by
  apply h.casesOn (motive := fun {basis : Basis} (a : PreMS basis) (h_trimmed : a.isTrimmed) =>
    (h_basis : basis = basis_hd :: basis_tl) → (a = h_basis ▸ (CoList.cons (deg, coef) tl)) →
      coef.isTrimmed ∧ ¬ coef.isFlatZero)
  · intro _ h_basis
    simp at h_basis
  · intro _ _ h_basis h
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp at h
  · intro _ _ deg coef tl h_trimmed h_ne_flat_zero h_basis h
    simp at h_basis
    obtain ⟨h_basis_hd, h_basis_tl⟩ := h_basis
    subst h_basis_hd h_basis_tl
    simp at h
    rw [← h.1.2]
    exact ⟨h_trimmed, h_ne_flat_zero⟩
  · rfl
  · rfl

def hasNegativeLeading {basis : Basis} (ms : PreMS basis) : Prop :=
  match basis with
  | [] => False
  | _ :: _ => ms.leadingExp < 0

-- inductive hasNegativeLeading : {basis : Basis} → (ms : PreMS basis) → Prop
-- | nil {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} :
--   hasNegativeLeading (basis := basis_hd :: basis_tl) .nil
-- | cons {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)} {deg : ℝ} {coef : PreMS basis_tl}
--     {tl : PreMS (basis_hd :: basis_tl)} (h : deg < 0) :
--   hasNegativeLeading (basis := basis_hd :: basis_tl) (.cons (deg, coef) tl)

def isPartiallyTrimmed {basis : Basis} (ms : PreMS basis) : Prop :=
  ms.hasNegativeLeading ∨ ms.isTrimmed

-- may be put in another file?
theorem hasNegativeLeading_tendsto_zero {basis : Basis} {ms : PreMS basis} {F : ℝ → ℝ}
    (h_neg : ms.hasNegativeLeading) (h_approx : ms.isApproximation F basis) :
    Filter.Tendsto F Filter.atTop (nhds 0) := by
  cases basis with
  | nil => simp [hasNegativeLeading] at h_neg
  | cons =>
    simp [hasNegativeLeading] at h_neg
    revert h_neg h_approx
    apply ms.casesOn
    · intro _ h_approx
      replace h_approx := isApproximation_nil h_approx
      apply Filter.Tendsto.congr' h_approx.symm
      apply tendsto_const_nhds
    · intro (deg, coef) tl h_neg h_approx
      simp [leadingExp] at h_neg
      replace h_approx := isApproximation_cons h_approx
      obtain ⟨_, _, h_comp, _⟩ := h_approx
      apply majorated_tendsto_zero_of_neg h_neg h_comp

namespace Trimming

theorem PreMS.isApproximation_sub_zero {basis : Basis} {ms : PreMS basis} {F C : ℝ → ℝ}
    (h_approx : ms.isApproximation (F - C) basis) (h_C : C =ᶠ[Filter.atTop] 0) :
    ms.isApproximation F basis := by
  apply PreMS.isApproximation_of_EventuallyEq _ h_approx
  have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ F) h_C
  simpa using this

structure PreMS.TrimmingResult {basis : Basis} (ms : PreMS basis) where
  result : PreMS basis
  h_wo : ms.wellOrdered → result.wellOrdered
  h_approx : ∀ F, ms.isApproximation F basis → result.isApproximation F basis
  h_trimmed : result.isTrimmed

def maxUnfoldingSteps : ℕ := 20

def PreMS.trim {basis : Basis} (ms : PreMS basis) (stepsLeft := maxUnfoldingSteps) :
    TendstoM <| PreMS.TrimmingResult ms :=
  match stepsLeft with
  | 0 => do throw TendstoException.trimmingException
  | stepsLeftNext + 1 => do
    match basis with
    | [] => return {
        result := ms
        h_wo := by simp [PreMS.wellOrdered]
        h_approx := by simp
        h_trimmed := by constructor
      }
    | basis_hd :: basis_tl =>
      ms.casesOn (motive := fun x ↦ TendstoM (TrimmingResult (basis := basis_hd :: basis_tl) x))
        (nil := do return {
          result := .nil
          h_wo := by simp [PreMS.wellOrdered]
          h_approx := by simp
          h_trimmed := by constructor
        })
        (cons := fun (deg, coef) tl => do
          let coef_trimmed ← PreMS.trim coef stepsLeftNext
          match basis_tl with
          | [] =>
            match ← TendstoTactic.runOracle coef with
            | .zero h_c_zero =>
              let tl_trimmed ← PreMS.trim tl stepsLeftNext
              return {
                result := tl_trimmed.result
                h_wo := by
                  intro h_wo
                  replace h_wo := wellOrdered_cons h_wo
                  exact tl_trimmed.h_wo h_wo.right.right
                h_approx := by
                  intro F h_approx
                  replace h_approx := isApproximation_cons h_approx
                  obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                  simp [isApproximation] at h_coef
                  subst h_c_zero
                  apply tl_trimmed.h_approx
                  apply isApproximation_sub_zero h_tl
                  have := Filter.EventuallyEq.mul
                    (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) h_coef
                  simpa using this
                h_trimmed := tl_trimmed.h_trimmed
              }
            | .pos h_c_pos => return {
                result := .cons (deg, coef_trimmed.result) tl
                h_wo := by
                  intro h_wo
                  replace h_wo := wellOrdered_cons h_wo
                  apply wellOrdered.cons
                  · apply coef_trimmed.h_wo
                    exact h_wo.left
                  · exact h_wo.right.left
                  · exact h_wo.right.right
                h_approx := by
                  intro F h_approx
                  replace h_approx := isApproximation_cons h_approx
                  obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                  apply PreMS.isApproximation.cons C
                  · exact coef_trimmed.h_approx _ h_coef
                  · exact h_comp
                  · exact h_tl
                h_trimmed := by
                  constructor
                  · exact coef_trimmed.h_trimmed
                  · intro h
                    cases h with | const h =>
                    have : coef = 0 := by
                      have : isApproximation (fun x ↦ coef) [] coef_trimmed.result := by
                        apply coef_trimmed.h_approx (fun _ ↦ coef)
                        simp [isApproximation]
                      rw [h] at this
                      simp [isApproximation, Filter.EventuallyEq] at this
                      obtain ⟨w, this⟩ := this
                      specialize this (w + 1)
                      apply this
                      linarith
                    linarith
              }
            | .neg h_c_neg => return { -- copypaste from pos
                result := .cons (deg, coef_trimmed.result) tl
                h_wo := by
                  intro h_wo
                  replace h_wo := wellOrdered_cons h_wo
                  apply wellOrdered.cons
                  · apply coef_trimmed.h_wo
                    exact h_wo.left
                  · exact h_wo.right.left
                  · exact h_wo.right.right
                h_approx := by
                  intro F h_approx
                  replace h_approx := isApproximation_cons h_approx
                  obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                  apply PreMS.isApproximation.cons C
                  · exact coef_trimmed.h_approx _ h_coef
                  · exact h_comp
                  · exact h_tl
                h_trimmed := by
                  -- simp [PreMS.isTrimmed]
                  constructor
                  · exact coef_trimmed.h_trimmed
                  · intro h
                    cases h with | const h =>
                    have : coef = 0 := by
                      have : isApproximation (fun x ↦ coef) [] coef_trimmed.result := by
                        apply coef_trimmed.h_approx (fun _ ↦ coef)
                        simp [isApproximation]
                      rw [h] at this
                      simp [isApproximation, Filter.EventuallyEq] at this
                      obtain ⟨w, this⟩ := this
                      specialize this (w + 1)
                      apply this
                      linarith
                    linarith
              }
          | basis_tl_hd :: basis_tl_tl =>
            coef_trimmed.result.casesOn (motive := fun x => coef_trimmed.result = x → TendstoM (TrimmingResult (basis := basis_hd :: basis_tl_hd :: basis_tl_tl) (CoList.cons (deg, coef) tl)))
              (nil := fun h_coef_trimmed => do
                let tl_trimmed ← PreMS.trim tl stepsLeftNext
                return {
                  result := tl_trimmed.result
                  h_wo := by
                    intro h_wo
                    replace h_wo := wellOrdered_cons h_wo
                    exact tl_trimmed.h_wo h_wo.right.right
                  h_approx := by
                    intro F h_approx
                    replace h_approx := isApproximation_cons h_approx
                    obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                    -- simp [isApproximation] at h_coef
                    -- subst h_c_zero
                    apply tl_trimmed.h_approx
                    apply isApproximation_sub_zero h_tl
                    have hC : C =ᶠ[Filter.atTop] 0 := by
                      have := h_coef_trimmed ▸ coef_trimmed.h_approx C h_coef
                      exact isApproximation_nil this
                    have := Filter.EventuallyEq.mul
                      (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) hC
                    simpa using this
                  h_trimmed := tl_trimmed.h_trimmed
                }
              )
              (cons := fun (tl_deg, tl_coef) tl_tl => fun h_coef_trimmed => do
                return {
                  result := .cons (deg, coef_trimmed.result) tl
                  h_wo := by
                    intro h_wo
                    replace h_wo := wellOrdered_cons h_wo
                    apply wellOrdered.cons
                    · apply coef_trimmed.h_wo
                      exact h_wo.left
                    · exact h_wo.right.left
                    · exact h_wo.right.right
                  h_approx := by
                    intro F h_approx
                    replace h_approx := isApproximation_cons h_approx
                    obtain ⟨C, h_coef, h_comp, h_tl⟩ := h_approx
                    apply PreMS.isApproximation.cons C
                    · exact coef_trimmed.h_approx _ h_coef
                    · exact h_comp
                    · exact h_tl
                  h_trimmed := by
                    constructor
                    · exact coef_trimmed.h_trimmed
                    · rw [h_coef_trimmed]
                      apply isFlatZero_cons
                }
              )
              (by rfl)
        )

end Trimming

end PreMS

open PreMS.Trimming

def MS.isTrimmed (ms : MS) : Prop :=
  ms.val.isTrimmed

structure MS.TrimmingResult (ms : MS) where
  result : MS
  h_eq_basis : ms.basis = result.basis
  h_eq_F : ms.F = result.F
  h_trimmed : result.isTrimmed

def MS.trim (ms : MS) : TendstoM <| MS.TrimmingResult ms := do
  let r ← PreMS.trim ms.val
  return {
    result := {
      val := r.result
      basis := ms.basis
      F := ms.F
      h_wo := r.h_wo ms.h_wo
      h_approx := r.h_approx _ ms.h_approx
    }
    h_eq_basis := by rfl
    h_eq_F := by rfl
    h_trimmed := r.h_trimmed
  }

end TendstoTactic
