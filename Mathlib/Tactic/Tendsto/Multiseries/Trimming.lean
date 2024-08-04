import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.TendstoM

namespace TendstoTactic

namespace Trimming

structure PreMS.TrimmingResult (ms : PreMS) (n : ℕ) (F : ℝ → ℝ) (basis : Basis) where
  result : PreMS
  h_depth : result.hasDepth n
  h_wo : result.wellOrdered
  h_approx : result.isApproximation F basis
  h_trimmed : result.isTrimmed

-- structural recursion can't be used because PreMS is a nested type
noncomputable def PreMS.isApproximation_of_EventuallyEq {ms : PreMS} {F F' : ℝ → ℝ} {basis : Basis}
    (h_approx : ms.isApproximation F basis) (h_equiv : F =ᶠ[Filter.atTop] F') : ms.isApproximation F' basis := by
  induction ms using PreMS.rec' generalizing F F' with
  | nil =>
    cases h_approx with | nil _ _ h =>
    apply PreMS.isApproximation.nil
    exact Filter.EventuallyEq.trans h_equiv.symm h
  | const =>
    cases h_approx with | const _ _ h =>
    apply PreMS.isApproximation.const
    exact Filter.EventuallyEq.trans h_equiv.symm h
  | cons deg coef tl coef_ih tl_ih =>
    cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
    apply PreMS.isApproximation.cons
    · exact h_coef
    · apply tl_ih h_tl
      apply Filter.EventuallyEq.sub h_equiv (by apply Filter.EventuallyEq.refl)
    · intros
      apply Filter.EventuallyEq.trans_isLittleO h_equiv.symm (h_comp _ _)
      assumption

noncomputable def PreMS.isApproximation_sub_zero {ms : PreMS} {F C : ℝ → ℝ} {basis : Basis}
    (h_approx : ms.isApproximation (F - C) basis) (h_C : C =ᶠ[Filter.atTop] 0) : ms.isApproximation F basis := by
  apply isApproximation_of_EventuallyEq h_approx
  have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ F) h_C
  simpa using this

noncomputable def PreMS.trim {ms : PreMS} {n : ℕ} {F : ℝ → ℝ} {basis : Basis}
    (h_depth : ms.hasDepth n) (h_wo : ms.wellOrdered) (h_approx : ms.isApproximation F basis) :
    TendstoM <| PreMS.TrimmingResult ms n F basis := do
  match ms, basis, n, h_approx with
  | .nil, _, _, .nil _ _ h => return {
      result := .nil
      h_depth := PreMS.hasDepth.nil _
      h_wo := by simp [PreMS.wellOrdered]
      h_approx := PreMS.isApproximation.nil _ _ h
      h_trimmed := by simp [PreMS.isTrimmed]
    }
  | .const c, [], 0, .const _ _ h => return {
      result := .const c
      h_depth := PreMS.hasDepth.const _
      h_wo := by simp [PreMS.wellOrdered]
      h_approx := PreMS.isApproximation.const _ _ h
      h_trimmed := by simp [PreMS.isTrimmed]
    }
  | .cons deg coef tl, .cons basis_hd basis_tl, m + 1, .cons _ _ _ _ C _ _ h_coef h_tl h_comp =>
    let coef_trimmed ← PreMS.trim (by cases h_depth; assumption)
      (by simp [PreMS.wellOrdered] at h_wo; exact h_wo.left) h_coef
    match h_coef_trimmed : coef_trimmed.result with
    | .const c =>
      match ← TendstoTactic.runOracle c with
      | .zero h_c_zero =>
        let tl_trimmed ← PreMS.trim (by cases h_depth; assumption)
          (by simp [PreMS.wellOrdered] at h_wo; exact h_wo.right.left) h_tl
        return {
          result := tl_trimmed.result
          h_trimmed := tl_trimmed.h_trimmed
          h_depth := tl_trimmed.h_depth
          h_wo := tl_trimmed.h_wo
          h_approx := by
            cases h_coef_trimmed ▸ coef_trimmed.h_approx
            rename_i h_C
            simp_rw [h_c_zero] at h_C
            apply isApproximation_sub_zero tl_trimmed.h_approx
            have := Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) h_C
            simpa using this
        }
      | .pos h_c_pos => return {
          result := .cons deg coef_trimmed.result tl
          h_depth := by
            cases h_depth
            apply PreMS.hasDepth.cons
            · exact coef_trimmed.h_depth
            · assumption
          h_wo := by
            unfold PreMS.wellOrdered
            constructor
            · exact coef_trimmed.h_wo
            · unfold PreMS.wellOrdered at h_wo
              exact h_wo.right
          h_approx := by
            apply PreMS.isApproximation.cons
            exacts [coef_trimmed.h_approx, h_tl, h_comp]
          h_trimmed := by
            simp [PreMS.isTrimmed]
            constructor
            · exact coef_trimmed.h_trimmed
            · simp [h_coef_trimmed, PreMS.isFlatZero, h_c_pos.ne.symm]
        }
      | .neg h_c_neg => return { -- same as pos
          result := .cons deg coef_trimmed.result tl
          h_depth := by
            cases h_depth
            apply PreMS.hasDepth.cons
            · exact coef_trimmed.h_depth
            · assumption
          h_wo := by
            unfold PreMS.wellOrdered
            constructor
            · exact coef_trimmed.h_wo
            · unfold PreMS.wellOrdered at h_wo
              exact h_wo.right
          h_approx := by
            apply PreMS.isApproximation.cons
            exacts [coef_trimmed.h_approx, h_tl, h_comp]
          h_trimmed := by
            simp [PreMS.isTrimmed]
            constructor
            · exact coef_trimmed.h_trimmed
            · simp [h_coef_trimmed, PreMS.isFlatZero, h_c_neg.ne]
        }
    | .nil =>
      let tl_trimmed ← PreMS.trim (by cases h_depth; assumption)
          (by simp [PreMS.wellOrdered] at h_wo; exact h_wo.right.left) h_tl
      return {
        result := tl_trimmed.result
        h_depth := tl_trimmed.h_depth
        h_wo := tl_trimmed.h_wo
        h_approx := by
          cases h_coef_trimmed ▸ coef_trimmed.h_approx
          rename_i h_C
          apply isApproximation_sub_zero tl_trimmed.h_approx
          have := Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) h_C
          simpa using this
        h_trimmed := tl_trimmed.h_trimmed
      }
    | .cons _ _ _ => return {
        result := .cons deg coef_trimmed.result tl
        h_depth := by
          cases h_depth
          apply PreMS.hasDepth.cons
          · exact coef_trimmed.h_depth
          · assumption
        h_wo := by
          unfold PreMS.wellOrdered
          constructor
          · exact coef_trimmed.h_wo
          · unfold PreMS.wellOrdered at h_wo
            exact h_wo.right
        h_approx := by
          apply PreMS.isApproximation.cons
          exacts [coef_trimmed.h_approx, h_tl, h_comp]
        h_trimmed := by
          simp [PreMS.isTrimmed]
          constructor
          · exact coef_trimmed.h_trimmed
          · simp [h_coef_trimmed, PreMS.isFlatZero]
      }

structure MS.TrimmingResult (ms : MS) where
  result : MS
  h_eq_basis : ms.basis = result.basis
  h_eq_F : ms.F = result.F
  h_trimmed : result.isTrimmed

noncomputable def MS.trim (ms : MS) : TendstoM <| MS.TrimmingResult ms := do
  let r ← PreMS.trim ms.h_depth ms.h_wo ms.h_approx
  return {
    result := {
      val := r.result
      basis := ms.basis
      F := ms.F
      h_depth := r.h_depth
      h_wo := r.h_wo
      h_approx := r.h_approx
    }
    h_eq_basis := by rfl
    h_eq_F := by rfl
    h_trimmed := r.h_trimmed
  }


end Trimming

end TendstoTactic
