import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Tactic.Tendsto.TendstoM

namespace TendstoTactic

namespace Trimming

-- structural recursion can't be used because PreMS is a nested type
theorem PreMS.isApproximation_of_EventuallyEq {ms : PreMS} {F F' : ℝ → ℝ} {basis : Basis}
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

theorem PreMS.isApproximation_sub_zero {ms : PreMS} {F C : ℝ → ℝ} {basis : Basis}
    (h_approx : ms.isApproximation (F - C) basis) (h_C : C =ᶠ[Filter.atTop] 0) : ms.isApproximation F basis := by
  apply isApproximation_of_EventuallyEq h_approx
  have := Filter.EventuallyEq.sub (Filter.EventuallyEq.refl _ F) h_C
  simpa using this


structure PreMS.TrimmingResult (ms : PreMS) where
  result : PreMS
  h_depth : ∀ n, ms.hasDepth n → result.hasDepth n
  h_wo : ms.wellOrdered → result.wellOrdered
  h_approx : ∀ F basis, ms.isApproximation F basis → result.isApproximation F basis
  h_trimmed : result.isTrimmed

def PreMS.trim (ms : PreMS) : TendstoM <| PreMS.TrimmingResult ms := do
  match ms with
  | .nil => return {
      result := .nil
      h_depth := by intros; assumption
      h_wo := by simp [PreMS.wellOrdered]
      h_approx := by intro _ _ h; cases h; apply PreMS.isApproximation.nil; assumption
      h_trimmed := by simp [PreMS.isTrimmed]
    }
  | .const c => return {
      result := .const c
      h_depth := by intros; assumption
      h_wo := by simp [PreMS.wellOrdered]
      h_approx := by intro _ _ h; cases h; apply PreMS.isApproximation.const; assumption
      h_trimmed := by simp [PreMS.isTrimmed]
    }
  | .cons deg coef tl =>
    let coef_trimmed ← PreMS.trim coef
    match h_coef_trimmed : coef_trimmed.result with
    | .const c =>
      match ← TendstoTactic.runOracle c with
      | .zero h_c_zero =>
        let tl_trimmed ← PreMS.trim tl.get
        return {
          result := tl_trimmed.result
          h_depth := by intro _ h; cases h; apply tl_trimmed.h_depth; assumption
          h_wo := by intro h_wo; simp [PreMS.wellOrdered] at h_wo; exact tl_trimmed.h_wo h_wo.right.left
          h_approx := by
            intro F basis h_approx
            cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
            cases h_coef_trimmed ▸ (coef_trimmed.h_approx _ _ h_coef)
            rename_i h_C
            simp_rw [h_c_zero] at h_C
            apply isApproximation_sub_zero (tl_trimmed.h_approx _ _ h_tl)
            have := Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) h_C
            simpa using this
          h_trimmed := tl_trimmed.h_trimmed
        }
      | .pos h_c_pos => return {
          result := .cons deg coef_trimmed.result tl
          h_depth := by
            intro _ h_depth
            cases h_depth with | cons _ _ _ _ h_coef h_tl =>
            apply PreMS.hasDepth.cons
            · exact coef_trimmed.h_depth _ h_coef
            · assumption
          h_wo := by
            intro h_wo
            simp [PreMS.wellOrdered] at h_wo
            unfold PreMS.wellOrdered
            constructor
            · exact coef_trimmed.h_wo h_wo.left
            · exact h_wo.right
          h_approx := by
            intro F basis h_approx
            cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
            apply PreMS.isApproximation.cons
            exacts [coef_trimmed.h_approx _ _ h_coef, h_tl, h_comp]
          h_trimmed := by
            simp [PreMS.isTrimmed]
            constructor
            · exact coef_trimmed.h_trimmed
            · simp [h_coef_trimmed, PreMS.isFlatZero, h_c_pos.ne.symm]
        }
      | .neg h_c_neg => return { -- copypaste from pos
          result := .cons deg coef_trimmed.result tl
          h_depth := by
            intro _ h_depth
            cases h_depth with | cons _ _ _ _ h_coef h_tl =>
            apply PreMS.hasDepth.cons
            · exact coef_trimmed.h_depth _ h_coef
            · assumption
          h_wo := by
            intro h_wo
            simp [PreMS.wellOrdered] at h_wo
            unfold PreMS.wellOrdered
            constructor
            · exact coef_trimmed.h_wo h_wo.left
            · exact h_wo.right
          h_approx := by
            intro F basis h_approx
            cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
            apply PreMS.isApproximation.cons
            exacts [coef_trimmed.h_approx _ _ h_coef, h_tl, h_comp]
          h_trimmed := by
            simp [PreMS.isTrimmed]
            constructor
            · exact coef_trimmed.h_trimmed
            · simp [h_coef_trimmed, PreMS.isFlatZero, h_c_neg.ne]
        }
    | .nil => -- copy from const zero
      let tl_trimmed ← PreMS.trim tl.get
        return {
          result := tl_trimmed.result
          h_depth := by intro _ h; cases h; apply tl_trimmed.h_depth; assumption
          h_wo := by intro h_wo; simp [PreMS.wellOrdered] at h_wo; exact tl_trimmed.h_wo h_wo.right.left
          h_approx := by
            intro F basis h_approx
            cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
            cases h_coef_trimmed ▸ (coef_trimmed.h_approx _ _ h_coef)
            rename_i h_coef
            apply isApproximation_sub_zero (tl_trimmed.h_approx _ _ h_tl)
            have := Filter.EventuallyEq.mul (Filter.EventuallyEq.refl _ (fun x ↦ basis_hd x ^ deg)) h_coef
            simpa using this
          h_trimmed := tl_trimmed.h_trimmed
        }
    | .cons _ _ _ => return { -- copypaste from pos
        result := .cons deg coef_trimmed.result tl
        h_depth := by
          intro _ h_depth
          cases h_depth with | cons _ _ _ _ h_coef h_tl =>
          apply PreMS.hasDepth.cons
          · exact coef_trimmed.h_depth _ h_coef
          · assumption
        h_wo := by
          intro h_wo
          simp [PreMS.wellOrdered] at h_wo
          unfold PreMS.wellOrdered
          constructor
          · exact coef_trimmed.h_wo h_wo.left
          · exact h_wo.right
        h_approx := by
          intro F basis h_approx
          cases h_approx with | cons _ _ _ _ C basis_hd basis_tl h_coef h_tl h_comp =>
          apply PreMS.isApproximation.cons
          exacts [coef_trimmed.h_approx _ _ h_coef, h_tl, h_comp]
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

def MS.trim (ms : MS) : TendstoM <| MS.TrimmingResult ms := do
  let r ← PreMS.trim ms.val
  return {
    result := {
      val := r.result
      basis := ms.basis
      F := ms.F
      h_depth := r.h_depth _ ms.h_depth
      h_wo := r.h_wo ms.h_wo
      h_approx := r.h_approx _ _ ms.h_approx
    }
    h_eq_basis := by rfl
    h_eq_F := by rfl
    h_trimmed := r.h_trimmed
  }


end Trimming

end TendstoTactic
