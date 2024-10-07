import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Asymptotics Filter

namespace TendstoTactic

def MS.wellOrderedBasis (basis : Basis) : Prop :=
  match basis with
  | [] => True
  | hd :: tl => Tendsto hd atTop atTop ∧ MS.wellOrderedBasis tl ∧ match tl with
    | [] => True
    | hd' :: _ => (Real.log ∘ hd') =o[atTop] (Real.log ∘ hd)

def MS.wellOrderedBasis_tail {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : MS.wellOrderedBasis (basis_hd :: basis_tl)) : MS.wellOrderedBasis basis_tl := by
  simp [MS.wellOrderedBasis] at h
  exact h.right.left

example : MS.wellOrderedBasis [Real.exp, id] := by
  simp [MS.wellOrderedBasis]
  constructor
  · exact Real.tendsto_exp_atTop
  · constructor
    · exact fun ⦃U⦄ a ↦ a
    · unfold Function.comp
      simp
      exact Real.isLittleO_log_id_atTop

-- to upstream? here wasn't used
universe u in
theorem List.foldl_map'' {α β γ γ' : Type u} (g : α → β) (h : γ → γ') (f : α → γ → α)
    (f' : β → γ' → β) (a : α) (l : List γ) (h_congr : ∀ x y, f' (g x) (h y) = g (f x y)) :
    (l.map h).foldl f' (g a) = g (l.foldl f a) := by
  induction l generalizing a
  · simp
  · simp [*, h_congr]

theorem MS.basis_tendsto_top {basis : Basis} (h : MS.wellOrderedBasis basis) :
    ∀ f ∈ basis, Tendsto f atTop atTop := by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp [wellOrderedBasis] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · exact h.left
    · exact ih h.right.left

theorem MS.basis_eventually_pos {basis : Basis} (h : MS.wellOrderedBasis basis) :
    ∀ᶠ x in atTop, ∀ f ∈ basis, 0 < f x := by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp [wellOrderedBasis] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    apply Filter.Eventually.and
    · exact Tendsto.eventually h.left <| eventually_gt_atTop 0
    · apply ih
      exact h.right.left

theorem MS.basis_head_eventually_pos {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h : MS.wellOrderedBasis (basis_hd :: basis_tl)) : ∀ᶠ x in atTop, 0 < basis_hd x := by
  apply Eventually.mono <| (forall_eventually_of_eventually_forall (MS.basis_eventually_pos h))
    basis_hd
  intro x h
  apply h
  simp

theorem MS.basis_IsLittleO_of_head {hd : ℝ → ℝ} {tl : Basis} (h : MS.wellOrderedBasis (hd :: tl)) :
    ∀ f ∈ tl, (Real.log ∘ f) =o[atTop] (Real.log ∘ hd) := by
  induction tl generalizing hd with
  | nil => simp
  | cons tl_hd tl_tl ih =>
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · simp [wellOrderedBasis] at h
      exact h.right.right
    · unfold wellOrderedBasis at h
      have := ih h.right.left
      unfold wellOrderedBasis at h
      simp at h
      intro f hf
      exact IsLittleO.trans (this f hf) h.right.right

theorem MS.basis_compare {f g : ℝ → ℝ} (a b : ℝ) (hf : ∀ᶠ x in atTop, 0 < f x)
    (hg : Tendsto g atTop atTop) (h : (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) (hb : 0 < b) :
    (fun x ↦ (f x)^a) =o[atTop] fun x ↦ (g x)^b := by
  obtain ⟨φ, h1, h2⟩ := IsLittleO.exists_eq_mul <| IsLittleO.const_mul_right' (c := b)
    (isUnit_iff_ne_zero.mpr hb.ne.symm) (IsLittleO.const_mul_left h a)
  have hf_exp_log : (fun x ↦ (f x)^a) =ᶠ[atTop] fun x ↦ Real.exp (a * (Real.log (f x))) := by
    simp only [EventuallyEq]
    apply Eventually.mono hf
    intro x hx
    rw [mul_comm, Real.exp_mul, Real.exp_log hx]
  have hg_exp_log : (fun x ↦ (g x)^b) =ᶠ[atTop] fun x ↦ Real.exp (b * (Real.log (g x))) := by
    simp only [EventuallyEq]
    apply Eventually.mono (Tendsto.eventually_gt_atTop hg 0)
    intro x hx
    rw [mul_comm, Real.exp_mul, Real.exp_log hx]
  apply IsLittleO.trans_eventuallyEq _ hg_exp_log.symm
  apply EventuallyEq.trans_isLittleO hf_exp_log
  simp only [Function.comp_apply] at h2
  have h2 := EventuallyEq.fun_comp h2 Real.exp
  eta_expand at h2; simp at h2
  apply EventuallyEq.trans_isLittleO h2
  apply isLittleO_of_tendsto'
  · apply Eventually.of_forall
    intro x h
    absurd h
    apply (Real.exp_pos _).ne.symm
  · simp only [← Real.exp_sub, Real.tendsto_exp_comp_nhds_zero]
    conv =>
      arg 1
      ext x
      rw [show φ x * (b * Real.log (g x)) - b * Real.log (g x) =
        b * ((φ x - 1) * Real.log (g x)) by ring]
    apply Tendsto.const_mul_atBot hb
    apply Tendsto.neg_mul_atTop (C := -1) (by simp)
    · simp_rw [show (-1 : ℝ) = 0 - 1 by simp]
      apply Tendsto.sub_const h1
    · exact Tendsto.comp Real.tendsto_log_atTop hg

-- TODO: rename
theorem PreMS.isApproximation_coef_isLittleO_head {C basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS basis_tl} (h_approx : ms.isApproximation C basis_tl)
    (h_basis : MS.wellOrderedBasis (basis_hd :: basis_tl)) :
    majorated C basis_hd 0 := by
  intro deg' h_deg
  cases basis_tl with
  | nil =>
    simp [isApproximation] at h_approx
    apply EventuallyEq.trans_isLittleO h_approx
    apply isLittleO_const_left.mpr
    right
    apply Tendsto.comp tendsto_norm_atTop_atTop
    apply Tendsto.comp (tendsto_rpow_atTop h_deg)
    simpa [MS.wellOrderedBasis] using h_basis
  | cons basis_tl_hd basis_tl_tl =>
    revert h_approx
    apply ms.casesOn
    · intro h_approx
      replace h_approx := isApproximation_nil h_approx
      apply EventuallyEq.trans_isLittleO h_approx
      apply isLittleO_const_left.mpr
      left
      rfl
    · intro (deg, coef) tl h_approx
      obtain ⟨CC, _, h_comp, _⟩ := isApproximation_cons h_approx
      apply Asymptotics.IsLittleO.trans <| h_comp (deg + 1) (by linarith)
      apply MS.basis_compare
      · apply MS.basis_head_eventually_pos
        unfold MS.wellOrderedBasis at h_basis
        exact h_basis.right.left
      · apply MS.basis_tendsto_top h_basis
        simp only [List.mem_cons, true_or]
      · simp [MS.wellOrderedBasis] at h_basis
        exact h_basis.right.right
      · exact h_deg

end TendstoTactic
