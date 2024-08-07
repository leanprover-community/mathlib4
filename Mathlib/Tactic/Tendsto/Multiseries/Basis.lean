import Mathlib.Tactic.Tendsto.Multiseries.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

open Asymptotics Filter

namespace TendstoTactic

def MS.wellOrderedBasis (basis : List (ℝ → ℝ)) : Prop :=
  match basis with
  | [] => True
  | hd :: tl => Tendsto hd atTop atTop ∧ MS.wellOrderedBasis tl ∧ match tl with
    | [] => True
    | hd' :: _ => (Real.log ∘ hd') =o[atTop] (Real.log ∘ hd)

example : MS.wellOrderedBasis [Real.exp, id] := by
  simp [MS.wellOrderedBasis]
  constructor
  · exact Real.tendsto_exp_atTop
  · constructor
    · exact fun ⦃U⦄ a ↦ a
    · simp [Function.comp]
      exact Real.isLittleO_log_id_atTop

-- to upstream? here wasn't used
universe u in
theorem List.foldl_map'' {α β γ γ' : Type u} (g : α → β) (h : γ → γ') (f : α → γ → α) (f' : β → γ' → β) (a : α) (l : List γ)
    (h_congr : ∀ x y, f' (g x) (h y) = g (f x y)) :
    (l.map h).foldl f' (g a) = g (l.foldl f a) := by
  induction l generalizing a
  · simp
  · simp [*, h_congr]

theorem MS.basis_tendsto_top {basis : List (ℝ → ℝ)} (h : MS.wellOrderedBasis basis) :
    ∀ f ∈ basis, Tendsto f atTop atTop := by
  induction basis with
  | nil => simp
  | cons hd tl ih =>
    simp [wellOrderedBasis] at h
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · exact h.left
    · exact ih h.right.left

theorem MS.basis_eventually_pos {basis : List (ℝ → ℝ)} (h : MS.wellOrderedBasis basis) :
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

theorem MS.basis_head_eventually_pos {basis_hd : ℝ → ℝ} {basis_tl : List (ℝ → ℝ)}
    (h : MS.wellOrderedBasis (basis_hd :: basis_tl)) : ∀ᶠ x in atTop, 0 < basis_hd x := by
  apply Eventually.mono <| (forall_eventually_of_eventually_forall (MS.basis_eventually_pos h)) basis_hd
  intro x h
  apply h
  simp

theorem MS.basis_IsLittleO_of_head {hd : ℝ → ℝ} {tl : List (ℝ → ℝ)} (h : MS.wellOrderedBasis (hd :: tl)) :
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

theorem MS.basis_compare {f g : ℝ → ℝ} (a b : ℝ) (hf : ∀ᶠ x in atTop, 0 < f x) (hg : Tendsto g atTop atTop)
    (h : (Real.log ∘ f) =o[atTop] (Real.log ∘ g)) (hb : 0 < b) :
    (fun x ↦ (f x)^a) =o[atTop] fun x ↦ (g x)^b := by
  obtain ⟨φ, h1, h2⟩ := IsLittleO.exists_eq_mul <| IsLittleO.const_mul_right' (c := b) (isUnit_iff_ne_zero.mpr hb.ne.symm)
    (IsLittleO.const_mul_left h a)
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
  · apply eventually_of_forall
    intro x h
    absurd h
    apply (Real.exp_pos _).ne.symm
  · simp only [← Real.exp_sub, Real.tendsto_exp_comp_nhds_zero]
    conv =>
      arg 1
      ext x
      rw [show φ x * (b * Real.log (g x)) - b * Real.log (g x) = b * ((φ x - 1) * Real.log (g x)) by ring_nf]
    apply Tendsto.const_mul_atBot hb
    apply Tendsto.neg_mul_atTop (C := -1) (by simp)
    · simp_rw [show (-1 : ℝ) = 0 - 1 by simp]
      apply Tendsto.sub_const h1
    · exact Tendsto.comp Real.tendsto_log_atTop hg

-- to upstream
lemma MS.compare_self {f : ℝ → ℝ} {e1 e2 : ℝ} (h1 : Tendsto f atTop atTop) (h2 : e1 < e2) :
    (fun x ↦ (f x)^e1) =o[atTop] fun x ↦ (f x)^e2 := by
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun x ↦ f x ^ e1 / f x ^ e2) =ᶠ[atTop] fun x ↦ (f x)^(e1 - e2) := by
      apply Eventually.mono <| Tendsto.eventually_gt_atTop h1 0
      intro x h
      simp only
      rw [← Real.rpow_sub h]
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun x ↦ f x ^ (e1 - e2)) = ((fun x ↦ x^(-(e2 - e1))) ∘ f) by ext; simp]
    apply Tendsto.comp _ h1
    apply tendsto_rpow_neg_atTop
    linarith
  · apply Eventually.mono <| Tendsto.eventually_gt_atTop h1 0
    intro x h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

theorem PreMS.isApproximation_coef_isLittleO_head {c : PreMS} {C basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {deg : ℝ} (h_deg : 0 < deg) (h_approx : c.isApproximation C basis_tl) (h_basis : MS.wellOrderedBasis (basis_hd :: basis_tl)) :
    C =o[atTop] fun x ↦ (basis_hd x)^deg := by
  cases h_approx with
  | const c _ hC =>
    apply EventuallyEq.trans_isLittleO hC
    apply isLittleO_const_left.mpr
    right
    apply Tendsto.comp tendsto_norm_atTop_atTop
    apply Tendsto.comp (tendsto_rpow_atTop h_deg)
    simpa [MS.wellOrderedBasis] using h_basis
  | nil _ _ hC =>
    apply EventuallyEq.trans_isLittleO hC
    apply isLittleO_const_left.mpr
    left
    rfl
  | cons coef_deg coef_coef coef_tl _ CC basis_tl_hd basis_tl_tl h_coef_coef h_coef_tl h_coef_comp =>
    apply Asymptotics.IsLittleO.trans <| h_coef_comp (coef_deg + 1) (by linarith)
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
