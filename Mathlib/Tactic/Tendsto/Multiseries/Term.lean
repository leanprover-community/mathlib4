/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic.Tendsto.Multiseries.Basis
import Mathlib.Tactic.Tendsto.TendstoM

/-!
Here we find the limit of the term of the form `coef * b1(x)^d1 * b2(x)^d2 * ...`
where `[b1, b2, ...]` is well-formed basis and `coef` is real constant.
-/

namespace TendstoTactic

open Asymptotics Filter

structure MS.Term where
  coef : ℝ
  exps : List ℝ

namespace MS.Term

noncomputable def toFun (t : MS.Term) (basis : List (ℝ → ℝ)) : ℝ → ℝ :=
  fun x => t.exps.zip basis |>.foldl (init := t.coef) fun acc (exp, f) =>
    acc * (f x)^exp

-- TODO: rename
theorem fun_mul (li : List (ℝ × (ℝ → ℝ))) (coef : ℝ) (x : ℝ) :
    (li.foldl (init := coef) fun acc (exp, f) => acc * (f x)^exp) =
    coef * (li.foldl (init := 1) fun acc (exp, f) => acc * (f x)^exp) := by
  induction li generalizing coef with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, one_mul] at *
    rw [ih (coef * hd.2 x ^ hd.1), ih (hd.2 x ^ hd.1)]
    ring

theorem zero_coef_fun {t : MS.Term} (basis : List (ℝ → ℝ)) (h_coef : t.coef = 0) :
    t.toFun basis = 0 := by
  unfold toFun
  ext
  rw [fun_mul, h_coef]
  simp

theorem neg_coef {t : MS.Term} {basis : List (ℝ → ℝ)} :
    t.toFun basis = fun x => -(MS.Term.mk (-t.coef) t.exps).toFun basis x := by
  unfold MS.Term.toFun
  ext
  rw [fun_mul (coef := t.coef), fun_mul (coef := -t.coef)]
  simp

noncomputable def inv (t : MS.Term) : MS.Term :=
  ⟨t.coef⁻¹, t.exps.map fun exp => -exp⟩

theorem inv_length {t : MS.Term} : t.inv.exps.length = t.exps.length := by
  simp [inv]

theorem fun_inv {t : MS.Term} {basis : Basis} (h_basis : MS.WellOrderedBasis basis) :
    (fun x ↦ (t.toFun basis x)⁻¹) =ᶠ[atTop] fun x ↦ t.inv.toFun basis x := by
  unfold toFun
  simp [inv]
  induction t.exps generalizing basis with
  | nil => simp
  | cons hd tl ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      unfold EventuallyEq
      specialize ih (MS.WellOrderedBasis_tail h_basis)
      unfold EventuallyEq at ih
      apply Eventually.mono ((MS.basis_head_eventually_pos h_basis).and ih)
      rintro x ⟨h_pos, ih⟩
      simp at ih
      simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons]
      simp [MS.WellOrderedBasis] at h_basis
      conv =>
        congr <;> rw [fun_mul]
      simp

      conv at ih =>
        congr <;> rw [fun_mul]
      simp at ih

      -- why can't use ring?
      conv =>
        rhs
        lhs
        rw [mul_comm]

      conv =>
        rhs
        rw [mul_assoc]
        rw [← ih]
        rw [← mul_assoc]
        lhs
        rw [mul_comm]

      conv =>
        rhs
        rw [mul_assoc]
        rw [Real.rpow_neg (h_pos.le)]

theorem fun_pos {t : MS.Term} {basis : List (ℝ → ℝ)}
    (h_basis : MS.WellOrderedBasis basis) (h_coef : 0 < t.coef) :
    ∀ᶠ x in atTop, 0 < t.toFun basis x := by
  apply Eventually.mono <| MS.basis_eventually_pos h_basis
  intro x hx
  have hx' : ∀ hd ∈ t.exps.zip basis, 0 < hd.2 x := by
    intro hd h_hd
    exact hx _ (List.of_mem_zip h_hd).right
  simp [toFun]
  generalize t.coef = c at *
  generalize t.exps.zip basis = li at *
  induction li generalizing c with
  | nil => simpa
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · apply mul_pos h_coef
      apply Real.rpow_pos_of_pos
      apply hx'
      simp
    · intro hd h_hd
      apply hx'
      simp; right; assumption

theorem fun_log {t : MS.Term} {basis : List (ℝ → ℝ)}
    (h_coef : 0 < t.coef) (h_basis : MS.WellOrderedBasis basis) :
    Real.log ∘ t.toFun basis =ᶠ[atTop]
      (fun x => t.exps.zip basis |>.foldl (init := Real.log t.coef) fun acc (exp, f) =>
        acc + exp * Real.log ((f x))) := by
  have h_pos : ∀ᶠ x in atTop, ∀ hd ∈ t.exps.zip basis, 0 < hd.2 x := by
    -- TODO : rewrite using `MS.basis_eventually_pos`
    have h_pos : ∀ hd ∈ t.exps.zip basis, ∀ᶠ x in atTop, 0 < hd.2 x := by
      have h' : ∀ hd ∈ t.exps.zip basis, Tendsto hd.2 atTop atTop := by
        intro hd h_hd
        apply MS.basis_tendsto_top h_basis
        exact (List.of_mem_zip h_hd).right
      intro hd h_hd
      exact Tendsto.eventually (h' hd h_hd) <| eventually_gt_atTop 0
    generalize t.exps.zip basis = li at *
    induction li with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.mem_cons, forall_eq_or_imp]
      apply Filter.Eventually.and
      · apply h_pos
        simp
      · apply ih
        intro hd h_hd
        apply h_pos
        simp only [List.mem_cons]
        right; exact h_hd
  unfold toFun
  simp only [EventuallyEq]
  apply Eventually.mono h_pos
  clear h_pos
  intro x hf
  generalize t.exps.zip basis = li at *
  generalize t.coef = c at *
  induction li generalizing c with
  | nil => simp [Function.comp, Real.exp_log h_coef]
  | cons hd tl tl_ih =>
    unfold List.foldl
    simp only [Function.comp_apply]
    have hf' : 0 < hd.2 x := by simp [hf]
    conv =>
      rhs
      lhs
      rw [← Real.log_rpow hf', ← Real.log_mul h_coef.ne.symm (Real.rpow_pos_of_pos hf' _).ne.symm]
    apply tl_ih
    · intro hd hd_mem
      apply hf hd
      simp [hd_mem]
    · nlinarith [Real.rpow_pos_of_pos hf' hd.1]

theorem trim_zero_head (coef : ℝ) {exp : ℝ} {tl : List ℝ} {basis : List (ℝ → ℝ)}
    (h_length : (exp :: tl).length = basis.length) (h_exp : exp = 0) :
    let t : MS.Term := ⟨coef, exp :: tl⟩;
    t.toFun basis = (MS.Term.mk coef tl).toFun basis.tail! := by
  unfold toFun
  cases basis with
  | nil => simp at h_length
  | cons basis_hd basis_tl => simp [h_exp]

theorem IsEquivalent_of_nonzero_head {coef exp : ℝ} {tl : List ℝ} {basis : List (ℝ → ℝ)}
    (h_length : (exp :: tl).length = basis.length) (h_basis : MS.WellOrderedBasis basis)
    (h_coef : 0 < coef) (h_exp : exp ≠ 0) :
    let t : MS.Term := ⟨coef, exp :: tl⟩;
    Real.log ∘ t.toFun basis ~[atTop] fun x => Real.log coef + exp * Real.log (basis.head! x) := by
  intro t
  apply Asymptotics.IsEquivalent.congr_left _ <| (MS.Term.fun_log (t := t) h_coef h_basis).symm
  cases basis with
  | nil => simp at h_length
  | cons basis_hd basis_tl =>
    have h_pull_init : ∀ (li : List (ℝ × (ℝ → ℝ))) (init : ℝ) (x : ℝ),
        (li.foldl (init := init) (fun acc (exp, f) => acc + exp * Real.log (f x))) =
        init + (li.foldl (init := 0) (fun acc (exp, f) => acc + exp * Real.log (f x))) := by
      intro li init x
      induction li generalizing init with
      | nil => simp
      | cons hd tl ih =>
        simp at ih ⊢
        rw [ih (hd.1 * Real.log (hd.2 x)), ih (init + hd.1 * Real.log (hd.2 x))]
        ring
    simp
    simp at h_pull_init
    conv =>
      lhs
      ext x
      rw [h_pull_init]
    simp only [IsEquivalent]
    conv =>
      lhs
      ext x
      simp

    have h_little : ∀ hd ∈ tl.zip basis_tl, (Real.log ∘ hd.2) =o[atTop] (Real.log ∘ basis_hd) := by
      intro hd h_hd
      apply MS.basis_IsLittleO_of_head h_basis
      exact (List.of_mem_zip h_hd).right

    have h_tendsto : ∀ hd ∈ tl.zip basis_tl, Tendsto hd.2 atTop atTop := by
      intro hd h_hd
      apply MS.basis_tendsto_top h_basis
      simp; right
      exact (List.of_mem_zip h_hd).right

    generalize tl.zip basis_tl = li at *
    induction li with
    | nil => simp
    | cons tl_hd tl_tl ih =>
      simp
      conv =>
        lhs
        ext x
        rw [h_pull_init]
      apply IsLittleO.add
      · apply IsLittleO.const_mul_left
        have : (fun _ ↦ Real.log coef) =o[atTop] fun x ↦ exp * Real.log (basis_hd x) := by
          apply IsLittleO.const_mul_right' (by simp [h_exp])
          apply Asymptotics.isLittleO_const_left.mpr
          right
          apply Filter.Tendsto.comp tendsto_norm_atTop_atTop
          rw [← Function.comp_def]
          apply Filter.Tendsto.comp Real.tendsto_log_atTop
          simp [MS.WellOrderedBasis] at h_basis
          exact h_basis.right.left
        rw [show (fun x ↦ Real.log coef + exp * Real.log (basis_hd x)) =
          (fun _ ↦ Real.log coef) + (fun x ↦ exp * Real.log (basis_hd x)) by rfl]
        apply Asymptotics.IsLittleO.trans_isTheta _ (Asymptotics.IsLittleO.right_isTheta_add this)
        apply IsLittleO.const_mul_right' (by simp [h_exp])
        apply h_little
        simp
      · apply ih
        · intro hd h_hd
          apply h_little; right; assumption
        · intro hd h_hd
          apply h_tendsto; right; assumption


theorem tendsto_top {coef exp : ℝ} {tl : List ℝ} {basis : List (ℝ → ℝ)}
    (h_length : (exp :: tl).length = basis.length) (h_basis : MS.WellOrderedBasis basis)
    (h_coef : 0 < coef) (h_exp : 0 < exp) :
    let t : MS.Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop atTop := by
  intro t
  have h_t_equiv : Real.log ∘ t.toFun basis ~[atTop]
      fun x => Real.log coef + exp * Real.log (basis.head! x) :=
    MS.Term.IsEquivalent_of_nonzero_head h_length h_basis h_coef h_exp.ne.symm
  suffices h_log : Tendsto (Real.log ∘ t.toFun basis) atTop atTop by
    have := Tendsto.comp Real.tendsto_exp_atTop h_log
    apply Filter.Tendsto.congr' _ this
    simp only [EventuallyEq]
    apply Eventually.mono <| MS.Term.fun_pos (t := t) h_basis h_coef
    intro x hx
    simp [Real.exp_log hx]

  apply IsEquivalent.tendsto_atTop h_t_equiv.symm
  apply Filter.tendsto_atTop_add_const_left
  apply Filter.Tendsto.const_mul_atTop h_exp
  rw [← Function.comp_def]
  apply Tendsto.comp Real.tendsto_log_atTop
  apply MS.basis_tendsto_top h_basis
  cases basis
  · simp at h_length
  · simp

theorem tendsto_bot {coef exp : ℝ} {tl : List ℝ} {basis : List (ℝ → ℝ)}
    (h_length : (exp :: tl).length = basis.length) (h_basis : MS.WellOrderedBasis basis)
    (h_coef : coef < 0) (h_exp : 0 < exp) :
    let t : MS.Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop atBot := by
  intro t
  rw [neg_coef (t := t)]
  apply Filter.tendsto_neg_atBot_iff.mpr
  apply MS.Term.tendsto_top h_length h_basis _ h_exp
  linarith

-- todo: it's copypaste from `MS.Term.tendsto_top`
lemma tendsto_zero_aux1 {coef exp : ℝ} {tl : List ℝ} {basis : List (ℝ → ℝ)}
    (h_length : (exp :: tl).length = basis.length) (h_basis : MS.WellOrderedBasis basis)
    (h_coef : 0 < coef) (h_exp : exp < 0) :
    let t : MS.Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop (nhds 0) := by
  intro t
  have h_t_equiv : Real.log ∘ t.toFun basis ~[atTop]
      fun x => Real.log coef + exp * Real.log (basis.head! x) :=
    MS.Term.IsEquivalent_of_nonzero_head h_length h_basis h_coef h_exp.ne
  suffices h_log : Tendsto (Real.log ∘ t.toFun basis) atTop atBot by
    have := Tendsto.comp Real.tendsto_exp_atBot h_log
    apply Filter.Tendsto.congr' _ this
    simp only [EventuallyEq]
    apply Eventually.mono <| MS.Term.fun_pos (t := t) h_basis h_coef
    intro x hx
    simp [Real.exp_log hx]

  apply IsEquivalent.tendsto_atBot h_t_equiv.symm
  apply Filter.tendsto_atBot_add_const_left
  apply (Filter.tendsto_neg_atTop_iff).mp
  simp_rw [← neg_mul]
  apply Filter.Tendsto.const_mul_atTop (by linarith)
  rw [← Function.comp_def]
  apply Tendsto.comp Real.tendsto_log_atTop
  apply MS.basis_tendsto_top h_basis
  cases basis
  · simp at h_length
  · simp

lemma tendsto_zero_aux2 {coef exp : ℝ} {tl : List ℝ} {basis : List (ℝ → ℝ)}
    (h_length : (exp :: tl).length = basis.length)
    (h_coef : coef < 0) (h_exp : exp < 0) (h_basis : MS.WellOrderedBasis basis) :
    let t : MS.Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop (nhds 0) := by
  intro t
  rw [neg_coef (t := t), ← neg_zero]
  apply Filter.Tendsto.neg
  apply MS.Term.tendsto_zero_aux1 h_length h_basis _ h_exp
  linarith

theorem tendsto_zero (coef : ℝ) {exp : ℝ} {tl : List ℝ} {basis : List (ℝ → ℝ)}
    (h_length : (exp :: tl).length = basis.length)
    (h_exp : exp < 0) (h_basis : MS.WellOrderedBasis basis) :
    let t : MS.Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop (nhds 0) := by
  intro t
  rcases lt_trichotomy coef 0 with (h_coef | h_coef | h_coef)
  · apply MS.Term.tendsto_zero_aux2 <;> assumption
  · rw [MS.Term.zero_coef_fun (t := t) basis h_coef]
    apply tendsto_const_nhds
  · apply MS.Term.tendsto_zero_aux1 <;> assumption

theorem nil_tendsto_const (coef : ℝ) (basis : List (ℝ → ℝ)) :
    let t : MS.Term := ⟨coef, []⟩;
    Tendsto (t.toFun basis) atTop (nhds coef) := by
  eta_expand
  simp [toFun]

noncomputable def findLimit (t : MS.Term) (basis : List (ℝ → ℝ))
    (h_length : t.exps.length = basis.length) (h_basis : MS.WellOrderedBasis basis) :
    FindLimitResult (t.toFun basis) :=
  match h_exps : t.exps with
  | [] => .fin t.coef (by {
      have := MS.Term.nil_tendsto_const t.coef basis
      cases t
      simp_all
    })
  | exp :: tl =>
    if h_exp : 0 < exp then
      if h_coef : 0 < t.coef then
        .top (by {
          have := MS.Term.tendsto_top (h_exps ▸ h_length) h_basis h_coef h_exp
          cases t
          simp_all
        })
      else if h_coef : t.coef < 0 then
        .bot (by {
          have := MS.Term.tendsto_bot (h_exps ▸ h_length) h_basis h_coef h_exp
          cases t
          simp_all
        })
      else
        have h_coef : t.coef = 0 := by linarith
        .fin 0 (by {
          rw [MS.Term.zero_coef_fun basis h_coef]
          apply tendsto_const_nhds
        })
    else if h_exp : exp < 0 then
      .fin 0 (by {
        have := MS.Term.tendsto_zero t.coef (h_exps ▸ h_length) h_exp
        cases t
        simp_all
      })
    else
      have h_exp : exp = 0 := by linarith
      match basis with
      | [] => by simp [h_exps] at h_length
      | basis_hd :: basis_tl =>

        let r := MS.Term.findLimit ⟨t.coef, tl⟩ basis_tl
          (by simpa [h_exps] using h_length) (by simp [MS.WellOrderedBasis] at h_basis; tauto)
        match r with
        | .top p => .top (by {
            have := MS.Term.trim_zero_head t.coef (h_exps ▸ h_length) h_exp
            cases t
            simp at h_exps
            simp_all
          })
        | .bot p => .bot (by {
            have := MS.Term.trim_zero_head t.coef (h_exps ▸ h_length) h_exp
            cases t
            simp at h_exps
            simp_all
          })
        | .fin c p => .fin c (by {
            have := MS.Term.trim_zero_head t.coef (h_exps ▸ h_length) h_exp
            cases t
            simp at h_exps
            simp_all
          })

-------------------------------

theorem tail_fun_IsLittleO_head {t : MS.Term} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_length : t.exps.length = basis_tl.length)
    (h_basis : MS.WellOrderedBasis (basis_hd :: basis_tl)) {exp : ℝ} (h_exp : 0 < exp) :
    t.toFun basis_tl =o[atTop] fun x ↦ (basis_hd x)^exp := by
  unfold toFun
  simp only
  generalize t.exps = exps at *
  induction exps generalizing basis_hd basis_tl with
  | nil =>
    simp
    right
    apply Tendsto.comp tendsto_norm_atTop_atTop
    apply Tendsto.comp (tendsto_rpow_atTop h_exp)
    simp [MS.WellOrderedBasis] at h_basis
    exact h_basis.right.left
  | cons exps_hd exps_tl ih =>
    cases basis_tl with
    | nil =>
      simp at h_length
    | cons basis_tl_hd basis_tl_tl =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      unfold MS.WellOrderedBasis at h_basis
      simp only [List.length_cons, add_left_inj] at h_length
      specialize ih (MS.WellOrderedBasis_tail h_basis) h_length
      conv at ih =>
        lhs
        ext
        rw [fun_mul]
        simp only
      conv =>
        lhs
        ext
        rw [fun_mul]
        lhs; rw [mul_comm]
      conv =>
        lhs
        ext
        rw [mul_assoc]
      simp only

      -- TODO: rewrite it using proved lemmas
      have h_comp : ∀ (a b : ℝ), (0 < a) → (fun x ↦ (basis_tl_hd x)^b) =o[atTop]
          fun x ↦ (basis_hd x)^a := by
        intro a b ha
        simp [MS.WellOrderedBasis] at h_basis
        apply MS.basis_compare b a (Tendsto.eventually_gt_atTop h_basis.right.right.left 0)
          h_basis.right.left h_basis.left.left.left ha

      have ih := IsLittleO.trans ih (h_comp (exp / 2) exp (by linarith))

      have aux : (fun x ↦ (basis_hd x)^exp) =ᶠ[atTop]
          fun x ↦ (basis_hd x)^(exp / 2) * (basis_hd x)^(exp / 2) := by
        apply Eventually.mono <| MS.basis_head_eventually_pos h_basis
        intro x h
        simp only
        rw [← Real.rpow_add h]
        ring_nf
      apply IsLittleO.trans_eventuallyEq _ aux.symm
      apply IsLittleO.mul
      · apply h_comp _ _ (by linarith)
      · exact ih

end MS.Term

end TendstoTactic
