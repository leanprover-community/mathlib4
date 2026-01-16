/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis


/-!
Here we find the limit of the term of the form `coef * b1(x)^d1 * b2(x)^d2 * ...`
where `[b1, b2, ...]` is well-formed basis and `coef` is real constant.
-/

@[expose] public section

namespace ComputeAsymptotics

open Asymptotics Filter Topology

/-- Structure for representing monomials in some basis of functions. When some
`basis : List (R -> R)` is given, one can interpret `⟨coef, exps⟩ : Term` as function
`coef * basis[0]^exps[0] * basis[1]^exps[1] * ...`. -/
structure Term where
  /-- Real coefficient of monomial. -/
  coef : ℝ
  /-- List of exponents. -/
  exps : List ℝ

namespace Term

/-- Converts `t : Term` to real function represented by the corresponding monomial, i.e.
`t.coef * basis[0]^t.exps[0] * basis[1]^t.exps[1] * ...`. It is always assumed that
`t.exps.length = basis.length`, but some theorems below do not require this assumption. -/
noncomputable def toFun (t : Term) (basis : Basis) : ℝ → ℝ :=
  fun x ↦ t.exps.zip basis |>.foldl (init := t.coef) fun acc (exp, f) =>
    acc * (f x)^exp

/-- Auxillary lemma stating that in the `List.fold` used in `toFun` definition we can pull `t.coef`
outside `List.fold` as a multiplier. -/
theorem fold_eq_mul (li : List (ℝ × (ℝ → ℝ))) (coef : ℝ) (x : ℝ) :
    (li.foldl (init := coef) fun acc (exp, f) => acc * (f x)^exp) =
    coef * (li.foldl (init := 1) fun acc (exp, f) => acc * (f x)^exp) := by
  induction li generalizing coef with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.foldl_cons, one_mul] at *
    rw [ih (coef * hd.2 x ^ hd.1), ih (hd.2 x ^ hd.1)]
    ring

/-- If `t.coef = 0`, then t.toFun is zero. -/
theorem zero_coef_toFun {t : Term} (basis : Basis) (h_coef : t.coef = 0) :
    t.toFun basis = 0 := by
  unfold toFun
  ext
  rw [fold_eq_mul, h_coef]
  simp


/-- If `t.coef = 0`, then t.toFun is zero. -/
theorem zero_coef_toFun' (basis : Basis) (exps : List ℝ) :
    Term.toFun ⟨0, exps⟩ basis = 0 := zero_coef_toFun _ rfl

/-- Flipping the sign of `coef` flips the sign of `toFun`. The theorem is stated in this form,
because it allows one to rewrite `t.toFun basis` expression. It is used below in cases where we want
to reduce the case of `t.coef < 0` to `t.coef > 0`. -/
theorem neg_coef_toFun {t : Term} {basis : Basis} :
    t.toFun basis = fun x => -(mk (-t.coef) t.exps).toFun basis x := by
  unfold toFun
  ext
  rw [fold_eq_mul (coef := t.coef), fold_eq_mul (coef := -t.coef)]
  simp

/-- Multiplication of monomials. -/
noncomputable def mul (t1 t2 : Term) : Term :=
  ⟨t1.coef * t2.coef, t1.exps.zip t2.exps |>.map fun (exp1, exp2) => exp1 + exp2⟩

/-- Inversion operation for monomials. -/
noncomputable def inv (t : Term) : Term :=
  ⟨t.coef⁻¹, t.exps.map fun exp => -exp⟩

theorem mul_length (t1 t2 : Term) (h : t1.exps.length = t2.exps.length) :
    (mul t1 t2).exps.length = t1.exps.length := by
  simp [mul, h]

/-- Inversion keeps length of `exps` the same. -/
theorem inv_length {t : Term} : t.inv.exps.length = t.exps.length := by
  simp [inv]

theorem mul_toFun {t1 t2 : Term} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : t1.exps.length = t2.exps.length) :
    (mul t1 t2).toFun basis =ᶠ[atTop] fun x ↦ t1.toFun basis x * t2.toFun basis x := by
  obtain ⟨coef1, exps1⟩ := t1
  obtain ⟨coef2, exps2⟩ := t2
  apply (basis_eventually_pos h_basis).mono
  intro x h_pos
  simp only [toFun, mul]
  simp only at h_length
  rw [fold_eq_mul]
  conv_rhs => rw [fold_eq_mul]; arg 2; rw [fold_eq_mul]
  move_mul [coef1, coef2]
  simp only [mul_eq_mul_right_iff]
  left
  left
  induction exps1 generalizing exps2 basis with
  | nil =>
    symm at h_length
    simp_all
  | cons exp1 exps1 ih =>
  obtain _ | ⟨exp2, exps2⟩ := exps2
  · simp at h_length
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp
  simp only [List.zip_cons_cons, List.map_cons, List.foldl_cons, one_mul]
  rw [fold_eq_mul]
  conv_rhs => rw [fold_eq_mul]; arg 2; rw [fold_eq_mul]
  specialize ih h_basis.tail exps2 (by simpa using h_length)
    (fun f hf ↦ h_pos f <| List.mem_cons_of_mem basis_hd hf)
  rw [ih, Real.rpow_add (h_pos _ (by simp))]
  ring

theorem smul_toFun {t : Term} {basis : Basis} (c : ℝ) :
    (mk (t.coef * c) t.exps).toFun basis = c • t.toFun basis := by
  ext x
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [fold_eq_mul]
  conv_rhs => rw [fold_eq_mul]
  ring

theorem inv_toFun {t : Term} {basis : Basis} (h_basis : WellFormedBasis basis) :
    (fun x ↦ (t.toFun basis x)⁻¹) =ᶠ[atTop] fun x ↦ t.inv.toFun basis x := by
  unfold toFun
  simp only [inv]
  induction t.exps generalizing basis with
  | nil => simp
  | cons hd tl ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      unfold EventuallyEq
      specialize ih (h_basis.tail)
      unfold EventuallyEq at ih
      apply ((basis_head_eventually_pos h_basis).and ih).mono
      rintro x ⟨h_pos, ih⟩
      simp only at ih
      simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons]
      simp [WellFormedBasis] at h_basis
      conv => congr <;> rw [fold_eq_mul]
      simp only [mul_inv_rev]
      conv at ih => congr <;> rw [fold_eq_mul]
      simp only [mul_inv_rev] at ih
      -- why can't use ring?
      conv_rhs => lhs; rw [mul_comm]
      conv_rhs =>
        rw [mul_assoc, ← ih, ← mul_assoc]
        lhs
        rw [mul_comm]
      conv_rhs => rw [mul_assoc, Real.rpow_neg (h_pos.le)]

/-- If `t.coef > 0` then t.toFun is eventually positive. -/
theorem toFun_pos {t : Term} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_coef : 0 < t.coef) :
    ∀ᶠ x in atTop, 0 < t.toFun basis x := by
  apply (basis_eventually_pos h_basis).mono
  intro x hx
  have hx' : ∀ hd ∈ t.exps.zip basis, 0 < hd.2 x := by
    intro hd h_hd
    exact hx _ (List.of_mem_zip h_hd).right
  simp only [toFun, gt_iff_lt]
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
      grind

theorem toFun_ne_zero {t : Term} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_coef : t.coef ≠ 0) :
    ∀ᶠ x in atTop, t.toFun basis x ≠ 0 := by
  rcases lt_or_gt_of_ne h_coef with h_coef | h_coef
  · rw [neg_coef_toFun]
    apply (toFun_pos (t := mk (-t.coef) t.exps) h_basis (by simpa)).mono
    intro x hx
    simp only [ne_eq, neg_eq_zero]
    linarith
  · apply (toFun_pos h_basis h_coef).mono
    intro x hx
    linarith

/-- Expresses `log t.toFun` as some `List.fold`. -/
theorem toFun_log {t : Term} {basis : Basis}
    (h_coef : 0 < t.coef) (h_basis : WellFormedBasis basis) :
    Real.log ∘ t.toFun basis =ᶠ[atTop]
      (fun x => t.exps.zip basis |>.foldl (init := Real.log t.coef) fun acc (exp, f) =>
        acc + exp * Real.log ((f x))) := by
  have h_pos : ∀ᶠ x in atTop, ∀ hd ∈ t.exps.zip basis, 0 < hd.2 x := by
    -- TODO : rewrite using `basis_eventually_pos`
    have h_pos : ∀ hd ∈ t.exps.zip basis, ∀ᶠ x in atTop, 0 < hd.2 x := by
      have h' : ∀ hd ∈ t.exps.zip basis, Tendsto hd.2 atTop atTop := by
        intro hd h_hd
        apply basis_tendsto_top h_basis
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
  apply h_pos.mono
  clear h_pos
  intro x hf
  generalize t.exps.zip basis = li at *
  generalize t.coef = c at *
  induction li generalizing c with
  | nil => simp
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

/-- If `t.exps[0]` is zero, then one can exclude the first function from the basis keeping `t.toFun`
the same. -/
theorem zero_head_toFun (coef : ℝ) {exp : ℝ} {exps_tl : List ℝ} {basis : Basis}
    (h_length : (exp :: exps_tl).length = basis.length) (h_exp : exp = 0) :
    let t : Term := ⟨coef, exp :: exps_tl⟩;
    t.toFun basis = (mk coef exps_tl).toFun basis.tail! := by
  unfold toFun
  cases basis with
  | nil => simp at h_length
  | cons basis_hd basis_tl => simp [h_exp]

theorem zeros_append_toFun (coef : ℝ) {exps : List ℝ} {left right : Basis}
    (h_length : exps.length = right.length) :
    let t : Term := ⟨coef, List.replicate left.length 0 ++ exps⟩;
    t.toFun (left ++ right) = (mk coef exps).toFun right := by
  induction left with
  | nil => rfl
  | cons left_hd left_tl ih =>
  simp only [List.length_cons, List.replicate_succ, List.cons_append]
  rw [Term.zero_head_toFun _ (by simpa) rfl]
  simpa using ih

/-- If the first exponent is not zero, then `log t.toFun` is asymptotically equivalent to
`log coef + exps[0] * log basis[0]`. -/
theorem log_IsEquivalent_of_nonzero_head {coef exp : ℝ} {tl : List ℝ} {basis : Basis}
    (h_length : (exp :: tl).length = basis.length) (h_basis : WellFormedBasis basis)
    (h_coef : 0 < coef) (h_exp : exp ≠ 0) :
    let t : Term := ⟨coef, exp :: tl⟩;
    Real.log ∘ t.toFun basis ~[atTop] fun x => Real.log coef + exp * Real.log (basis.head! x) := by
  intro t
  apply Asymptotics.IsEquivalent.congr_left _ <| (toFun_log (t := t) h_coef h_basis).symm
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
        simp only [List.foldl_cons, zero_add] at ih ⊢
        rw [ih (hd.1 * Real.log (hd.2 x)), ih (init + hd.1 * Real.log (hd.2 x))]
        ring
    simp only [t, List.zip_cons_cons, List.foldl_cons, List.head!_cons]
    conv_lhs => ext; rw [h_pull_init]
    simp only [IsEquivalent]
    conv_lhs => ext; simp
    have h_little : ∀ hd ∈ tl.zip basis_tl, (Real.log ∘ hd.2) =o[atTop] (Real.log ∘ basis_hd) := by
      intro hd h_hd
      apply basis_IsLittleO_of_head h_basis
      exact (List.of_mem_zip h_hd).right
    have h_tendsto : ∀ hd ∈ tl.zip basis_tl, Tendsto hd.2 atTop atTop := by
      intro hd h_hd
      apply basis_tendsto_top h_basis
      simp only [List.mem_cons]
      right
      exact (List.of_mem_zip h_hd).right
    generalize tl.zip basis_tl = li at *
    induction li with
    | nil => simp
    | cons tl_hd tl_tl ih =>
      simp only [List.foldl_cons, zero_add]
      conv_lhs => ext; rw [h_pull_init]
      apply IsLittleO.add
      · apply IsLittleO.const_mul_left
        have : (fun _ ↦ Real.log coef) =o[atTop] fun x ↦ exp * Real.log (basis_hd x) := by
          apply IsLittleO.const_mul_right' (by simp [h_exp])
          apply Asymptotics.isLittleO_const_left.mpr
          right
          apply Filter.Tendsto.comp tendsto_norm_atTop_atTop
          rw [← Function.comp_def]
          apply Filter.Tendsto.comp Real.tendsto_log_atTop
          simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons,
            forall_eq_or_imp] at h_basis
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

/-- `t.toFun` tends to `atTop` when `t.coef > 0` and `t.exps[0] > 0`. -/
theorem tendsto_top {coef exp : ℝ} {tl : List ℝ} {basis : Basis}
    (h_length : (exp :: tl).length = basis.length) (h_basis : WellFormedBasis basis)
    (h_coef : 0 < coef) (h_exp : 0 < exp) :
    let t : Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop atTop := by
  intro t
  have h_t_equiv : Real.log ∘ t.toFun basis ~[atTop]
      fun x => Real.log coef + exp * Real.log (basis.head! x) :=
    log_IsEquivalent_of_nonzero_head h_length h_basis h_coef h_exp.ne.symm
  suffices h_log : Tendsto (Real.log ∘ t.toFun basis) atTop atTop by
    have := Tendsto.comp Real.tendsto_exp_atTop h_log
    apply Filter.Tendsto.congr' _ this
    simp only [EventuallyEq]
    apply (toFun_pos (t := t) h_basis h_coef).mono
    intro x hx
    simp [Real.exp_log hx]
  apply IsEquivalent.tendsto_atTop h_t_equiv.symm
  apply Filter.tendsto_atTop_add_const_left
  apply Filter.Tendsto.const_mul_atTop h_exp
  rw [← Function.comp_def]
  apply Tendsto.comp Real.tendsto_log_atTop
  apply basis_tendsto_top h_basis
  cases basis
  · simp at h_length
  · simp

/-- `t.toFun` tends to `atBot` when `t.coef < 0` and `t.exps[0] > 0`. -/
theorem tendsto_bot {coef exp : ℝ} {tl : List ℝ} {basis : Basis}
    (h_length : (exp :: tl).length = basis.length) (h_basis : WellFormedBasis basis)
    (h_coef : coef < 0) (h_exp : 0 < exp) :
    let t : Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop atBot := by
  intro t
  rw [neg_coef_toFun (t := t)]
  apply Filter.tendsto_neg_atBot_iff.mpr
  apply tendsto_top h_length h_basis _ h_exp
  linarith

-- TODO: it's copypaste from `tendsto_top`
/-- Auxillary lemma. `t.toFun` tends to `𝓝 0` when `t.coef > 0` and `t.exps[0] < 0`. -/
lemma tendsto_zero_pos_coef {coef exp : ℝ} {tl : List ℝ} {basis : Basis}
    (h_length : (exp :: tl).length = basis.length) (h_basis : WellFormedBasis basis)
    (h_coef : 0 < coef) (h_exp : exp < 0) :
    let t : Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  have h_t_equiv : Real.log ∘ t.toFun basis ~[atTop]
      fun x => Real.log coef + exp * Real.log (basis.head! x) :=
    log_IsEquivalent_of_nonzero_head h_length h_basis h_coef h_exp.ne
  suffices h_log : Tendsto (Real.log ∘ t.toFun basis) atTop atBot by
    have := Tendsto.comp Real.tendsto_exp_atBot h_log
    apply Filter.Tendsto.congr' _ this
    simp only [EventuallyEq]
    apply (toFun_pos (t := t) h_basis h_coef).mono
    intro x hx
    simp [Real.exp_log hx]
  apply IsEquivalent.tendsto_atBot h_t_equiv.symm
  apply Filter.tendsto_atBot_add_const_left
  apply (Filter.tendsto_neg_atTop_iff).mp
  simp_rw [← neg_mul]
  apply Filter.Tendsto.const_mul_atTop (by linarith)
  rw [← Function.comp_def]
  apply Tendsto.comp Real.tendsto_log_atTop
  apply basis_tendsto_top h_basis
  cases basis
  · simp at h_length
  · simp

/-- Auxillary lemma. `t.toFun` tends to `𝓝 0` when `t.coef < 0` and `t.exps[0] < 0`. -/
lemma tendsto_zero_neg_coef {coef exp : ℝ} {tl : List ℝ} {basis : Basis}
    (h_length : (exp :: tl).length = basis.length)
    (h_coef : coef < 0) (h_exp : exp < 0) (h_basis : WellFormedBasis basis) :
    let t : Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  rw [neg_coef_toFun (t := t), ← neg_zero]
  apply Filter.Tendsto.neg
  apply tendsto_zero_pos_coef h_length h_basis _ h_exp
  linarith

/-- `t.toFun` tends to `𝓝 0` when `t.exps[0] < 0`. -/
theorem tendsto_zero (coef : ℝ) {exp : ℝ} {tl : List ℝ} {basis : Basis}
    (h_length : (exp :: tl).length = basis.length)
    (h_exp : exp < 0) (h_basis : WellFormedBasis basis) :
    let t : Term := ⟨coef, exp :: tl⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  rcases lt_trichotomy coef 0 with (h_coef | h_coef | h_coef)
  · apply tendsto_zero_neg_coef <;> assumption
  · rw [zero_coef_toFun (t := t) basis h_coef]
    apply tendsto_const_nhds
  · apply tendsto_zero_pos_coef <;> assumption

/-- `t.toFun` tends to `𝓝 t.coef` when `t.exps` is empty. -/
theorem nil_tendsto_const (coef : ℝ) (basis : Basis) :
    let t : Term := ⟨coef, []⟩;
    Tendsto (t.toFun basis) atTop (𝓝 coef) := by
  eta_expand
  simp [toFun]

/-- `t.toFun` tends to `𝓝 0` when `t.coef = 0`. -/
theorem tendsto_zero_of_coef_zero {coef : ℝ} {exps : List ℝ} (basis : Basis)
    (h_coef : coef = 0) :
    let t : Term := ⟨coef, exps⟩;
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  rw [zero_coef_toFun]
  · eta_expand
    simp
  · simpa [t]

/-- Predicate stating that the first non-zero element of the list is positive. -/
def FirstIsPos (x : List ℝ) : Prop := match x with
| [] => False
| hd :: tl => 0 < hd ∨ (hd = 0 ∧ FirstIsPos tl)

/-- Predicate stating that the first non-zero element of the list is negative. -/
def FirstIsNeg (x : List ℝ) : Prop := match x with
| [] => False
| hd :: tl => hd < 0 ∨ (hd = 0 ∧ FirstIsNeg tl)

/-- Predicate stating that all elements of the list are zero. -/
def AllZero (x : List ℝ) : Prop := match x with
| [] => True
| hd :: tl => hd = 0 ∧ AllZero tl

theorem AllZero_of_nil : AllZero [] := by
  simp [AllZero]

theorem AllZero_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0) (h_tl : AllZero tl) :
    AllZero (hd :: tl) := by
  simp [AllZero]
  tauto

theorem FirstIsPos_of_head {hd : ℝ} (tl : List ℝ) (h : 0 < hd) : FirstIsPos (hd :: tl) := by
  simp [FirstIsPos]
  tauto

theorem FirstIsPos_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0) (h_tl : FirstIsPos tl) :
    FirstIsPos (hd :: tl) := by
  simp [FirstIsPos]
  tauto

theorem FirstIsNeg_of_head {hd : ℝ} (tl : List ℝ) (h : hd < 0) : FirstIsNeg (hd :: tl) := by
  simp [FirstIsNeg]
  tauto

theorem FirstIsNeg_of_tail {hd : ℝ} {tl : List ℝ} (h_hd : hd = 0) (h_tl : FirstIsNeg tl) :
    FirstIsNeg (hd :: tl) := by
  simp [FirstIsNeg]
  tauto

theorem AllZero_of_replicate {n : ℕ} : AllZero (List.replicate n 0) := by
  cases n with
  | zero => simp [AllZero]
  | succ n =>
    simpa only [List.replicate_succ, AllZero, true_and] using AllZero_of_replicate

theorem not_FirstIsPos_of_AllZero {x : List ℝ} (h : AllZero x) : ¬ FirstIsPos x := by
  cases x with
  | nil => simp [FirstIsPos]
  | cons hd tl =>
    intro h'
    simp only [AllZero, FirstIsPos] at h h'
    simp only [h.left, lt_self_iff_false, true_and, false_or] at h'
    exact not_FirstIsPos_of_AllZero h.right h'

theorem not_FirstIsPos_of_FirstIsNeg {x : List ℝ} (h : FirstIsNeg x) : ¬ FirstIsPos x := by
  cases x with
  | nil => simp [FirstIsPos]
  | cons hd tl =>
    intro h'
    simp only [FirstIsNeg, FirstIsPos] at h h'
    by_cases h_hd : hd = 0
    · simp only [h_hd, lt_self_iff_false, true_and, false_or] at h h'
      exact not_FirstIsPos_of_FirstIsNeg h h'
    simp [h_hd] at h h'
    linarith

theorem tendsto_const_of_AllZero {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_length : exps.length = basis.length)
    (h_exps : AllZero exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 coef) := by
  cases exps with
  | nil =>
    exact nil_tendsto_const coef basis
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [AllZero] at h_exps
      have := zero_head_toFun coef h_length h_exps.left
      simp only [this, List.tail!_cons]
      simp only [List.length_cons, add_left_inj] at h_length
      exact tendsto_const_of_AllZero h_length h_exps.right

theorem tendsto_zero_of_FirstIsNeg {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_exps : FirstIsNeg exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  cases exps with
  | nil =>
    simp [FirstIsNeg] at h_exps
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstIsNeg] at h_exps
      obtain h_exps | h_exps := h_exps
      · exact tendsto_zero coef h_length h_exps h_basis
      · have := zero_head_toFun coef h_length h_exps.left
        simp only [this, List.tail!_cons]
        simp only [List.length_cons, add_left_inj] at h_length
        exact tendsto_zero_of_FirstIsNeg (h_basis.tail) h_length h_exps.right

theorem tendsto_top_of_FirstIsPos {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : 0 < coef)
    (h_exps : FirstIsPos exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atTop := by
  cases exps with
  | nil =>
    simp [FirstIsPos] at h_exps
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstIsPos] at h_exps
      obtain h_exps | h_exps := h_exps
      · exact tendsto_top h_length h_basis h_coef h_exps
      · have := zero_head_toFun coef h_length h_exps.left
        simp only [this, List.tail!_cons]
        simp only [List.length_cons, add_left_inj] at h_length
        exact tendsto_top_of_FirstIsPos (h_basis.tail) h_length h_coef
          h_exps.right

theorem tendsto_bot_of_FirstIsPos {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : coef < 0)
    (h_exps : FirstIsPos exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atBot := by
  cases exps with
  | nil =>
    simp [FirstIsPos] at h_exps
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [FirstIsPos] at h_exps
      obtain h_exps | h_exps := h_exps
      · exact tendsto_bot h_length h_basis h_coef h_exps
      · have := zero_head_toFun coef h_length h_exps.left
        simp only [this, List.tail!_cons]
        simp only [List.length_cons, add_left_inj] at h_length
        exact tendsto_bot_of_FirstIsPos (h_basis.tail) h_length h_coef
          h_exps.right

-------------------------------

-- TODO
theorem tail_fun_IsLittleO_head {t : Term} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_length : t.exps.length = basis_tl.length)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) {exp : ℝ} (h_exp : 0 < exp) :
    t.toFun basis_tl =o[atTop] fun x ↦ (basis_hd x)^exp := by
  unfold toFun
  simp only
  generalize t.exps = exps at *
  induction exps generalizing basis_hd basis_tl with
  | nil =>
    simp only [List.zip_nil_left, List.foldl_nil, isLittleO_const_left]
    right
    apply Tendsto.comp tendsto_norm_atTop_atTop
    apply Tendsto.comp (tendsto_rpow_atTop h_exp)
    simp only [WellFormedBasis, List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h_basis
    exact h_basis.right.left
  | cons exps_hd exps_tl ih =>
    cases basis_tl with
    | nil =>
      simp at h_length
    | cons basis_tl_hd basis_tl_tl =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      unfold WellFormedBasis at h_basis
      simp only [List.length_cons, add_left_inj] at h_length
      specialize ih (WellFormedBasis.tail h_basis) h_length
      conv at ih =>
        lhs
        ext
        rw [fold_eq_mul]
        simp only
      conv =>
        lhs
        ext
        rw [fold_eq_mul]
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
        simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at h_basis
        apply basis_compare b a (Tendsto.eventually_gt_atTop h_basis.right.right.left 0)
          h_basis.right.left h_basis.left.left.left ha

      have ih := IsLittleO.trans ih (h_comp (exp / 2) exp (by linarith))

      have aux : (fun x ↦ (basis_hd x)^exp) =ᶠ[atTop]
          fun x ↦ (basis_hd x)^(exp / 2) * (basis_hd x)^(exp / 2) := by
        apply (basis_head_eventually_pos h_basis).mono
        intro x h
        simp only
        rw [← Real.rpow_add h]
        ring_nf
      apply IsLittleO.trans_eventuallyEq _ aux.symm
      apply IsLittleO.mul
      · apply h_comp _ _ (by linarith)
      · exact ih

end Term

end ComputeAsymptotics
