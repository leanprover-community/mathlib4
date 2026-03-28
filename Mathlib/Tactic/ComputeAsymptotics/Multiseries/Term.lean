/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Tactic.MoveAdd
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basis
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Term.Predicates

/-!
Here we find the limit of the term of the form `coef * b1(x)^d1 * b2(x)^d2 * ...`
where `[b1, b2, ...]` is well-formed basis and `coef` is real constant.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Asymptotics Filter Topology Real

/-- Monomial, represented as a list of its exponents. `[e1, e2, ..., en]` corresponds to
`basis[0] ^ e1 * ... * basis[n] ^ en` where `basis` is the basis of functions. -/
abbrev Monomial := List ℝ

/-- Structure for representing monomials with coefficients. -/
structure Term where
  /-- Real coefficient of monomial. -/
  coef : ℝ
  /-- Exponents of monomial. -/
  monomial : Monomial

namespace Monomial

/-- Function corresponding to a monomial. -/
noncomputable def toFun (m : Monomial) (basis : Basis) : ℝ → ℝ :=
  fun x ↦ (m.zipWith (fun exp b ↦ (b x)^exp) basis).prod

/-- Logarithm of function represented by a monomial, i.e.
`m[0] * log basis[0] + ... m[n] * log basis[n]`. -/
noncomputable def toLogFun (m : Monomial) (basis : Basis) : ℝ → ℝ :=
  fun x ↦ (m.zipWith (fun exp b ↦ exp * log (b x)) basis).sum

@[simp]
theorem toFun_nil (basis : Basis) : (Monomial.toFun [] basis) = 1 := by
  ext x
  simp [toFun]

@[simp]
theorem toFun_cons (exp : ℝ) (tl : Monomial) (basis_hd : ℝ → ℝ) (basis_tl : Basis) :
    (Monomial.toFun (exp :: tl) (basis_hd :: basis_tl)) = basis_hd ^ exp * tl.toFun basis_tl := by
  ext x
  simp [toFun]

/-- Multiplication of monomials. -/
noncomputable def mul (m1 m2 : Monomial) : Monomial :=
  m1.zipWith (· + ·) m2

/-- Inversion of a monomial. -/
noncomputable def inv (m : Monomial) : Monomial :=
  m.map (-·)

theorem mul_length {m1 m2 : Monomial} (h : m1.length = m2.length) :
    (mul m1 m2).length = m1.length := by
  simp [mul, h]

@[simp]
theorem inv_length (m : Monomial) :
    (inv m).length = m.length := by
  simp [inv]

theorem mul_toFun {m1 m2 : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : m1.length = m2.length) :
    (m1.mul m2).toFun basis =ᶠ[atTop] m1.toFun basis * m2.toFun basis := by
  apply h_basis.eventually_pos.mono
  intro x h_pos
  simp only [toFun, mul, Pi.mul_apply]
  induction m1 generalizing m2 basis with
  | nil =>
    symm at h_length
    simp_all
  | cons exp1 exps1 ih =>
    cases m2 with
    | nil => simp at h_length
    | cons exp2 exps2 =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
    simp only [List.zipWith_cons_cons, List.prod_cons] at ih ⊢
    rw [ih h_basis.tail (by grind) (by grind), Real.rpow_add (h_pos _ (by simp))]
    grind

theorem inv_toFun {m : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    m.inv.toFun basis =ᶠ[atTop] (m.toFun basis)⁻¹ := by
  eta_expand
  simp only [toFun, inv, Pi.inv_apply]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      apply ((h_basis.head_eventually_pos).and (ih (h_basis.tail))).mono
      rintro x ⟨h_pos, ih⟩
      simp only [List.map_cons, List.zipWith_cons_cons, List.prod_cons, mul_inv_rev] at ih ⊢
      rw [ih, ← Real.rpow_neg h_pos.le]
      ring

theorem tail_toFun_IsLittleO_head {m : Monomial} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_length : m.length = basis_tl.length)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    Majorized (m.toFun basis_tl) basis_hd 0 := by
  induction m generalizing basis_hd basis_tl with
  | nil =>
    simpa using Majorized.const (h_basis.tendsto_atTop (by simp))
  | cons hd tl ih =>
    cases basis_tl with
    | nil =>
      simp at h_length
    | cons basis_tl_hd basis_tl_tl =>
      simp only [List.length_cons, Nat.add_right_cancel_iff, toFun_cons] at h_length ⊢
      rw [show (0 : ℝ) = 0 + 0 by simp]
      apply Majorized.mul
      · apply basis_tail_pow_Majorized_head h_basis (by simp)
      · specialize ih h_length h_basis.tail 1 (by simp)
        intro exp h_exp
        apply ih.trans
        exact basis_tail_pow_Majorized_head (f := basis_tl_hd) h_basis (by simp) 1 exp h_exp
      · exact h_basis.head_eventually_pos

theorem toFun_pos {m : Monomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) :
    ∀ᶠ x in atTop, 0 < m.toFun basis x := by
  apply h_basis.eventually_pos.mono
  intro x hx
  simp only [toFun]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [List.zipWith_cons_cons, List.prod_cons]
      apply mul_pos
      · exact Real.rpow_pos_of_pos (hx basis_hd (by simp)) _
      · exact ih h_basis.tail (fun f hf => hx f (by simp [hf]))

theorem toFun_ne_zero {m : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    ∀ᶠ x in atTop, m.toFun basis x ≠ 0 := by
  exact (toFun_pos h_basis).mono fun x hx => hx.ne'

theorem zeros_append_toFun {m : Monomial} {left right : Basis} :
    let m' : Monomial := List.replicate left.length 0 ++ m
    m'.toFun (left ++ right) = m.toFun right := by
  induction left with
  | nil => rfl
  | cons left_hd left_tl ih =>
    simp at ih
    simp [List.replicate_succ, ih]

theorem logToFun_eq_toLogFun {m : Monomial} {basis : Basis} (h_basis : WellFormedBasis basis) :
    Real.log ∘ m.toFun basis =ᶠ[atTop] m.toLogFun basis := by
  apply (h_basis.eventually_pos).mono
  intro x hx
  simp only [Function.comp_apply, toFun, toLogFun]
  induction m generalizing basis with
  | nil => simp
  | cons exp exps ih =>
    cases basis with
    | nil => simp
    | cons basis_hd basis_tl =>
      simp only [List.zipWith_cons_cons, List.prod_cons, List.sum_cons]
      have h_head : 0 < basis_hd x := hx basis_hd (by simp)
      have h_prod_pos : 0 < (List.zipWith (fun e b => b x ^ e) exps basis_tl).prod := by
        have hx_tl : ∀ f ∈ basis_tl, 0 < f x := fun f hf => hx f (by simp [hf])
        clear h_basis hx ih
        induction exps generalizing basis_tl with
        | nil => simp
        | cons e' es' ih' =>
          cases basis_tl with
          | nil => simp
          | cons bh bt =>
            simp only [List.zipWith_cons_cons, List.prod_cons]
            exact mul_pos (Real.rpow_pos_of_pos (hx_tl bh (by simp)) _)
              (ih' bt (fun f hf => hx_tl f (List.mem_cons.mpr (Or.inr hf))))
      rw [Real.log_mul (Real.rpow_pos_of_pos h_head _).ne' h_prod_pos.ne',
          Real.log_rpow h_head]
      congr 1
      exact ih h_basis.tail (fun f hf => hx f (by simp [hf]))

theorem logToFun_isEquivalent_of_nonzero_head {exps_hd : ℝ} {exps_tl : Monomial} {basis_hd : ℝ → ℝ}
    {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : exps_hd ≠ 0) :
    Monomial.toLogFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • log ∘ basis_hd := by
  unfold toLogFun
  simp only [List.zipWith_cons_cons, List.sum_cons]
  rw [show (fun x => exps_hd * Real.log (basis_hd x) +
      (List.zipWith (fun exp b => exp * Real.log (b x)) exps_tl basis_tl).sum) =
      (exps_hd • Real.log ∘ basis_hd) + fun x =>
      (List.zipWith (fun exp b => exp * Real.log (b x)) exps_tl basis_tl).sum from by
    ext x; simp [smul_eq_mul]]
  apply IsEquivalent.add_isLittleO IsEquivalent.refl
  apply IsLittleO.const_mul_right' (isUnit_iff_ne_zero.mpr h_nonzero)
  have h_key : ∀ (li : List (ℝ × (ℝ → ℝ))),
      (∀ p ∈ li, (Real.log ∘ p.2) =o[atTop] (Real.log ∘ basis_hd)) →
      (fun x => (li.map (fun p => p.1 * Real.log (p.2 x))).sum) =o[atTop]
        (Real.log ∘ basis_hd) := by
    intro li
    induction li with
    | nil => simp
    | cons hd tl ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      have : (fun x => hd.1 * Real.log (hd.2 x) + (tl.map (fun p => p.1 * Real.log (p.2 x))).sum) =
          (fun x => hd.1 * Real.log (hd.2 x)) +
          fun x => (tl.map (fun p => p.1 * Real.log (p.2 x))).sum := rfl
      rw [this]
      apply IsLittleO.add
      · apply IsLittleO.const_mul_left; exact h _ (by simp)
      · exact ih (fun p hp => h p (by right; exact hp))
  have h_conv : ∀ (l₁ : List ℝ) (l₂ : Basis) (x : ℝ),
      List.zipWith (fun exp b => exp * Real.log (b x)) l₁ l₂ =
      (l₁.zip l₂).map (fun p => p.1 * Real.log (p.2 x)) := by
    intro l₁
    induction l₁ with
    | nil => simp
    | cons e es ih =>
      intro l₂ x
      cases l₂ with
      | nil => simp
      | cons b bs => simp [List.zipWith_cons_cons, List.zip_cons_cons, ih]
  rw [show (fun x => (List.zipWith (fun exp b => exp * Real.log (b x)) exps_tl basis_tl).sum) =
      fun x => ((exps_tl.zip basis_tl).map (fun p => p.1 * Real.log (p.2 x))).sum from by
    ext x; congr 1; exact h_conv exps_tl basis_tl x]
  apply h_key
  intro p hp
  apply h_basis.tail_isLittleO_head
  exact (List.of_mem_zip hp).right

theorem toFun_tendsto_top_of_head_pos {exps_hd : ℝ} {exps_tl : Monomial} {basis_hd : ℝ → ℝ}
    {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : 0 < exps_hd) :
    Tendsto (Monomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl)) atTop atTop := by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (logToFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne').congr_left
      (logToFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl))
      atTop atTop by
    have hmono := Real.tendsto_exp_atTop.comp h_log
    apply Filter.Tendsto.congr' _ hmono
    apply (toFun_pos (m := (exps_hd :: exps_tl)) h_basis).mono
    intro x hx
    simp only [Function.comp_apply]
    exact Real.exp_log hx
  apply IsEquivalent.tendsto_atTop h_equiv.symm
  apply Filter.Tendsto.const_mul_atTop h_nonzero
  apply Tendsto.comp Real.tendsto_log_atTop
  exact h_basis.tendsto_atTop (by simp)

theorem toFun_tendsto_zero_of_head_neg {exps_hd : ℝ} {exps_tl : Monomial} {basis_hd : ℝ → ℝ}
    {basis_tl : Basis}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_nonzero : exps_hd < 0) :
    Tendsto (Monomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl)) atTop (𝓝 0) := by
  have h_equiv : Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) ~[atTop]
      exps_hd • Real.log ∘ basis_hd :=
    (logToFun_isEquivalent_of_nonzero_head h_basis h_nonzero.ne).congr_left
      (logToFun_eq_toLogFun h_basis).symm
  suffices h_log : Tendsto (Real.log ∘ toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl))
      atTop atBot by
    have hmono := Real.tendsto_exp_atBot.comp h_log
    apply Filter.Tendsto.congr' _ hmono
    apply (toFun_pos (m := (exps_hd :: exps_tl)) h_basis).mono
    intro x hx
    simp only [Function.comp_apply]
    exact Real.exp_log hx
  apply IsEquivalent.tendsto_atBot h_equiv.symm
  have h_log_atTop : Tendsto (fun x => Real.log (basis_hd x)) atTop atTop :=
    Tendsto.comp Real.tendsto_log_atTop (h_basis.tendsto_atTop (by simp))
  exact Filter.Tendsto.const_mul_atTop_of_neg h_nonzero h_log_atTop

theorem toFun_tendsto_top_of_FirstIsPos {m : Monomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_length : m.length = basis.length)
    (h_firstIsPos : List.FirstIsPos m) :
    Tendsto (Monomial.toFun m basis) atTop atTop := by
  cases m with
  | nil => simp [List.FirstIsPos] at h_firstIsPos
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [List.FirstIsPos] at h_firstIsPos
      obtain h | h := h_firstIsPos
      · exact toFun_tendsto_top_of_head_pos h_basis h
      · have h_eq : Monomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                    Monomial.toFun exps_tl basis_tl := by
          ext x; simp [Monomial.toFun, h.left]
        rw [h_eq]
        exact toFun_tendsto_top_of_FirstIsPos h_basis.tail (by simpa using h_length) h.right

theorem toFun_tendsto_zero_of_FirstIsNeg {m : Monomial} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_length : m.length = basis.length)
    (h_firstIsNeg : List.FirstIsNeg m) :
    Tendsto (Monomial.toFun m basis) atTop (𝓝 0) := by
  cases m with
  | nil => simp [List.FirstIsNeg] at h_firstIsNeg
  | cons exps_hd exps_tl =>
    cases basis with
    | nil => simp at h_length
    | cons basis_hd basis_tl =>
      simp only [List.FirstIsNeg] at h_firstIsNeg
      obtain h | h := h_firstIsNeg
      · exact toFun_tendsto_zero_of_head_neg h_basis h
      · have h_eq : Monomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                    Monomial.toFun exps_tl basis_tl := by
          ext x; simp [Monomial.toFun, h.left]
        rw [h_eq]
        exact toFun_tendsto_zero_of_FirstIsNeg h_basis.tail (by simpa using h_length) h.right

theorem toFun_tendsto_one_of_AllZero {m : Monomial} {basis : Basis}
    (h_allZero : List.AllZero m) :
    Tendsto (Monomial.toFun m basis) atTop (𝓝 1) := by
  cases m with
  | nil =>
    exact tendsto_const_nhds
  | cons exps_hd exps_tl =>
    cases basis with
    | nil =>
      eta_expand
      simp [toFun]
    | cons basis_hd basis_tl =>
      simp only [List.AllZero] at h_allZero
      have h_eq : Monomial.toFun (exps_hd :: exps_tl) (basis_hd :: basis_tl) =
                  Monomial.toFun exps_tl basis_tl := by
        ext x; simp [Monomial.toFun, h_allZero.left]
      rw [h_eq]
      exact toFun_tendsto_one_of_AllZero h_allZero.right

lemma IsLittleO_of_lt {basis : Basis} {m1 m2 : Monomial}
    (h_basis : WellFormedBasis basis)
    (h1 : m1.length = basis.length)
    (h2 : m2.length = basis.length)
    (h_lt : m1 < m2) :
    m1.toFun basis =o[atTop] m2.toFun basis := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [List.length_nil, List.length_eq_zero_iff] at h1 h2
    simp [h1, h2] at h_lt

  obtain _ | ⟨exp1, m1⟩ := m1
  · simp at h1
  obtain _ | ⟨exp2, m2⟩ := m2
  · simp at h2
  cases h_lt with
  | cons h =>
    simp only [toFun_cons]
    apply IsBigO.mul_isLittleO (isBigO_refl _ _)
    exact IsLittleO_of_lt h_basis.tail (by simpa using h1) (by simpa using h2) h
  | rel h =>
    simp only [List.length_cons, Nat.add_right_cancel_iff, toFun_cons] at h1 h2 ⊢
    apply IsLittleO.of_tendsto_div_atTop
    apply Filter.Tendsto.congr' (f₁ := Monomial.toFun ((exp2 - exp1) ::
      Monomial.mul m2 (Monomial.inv m1)) (basis_hd :: basis_tl))
    · simp only [toFun_cons, Pi.mul_apply, Pi.pow_apply]
      grw [mul_toFun h_basis.tail (by grind [inv_length]), inv_toFun h_basis.tail]
      apply h_basis.head_eventually_pos.mono
      intro x hx
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.inv_apply, Real.rpow_sub hx]
      field
    · apply toFun_tendsto_top_of_FirstIsPos h_basis
      · grind [inv_length, mul_length]
      · apply List.FirstIsPos_of_head
        grind

end Monomial

namespace Term

/-- Converts `t : Term` to real function represented by the corresponding monomial, i.e.
`t.coef * basis[0]^t.exps[0] * basis[1]^t.exps[1] * ...`. It is always assumed that
`t.exps.length = basis.length`, but some theorems below do not require this assumption. -/
noncomputable def toFun (t : Term) (basis : Basis) : ℝ → ℝ :=
  t.coef • t.monomial.toFun basis

@[simp]
theorem nil_toFun {coef : ℝ} {basis : Basis} :
    Term.toFun ⟨coef, []⟩ basis = fun _ ↦ coef := by
  ext x
  simp [toFun]

@[simp]
theorem cons_toFun {coef exp : ℝ} {m : Monomial} {basis_hd : ℝ → ℝ} {basis_tl : Basis} :
    Term.toFun ⟨coef, exp :: m⟩ (basis_hd :: basis_tl) =
    basis_hd ^ exp * Term.toFun ⟨coef, m⟩ basis_tl := by
  ext x
  simp [toFun]
  ring

/-- If `t.coef = 0`, then t.toFun is zero. -/
theorem zero_coef_toFun {t : Term} (basis : Basis) (h_coef : t.coef = 0) :
    t.toFun basis = 0 := by
  unfold toFun
  ext x
  simp [h_coef]

/-- If `t.coef = 0`, then t.toFun is zero. -/
theorem zero_coef_toFun' (basis : Basis) (exps : List ℝ) :
    Term.toFun ⟨0, exps⟩ basis = 0 := zero_coef_toFun _ rfl

/-- Negation of a term. -/
noncomputable def neg (t : Term) : Term :=
  ⟨-t.coef, t.monomial⟩

/-- Multiplication of terms. -/
noncomputable def mul (t1 t2 : Term) : Term :=
  ⟨t1.coef * t2.coef, t1.monomial.mul t2.monomial⟩

/-- Scales a term by a real factor `c`. -/
noncomputable def smul (t : Term) (c : ℝ) : Term :=
  ⟨c * t.coef, t.monomial⟩

/-- Inversion operation for monomials. -/
noncomputable def inv (t : Term) : Term :=
  ⟨t.coef⁻¹, t.monomial.inv⟩

/-- Flipping the sign of `coef` flips the sign of `toFun`. The theorem is stated in this form,
because it allows one to rewrite `t.toFun basis` expression. It is used below in cases where we want
to reduce the case of `t.coef < 0` to `t.coef > 0`. -/
theorem neg_toFun {t : Term} {basis : Basis} :
    t.toFun basis = -t.neg.toFun basis := by
  ext x
  simp [neg, toFun]

theorem mul_toFun {t1 t2 : Term} {basis : Basis} (h_basis : WellFormedBasis basis)
    (h_length : t1.monomial.length = t2.monomial.length) :
    (mul t1 t2).toFun basis =ᶠ[atTop] t1.toFun basis * t2.toFun basis := by
  simp only [toFun, mul, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  grw [Monomial.mul_toFun h_basis h_length]
  apply EventuallyEq.of_eq
  ext t
  simp
  ring

theorem smul_toFun {t : Term} {basis : Basis} (c : ℝ) :
    (smul t c).toFun basis = c • t.toFun basis := by
  ext x
  simp [smul, toFun]
  grind

theorem inv_toFun {t : Term} {basis : Basis} (h_basis : WellFormedBasis basis) :
    t.inv.toFun basis =ᶠ[atTop] (t.toFun basis)⁻¹ := by
  simp only [toFun, inv]
  grw [Monomial.inv_toFun h_basis]
  apply EventuallyEq.of_eq
  ext x
  simp
  ring

@[simp]
theorem inv_length (t : Term) :
    t.inv.monomial.length = t.monomial.length := by
  simp [inv]

/-- If `t.coef > 0` then t.toFun is eventually positive. -/
theorem toFun_pos {t : Term} {basis : Basis}
    (h_basis : WellFormedBasis basis) (h_coef : 0 < t.coef) :
    ∀ᶠ x in atTop, 0 < t.toFun basis x := by
  simp only [Term.toFun]
  apply (t.monomial.toFun_pos h_basis).mono
  intro x hx
  simp only [Pi.smul_apply, smul_eq_mul]
  positivity

theorem zeros_append_toFun (coef : ℝ) {exps : List ℝ} {left right : Basis} :
    let t : Term := ⟨coef, List.replicate left.length 0 ++ exps⟩;
    t.toFun (left ++ right) = (mk coef exps).toFun right := by
  simp only [toFun]
  congr 1
  exact Monomial.zeros_append_toFun

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

theorem toFun_tendsto_zero_of_FirstIsNeg {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_exps : List.FirstIsNeg exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 0) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _
    (Monomial.toFun_tendsto_zero_of_FirstIsNeg h_basis h_length h_exps)
  simp

theorem toFun_tendsto_top_of_FirstIsPos {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : 0 < coef)
    (h_exps : List.FirstIsPos exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atTop := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop h_coef
    (Monomial.toFun_tendsto_top_of_FirstIsPos h_basis h_length h_exps)

theorem toFun_tendsto_bot_of_FirstIsPos {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_basis : WellFormedBasis basis)
    (h_length : exps.length = basis.length)
    (h_coef : coef < 0)
    (h_exps : List.FirstIsPos exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop atBot := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul_atTop_of_neg h_coef
    (Monomial.toFun_tendsto_top_of_FirstIsPos h_basis h_length h_exps)

theorem toFun_tendsto_const_of_AllZero {coef : ℝ} {exps : List ℝ} {basis : Basis}
    (h_exps : List.AllZero exps) :
    let t : Term := ⟨coef, exps⟩
    Tendsto (t.toFun basis) atTop (𝓝 coef) := by
  intro t
  eta_expand
  simp only [toFun, Pi.smul_apply, smul_eq_mul]
  convert Filter.Tendsto.const_mul _ (Monomial.toFun_tendsto_one_of_AllZero h_exps)
  simp [t]

theorem tail_toFun_IsLittleO_head {t : Term} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (h_length : t.monomial.length = basis_tl.length)
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
    Majorized (t.toFun basis_tl) basis_hd 0 := by
  unfold toFun
  apply Majorized.smul
  apply Monomial.tail_toFun_IsLittleO_head h_length h_basis

lemma IsLittleO_of_lt_exps {basis : Basis} {t1 t2 : Term}
    (h_basis : WellFormedBasis basis)
    (h1 : t1.monomial.length = basis.length)
    (h2 : t2.monomial.length = basis.length)
    (h_coef2 : t2.coef ≠ 0)
    (h_lt : t1.monomial < t2.monomial) :
    t1.toFun basis =o[atTop] t2.toFun basis := by
  simp only [toFun]
  pull fun _ ↦ _
  apply Asymptotics.IsBigO.smul_isLittleO
  · simp at h_coef2
    simp
    grind
  apply Monomial.IsLittleO_of_lt h_basis h1 h2 h_lt

theorem IsLittleO_of_lt_exps_left {left right : Basis} {t1 t2 : Term}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.monomial.length = left.length + right.length)
    (h2 : t2.monomial.length = right.length)
    (h_coef2 : t2.coef ≠ 0)
    (h_lt : t1.monomial < List.replicate left.length 0 ++ t2.monomial) :
    t1.toFun (left ++ right) =o[atTop] t2.toFun right := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Term := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Term.toFun ⟨coef2, exps2⟩ right := Term.zeros_append_toFun _
  rw [← this]
  apply Term.IsLittleO_of_lt_exps h_basis <;> simpa [t2']

theorem IsLittleO_of_lt_exps_right {left right : Basis} {t1 t2 : Term}
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : t1.monomial.length = left.length + right.length)
    (h2 : t2.monomial.length = right.length)
    (h_coef1 : t1.coef ≠ 0)
    (h_lt : List.replicate left.length 0 ++ t2.monomial < t1.monomial) :
    t2.toFun right =o[atTop] t1.toFun (left ++ right) := by
  obtain ⟨coef2, exps2⟩ := t2
  let t2' : Term := ⟨coef2, List.replicate left.length 0 ++ exps2⟩
  have : t2'.toFun (left ++ right) = Term.toFun ⟨coef2, exps2⟩ right := Term.zeros_append_toFun _
  rw [← this]
  apply Term.IsLittleO_of_lt_exps h_basis <;> simpa [t2']

end Term

end Tactic.ComputeAsymptotics
