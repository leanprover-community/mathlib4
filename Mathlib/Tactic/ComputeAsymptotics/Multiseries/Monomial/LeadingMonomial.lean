/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Monomial.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Trimming

/-!
# Leading monomial of a multiseries

In this file we define the *leading monomial* of a multiseries: the `Monomial` obtained by
descending along the heads of the nested expansion, i.e. the first summand of the series.

If the multiseries is trimmed, then its leading monomial carries the whole asymptotic behaviour
of the approximated function. This reduces computing the limit of a multiseries to computing the
limit of a single monomial, which is done in
`Mathlib/Tactic/ComputeAsymptotics/Multiseries/Monomial/Basic.lean`.

## Main definitions

* `leadingCoef ms` is the coefficient of the leading monomial of `ms`.
* `leadingUnit ms` and `Multiseries.leadingUnit ms` are its unit part, i.e. the list of exponents
  `[e₁, ..., eₙ]` of the basis functions.
* `leadingMonomial ms` packs them together into a `Monomial`.

## Main theorems

* `IsEquivalent_leadingMonomial`: if `ms` is sorted, trimmed and approximates its attached
  function, then this function is asymptotically equivalent to `ms.leadingMonomial.toFun`.

-/

@[expose] public section

open Filter Asymptotics Topology

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

mutual

/-- Unit part of the leading monomial of a `Multiseries basis_hd basis_tl`. -/
def Multiseries.leadingUnit {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    UnitMonomial :=
  match ms.head with
  | none => List.replicate (basis_hd :: basis_tl).length 0
  | some (exp, coef) => exp :: coef.leadingUnit

/-- Unit part of the leading monomial of a `MultiseriesExpansion basis`. -/
def leadingUnit {basis : Basis} (ms : MultiseriesExpansion basis) : UnitMonomial :=
  match basis with
  | [] => []
  | List.cons _ _ => ms.seq.leadingUnit

end

/-- Coefficient of the leading monomial of a `MultiseriesExpansion basis`. -/
def leadingCoef {basis : Basis} (ms : MultiseriesExpansion basis) : ℝ :=
  match basis with
  | [] => ms.toReal
  | List.cons _ _ =>
    match ms.seq.head with
    | none => 0
    | some (_, coef) => coef.leadingCoef

/-- Leading monomial of a `MultiseriesExpansion basis`. -/
def leadingMonomial {basis : Basis} (ms : MultiseriesExpansion basis) : Monomial :=
  ⟨ms.leadingCoef, ms.leadingUnit⟩

@[simp]
theorem const_leadingCoef' {ms : MultiseriesExpansion []} :
    ms.leadingCoef = ms.toReal := rfl

@[simp]
theorem const_leadingUnit' {ms : MultiseriesExpansion []} :
    ms.leadingUnit = [] := by
  simp [leadingUnit]

@[simp]
theorem const_leadingMonomial {ms : MultiseriesExpansion []} :
    ms.leadingMonomial = ⟨ms.toReal, []⟩ := by
  simp [leadingMonomial]

@[simp]
theorem leadingUnit_eq_seq_leadingUnit {basis_hd basis_tl}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.leadingUnit = ms.seq.leadingUnit := by
  simp [leadingUnit, Multiseries.leadingUnit]

@[simp]
theorem Multiseries.nil_leadingUnit {basis_hd basis_tl} :
    (nil : Multiseries basis_hd basis_tl).leadingUnit =
      List.replicate (basis_hd :: basis_tl).length 0 := by
  simp [Multiseries.leadingUnit]

@[simp]
theorem Multiseries.cons_leadingUnit {basis_hd basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).leadingUnit = exp :: coef.leadingUnit := by
  simp [Multiseries.leadingUnit]

@[simp]
theorem nil_leadingCoef {basis_hd} {basis_tl} {f : ℝ → ℝ} :
    (@leadingCoef (basis_hd :: basis_tl) (mk .nil f)) = 0 :=
  rfl

@[simp]
theorem cons_leadingCoef {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    (@leadingCoef (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) =
    coef.leadingCoef :=
  rfl

@[simp]
theorem nil_leadingMonomial {basis_hd basis_tl} {f : ℝ → ℝ} :
    (@leadingMonomial (basis_hd :: basis_tl) (mk .nil f)) =
    ⟨0, List.replicate (basis_hd :: basis_tl).length 0⟩ := by
  simp [leadingMonomial]

@[simp]
theorem cons_leadingMonomial {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    (@leadingMonomial (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) =
    ⟨coef.leadingMonomial.coef, exp :: coef.leadingMonomial.unit⟩ := by
  simp [leadingMonomial]

theorem cons_leadingMonomial' {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} {coef' : ℝ} {unit : UnitMonomial}
    (h_eq : coef.leadingMonomial = ⟨coef', unit⟩) :
    (@leadingMonomial (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) =
    ⟨coef', exp :: unit⟩ := by
  simp [h_eq]

/-- `Monomial.coef ms.coef.leadingMonomial` is equal to `Monomial.coef ms.leadingMonomial`. -/
theorem leadingMonomial_cons_coef {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    (@leadingMonomial (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)).coef =
    coef.leadingMonomial.coef :=
  rfl

mutual

theorem Multiseries.leadingUnit_length {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    ms.leadingUnit.length = (basis_hd :: basis_tl).length := by
  cases ms with
  | nil => simp
  | cons exp coef tl => simp [leadingUnit_length coef]

theorem leadingUnit_length {basis : Basis} (ms : MultiseriesExpansion basis) :
    ms.leadingUnit.length = basis.length := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl => simp [Multiseries.leadingUnit_length ms.seq]

end

theorem leadingMonomial_length {basis : Basis} {ms : MultiseriesExpansion basis} :
    ms.leadingMonomial.unit.length = basis.length := by
  simp [leadingMonomial, leadingUnit_length]

theorem Multiseries.leadingUnit_ne_nil {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    ms.leadingUnit ≠ [] := by
  cases ms <;> simp

theorem leadingMonomial_ne_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.leadingMonomial.unit ≠ [] := by
  simpa [leadingMonomial] using Multiseries.leadingUnit_ne_nil _

theorem leadingMonomial_cons_toFun {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    (t : ℝ) :
    (leadingMonomial (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)).toFun
      (basis_hd :: basis_tl) t =
    (basis_hd t) ^ exp * (leadingMonomial coef).toFun basis_tl t := by
  simp

theorem IsZero_of_leadingMonomial_zero_coef {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_trimmed : ms.Trimmed) (h : ms.leadingMonomial.coef = 0) : IsZero ms := by
  cases basis with
  | nil => simpa [leadingMonomial] using h
  | cons basis_hd basis_tl =>
    cases ms with
    | nil => simp
    | cons exp coef tl =>
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed.elim_cons
      rw [leadingMonomial_cons_coef] at h
      exact absurd (IsZero_of_leadingMonomial_zero_coef h_coef_trimmed h) h_coef_ne_zero

/-- If `ms` is not zero, then eventually `ms.leadingMonomial.toFun` is non-zero. -/
theorem leadingMonomial_eventually_ne_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_trimmed : ms.Trimmed) (h_ne_zero : ¬ IsZero ms)
    (h_basis : WellFormedBasis basis) :
    ∀ᶠ t in atTop, ms.leadingMonomial.toFun basis t ≠ 0 := by
  cases basis with
  | nil => simp_all
  | cons basis_hd basis_tl =>
    cases ms with
    | nil => exact absurd (by constructor) h_ne_zero
    | cons exp coef tl f =>
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed.elim_cons
      filter_upwards [coef.leadingMonomial_eventually_ne_zero h_coef_trimmed h_coef_ne_zero
        h_basis.tail, h_basis.head_eventually_pos] with t coef_ih h_basis_hd_pos
      simpa [Monomial.toFun, (Real.rpow_pos_of_pos h_basis_hd_pos exp).ne'] using coef_ih

mutual
  /-- If function `f` is approximated by `cons (exp, coef) tl` and `coef` approximates `fC`, then
  `f` is asymptotically equivalent to `fC * basis_hd ^ exp`. -/
  theorem IsEquivalent_coef {basis_hd f : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
      {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl}
      (h_approx : Approximates (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f))
      (h_sorted : Sorted (mk (.cons exp coef tl) f))
      (h_coef_trimmed : coef.Trimmed)
      (h_coef_ne_zero : ¬ IsZero coef)
      (h_basis : WellFormedBasis (basis_hd :: basis_tl)) :
      f ~[atTop] basis_hd ^ exp * coef.toFun := by
    obtain ⟨h_coef_sorted, h_comp, -⟩ := h_sorted.elim_cons
    obtain ⟨h_coef, -, h_tl⟩ := h_approx.elim_cons
    have coef_ih := coef.IsEquivalent_leadingMonomial h_coef_sorted h_coef h_coef_trimmed
      h_basis.tail
    eta_expand
    simp only [IsEquivalent]
    cases tl with
    | nil => exact (Approximates.elim_nil h_tl).trans_isLittleO (isLittleO_zero _ _)
    | cons tl_exp tl_coef tl_tl =>
      obtain ⟨_, h_tl_maj, _⟩ := h_tl.elim_cons
      simp only [Multiseries.leadingExp_cons, WithBot.coe_lt_coe] at h_comp
      let exp' := (exp + tl_exp) / 2
      specialize h_tl_maj exp' (by simp only [exp']; linarith)
      apply IsLittleO.trans h_tl_maj
      apply (isLittleO_iff_tendsto' _).mpr
      · pull fun _ ↦ _
        simp_rw [← div_div]
        conv in _ / _ => rw [div_eq_mul_inv, div_mul_comm, div_mul]
        apply (isLittleO_iff_tendsto' _).mp
        · have : (fun t ↦ basis_hd t ^ exp / basis_hd t ^ exp') =ᶠ[atTop]
              fun t ↦ (basis_hd t) ^ (exp - exp') := by
            filter_upwards [h_basis.head_eventually_pos] with t h using (Real.rpow_sub h ..).symm
          apply IsLittleO.trans_eventuallyEq _ this.symm
          apply IsEquivalent.trans_isLittleO (IsEquivalent.inv coef_ih)
          apply EventuallyEq.trans_isLittleO (Monomial.inv_toFun h_basis.tail).symm
          refine Monomial.majorized_tail_toFun_head ?_ h_basis _ ?_
          · rw [Monomial.inv_length, leadingMonomial_length]
          · simp only [exp']
            linarith
        · filter_upwards [h_basis.head_eventually_pos] with t h1 h2 using
            absurd h2 (div_ne_zero (Real.rpow_pos_of_pos h1 _).ne' (Real.rpow_pos_of_pos h1 _).ne')
      · have h_C_ne_zero : ∀ᶠ t in atTop, coef.toFun t ≠ 0 := by
          obtain ⟨φ, h_φ, h_C⟩ := coef_ih.exists_eq_mul
          apply EventuallyEq.rw (p := fun _ b => b ≠ 0) h_C.symm
          filter_upwards [h_φ.eventually_const_lt zero_lt_one,
            leadingMonomial_eventually_ne_zero h_coef_trimmed h_coef_ne_zero h_basis.tail]
            with t h_φ_pos h using mul_ne_zero h_φ_pos.ne' h
        filter_upwards [h_C_ne_zero, h_basis.head_eventually_pos] with t h_C_ne_zero h_basis_pos h
        exact absurd h (mul_ne_zero (Real.rpow_pos_of_pos h_basis_pos _).ne' h_C_ne_zero)

  /-- If `f` is approximated by trimmed multiseries `ms`, then it is asymptotically equivalent to
  `ms.leadingMonomial.toFun`. -/
  theorem IsEquivalent_leadingMonomial {basis : Basis} {ms : MultiseriesExpansion basis}
      (h_sorted : ms.Sorted)
      (h_approx : ms.Approximates) (h_trimmed : ms.Trimmed)
      (h_basis : WellFormedBasis basis) :
      ms.toFun ~[atTop] ms.leadingMonomial.toFun basis := by
    cases basis with
    | nil =>
      refine EventuallyEq.isEquivalent (Eventually.of_forall fun x ↦ ?_)
      simp [leadingMonomial, Monomial.toFun]
    | cons basis_hd basis_tl =>
      cases ms with
      | nil =>
        rw [nil_leadingMonomial, Monomial.zero_coef_toFun']
        exact (Approximates.elim_nil h_approx).isEquivalent
      | cons exp coef tl f =>
        obtain ⟨h_coef, -, -⟩ := h_approx.elim_cons
        obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := h_trimmed.elim_cons
        obtain ⟨h_coef_sorted, -, -⟩ := h_sorted.elim_cons
        refine (IsEquivalent_coef h_approx h_sorted h_coef_trimmed h_coef_ne_zero h_basis).trans ?_
        eta_expand
        simp_rw [leadingMonomial_cons_toFun]
        exact IsEquivalent.mul IsEquivalent.refl
          (coef.IsEquivalent_leadingMonomial h_coef_sorted h_coef h_coef_trimmed h_basis.tail)
end

/-- If `f` is approximated by `ms`, and `ms.leadingCoef > 0`, then
`f` is eventually positive. -/
theorem eventually_pos_of_coef_pos {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_pos : 0 < ms.leadingCoef) (h_sorted : ms.Sorted) (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis) :
    ∀ᶠ t in atTop, 0 < ms.toFun t :=
  (IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis).eventually_pos
    (Monomial.toFun_pos h_basis h_pos)

/-- If `f` is approximated by `ms`, and `ms` is not zero, then
`f` is eventually non-zero. -/
theorem eventually_ne_zero_of_not_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_ne_zero : ¬ IsZero ms) (h_sorted : ms.Sorted) (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis) :
    ∀ᶠ t in atTop, ms.toFun t ≠ 0 := by
  obtain ⟨φ, hφ_tendsto, h_eq⟩ :=
    (IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis).exists_eq_mul
  have hφ : ∀ᶠ t in atTop, 1 / 2 < φ t := hφ_tendsto.eventually_const_lt (by norm_num)
  filter_upwards [h_eq, hφ,
    leadingMonomial_eventually_ne_zero h_trimmed h_ne_zero h_basis] with t h_eq hφ h_lm
  simp only [h_eq, Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
  exact ⟨by linarith, h_lm⟩

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
