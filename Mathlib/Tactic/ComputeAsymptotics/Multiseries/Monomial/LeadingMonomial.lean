/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Monomial.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Trimming

/-!
Here we find the limit of multiseries by reducing the problem to computing limits for its leading
monomial.
-/

@[expose] public section

open Filter Asymptotics Topology

namespace Tactic.ComputeAsymptotics

namespace MultiseriesExpansion

mutual

/-- List of leading exponents of a `Multiseries basis_hd basis_tl`. -/
def Multiseries.exps {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) : UnitMonomial :=
  match ms.head with
  | none => List.replicate (basis_hd :: basis_tl).length 0
  | some (exp, coef) => exp :: coef.exps

/-- List of leading exponents of a `MultiseriesExpansion basis`. -/
def exps {basis : Basis} (ms : MultiseriesExpansion basis) : UnitMonomial :=
  match basis with
  | [] => []
  | List.cons _ _ => ms.seq.exps

end

/-- Real coefficient at the leading monomial of a `MultiseriesExpansion basis`. -/
def realCoef {basis : Basis} (ms : MultiseriesExpansion basis) : ℝ :=
  match basis with
  | [] => ms.toReal
  | List.cons _ _ =>
    match ms.seq.head with
    | none => 0
    | some (_, coef) => coef.realCoef

/-- Leading monomial of a `MultiseriesExpansion basis`. -/
def leadingMonomial {basis : Basis} (ms : MultiseriesExpansion basis) : Monomial :=
  ⟨ms.realCoef, ms.exps⟩

@[simp]
theorem const_realCoef' {ms : MultiseriesExpansion []} :
    ms.realCoef = ms.toReal := rfl

@[simp]
theorem const_exps' {ms : MultiseriesExpansion []} :
    ms.exps = [] := by
  simp [exps]

@[simp]
theorem const_leadingMonomial {ms : MultiseriesExpansion []} :
    ms.leadingMonomial = ⟨ms.toReal, []⟩ := by
  simp [leadingMonomial]

@[simp]
theorem exps_eq_Seq_exps {basis_hd basis_tl} {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.exps = ms.seq.exps := by
  simp [exps, Multiseries.exps]

@[simp]
theorem Multiseries.nil_exps {basis_hd basis_tl} :
    (nil : Multiseries basis_hd basis_tl).exps =
      List.replicate (basis_hd :: basis_tl).length 0 := by
  simp [Multiseries.exps]

@[simp]
theorem Multiseries.cons_exps {basis_hd basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} :
    (cons exp coef tl).exps = exp :: coef.exps := by
  simp [Multiseries.exps]

@[simp]
theorem nil_realCoef {basis_hd} {basis_tl} {f : ℝ → ℝ} :
    (@realCoef (basis_hd :: basis_tl) (mk .nil f)) = 0 := by
  simp [realCoef]

@[simp]
theorem cons_realCoef {basis_hd} {basis_tl} {exp : ℝ} {coef : MultiseriesExpansion basis_tl}
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    (@realCoef (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) =
    coef.realCoef := by
  simp [realCoef]

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
    {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} {coef' : ℝ} {exps : UnitMonomial}
    (h_eq : coef.leadingMonomial = ⟨coef', exps⟩) :
    (@leadingMonomial (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)) =
    ⟨coef', exp :: exps⟩ := by
  rw [cons_leadingMonomial]
  simp [h_eq]

/-- `Monomial.coef ms.coef.leadingMonomial` is equal to `Monomial.coef ms.leadingMonomial`. -/
theorem leadingMonomial_cons_coef {basis_hd} {basis_tl} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ} :
    (@leadingMonomial (basis_hd :: basis_tl) (mk (.cons exp coef tl) f)).coef =
    coef.leadingMonomial.coef := by
  simp [leadingMonomial]

mutual

theorem Multiseries.exps_length {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    ms.exps.length = (basis_hd :: basis_tl).length := by
  cases ms with
  | nil => simp
  | cons exp coef tl =>
    simp only [Multiseries.cons_exps, List.length_cons, Nat.add_right_cancel_iff]
    rw [exps_length]

theorem exps_length {basis : Basis} (ms : MultiseriesExpansion basis) :
    ms.exps.length = basis.length := by
  cases basis with
  | nil => simp
  | cons basis_hd basis_tl =>
    simp only [exps_eq_Seq_exps, List.length_cons]
    rw [Multiseries.exps_length]
    simp

end

theorem leadingMonomial_length {basis : Basis} {ms : MultiseriesExpansion basis} :
    ms.leadingMonomial.unit.length = basis.length := by
  simp [leadingMonomial, exps_length]

theorem Multiseries.exps_ne_nil {basis_hd basis_tl} (ms : Multiseries basis_hd basis_tl) :
    ms.exps ≠ [] := by
  cases ms with
  | nil => simp
  | cons exp coef tl =>
    simp

theorem leadingMonomial_ne_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : MultiseriesExpansion (basis_hd :: basis_tl)} :
    ms.leadingMonomial.unit ≠ [] := by
  simpa [leadingMonomial] using Multiseries.exps_ne_nil _

theorem leadingMonomial_cons_toFun {basis_hd : ℝ → ℝ} {basis_tl : Basis} {exp : ℝ}
    {coef : MultiseriesExpansion basis_tl} {tl : Multiseries basis_hd basis_tl} {f : ℝ → ℝ}
    (t : ℝ) :
    (leadingMonomial (basis := basis_hd :: basis_tl) (mk (.cons exp coef tl) f)).toFun
      (basis_hd :: basis_tl) t =
    (basis_hd t) ^ exp * (leadingMonomial coef).toFun basis_tl t := by
  simp

theorem IsZero_of_leadingMonomial_zero_coef {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_trimmed : ms.Trimmed) (h : ms.leadingMonomial.coef = 0) : IsZero ms:= by
  cases basis with
  | nil => simpa [leadingMonomial] using h
  | cons basis_hd basis_tl =>
    cases ms with
    | nil => simp
    | cons exp coef tl =>
    simp only [leadingMonomial, cons_realCoef, exps_eq_Seq_exps, mk_seq, Multiseries.cons_exps] at h
    replace h_trimmed := Trimmed_cons h_trimmed
    have : IsZero coef := IsZero_of_leadingMonomial_zero_coef h_trimmed.left h
    simp [this] at h_trimmed

/-- If `ms` is not zero, then eventually `ms.leadingMonomial.toFun` is non-zero. -/
theorem leadingMonomial_eventually_ne_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_trimmed : ms.Trimmed) (h_ne_zero : ¬ IsZero ms)
    (h_basis : WellFormedBasis basis) :
    ∀ᶠ t in atTop, ms.leadingMonomial.toFun basis t ≠ 0 := by
  cases basis with
  | nil =>
    simp at h_ne_zero
    simp [h_ne_zero]
  | cons basis_hd basis_tl =>
    cases ms with
    | nil =>
      absurd h_ne_zero
      constructor
    | cons exp coef tl f =>
      obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
      have coef_ih := coef.leadingMonomial_eventually_ne_zero h_coef_trimmed h_coef_ne_zero
        (h_basis.tail)
      apply (coef_ih.and (h_basis.head_eventually_pos)).mono
      rintro t ⟨coef_ih, h_basis_hd_pos⟩
      suffices ¬basis_hd t ^ exp = 0 by
        simp [Monomial.toFun] at coef_ih ⊢
        grind
      exact (Real.rpow_pos_of_pos h_basis_hd_pos _).ne.symm

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
    obtain ⟨h_coef_sorted, h_comp, h_tl_sorted⟩ := h_sorted.elim_cons
    obtain ⟨h_coef, h_maj, h_tl⟩ := h_approx.elim_cons
    have coef_ih := coef.IsEquivalent_leadingMonomial h_coef_sorted h_coef h_coef_trimmed
      (h_basis.tail)
    simp only [IsEquivalent]
    eta_expand
    simp only [Pi.sub_apply]
    cases tl with
    | nil =>
      apply Approximates.elim_nil at h_tl
      apply EventuallyEq.trans_isLittleO h_tl
      apply Asymptotics.isLittleO_zero -- should be simp lemma
    | cons tl_exp tl_coef tl_tl =>
      obtain ⟨_, h_tl_maj, _⟩ := h_tl.elim_cons
      simp only [Multiseries.leadingExp_cons, WithBot.coe_lt_coe] at h_comp
      let exp' := (exp + tl_exp) / 2
      specialize h_tl_maj exp' (by simp only [exp']; linarith)
      apply IsLittleO.trans h_tl_maj
      apply (isLittleO_iff_tendsto' _).mpr
      · pull fun _ ↦ _
        simp_rw [← div_div]
        conv in _ / _ =>
          rw [div_eq_mul_inv, div_mul_comm, div_mul]
        apply (isLittleO_iff_tendsto' _).mp
        · have : (fun t ↦ basis_hd t ^ exp / basis_hd t ^ exp') =ᶠ[atTop]
              fun t ↦ (basis_hd t)^(exp - exp') := by
            apply (h_basis.head_eventually_pos).mono
            intro t h
            simp only
            rw [← Real.rpow_sub h]
          apply IsLittleO.trans_eventuallyEq _ this.symm
          have := IsEquivalent.inv coef_ih
          apply IsEquivalent.trans_isLittleO this
          apply EventuallyEq.trans_isLittleO (Monomial.inv_toFun h_basis.tail).symm
          apply Monomial.tail_toFun_IsLittleO_head
          · rw [Monomial.inv_length, leadingMonomial_length]
          · exact h_basis
          · simp only [exp']
            linarith
        · apply (h_basis.head_eventually_pos).mono
          intro t h1 h2
          absurd h2
          apply div_ne_zero <;> exact (Real.rpow_pos_of_pos h1 _).ne.symm
      · have h_C_ne_zero : ∀ᶠ t in atTop, coef.toFun t ≠ 0 := by
          obtain ⟨φ, h_φ, h_C⟩ := Asymptotics.IsEquivalent.exists_eq_mul coef_ih
          have h_φ_pos : ∀ᶠ t in atTop, 0 < φ t := by
            apply Filter.Tendsto.eventually_const_lt (by simp) h_φ
          apply EventuallyEq.rw (p := fun _ b => b ≠ 0) h_C.symm
          apply (h_φ_pos.and (leadingMonomial_eventually_ne_zero
            h_coef_trimmed h_coef_ne_zero ((h_basis.tail)))).mono
          rintro t ⟨h_φ_pos, h⟩
          exact mul_ne_zero h_φ_pos.ne.symm h
        apply (h_C_ne_zero.and (h_basis.head_eventually_pos)).mono
        rintro t ⟨h_C_ne_zero, h_basis_pos⟩
        intro h
        absurd h
        apply mul_ne_zero _ h_C_ne_zero
        exact (Real.rpow_pos_of_pos h_basis_pos _).ne.symm

  /-- If `f` is approximated by trimmed multiseries `ms`, then it is asymptotically equivalent to
  `ms.leadingMonomial.toFun`. -/
  theorem IsEquivalent_leadingMonomial {basis : Basis} {ms : MultiseriesExpansion basis}
      (h_sorted : ms.Sorted)
      (h_approx : ms.Approximates) (h_trimmed : ms.Trimmed)
      (h_basis : WellFormedBasis basis) :
      ms.toFun ~[atTop] ms.leadingMonomial.toFun basis := by
    cases basis with
    | nil =>
      simp only [const_toFun, leadingMonomial, const_realCoef', const_exps', Monomial.toFun,
        UnitMonomial.toFun_nil]
      convert Asymptotics.IsEquivalent.refl using 1
      ext x
      simp
    | cons basis_hd basis_tl =>
      cases ms with
      | nil =>
        have hF := Approximates.elim_nil h_approx
        unfold leadingMonomial
        simp only [mk_toFun, realCoef, mk_seq, Multiseries.head_nil, exps_eq_Seq_exps,
          Multiseries.nil_exps, List.length_cons, Monomial.zero_coef_toFun']
        apply EventuallyEq.isEquivalent (by assumption)
      | cons exp coef tl f =>
        obtain ⟨h_coef, _, h_tl⟩ := h_approx.elim_cons
        obtain ⟨h_coef_trimmed, h_coef_ne_zero⟩ := Trimmed_cons h_trimmed
        obtain ⟨h_coef_sorted, h_comp, _⟩ := h_sorted.elim_cons
        have coef_ih := coef.IsEquivalent_leadingMonomial h_coef_sorted h_coef h_coef_trimmed
          (h_basis.tail)
        have : f ~[atTop] basis_hd ^ exp * coef.toFun :=
          IsEquivalent_coef h_approx h_sorted h_coef_trimmed h_coef_ne_zero h_basis
        apply IsEquivalent.trans this
        eta_expand
        simp_rw [leadingMonomial_cons_toFun]
        apply IsEquivalent.mul IsEquivalent.refl
        exact coef_ih
end

/-- If `f` is approximated by `ms`, and `ms.realCoef > 0`, then
`f` is eventually positive. -/
theorem eventually_pos_of_coef_pos {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_pos : 0 < ms.realCoef) (h_sorted : ms.Sorted) (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis) :
    ∀ᶠ t in atTop, 0 < ms.toFun t := by
  apply (IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis).eventually_pos
  exact Monomial.toFun_pos h_basis h_pos

/-- If `f` is approximated by `ms`, and `ms` is not zero, then
`f` is eventually non-zero. -/
theorem eventually_ne_zero_of_not_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_ne_zero : ¬ IsZero ms) (h_sorted : ms.Sorted) (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed) (h_basis : WellFormedBasis basis) :
    ∀ᶠ t in atTop, ms.toFun t ≠ 0 := by
  have := IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis
  obtain ⟨φ, hφ_tendsto, h_eq⟩ := Asymptotics.IsEquivalent.exists_eq_mul this
  have hφ : ∀ᶠ t in atTop, 1/2 < φ t := by
    apply Filter.Tendsto.eventually_const_lt _ hφ_tendsto
    linarith
  have h_leadingMonomial := leadingMonomial_eventually_ne_zero h_trimmed h_ne_zero h_basis
  simp only [EventuallyEq] at h_eq
  apply ((h_eq.and hφ).and h_leadingMonomial).mono
  intro t ⟨⟨h_eq, hφ⟩, h_leadingMonomial⟩
  rw [h_eq]
  simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
  constructor
  · linarith
  · exact h_leadingMonomial

/- ## Comparisson of functions by comparisson of leading monomials -/

theorem IsLittleO_of_lt_leadingMonomial_left {left right : Basis}
    {ms1 : MultiseriesExpansion (left ++ right)} {ms2 : MultiseriesExpansion right}
    (h_sorted1 : ms1.Sorted) (h_sorted2 : ms2.Sorted)
    (h_approx1 : ms1.Approximates) (h_approx2 : ms2.Approximates)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (left ++ right))
    (h2 : ¬ IsZero ms2)
    (h_lt : ms1.leadingMonomial.unit < List.replicate left.length 0 ++ ms2.leadingMonomial.unit) :
    ms1.toFun =o[atTop] ms2.toFun := by
  apply Asymptotics.IsEquivalent.trans_isLittleO
    (IsEquivalent_leadingMonomial h_sorted1 h_approx1 h_trimmed1 h_basis)
  apply Asymptotics.IsLittleO.trans_isEquivalent _
    (IsEquivalent_leadingMonomial h_sorted2 h_approx2 h_trimmed2 h_basis.of_append_right).symm
  apply Monomial.IsLittleO_of_lt_exps_left h_basis _ _ _ h_lt
  · simp [leadingMonomial_length]
  · simp [leadingMonomial_length]
  · contrapose! h2
    exact IsZero_of_leadingMonomial_zero_coef h_trimmed2 h2

theorem IsLittleO_of_lt_leadingMonomial_right {left right : Basis}
    {ms1 : MultiseriesExpansion (left ++ right)} {ms2 : MultiseriesExpansion right}
    (h_sorted1 : ms1.Sorted) (h_sorted2 : ms2.Sorted)
    (h_approx1 : ms1.Approximates) (h_approx2 : ms2.Approximates)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (left ++ right))
    (h1 : ¬ IsZero ms1)
    (h_lt : List.replicate left.length 0 ++ ms2.leadingMonomial.unit < ms1.leadingMonomial.unit) :
    ms2.toFun =o[atTop] ms1.toFun := by
  apply Asymptotics.IsEquivalent.trans_isLittleO
    (IsEquivalent_leadingMonomial h_sorted2 h_approx2 h_trimmed2 h_basis.of_append_right)
  apply Asymptotics.IsLittleO.trans_isEquivalent _
    (IsEquivalent_leadingMonomial h_sorted1 h_approx1 h_trimmed1 h_basis).symm
  apply Monomial.IsLittleO_of_lt_exps_right h_basis _ _ _ h_lt
  · simp [leadingMonomial_length]
  · simp [leadingMonomial_length]
  · contrapose! h1
    exact IsZero_of_leadingMonomial_zero_coef h_trimmed1 h1


theorem IsLittleO_of_lt_leadingMonomial {basis : Basis}
    {ms1 ms2 : MultiseriesExpansion basis}
    (h_sorted1 : ms1.Sorted) (h_sorted2 : ms2.Sorted)
    (h_approx1 : ms1.Approximates) (h_approx2 : ms2.Approximates)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis basis)
    (h2 : ¬ IsZero ms2)
    (h_lt : ms1.leadingMonomial.unit < ms2.leadingMonomial.unit) :
    ms1.toFun =o[atTop] ms2.toFun :=
  IsLittleO_of_lt_leadingMonomial_left (left := []) h_sorted1 h_sorted2 h_approx1 h_approx2
    h_trimmed1 h_trimmed2 h_basis h2 h_lt

theorem IsEquivalent_of_leadingMonomial_zeros_append {left right : Basis} {f2 : ℝ → ℝ}
    {ms1 : MultiseriesExpansion (left ++ right)} {ms2 : MultiseriesExpansion right}
    (h_sorted1 : ms1.Sorted) (h_sorted2 : ms2.Sorted)
    (h_approx1 : ms1.Approximates) (h_approx2 : ms2.Approximates)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_f2 : ms2.toFun = f2)
    (h_basis : WellFormedBasis (left ++ right))
    (h_coef : ms1.leadingMonomial.coef = ms2.leadingMonomial.coef)
    (h_exps : List.replicate left.length 0 ++ ms2.leadingMonomial.unit = ms1.leadingMonomial.unit) :
    ms1.toFun ~[atTop] f2 := by
  subst h_f2
  apply Asymptotics.IsEquivalent.trans
    (IsEquivalent_leadingMonomial h_sorted1 h_approx1 h_trimmed1 h_basis)
  apply Asymptotics.IsEquivalent.trans _
    (IsEquivalent_leadingMonomial h_sorted2 h_approx2 h_trimmed2 h_basis.of_append_right).symm
  convert Asymptotics.IsEquivalent.refl using 1
  let t2' : Monomial :=
    ⟨ms2.leadingMonomial.coef, List.replicate left.length 0 ++ ms2.leadingMonomial.unit⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ms2.leadingMonomial right :=
    Monomial.zeros_append_toFun _
  rw [← this]
  congr!
  simp only [t2']
  conv_rhs => change ⟨ms1.leadingMonomial.coef, ms1.leadingMonomial.unit⟩
  congr 1
  rw [h_coef]

theorem IsEquivalent_of_leadingMonomial_zeros_append_mul_coef {left right : Basis}
    {ms1 : MultiseriesExpansion (left ++ right)} {ms2 : MultiseriesExpansion right}
    {coef1 coef2 : ℝ} {exps1 exps2 : UnitMonomial}
    (h_sorted1 : ms1.Sorted) (h_sorted2 : ms2.Sorted)
    (h_approx1 : ms1.Approximates) (h_approx2 : ms2.Approximates)
    (h_trimmed1 : ms1.Trimmed) (h_trimmed2 : ms2.Trimmed)
    (h_basis : WellFormedBasis (left ++ right))
    (h_leading1 : ms1.leadingMonomial = ⟨coef1, exps1⟩)
    (h_leading2 : ms2.leadingMonomial = ⟨coef2, exps2⟩)
    (h_coef : coef1 / coef2 ≠ 0)
    (h_exps : List.replicate left.length 0 ++ exps2 = exps1) :
    ms1.toFun ~[atTop] (coef1 / coef2) • ms2.toFun := by
  apply Asymptotics.IsEquivalent.trans
    (IsEquivalent_leadingMonomial h_sorted1 h_approx1 h_trimmed1 h_basis)
  trans (ms1.leadingMonomial.coef / ms2.leadingMonomial.coef) • (ms2.leadingMonomial.toFun right)
  swap
  · have h_eq :=
      (IsEquivalent_leadingMonomial h_sorted2 h_approx2 h_trimmed2 h_basis.of_append_right).symm
    have : (fun (_ : ℝ) ↦ ms1.leadingMonomial.coef / ms2.leadingMonomial.coef) ~[atTop]
        (fun _ ↦ ms1.leadingMonomial.coef / ms2.leadingMonomial.coef) := by
      rfl
    convert Asymptotics.IsEquivalent.smul this h_eq using 1
    ext t
    simp [h_leading1, h_leading2]
  convert Asymptotics.IsEquivalent.refl using 1
  let t2' : Monomial :=
    ⟨ms2.leadingMonomial.coef, List.replicate left.length 0 ++ ms2.leadingMonomial.unit⟩
  have : t2'.toFun (left ++ right) = Monomial.toFun ms2.leadingMonomial right :=
    Monomial.zeros_append_toFun _
  rw [← this, ← Monomial.smul_toFun]
  congr 1
  simp only [Monomial.smul, h_leading1, h_leading2, h_exps, Monomial.mk.injEq, and_true, t2']
  rw [div_mul_cancel₀]
  contrapose! h_coef
  simp [h_coef]

theorem FirstNonzeroIsPos_ne_zero {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_pos : ms.exps.FirstNonzeroIsPos) :
    ¬ IsZero ms := by
  intro h
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [const_exps'] at h_pos
    cases h_pos
  · apply UnitMonomial.AllZero.not_FirstNonzeroIsPos _ h_pos
    cases h with | nil f =>
    simp only [exps_eq_Seq_exps, mk_seq, Multiseries.nil_exps, List.length_cons]
    exact UnitMonomial.AllZero.replicate

/- ## Leading terms of basic constructions -/

@[simp]
theorem const_realCoef {basis : Basis} {c : ℝ} :
    (@MultiseriesExpansion.const basis c).realCoef = c := by
  cases basis with
  | nil => simp [const, realCoef, ofReal, toReal]
  | cons basis_hd basis_tl =>
    simp only [realCoef, const, Multiseries.const, mk_seq, Multiseries.head_cons]
    rw [const_realCoef]

mutual

@[simp]
theorem Multiseries.const_exps {basis_hd : ℝ → ℝ} {basis_tl : Basis} {c : ℝ} :
    (Multiseries.const basis_hd basis_tl c).exps =
      List.replicate (basis_hd :: basis_tl).length 0 := by
  simp only [Multiseries.const, Multiseries.cons_exps, List.length_cons]
  rw [const_exps]
  simp [List.replicate_succ]

@[simp]
theorem const_exps {basis : Basis} {c : ℝ} :
    (@MultiseriesExpansion.const basis c).exps = List.replicate basis.length 0 := by
  cases basis with
  | nil => simp
  | cons =>
    simp only [exps_eq_Seq_exps, const_seq, List.length_cons]
    rw [Multiseries.const_exps]
    simp

end

theorem const_leadingMonomial_eq {basis : Basis} {c : ℝ} :
    (@MultiseriesExpansion.const basis c).leadingMonomial = ⟨c, List.replicate basis.length 0⟩ := by
  simp [leadingMonomial, const_realCoef, const_exps]

theorem monomialRpow_realCoef {basis : Basis} {n : ℕ} {r : ℝ} (h : n < basis.length) :
    (@MultiseriesExpansion.monomialRpow basis n r).realCoef = 1 := by
  cases basis with
  | nil => simp at h
  | cons basis_hd basis_tl =>
    cases n with
    | zero =>
      simp [realCoef, Multiseries.monomialRpow, one, const_realCoef]
    | succ n =>
      simp [realCoef, Multiseries.monomialRpow, monomialRpow_realCoef (by simpa using h)]

mutual

theorem Multiseries.monomialRpow_exps {basis_hd : ℝ → ℝ} {basis_tl : Basis} {n : ℕ} {r : ℝ}
    (h : n < (basis_hd :: basis_tl).length) :
    (Multiseries.monomialRpow basis_hd basis_tl n r).exps =
    List.replicate n 0 ++ r :: List.replicate ((basis_hd :: basis_tl).length - n - 1) 0 := by
  cases n with
  | zero => simp [Multiseries.monomialRpow, one]
  | succ n =>
    simp only [Multiseries.monomialRpow, Multiseries.cons_exps, List.replicate_succ,
      List.length_cons, Nat.reduceSubDiff, List.cons_append, List.cons.injEq, true_and]
    rw [monomialRpow_exps (by simpa using h)]

theorem monomialRpow_exps {basis : Basis} {n : ℕ} {r : ℝ} (h : n < basis.length) :
    (@MultiseriesExpansion.monomialRpow basis n r).exps =
    List.replicate n 0 ++ r :: List.replicate (basis.length - n - 1) 0 := by
  cases basis with
  | nil => simp at h
  | cons basis_hd basis_tl =>
    simp only [exps_eq_Seq_exps, monomialRpow_seq, List.length_cons]
    rw [Multiseries.monomialRpow_exps h]
    simp

end

theorem monomialRpow_leadingMonomial_eq {basis : Basis} {n : ℕ} (h : n < basis.length) (r : ℝ) :
    (@MultiseriesExpansion.monomialRpow basis n r).leadingMonomial =
    ⟨1, List.replicate n 0 ++ r :: List.replicate (basis.length - n - 1) 0⟩ := by
  simp [leadingMonomial, monomialRpow_realCoef h, monomialRpow_exps h]

theorem monomial_leadingMonomial_eq {basis : Basis} {n : ℕ} (h : n < basis.length) :
    (@MultiseriesExpansion.monomial basis n).leadingMonomial =
      ⟨1, List.replicate n 0 ++ 1 :: List.replicate (basis.length - n - 1) 0⟩ :=
  monomialRpow_leadingMonomial_eq h 1

theorem extendBasisEnd_leadingMonomial_eq {basis : Basis} {b : ℝ → ℝ}
    {ms : MultiseriesExpansion basis} :
    (ms.extendBasisEnd b).leadingMonomial =
    ⟨ms.leadingMonomial.coef, ms.leadingMonomial.unit ++ [0]⟩ := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp [extendBasisEnd, leadingMonomial, const, Multiseries.const, ofReal]
  cases ms with
  | nil f =>
    simp [extendBasisEnd, leadingMonomial, List.replicate_succ', Multiseries.extendBasisEnd]
  | cons exp coef tl f =>
    have := extendBasisEnd_leadingMonomial_eq (b := b) (ms := coef)
    simp [leadingMonomial] at this
    simp [extendBasisEnd, leadingMonomial, Multiseries.extendBasisEnd, this]

lemma log_basis_getLast_IsLittleO_aux {basis : Basis}
    {ms : MultiseriesExpansion basis}
    (h_pos : ms.exps.FirstNonzeroIsPos) :
    basis ≠ [] := by
  contrapose! h_pos
  subst h_pos
  simp [const_exps']

-- TODO: move?
set_option backward.isDefEq.respectTransparency false in
/-- Logarithm of the last basis element is little-o of any function approximated in the basis. -/
theorem log_basis_getLast_IsLittleO {basis : Basis} (h_basis : WellFormedBasis basis)
    {ms : MultiseriesExpansion basis} (h_sorted : ms.Sorted) (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed) (h_pos : ms.leadingMonomial.unit.FirstNonzeroIsPos) :
    (Real.log ∘ (basis.getLast (log_basis_getLast_IsLittleO_aux h_pos))) =o[atTop] ms.toFun := by
  simp only [leadingMonomial] at h_pos
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [const_exps'] at h_pos
    cases h_pos
  have h_basis' := h_basis.push_log_last
  let ms' :
      MultiseriesExpansion
        (basis_hd :: basis_tl ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
    ms.extendBasisEnd (Real.log ∘ (basis_hd :: basis_tl).getLast (by simp))
  have h_sorted' : ms'.Sorted := MultiseriesExpansion.extendBasisEnd_Sorted h_sorted
  have h_approx' : ms'.Approximates :=
    MultiseriesExpansion.extendBasisEnd_Approximates h_basis' h_approx
  have h_trimmed' : ms'.Trimmed := extendBasisEnd_Trimmed h_trimmed
  have h_toFun : ms'.toFun = ms.toFun := by
    simp [ms']
  let ms_log :
      MultiseriesExpansion
        (basis_hd :: basis_tl ++ [Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)]) :=
    MultiseriesExpansion.monomial _ (basis_tl.length + 1)
  have h_log_sorted : ms_log.Sorted := monomial_Sorted
  have h_log_approx : ms_log.Approximates :=
    monomial_Approximates (n := ⟨basis_tl.length + 1, by simp⟩) h_basis'
  have h_log_trimmed : ms_log.Trimmed := monomial_Trimmed (by simp)
  have h_log_toFun : ms_log.toFun = (Real.log ∘ (basis_hd :: basis_tl).getLast (by simp)) := by
    simp [ms_log]
  rw [← h_log_toFun, ← h_toFun]
  apply IsLittleO_of_lt_leadingMonomial h_log_sorted h_sorted' h_log_approx h_approx' h_log_trimmed
    h_trimmed' h_basis'
  · exact extendBasisEnd_ne_zero (FirstNonzeroIsPos_ne_zero h_pos)
  simp only [ms_log, ms']
  rw [monomial_leadingMonomial_eq (by simp)]
  simp only [List.cons_append, List.length_cons, List.length_append, List.length_nil, zero_add,
    add_tsub_cancel_left, tsub_self, List.replicate_zero, extendBasisEnd_leadingMonomial_eq]
  have h_len : ms.exps.length = basis_tl.length + 1 := by
    simp only [exps_length, List.length_cons]
  clear * - h_pos h_len
  simp only [leadingMonomial]
  generalize ms.exps = exps at *
  generalize basis_tl.length + 1 = n at *
  induction n generalizing exps with
  | zero =>
    simp only [List.length_eq_zero_iff] at h_len
    simp only [h_len] at h_pos
    cases h_pos
  | succ n ih =>
    obtain _ | ⟨exp, exps_tl⟩ := exps
    · simp at h_len
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h_len
    simp only [UnitMonomial.FirstNonzeroIsPos.cons_iff] at h_pos
    rcases h_pos with h_pos | ⟨rfl, h_pos⟩
    · exact List.Lex.rel h_pos
    apply List.Lex.cons
    apply ih _ h_pos h_len

/- ## Computing limits by inspecting the leading terms of expansions -/

-- TODO: remove assumptions here using `zero_of_leadingMonomial_zero_coef`
theorem tendsto_zero_of_zero_coef {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_sorted : ms.Sorted)
    (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : UnitMonomial}
    (h_eq : ms.leadingMonomial = ⟨t_coef, t_exps⟩)
    (h_coef : t_coef = 0) :
    Tendsto ms.toFun atTop (𝓝 0) := by
  apply (IsEquivalent.tendsto_nhds_iff
    (IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis)).mpr
  rw [h_eq]
  apply Monomial.tendsto_zero_of_coef_zero _ h_coef

theorem tendsto_const_of_AllZero {basis : Basis} {ms : MultiseriesExpansion basis} {f : ℝ → ℝ}
    (h_sorted : ms.Sorted)
    (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : UnitMonomial}
    (h_eq : ms.leadingMonomial = ⟨t_coef, t_exps⟩)
    (h_exps : t_exps.AllZero)
    (hf_eq : f = ms.toFun) :
    Tendsto f atTop (𝓝 t_coef) := by
  rw [hf_eq]
  apply (IsEquivalent.tendsto_nhds_iff
    (IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis)).mpr
  rw [h_eq]
  apply Monomial.toFun_tendsto_const_of_AllZero h_exps

theorem tendsto_zero_of_FirstNonzeroIsNeg_aux {basis : Basis} {ms : MultiseriesExpansion basis}
    (h_sorted : ms.Sorted)
    (h_approx : ms.Approximates)
    {t_coef : ℝ} {t_exps : UnitMonomial}
    (h_eq : ms.leadingMonomial = ⟨t_coef, t_exps⟩)
    (h_exps : t_exps.FirstNonzeroIsNeg) :
    Tendsto ms.toFun atTop (𝓝 0) := by
  obtain _ | ⟨basis_hd, basis_tl⟩ := basis
  · simp only [leadingMonomial, realCoef, exps, Monomial.mk.injEq, List.nil_eq] at h_eq
    simp [h_eq.right] at h_exps
  cases ms with
  | nil =>
    apply Approximates.elim_nil at h_approx
    apply Tendsto.congr' h_approx.symm
    apply tendsto_const_nhds
  | cons exp coef tl f =>
    obtain ⟨h_coef_sorted, h_comp, h_tl_sorted⟩ := h_sorted.elim_cons
    obtain ⟨h_coef_approx, h_maj, h_tl_approx⟩ := h_approx.elim_cons
    simp only [leadingMonomial, realCoef, mk_seq, Multiseries.head_cons, exps_eq_Seq_exps,
      Multiseries.cons_exps, Monomial.mk.injEq] at h_eq
    simp only [← h_eq.right, UnitMonomial.FirstNonzeroIsNeg.cons_iff] at h_exps
    obtain h_neg | h_zero := h_exps
    · exact Majorized.tendsto_zero_of_neg h_neg h_maj
    have hC : Tendsto coef.toFun atTop (𝓝 0) := by
      apply tendsto_zero_of_FirstNonzeroIsNeg_aux (t_coef := t_coef) h_coef_sorted h_coef_approx _
        h_zero.right
      rw [← h_eq.left]
      rfl
    have h_tl : Tendsto (f - coef.toFun) atTop (𝓝 0) := by
      have h : Tendsto (fun t ↦ f t - basis_hd t ^ exp * coef.toFun t) atTop (𝓝 0) := by
        apply neg_leadingExp_tendsto_zero _ h_tl_approx
        convert h_comp
        simp [h_zero.left]
      apply Tendsto.congr' _ h
      simp [h_zero.left]
      rfl
    simpa using Tendsto.add h_tl hC

theorem tendsto_zero_of_FirstNonzeroIsNeg {basis : Basis} {ms : MultiseriesExpansion basis}
    {f : ℝ → ℝ}
    (h_sorted : ms.Sorted)
    (h_approx : ms.Approximates)
    {t_coef : ℝ} {t_exps : UnitMonomial}
    (h_eq : ms.leadingMonomial = ⟨t_coef, t_exps⟩)
    (h_exps : t_exps.FirstNonzeroIsNeg)
    (hf_eq : f = ms.toFun) :
    Tendsto f atTop (𝓝 0) := by
  rw [hf_eq]
  apply tendsto_zero_of_FirstNonzeroIsNeg_aux h_sorted h_approx h_eq h_exps

theorem tendsto_top_of_FirstNonzeroIsPos {basis : Basis} {ms : MultiseriesExpansion basis}
    {f : ℝ → ℝ}
    (h_sorted : ms.Sorted)
    (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : UnitMonomial}
    (h_eq : ms.leadingMonomial = ⟨t_coef, t_exps⟩)
    (h_exps : t_exps.FirstNonzeroIsPos)
    (h_coef : 0 < t_coef)
    (hf_eq : f = ms.toFun) :
    Tendsto f atTop atTop := by
  rw [hf_eq]
  apply (IsEquivalent.tendsto_atTop_iff
    (IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis)).mpr
  simp [leadingMonomial] at h_eq
  apply Monomial.toFun_tendsto_top_of_FirstNonzeroIsPos h_basis leadingMonomial_length
  all_goals simpa [leadingMonomial, h_eq]

theorem tendsto_bot_of_FirstNonzeroIsPos {basis : Basis} {ms : MultiseriesExpansion basis}
    {f : ℝ → ℝ}
    (h_sorted : ms.Sorted)
    (h_approx : ms.Approximates)
    (h_trimmed : ms.Trimmed)
    (h_basis : WellFormedBasis basis)
    {t_coef : ℝ} {t_exps : UnitMonomial}
    (h_eq : ms.leadingMonomial = ⟨t_coef, t_exps⟩)
    (h_exps : t_exps.FirstNonzeroIsPos)
    (h_coef : t_coef < 0)
    (hf_eq : f = ms.toFun) :
    Tendsto f atTop atBot := by
  rw [hf_eq]
  apply (IsEquivalent.tendsto_atBot_iff
    (IsEquivalent_leadingMonomial h_sorted h_approx h_trimmed h_basis)).mpr
  simp [leadingMonomial] at h_eq
  apply Monomial.toFun_tendsto_bot_of_FirstNonzeroIsPos h_basis leadingMonomial_length
  all_goals simpa [leadingMonomial, h_eq]

end MultiseriesExpansion

end Tactic.ComputeAsymptotics
