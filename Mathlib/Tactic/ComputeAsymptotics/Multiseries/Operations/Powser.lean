/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Basic
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Operations.Mul
public import Mathlib.Tactic.ComputeAsymptotics.Multiseries.Trimming

/-!
# Substituting multiseries into convergent series

-/

@[expose] public section

open Filter Asymptotics Topology Stream'

namespace ComputeAsymptotics

namespace PreMS

/-- Lazy series is a sequence of real numbers constructed as a formal series
`c₀ + c₁ * x + c₂ * x² + ...`. -/
abbrev LazySeries := Seq ℝ

namespace LazySeries

open Seq

-- I do not know why it is necessary
/-- Recursion principle for lazy series. -/
@[cases_eliminator]
def recOn {motive : LazySeries → Sort*} (s : LazySeries) (nil : motive Seq.nil)
    (cons : ∀ x s, motive (Seq.cons x s)) :
    motive s :=
  Stream'.Seq.recOn s nil cons

/-- Lazy series defined by a function starting from `n`:
```
[f n, f (n + 1), f (n + 2), ...]
```
-/
def ofFnFrom (f : ℕ → ℝ) (n : ℕ) : LazySeries :=
  ⟨fun i ↦ some (f (n + i)), by simp [IsSeq]⟩

/-- Lazy series defined by a function:
```
[f 0, f 1, f 2, ...]
```
-/
def ofFn (f : ℕ → ℝ) : LazySeries :=
  ofFnFrom f 0

theorem ofFnFrom_eq_cons {f : ℕ → ℝ} {n : ℕ} :
    ofFnFrom f n = Seq.cons (f n) (ofFnFrom f (n + 1)) := by
  ext i x
  simp only [ofFnFrom, get?_mk, Option.some.injEq]
  cases i with
  | zero =>
    simp
  | succ i =>
    simp only [get?_cons_succ, get?_mk, Option.some.injEq]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> (convert h using 2; ring)

@[simp]
theorem ofFnFrom_get {f : ℕ → ℝ} {n m : ℕ} : (ofFnFrom f n).get? m = some (f (n + m)) := by
  simp [ofFnFrom]

@[simp]
theorem ofFn_get {f : ℕ → ℝ} {n : ℕ} : (ofFn f).get? n = some (f n) := by
  convert ofFnFrom_get
  omega

-- theorems

/-- Coefficient of the lazy series at index `n`. -/
noncomputable def coeff (s : LazySeries) (n : ℕ) : ℝ :=
  (s.get? n).getD 0

/-- Converts a lazy series to a formal multilinear series. -/
noncomputable def toFormalMultilinearSeries (s : LazySeries) : FormalMultilinearSeries ℝ ℝ ℝ :=
  .ofScalars ℝ (coeff s)

@[simp]
theorem toFormalMultilinearSeries_coeff {s : LazySeries} {n : ℕ} :
    s.toFormalMultilinearSeries.coeff n = (s.get? n).getD 0 := by
  unfold FormalMultilinearSeries.coeff toFormalMultilinearSeries
  eta_expand
  simp_rw [Pi.one_apply, FormalMultilinearSeries.ofScalars_apply_eq, coeff]
  simp

/-- Predicate stating that a lazy series is convergent (has positive radius of convergence). -/
def Convergent (s : LazySeries) : Prop := 0 < s.toFormalMultilinearSeries.radius

open ENNReal in
theorem tail_radius_eq {s_hd : ℝ} {s_tl : LazySeries} :
    (toFormalMultilinearSeries (.cons s_hd s_tl)).radius =
    s_tl.toFormalMultilinearSeries.radius := by
  apply le_antisymm
  · refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    obtain ⟨C, ⟨_, h_bound⟩⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hr
    by_cases hr_pos : r = 0
    · rw [hr_pos]
      simp
    replace hr_pos : 0 < r := lt_of_le_of_ne' (zero_le _) hr_pos
    apply FormalMultilinearSeries.le_radius_of_bound (C := C / r)
    intro n
    specialize h_bound (n + 1)
    simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, toFormalMultilinearSeries_coeff,
      get?_cons_succ, Real.norm_eq_abs, pow_succ, ← mul_assoc] at h_bound ⊢
    rwa [le_div_iff₀]
    simpa
  · refine le_of_forall_nnreal_lt (fun r hr ↦ ?_)
    obtain ⟨C, ⟨_, h_bound⟩⟩ := FormalMultilinearSeries.norm_mul_pow_le_of_lt_radius _ hr
    by_cases hr_pos : r = 0
    · rw [hr_pos]
      simp
    replace hr_pos : 0 < r := lt_of_le_of_ne' (zero_le _) hr_pos
    apply FormalMultilinearSeries.le_radius_of_bound (C := (C * r) ⊔ |s_hd|)
    intro n
    cases n with
    | zero =>
      simp [toFormalMultilinearSeries_coeff]
    | succ m =>
      specialize h_bound m
      simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, toFormalMultilinearSeries_coeff,
        get?_cons_succ, Real.norm_eq_abs, le_sup_iff]
      left
      simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, toFormalMultilinearSeries_coeff,
        Real.norm_eq_abs, pow_succ, ← mul_assoc] at h_bound ⊢
      rw [← div_le_iff₀, mul_div_assoc, ← NNReal.coe_div, div_self hr_pos.ne.symm] <;> simpa

theorem cons_convergent {s_hd : ℝ} {s_tl : LazySeries} (h_convergent : Convergent s_tl) :
    Convergent (.cons s_hd s_tl) := by
  simp only [Convergent]
  rw [tail_radius_eq]
  exact h_convergent

theorem tail_convergent {s_hd : ℝ} {s_tl : LazySeries}
    (h_convergent : Convergent (.cons s_hd s_tl)) :
    Convergent s_tl := by
  simp only [Convergent] at *
  rwa [← tail_radius_eq]

/-- The function represented by a lazy series. -/
noncomputable def toFun (s : LazySeries) : ℝ → ℝ :=
  s.toFormalMultilinearSeries.sum

@[simp]
theorem toFun_nil : toFun Seq.nil = 0 := by
  simp only [toFun]
  unfold toFormalMultilinearSeries coeff
  simp only [get?_nil, Option.getD_none]
  unfold FormalMultilinearSeries.ofScalars FormalMultilinearSeries.sum
  simp
  rfl

theorem toFun_cons {s_hd : ℝ} {s_tl : LazySeries} {t : ℝ}
    (h : Convergent (Seq.cons s_hd s_tl))
    (ht : t ∈ EMetric.ball 0 (toFormalMultilinearSeries (Seq.cons s_hd s_tl)).radius) :
    toFun (.cons s_hd s_tl) t = s_hd + t * ((toFun s_tl) t) := by
  have h_tl := tail_convergent h
  have h_hsum := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h
  replace h_hsum := HasFPowerSeriesOnBall.hasSum h_hsum ht
  have h_hsum_tl := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h_tl
  replace h_hsum_tl := HasFPowerSeriesOnBall.hasSum h_hsum_tl (tail_radius_eq ▸ ht)
  simp only [FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, zero_add] at h_hsum h_hsum_tl
  simp_rw [toFormalMultilinearSeries_coeff] at h_hsum h_hsum_tl
  unfold toFun
  generalize (toFormalMultilinearSeries (Seq.cons s_hd s_tl)).sum t = a at *
  generalize (toFormalMultilinearSeries s_tl).sum t = b at *
  apply HasSum.unique h_hsum
  replace h_hsum_tl := HasSum.mul_right t h_hsum_tl
  ring_nf at h_hsum_tl
  conv at h_hsum_tl =>
    arg 1
    ext i
    rw [← pow_succ']
    rw [show Seq.get? s_tl i = Seq.get? (.cons s_hd s_tl) (i + 1) by simp]
  have := HasSum.zero_add (f := (fun n ↦ t ^ n * (Seq.get? (Seq.cons s_hd s_tl) n).getD 0))
    h_hsum_tl
  convert this using 2
  simp

theorem toFun_cons_eventually_eq {s_hd : ℝ} {s_tl : LazySeries}
    (h : Convergent (Seq.cons s_hd s_tl)) :
    toFun (.cons s_hd s_tl) =ᶠ[𝓝 0] (fun t ↦ s_hd + t * ((toFun s_tl) t)) := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  use EMetric.ball 0 (toFormalMultilinearSeries (Seq.cons s_hd s_tl)).radius
  refine ⟨EMetric.ball_mem_nhds 0 h, fun t ht ↦ ?_⟩
  rw [toFun_cons h ht]

theorem toFun_of_HasFPowerSeriesAt {s : LazySeries} {f : ℝ → ℝ}
    (h : HasFPowerSeriesAt f s.toFormalMultilinearSeries 0) :
    s.toFun =ᶠ[𝓝 0] f := by
  simp only [toFun]
  obtain ⟨r, h⟩ := h
  rw [Filter.eventuallyEq_iff_exists_mem]
  use EMetric.ball 0 r
  constructor
  · refine EMetric.ball_mem_nhds 0 h.r_pos
  simp only [Set.EqOn]
  intro x hx
  rw [← HasFPowerSeriesOnBall.sum h hx]
  simp

theorem convergent_of_HasFPowerSeriesAt {s : LazySeries} {f : ℝ → ℝ}
    (h : HasFPowerSeriesAt f s.toFormalMultilinearSeries 0) :
    s.Convergent := HasFPowerSeriesAt.radius_pos h

theorem toFun_tendsto_head {s_hd : ℝ} {s_tl : LazySeries}
    (h_convergent : Convergent (.cons s_hd s_tl)) :
    Tendsto (toFun (.cons s_hd s_tl)) (𝓝 0) (𝓝 s_hd) := by
  have : (toFun (.cons s_hd s_tl)) 0 = s_hd := by
    simp only [toFun, FormalMultilinearSeries.sum, FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [tsum_eq_zero_add']
    · simp only [pow_zero, one_mul, ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, zero_pow, zero_mul, tsum_zero, add_zero]
      unfold toFormalMultilinearSeries
      simp [FormalMultilinearSeries.ofScalars, FormalMultilinearSeries.coeff, coeff]
    · simpa using summable_zero
  conv =>
    arg 3
    rw [← this]
  apply ContinuousAt.tendsto
  have h_hsum := FormalMultilinearSeries.hasFPowerSeriesOnBall _ h_convergent
  replace h_hsum := HasFPowerSeriesOnBall.hasFPowerSeriesAt h_hsum
  exact HasFPowerSeriesAt.continuousAt h_hsum

theorem toFun_IsBigO_one {s : LazySeries} (h_convergent : s.Convergent) {f : ℝ → ℝ}
    (hF : Tendsto f atTop (𝓝 0)) : ((toFun s) ∘ f) =O[atTop] (1 : ℝ → ℝ) := by
  cases s with
  | nil =>
    simp only [toFun_nil, Pi.zero_comp]
    apply isBigO_zero
  | cons s_hd s_tl =>
    apply isBigO_const_of_tendsto (y := s_hd) _ (by exact ne_zero_of_eq_one rfl)
    apply Tendsto.comp _ hF
    apply toFun_tendsto_head h_convergent

theorem toFun_Majorated_zero {s : LazySeries} (h_convergent : s.Convergent) {f basis_hd : ℝ → ℝ}
    (hf : Tendsto f atTop (𝓝 0)) (h_basis : Tendsto basis_hd atTop atTop) :
    Majorated ((toFun s) ∘ f) basis_hd 0 := by
  intro exp h_pos
  apply IsBigO.trans_isLittleO (toFun_IsBigO_one h_convergent hf)
  eta_expand
  simp only [Pi.one_apply, isLittleO_one_left_iff, Real.norm_eq_abs]
  apply Tendsto.comp Filter.tendsto_abs_atTop_atTop
  exact Tendsto.comp (tendsto_rpow_atTop h_pos) h_basis

theorem convergent_of_all_le_one {s : LazySeries} (h : ∀ x ∈ s, |x| ≤ 1) : s.Convergent := by
  simp only [Convergent]
  apply lt_of_lt_of_le (b := 1)
  · simp
  apply FormalMultilinearSeries.le_radius_of_bound (C := 1)
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, toFormalMultilinearSeries_coeff,
    Real.norm_eq_abs, NNReal.coe_one, one_pow, mul_one]
  intro n
  cases h_get : s.get? n with
  | none => simp
  | some val =>
  apply h
  exact get?_mem h_get

end LazySeries

-- TODO: move
theorem mul_bounded_Majorated {f g basis_hd : ℝ → ℝ} {exp : ℝ} (hf : Majorated f basis_hd exp)
    (hg : g =O[atTop] (fun _ ↦ (1 : ℝ))) :
    Majorated (f * g) basis_hd exp := by
  simp only [Majorated] at *
  intro exp h_exp
  conv =>
    rhs; ext t; rw [← mul_one (basis_hd t ^ exp)]
  apply IsLittleO.mul_isBigO
  · exact hf _ h_exp
  · exact hg

/-- `SeqMS`-part of `PreMS.powser`. -/
noncomputable def SeqMS.powser (s : LazySeries) {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : SeqMS basis_hd basis_tl) : SeqMS basis_hd basis_tl :=
  let T := LazySeries
  let g : T → Option (ℝ × PreMS basis_tl × SeqMS basis_hd basis_tl × T) := fun s =>
    match s.destruct with
    | none => none
    | some (c, cs) =>
      some (0, PreMS.const _ c, ms, cs)
  SeqMS.gcorec g SeqMS.mul s

/-- Applies a lazy series to a multiseries: `c0 * ms + c1 * ms^2 + c2 * ms^3 + ...`. -/
noncomputable def powser (s : LazySeries) {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    (ms : PreMS (basis_hd :: basis_tl)) : PreMS (basis_hd :: basis_tl) :=
  mk (SeqMS.powser s ms.seq) (s.toFun ∘ ms.toFun)

@[simp]
theorem powser_toFun {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} :
    (powser s ms).toFun = s.toFun ∘ ms.toFun :=
  rfl

@[simp]
theorem powser_seq {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} :
    (powser s ms).seq = SeqMS.powser s ms.seq :=
  rfl

@[simp]
theorem SeqMS.powser_nil {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} :
    SeqMS.powser .nil ms = .nil := by
  simp [SeqMS.powser, SeqMS.gcorec_nil]

@[simp]
theorem SeqMS.powser_cons {s_hd : ℝ} {s_tl : LazySeries}
    {basis_hd : ℝ → ℝ} {basis_tl : Basis} {ms : SeqMS basis_hd basis_tl} :
    (SeqMS.powser (.cons s_hd s_tl) ms) =
    .cons 0 (PreMS.const _ s_hd) (ms.mul (SeqMS.powser s_tl ms)) := by
  simp only [SeqMS.powser]
  rw [SeqMS.gcorec_some]
  rfl

theorem SeqMS.powser_leadingExp_le_zero {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl} :
    (SeqMS.powser s ms).leadingExp ≤ 0 := by
  cases s <;> simp

theorem SeqMS.powser_Sorted {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : SeqMS basis_hd basis_tl}
    (h_wo : ms.Sorted) (h_neg : ms.leadingExp < 0) :
    (SeqMS.powser s ms).Sorted := by
  let motive (X : SeqMS basis_hd basis_tl) : Prop :=
    ∃ s, X = SeqMS.powser s ms
  apply SeqMS.Sorted.mul_coind motive
  · use s
  intro exp coef tl ⟨s, h_eq⟩
  cases s with
  | nil => simp at h_eq
  | cons s_hd s_tl =>
  simp only [powser_cons, SeqMS.cons_eq_cons] at h_eq
  simp only [h_eq, PreMS.const_Sorted, SeqMS.mul_leadingExp, WithBot.coe_zero, true_and]
  constructor
  · generalize ms.leadingExp = x at *
    have : (SeqMS.powser s_tl ms).leadingExp ≤ 0 := powser_leadingExp_le_zero
    generalize (SeqMS.powser s_tl ms).leadingExp = y at *
    cases x <;> cases y <;> simp; norm_cast at this h_neg ⊢; linarith
  exact ⟨_, _, rfl, h_wo, s_tl, rfl⟩

theorem powser_Sorted {s : LazySeries} {basis_hd : ℝ → ℝ} {basis_tl : Basis}
    {ms : PreMS (basis_hd :: basis_tl)} (h_wo : ms.Sorted) (h_neg : ms.leadingExp < 0) :
    (powser s ms).Sorted := by
  simp only [Sorted_iff_Seq_Sorted, leadingExp_def, powser_seq] at *
  exact SeqMS.powser_Sorted h_wo h_neg

theorem powser_Approximates {s : LazySeries} (h_convergent : s.Convergent) {basis_hd : ℝ → ℝ}
    {basis_tl : Basis} {ms : PreMS (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl))
    (h_neg : ms.leadingExp < 0) (h_wo : ms.Sorted)
    (h_approx : ms.Approximates) : (powser s ms).Approximates := by
  have hf_tendsto_zero : Tendsto ms.toFun atTop (𝓝 0) := by
    apply neg_leadingExp_tendsto_zero h_neg h_approx
  let motive (X : PreMS (basis_hd :: basis_tl)) : Prop :=
    ∃ (s : LazySeries), s.Convergent ∧ X ≈ powser s ms
  apply Approximates.mul_coind h_basis motive (powser_Sorted h_wo h_neg)
  · use s
  rintro X ⟨s, h_convergent, h_seq_eq, hf_eq⟩
  cases s with
  | nil =>
    simp at hf_eq
    simp [h_seq_eq, hf_eq]
  | cons s_hd s_tl =>
  right
  simp only [powser_toFun] at hf_eq
  simp only [↓existsAndEq, h_seq_eq, powser_seq, SeqMS.powser_cons, mul_seq, SeqMS.cons_eq_cons,
    Sorted_iff_Seq_Sorted, true_and, const_toFun', real_real_rpow_zero, one_mul]
  have : LazySeries.toFun (Seq.cons s_hd s_tl) ∘ ms.toFun =ᶠ[atTop]
      (fun t ↦ s_hd + t * ((LazySeries.toFun s_tl) t)) ∘ ms.toFun := by
    apply Filter.EventuallyEq.comp_tendsto _ hf_tendsto_zero
    exact LazySeries.toFun_cons_eventually_eq h_convergent
  use ms, powser s_tl ms
  simp only [powser_seq, const_Approximates h_basis.tail, powser_toFun, h_approx,
    SeqMS.powser_Sorted (by simpa using h_wo) h_neg, true_and]
  constructorm* _ ∧ _
  · apply Majorated_of_EventuallyEq hf_eq
    apply LazySeries.toFun_Majorated_zero h_convergent hf_tendsto_zero
    apply basis_tendsto_top h_basis
    simp
  · grw [hf_eq, this]
    apply EventuallyEq.of_eq
    ext t
    simp
  simp only [equiv_def, powser_seq, powser_toFun, motive]
  refine ⟨s_tl, LazySeries.tail_convergent h_convergent, rfl, by rfl⟩

section Zeros

/-- Infinite sequence of zeros. -/
def zeros : LazySeries := Seq.corec (fun () ↦ some (0, ())) ()

open LazySeries

theorem zeros_eq_cons : zeros = .cons 0 zeros := by
  simp only [zeros]
  nth_rw 1 [Seq.corec_cons]
  rfl

@[simp]
theorem zeros_get {n : ℕ} : zeros.get? n = .some 0 := by
  induction n with
  | zero =>
    rw [zeros_eq_cons]
    simp
  | succ =>
    rw [zeros_eq_cons]
    simpa

@[simp]
theorem zeros_toFun : zeros.toFun = 0 := by
  simp only [LazySeries.toFun, toFormalMultilinearSeries]
  unfold FormalMultilinearSeries.sum FormalMultilinearSeries.ofScalars
  simp [coeff, zeros_get]
  rfl

@[simp]
theorem zeros_radius : zeros.toFormalMultilinearSeries.radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  simp only [FormalMultilinearSeries.norm_apply_eq_norm_coef, toFormalMultilinearSeries_coeff,
    zeros_get, Option.getD_some, norm_zero, zero_mul, forall_const]
  exact summable_zero

theorem zeros_convergent : Convergent zeros := by
  apply convergent_of_all_le_one
  intro x hx
  apply Seq.all_coind (fun s ↦ s = zeros) _ _ _ hx
  · rfl
  · intro hd tl h_eq
    rw [zeros_eq_cons, Seq.cons_eq_cons] at h_eq
    rw [h_eq.left, h_eq.right]
    simp

-- I am almost sure we don't really need `h_wo` and `h_approx`
theorem zeros_powser_Approximates {basis_hd} {basis_tl} {ms : PreMS (basis_hd :: basis_tl)}
    (h_basis : WellFormedBasis (basis_hd :: basis_tl)) (h_wo : ms.Sorted)
    (h_approx : ms.Approximates) (h_neg : ms.leadingExp < 0) :
    (ms.powser zeros).Approximates :=
  powser_Approximates zeros_convergent h_basis h_neg h_wo h_approx

end Zeros


end PreMS

end ComputeAsymptotics
