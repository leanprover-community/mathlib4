/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.Data.Polynomial.Derivative2

/-!
# The Lindemann-Weierstrass theorem
-/

noncomputable section

open scoped Nat

open Complex Polynomial

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]

theorem DifferentiableAt.real_of_complex {e : ℂ → ℂ} {z : ℝ} (h : DifferentiableAt ℂ e ↑z) :
    DifferentiableAt ℝ (fun x : ℝ => e ↑x) z :=
  (h.restrictScalars ℝ).comp z ofRealClm.differentiable.differentiableAt
#align differentiable_at.real_of_complex DifferentiableAt.real_of_complex

theorem Differentiable.real_of_complex {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ fun x : ℝ => e ↑x :=
  (h.restrictScalars ℝ).comp ofRealClm.differentiable
#align differentiable.real_of_complex Differentiable.real_of_complex

theorem deriv_eq_f (p : ℂ[X]) (s : ℂ) :
    (deriv fun x ↦ -(cexp (-(x • s)) * p.sumIderiv.eval (x • s))) =
      fun x : ℝ ↦ s * (cexp (-(x • s)) * p.eval (x • s)) := by
  have h :
    (fun y : ℝ => p.sumIderiv.eval (y • s)) =
      (fun x => p.sumIderiv.eval x) ∘ fun y => y • s :=
    rfl
  funext x
  rw [deriv.neg, deriv_mul, deriv_cexp, deriv.neg]
  any_goals simp_rw [h]; clear h
  rw [deriv_smul_const, deriv_id'', deriv.comp, Polynomial.deriv, deriv_smul_const, deriv_id'']
  simp_rw [one_smul, mul_assoc, ← mul_add]
  have h :
    s * p.sumIderiv.eval (x • s) -
        (derivative (R := ℂ) (sumIderiv p)).eval (x • s) * s =
      s * p.eval (x • s)
  · conv_lhs =>
      congr
      rw [sumIderiv_eq_self_add, sumIderiv_derivative]
    rw [mul_comm _ s, eval_add, mul_add, add_sub_cancel]
  rw [← mul_neg, neg_add', neg_mul, neg_neg, h, mul_left_comm]
  any_goals apply Differentiable.differentiableAt
  rotate_left 5; apply @Differentiable.real_of_complex fun c : ℂ => exp (-(c * s))
  rotate_left; apply Differentiable.comp; apply @Differentiable.restrictScalars ℝ _ ℂ
  any_goals
    repeat'
      first
      | exact differentiable_id
      | apply Polynomial.differentiable
      | apply Differentiable.smul_const
      | apply Differentiable.neg
      | apply Differentiable.cexp
      | apply Differentiable.mul_const
#align deriv_eq_f deriv_eq_f

theorem integral_f_eq (p : ℂ[X]) (s : ℂ) :
    s * ∫ x in (0)..1, exp (-(x • s)) * p.eval (x • s) =
      -(exp (-s) * p.sumIderiv.eval s) -
        -p.sumIderiv.eval 0 := by
  rw [← intervalIntegral.integral_const_mul]
  convert
    intervalIntegral.integral_deriv_eq_sub'
      (fun x : ℝ => -(exp (-(x • s)) * p.sumIderiv.eval (x • s)))
      (deriv_eq_f p s) _ _
  · rw [one_smul]
  · rw [one_smul]
  · simp_rw [zero_smul, neg_zero, Complex.exp_zero, one_mul]
  · intro x _; apply (Differentiable.mul _ _).neg.differentiableAt
    apply @Differentiable.real_of_complex fun c : ℂ => exp (-(c * s))
    refine' (differentiable_id.mul_const _).neg.cexp
    change Differentiable ℝ ((fun y : ℂ => p.sumIderiv.eval y) ∘ fun x : ℝ => x • s)
    apply Differentiable.comp
    apply @Differentiable.restrictScalars ℝ _ ℂ; exact Polynomial.differentiable _
    exact differentiable_id'.smul_const _
  · refine' (continuous_const.mul ((continuous_id'.smul continuous_const).neg.cexp.mul _)).continuousOn
    change Continuous ((fun y : ℂ => p.eval y) ∘ fun x : ℝ => x • s)
    exact p.continuous_aeval.comp (continuous_id'.smul continuous_const)
#align integral_f_eq integral_f_eq

def P (p : ℂ[X]) (s : ℂ) :=
  exp s * p.sumIderiv.eval 0 - p.sumIderiv.eval s
set_option linter.uppercaseLean3 false in
#align P P

theorem P_le' (p : ℕ → ℂ[X]) (s : ℂ)
    (h :
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q : ℕ,
      Complex.abs (P (p q) s) ≤
        Real.exp s.re * (Real.exp (Complex.abs s) * c ^ q * (Complex.abs s)) := by
  simp_rw [P]; cases' h with c hc; replace hc := fun q x hx => (hc q x hx).trans (le_abs_self _)
  simp_rw [_root_.abs_pow] at hc; use |c|, abs_nonneg _; intro q
  have h := integral_f_eq (p q) s
  rw [← @mul_right_inj' _ _ (exp s) _ _ (exp_ne_zero _),
    neg_sub_neg, mul_sub, ← mul_assoc _ (exp _), ← exp_add, add_neg_self, exp_zero, one_mul] at h
  replace h := congr_arg Complex.abs h
  simp_rw [map_mul, abs_exp] at h
  rw [← h, mul_le_mul_left (Real.exp_pos _), mul_comm]
  apply mul_le_mul_of_nonneg_right _ (Complex.abs.nonneg _)
  rw [intervalIntegral.integral_of_le zero_le_one, ← Complex.norm_eq_abs, ← mul_one (_ * _)]
  clear h
  convert MeasureTheory.norm_set_integral_le_of_norm_le_const' _ _ _
  · rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  · exact measurableSet_Ioc
  intro x hx; rw [norm_mul]; refine' mul_le_mul _ (hc q x hx) (norm_nonneg _) (Real.exp_pos _).le
  rw [norm_eq_abs, abs_exp, Real.exp_le_exp]; apply (re_le_abs _).trans;
  rw [← norm_eq_abs, norm_neg, norm_smul, norm_eq_abs, Real.norm_of_nonneg hx.1.le]
  exact mul_le_of_le_one_left (Complex.abs.nonneg _) hx.2
set_option linter.uppercaseLean3 false in
#align P_le' P_le'

theorem P_le (p : ℕ → ℂ[X]) (s : ℂ)
    (h :
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1,
        Complex.abs ((p q).eval (x • s)) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q ≥ 1, Complex.abs (P (p q) s) ≤ c ^ q := by
  simp_rw []; obtain ⟨c', hc', h'⟩ := P_le' p s h; clear h
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp (Complex.abs s)) 1
  have h₂ : 0 ≤ Real.exp (Complex.abs s) := (Real.exp_pos _).le
  let c₃ := max (Complex.abs s) 1; have h₃ : 0 ≤ (Complex.abs s) := Complex.abs.nonneg _
  have hc : ∀ {x : ℝ}, 0 ≤ max x 1 := fun {x} => zero_le_one.trans (le_max_right _ _)
  use c₁ * (c₂ * c' * c₃), mul_nonneg hc (mul_nonneg (mul_nonneg hc hc') hc)
  intro q hq; refine' (h' q).trans _; simp_rw [mul_pow]
  have hcq : ∀ {x : ℝ}, 0 ≤ max x 1 ^ q := fun {x} => pow_nonneg hc q
  have hcq' := pow_nonneg hc' q
  have le_max_one_pow : ∀ {x : ℝ}, x ≤ max x 1 ^ q := fun {x} =>
    (max_cases x 1).elim (fun h => h.1.symm ▸ le_self_pow h.2 (zero_lt_one.trans_le hq).ne')
      fun h => by rw [h.1, one_pow]; exact h.2.le
  refine' mul_le_mul le_max_one_pow _ (mul_nonneg (mul_nonneg h₂ hcq') h₃) hcq
  refine' mul_le_mul _ le_max_one_pow h₃ (mul_nonneg hcq hcq')
  refine' mul_le_mul le_max_one_pow le_rfl hcq' hcq
set_option linter.uppercaseLean3 false in
#align P_le P_le

open Polynomial

theorem Int.coe_castRingHom' {α} [NonAssocRing α] : ⇑(castRingHom α) = Int.cast :=
  rfl

theorem exp_polynomial_approx (p : ℤ[X]) (p0 : p.eval 0 ≠ 0) :
    ∃ c,
      ∀ q > (eval 0 p).natAbs, q.Prime →
        ∃ (n : ℤ) (_ : n % q ≠ 0) (gp : ℤ[X]) (_ : gp.natDegree ≤ q * p.natDegree - 1),
          ∀ {r : ℂ}, r ∈ p.aroots ℂ →
            Complex.abs (n • exp r - q • aeval r gp : ℂ) ≤ c ^ q / (q - 1)! := by
  let p' q := (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ)
  have : ∀ s : ℂ, ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc (0 : ℝ) 1,
      Complex.abs ((p' q).eval (x • s)) ≤ c ^ q
  · intro s; dsimp only
    simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, map_mul,
      Complex.abs_pow, real_smul, map_mul, abs_ofReal, ← eval₂_eq_eval_map, ← aeval_def]
    have : Bornology.IsBounded
        ((fun x : ℝ => max (x * abs s) 1 * Complex.abs (aeval (x * s) p)) '' Set.Ioc 0 1)
    · have h :
        (fun x : ℝ => max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) '' Set.Ioc 0 1 ⊆
          (fun x : ℝ => max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) '' Set.Icc 0 1 :=
        Set.image_subset _ Set.Ioc_subset_Icc_self
      refine' (IsCompact.image isCompact_Icc _).isBounded.subset h
      · refine' ((continuous_id.mul continuous_const).max continuous_const).mul _
        refine' Complex.continuous_abs.comp (p.continuous_aeval.comp _)
        exact continuous_ofReal.mul continuous_const
    cases' this.exists_norm_le with c h
    use c; intro q x hx
    specialize h (max (x * abs s) 1 * Complex.abs (aeval (↑x * s) p)) (Set.mem_image_of_mem _ hx)
    refine' le_trans _ (pow_le_pow_left (norm_nonneg _) h _)
    simp_rw [norm_mul, Real.norm_eq_abs, Complex.abs_abs, mul_pow, abs_of_pos hx.1]
    refine' mul_le_mul_of_nonneg_right _ (pow_nonneg (Complex.abs.nonneg _) _)
    rw [max_def]; split_ifs with hx1
    · rw [_root_.abs_one, one_pow, ← mul_pow]
      exact pow_le_one _ (mul_nonneg hx.1.le (Complex.abs.nonneg _)) hx1
    · push_neg at hx1
      rw [_root_.abs_mul, Complex.abs_abs, ← mul_pow, abs_of_pos hx.1]
      exact pow_le_pow_right hx1.le (Nat.sub_le _ _)
  choose c' c'0 Pp'_le using fun r ↦ P_le p' r (this r)
  let c :=
    if h : ((p.aroots ℂ).map c').toFinset.Nonempty then ((p.aroots ℂ).map c').toFinset.max' h else 0
  have hc : ∀ x ∈ p.aroots ℂ, c' x ≤ c
  · intro x hx; dsimp only
    split_ifs with h
    · apply Finset.le_max'; rw [Multiset.mem_toFinset]
      refine' Multiset.mem_map_of_mem _ hx
    · rw [Finset.nonempty_iff_ne_empty, Ne.def, Multiset.toFinset_eq_empty,
        Multiset.eq_zero_iff_forall_not_mem] at h
      push_neg at h
      exact absurd (Multiset.mem_map_of_mem _ hx) (h (c' x))
  use c
  intro q q_gt prime_q
  have q0 : 0 < q := Nat.Prime.pos prime_q
  obtain ⟨gp', -, h'⟩ := sumIderiv_sl' ℤ (X ^ (q - 1) * p ^ q) q0
  simp_rw [RingHom.algebraMap_toAlgebra, map_id] at h'
  specialize h' (RingHom.injective_int _) 0 (by rw [C_0, sub_zero])
  rw [eval_pow] at h'
  use p.eval 0 ^ q + q • aeval (0 : ℤ) gp'
  rw [exists_prop]
  constructor
  · rw [Int.add_emod, nsmul_eq_mul, Int.mul_emod_right, add_zero, Int.emod_emod, Ne.def, ←
      Int.dvd_iff_emod_eq_zero]
    intro h
    replace h := Int.Prime.dvd_pow' prime_q h; rw [Int.coe_nat_dvd_left] at h
    replace h := Nat.le_of_dvd (Int.natAbs_pos.mpr p0) h
    revert h; rwa [imp_false, not_le]
  obtain ⟨gp, gp'_le, h⟩ := sumIderiv_sl ℂ (X ^ (q - 1) * p ^ q) q
  refine' ⟨gp, _, _⟩
  · refine' gp'_le.trans ((tsub_le_tsub_right natDegree_mul_le q).trans _)
    rw [natDegree_X_pow, natDegree_pow, tsub_add_eq_add_tsub (Nat.one_le_of_lt q0),
      tsub_right_comm]
    apply tsub_le_tsub_right; rw [add_tsub_cancel_left]
  intro r hr
  have :
    (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ) =
      (X - C r) ^ q *
        (X ^ (q - 1) *
          (C (map (algebraMap ℤ ℂ) p).leadingCoeff *
              (((p.aroots ℂ).erase r).map fun a : ℂ => X - C a).prod) ^
            q)
  · rw [mul_left_comm, ← mul_pow, mul_left_comm (_ - _),
      Multiset.prod_map_erase (f := fun a =>  X - C a) hr]
    have : Multiset.card (p.aroots ℂ) = (p.map (algebraMap ℤ ℂ)).natDegree :=
      splits_iff_card_roots.mp (IsAlgClosed.splits _)
    rw [C_leadingCoeff_mul_prod_multiset_X_sub_C this, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, map_X]
  specialize h r this; clear this
  rw [le_div_iff (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _), ← abs_natCast, ← map_mul,
    mul_comm, mul_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, smul_smul, mul_comm,
    Nat.mul_factorial_pred q0, ← h]
  rw [nsmul_eq_mul, ← Int.cast_ofNat, ← zsmul_eq_mul, smul_smul, mul_add, ← nsmul_eq_mul, ←
    nsmul_eq_mul, smul_smul, mul_comm, Nat.mul_factorial_pred q0, ← h', zsmul_eq_mul, aeval_def,
    eval₂_at_zero, eq_intCast, Int.cast_id, ← Int.coe_castRingHom', ← algebraMap_int_eq, ←
    eval₂_at_zero, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map, mul_comm, ← sumIderiv_map, ← P]
  exact (Pp'_le r q (Nat.one_le_of_lt q0)).trans (pow_le_pow_left (c'0 r) (hc r hr) _)
#align exp_polynomial_approx exp_polynomial_approx
