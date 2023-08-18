/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao

! This file was ported from Lean 3 source module main
-/
import Mathlib.Algebra.BigOperators.Finsupp
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Polynomials
import Mathlib.Data.Complex.Exponential
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.RingTheory.Algebraic
import Mathlib.Algebra.CharP.Algebra

import Mathlib.Data.Polynomial.Derivative2
import Mathlib.FieldTheory.GalConj

-- assert_not_exists Module.Dual
-- attribute [-reducible] Module.Dual

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

noncomputable section

open scoped BigOperators Classical Polynomial

open Finset

namespace Finsupp

variable {α M N : Type _}

theorem indicator_const_eq_sum_single [AddCommMonoid M] (s : Finset α) (m : M) :
    (indicator s fun _ _ => m) = ∑ x in s, single x m :=
  (indicator_eq_sum_single _ _).trans <| @sum_attach _ _ _ _ fun i => single i m
#align finsupp.indicator_const_eq_sum_single Finsupp.indicator_const_eq_sum_single

@[to_additive (attr := simp)]
theorem prod_indicator_const_index [Zero M] [CommMonoid N] {s : Finset α} (m : M) {h : α → M → N}
    (h_zero : ∀ a ∈ s, h a 0 = 1) : (indicator s fun _ _ => m).prod h = ∏ x in s, h x m :=
  (prod_indicator_index _ h_zero).trans <| @prod_attach _ _ _ _ fun i => h i m
#align finsupp.prod_indicator_const_index Finsupp.prod_indicator_const_index
#align finsupp.sum_indicator_const_index Finsupp.sum_indicator_const_index

end Finsupp

namespace Polynomial

section

variable {R k : Type _} [Semiring R]

theorem mem_roots_map_of_injective {p : R[X]} [CommRing k] [IsDomain k] {f : R →+* k}
    (hf : Function.Injective f) {x : k} (hp : p ≠ 0) : x ∈ (p.map f).roots ↔ p.eval₂ f x = 0 :=
  by
  rw [mem_roots ((Polynomial.map_ne_zero_iff hf).mpr hp)]
  dsimp only [IsRoot]
  rw [Polynomial.eval_map]
#align polynomial.mem_roots_map_of_injective Polynomial.mem_roots_map_of_injective

end

section

variable {R k : Type _} [CommRing R]

theorem mem_rootSet_of_injective {p : R[X]} [CommRing k] [IsDomain k] [Algebra R k]
    (h : Function.Injective (algebraMap R k)) {x : k} (hp : p ≠ 0) :
    x ∈ p.rootSet k ↔ aeval x p = 0 :=
  Multiset.mem_toFinset.trans (mem_roots_map_of_injective h hp)
#align polynomial.mem_root_set_of_injective Polynomial.mem_rootSet_of_injective

end

end Polynomial

open Polynomial

open scoped Nat

variable {R A : Type _} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]


open Complex

theorem DifferentiableAt.real_of_complex {e : ℂ → ℂ} {z : ℝ} (h : DifferentiableAt ℂ e ↑z) :
    DifferentiableAt ℝ (fun x : ℝ => e ↑x) z :=
  (h.restrictScalars ℝ).comp z ofRealClm.differentiable.differentiableAt
#align differentiable_at.real_of_complex DifferentiableAt.real_of_complex

theorem Differentiable.real_of_complex {e : ℂ → ℂ} (h : Differentiable ℂ e) :
    Differentiable ℝ fun x : ℝ => e ↑x :=
  (h.restrictScalars ℝ).comp ofRealClm.differentiable
#align differentiable.real_of_complex Differentiable.real_of_complex

theorem deriv_eq_f (p : ℂ[X]) (s : ℂ) :
    (deriv fun x : ℝ =>
        -(exp (-(x • exp (s.arg • I))) * p.sumIderiv.eval (x • exp (s.arg • I))) /
          exp (s.arg • I)) =
      fun x : ℝ => exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) :=
  by
  have h :
    (fun y : ℝ => p.sumIderiv.eval (y • exp (s.arg • I))) =
      (fun x => p.sumIderiv.eval x) ∘ fun y => y • exp (s.arg • I) :=
    rfl
  funext x
  rw [deriv_div_const, deriv.neg, deriv_mul, deriv_cexp, deriv.neg]
  any_goals simp_rw [h]; clear h
  rw [deriv_smul_const, deriv_id'', deriv.comp, Polynomial.deriv, deriv_smul_const, deriv_id'']
  simp_rw [derivative_map, one_smul, mul_assoc, ← mul_add]
  have h :
    exp (s.arg • I) * p.sumIderiv.eval (x • exp (s.arg • I)) -
        (derivative (R := ℂ) (sumIderiv p)).eval (x • exp (s.arg • I)) * exp (s.arg • I) =
      p.eval (x • exp (s.arg • I)) * exp (s.arg • I) :=
    by
    conv_lhs =>
      congr
      rw [sumIderiv_eq_self_add, sumIderiv_derivative]
    rw [mul_comm, eval_add, add_mul, add_sub_cancel]
  rw [← mul_neg, neg_add', neg_mul, neg_neg, h, ← mul_assoc, mul_div_cancel]
  exact exp_ne_zero _
  any_goals apply Differentiable.differentiableAt
  rotate_left 5; apply @Differentiable.real_of_complex fun c : ℂ => exp (-(c * exp (s.arg • I)))
  rotate_left; apply Differentiable.comp; apply @Differentiable.restrictScalars ℝ _ ℂ
  any_goals
    repeat'
      first
      | apply Differentiable.neg
      | apply Differentiable.cexp
      | apply Differentiable.mul_const
      | apply Polynomial.differentiable
      | apply Differentiable.smul_const
      | exact differentiable_id
#align deriv_eq_f deriv_eq_f

theorem integral_f_eq (p : ℂ[X]) (s : ℂ) :
    ∫ x in (0)..(Complex.abs s), exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) =
      -(exp (-s) * p.sumIderiv.eval s) / exp (s.arg • I) - -p.sumIderiv.eval 0 / exp (s.arg • I) :=
  by
  convert
    intervalIntegral.integral_deriv_eq_sub'
      (fun x : ℝ =>
        -(exp (-(x • exp (s.arg • I))) * p.sumIderiv.eval (x • exp (s.arg • I))) / exp (s.arg • I))
      (deriv_eq_f p s) _ _
  any_goals simp_rw [real_smul, abs_mul_exp_arg_mul_I]
  · simp_rw [zero_smul, neg_zero, Complex.exp_zero, one_mul]
    simp only [ofReal_zero, zero_mul, neg_zero, exp_zero, one_mul]
  · intro x hx; apply ((Differentiable.mul _ _).neg.div_const _).differentiableAt
    apply @Differentiable.real_of_complex fun c : ℂ => exp (-(c * exp (s.arg • I)))
    refine' (differentiable_id.mul_const _).neg.cexp
    change Differentiable ℝ ((fun y : ℂ => p.sumIderiv.eval y) ∘ fun x : ℝ => x • exp (s.arg • I))
    apply Differentiable.comp
    apply @Differentiable.restrictScalars ℝ _ ℂ; exact Polynomial.differentiable _
    exact differentiable_id'.smul_const _
  · refine' ((continuous_id'.smul continuous_const).neg.cexp.mul _).continuousOn
    change Continuous ((fun y : ℂ => p.eval y) ∘ fun x : ℝ => x • exp (s.arg • I))
    exact p.continuous_aeval.comp (continuous_id'.smul continuous_const)
#align integral_f_eq integral_f_eq

def P (p : ℂ[X]) (s : ℂ) :=
  exp s * p.sumIderiv.eval 0 - p.sumIderiv.eval s
#align P P

theorem p_le' (p : ℕ → ℂ[X]) (s : ℂ)
    (h : ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 (Complex.abs s), Complex.abs ((p q).eval (x • exp (s.arg • I))) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q : ℕ, Complex.abs (P (p q) s) ≤ Real.exp s.re * (Real.exp (Complex.abs s) * c ^ q * (Complex.abs s)) :=
  by
  simp_rw [P]; cases' h with c hc; replace hc := fun q x hx => (hc q x hx).trans (le_abs_self _)
  simp_rw [_root_.abs_pow] at hc ; use |c|, abs_nonneg _; intro q
  have h := integral_f_eq (p q) s
  rw [← sub_div, eq_div_iff (exp_ne_zero _), ← @mul_right_inj' _ _ (exp s) _ _ (exp_ne_zero _),
    neg_sub_neg, mul_sub, ← mul_assoc _ (exp _), ← exp_add, add_neg_self, exp_zero, one_mul] at h
  replace h := congr_arg Complex.abs h
  simp_rw [map_mul, abs_exp, smul_re, I_re, smul_zero, Real.exp_zero, mul_one] at h
  rw [← h, mul_le_mul_left (Real.exp_pos _), ← Complex.norm_eq_abs,
    intervalIntegral.integral_of_le (Complex.abs.nonneg _)]
  clear h
  convert MeasureTheory.norm_set_integral_le_of_norm_le_const' _ _ _
  · rw [Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal (Complex.abs.nonneg _)]
  · rw [Real.volume_Ioc, sub_zero]; exact ENNReal.ofReal_lt_top
  · exact measurableSet_Ioc
  intro x hx; rw [norm_mul]; refine' mul_le_mul _ (hc q x hx) (norm_nonneg _) (Real.exp_pos _).le
  rw [norm_eq_abs, abs_exp, Real.exp_le_exp]; apply (re_le_abs _).trans;
  rw [← norm_eq_abs, norm_neg, norm_smul, norm_eq_abs, abs_exp, smul_re, I_re, smul_zero,
    Real.exp_zero, mul_one, Real.norm_eq_abs, abs_eq_self.mpr hx.1.le]
  exact hx.2
#align P_le' p_le'

theorem p_le (p : ℕ → ℂ[X]) (s : ℂ)
    (h : ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 (Complex.abs s), Complex.abs ((p q).eval (x • exp (s.arg • I))) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q ≥ 1, Complex.abs (P (p q) s) ≤ c ^ q :=
  by
  simp_rw []; obtain ⟨c', hc', h'⟩ := p_le' p s h; clear h
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp (Complex.abs s)) 1; have h₂ : 0 ≤ Real.exp (Complex.abs s) := (Real.exp_pos _).le
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
#align P_le p_le

open Polynomial

theorem Int.coe_castRingHom' {α} [NonAssocRing α] : ⇑(castRingHom α) = Int.cast :=
  rfl

theorem exp_polynomial_approx (p : ℤ[X]) (p0 : p.eval 0 ≠ 0) :
    ∃ c,
      ∀ q > (eval 0 p).natAbs,
        ∀ (prime_q : Nat.Prime q),
          ∃ (n : ℤ) (hn : n % q ≠ 0) (gp : ℤ[X]) (gp_le : gp.natDegree ≤ q * p.natDegree - 1),
            ∀ {r : ℂ} (hr : r ∈ p.aroots ℂ),
              Complex.abs (n • exp r - q • aeval r gp : ℂ) ≤ c ^ q / (q - 1)! :=
  by
  let p' q := (X ^ (q - 1) * p ^ q).map (algebraMap ℤ ℂ)
  have :
    ∀ s : ℂ,
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 (Complex.abs s), Complex.abs ((p' q).eval (x • exp (s.arg • I))) ≤ c ^ q :=
    by
    intro s; dsimp only []
    simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, map_mul,
      Complex.abs_pow, real_smul, map_mul, abs_exp_ofReal_mul_I, abs_ofReal, mul_one, ←
      eval₂_eq_eval_map, ← aeval_def]
    have :
      Metric.Bounded
        ((fun (x : ℝ) => max |x| 1 * (Complex.abs (aeval (↑x * exp (↑s.arg * I)) p))) '' Set.Ioc 0 (abs s)) :=
      by
      have h :
        (fun (x : ℝ) => max |x| 1 * (Complex.abs (aeval (↑x * exp (↑s.arg * I)) p))) '' Set.Ioc 0 (abs s) ⊆
          (fun (x : ℝ) => max |x| 1 * (Complex.abs (aeval (↑x * exp (↑s.arg * I)) p))) '' Set.Icc 0 (abs s) :=
        Set.image_subset _ Set.Ioc_subset_Icc_self
      refine' (IsCompact.image isCompact_Icc _).bounded.mono h
      · refine' (continuous_id.abs.max continuous_const).mul _
        refine' Complex.continuous_abs.comp (p.continuous_aeval.comp _)
        exact continuous_ofReal.mul continuous_const
    cases' this.exists_norm_le with c h
    use c; intro q x hx
    specialize h (max |x| 1 * Complex.abs (aeval (↑x * exp (↑s.arg * I)) p)) (Set.mem_image_of_mem _ hx)
    refine' le_trans _ (pow_le_pow_of_le_left (norm_nonneg _) h _)
    simp_rw [norm_mul, Real.norm_eq_abs, Complex.abs_abs, mul_pow]
    refine' mul_le_mul_of_nonneg_right _ (pow_nonneg (Complex.abs.nonneg _) _)
    rw [max_def]; split_ifs with hx1
    · rw [_root_.abs_one, one_pow]
      exact pow_le_one _ (abs_nonneg _) hx1
    · push_neg at hx1
      rw [_root_.abs_abs]; exact pow_le_pow hx1.le (Nat.sub_le _ _)
  let c' r := (p_le p' r (this r)).choose
  have c'0 : ∀ r, 0 ≤ c' r := fun r => (p_le p' r (this r)).choose_spec.1
  have Pp'_le : ∀ (r : ℂ), ∀ q ≥ 1, abs (P (p' q) r) ≤ c' r ^ q := fun r =>
    (p_le p' r (this r)).choose_spec.2
  let c :=
    if h : ((p.aroots ℂ).map c').toFinset.Nonempty then ((p.aroots ℂ).map c').toFinset.max' h else 0
  have hc : ∀ x ∈ p.aroots ℂ, c' x ≤ c := by
    intro x hx; dsimp only []
    split_ifs with h
    · apply Finset.le_max'; rw [Multiset.mem_toFinset]
      refine' Multiset.mem_map_of_mem _ hx
    · rw [nonempty_iff_ne_empty, Ne.def, Multiset.toFinset_eq_empty,
        Multiset.eq_zero_iff_forall_not_mem] at h
      push_neg at h
      exact absurd (Multiset.mem_map_of_mem _ hx) (h (c' x))
  use c
  intro q q_gt prime_q
  have q0 : 0 < q := Nat.Prime.pos prime_q
  obtain ⟨gp', gp'_le, h'⟩ := sumIderiv_sl' ℤ (X ^ (q - 1) * p ^ q) q0
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
    replace h := Nat.le_of_dvd (Int.natAbs_pos_of_ne_zero p0) h
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
            q) :=
    by
    rw [mul_left_comm, ← mul_pow, mul_left_comm (_ - _),
      Multiset.prod_map_erase (f := fun a =>  X - C a) hr]
    have : Multiset.card (p.aroots ℂ) = (p.map (algebraMap ℤ ℂ)).natDegree :=
      splits_iff_card_roots.mp (IsAlgClosed.splits _)
    rw [C_leadingCoeff_mul_prod_multiset_X_sub_C this, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_pow, map_X]
  specialize h r this; clear this
  rw [le_div_iff (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _), ← abs_of_nat, ← map_mul,
    mul_comm, mul_sub, ← nsmul_eq_mul, ← nsmul_eq_mul, smul_smul, mul_comm,
    Nat.mul_factorial_pred q0, ← h]
  rw [nsmul_eq_mul, ← Int.cast_ofNat, ← zsmul_eq_mul, smul_smul, mul_add, ← nsmul_eq_mul, ←
    nsmul_eq_mul, smul_smul, mul_comm, Nat.mul_factorial_pred q0, ← h', zsmul_eq_mul, aeval_def,
    eval₂_at_zero, eq_intCast, Int.cast_id, ← Int.coe_castRingHom', ← algebraMap_int_eq, ←
    eval₂_at_zero, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map, mul_comm, ← sumIderiv_map, ← P]
  exact (Pp'_le r q (Nat.one_le_of_lt q0)).trans (pow_le_pow_of_le_left (c'0 r) (hc r hr) _)
#align exp_polynomial_approx exp_polynomial_approx

namespace AddMonoidAlgebra

@[simps]
def ringEquivCongrLeft {R S G : Type _} [Semiring R] [Semiring S] [AddMonoid G] (f : R ≃+* S) :
    AddMonoidAlgebra R G ≃+* AddMonoidAlgebra S G :=
  {
    Finsupp.mapRange.addEquiv
      f.toAddEquiv with
    toFun := (Finsupp.mapRange f f.map_zero : AddMonoidAlgebra R G → AddMonoidAlgebra S G)
    invFun :=
      (Finsupp.mapRange f.symm f.symm.map_zero : AddMonoidAlgebra S G → AddMonoidAlgebra R G)
    map_mul' := fun x y => by
      -- Porting note: was `ext`
      refine Finsupp.ext fun a => ?_
      simp_rw [mul_apply, mul_def, Finsupp.mapRange_apply]
      rw [Finsupp.sum_apply, map_finsupp_sum f]
      rw [Finsupp.sum_mapRange_index];
      -- Porting note: was `congrm`
      apply congr_arg _ <| funext₂ fun g1 r1 => ?_
      rw [Finsupp.sum_mapRange_index];
      rw [Finsupp.sum_apply, map_finsupp_sum f]
      -- Porting note: was `congrm`
      apply congr_arg _ <| funext₂ fun g2 r2 => ?_
      · rw [Finsupp.single_apply]
        split_ifs with h <;> simp only [h, if_false, if_true, map_mul, map_zero]
      all_goals
        intro; simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul];
        simp only [ite_self, Finsupp.sum_zero] }
#align add_monoid_algebra.ring_equiv_congr_left AddMonoidAlgebra.ringEquivCongrLeft

@[simps]
def algEquivCongrLeft {k R S G : Type _} [CommSemiring k] [Semiring R] [Algebra k R] [Semiring S]
    [Algebra k S] [AddMonoid G] (f : R ≃ₐ[k] S) : AddMonoidAlgebra R G ≃ₐ[k] AddMonoidAlgebra S G :=
  {
    ringEquivCongrLeft
      f.toRingEquiv with
    toFun := (Finsupp.mapRange f f.map_zero : AddMonoidAlgebra R G → AddMonoidAlgebra S G)
    invFun :=
      (Finsupp.mapRange f.symm f.symm.map_zero : AddMonoidAlgebra S G → AddMonoidAlgebra R G)
    commutes' := fun r => by
      -- Porting note: was `ext`
      refine Finsupp.ext fun a => ?_
      simp_rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Finsupp.mapRange_single]
      congr 2
      change f.toAlgHom ((algebraMap k R) r) = (algebraMap k S) r
      rw [AlgHom.map_algebraMap] }
#align add_monoid_algebra.alg_equiv_congr_left AddMonoidAlgebra.algEquivCongrLeft

@[simps]
def algAutCongrLeft {k R G : Type _} [CommSemiring k] [Semiring R] [Algebra k R] [AddMonoid G] :
    (R ≃ₐ[k] R) →* AddMonoidAlgebra R G ≃ₐ[k] AddMonoidAlgebra R G
    where
  toFun f := algEquivCongrLeft f
  map_one' := by
    ext
    refine Finsupp.ext fun a => ?_
    simp [Finsupp.mapRange_apply]
  map_mul' x y := by
    ext
    refine Finsupp.ext fun a => ?_
    simp [Finsupp.mapRange_apply]
#align add_monoid_algebra.alg_aut_congr_left AddMonoidAlgebra.algAutCongrLeft

@[simps]
def mapDomainRingEquiv (k : Type _) [Semiring k] {G H : Type _} [AddMonoid G] [AddMonoid H]
    (f : G ≃+ H) : AddMonoidAlgebra k G ≃+* AddMonoidAlgebra k H :=
  { Finsupp.domCongr f.toEquiv with
    toFun := Finsupp.equivMapDomain f
    invFun := Finsupp.equivMapDomain f.symm
    map_mul' := fun x y => by
      simp_rw [← Finsupp.domCongr_apply]
      induction x using Finsupp.induction_linear with
      | h0 =>
          simp only [map_zero, MulZeroClass.zero_mul]
      | hadd f g hf hg =>
        -- Porting note: was
        -- simp only [add_mul, map_add, *]
        rw [add_mul, map_add, hf, hg, map_add, add_mul]
      | hsingle => ?_
      induction y using Finsupp.induction_linear <;>
        simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, map_zero, mul_add, map_add, *]
      -- Porting note: was `ext`
      refine Finsupp.ext fun a => ?_
      simp only [Finsupp.domCongr_apply, single_mul_single, Finsupp.equivMapDomain_single,
        AddEquiv.coe_toEquiv, map_add] }
#align add_monoid_algebra.map_domain_ring_equiv AddMonoidAlgebra.mapDomainRingEquiv

@[simps]
def mapDomainAlgEquiv (k A : Type _) [CommSemiring k] [Semiring A] [Algebra k A] {G H : Type _}
    [AddMonoid G] [AddMonoid H] (f : G ≃+ H) : AddMonoidAlgebra A G ≃ₐ[k] AddMonoidAlgebra A H :=
  { mapDomainRingEquiv A f with
    toFun := Finsupp.equivMapDomain f
    invFun := Finsupp.equivMapDomain f.symm
    commutes' := fun r => by
      simp only [Function.comp_apply, Finsupp.equivMapDomain_single,
        AddMonoidAlgebra.coe_algebraMap, map_zero, AddEquiv.coe_toEquiv] }
#align add_monoid_algebra.map_domain_alg_equiv AddMonoidAlgebra.mapDomainAlgEquiv

@[simps]
def mapDomainAlgAut (k A : Type _) [CommSemiring k] [Semiring A] [Algebra k A] {G : Type _}
    [AddMonoid G] : AddAut G →* AddMonoidAlgebra A G ≃ₐ[k] AddMonoidAlgebra A G
    where
  toFun := mapDomainAlgEquiv k A
  map_one' := by
    ext
    refine Finsupp.ext fun a => ?_
    rfl
  map_mul' x y := by
    ext
    refine Finsupp.ext fun a => ?_
    rfl
#align add_monoid_algebra.map_domain_alg_aut AddMonoidAlgebra.mapDomainAlgAut

end AddMonoidAlgebra

namespace Aux

variable (p : ℚ[X])

abbrev k' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (p.rootSet ℂ)
#align aux.K' Aux.k'

instance k'.isSplittingField : IsSplittingField ℚ (k' p) p :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain p)
#align aux.K'.is_splitting_field Aux.k'.isSplittingField

abbrev K : Type _ :=
  p.SplittingField
#align aux.K Aux.K

instance : CharZero (K p) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (K p)).injective

instance : IsGalois ℚ (K p) where

abbrev lift : k' p ≃ₐ[ℚ] K p :=
  IsSplittingField.algEquiv (k' p) p
#align aux.Lift Aux.lift

instance algebraKℂ : Algebra (K p) ℂ :=
  ((k' p).val.comp (lift p).symm.toAlgHom).toRingHom.toAlgebra
#align aux.algebra_K_ℂ Aux.algebraKℂ

instance avoidDiamondCache : Algebra (⊥ : IntermediateField ℚ (K p)) (K p) :=
  IntermediateField.toAlgebra _
#align aux.avoid_diamond_cache Aux.avoidDiamondCache

/-- example : algebra_int (K p) = (infer_instance : algebra ℤ (K p)) := rfl
-/
instance avoidDiamondIntCache : Algebra ℤ (K p) :=
  algebraInt (K p)
#align aux.avoid_diamond_int_cache Aux.avoidDiamondIntCache

instance : Algebra ℚ (K p) :=
  inferInstance

instance : SMul ℚ (K p) :=
  Algebra.toSMul

instance cache_ℚ_k_ℂ : IsScalarTower ℚ (K p) ℂ :=
  inferInstance
#align aux.cache_ℚ_K_ℂ Aux.cache_ℚ_k_ℂ

instance cache_ℤ_k_ℂ : IsScalarTower ℤ (K p) ℂ :=
  inferInstance
#align aux.cache_ℤ_K_ℂ Aux.cache_ℤ_k_ℂ

end Aux

namespace Quot

@[reducible, elab_as_elim]
protected def liftFinsupp {α : Type _} {r : α → α → Prop} {β : Type _} [Zero β] (f : α →₀ β)
    (h : ∀ a b, r a b → f a = f b) : Quot r →₀ β :=
  by
  refine' ⟨image (mk r) f.support, Quot.lift f h, fun a => ⟨_, a.ind fun b => _⟩⟩
  · rw [mem_image]; rintro ⟨b, hb, rfl⟩; exact finsupp.mem_support_iff.mp hb
  · rw [lift_mk _ h]; refine' fun hb => mem_image_of_mem _ (finsupp.mem_support_iff.mpr hb)
#align quot.lift_finsupp Quot.liftFinsupp

theorem liftFinsupp_mk {α : Type _} {r : α → α → Prop} {γ : Type _} [Zero γ] (f : α →₀ γ)
    (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) : Quot.liftFinsupp f h (Quot.mk r a) = f a :=
  rfl
#align quot.lift_finsupp_mk Quot.liftFinsupp_mk

end Quot

namespace Quotient

@[reducible, elab_as_elim]
protected def liftFinsupp {α : Type _} {β : Type _} [s : Setoid α] [Zero β] (f : α →₀ β) :
    (∀ a b, a ≈ b → f a = f b) → Quotient s →₀ β :=
  Quot.liftFinsupp f
#align quotient.lift_finsupp Quotient.liftFinsupp

@[simp]
theorem liftFinsupp_mk' {α : Type _} {β : Type _} [s : Setoid α] [Zero β] (f : α →₀ β)
    (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) : Quotient.liftFinsupp f h (Quotient.mk' x) = f x :=
  rfl
#align quotient.lift_finsupp_mk Quotient.liftFinsupp_mk'

end Quotient

section

variable (s : Finset ℂ)

abbrev poly : ℚ[X] :=
  ∏ x in s, minpoly ℚ x
#align Poly poly

abbrev k' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((poly s).rootSet ℂ)
#align K' k'

abbrev K : Type _ :=
  (poly s).SplittingField
#align K K

abbrev Gal : Type _ :=
  (poly s).Gal
#align Gal Gal

/- warning: Lift clashes with lift -> lift
Case conversion may be inaccurate. Consider using '#align Lift liftₓ'. -/
#print lift /-
abbrev lift : k' s ≃ₐ[ℚ] K s :=
  IsSplittingField.algEquiv (k' s) (poly s)
#align Lift lift
-/

theorem algebraMap_k_apply (x) : algebraMap (K s) ℂ x = ((lift s).symm x : ℂ) :=
  rfl
#align algebra_map_K_apply algebraMap_k_apply

theorem poly_ne_zero (hs : ∀ x ∈ s, IsIntegral ℚ x) : poly s ≠ 0 :=
  prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hs x hx)
#align Poly_ne_zero poly_ne_zero

noncomputable def ratCoeff : Subalgebra ℚ (AddMonoidAlgebra (K s) (K s))
    where
  carrier x := ∀ i : K s, x i ∈ (⊥ : IntermediateField ℚ (K s))
  mul_mem' a b ha hb i := by
    rw [AddMonoidAlgebra.mul_apply]
    refine' sum_mem fun c hc => sum_mem fun d hd => _
    dsimp only; split_ifs; exacts [mul_mem (ha c) (hb d), zero_mem _]
  add_mem' a b ha hb i := by rw [Finsupp.add_apply]; exact add_mem (ha i) (hb i)
  algebraMap_mem' r hr :=
    by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Finsupp.single_apply]
    split_ifs; exacts [IntermediateField.algebraMap_mem _ _, zero_mem _]
#align rat_coeff ratCoeff

--cache
instance : ZeroMemClass (IntermediateField ℚ (K s)) (K s) :=
  inferInstance

def RatCoeffEquiv.aux : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra (⊥ : IntermediateField ℚ (K s)) (K s)
    where
  toFun x :=
    { support := (x : AddMonoidAlgebra (K s) (K s)).support
      toFun := fun i => ⟨x i, x.2 i⟩
      mem_support_toFun := fun i => by
        rw [Finsupp.mem_support_iff]
        have : (0 : (⊥ : IntermediateField ℚ (K s))) = ⟨0, ZeroMemClass.zero_mem _⟩ := rfl
        simp_rw [this, Ne.def, Subtype.mk.inj_eq]; rfl }
  invFun x :=
    ⟨⟨x.support, fun i => x i, fun i => by
        simp_rw [Finsupp.mem_support_iff, Ne.def, ZeroMemClass.coe_eq_zero]⟩,
      fun i => SetLike.coe_mem _⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by
    ext; change (x * y : AddMonoidAlgebra (K s) (K s)) a = _
    simp_rw [AddMonoidAlgebra.mul_apply, Finsupp.sum, AddSubmonoidClass.coe_finset_sum]
    refine' sum_congr rfl fun i hi => sum_congr rfl fun j hj => _
    split_ifs <;> rfl
  map_add' x y := by
    ext; change (x + y : AddMonoidAlgebra (K s) (K s)) a = x a + y a
    rw [Finsupp.add_apply]; rfl
  commutes' x := by
    ext
    change
      (algebraMap ℚ (ratCoeff s) x) a =
        (Finsupp.single 0 (algebraMap ℚ (⊥ : IntermediateField ℚ (K s)) x)) a
    simp_rw [Algebra.algebraMap_eq_smul_one]
    change (x • Finsupp.single 0 (1 : K s)) a = _
    simp_rw [Finsupp.smul_single, Finsupp.single_apply]
    split_ifs <;> rfl
#align rat_coeff_equiv.aux RatCoeffEquiv.aux

def ratCoeffEquiv : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra ℚ (K s) :=
  (RatCoeffEquiv.aux s).trans
    (AddMonoidAlgebra.algEquivCongrLeft (IntermediateField.botEquiv ℚ (K s)))
#align rat_coeff_equiv ratCoeffEquiv

theorem ratCoeffEquiv_apply_apply (x : ratCoeff s) (i : K s) :
    ratCoeffEquiv s x i = (IntermediateField.botEquiv ℚ (K s)) ⟨x i, x.2 i⟩ :=
  rfl
#align rat_coeff_equiv_apply_apply ratCoeffEquiv_apply_apply

theorem support_ratCoeffEquiv (x : ratCoeff s) :
    (ratCoeffEquiv s x).support = (x : AddMonoidAlgebra (K s) (K s)).support :=
  by
  dsimp [ratCoeffEquiv, RatCoeffEquiv.aux]
  rw [Finsupp.support_mapRange_of_injective]
  exact AlgEquiv.injective _
#align support_rat_coeff_equiv support_ratCoeffEquiv

section

variable (F : Type _) [Field F] [Algebra ℚ F]

noncomputable def mapDomainFixed : Subalgebra F (AddMonoidAlgebra F (K s))
    where
  carrier x := ∀ f : Gal s, AddMonoidAlgebra.mapDomainAlgAut ℚ _ f.toAddEquiv x = x
  mul_mem' {a b} ha hb f := by rw [map_mul, ha, hb]
  add_mem' {a b} ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f :=
    by
    change Finsupp.equivMapDomain f.toEquiv (Finsupp.single _ _) = Finsupp.single _ _
    rw [Finsupp.equivMapDomain_single]
    change Finsupp.single (f 0) _ = _; rw [AlgEquiv.map_zero]
#align map_domain_fixed mapDomainFixed

theorem mem_mapDomainFixed_iff (x : AddMonoidAlgebra F (K s)) :
    x ∈ mapDomainFixed s F ↔ ∀ i j, i ∈ MulAction.orbit (Gal s) j → x i = x j :=
  by
  simp_rw [MulAction.mem_orbit_iff]
  change (∀ f : Gal s, Finsupp.equivMapDomain (↑(AlgEquiv.toAddEquiv f)) x = x) ↔ _
  refine' ⟨fun h i j hij => _, fun h f => _⟩
  · obtain ⟨f, rfl⟩ := hij
    rw [AlgEquiv.smul_def, ← Finsupp.congr_fun (h f) (f j)]
    change x (f.symm (f j)) = _; rw [AlgEquiv.symm_apply_apply]
  · ext i; change x (f.symm i) = x i
    refine' (h i ((AlgEquiv.symm f) i) ⟨f, _⟩).symm
    rw [AlgEquiv.smul_def, AlgEquiv.apply_symm_apply]
#align mem_map_domain_fixed_iff mem_mapDomainFixed_iff

noncomputable def mapDomainFixedEquivSubtype :
    mapDomainFixed s F ≃
      { f : AddMonoidAlgebra F (K s) // MulAction.orbitRel (Gal s) (K s) ≤ Setoid.ker f }
    where
  toFun f := ⟨f, (mem_mapDomainFixed_iff s F f).mp f.2⟩
  invFun f := ⟨f, (mem_mapDomainFixed_iff s F f).mpr f.2⟩
  left_inv f := by simp_rw [← Subtype.coe_inj, Subtype.coe_mk]
  right_inv f := by simp_rw [← Subtype.coe_inj, Subtype.coe_mk]
#align map_domain_fixed_equiv_subtype mapDomainFixedEquivSubtype

end
