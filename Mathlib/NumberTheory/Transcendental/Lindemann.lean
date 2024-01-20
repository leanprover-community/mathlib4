/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
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
import Mathlib.RingTheory.MvPolynomial.Symmetric.Eval
import Mathlib.Data.Complex.Exponential
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Order.Extension.Linear
import Mathlib.Data.Finsupp.Lex
import Mathlib.Algebra.Group.UniqueProds

/-!
# The Lindemann-Weierstrass theorem
-/

noncomputable section

open scoped BigOperators Classical Polynomial Nat

open Finset Polynomial

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A] [Algebra R A]


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
      fun x : ℝ => exp (-(x • exp (s.arg • I))) * p.eval (x • exp (s.arg • I)) := by
  have h :
    (fun y : ℝ => p.sumIderiv.eval (y • exp (s.arg • I))) =
      (fun x => p.sumIderiv.eval x) ∘ fun y => y • exp (s.arg • I) :=
    rfl
  funext x
  rw [deriv_div_const, deriv.neg, deriv_mul, deriv_cexp, deriv.neg]
  any_goals simp_rw [h]; clear h
  rw [deriv_smul_const, deriv_id'', deriv.comp, Polynomial.deriv, deriv_smul_const, deriv_id'']
  simp_rw [one_smul, mul_assoc, ← mul_add]
  have h :
    exp (s.arg • I) * p.sumIderiv.eval (x • exp (s.arg • I)) -
        (derivative (R := ℂ) (sumIderiv p)).eval (x • exp (s.arg • I)) * exp (s.arg • I) =
      p.eval (x • exp (s.arg • I)) * exp (s.arg • I)
  · conv_lhs =>
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
      -(exp (-s) * p.sumIderiv.eval s) / exp (s.arg • I) -
        -p.sumIderiv.eval 0 / exp (s.arg • I) := by
  convert
    intervalIntegral.integral_deriv_eq_sub'
      (fun x : ℝ =>
        -(exp (-(x • exp (s.arg • I))) * p.sumIderiv.eval (x • exp (s.arg • I))) / exp (s.arg • I))
      (deriv_eq_f p s) _ _
  any_goals simp_rw [real_smul, abs_mul_exp_arg_mul_I]
  · simp_rw [zero_smul, neg_zero, Complex.exp_zero, one_mul]
  · intro x _; apply ((Differentiable.mul _ _).neg.div_const _).differentiableAt
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
set_option linter.uppercaseLean3 false in
#align P P

theorem P_le' (p : ℕ → ℂ[X]) (s : ℂ)
    (h :
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 (Complex.abs s),
        Complex.abs ((p q).eval (x • exp (s.arg • I))) ≤ c ^ q) :
    ∃ c ≥ 0, ∀ q : ℕ,
      Complex.abs (P (p q) s) ≤
        Real.exp s.re * (Real.exp (Complex.abs s) * c ^ q * (Complex.abs s)) := by
  simp_rw [P]; cases' h with c hc; replace hc := fun q x hx => (hc q x hx).trans (le_abs_self _)
  simp_rw [_root_.abs_pow] at hc; use |c|, abs_nonneg _; intro q
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
set_option linter.uppercaseLean3 false in
#align P_le' P_le'

theorem P_le (p : ℕ → ℂ[X]) (s : ℂ)
    (h :
      ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 (Complex.abs s),
        Complex.abs ((p q).eval (x • exp (s.arg • I))) ≤ c ^ q) :
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
  have : ∀ s : ℂ, ∃ c, ∀ (q : ℕ), ∀ x ∈ Set.Ioc 0 (Complex.abs s),
      Complex.abs ((p' q).eval (x • exp (s.arg • I))) ≤ c ^ q
  · intro s; dsimp only
    simp_rw [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X, map_mul,
      Complex.abs_pow, real_smul, map_mul, abs_exp_ofReal_mul_I, abs_ofReal, mul_one, ←
      eval₂_eq_eval_map, ← aeval_def]
    have : Bornology.IsBounded
        ((fun x : ℝ => max |x| 1 * Complex.abs (aeval (x * exp (s.arg * I)) p)) ''
          Set.Ioc 0 (abs s))
    · have h :
        (fun x : ℝ => max |x| 1 * Complex.abs (aeval (↑x * exp (↑s.arg * I)) p)) ''
            Set.Ioc 0 (abs s) ⊆
          (fun x : ℝ => max |x| 1 * Complex.abs (aeval (↑x * exp (↑s.arg * I)) p)) ''
              Set.Icc 0 (abs s) :=
        Set.image_subset _ Set.Ioc_subset_Icc_self
      refine' (IsCompact.image isCompact_Icc _).isBounded.subset h
      · refine' (continuous_id.abs.max continuous_const).mul _
        refine' Complex.continuous_abs.comp (p.continuous_aeval.comp _)
        exact continuous_ofReal.mul continuous_const
    cases' this.exists_norm_le with c h
    use c; intro q x hx
    specialize h (max |x| 1 * Complex.abs (aeval (↑x * exp (↑s.arg * I)) p))
      (Set.mem_image_of_mem _ hx)
    refine' le_trans _ (pow_le_pow_left (norm_nonneg _) h _)
    simp_rw [norm_mul, Real.norm_eq_abs, Complex.abs_abs, mul_pow]
    refine' mul_le_mul_of_nonneg_right _ (pow_nonneg (Complex.abs.nonneg _) _)
    rw [max_def]; split_ifs with hx1
    · rw [_root_.abs_one, one_pow]
      exact pow_le_one _ (abs_nonneg _) hx1
    · push_neg at hx1
      rw [_root_.abs_abs]; exact pow_le_pow_right hx1.le (Nat.sub_le _ _)
  choose c' c'0 Pp'_le using fun r ↦ P_le p' r (this r)
  let c :=
    if h : ((p.aroots ℂ).map c').toFinset.Nonempty then ((p.aroots ℂ).map c').toFinset.max' h else 0
  have hc : ∀ x ∈ p.aroots ℂ, c' x ≤ c
  · intro x hx; dsimp only
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

namespace AuxInstances

variable (p : ℚ[X])

abbrev K' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (p.rootSet ℂ)
set_option linter.uppercaseLean3 false in
#align aux.K' AuxInstances.K'

instance K'.isSplittingField : IsSplittingField ℚ (K' p) p :=
  IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits_codomain p)
set_option linter.uppercaseLean3 false in
#align aux.K'.is_splitting_field AuxInstances.K'.isSplittingField

abbrev K : Type _ :=
  p.SplittingField
set_option linter.uppercaseLean3 false in
#align aux.K AuxInstances.K

instance : CharZero (K p) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (K p)).injective

instance : IsGalois ℚ (K p) where

abbrev Lift : K' p ≃ₐ[ℚ] K p :=
  IsSplittingField.algEquiv (K' p) p
set_option linter.uppercaseLean3 false in
#align aux.Lift AuxInstances.Lift

instance algebraKℂ : Algebra (K p) ℂ :=
  ((K' p).val.comp (Lift p).symm.toAlgHom).toRingHom.toAlgebra
set_option linter.uppercaseLean3 false in
#align aux.algebra_K_ℂ AuxInstances.algebraKℂ

instance : Algebra ℚ (K p) :=
  inferInstance

instance : SMul ℚ (K p) :=
  Algebra.toSMul

instance cache_ℚ_K_ℂ : IsScalarTower ℚ (K p) ℂ :=
  inferInstance
set_option linter.uppercaseLean3 false in
#align aux.cache_ℚ_K_ℂ AuxInstances.cache_ℚ_K_ℂ

instance cache_ℤ_K_ℂ : IsScalarTower ℤ (K p) ℂ :=
  inferInstance
set_option linter.uppercaseLean3 false in
#align aux.cache_ℤ_K_ℂ AuxInstances.cache_ℤ_K_ℂ

end AuxInstances

namespace Quot

@[reducible] --, elab_as_elim]
protected def liftFinsupp {α : Type*} {r : α → α → Prop} {β : Type*} [Zero β] (f : α →₀ β)
    (h : ∀ a b, r a b → f a = f b) : Quot r →₀ β := by
  refine' ⟨image (mk r) f.support, Quot.lift f h, fun a => ⟨_, _⟩⟩
  · rw [mem_image]; rintro ⟨b, hb, rfl⟩; exact Finsupp.mem_support_iff.mp hb
  · induction a using Quot.ind
    rw [lift_mk _ h]; refine' fun hb => mem_image_of_mem _ (Finsupp.mem_support_iff.mpr hb)
#align quot.lift_finsupp Quot.liftFinsupp

theorem liftFinsupp_mk {α : Type*} {r : α → α → Prop} {γ : Type*} [Zero γ] (f : α →₀ γ)
    (h : ∀ a₁ a₂, r a₁ a₂ → f a₁ = f a₂) (a : α) : Quot.liftFinsupp f h (Quot.mk r a) = f a :=
  rfl
#align quot.lift_finsupp_mk Quot.liftFinsupp_mk

end Quot

namespace Quotient

@[reducible] --, elab_as_elim]
protected def liftFinsupp {α : Type*} {β : Type*} [s : Setoid α] [Zero β] (f : α →₀ β) :
    (∀ a b, a ≈ b → f a = f b) → Quotient s →₀ β :=
  Quot.liftFinsupp f
#align quotient.lift_finsupp Quotient.liftFinsupp

@[simp]
theorem liftFinsupp_mk' {α : Type*} {β : Type*} [Setoid α] [Zero β] (f : α →₀ β)
    (h : ∀ a b : α, a ≈ b → f a = f b) (x : α) : Quotient.liftFinsupp f h (Quotient.mk' x) = f x :=
  rfl
#align quotient.lift_finsupp_mk Quotient.liftFinsupp_mk'

end Quotient

section

variable (s : Finset ℂ)

namespace Transcendental -- Conflict with Mathlib.NumberTheory.Dioph
abbrev Poly : ℚ[X] :=
  ∏ x in s, minpoly ℚ x
set_option linter.uppercaseLean3 false in
#align Poly Transcendental.Poly
end Transcendental

open Transcendental

abbrev K' : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ((Poly s).rootSet ℂ)
set_option linter.uppercaseLean3 false in
#align K' K'

abbrev K : Type _ :=
  (Poly s).SplittingField
set_option linter.uppercaseLean3 false in
#align K K

abbrev Gal : Type _ :=
  (Poly s).Gal
set_option linter.uppercaseLean3 false in
#align Gal Gal

abbrev Lift : K' s ≃ₐ[ℚ] K s :=
  IsSplittingField.algEquiv (K' s) (Poly s)
set_option linter.uppercaseLean3 false in
#align Lift Lift


theorem algebraMap_K_apply (x) : algebraMap (K s) ℂ x = ((Lift s).symm x : ℂ) :=
  rfl
set_option linter.uppercaseLean3 false in
#align algebra_map_K_apply algebraMap_K_apply

theorem poly_ne_zero (hs : ∀ x ∈ s, IsIntegral ℚ x) : Poly s ≠ 0 :=
  prod_ne_zero_iff.mpr fun x hx => minpoly.ne_zero (hs x hx)
set_option linter.uppercaseLean3 false in
#align Poly_ne_zero poly_ne_zero

noncomputable def ratCoeff : Subalgebra ℚ (AddMonoidAlgebra (K s) (K s))
    where
  carrier := {x | ∀ i : K s, x i ∈ (⊥ : IntermediateField ℚ (K s))}
  mul_mem' {a b} ha hb i := by
    rw [AddMonoidAlgebra.mul_apply]
    refine' sum_mem fun c _ => sum_mem fun d _ => _
    dsimp only; split_ifs; exacts [mul_mem (ha c) (hb d), zero_mem _]
  add_mem' {a b} ha hb i := by rw [Finsupp.add_apply]; exact add_mem (ha i) (hb i)
  algebraMap_mem' r hr := by
    rw [AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, Finsupp.single_apply]
    split_ifs; exacts [IntermediateField.algebraMap_mem _ _, zero_mem _]
#align rat_coeff ratCoeff

--cache
instance : ZeroMemClass (IntermediateField ℚ (K s)) (K s) :=
  inferInstance
instance : AddCommMonoid (⊥ : IntermediateField ℚ (K s)) :=
  letI : AddCommGroup (⊥ : IntermediateField ℚ (K s)) := NonUnitalNonAssocRing.toAddCommGroup
  AddCommGroup.toAddCommMonoid
instance : Algebra ℚ (⊥ : IntermediateField ℚ (K s)) :=
  IntermediateField.algebra _

@[simps!]
def RatCoeffEquiv.aux : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra (⊥ : IntermediateField ℚ (K s)) (K s)
    where
  toFun x :=
    { support := (x : AddMonoidAlgebra (K s) (K s)).support
      toFun := fun i => ⟨(x : AddMonoidAlgebra (K s) (K s)) i, x.2 i⟩
      mem_support_toFun := fun i => by
        rw [Finsupp.mem_support_iff]
        have : (0 : (⊥ : IntermediateField ℚ (K s))) = ⟨0, ZeroMemClass.zero_mem _⟩ := rfl
        simp_rw [this, Ne.def, Subtype.mk_eq_mk] }
  invFun x :=
    ⟨⟨x.support, fun i => x i, fun i => by
        simp_rw [Finsupp.mem_support_iff, Ne.def, ZeroMemClass.coe_eq_zero]⟩,
      fun i => SetLike.coe_mem _⟩
  left_inv x := by ext; rfl
  right_inv x := by
    refine Finsupp.ext fun a => ?_
    rfl
  map_mul' x y := by
    refine Finsupp.ext fun a => ?_
    ext
    change (x * y : AddMonoidAlgebra (K s) (K s)) a = _
    simp_rw [AddMonoidAlgebra.mul_apply, Finsupp.sum, AddSubmonoidClass.coe_finset_sum]
    refine' sum_congr rfl fun i _ => sum_congr rfl fun j _ => _
    split_ifs <;> rfl
  map_add' x y := by
    refine Finsupp.ext fun a => ?_
    ext
    change (x + y : AddMonoidAlgebra (K s) (K s)) a =
      (x : AddMonoidAlgebra (K s) (K s)) a + (y : AddMonoidAlgebra (K s) (K s)) a
    rw [Finsupp.add_apply]
  commutes' x := by
    refine Finsupp.ext fun a => ?_
    ext
    change
      ((algebraMap ℚ (ratCoeff s) x) : AddMonoidAlgebra (K s) (K s)) a =
        (Finsupp.single 0 (algebraMap ℚ (⊥ : IntermediateField ℚ (K s)) x)) a
    simp_rw [Algebra.algebraMap_eq_smul_one]
    change (x • Finsupp.single 0 (1 : K s)) a = _
    simp_rw [Finsupp.smul_single, Finsupp.single_apply]
    split_ifs <;> rfl
#align rat_coeff_equiv.aux RatCoeffEquiv.aux

@[simps! apply]
def ratCoeffEquiv : ratCoeff s ≃ₐ[ℚ] AddMonoidAlgebra ℚ (K s) :=
  (RatCoeffEquiv.aux s).trans
    (AddMonoidAlgebra.mapRangeAlgEquiv (IntermediateField.botEquiv ℚ (K s)))
#align rat_coeff_equiv ratCoeffEquiv

theorem ratCoeffEquiv_apply_apply (x : ratCoeff s) (i : K s) :
    ratCoeffEquiv s x i =
      (IntermediateField.botEquiv ℚ (K s)) ⟨(x : AddMonoidAlgebra (K s) (K s)) i, x.2 i⟩ := by
  rw [ratCoeffEquiv_apply]; rfl

#align rat_coeff_equiv_apply_apply ratCoeffEquiv_apply_apply

theorem support_ratCoeffEquiv (x : ratCoeff s) :
    (ratCoeffEquiv s x).support = (x : AddMonoidAlgebra (K s) (K s)).support := by
  simp [Finsupp.support_mapRange_of_injective _ _ (AlgEquiv.injective _)]
#align support_rat_coeff_equiv support_ratCoeffEquiv

section

variable (F : Type*) [Field F] [Algebra ℚ F]

noncomputable def mapDomainFixed : Subalgebra F (AddMonoidAlgebra F (K s)) where
  carrier := {x | ∀ f : Gal s, AddMonoidAlgebra.domCongrAut ℚ _ f.toAddEquiv x = x}
  mul_mem' {a b} ha hb f := by rw [map_mul, ha, hb]
  add_mem' {a b} ha hb f := by rw [map_add, ha, hb]
  algebraMap_mem' r f := by
    change Finsupp.equivMapDomain f.toEquiv (Finsupp.single _ _) = Finsupp.single _ _
    rw [Finsupp.equivMapDomain_single]
    change Finsupp.single (f 0) _ = _; rw [AlgEquiv.map_zero]
#align map_domain_fixed mapDomainFixed

instance : CoeFun (mapDomainFixed s F) fun _ => (K s) → F where
  coe f := f.1

theorem mem_mapDomainFixed_iff (x : AddMonoidAlgebra F (K s)) :
    x ∈ mapDomainFixed s F ↔ ∀ i j, i ∈ MulAction.orbit (Gal s) j → x i = x j := by
  simp_rw [MulAction.mem_orbit_iff]
  change (∀ f : Gal s, Finsupp.equivMapDomain (↑(AlgEquiv.toAddEquiv f)) x = x) ↔ _
  refine' ⟨fun h i j hij => _, fun h f => _⟩
  · obtain ⟨f, rfl⟩ := hij
    rw [AlgEquiv.smul_def, ← DFunLike.congr_fun (h f) (f j)]
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
  left_inv _ := rfl
  right_inv _ := rfl
#align map_domain_fixed_equiv_subtype mapDomainFixedEquivSubtype

end

section toConjEquiv

variable (F : Type*) [Field F] [Algebra ℚ F]

open GalConjClasses

def toConjEquiv : mapDomainFixed s F ≃ (GalConjClasses ℚ (K s) →₀ F) := by
  refine' (mapDomainFixedEquivSubtype s F).trans _
  let f'
      (f : { f : AddMonoidAlgebra F (K s) // MulAction.orbitRel (Gal s) (K s) ≤ Setoid.ker ↑f }) :=
    @Quotient.liftFinsupp _ _ (IsGalConj.setoid _ _) _ (f : AddMonoidAlgebra F (K s)) f.2
  refine'
    { toFun := f'
      invFun := fun f => ⟨_, _⟩
      left_inv := _
      right_inv := _ }
  · refine' ⟨f.support.biUnion fun i => i.orbit.toFinset, fun x => f (GalConjClasses.mk ℚ x),
      fun i => _⟩
    simp_rw [mem_biUnion, Set.mem_toFinset, mem_orbit, Finsupp.mem_support_iff, exists_eq_right']
  · change ∀ i j, i ∈ MulAction.orbit (Gal s) j → f (Quotient.mk'' i) = f (Quotient.mk'' j)
    exact fun i j h => congr_arg f (Quotient.sound' h)
  · exact fun _ => Subtype.eq <| Finsupp.ext fun x => rfl
  · refine' fun f => Finsupp.ext fun x => Quotient.inductionOn' x fun i => rfl
#align to_conj_equiv toConjEquiv

@[simp 1001] -- LHS simplifies
theorem toConjEquiv_apply_apply_mk (f : mapDomainFixed s F) (i : K s) :
    toConjEquiv s F f (mk ℚ i) = f i :=
  rfl
#align to_conj_equiv_apply_apply_mk toConjEquiv_apply_apply_mk

@[simp]
theorem toConjEquiv_symm_apply_apply (f : GalConjClasses ℚ (K s) →₀ F) (i : K s) :
    (toConjEquiv s F).symm f i = f (mk ℚ i) :=
  rfl
#align to_conj_equiv_symm_apply_apply toConjEquiv_symm_apply_apply

@[simp]
theorem toConjEquiv_apply_apply (f : mapDomainFixed s F) (i : GalConjClasses ℚ (K s)) :
    toConjEquiv s F f i = f i.out := by rw [← i.out_eq, toConjEquiv_apply_apply_mk, i.out_eq]
#align to_conj_equiv_apply_apply toConjEquiv_apply_apply

@[simp 1001] -- LHS simplifies
theorem toConjEquiv_apply_zero_eq (f : mapDomainFixed s F) : toConjEquiv s F f 0 = f 0 := by
  rw [toConjEquiv_apply_apply, GalConjClasses.zero_out]
#align to_conj_equiv_apply_zero_eq toConjEquiv_apply_zero_eq

@[simp 1001] -- LHS simplifies
theorem toConjEquiv_symm_apply_zero_eq (f : GalConjClasses ℚ (K s) →₀ F) :
    (toConjEquiv s F).symm f 0 = f 0 := by rw [toConjEquiv_symm_apply_apply]; rfl
#align to_conj_equiv_symm_apply_zero_eq toConjEquiv_symm_apply_zero_eq

instance : AddCommMonoid (mapDomainFixed s F) :=
  letI : AddCommGroup (mapDomainFixed s F) := NonUnitalNonAssocRing.toAddCommGroup
  AddCommGroup.toAddCommMonoid

@[simps]
def toConjLinearEquiv : mapDomainFixed s F ≃ₗ[F] GalConjClasses ℚ (K s) →₀ F :=
  { toConjEquiv s F with
    toFun := toConjEquiv s F
    invFun := (toConjEquiv s F).symm
    map_add' := fun x y => by
      ext i; simp_rw [Finsupp.coe_add, Pi.add_apply, toConjEquiv_apply_apply]
      rfl
    map_smul' := fun r x => by
      ext i; simp_rw [Finsupp.coe_smul, toConjEquiv_apply_apply]
      simp only [SetLike.val_smul, RingHom.id_apply]
      rw [Finsupp.coe_smul, Pi.smul_apply]
      rw [Pi.smul_apply]
      rw [toConjEquiv_apply_apply] }
#align to_conj_linear_equiv toConjLinearEquiv

namespace Finsupp.GalConjClasses

instance : One (GalConjClasses ℚ (K s) →₀ F) where
  one := toConjLinearEquiv s F 1

theorem one_def : (1 : GalConjClasses ℚ (K s) →₀ F) = toConjLinearEquiv s F 1 :=
  rfl
#align finsupp.gal_conj_classes.one_def Finsupp.GalConjClasses.one_def

instance : Mul (GalConjClasses ℚ (K s) →₀ F) where
  mul x y :=
    toConjLinearEquiv s F <| (toConjLinearEquiv s F).symm x * (toConjLinearEquiv s F).symm y

theorem mul_def (x y : GalConjClasses ℚ (K s) →₀ F) :
    x * y =
      toConjLinearEquiv s F ((toConjLinearEquiv s F).symm x * (toConjLinearEquiv s F).symm y) :=
  rfl
#align finsupp.gal_conj_classes.mul_def Finsupp.GalConjClasses.mul_def

instance : CommSemigroup (GalConjClasses ℚ (K s) →₀ F) where
  mul_assoc a b c := by
    simp_rw [mul_def, LinearEquiv.symm_apply_apply, mul_assoc]
  mul_comm a b := by
    simp_rw [mul_def]
    exact congr_arg _ (mul_comm _ _)

instance : MulZeroClass (GalConjClasses ℚ (K s) →₀ F) where
  zero_mul a :=
    graph_eq_empty.mp rfl
  mul_zero a := by
    rw [mul_comm]
    exact graph_eq_empty.mp rfl

instance : CommRing (GalConjClasses ℚ (K s) →₀ F) :=
  { (inferInstance : AddCommGroup (GalConjClasses ℚ (K s) →₀ F)),
    (inferInstance : CommSemigroup (GalConjClasses ℚ (K s) →₀ F)),
    (inferInstance : MulZeroClass (GalConjClasses ℚ (K s) →₀ F)) with
    one_mul := fun a => by
      simp_rw [one_def, mul_def, LinearEquiv.symm_apply_apply, one_mul,
        LinearEquiv.apply_symm_apply]
    mul_one := fun a => by
      simp_rw [one_def, mul_def, LinearEquiv.symm_apply_apply, mul_one,
        LinearEquiv.apply_symm_apply]
    left_distrib := fun a b c => by
      simp only [mul_def, ← map_add, ← mul_add]
    right_distrib := fun a b c => by
      simp only [mul_def, ← map_add, ← add_mul] }

instance : Algebra F (GalConjClasses ℚ (K s) →₀ F) :=
  Algebra.ofModule'
    (fun r x => by
      rw [one_def, mul_def, SMulHomClass.map_smul, LinearEquiv.symm_apply_apply, smul_one_mul, ←
        SMulHomClass.map_smul, LinearEquiv.apply_symm_apply])
    fun r x => by
    rw [one_def, mul_def, SMulHomClass.map_smul, LinearEquiv.symm_apply_apply, mul_smul_one, ←
      SMulHomClass.map_smul, LinearEquiv.apply_symm_apply]

theorem one_eq_single : (1 : GalConjClasses ℚ (K s) →₀ F) = Finsupp.single 0 1 := by
  change toConjEquiv s F 1 = _
  ext i; rw [toConjEquiv_apply_apply]
  change (1 : AddMonoidAlgebra F (K s)) i.out = Finsupp.single 0 1 i
  simp_rw [AddMonoidAlgebra.one_def, Finsupp.single_apply]
  change (ite (0 = i.out) 1 0 : F) = ite (0 = i) 1 0
  simp_rw [@eq_comm _ _ i.out, @eq_comm _ _ i, GalConjClasses.out_eq_zero_iff]
#align finsupp.gal_conj_classes.one_eq_single Finsupp.GalConjClasses.one_eq_single

theorem algebraMap_eq_single (x : F) :
    algebraMap F (GalConjClasses ℚ (K s) →₀ F) x = Finsupp.single 0 x := by
  change x • (1 : GalConjClasses ℚ (K s) →₀ F) = Finsupp.single 0 x
  rw [one_eq_single, Finsupp.smul_single, smul_eq_mul, mul_one]
#align finsupp.gal_conj_classes.algebra_map_eq_single Finsupp.GalConjClasses.algebraMap_eq_single

end Finsupp.GalConjClasses

@[simps]
def toConjAlgEquiv : mapDomainFixed s F ≃ₐ[F] GalConjClasses ℚ (K s) →₀ F :=
  { toConjLinearEquiv s F with
    toFun := toConjLinearEquiv s F
    invFun := (toConjLinearEquiv s F).symm
    map_mul' := fun x y => by simp_rw [Finsupp.GalConjClasses.mul_def, LinearEquiv.symm_apply_apply]
    commutes' := fun r => by
      simp_rw [Finsupp.GalConjClasses.algebraMap_eq_single]
      change toConjEquiv s F (algebraMap F (mapDomainFixed s F) r) = _
      ext i; rw [toConjEquiv_apply_apply]
      change Finsupp.single 0 r i.out = Finsupp.single 0 r i
      simp_rw [Finsupp.single_apply]
      change ite (0 = i.out) r 0 = ite (0 = i) r 0
      simp_rw [@eq_comm _ _ i.out, @eq_comm _ _ i, out_eq_zero_iff] }
#align to_conj_alg_equiv toConjAlgEquiv

theorem ToConjEquivSymmSingle.aux (x : GalConjClasses ℚ (K s)) (a : F) :
    (Finsupp.indicator x.orbit.toFinset fun _ _ => a) ∈ mapDomainFixed s F := by
  rw [mem_mapDomainFixed_iff]
  rintro i j h
  simp_rw [Finsupp.indicator_apply, Set.mem_toFinset]; dsimp; congr 1
  simp_rw [mem_orbit, eq_iff_iff]
  apply Eq.congr_left
  rwa [GalConjClasses.eq]
#align to_conj_equiv_symm_single.aux ToConjEquivSymmSingle.aux

theorem toConjEquiv_symm_single (x : GalConjClasses ℚ (K s)) (a : F) :
    (toConjEquiv s F).symm (Finsupp.single x a) =
      ⟨Finsupp.indicator x.orbit.toFinset fun _ _ => a, ToConjEquivSymmSingle.aux s F x a⟩ := by
  rw [Equiv.symm_apply_eq]
  ext i; rw [toConjEquiv_apply_apply]
  change Finsupp.single x a i = Finsupp.indicator x.orbit.toFinset (fun _ _ => a) i.out
  rw [Finsupp.single_apply, Finsupp.indicator_apply]; dsimp; congr 1
  rw [Set.mem_toFinset, mem_orbit, out_eq, @eq_comm _ i]
#align to_conj_equiv_symm_single toConjEquiv_symm_single

theorem single_prod_apply_zero_ne_zero_iff (x : GalConjClasses ℚ (K s)) {a : F} (ha : a ≠ 0)
    (y : GalConjClasses ℚ (K s)) {b : F} (hb : b ≠ 0) :
    (Finsupp.single x a * Finsupp.single y b) 0 ≠ 0 ↔ x = -y := by
  simp_rw [Finsupp.GalConjClasses.mul_def, toConjLinearEquiv_apply, toConjLinearEquiv_symm_apply,
    toConjEquiv_apply_zero_eq]
  simp_rw [toConjEquiv_symm_single, MulMemClass.mk_mul_mk]
  haveI := Nat.noZeroSMulDivisors ℚ F
  simp_rw [Finsupp.indicator_eq_sum_single, sum_mul, mul_sum,
    AddMonoidAlgebra.single_mul_single]
  -- Porting note: next four lines were `simp_rw [Finsupp.coe_finset_sum, sum_apply]`
  rw [Finsupp.coe_finset_sum, sum_apply]
  conv =>
    enter [1, 1, 2, c]
    rw [Finsupp.coe_finset_sum, sum_apply]
  simp_rw [Finsupp.single_apply, ←
    sum_product', sum_ite, sum_const_zero, add_zero, sum_const, smul_ne_zero_iff, mul_ne_zero_iff,
    iff_true_intro ha, iff_true_intro hb, and_true_iff, Ne.def, card_eq_zero, filter_eq_empty_iff]
  push_neg
  simp_rw [Prod.exists, mem_product, Set.mem_toFinset]
  exact GalConjClasses.exist_mem_orbit_add_eq_zero x y
#align single_prod_apply_zero_ne_zero_iff single_prod_apply_zero_ne_zero_iff

theorem single_prod_apply_zero_eq_zero_iff (x : GalConjClasses ℚ (K s)) {a : F} (ha : a ≠ 0)
    (y : GalConjClasses ℚ (K s)) {b : F} (hb : b ≠ 0) :
    (Finsupp.single x a * Finsupp.single y b) 0 = 0 ↔ x ≠ -y :=
  (single_prod_apply_zero_ne_zero_iff s F x ha y hb).not_right
#align single_prod_apply_zero_eq_zero_iff single_prod_apply_zero_eq_zero_iff

end toConjEquiv

section Eval

set_option linter.uppercaseLean3 false

variable (F : Type*) [Field F] [Algebra F ℂ]

def Eval : AddMonoidAlgebra F (K s) →ₐ[F] ℂ :=
  AddMonoidAlgebra.lift F (K s) ℂ
    (expMonoidHom.comp (AddMonoidHom.toMultiplicative (algebraMap (K s) ℂ).toAddMonoidHom))
#align Eval Eval

theorem Eval_apply (x : AddMonoidAlgebra F (K s)) :
    Eval s F x = x.sum fun a c => c • exp (algebraMap (K s) ℂ a) := by
  rw [Eval, AddMonoidAlgebra.lift_apply]; rfl
#align Eval_apply Eval_apply

theorem Eval_ratCoeff (x : ratCoeff s) : Eval s (K s) x = Eval s ℚ (ratCoeffEquiv s x) := by
  simp_rw [Eval_apply, Finsupp.sum, support_ratCoeffEquiv, ratCoeffEquiv_apply_apply]
  refine' sum_congr rfl fun i _ => _
  simp_rw [Algebra.smul_def, IsScalarTower.algebraMap_eq ℚ (K s) ℂ, RingHom.comp_apply]
  congr 2
  simp_rw [IsScalarTower.algebraMap_apply ℚ (⊥ : IntermediateField ℚ (K s)) (K s),
    ← IntermediateField.botEquiv_symm]
  rw [AlgEquiv.symm_apply_apply]
  rfl
#align Eval_rat_coeff Eval_ratCoeff

theorem Eval_toConjAlgEquiv_symm (x : GalConjClasses ℚ (K s) →₀ ℚ) :
    Eval s ℚ ((toConjAlgEquiv s ℚ).symm x) =
      ∑ c : GalConjClasses ℚ (K s) in x.support,
        x c • ∑ i : K s in c.orbit.toFinset, exp (algebraMap (K s) ℂ i) := by
  conv_lhs => rw [← x.sum_single, Finsupp.sum, map_sum]
  simp_rw [toConjAlgEquiv_symm_apply, toConjLinearEquiv_symm_apply]
  have :
    ∀ (s' : Finset (K s)) (b : ℚ),
      ((Finsupp.indicator s' fun _ _ => b).sum fun a c => c • exp (algebraMap (K s) ℂ a)) =
        ∑ i in s', b • exp (algebraMap (K s) ℂ i) :=
    fun s' b => Finsupp.sum_indicator_index _ fun i _ => by rw [zero_smul]
  simp_rw [toConjEquiv_symm_single, AddSubmonoidClass.coe_finset_sum, map_sum,
    Eval_apply, this, smul_sum]
#align Eval_to_conj_alg_equiv_symm Eval_toConjAlgEquiv_symm

end Eval

instance instIsDomain1 : NoZeroDivisors (AddMonoidAlgebra (K s) (K s)) := inferInstance
instance instIsDomain2 : IsDomain (AddMonoidAlgebra ℚ (K s)) := IsDomain.mk
instance instIsDomain3 : IsDomain (GalConjClasses ℚ (K s) →₀ ℚ) :=
MulEquiv.isDomain (mapDomainFixed s ℚ) (toConjAlgEquiv s ℚ).symm
instance : AddZeroClass { x // x ∈ mapDomainFixed s ℚ } := inferInstance

theorem linear_independent_exp_aux2 (s : Finset ℂ) (x : AddMonoidAlgebra ℚ (K s)) (x0 : x ≠ 0)
    (x_ker : x ∈ RingHom.ker (Eval s ℚ)) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (q : Finset (GalConjClasses ℚ (K s))) (_hq :
      (0 : GalConjClasses ℚ (K s)) ∉ q) (w' : GalConjClasses ℚ (K s) → ℚ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K s) ℂ x) : ℂ) = 0 := by
  let V := ∏ f : Gal s, AddMonoidAlgebra.domCongrAut ℚ _ f.toAddEquiv x
  have hV : V ∈ mapDomainFixed s ℚ
  · intro f; dsimp only
    rw [map_prod]; simp_rw [← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact
      (Group.mulLeft_bijective f).prod_comp fun g =>
        AddMonoidAlgebra.domCongrAut ℚ _ g.toAddEquiv x
  have V0 : V ≠ 0
  · dsimp only; rw [prod_ne_zero_iff]; intro f _hf
    rwa [AddEquivClass.map_ne_zero_iff]
  have V_ker : V ∈ RingHom.ker (Eval s ℚ)
  · dsimp only
    rw [← mul_prod_erase (univ : Finset (Gal s)) _ (mem_univ 1)]
    erw [map_one]
    rw [AlgEquiv.one_apply]
    exact Ideal.mul_mem_right _ _ x_ker
  set V' := toConjAlgEquiv s ℚ ⟨V, hV⟩ with V'_def
  have V'0 : V' ≠ 0
  · dsimp only; rw [AddEquivClass.map_ne_zero_iff]
    exact fun h => absurd (Subtype.mk.inj h) V0
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr V'0
  set V'' := V' * Finsupp.single (-i) (1 : ℚ) with V''_def
  have V''0 : V'' ≠ 0
  · have : NoZeroDivisors (GalConjClasses ℚ (K s) →₀ ℚ) := IsDomain.to_noZeroDivisors _
    rw [V''_def]
    refine' mul_ne_zero V'0 fun h => _
    rw [Finsupp.single_eq_zero] at h
    exact one_ne_zero h
  have hV'' : V'' 0 ≠ 0
  · rw [V''_def, ← V'.sum_single, Finsupp.sum, ← add_sum_erase _ _ hi, add_mul, sum_mul,
      Finsupp.add_apply]
    convert_to
      ((Finsupp.single i (V' i) * Finsupp.single (-i) 1 : GalConjClasses ℚ (K s) →₀ ℚ) 0 + 0) ≠ 0
    · congr 1
      rw [Finsupp.finset_sum_apply]
      refine' sum_eq_zero fun j hj => _
      rw [mem_erase, Finsupp.mem_support_iff] at hj
      rw [single_prod_apply_zero_eq_zero_iff _ _ _ hj.2]
      · rw [neg_neg]; exact hj.1
      · exact one_ne_zero
    rw [add_zero, single_prod_apply_zero_ne_zero_iff]
    · rw [neg_neg]
    · rwa [Finsupp.mem_support_iff] at hi
    · exact one_ne_zero
  have zero_mem : (0 : GalConjClasses ℚ (K s)) ∈ V''.support := by rwa [Finsupp.mem_support_iff]
  have Eval_V'' : Eval s ℚ ((toConjAlgEquiv s ℚ).symm V'') = 0
  · dsimp only
    rw [map_mul, Subalgebra.coe_mul, map_mul, AlgEquiv.symm_apply_apply, Subtype.coe_mk]
    rw [RingHom.mem_ker] at V_ker
    rw [V_ker, MulZeroClass.zero_mul]
  use V'' 0, hV'', V''.support.erase 0, not_mem_erase _ _, V''
  rw [← Eval_V'', Eval_toConjAlgEquiv_symm, ← add_sum_erase _ _ zero_mem]
  congr 1
  simp_rw [GalConjClasses.orbit_zero, Set.toFinset_singleton, sum_singleton, map_zero, exp_zero,
    Rat.smul_one_eq_coe]
#align linear_independent_exp_aux2 linear_independent_exp_aux2

instance : AddZeroClass { x // x ∈ ratCoeff s } := inferInstance

theorem linear_independent_exp_aux1 (s : Finset ℂ) (x : AddMonoidAlgebra (K s) (K s)) (x0 : x ≠ 0)
    (x_ker : x ∈ RingHom.ker (Eval s (K s))) :
    ∃ (w : ℚ) (_w0 : w ≠ 0) (q : Finset (GalConjClasses ℚ (K s))) (_hq :
      (0 : GalConjClasses ℚ (K s)) ∉ q) (w' : GalConjClasses ℚ (K s) → ℚ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K s) ℂ x) : ℂ) = 0 := by
  let U := ∏ f : Gal s, AddMonoidAlgebra.mapRangeAlgAut f x
  have hU : ∀ f : Gal s, AddMonoidAlgebra.mapRangeAlgAut f U = U
  · intro f; dsimp only
    simp_rw [map_prod, ← AlgEquiv.trans_apply, ← AlgEquiv.aut_mul, ← map_mul]
    exact (Group.mulLeft_bijective f).prod_comp fun g => AddMonoidAlgebra.mapRangeAlgAut g x
  have U0 : U ≠ 0
  · dsimp only; rw [prod_ne_zero_iff]; intro f _hf
    rwa [AddEquivClass.map_ne_zero_iff]
  have U_ker : U ∈ RingHom.ker (Eval s (K s))
  · suffices
      (fun f : Gal s => AddMonoidAlgebra.mapRangeAlgAut f x) 1 *
          ∏ f : Gal s in univ.erase 1, AddMonoidAlgebra.mapRangeAlgAut f x ∈
            RingHom.ker (Eval s (K s)) by
      convert this
      exact (mul_prod_erase (univ : Finset (Gal s)) _ (mem_univ _)).symm
    dsimp only
    rw [map_one]; exact Ideal.mul_mem_right _ _ x_ker
  have U_mem : ∀ i : K s, U i ∈ IntermediateField.fixedField (⊤ : Subgroup (K s ≃ₐ[ℚ] K s))
  · intro i; dsimp [IntermediateField.fixedField, FixedPoints.intermediateField]
    rintro ⟨f, hf⟩; rw [Subgroup.smul_def, Subgroup.coe_mk]
    replace hU : AddMonoidAlgebra.mapRangeAlgAut f U i = U i; · rw [hU f]
    rwa [AddMonoidAlgebra.mapRangeAlgAut_apply, AddMonoidAlgebra.mapRangeAlgEquiv_apply,
      Finsupp.mapRange_apply] at hU
  replace U_mem : U ∈ ratCoeff s
  · intro i; specialize U_mem i
    have := ((@IsGalois.tfae ℚ _ (K s) _ _ _).out 0 1).mp (by infer_instance)
    rwa [this] at U_mem
  let U' := ratCoeffEquiv s ⟨U, U_mem⟩
  have U'0 : U' ≠ 0
  · dsimp only
    rw [AddEquivClass.map_ne_zero_iff, ZeroMemClass.zero_def]
    exact fun h => absurd (Subtype.mk.inj h) U0
  have U'_ker : U' ∈ RingHom.ker (Eval s ℚ)
  · dsimp only
    rw [RingHom.mem_ker, ← Eval_ratCoeff]
    rwa [RingHom.mem_ker] at U_ker
  exact linear_independent_exp_aux2 s U' U'0 U'_ker
#align linear_independent_exp_aux1 linear_independent_exp_aux1

end

variable {ι : Type*} [Fintype ι]

abbrev range (u : ι → ℂ) (v : ι → ℂ) : Finset ℂ :=
  univ.image u ∪ univ.image v
set_option linter.uppercaseLean3 false in
#align Range range

theorem linear_independent_exp_aux_rat (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℚ) (_ : w ≠ 0) (q : Finset (GalConjClasses ℚ (K (range u v)))) (_ :
      (0 : GalConjClasses _ _) ∉ q) (w' : GalConjClasses ℚ (K (range u v)) → ℚ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K (range u v)) ℂ x) : ℂ) =
        0 := by
  let s := range u v
  have hs : ∀ x ∈ s, IsIntegral ℚ x
  · intro x hx
    cases' mem_union.mp hx with hxu hxv
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hxu
      exact hu i
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hxv
      exact hv i
  have u_mem : ∀ i, u i ∈ K' s
  · intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact
      ⟨poly_ne_zero s hs, u i, mem_union_left _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
        minpoly.aeval _ _⟩
  have v_mem : ∀ i, v i ∈ K' s
  · intro i
    apply IntermediateField.subset_adjoin
    rw [mem_rootSet, map_prod, prod_eq_zero_iff]
    exact
      ⟨poly_ne_zero s hs, v i, mem_union_right _ (mem_image.mpr ⟨i, mem_univ _, rfl⟩),
        minpoly.aeval _ _⟩
  let u' : ∀ _, K s := fun i : ι => Lift s ⟨u i, u_mem i⟩
  let v' : ∀ _, K s := fun i : ι => Lift s ⟨v i, v_mem i⟩
  have u'_inj : Function.Injective u' := fun i j hij =>
    u_inj (Subtype.mk.inj ((Lift s).injective hij))
  replace h : ∑ i, algebraMap (K s) ℂ (v' i) * exp (algebraMap (K s) ℂ (u' i)) = 0
  · simp_rw [algebraMap_K_apply, AlgEquiv.symm_apply_apply, ← h]
  let f : AddMonoidAlgebra (K s) (K s) :=
    Finsupp.onFinset (image u' univ)
      (fun x =>
        if hx : x ∈ image u' univ then
          v' (u'_inj.invOfMemRange ⟨x, mem_image_univ_iff_mem_range.mp hx⟩)
        else 0)
      fun x => by contrapose!; intro hx; rw [dif_neg hx]
  replace hf : Eval s (K s) f = 0
  · rw [Eval_apply, ← h, Finsupp.onFinset_sum _ fun a => _]; swap; · intro _; rw [zero_smul]
    rw [sum_image, sum_congr rfl]; swap; · exact fun i _ j _ hij => u'_inj hij
    intro x _
    rw [dif_pos, u'_inj.right_inv_of_invOfMemRange]; · rfl
    exact mem_image_of_mem _ (mem_univ _)
  have f0 : f ≠ 0
  · rw [Ne.def, Function.funext_iff] at v0; push_neg at v0
    cases' v0 with i hi
    rw [Pi.zero_apply] at hi
    have h : f (u' i) ≠ 0
    · rwa [Finsupp.onFinset_apply, dif_pos, u'_inj.right_inv_of_invOfMemRange, Ne.def,
        AddEquivClass.map_eq_zero_iff, ← ZeroMemClass.coe_eq_zero]
      exact mem_image_of_mem _ (mem_univ _)
    intro f0
    rw [f0, Finsupp.zero_apply] at h
    exact absurd rfl h
  rw [← AlgHom.coe_toRingHom, ← RingHom.mem_ker] at hf
  exact linear_independent_exp_aux1 s f f0 hf
#align linear_independent_exp_aux_rat linear_independent_exp_aux_rat

theorem linear_independent_exp_aux'' (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (_w0 : w ≠ 0) (q : Finset (GalConjClasses ℚ (K (range u v)))) (_hq :
      (0 : GalConjClasses _ _) ∉ q) (w' : GalConjClasses ℚ (K (range u v)) → ℤ),
      (w + ∑ c in q, w' c • ∑ x in c.orbit.toFinset, exp (algebraMap (K (range u v)) ℂ x) : ℂ) =
        0 := by
  obtain ⟨w, w0, q, hq, w', h⟩ := linear_independent_exp_aux_rat u hu u_inj v hv v0 h
  let N := w.den * ∏ c in q, (w' c).den
  have wN0 : (w * N).num ≠ 0
  · refine' Rat.num_ne_zero_of_ne_zero (mul_ne_zero w0 _); dsimp only
    rw [Nat.cast_ne_zero, mul_ne_zero_iff, prod_ne_zero_iff]
    exact ⟨Rat.den_nz _, fun c _hc => Rat.den_nz _⟩
  use (w * N).num, wN0, q, hq, fun c => (w' c * N).num
  have hw : ((w * N).num : ℚ) = w * N
  · dsimp only
    rw [← Rat.den_eq_one_iff, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num]
    norm_cast
  have hw' : ∀ c ∈ q, ((w' c * N).num : ℚ) = w' c * N
  · intro c hc; dsimp only
    rw [← Rat.den_eq_one_iff, ← mul_prod_erase _ _ hc, mul_left_comm, Nat.cast_mul, ← mul_assoc,
      Rat.mul_den_eq_num]
    norm_cast
  convert_to
    (w * N + ∑ c in q, (w' c * N) • ∑ x in c.orbit.toFinset, exp (algebraMap (K (range u v)) ℂ x))
      = 0
  · congr 1
    · norm_cast
    · refine' sum_congr rfl fun i hi => _
      rw [← hw' i hi, Rat.coe_int_num, ← zsmul_eq_smul_cast]
  · simp_rw [mul_comm _ (N : ℂ), mul_comm _ (N : ℚ), ← smul_smul, ← smul_sum, ← nsmul_eq_mul,
      ← nsmul_eq_smul_cast, ← smul_add, h, nsmul_zero]
#align linear_independent_exp_aux'' linear_independent_exp_aux''

theorem linear_independent_exp_aux' (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℚ[X]) (_p0 : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        (w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum : ℂ) = 0 := by
  obtain ⟨w, w0, q, hq, w', h⟩ := linear_independent_exp_aux'' u hu u_inj v hv v0 h
  let c : Fin q.card → GalConjClasses ℚ (K (range u v)) := fun j => q.equivFin.symm j
  have hc : ∀ j, c j ∈ q := fun j => Finset.coe_mem _
  refine' ⟨w, w0, q.card, fun j => (c j).minpoly, _, fun j => w' (c j), _⟩
  · intro j; specialize hc j
    suffices ((c j).minpoly.map (algebraMap ℚ (K (range u v)))).eval
        (algebraMap ℚ (K (range u v)) 0) ≠ 0 by
      rwa [eval_map, ← aeval_def, aeval_algebraMap_apply, _root_.map_ne_zero] at this
    rw [RingHom.map_zero, GalConjClasses.minpoly.map_eq_prod, eval_prod, prod_ne_zero_iff]
    intro a ha
    rw [eval_sub, eval_X, eval_C, sub_ne_zero]
    rintro rfl
    rw [Set.mem_toFinset, GalConjClasses.mem_orbit, GalConjClasses.mk_zero] at ha
    rw [← ha] at hc; exact hq hc
  rw [← h, add_right_inj]
  change ∑ j, ((fun c => w' c • ((c.minpoly.aroots ℂ).map exp).sum) ·) (q.equivFin.symm j) = _
  -- Porting note: were `rw [Equiv.sum_comp q.equivFin.symm, sum_coe_sort]`
  rw [Equiv.sum_comp q.equivFin.symm
    ((fun c ↦ w' c • ((c.minpoly.aroots ℂ).map exp).sum) ·),
    sum_coe_sort _ (fun c ↦ w' c • ((c.minpoly.aroots ℂ).map exp).sum)]
  refine' sum_congr rfl fun c _hc => _
  have : c.minpoly.aroots ℂ = (c.minpoly.aroots (K (range u v))).map (algebraMap (K (range u v)) ℂ)
  · change roots _ = _
    rw [← roots_map, Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ (K (range u v)) ℂ]
    rw [splits_map_iff, RingHom.id_comp]; exact c.splits_minpoly
  rw [this, c.aroots_minpoly_eq_orbit_val, Multiset.map_map, sum_eq_multiset_sum]; rfl
#align linear_independent_exp_aux' linear_independent_exp_aux'

theorem linear_independent_exp_aux (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i)) (v0 : v ≠ 0)
    (h : ∑ i, v i * exp (u i) = 0) :
    ∃ (w : ℤ) (w0 : w ≠ 0) (n : ℕ) (p : Fin n → ℤ[X]) (_p0 : ∀ j, (p j).eval 0 ≠ 0)
      (w' : Fin n → ℤ),
        (w + ∑ j, w' j • (((p j).aroots ℂ).map fun x => exp x).sum : ℂ) = 0 := by
  obtain ⟨w, w0, n, p, hp, w', h⟩ := linear_independent_exp_aux' u hu u_inj v hv v0 h
  choose b hb using
    fun j ↦ IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (p j)
  refine'
    ⟨w, w0, n, fun i => IsLocalization.integerNormalization (nonZeroDivisors ℤ) (p i), _, w', _⟩
  · intro j
    suffices
      aeval (algebraMap ℤ ℚ 0) (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (p j)) ≠ 0
      by rwa [aeval_algebraMap_apply, map_ne_zero_iff _ (algebraMap ℤ ℚ).injective_int] at this
    rw [map_zero, aeval_def, eval₂_eq_eval_map, hb, eval_smul, smul_ne_zero_iff]
    exact ⟨nonZeroDivisors.coe_ne_zero _, hp j⟩
  rw [← h, add_right_inj]
  refine' sum_congr rfl fun j _hj => congr_arg _ (congr_arg _ (Multiset.map_congr _ fun _ _ => rfl))
  change roots _ = roots _
  rw [IsScalarTower.algebraMap_eq ℤ ℚ ℂ, ← Polynomial.map_map, hb,
    zsmul_eq_mul, ← C_eq_int_cast, Polynomial.map_mul, map_C, roots_C_mul]
  rw [map_ne_zero_iff _ (algebraMap ℚ ℂ).injective, Int.cast_ne_zero]
  exact nonZeroDivisors.coe_ne_zero _
#align linear_independent_exp_aux linear_independent_exp_aux

theorem linear_independent_exp_exists_prime_nat'' (c : ℕ) : ∃ n > c, c ^ n < (n - 1)! := by
  refine' ⟨2 * (c ^ 2 + 1), _, _⟩; · have : c ≤ c * c := Nat.le_mul_self _; linarith
  rw [pow_mul, two_mul, add_right_comm, add_tsub_cancel_right]
  refine' lt_of_lt_of_le _ Nat.factorial_mul_pow_le_factorial
  rw [← one_mul (_ ^ _ : ℕ)]
  exact Nat.mul_lt_mul_of_le_of_lt (Nat.one_le_of_lt (Nat.factorial_pos _))
    (Nat.pow_lt_pow_left (Nat.lt_succ_self _) (Nat.succ_ne_zero _)) (Nat.factorial_pos _)
#align linear_independent_exp_exists_prime_nat'' linear_independent_exp_exists_prime_nat''

theorem linear_independent_exp_exists_prime_nat' (n : ℕ) (c : ℕ) :
    ∃ p > n, p.Prime ∧ c ^ p < (p - 1)! := by
  obtain ⟨m, hm, h⟩ := linear_independent_exp_exists_prime_nat'' c
  let N := max (n + 2) (m + 1)
  obtain ⟨p, hp', prime_p⟩ := Nat.exists_infinite_primes N
  have hnp : n + 1 < p := (Nat.add_one_le_iff.mp (le_max_left _ _)).trans_le hp'
  have hnp' : n < p := lt_of_add_lt_of_nonneg_left hnp zero_le_one
  have hmp : m < p := (Nat.add_one_le_iff.mp (le_max_right _ _)).trans_le hp'
  use p, hnp', prime_p
  cases' lt_or_ge m 2 with m2 m2
  · have : c = 0 := by linarith
    rw [this, zero_pow prime_p.pos]
    exact Nat.factorial_pos _
  rcases Nat.eq_zero_or_pos c with (rfl | c0)
  · rw [zero_pow prime_p.pos]
    exact Nat.factorial_pos _
  have m1 : 1 ≤ m := one_le_two.trans m2
  have one_le_m_sub_one : 1 ≤ m - 1 := by rwa [Nat.le_sub_iff_add_le m1]
  have : m - 1 - 1 < p - 1
  · rw [tsub_lt_tsub_iff_right one_le_m_sub_one]
    exact tsub_le_self.trans_lt hmp
  refine' lt_of_lt_of_le _ (Nat.factorial_mul_pow_sub_le_factorial this)
  have : (m - 1 - 1).succ = m - 1 := by rwa [Nat.succ_eq_add_one, tsub_add_cancel_of_le]
  rw [this]
  convert_to c ^ m * c ^ (p - m) < _
  · rw [← pow_add, add_tsub_cancel_of_le]; exact hmp.le
  rw [tsub_tsub_tsub_cancel_right m1]
  exact Nat.mul_lt_mul_of_lt_of_le' h (pow_le_pow_left' (Nat.le_pred_of_lt hm) _) (pow_pos c0 _)
#align linear_independent_exp_exists_prime_nat' linear_independent_exp_exists_prime_nat'

theorem linear_independent_exp_exists_prime_nat (n : ℕ) (a : ℕ) (c : ℕ) :
    ∃ p > n, p.Prime ∧ a * c ^ p < (p - 1)! := by
  obtain ⟨p, hp, prime_p, h⟩ := linear_independent_exp_exists_prime_nat' n (a * c)
  use p, hp, prime_p
  refine' lt_of_le_of_lt _ h
  rcases Nat.eq_zero_or_pos a with (rfl | a0)
  · simp_rw [MulZeroClass.zero_mul, zero_pow' _ prime_p.ne_zero, le_rfl]
  rw [mul_pow]
  apply Nat.mul_le_mul_right
  convert_to a ^ 1 ≤ a ^ p; · rw [pow_one]
  exact Nat.pow_le_pow_of_le_right a0 (Nat.one_le_of_lt prime_p.pos)
#align linear_independent_exp_exists_prime_nat linear_independent_exp_exists_prime_nat

theorem linear_independent_exp_exists_prime (n : ℕ) (a : ℝ) (c : ℝ) :
    ∃ p > n, p.Prime ∧ a * c ^ p / (p - 1)! < 1 := by
  simp_rw [@div_lt_one ℝ _ _ _ (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  obtain ⟨p, hp, prime_p, h⟩ := linear_independent_exp_exists_prime_nat n ⌈|a|⌉.natAbs ⌈|c|⌉.natAbs
  use p, hp, prime_p
  have : a * c ^ p ≤ ⌈|a|⌉ * (⌈|c|⌉ : ℝ) ^ p
  · refine' (le_abs_self _).trans _
    rw [_root_.abs_mul, _root_.abs_pow]
    refine'
      mul_le_mul (Int.le_ceil _) (pow_le_pow_left (abs_nonneg _) (Int.le_ceil _) _)
        (pow_nonneg (abs_nonneg _) _) (Int.cast_nonneg.mpr (Int.ceil_nonneg (abs_nonneg _)))
  refine' this.trans_lt _; clear this
  refine' lt_of_eq_of_lt (_ : _ = ((⌈|a|⌉.natAbs * ⌈|c|⌉.natAbs ^ p : ℕ) : ℝ)) _
  · simp_rw [Nat.cast_mul, Nat.cast_pow, Int.cast_natAbs,
      abs_eq_self.mpr (Int.ceil_nonneg (_root_.abs_nonneg (_ : ℝ)))]
  rwa [Nat.cast_lt]
#align linear_independent_exp_exists_prime linear_independent_exp_exists_prime

theorem exists_sum_map_aroot_smul_eq {R S : Type*} [CommRing R] [Field S] [Algebra R S] (p : R[X])
    (k : R) (e : ℕ) (q : R[X]) (hk : p.leadingCoeff ∣ k) (he : q.natDegree ≤ e)
    (inj : Function.Injective (algebraMap R S))
    (card_aroots : Multiset.card (p.map (algebraMap R S)).roots = p.natDegree) :
    ∃ c, ((p.aroots S).map fun x => k ^ e • aeval x q).sum = algebraMap R S c := by
  obtain ⟨k', rfl⟩ := hk; let k := p.leadingCoeff * k'
  have :
    (fun x : S => k ^ e • aeval x q) =
      (fun x => aeval x (∑ i in range (e + 1), monomial i (k' ^ i * k ^ (e - i) * q.coeff i))) ∘
        fun x => p.leadingCoeff • x
  · funext x; rw [Function.comp_apply]
    simp_rw [map_sum, aeval_eq_sum_range' (Nat.lt_add_one_iff.mpr he), aeval_monomial, smul_sum]
    refine' sum_congr rfl fun i hi => _
    rw [← Algebra.smul_def, smul_pow, smul_smul, smul_smul, mul_comm (_ * _) (_ ^ _), ← mul_assoc,
      ← mul_assoc, ← mul_pow, ← pow_add,
      add_tsub_cancel_of_le (Nat.lt_add_one_iff.mp (mem_range.mp hi))]
  rw [this, ← Multiset.map_map _ fun x => p.leadingCoeff • x]
  have : Multiset.card ((p.aroots S).map fun x => p.leadingCoeff • x) =
      Fintype.card (Fin (Multiset.card (p.aroots S)))
  · rw [Multiset.card_map, Fintype.card_fin]
  rw [← MvPolynomial.symmetricSubalgebra.aevalMultiset_sumPolynomial _ _ this,
    ← MvPolynomial.symmetricSubalgebra.scaleAEvalRoots_eq_aevalMultiset]
  exact ⟨_, rfl⟩
  · exact inj
  · rw [Fintype.card_fin]; exact (card_roots' _).trans (natDegree_map_le _ _)
  · exact card_aroots
#align exists_sum_map_aroot_smul_eq exists_sum_map_aroot_smul_eq

theorem linear_independent_exp (u : ι → ℂ) (hu : ∀ i, IsIntegral ℚ (u i))
    (u_inj : Function.Injective u) (v : ι → ℂ) (hv : ∀ i, IsIntegral ℚ (v i))
    (h : ∑ i, v i * exp (u i) = 0) : v = 0 := by
  by_contra! v0
  obtain ⟨w, w0, m, p, p0, w', h⟩ := linear_independent_exp_aux u hu u_inj v hv v0 h
  have m0 : m ≠ 0
  · rintro rfl; rw [Fin.sum_univ_zero, add_zero, Int.cast_eq_zero] at h
    exact w0 h
  haveI I : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero m0)
  let P := ∏ i : Fin m, p i
  let K := SplittingField (P.map (algebraMap ℤ ℚ))
  have p0' : ∀ j, p j ≠ 0 := by intro j h; specialize p0 j; rw [h, eval_zero] at p0; exact p0 rfl
  have P0 : P.eval 0 ≠ 0 := by dsimp only; rw [eval_prod, prod_ne_zero_iff]; exact fun j _hj => p0 j
  have P0' : P ≠ 0 := by intro h; rw [h, eval_zero] at P0; exact P0 rfl
  have P0'' : P.map (algebraMap ℤ K) ≠ 0 := by
    rwa [Polynomial.map_ne_zero_iff (algebraMap ℤ K).injective_int]

  have splits_p : ∀ j, ((p j).map (algebraMap ℤ K)).Splits (RingHom.id K)
  · intro j
    refine' splits_of_splits_of_dvd _ P0'' _ _
    · rw [IsScalarTower.algebraMap_eq ℤ ℚ K, ← Polynomial.map_map, splits_map_iff, RingHom.id_comp]
      exact IsSplittingField.splits _ _
    simp_rw [Polynomial.map_prod]
    exact dvd_prod_of_mem _ (mem_univ _)

  have sum_aroots_K_eq_sum_aroots_ℂ :
    ∀ (j) (f : ℂ → ℂ),
      (((p j).aroots K).map fun x => f (algebraMap K ℂ x)).sum =
        (((p j).aroots ℂ).map f).sum
  · intro j f
    have : (p j).aroots ℂ = ((p j).aroots K).map (algebraMap K ℂ) := by
      -- Porting note: `simp_rw [aroots_def]` very slow
      rw [aroots_def, aroots_def, IsScalarTower.algebraMap_eq ℤ K ℂ, ← Polynomial.map_map,
        roots_map _ (splits_p j)]
    rw [this, Multiset.map_map]
    rfl

  replace h :
    (w + ∑ j : Fin m, w' j • (((p j).aroots K).map fun x => exp (algebraMap K ℂ x)).sum : ℂ) = 0 :=
    h ▸
      (congr_arg _ <|
        congr_arg _ <| funext fun j => congr_arg _ <| sum_aroots_K_eq_sum_aroots_ℂ j exp)

  let k : ℤ := ∏ j, (p j).leadingCoeff
  have k0 : k ≠ 0 := prod_ne_zero_iff.mpr fun j _hj => leadingCoeff_ne_zero.mpr (p0' j)

  obtain ⟨c, hc'⟩ := exp_polynomial_approx P P0
  let N := max (eval 0 P).natAbs (max k.natAbs w.natAbs)

  let W := sup' univ univ_nonempty fun j => ‖w' j‖
  have W0 : 0 ≤ W := I.elim fun j => (norm_nonneg (w' j)).trans (le_sup' (‖w' ·‖) (mem_univ j))

  obtain ⟨q, hqN, prime_q, hq⟩ :=
    linear_independent_exp_exists_prime N (W * ↑(∑ i : Fin m, Multiset.card ((p i).aroots ℂ)))
      (‖k‖ ^ P.natDegree * c)

  obtain ⟨n, hn, gp, hgp, hc⟩ := hc' q ((le_max_left _ _).trans_lt hqN) prime_q
  replace hgp : gp.natDegree ≤ P.natDegree * q; · rw [mul_comm]; exact hgp.trans tsub_le_self

  have sz_h₁ : ∀ j, (p j).leadingCoeff ∣ k := fun j => dvd_prod_of_mem _ (mem_univ _)
  have sz_h₂ := fun j => (natDegree_eq_card_roots (splits_p j)).symm
  -- Porting note: `simp_rw [map_id] at sz_h₂` very slow
  conv at sz_h₂ =>
    ext
    rw [map_id, natDegree_map_eq_of_injective (algebraMap ℤ K).injective_int]

  choose sz hsz using fun j ↦
    exists_sum_map_aroot_smul_eq (p j) k (P.natDegree * q) gp (sz_h₁ j) hgp
      (algebraMap ℤ K).injective_int (sz_h₂ j)

  let t := P.natDegree * q

  have H :=
    calc
      ‖algebraMap K ℂ
              ((k ^ t * n * w : ℤ) +
                q • ∑ j, w' j • (((p j).aroots K).map fun x => k ^ t • aeval x gp).sum)‖
        = ‖algebraMap K ℂ
              (k ^ t • n • (w : K) +
                q • ∑ j, w' j • (((p j).aroots K).map fun x => k ^ t • aeval x gp).sum)‖ := by
        -- Porting note: `simp_rw [zsmul_eq_mul]` very slow
        -- simp_rw [zsmul_eq_mul]; norm_cast; rw [mul_assoc]
        rw [zsmul_eq_mul, zsmul_eq_mul]
        congr 3
        norm_cast
        rw [mul_assoc]
      _ = ‖algebraMap K ℂ
                (k ^ t • n • (w : K) +
                  q • ∑ j, w' j • (((p j).aroots K).map fun x => k ^ t • aeval x gp).sum) -
              k ^ t •
                n • (w + ∑ j, w' j • (((p j).aroots K).map fun x => exp (algebraMap K ℂ x)).sum)‖ :=
        by rw [h, smul_zero, smul_zero, sub_zero]
      _ = ‖algebraMap K ℂ
                (k ^ t • n • (w : K) +
                  k ^ t • ∑ j, w' j • (((p j).aroots K).map fun x => q • aeval x gp).sum) -
              (k ^ t • n • (w : ℂ) +
                k ^ t •
                  ∑ j, w' j • (((p j).aroots K).map fun x => n • exp (algebraMap K ℂ x)).sum)‖ := by
        -- simp_rw [smul_add, smul_sum, Multiset.smul_sum, Multiset.map_map, Function.comp,
        --  smul_comm n, smul_comm (k ^ t), smul_comm q]
        congr 4 <;>
        · repeat rw [smul_add]
          repeat rw [smul_sum]
          congr; funext
          repeat rw [Multiset.smul_sum]
          repeat rw [Multiset.map_map]
          dsimp only [(· ∘ ·)]
          congr; funext
          repeat rw [smul_comm n]
          repeat rw [smul_comm (k ^ t)]
          repeat rw [smul_comm q]
          simp only [algebraMap_int_eq, nsmul_eq_mul, zsmul_eq_mul, comp_mul_left, Int.cast_pow,
            Int.cast_prod, Function.comp_apply]
          ring
      _ = ‖(k ^ t • n • (w : ℂ) +
                  k ^ t •
                    ∑ j,
                      w' j • (((p j).aroots K).map fun x => q • algebraMap K ℂ (aeval x gp)).sum) -
              (k ^ t • n • (w : ℂ) +
                k ^ t •
                  ∑ j, w' j • (((p j).aroots K).map fun x => n • exp (algebraMap K ℂ x)).sum)‖ := by
        -- simp only [map_add, map_nsmul, map_zsmul, map_intCast, map_sum, map_multiset_sum,
        --   Multiset.map_map, Function.comp]
        congr 4
        rw [map_add, map_zsmul, map_zsmul, map_zsmul, map_intCast, map_sum]
        congr; funext
        rw [map_zsmul, map_multiset_sum, Multiset.map_map]
        congr; funext
        rw [Function.comp_apply, map_nsmul]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      q • algebraMap K ℂ (aeval x gp) - n • exp (algebraMap K ℂ x)).sum‖ := by
        -- simp only [add_sub_add_left_eq_sub, ← smul_sub, ← sum_sub_distrib,
        --   ← Multiset.sum_map_sub]
        rw [add_sub_add_left_eq_sub, ← smul_sub, ← sum_sub_distrib]
        congr; funext
        rw [← smul_sub, ← Multiset.sum_map_sub]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      q • aeval (algebraMap K ℂ x) gp - n • exp (algebraMap K ℂ x)).sum‖ := by
        -- simp_rw [aeval_algebraMap_apply]
        congr; funext; congr; funext; congr 2
        rw [aeval_algebraMap_apply]
      _ = ‖k ^ t •
              ∑ j,
                w' j •
                  (((p j).aroots K).map fun x =>
                      (fun x' => q • aeval x' gp - n • exp x') (algebraMap K ℂ x)).sum‖ :=
        rfl
      _ = ‖k ^ t • ∑ j, w' j • (((p j).aroots ℂ).map fun x => q • aeval x gp - n • exp x).sum‖ := by
        congr; funext; congr 1
        exact sum_aroots_K_eq_sum_aroots_ℂ _ (fun x ↦ q • aeval x gp - n • exp x)
      _ ≤ ‖k ^ t‖ * ∑ j, W * (((p j).aroots ℂ).map fun _ => c ^ q / ↑(q - 1)!).sum := by
        refine' (norm_zsmul_le _ _).trans _
        refine' mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        refine' (norm_sum_le _ _).trans _
        refine' sum_le_sum fun j _hj => _
        refine' (norm_zsmul_le _ _).trans _
        refine' mul_le_mul (le_sup' (‖w' ·‖) (mem_univ j)) _ (norm_nonneg _) W0
        refine' (norm_multiset_sum_le _).trans _
        rw [Multiset.map_map]
        refine' Multiset.sum_map_le_sum_map _ _ fun x hx => _
        rw [Function.comp_apply, norm_sub_rev]
        refine' hc _
        rw [mem_roots_map_of_injective (algebraMap ℤ ℂ).injective_int (p0' j)] at hx
        rw [mem_roots_map_of_injective (algebraMap ℤ ℂ).injective_int P0', ← aeval_def]
        rw [map_prod]
        exact prod_eq_zero (mem_univ j) hx
  -- simp_rw [Int.norm_eq_abs, Int.cast_pow, _root_.abs_pow, ← Int.norm_eq_abs, Multiset.map_const,
  --   Multiset.sum_replicate, ← mul_sum, ← sum_smul, nsmul_eq_mul, mul_comm (‖k‖ ^ t), mul_assoc,
  --   mul_comm (_ / _ : ℝ), t, pow_mul, mul_div (_ ^ _ : ℝ), ← mul_pow, ← mul_assoc, mul_div, ←
  --   pow_mul] at H
  rw [Int.norm_eq_abs, _root_.abs_pow, Int.cast_pow, ← Int.norm_eq_abs] at H
  conv_rhs at H =>
    congr
    · skip
    · congr
      · skip
      · ext
        rw [Multiset.map_const', Multiset.sum_replicate]
  conv_rhs at H =>
    rw [← mul_sum, mul_left_comm, ← sum_smul, nsmul_eq_mul, mul_comm (‖k‖ ^ t), mul_assoc,
      mul_comm (_ / _ : ℝ), pow_mul, mul_div (_ ^ _ : ℝ), ← mul_pow, ← mul_assoc, mul_div]
  replace H := H.trans_lt hq
  have : ∑ j, w' j • (((p j).aroots K).map fun x : K => k ^ (P.natDegree * q) • aeval x gp).sum =
      algebraMap ℤ K (∑ j, w' j • sz j)
  · rw [map_sum]; congr; funext j; rw [map_zsmul, hsz]
  rw [this] at H
  have :
    ‖algebraMap K ℂ (↑(k ^ (P.natDegree * q) * n * w) + ↑q * algebraMap ℤ K (∑ j, w' j • sz j))‖ =
      ‖algebraMap ℤ ℂ (k ^ (P.natDegree * q) * n * w + q * ∑ j, w' j • sz j)‖
  · simp_rw [IsScalarTower.algebraMap_apply ℤ K ℂ, algebraMap_int_eq, Int.coe_castRingHom]
    norm_cast
  rw [nsmul_eq_mul, this, algebraMap_int_eq, Int.coe_castRingHom, norm_int, ← Int.cast_abs,
    ← Int.cast_one, Int.cast_lt, Int.abs_lt_one_iff] at H
  replace H : (k ^ (P.natDegree * q) * n * w + q * ∑ j : Fin m, w' j • sz j) % q = 0
  · rw [H, Int.zero_emod]
  rw [Int.add_mul_emod_self_left, ← Int.dvd_iff_emod_eq_zero] at H
  replace H :=
    (Int.Prime.dvd_mul prime_q H).imp_left (Int.Prime.dvd_mul prime_q ∘ Int.coe_nat_dvd_left.mpr)
  revert H; rw [Int.natAbs_pow, imp_false]; push_neg
  exact
    ⟨⟨fun h =>
        Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr k0)
          (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hqN)
          (Nat.Prime.dvd_of_dvd_pow prime_q h),
        fun h => hn ((Int.dvd_iff_emod_eq_zero _ _).mp (Int.coe_nat_dvd_left.mpr h))⟩,
      Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr w0)
        (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hqN)⟩
#align linear_independent_exp linear_independent_exp

theorem Complex.isIntegral_int_i : IsIntegral ℤ I := by
  refine' ⟨X ^ 2 + C 1, monic_X_pow_add_C two_ne_zero, _⟩
  rw [eval₂_add, eval₂_X_pow, eval₂_C, I_sq, eq_intCast, Int.cast_one, add_left_neg]
set_option linter.uppercaseLean3 false in
#align complex.is_integral_int_I Complex.isIntegral_int_i

theorem Complex.isIntegral_rat_i : IsIntegral ℚ I :=
  Complex.isIntegral_int_i.tower_top
set_option linter.uppercaseLean3 false in
#align complex.is_integral_rat_I Complex.isIntegral_rat_i

theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (exp a) := by
  intro h
  have is_integral_a : IsIntegral ℚ a :=
    isAlgebraic_iff_isIntegral.mp (ha.tower_top_of_injective (algebraMap ℤ ℚ).injective_int)
  have is_integral_expa : IsIntegral ℚ (exp a) :=
    isAlgebraic_iff_isIntegral.mp (h.tower_top_of_injective (algebraMap ℤ ℚ).injective_int)
  have := linear_independent_exp (fun i : Prop => if i then a else 0) ?_ ?_
      (fun i : Prop => if i then 1 else -exp a) ?_ ?_
  · simpa [ite_eq_iff] using congr_fun this True
  · intro i; dsimp only; split_ifs
    exacts [is_integral_a, isIntegral_zero]
  · intro i j; dsimp
    split_ifs with h_1 h_2 h_2 <;>
      simp only [IsEmpty.forall_iff, forall_true_left, a0, a0.symm, *]
  · intro i; dsimp; split_ifs; exacts [isIntegral_one, is_integral_expa.neg]
  simp
#align transcendental_exp transcendental_exp

theorem transcendental_e : Transcendental ℤ (exp 1) :=
  transcendental_exp one_ne_zero isAlgebraic_one

theorem transcendental_pi : Transcendental ℤ Real.pi := by
  intro h
  have is_integral_pi' : IsIntegral ℚ Real.pi :=
    isAlgebraic_iff_isIntegral.mp
      (h.tower_top_of_injective (algebraMap ℤ ℚ).injective_int)
  have is_integral_pi : IsIntegral ℚ (algebraMap ℝ ℂ Real.pi) :=
    (isIntegral_algebraMap_iff (algebraMap ℝ ℂ).injective).mpr is_integral_pi'
  have := linear_independent_exp (fun i : Prop => if i then Real.pi * I else 0) ?_ ?_
      (fun _ : Prop => 1) ?_ ?_
  · simpa only [Pi.zero_apply, one_ne_zero] using congr_fun this False
  · intro i; dsimp only; split_ifs
    · exact is_integral_pi.mul Complex.isIntegral_rat_i
    · exact isIntegral_zero
  · intro i j; dsimp
    split_ifs <;>
      simp only [IsEmpty.forall_iff, forall_true_left, *, ofReal_eq_zero, mul_eq_zero,
        Real.pi_ne_zero, I_ne_zero, or_false, zero_eq_mul]
  · intro i; dsimp; exact isIntegral_one
  simp
#align transcendental_pi transcendental_pi
