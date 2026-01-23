/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral

/-!

# Results about coefficients of polynomials being integral

## Main results
- `Polynomial.isIntegral_coeff_of_dvd`: If a monic polynomial `p` divides another monic polynomial
  with integral coefficients, then the coefficients of `p` are themselves integral.
- `Polynomial.isIntegral_iff_isIntegral_coeff`:
  `p : S[X]` is integral over `R[X]` iff the coefficients of `p` are integral over `R`.
- `MvPolynomial.isIntegral_iff_isIntegral_coeff`: `p : MvPolynomial σ S` is integral over
  `MvPolynomial σ R` iff the coefficients of `p` are integral over `R`.
- We also provide the instance `[IsIntegrallyClosed R] : IsIntegrallyClosed R[X]`.

-/

@[expose] public section

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Polynomial

lemma isIntegral_coeff_prod
    (s : Finset ι) (p : ι → S[X]) (H : ∀ i ∈ s, ∀ j, IsIntegral R ((p i).coeff j)) (j : ℕ) :
    IsIntegral R ((s.prod p).coeff j) := by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simp [coeff_one, apply_ite, isIntegral_zero, isIntegral_one]
  | insert a s has IH =>
    rw [Finset.prod_insert has, coeff_mul]
    exact IsIntegral.sum _ fun i hi ↦ .mul (H _ (by simp) _) (IH (fun _ _ ↦ H _ (by aesop)) _)

lemma isIntegral_coeff_of_factors (p : S[X])
    (hpmon : IsIntegral R p.leadingCoeff) (hp : p.Splits)
    (hpr : ∀ x, p.IsRoot x → IsIntegral R x) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  classical
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hp
  rw [hm, Multiset.prod_eq_prod_coe, coeff_C_mul]
  refine .mul hpmon (isIntegral_coeff_prod _ _ ?_ _)
  have H {x} (hx : x ∈ m) : p.IsRoot x := by
    rw [IsRoot, hm, eval_mul, eval_multiset_prod, Multiset.prod_eq_zero, mul_zero]
    simpa [sub_eq_zero]
  rintro ⟨a, ⟨i, hi⟩⟩ -
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (i.zero_le.trans_lt hi))
  simp [coeff_X, coeff_C, IsIntegral.sub, apply_ite (IsIntegral R),
    isIntegral_one, isIntegral_zero, hpr x (H hx)]

open scoped TensorProduct in
@[stacks 00H6 "(1)"]
lemma isIntegral_coeff_of_dvd (p : R[X]) (q : S[X]) (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p.map (algebraMap R S)) (i : ℕ) : IsIntegral R (q.coeff i) := by
  nontriviality S
  obtain ⟨T, _, _, _, _, _, hqT⟩ := hq.exists_splits_map
  algebraize [(algebraMap S T).comp (algebraMap R S)]
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S T)
    (FaithfulSMul.algebraMap_injective S _)).mp ?_
  rw [IsScalarTower.coe_toAlgHom', ← coeff_map]
  refine Polynomial.isIntegral_coeff_of_factors _ (by simp [hq.map, isIntegral_one]) hqT ?_ i
  intro x hx
  exact ⟨p, hp, by simpa using aeval_eq_zero_of_dvd_aeval_eq_zero (a := x) H (by simp_all)⟩

end Polynomial

section

open scoped nonZeroDivisors

open Polynomial

attribute [local instance] Polynomial.algebra

@[stacks 00H0 "(1)"]
lemma IsAlmostIntegral.coeff [IsDomain R] [FaithfulSMul R S]
    {p : S[X]} (hp : IsAlmostIntegral R[X] p) (i : ℕ) :
    IsAlmostIntegral R (p.coeff i) := by
  have H {q : S[X]} (hq : IsAlmostIntegral R[X] q) : IsAlmostIntegral R q.leadingCoeff := by
    obtain ⟨p, hp, hp'⟩ := hq
    refine ⟨p.leadingCoeff, by simpa using hp, fun n ↦ ?_⟩
    obtain ⟨r, hr⟩ := hp' n
    simp only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] at hr ⊢
    by_cases h : algebraMap R S p.leadingCoeff * q.leadingCoeff ^ n = 0
    · simp [h]
    have h' : q.leadingCoeff ^ n ≠ 0 := by aesop
    use r.leadingCoeff
    simp only [← leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective R S), hr] at h ⊢
    rw [← leadingCoeff_pow' h'] at h ⊢
    rw [leadingCoeff_mul' h]
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with | h n IH =>
  by_cases hp' : p.natDegree = 0
  · obtain ⟨p, rfl⟩ := natDegree_eq_zero.mp hp'
    simp only [coeff_C]
    split_ifs with h
    · simpa using H hp
    · exact (completeIntegralClosure R S).zero_mem
  by_cases hi : i = p.natDegree
  · simp [hi, H hp]
  have : IsAlmostIntegral R[X] p.eraseLead := by
    rw [← self_sub_monomial_natDegree_leadingCoeff, ← mem_completeIntegralClosure,
      ← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S), ← Polynomial.map_pow]
    refine sub_mem hp (mul_mem ?_ (algebraMap_mem (R := R[X]) _ _))
    obtain ⟨r, hr, hr'⟩ := H hp
    refine ⟨C r, by simpa using hr, fun n ↦ ?_⟩
    obtain ⟨s, hs⟩ := hr' n
    exact ⟨C s, by simp [Algebra.smul_def, hs]⟩
  simpa [hi, eraseLead_coeff_of_ne] using
    IH (p := p.eraseLead) _ (p.eraseLead_natDegree_le.trans_lt (by lia)) this rfl

@[stacks 00H0 "(2)"]
protected lemma IsIntegral.coeff
    {p : S[X]} (hp : IsIntegral R[X] p) (i : ℕ) : IsIntegral R (p.coeff i) := by
  nontriviality R
  nontriviality S
  obtain rfl | hp0 := eq_or_ne p 0; · simp [isIntegral_zero]
  let q := minpoly R[X] p
  let m := (q.support.sup fun i ↦ (q.coeff i).natDegree) + p.natDegree + 1
  have hm₁ (i) : (q.coeff i).natDegree < m := by
    by_cases hi : i ∈ q.support
    · exact (Finset.le_sup (f := fun i ↦ (q.coeff i).natDegree) hi).trans_lt (by lia)
    · simp_all [m]
  have hm₁' : (q.eval (X ^ m)).Monic := by
    rw [eval_eq_sum_range, Finset.sum_range_succ]
    refine .add_of_right (by simp [q, minpoly.monic hp, ← pow_mul]) (degree_lt_degree ?_)
    refine lt_of_lt_of_eq (b := m * q.natDegree) ?_ (by simp [q, minpoly.monic hp, ← pow_mul])
    refine (natDegree_sum_le ..).trans_lt ((Finset.fold_max_lt _).mpr
      ⟨by simpa using ⟨by lia, minpoly.natDegree_pos hp⟩, fun i hi ↦ ?_⟩)
    dsimp
    simp only [Finset.mem_range] at hi
    grw [← pow_mul, natDegree_mul_le, natDegree_X_pow, ← Nat.add_one_le_iff.mpr hi]
    have := hm₁ i
    lia
  have hm₂ : p.natDegree < m := by grind
  have h₀ : algebraMap R[X] S[X] X = X := by simp
  have : (((taylor (X ^ m)) q).map (algebraMap R[X] S[X])).IsRoot (p - X ^ m) := by
    simpa [-algebraMap_def, q, h₀] using
      ((q.map (algebraMap _ _)).taylor_eval (X ^ m) (p - X ^ m) :)
  have : X ^ m - p ∣ (eval (X ^ m) q).map (algebraMap _ _) := by
    change X ^ m - p ∣ Algebra.ofId R[X] S[X] _
    rw [← coe_aeval_eq_eval, ← aeval_algHom_apply, ← neg_dvd, neg_sub]
    simpa [Polynomial.taylor_coeff_zero, -algebraMap_def, h₀] using this.dvd_coeff_zero
  have := (isIntegral_coeff_of_dvd _ _ hm₁'
    ((monic_X_pow _).sub_of_left (by simpa [← natDegree_lt_iff_degree_lt, hp0])) this i).neg
  obtain hi | hi := le_or_gt i p.natDegree
  · simpa [show i ≠ m by lia] using this
  · simp [coeff_eq_zero_of_natDegree_lt hi, isIntegral_zero]

@[deprecated (since := "2026-01-01")]
alias IsIntegral.coeff_of_exists_smul_mem_lifts := IsIntegral.coeff

@[deprecated (since := "2026-01-01")] alias IsIntegral.coeff_of_isFractionRing := IsIntegral.coeff

theorem Polynomial.isIntegral_iff_isIntegral_coeff {f : S[X]} :
    IsIntegral R[X] f ↔ ∀ n, IsIntegral R (f.coeff n) := by
  refine ⟨IsIntegral.coeff, fun H ↦ ?_⟩
  rw [← f.sum_monomial_eq, Polynomial.sum]
  simp only [← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S)]
  exact .sum _ fun i _ ↦ ((H i).map (CAlgHom (R := R))).tower_top.mul (.pow isIntegral_algebraMap _)

lemma IsIntegral.of_aeval_monic_of_isIntegral_coeff {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} {p : A[X]} (monic : p.Monic) (deg : p.natDegree ≠ 0)
    (hx : IsIntegral R (eval x p)) (hp : ∀ i, IsIntegral R (p.coeff i)) : IsIntegral R x := by
  obtain ⟨q, hqp, hdeg, hq⟩ :=
    lifts_and_natDegree_eq_and_monic (p := p) (f := algebraMap (integralClosure R A) _)
    (p.lifts_iff_coeff_lifts.mpr (by simpa)) monic
  exact isIntegral_trans _ (.of_aeval_monic hq (hdeg ▸ deg)
    (by simpa [← eval_map_algebraMap, hqp] using hx.tower_top))

@[stacks 030A]
instance {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed R[X] := by
  let K := FractionRing R
  have : IsIntegrallyClosed K[X] := UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn R[X] K[X] from .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K[X]
  refine isIntegrallyClosedIn_iff.mpr ⟨map_injective _ (IsFractionRing.injective _ _), ?_⟩
  refine fun {p} hp ↦ (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
  exact IsIntegrallyClosed.isIntegral_iff.mp (hp.coeff _)

end

attribute [local instance] MvPolynomial.algebraMvPolynomial in
attribute [-simp] AlgEquiv.symm_toRingEquiv in
theorem MvPolynomial.isIntegral_iff_isIntegral_coeff.{w} {σ : Type w} {f : MvPolynomial σ S} :
    IsIntegral (MvPolynomial σ R) f ↔ ∀ n, IsIntegral R (f.coeff n) := by
  classical
  refine ⟨fun H n ↦ ?mp, fun H ↦ ?mpr⟩
  case mpr =>
    rw [← f.support_sum_monomial_coeff]
    simp_rw [monomial_eq]
    refine IsIntegral.sum _ fun n _ ↦ .mul ((H n).map (Algebra.ofId _ _)).tower_top
      (.prod _ fun i _ ↦ .pow ?_ _)
    convert isIntegral_algebraMap (x := MvPolynomial.X i)
    simp only [algebraMap_def, map_X]
  unfold IsIntegral at H
  wlog hσ : Finite σ generalizing σ
  · obtain ⟨g, hg⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range (τ := f.vars) f _
      Subtype.val_injective (by simp)
    by_cases hn : n ∈ Set.range (Finsupp.mapDomain ((↑) : f.vars → σ))
    · obtain ⟨n, rfl⟩ := hn
      simp_rw [← hg, coeff_rename_mapDomain _ Subtype.val_injective]
      exact this (f := g) (RingHom.IsIntegralElem.of_map
        (g := (rename ((↑) : f.vars → σ)).toRingHom) (rename_injective _ Subtype.val_injective)
        (.of_comp (f := (killCompl (f := ((↑) : f.vars → σ)) Subtype.val_injective).toRingHom) <| by
        simp only [AlgHom.toRingHom_eq_coe, algebraMap_def, RingHom.coe_coe, hg]
        convert H.map ((rename Subtype.val).comp
          (killCompl (f := ((↑) : f.vars → σ)) Subtype.val_injective)).toRingHom
        · exact RingHom.ext (by simp [MvPolynomial.killCompl_map])
        · nth_rw 1 11 [← hg]; simp)) n (.of_fintype _)
    · rw [← hg, coeff_rename_eq_zero _ _ _ (by grind)]
      exact isIntegral_zero
  revert f n
  apply Finite.induction_empty_option _ _ _ σ
  · intro α β e IH f H n
    have := @IH (rename e.symm f) (.of_map (g := (rename e).toRingHom)
      (rename_injective _ e.injective) <| .of_comp (f := (rename e.symm).toRingHom)
        (by convert H <;> aesop)) (n.embDomain e.symm)
    simpa [Finsupp.embDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective] using this
  · intro f H n
    refine .of_map (g := (isEmptyAlgEquiv _ PEmpty).symm.toRingHom)
      (isEmptyAlgEquiv _ PEmpty).symm.injective
      (.of_comp (f := (isEmptyAlgEquiv _ PEmpty).toRingHom) ?_)
    convert H
    · aesop (add simp MvPolynomial.isEmptyAlgEquiv)
    · obtain rfl := Subsingleton.elim n 0
      have : constantCoeff = (isEmptyAlgEquiv S PEmpty).toRingHom := by aesop
      simpa [-EmbeddingLike.apply_eq_iff_eq, -isEmptyAlgEquiv_apply] using
        congr((isEmptyAlgEquiv S PEmpty.{w + 1}).symm ($this f))
  · intro α _ IH f H n
    have := IH (IsIntegral.coeff (R := MvPolynomial α R)
      (p := optionEquivLeft _ _ f) (.of_map
      (g := (optionEquivLeft _ _).symm.toRingHom) (optionEquivLeft _ _).symm.injective
      (.of_comp (f := (optionEquivLeft _ _).toRingHom) (by
        convert H
        · ext i m
          · aesop
          · cases i <;> aesop
        · aesop))) (n .none)) n.some
    rwa [optionEquivLeft_coeff_some_coeff_none] at this

end
