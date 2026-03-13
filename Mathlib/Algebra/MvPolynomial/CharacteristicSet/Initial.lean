/-
Copyright (c) 2026 Yuxuan Xiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxuan Xiao
-/
module

public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Initial of a polynomial

This file defines the **initial** of a multivariate polynomial.

For a polynomial `p` with main variable `xᵢ`, the initial is the coefficient (a polynomial)
of the highest power of `xᵢ` appearing in `p`.

## Main declarations

* `MvPolynomial.initialOf i p`:
  The initial of `p` with respect to a specific variable `i`.
  This is the coefficient of `X i ^ degᵢ(p)`.
* `MvPolynomial.initial`:
  The initial of `p` with respect to its main variable.
  For constants, this is defined as `1`.

## Main results

* `initialOf_eq_leadingCoeff`:
  `initᵢ(p)` is the leading coefficient when viewing `p` as a univariate polynomial in `X i`.
* `initialOf_decomposition`:
  `p = initᵢ(p) * Xᵢ^degᵢ(p) + remainder` where `degᵢ(remainder) < degᵢ(p)`
* `initial_reducedTo`: The initial is always reduced w.r.t. the original polynomial
* `initialOf_mul`: `initᵢ(p * q) = initᵢ(p) * initᵢ(q)` (for integral domains)

-/

@[expose] public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

section InitialOf

variable (i j : σ) (p : MvPolynomial σ R)

/-- The "initial" of a polynomial `p` with respect to a variable `i`.
It is the coefficient of the highest power of `X i` appearing in `p`.
More formally, it is the sum of terms in `p` whose degree in `i` equals `p.degreeOf i`,
but with the variable `i` removed (set to 1). -/
noncomputable def initialOf : MvPolynomial σ R :=
  ∑ s ∈ p.support with s i = p.degreeOf i, monomial (s.erase i) (p.coeff s)

theorem initialOf_def {p : MvPolynomial σ R} {i : σ} :
    p.initialOf i = ∑ s ∈ p.support with s i = p.degreeOf i, monomial (s.erase i) (p.coeff s) := rfl

@[simp] theorem initialOf_zero : (0 : MvPolynomial σ R).initialOf i = 0 := rfl

@[simp] theorem initialOf_monomial (s : σ →₀ ℕ) (r : R) :
    (monomial s r).initialOf i = monomial (s.erase i) r := by
  by_cases r_zero : r = 0
  · simp only [r_zero, monomial_zero, initialOf_zero]
  rewrite [initialOf_def, Finset.sum_filter, ← single_eq_monomial, degreeOf_eq_sup, support]
  rewrite [Finsupp.support_single_ne_zero s r_zero, Finset.sum_singleton, Finset.sup_singleton]
  rw [if_pos rfl, coeff, Finsupp.single_eq_same]

@[simp] theorem initialOf_C (r : R) : (C r : MvPolynomial σ R).initialOf i = C r :=
  by rw [C_apply, initialOf_monomial, Finsupp.erase_zero]

@[simp] theorem initialOf_one : (1 : MvPolynomial σ R).initialOf i = 1 := by rw [← C_1, initialOf_C]

@[simp] theorem initialOf_mul_X_self : (p * X i).initialOf i = p.initialOf i := by
  by_cases p_zero : p = 0
  · rw [p_zero, zero_mul, initialOf_zero]
  rewrite [initialOf_def, (degreeOf_mul_X_eq_degreeOf_add_one_iff i p).mpr p_zero]
  simp [Finset.sum_filter, initialOf_def]

theorem initialOf_mul_X_of_ne {i j : σ} (h : i ≠ j) :
    (p * X j).initialOf i = p.initialOf i * X j := by
  rewrite [initialOf_def, degreeOf_mul_X_of_ne _ h]
  simp [h, monomial_add_single, initialOf_def, Finset.sum_filter, Finset.sum_mul]

@[simp] theorem initialOf_mul_X_self_pow (k : ℕ) : (p * X i ^ k).initialOf i = p.initialOf i := by
  induction k with
  | zero => rw [pow_zero, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, initialOf_mul_X_self, hk]

theorem initialOf_mul_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    (p * X j ^ k).initialOf i = p.initialOf i * X j ^ k := by
  induction k with
  | zero => rw [pow_zero, mul_one, mul_one]
  | succ k hk => rw [pow_add, pow_one, ← mul_assoc, initialOf_mul_X_of_ne _ h, hk, mul_assoc]

@[simp] theorem initialOf_X_self : (X i).initialOf i = (1 : MvPolynomial σ R) :=
  by rw [← one_mul (X i), initialOf_mul_X_self, initialOf_one]

@[simp] theorem initialOf_X_self_pow (k : ℕ) : (X i ^ k).initialOf i = (1 : MvPolynomial σ R) :=
  by rw [← one_mul (X i ^ k), initialOf_mul_X_self_pow, initialOf_one]

theorem initialOf_X_of_ne {i j : σ} (h : i ≠ j) : (X j).initialOf i = (X j : MvPolynomial σ R) :=
  by rw [← one_mul (X j), initialOf_mul_X_of_ne _ h, initialOf_one]

theorem initialOf_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    (X j ^ k).initialOf i = (X j : MvPolynomial σ R) ^ k := by
  rw [← one_mul (X j ^ k), initialOf_mul_X_pow_of_ne _ _ h, initialOf_one]

theorem coeff_initialOf_eq_of_apply_ne_zero {s : σ →₀ ℕ} (h : s i ≠ 0) :
    (p.initialOf i).coeff s = 0 := by
  classical
  rewrite [initialOf, coeff_sum, Finset.sum_congr rfl fun _ _ ↦ coeff_monomial s _ _]
  have (x : σ →₀ ℕ) : x.erase i = s ↔ False := by
    refine iff_false_intro <| Finsupp.ne_iff.mpr ⟨i, ?_⟩
    rewrite [Finsupp.erase_apply, if_pos rfl]
    exact h.symm
  simp only [this, ↓reduceIte, Finset.sum_const_zero]

theorem coeff_initialOf_eq_of_apply_eq_zero {s : σ →₀ ℕ} (h : s i = 0) :
    (p.initialOf i).coeff s = p.coeff (s.update i (p.degreeOf i)) := by
  classical
  rewrite [initialOf, coeff_sum, Finset.sum_congr rfl fun _ _ ↦ coeff_monomial s _ _]
  have (x : σ →₀ ℕ) : x i = p.degreeOf i ∧ x.erase i = s ↔ x = s.update i (p.degreeOf i) := by
    refine ⟨fun hx ↦ Finsupp.ext fun j ↦ ?_, fun hx ↦ ?_⟩
    · rewrite [Finsupp.update_apply]
      split_ifs with hj
      · rw [hj, hx.1]
      rw [← hx.2, Finsupp.erase_apply, if_neg hj]
    simp only [hx, Finsupp.update_apply, reduceIte, Finsupp.erase_update_eq_erase, true_and]
    refine Finsupp.erase_of_notMem_support ?_
    exact Finsupp.notMem_support_iff.mpr h
  simpa [Finset.sum_filter, ← ite_and, this] using Eq.symm

theorem coeff_initialOf_eq (s : σ →₀ ℕ) :
    (p.initialOf i).coeff s = if s i = 0 then p.coeff (s.update i (p.degreeOf i)) else 0 :=
  if hs : s i = 0 then if_pos hs ▸ coeff_initialOf_eq_of_apply_eq_zero i p hs
  else if_neg hs ▸ coeff_initialOf_eq_of_apply_ne_zero i p hs

lemma coeff_initialOf_eq_of_ne_zero {i : σ} {p : MvPolynomial σ R} {s : σ →₀ ℕ} :
    (p.initialOf i).coeff s ≠ 0 → (p.initialOf i).coeff s = p.coeff (s.update i (p.degreeOf i)) :=
  fun h ↦ coeff_initialOf_eq_of_apply_eq_zero i p
    (by contrapose! h; exact (coeff_initialOf_eq_of_apply_ne_zero i p) h)

@[simp] theorem degreeOf_initialOf_self : (p.initialOf i).degreeOf i = 0 := by
  classical
  apply Multiset.count_eq_zero.mpr
  apply (not_iff_not.mpr mem_degrees).mpr
  simp only [ne_eq, Finsupp.mem_support_iff, not_exists, not_and, Decidable.not_not]
  intro s hs
  contrapose! hs
  exact coeff_initialOf_eq_of_apply_ne_zero i p hs

/-- The initial of `p` with respect to `i` is the leading coefficient
when viewing `p` as a univariate polynomial in `X i`. -/
theorem initialOf_eq_leadingCoeff [DecidableEq σ] {p : MvPolynomial σ R} {i : σ} :
    p.initialOf i = rename Subtype.val
      (optionEquivLeft R {b // b ≠ i} (rename (Equiv.optionSubtypeNe i).symm p)).leadingCoeff := by
  ext s
  set f := (Equiv.optionSubtypeNe i).symm
  have hsv : Subtype.val = f.symm ∘ (@some { b // b ≠ i }) := rfl
  by_cases hs : s i ≠ 0
  · suffices (rename Subtype.val
        ((optionEquivLeft R { b // b ≠ i }) ((rename ⇑f) p)).leadingCoeff).degreeOf i = 0 by
      have hsc : (p.initialOf i).coeff s = 0 := by
        apply notMem_support_iff.mp
        apply p.degreeOf_initialOf_self i ▸ notMem_support_of_degreeOf_lt i
        exact Nat.zero_lt_of_ne_zero hs
      rewrite [hsc]
      apply Eq.symm <| notMem_support_iff.mp ?_
      apply this ▸ notMem_support_of_degreeOf_lt i
      exact Nat.zero_lt_of_ne_zero hs
    simp [degreeOf, degrees_rename_of_injective Subtype.val_injective]
  rewrite [not_ne_iff] at hs
  rewrite [Polynomial.leadingCoeff, ← degreeOf_eq_natDegree]
  set s' : { b // b ≠ i } →₀ ℕ := (s.mapDomain f).some with hs'
  have : s'.mapDomain Subtype.val = s := by
    rewrite [hs', Finsupp.some, hsv, Finsupp.mapDomain_comp,
      Finsupp.mapDomain_comapDomain _ (Option.some_injective _)]
    · ext j
      simp [Finsupp.mapDomain_equiv_apply]
    refine Finsupp.support_subset_iff.mpr ?_
    simp only [Set.mem_range, Subtype.exists, not_exists, Finsupp.mapDomain_equiv_apply]
    intro j hj
    contrapose! hj
    refine ⟨f.symm j, by contrapose! hj; rw [hj, hs], ?_⟩
    have : f ∘ Subtype.val = @some { b // b ≠ i } := (Equiv.symm_comp_eq _ _ _).mpr hsv
    simp only [ne_eq, ← this, Function.comp_apply, Equiv.apply_symm_apply]
  rewrite [← this, coeff_rename_mapDomain _ Subtype.val_injective, this,
    optionEquivLeft_coeff_coeff, ← coeff_rename_mapDomain _ f.symm.injective]
  simp only [rename_rename, ne_eq, Equiv.symm_comp_self, rename_id, AlgHom.coe_id, id_eq]
  have (n : ℕ) : (s'.optionElim n).mapDomain f.symm = s.update i n := by
    ext j
    simp only [ne_eq, Finsupp.some, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm,
      Finsupp.optionElim_apply_eq_elim, Finsupp.update_apply, s', Option.elim]
    have : f i = none := Equiv.optionSubtypeNe_symm_self i
    split <;> expose_names
    · have : j ≠ i := fun hj ↦ by absurd heq; rewrite [hj, this]; exact not_eq_of_beq_eq_false rfl
      rw [if_neg this, Finsupp.comapDomain_apply, ← heq, Finsupp.mapDomain_apply f.injective]
    have : j = i := by apply f.injective; rw [this, heq]
    rw [if_pos this]
  exact this _ ▸ coeff_initialOf_eq_of_apply_eq_zero i p hs

theorem vars_initialOf_subset : (p.initialOf i).vars ⊆ p.vars := by
  classical
  apply subset_trans (vars_sum_subset _ _)
  simp only [Finset.biUnion_subset_iff_forall_subset, Finset.mem_filter, mem_support_iff, ne_eq]
  intro s ⟨hs, _⟩
  simp only [vars_monomial hs, Finsupp.support_erase]
  apply subset_trans (Finset.erase_subset i s.support)
  exact support_subset_vars_of_mem_support <| mem_support_iff.mpr hs

theorem initialOf_eq_of_degreeOf_eq_zero {p : MvPolynomial σ R} {i : σ} :
    p.degreeOf i = 0 → p.initialOf i = p := fun h ↦ Eq.symm (by
  nth_rewrite 1 [p.as_sum, initialOf_def, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s hs ↦ ?_)
  simp [h, Nat.eq_zero_of_le_zero <| degreeOf_le_iff.mp (le_of_eq h) s hs])

theorem degreeOf_initialOf_le : (p.initialOf i).degreeOf j ≤ p.degreeOf j := by
  refine le_trans (degreeOf_sum_le ..) <| Finset.sup_le ?_
  intro s hs
  simp only [Finset.mem_filter, mem_support_iff, ne_eq] at hs
  rewrite [degreeOf_monomial_eq _ _ hs.1, degreeOf_eq_sup]
  by_cases hi : i = j
  · rewrite [hi, Finsupp.erase_same]
    exact Nat.zero_le _
  rewrite [Finsupp.erase_ne (Ne.symm hi)]
  apply Finset.le_sup <| mem_support_iff.mpr hs.1

theorem initialOf_add_eq_of_degreeOf_lt {i : σ} {p q : MvPolynomial σ R}
    (h : q.degreeOf i < p.degreeOf i) : (p + q).initialOf i = p.initialOf i := by
  ext s
  rewrite [coeff_initialOf_eq, coeff_initialOf_eq, degreeOf_add_eq_of_degreeOf_lt h, coeff_add]
  split_ifs with hs
  · suffices q.coeff (s.update i (degreeOf i p)) = 0 by rw [this, add_zero]
    refine notMem_support_iff.mp <| notMem_support_of_degreeOf_lt i ?_
    classical simpa only [Finsupp.update_apply, reduceIte]
  rfl

theorem degreeOf_eq_of_initialOf_decomposition {i : σ} {p q r : MvPolynomial σ R} {d : ℕ}
    (q_ne : q ≠ 0) (hq : q.degreeOf i = 0) (hr : r.degreeOf i < d)
    (decomp : p = q * X i ^ d + r) : p.degreeOf i = d := by
  haveI : Nontrivial R := have ⟨s, hs⟩ := ne_zero_iff.mp q_ne; ⟨q.coeff s, 0, hs⟩
  have := degreeOf_mul_le i q (X i ^ d)
  rewrite [hq, zero_add] at this
  have := le_trans (degreeOf_add_le i (q * X i ^ d) r) (sup_le_sup_right this (r.degreeOf i))
  rewrite [← decomp, degreeOf_X_self_pow, max_eq_left_of_lt hr] at this
  apply le_antisymm this
  have d_eq := degreeOf_mul_X_self_pow_eq_add_of_ne_zero i d q_ne
  have : r.degreeOf i < (q * X i ^ d).degreeOf i :=
    d_eq ▸ (lt_of_lt_of_le hr <| Nat.le_add_left d _)
  rewrite [decomp, degreeOf_add_eq_of_degreeOf_lt this, d_eq]
  exact Nat.le_add_left d _

@[simp] theorem initialOf_initialOf_self : (p.initialOf i).initialOf i = p.initialOf i :=
  initialOf_eq_of_degreeOf_eq_zero <| degreeOf_initialOf_self ..

theorem initialOf_eq_iff_degreeOf_eq_zero {i : σ} {p : MvPolynomial σ R} :
    p.degreeOf i = 0 ↔ p.initialOf i = p :=
  ⟨initialOf_eq_of_degreeOf_eq_zero, fun h ↦ by rw [h.symm, degreeOf_initialOf_self]⟩

/-- Auxiliary decomposition lemma: `p` can be written as `initᵢ(p) * Xᵢ ^ degᵢ(p) + tail`. -/
protected lemma _initialOf_decomposition :
    let q := ∑ s ∈ p.support with s i ≠ p.degreeOf i, (monomial s) (p.coeff s)
    q.degreeOf i ≤ p.degreeOf i - 1 ∧ p = p.initialOf i * X i ^ p.degreeOf i + q := by
  classical
  set q := ∑ s ∈ p.support with s i ≠ p.degreeOf i, (monomial s) (p.coeff s) with hq
  simp only
  constructor
  · rewrite [degreeOf_eq_sup, Finset.sup_le_iff]
    intro s hs
    rewrite [hq,  mem_support_iff, coeff_sum, Finset.sum_filter] at hs
    set f := fun t ↦ if t i ≠ p.degreeOf i then (monomial t (p.coeff t)).coeff s else 0 with hf
    have hf : f = fun t ↦ if t = s then (if t i ≠ p.degreeOf i then (p.coeff t) else 0) else 0 :=
      by ext t; simp only [hf, coeff_monomial]; rewrite [← ite_and]; simp only [and_comm, ite_and]
    simp only [hf, ne_eq, Finset.sum_ite_eq', mem_support_iff, ite_eq_right_iff,
      Classical.not_imp] at hs
    have : s i ≤ p.degreeOf i := le_degreeOf_of_mem_support i <| mem_support_iff.mpr hs.1
    by_cases d_zero : p.degreeOf i = 0
    · rewrite [d_zero] at this ⊢
      exact this
    exact Nat.le_sub_one_of_lt <| lt_of_le_of_ne this hs.2.1
  rw [initialOf_def, Finset.sum_mul, hq, Finset.sum_filter, Finset.sum_filter, X_pow_eq_monomial]
  simp only [monomial_mul, mul_one, ne_eq, ite_not, ← Finset.sum_add_distrib]
  nth_rewrite 1 [as_sum p]
  refine Finset.sum_congr rfl (fun s _ ↦ ?_)
  split_ifs with hs
  · rw [← hs, Finsupp.erase_add_single, add_zero]
  rw [zero_add]

/-- The fundamental decomposition of a polynomial with respect to a variable `i`.
`p = initᵢ(p) * Xᵢ ^ degᵢ(p) + tail`, where `degᵢ(tail) < degᵢ(p)`. -/
theorem initialOf_decomposition : ∃ q, q.degreeOf i ≤ p.degreeOf i - 1 ∧
    p = p.initialOf i * X i ^ p.degreeOf i + q := ⟨_, p._initialOf_decomposition i⟩

theorem initialOf_ne_zero {p : MvPolynomial σ R} : p ≠ 0 → p.initialOf i ≠ 0 := mt fun h ↦ by
  obtain ⟨q, hq1, hq2⟩ := p.initialOf_decomposition i
  rewrite [h, zero_mul, zero_add] at hq2
  rewrite [← hq2] at hq1
  have : p.degreeOf i = 0 := by contrapose! hq1; exact Nat.sub_one_lt hq1
  exact initialOf_eq_of_degreeOf_eq_zero this ▸ h

theorem initialOf_ne_zero_of_degreeOf_ne_zero {i : σ} {p : MvPolynomial σ R} : p.degreeOf i ≠ 0 →
    p.initialOf i ≠ 0 := fun h ↦ (initialOf_ne_zero i) (ne_zero_of_degreeOf_ne_zero h)

theorem degreeOf_add_lt_of_initialOf_cancel {i : σ} {p q : MvPolynomial σ R}
    (hd : p.degreeOf i = q.degreeOf i) (hi : p.initialOf i + q.initialOf i = 0) :
    (p + q).degreeOf i ≤ p.degreeOf i - 1 := by
  obtain ⟨p', hp1, hp2⟩ := p.initialOf_decomposition i
  obtain ⟨q', hq1, hq2⟩ := q.initialOf_decomposition i
  set d := p.degreeOf i with hd'
  have : p' + q' = p + q :=
    calc p' + q' = (p.initialOf i + q.initialOf i) * X i ^ d + p' + q' := by simp [hi]
      _ = p.initialOf i * X i ^ d + p' + (q.initialOf i * X i ^ d + q') := by ring
      _ = p + q := by rw [← hp2, hd, ← hq2]
  rewrite [← this]
  exact le_trans (degreeOf_add_le i p' q') <| max_le hp1 (hd ▸ hq1)

theorem initialOf_cancel_of_degreeOf_add_lt {i : σ} {p q : MvPolynomial σ R}
    (h : (p + q).degreeOf i < p.degreeOf i) : p.initialOf i + q.initialOf i = 0 := by
  ext s
  simp only [coeff_add, coeff_initialOf_eq, coeff_zero]
  split_ifs with hs
  · have : p.degreeOf i = q.degreeOf i := by
      contrapose! h
      rcases lt_or_gt_of_ne h with h | h
      · rewrite [add_comm, degreeOf_add_eq_of_degreeOf_lt h]
        exact Nat.le_of_succ_le h
      rewrite [degreeOf_add_eq_of_degreeOf_lt h]
      rfl
    rewrite [← this, ← coeff_add]
    refine notMem_support_iff.mp <| notMem_support_of_degreeOf_lt i ?_
    classical simpa only [Finsupp.update_apply]
  rw [add_zero]

theorem initialOf_eq_of_initialOf_decomposition {i : σ} {p q r : MvPolynomial σ R} {d : ℕ}
    (q_ne : q ≠ 0) (hq : q.degreeOf i = 0) (hr : r.degreeOf i < d)
    (decomp : p = q * X i ^ d + r) : p.initialOf i = q := by
  ext s
  have d_eq : p.degreeOf i = d := degreeOf_eq_of_initialOf_decomposition q_ne hq hr decomp
  simp only [coeff_initialOf_eq, d_eq]
  split_ifs with hs
  · suffices r.coeff (s + Finsupp.single i d) = 0 by
      classical simp [decomp, X_pow_eq_monomial, coeff_mul_monomial',
        Finsupp.update_eq_add_single hs, this]
    refine notMem_support_iff.mp <| notMem_support_of_degreeOf_lt i ?_
    simpa using Nat.lt_add_left (s i) hr
  refine Eq.symm <| notMem_support_iff.mp <| notMem_support_of_degreeOf_lt i ?_
  exact hq ▸ Nat.zero_lt_of_ne_zero hs

theorem initialOf_add_of_degreeOf_eq_of_ne {p q : MvPolynomial σ R}
    (hi : p.initialOf i + q.initialOf i ≠ 0) (h : q.degreeOf i = p.degreeOf i) :
    (p + q).initialOf i = p.initialOf i + q.initialOf i := by
  by_cases pd_zero : p.degreeOf i = 0
  · have pI : p.initialOf i = p := initialOf_eq_of_degreeOf_eq_zero pd_zero
    have qI : q.initialOf i = q := initialOf_eq_of_degreeOf_eq_zero <| h ▸ pd_zero
    have := degreeOf_add_le i p q
    simp only [pd_zero, h, max_self, nonpos_iff_eq_zero] at this
    rw [initialOf_eq_of_degreeOf_eq_zero this, pI, qI]
  obtain ⟨p', hp1, hp2⟩ := p.initialOf_decomposition i
  obtain ⟨q', hq1, hq2⟩ := q.initialOf_decomposition i
  have pd_zero : 0 < p.degreeOf i := Nat.zero_lt_of_ne_zero pd_zero
  have hp1 : degreeOf i p' < degreeOf i p := Nat.lt_of_le_pred pd_zero hp1
  have hq1 : degreeOf i q' < degreeOf i p := Nat.lt_of_le_pred pd_zero (h ▸ hq1)
  have decomp : p + q = (p.initialOf i + q.initialOf i) * X i ^ p.degreeOf i + (p' + q') :=
    by nth_rewrite 1 [hp2, hq2, h]; ring
  have d_zero : (p.initialOf i + q.initialOf i).degreeOf i = 0 := by
    refine Nat.eq_zero_of_le_zero <| le_trans (degreeOf_add_le ..) ?_
    simp only [degreeOf_initialOf_self, max_self, le_refl]
  have hlt : (p' + q').degreeOf i < p.degreeOf i :=
      lt_of_le_of_lt (degreeOf_add_le ..) <| max_lt hp1 hq1
  exact initialOf_eq_of_initialOf_decomposition hi d_zero hlt decomp

variable (q) in
theorem initialOf_mul_decomposition : ∃ r, r.degreeOf i ≤ p.degreeOf i + q.degreeOf i - 1
    ∧ p * q = p.initialOf i * q.initialOf i * X i ^ (p.degreeOf i + q.degreeOf i) + r := by
  by_cases this : p.degreeOf i = 0 ∨ q.degreeOf i = 0
  · rcases this with h | h <;>
    have {p q : MvPolynomial σ R} (h : q.degreeOf i = 0) :
        ∃ r, r.degreeOf i ≤ p.degreeOf i + q.degreeOf i - 1
          ∧ p * q = p.initialOf i * q.initialOf i * X i ^ (p.degreeOf i + q.degreeOf i) + r := by
      obtain ⟨p', hp1, hp2⟩ := p.initialOf_decomposition i
      rewrite [initialOf_eq_of_degreeOf_eq_zero h]
      refine ⟨q * p', ?_, by nth_rewrite 1 [h, add_zero, hp2]; ring⟩
      refine le_trans (degreeOf_mul_le ..) ?_
      simpa [initialOf_eq_of_degreeOf_eq_zero, h] using hp1
    · rewrite [add_comm, mul_comm, mul_comm (p.initialOf i)]
      exact this h
    exact this h
  obtain ⟨p', hp1, hp2⟩ := p.initialOf_decomposition i
  obtain ⟨q', hq1, hq2⟩ := q.initialOf_decomposition i
  use q.initialOf i * X i ^ q.degreeOf i * p' + p.initialOf i * X i ^ p.degreeOf i * q' + p' * q'
  refine ⟨?_, by nth_rewrite 1 [hp2, hq2]; ring⟩
  have hp := Nat.zero_lt_of_ne_zero (not_or.mp this).1
  have hq := Nat.zero_lt_of_ne_zero (not_or.mp this).2
  have : (p' * q').degreeOf i ≤ p.degreeOf i + q.degreeOf i - 1 := by
    refine le_trans (degreeOf_mul_le i p' q') <| le_trans (add_le_add hp1 hq1) ?_
    simp [Nat.add_sub_assoc hq _]
  refine le_trans (degreeOf_add_le ..) (max_le ?_ this)
  refine le_trans (degreeOf_add_le ..) (max_le ?_ ?_)
  <;> refine le_trans (degreeOf_mul_le i ..) ?_
  · rewrite [add_comm (p.degreeOf i), Nat.add_sub_assoc hp _, Nat.succ_eq_add_one, zero_add]
    apply add_le_add ?_ hp1
    have : q.initialOf i ≠ 0 := initialOf_ne_zero_of_degreeOf_ne_zero <| Nat.ne_zero_of_lt hq
    rw [degreeOf_mul_X_self_pow_eq_add_of_ne_zero _ _ this, degreeOf_initialOf_self, zero_add]
  rewrite [Nat.add_sub_assoc hq _, Nat.succ_eq_add_one, zero_add]
  apply add_le_add ?_ hq1
  have : p.initialOf i ≠ 0 := initialOf_ne_zero_of_degreeOf_ne_zero <| Nat.ne_zero_of_lt hp
  rw [degreeOf_mul_X_self_pow_eq_add_of_ne_zero _ _ this, degreeOf_initialOf_self, zero_add]

end InitialOf

section Initial

variable [DecidableEq R] [LinearOrder σ] {p : MvPolynomial σ R}

/-- The "Initial" of a polynomial `p` is `p.initialOf p.max_vars` if `p` is not a constant,
and 1 if `p` is a non-zero constant. -/
noncomputable def initial (p : MvPolynomial σ R) : MvPolynomial σ R :=
  if p = 0 then 0 else
    match p.vars.max with
    | ⊥ => 1
    | some c => p.initialOf c

@[simp] theorem initial_zero : (0 : MvPolynomial σ R).initial = 0 := by
  simp only [initial, reduceIte]

theorem initial_ne_zero [Nontrivial R] {p : MvPolynomial σ R} : p ≠ 0 → p.initial ≠ 0 := fun h ↦ by
  simp only [initial, h, ↓reduceIte, ne_eq]
  match p.vars.max with
  | none => simp only [one_ne_zero, not_false_eq_true]
  | some c => simp only [initialOf_ne_zero c h, not_false_eq_true]

theorem initial_of_max_vars_eq_bot (hp : p ≠ 0) : p.vars.max = ⊥ → initial p = 1 :=
  fun h ↦ by simp only [initial, hp, reduceIte, h]

theorem initial_of_max_vars_isSome' {c : σ} :
    p.vars.max = c → initial p = p.initialOf c := fun h ↦ by
  have : p.vars.max ≠ ⊥ := WithBot.ne_bot_iff_exists.mpr <| Exists.intro c h.symm
  have : p ≠ 0 := fun h ↦ absurd this (by simp [h])
  simp only [initial, this, ↓reduceIte, h]

theorem initial_of_max_vars_isSome {c : σ} : p.vars.max = c →
    initial p = ∑ s ∈ p.support with s c = p.degreeOf c, monomial (s.erase c) (p.coeff s) :=
  fun h ↦ by rw [initial_of_max_vars_isSome' h, initialOf_def]

@[simp] theorem initial_C {r : R} (hr : r ≠ 0) : (C r : MvPolynomial σ R).initial = 1 :=
  initial_of_max_vars_eq_bot (C_ne_zero.mpr hr) (congrArg _ vars_C)

theorem initial_monomial {s : σ →₀ ℕ} (r : R) {c : σ} :
    s.support.max = c → (monomial s r).initial = monomial (s.erase c) r := fun hs ↦ by
  by_cases r_zero : r = 0
  · simp only [r_zero, initial, monomial_zero, reduceIte]
  have : (monomial s r).vars.max = c := hs ▸ congrArg _ (vars_monomial r_zero)
  rw [initial_of_max_vars_isSome' this, initialOf_monomial]

@[simp] theorem initial_X_pow (i : σ) {k : ℕ} (hk : k ≠ 0) :
    (X i ^ k).initial = (1 : MvPolynomial σ R) := by
  have : (Finsupp.single i k).support.max = i := by
    rewrite [Finsupp.support_single_ne_zero _ hk]; exact rfl
  rw [X_pow_eq_monomial, initial_monomial 1 this, Finsupp.erase_single, monomial_zero', C_1]

@[simp] theorem initial_X (i : σ) : (X i : MvPolynomial σ R).initial = 1 :=
  pow_one (X i : MvPolynomial σ R) ▸ initial_X_pow i one_ne_zero

theorem max_vars_initial_lt (hp : p.vars.max ≠ ⊥) :
    (initial p).vars.max < p.vars.max := by
  by_contra con
  have ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.mp hp
  absurd p.degreeOf_initialOf_self c
  rewrite [initial_of_max_vars_isSome' hc.symm] at con
  have con : (p.initialOf c).vars.max = p.vars.max :=
    eq_of_le_of_not_lt (Finset.max_mono <| vars_initialOf_subset c p) con
  have con := Finset.mem_of_max (hc ▸ con)
  simpa only [degreeOf, Multiset.count_ne_zero, vars_def, Multiset.mem_toFinset] using con

variable (p) (i) in
theorem degreeOf_initial_le : p.initial.degreeOf i ≤ p.degreeOf i := by
  by_cases hp : p = 0
  · simp only [hp, initial_zero, degreeOf_zero, le_refl]
  by_cases hc : p.vars.max = ⊥
  · simp only [initial_of_max_vars_eq_bot hp hc, degreeOf_one, zero_le]
  have ⟨c, hc⟩ :=  WithBot.ne_bot_iff_exists.mp hc
  exact initial_of_max_vars_isSome' hc.symm ▸ p.degreeOf_initialOf_le c i

/-- The product of initials of a set of polynomials. -/
noncomputable def initialProd (PS : Finset (MvPolynomial σ R)) : MvPolynomial σ R :=
  ∏ p ∈ PS, p.initial

theorem initialProd_def (PS : Finset (MvPolynomial σ R)) : initialProd PS = ∏ p ∈ PS, p.initial :=
  rfl

end Initial

section NoZeroDivisors

variable [NoZeroDivisors R] (i : σ) (p : MvPolynomial σ R)

@[simp] theorem initialOf_mul_eq (q : MvPolynomial σ R) :
    (p * q).initialOf i = p.initialOf i * q.initialOf i := by
  classical simp [initialOf_eq_leadingCoeff]

@[simp] theorem initialOf_smul {r : R} : (r • p).initialOf i = r • p.initialOf i := by
  rw [smul_eq_C_mul, smul_eq_C_mul, initialOf_mul_eq, initialOf_C]

@[simp] theorem initialOf_pow_eq (n : ℕ) : (p ^ n).initialOf i = p.initialOf i ^ n := by
  induction n with
  | zero => simp only [pow_zero, initialOf_one]
  | succ n ih => rw [pow_add, pow_add, pow_one, pow_one, initialOf_mul_eq, ih]

end NoZeroDivisors

section CommRing

variable {R σ : Type*} [CommRing R] {p q : MvPolynomial σ R}

@[simp] theorem initialOf_neg (i : σ) : (-p).initialOf i = -p.initialOf i :=
  by classical simp [initialOf_eq_leadingCoeff]

theorem degreeOf_sub_lt_of_initialOf_eq {i : σ} (hi : p.initialOf i = q.initialOf i)
    (hd : p.degreeOf i = q.degreeOf i) : (p - q).degreeOf i ≤ p.degreeOf i - 1 :=
  have hi : p.initialOf i + (-q).initialOf i = 0 := by rw [initialOf_neg i, hi, add_neg_cancel]
  have hd : p.degreeOf i = (-q).degreeOf i := by rw [degreeOf_neg, hd]
  sub_eq_add_neg p q ▸ degreeOf_add_lt_of_initialOf_cancel hd hi

theorem initialOf_eq_of_degreeOf_sub_lt {i : σ} {p q : MvPolynomial σ R}
    (h : (p - q).degreeOf i < p.degreeOf i) : p.initialOf i = q.initialOf i := by
  have : (p + (-q)).degreeOf i < p.degreeOf i := by rw [← sub_eq_add_neg]; exact h
  rw [← add_zero (p.initialOf i), ← add_neg_cancel ((-q).initialOf i), ← add_assoc,
    initialOf_cancel_of_degreeOf_add_lt this, zero_add, initialOf_neg, neg_neg]

end CommRing

end MvPolynomial
