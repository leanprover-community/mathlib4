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
  This is the coefficient polynomial of `X i ^ degᵢ(p)`.
* `MvPolynomial.eraseInitOf i p`:
  the sum of all terms in `p` whose degree in `i` is *not* equal to `p.degreeOf i`.
* `MvPolynomial.initial`:
  The initial of `p` with respect to its main variable.
  For constants, this is defined as `1`.

## Main results

* `initialOf_eq_leadingCoeff`:
  `initᵢ(p)` is the leading coefficient when viewing `p` as a univariate polynomial in `X i`.
* `initialOf_mul_X_pow_add_eraseInitOf`:
  The fundamental decomposition about the initial of a polynomial with respect to a variable `i`.
  `p = initᵢ(p) * Xᵢ ^ degᵢ(p) + eraseInitᵢ`.
* `initial_reducedTo`: The initial is always reduced w.r.t. the original polynomial
* `initialOf_mul`: `initᵢ(p * q) = initᵢ(p) * initᵢ(q)` (for integral domains)

## References
* [Wen-Tsun Wu, *Basic principles of mechanical theorem proving in elementary geometries*]
  [wen1986basic]

-/

public section

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R]

section InitialOf

variable (i j : σ) (p : MvPolynomial σ R)

/-- The "initial" of a polynomial `p` with respect to a variable `i`.
It is the coefficient of the highest power of `X i` appearing in `p`.
More formally, it is the sum of terms in `p` whose degree in `i` equals `p.degreeOf i`,
but with the variable `i` erased. -/
noncomputable def initialOf : MvPolynomial σ R :=
  ∑ s ∈ p.support with s i = p.degreeOf i, monomial (s.erase i) (p.coeff s)

theorem initialOf_def {p : MvPolynomial σ R} {i : σ} :
    p.initialOf i = ∑ s ∈ p.support with s i = p.degreeOf i, monomial (s.erase i) (p.coeff s) :=
  Eq.refl _

@[simp] theorem initialOf_zero : (0 : MvPolynomial σ R).initialOf i = 0 := Eq.refl _

@[simp] theorem initialOf_monomial (s : σ →₀ ℕ) (r : R) :
    (monomial s r).initialOf i = monomial (s.erase i) r := by
  by_cases r_zero : r = 0
  · simp only [r_zero, monomial_zero, initialOf_zero]
  rw [initialOf_def, Finset.sum_filter, ← single_eq_monomial, degreeOf_eq_sup, support]
  rw [Finsupp.support_single s r_zero, Finset.sum_singleton, Finset.sup_singleton]
  rw [if_pos rfl, coeff, Finsupp.single_eq_same]

@[simp] theorem initialOf_C (r : R) : (C r : MvPolynomial σ R).initialOf i = C r := by
  rw [C_apply, initialOf_monomial, Finsupp.erase_zero]

@[simp] theorem initialOf_one : (1 : MvPolynomial σ R).initialOf i = 1 := by
  rw [← C_1, initialOf_C]

@[simp] theorem initialOf_mul_X_self : (p * X i).initialOf i = p.initialOf i := by
  by_cases p_zero : p = 0
  · rw [p_zero, zero_mul, initialOf_zero]
  rw [initialOf_def, (degreeOf_mul_X_eq_degreeOf_add_one_iff i p).mpr p_zero]
  simp [Finset.sum_filter, initialOf_def]

theorem initialOf_mul_X_of_ne {i j : σ} (h : i ≠ j) :
    (p * X j).initialOf i = p.initialOf i * X j := by
  rw [initialOf_def, degreeOf_mul_X_of_ne _ h]
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

@[simp] theorem initialOf_X_self : (X i).initialOf i = (1 : MvPolynomial σ R) := by
  rw [← one_mul (X i), initialOf_mul_X_self, initialOf_one]

@[simp] theorem initialOf_X_self_pow (k : ℕ) : (X i ^ k).initialOf i = (1 : MvPolynomial σ R) := by
  rw [← one_mul (X i ^ k), initialOf_mul_X_self_pow, initialOf_one]

theorem initialOf_X_of_ne {i j : σ} (h : i ≠ j) : (X j).initialOf i = (X j : MvPolynomial σ R) := by
  rw [← one_mul (X j), initialOf_mul_X_of_ne _ h, initialOf_one]

theorem initialOf_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    (X j ^ k).initialOf i = (X j : MvPolynomial σ R) ^ k := by
  rw [← one_mul (X j ^ k), initialOf_mul_X_pow_of_ne _ _ h, initialOf_one]

theorem coeff_initialOf_eq_of_apply_ne_zero {s : σ →₀ ℕ} (h : s i ≠ 0) :
    (p.initialOf i).coeff s = 0 := by
  classical
  rw [initialOf, coeff_sum, Finset.sum_congr rfl fun _ _ ↦ coeff_monomial s _ _]
  have (x : σ →₀ ℕ) : x.erase i = s ↔ False := by
    refine iff_false_intro <| Finsupp.ne_iff.mpr ⟨i, ?_⟩
    rw [Finsupp.erase_apply, if_pos rfl]
    exact h.symm
  simp only [this, ↓reduceIte, Finset.sum_const_zero]

theorem coeff_initialOf_eq_of_apply_eq_zero {s : σ →₀ ℕ} (h : s i = 0) :
    (p.initialOf i).coeff s = p.coeff (s.update i (p.degreeOf i)) := by
  classical
  rw [initialOf, coeff_sum, Finset.sum_congr rfl fun _ _ ↦ coeff_monomial s _ _]
  have (x : σ →₀ ℕ) : x i = p.degreeOf i ∧ x.erase i = s ↔ x = s.update i (p.degreeOf i) := by
    refine ⟨fun hx ↦ Finsupp.ext fun j ↦ ?_, fun hx ↦ ?_⟩
    · rw [Finsupp.update_apply]
      split_ifs with hj
      · rw [hj, hx.1]
      rw [← hx.2, Finsupp.erase_apply, if_neg hj]
    simp only [hx, Finsupp.update_apply, reduceIte, Finsupp.erase_update_eq_erase, true_and]
    refine Finsupp.erase_of_notMem_support ?_
    exact Finsupp.notMem_support_iff.mpr h
  simpa [Finset.sum_filter, ← ite_and, this] using Eq.symm

theorem coeff_initialOf_eq (s : σ →₀ ℕ) :
    (p.initialOf i).coeff s = if s i = 0 then p.coeff (s.update i (p.degreeOf i)) else 0 := by
  split_ifs with hs
  · exact coeff_initialOf_eq_of_apply_eq_zero i p hs
  exact coeff_initialOf_eq_of_apply_ne_zero i p hs

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
      have hc {q : MvPolynomial σ R} (h : q.degreeOf i = 0) : q.coeff s = 0 := by
        rw [← notMem_support_iff]
        apply notMem_support_of_degreeOf_lt i
        rw [h]
        exact Nat.zero_lt_of_ne_zero hs
      rw [hc this, hc (p.degreeOf_initialOf_self i)]
    simp [degreeOf, degrees_rename_of_injective Subtype.val_injective]
  rw [not_ne_iff] at hs
  rw [Polynomial.leadingCoeff, ← degreeOf_eq_natDegree]
  set s' : { b // b ≠ i } →₀ ℕ := (s.mapDomain f).some with hs'
  have : s'.mapDomain Subtype.val = s := by
    rw [hs', Finsupp.some, hsv, Finsupp.mapDomain_comp,
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
  rw [← this, coeff_rename_mapDomain _ Subtype.val_injective, this,
    optionEquivLeft_coeff_coeff, ← coeff_rename_mapDomain _ f.symm.injective]
  simp only [rename_rename, ne_eq, Equiv.symm_comp_self, rename_id, AlgHom.coe_id, id_eq]
  suffices ∀ (n : ℕ), (s'.optionElim n).mapDomain f.symm = s.update i n by
    rw [this, coeff_initialOf_eq_of_apply_eq_zero i p hs]
  intro n
  ext j
  simp only [ne_eq, Finsupp.some, Finsupp.mapDomain_equiv_apply, Equiv.symm_symm,
    Finsupp.optionElim_apply_eq_elim, Finsupp.update_apply, s', Option.elim]
  have : f i = none := Equiv.optionSubtypeNe_symm_self i
  split <;> expose_names
  · have : j ≠ i := fun hj ↦ by
      absurd heq
      rw [hj, this]
      exact ne_of_beq_false rfl
    rw [if_neg this, Finsupp.comapDomain_apply, ← heq, Finsupp.mapDomain_apply f.injective]
  rw [if_pos]
  apply f.injective
  rw [this, heq]

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
  nth_rw 1 [p.as_sum, initialOf_def, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun s hs ↦ ?_)
  simp [h, Nat.eq_zero_of_le_zero <| degreeOf_le_iff.mp (le_of_eq h) s hs])

theorem degreeOf_initialOf_le : (p.initialOf i).degreeOf j ≤ p.degreeOf j := by
  refine le_trans (degreeOf_sum_le ..) <| Finset.sup_le ?_
  intro s hs
  simp only [Finset.mem_filter, mem_support_iff, ne_eq] at hs
  rw [degreeOf_monomial_eq _ _ hs.1, degreeOf_eq_sup]
  by_cases hi : i = j
  · rw [hi, Finsupp.erase_same]
    exact Nat.zero_le _
  rw [Finsupp.erase_ne (Ne.symm hi)]
  apply Finset.le_sup <| mem_support_iff.mpr hs.1

theorem initialOf_add_eq_of_degreeOf_lt {i : σ} {p q : MvPolynomial σ R}
    (h : q.degreeOf i < p.degreeOf i) : (p + q).initialOf i = p.initialOf i := by
  ext s
  rw [coeff_initialOf_eq, coeff_initialOf_eq, degreeOf_add_eq_of_degreeOf_lt h, coeff_add]
  split_ifs with hs
  · suffices q.coeff (s.update i (degreeOf i p)) = 0 by rw [this, add_zero]
    refine notMem_support_iff.mp <| notMem_support_of_degreeOf_lt i ?_
    classical simpa only [Finsupp.update_apply, reduceIte]
  rfl

theorem degreeOf_eq_of_initialOf_decomposition {i : σ} {p q r : MvPolynomial σ R} {d : ℕ}
    (q_ne : q ≠ 0) (hq : q.degreeOf i = 0) (hr : r.degreeOf i < d)
    (decomp : p = q * X i ^ d + r) : p.degreeOf i = d := by
  apply le_antisymm
  · haveI : Nontrivial R := have ⟨s, hs⟩ := ne_zero_iff.mp q_ne; ⟨q.coeff s, 0, hs⟩
    rw [← max_eq_left_of_lt hr, decomp]
    apply le_trans (degreeOf_add_le ..) (sup_le_sup_right ?_ _)
    apply le_trans (degreeOf_mul_le ..)
    rw [hq, zero_add, degreeOf_X_self_pow]
  have d_eq := degreeOf_mul_X_self_pow_eq_add_of_ne_zero i d q_ne
  rw [decomp, degreeOf_add_eq_of_degreeOf_lt (by grind), d_eq]
  exact Nat.le_add_left d _

@[simp] theorem initialOf_initialOf_self : (p.initialOf i).initialOf i = p.initialOf i :=
  initialOf_eq_of_degreeOf_eq_zero <| degreeOf_initialOf_self ..

theorem initialOf_eq_iff_degreeOf_eq_zero {i : σ} {p : MvPolynomial σ R} :
    p.degreeOf i = 0 ↔ p.initialOf i = p :=
  ⟨initialOf_eq_of_degreeOf_eq_zero, fun h ↦ by rw [h.symm, degreeOf_initialOf_self]⟩

/-- `eraseInitOf i p` for a polynomial `p` is the sum of all terms in `p`
whose degree in `i` is *not* equal to `p.degreeOf i`. -/
noncomputable def eraseInitOf : MvPolynomial σ R :=
  ∑ s ∈ p.support with s i ≠ p.degreeOf i, (monomial s) (p.coeff s)

theorem eraseInitOf_def :
    p.eraseInitOf i = ∑ s ∈ p.support with s i ≠ p.degreeOf i, (monomial s) (p.coeff s) :=
  Eq.refl _

theorem degreeOf_eraseInitOf_lt : (p.eraseInitOf i).degreeOf i ≤ p.degreeOf i - 1 := by
  set q := p.eraseInitOf i
  have hq : q = ∑ s ∈ p.support with s i ≠ p.degreeOf i, (monomial s) (p.coeff s) := rfl
  rw [degreeOf_eq_sup, Finset.sup_le_iff]
  intro s hs
  rw [hq,  mem_support_iff, coeff_sum, Finset.sum_filter] at hs
  set f := fun t ↦ if t i ≠ p.degreeOf i then (monomial t (p.coeff t)).coeff s else 0 with hf
  classical
  have hf : f = fun t ↦ if t = s then (if t i ≠ p.degreeOf i then (p.coeff t) else 0) else 0 := by
    aesop
  simp only [hf, ne_eq, Finset.sum_ite_eq', mem_support_iff, ite_eq_right_iff,
    Classical.not_imp] at hs
  have : s i ≤ p.degreeOf i := le_degreeOf_of_mem_support i <| mem_support_iff.mpr hs.1
  grind

/-- The fundamental decomposition about the initial of a polynomial with respect to a variable `i`.
`p = initᵢ(p) * Xᵢ ^ degᵢ(p) + eraseInitᵢ`. -/
theorem initialOf_mul_X_pow_add_eraseInitOf :
    p = p.initialOf i * X i ^ p.degreeOf i + p.eraseInitOf i := by
  rw [initialOf_def, Finset.sum_mul, eraseInitOf, Finset.sum_filter, Finset.sum_filter,
    X_pow_eq_monomial]
  simp only [monomial_mul, mul_one, ne_eq, ite_not, ← Finset.sum_add_distrib]
  nth_rw 1 [as_sum p]
  refine Finset.sum_congr rfl (fun s _ ↦ ?_)
  split_ifs with hs
  · rw [← hs, Finsupp.erase_add_single, add_zero]
  rw [zero_add]

theorem initialOf_ne_zero {p : MvPolynomial σ R} : p ≠ 0 → p.initialOf i ≠ 0 := mt fun h ↦ by
  rw [← h, initialOf_eq_of_degreeOf_eq_zero]
  have hq1 := p.degreeOf_eraseInitOf_lt i
  have hq2 := p.initialOf_mul_X_pow_add_eraseInitOf i
  rw [h, zero_mul, zero_add] at hq2
  rw [← hq2] at hq1
  contrapose! hq1
  exact Nat.sub_one_lt hq1

theorem initialOf_ne_zero_of_degreeOf_ne_zero {i : σ} {p : MvPolynomial σ R}
    (h : p.degreeOf i ≠ 0) : p.initialOf i ≠ 0 :=
  initialOf_ne_zero i (ne_zero_of_degreeOf_ne_zero h)

theorem degreeOf_add_lt_of_initialOf_cancel {i : σ} {p q : MvPolynomial σ R}
    (hd : p.degreeOf i = q.degreeOf i) (hi : p.initialOf i + q.initialOf i = 0) :
    (p + q).degreeOf i ≤ p.degreeOf i - 1 := by
  have hp1 := p.degreeOf_eraseInitOf_lt i
  have hp2 := p.initialOf_mul_X_pow_add_eraseInitOf i
  have hq1 := q.degreeOf_eraseInitOf_lt i
  have hq2 := q.initialOf_mul_X_pow_add_eraseInitOf i
  set p' := p.eraseInitOf i
  set q' := q.eraseInitOf i
  set d := p.degreeOf i
  have : p' + q' = p + q :=
    calc p' + q' = (p.initialOf i + q.initialOf i) * X i ^ d + p' + q' := by simp [hi]
      _ = p.initialOf i * X i ^ d + p' + (q.initialOf i * X i ^ d + q') := by ring
      _ = p + q := by rw [← hp2, hd, ← hq2]
  rw [← this]
  apply le_trans (degreeOf_add_le ..)
  rw [← hd] at hq1
  exact max_le hp1 hq1

theorem initialOf_cancel_of_degreeOf_add_lt {i : σ} {p q : MvPolynomial σ R}
    (h : (p + q).degreeOf i < p.degreeOf i) : p.initialOf i + q.initialOf i = 0 := by
  ext s
  simp only [coeff_add, coeff_initialOf_eq, coeff_zero]
  split_ifs with hs
  · have : p.degreeOf i = q.degreeOf i := by
      contrapose! h
      rcases lt_or_gt_of_ne h with h | h
      · rw [add_comm, degreeOf_add_eq_of_degreeOf_lt h]
        exact Nat.le_of_succ_le h
      rw [degreeOf_add_eq_of_degreeOf_lt h]
    rw [← this, ← coeff_add]
    refine notMem_support_iff.mp <| notMem_support_of_degreeOf_lt i ?_
    classical simpa only [Finsupp.update_apply]
  rw [add_zero]

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
  rw [initial_of_max_vars_isSome' ?_, initialOf_monomial]
  rw [← hs, vars_monomial r_zero]

@[simp] theorem initial_X_pow (i : σ) {k : ℕ} (hk : k ≠ 0) :
    (X i ^ k).initial = (1 : MvPolynomial σ R) := by
  have : (Finsupp.single i k).support.max = i := by
    rw [Finsupp.support_single _ hk]; exact rfl
  rw [X_pow_eq_monomial, initial_monomial 1 this, Finsupp.erase_single, monomial_zero', C_1]

@[simp] theorem initial_X (i : σ) : (X i : MvPolynomial σ R).initial = 1 := by
  rw [← pow_one (X i : MvPolynomial σ R), initial_X_pow i one_ne_zero]

theorem max_vars_initial_lt (hp : p.vars.max ≠ ⊥) :
    (initial p).vars.max < p.vars.max := by
  by_contra con
  have ⟨c, hc⟩ := WithBot.ne_bot_iff_exists.mp hp
  absurd p.degreeOf_initialOf_self c
  suffices c ∈ (p.initialOf c).vars by
    simpa only [degreeOf, Multiset.count_ne_zero, vars_def, Multiset.mem_toFinset] using this
  apply Finset.mem_of_max
  rw [hc]
  apply eq_of_le_of_not_lt (Finset.max_mono <| vars_initialOf_subset c p)
  rw [← initial_of_max_vars_isSome' hc.symm]
  exact con

variable (p) (i) in
theorem degreeOf_initial_le : p.initial.degreeOf i ≤ p.degreeOf i := by
  by_cases hp : p = 0
  · simp only [hp, initial_zero, degreeOf_zero, le_refl]
  by_cases hc : p.vars.max = ⊥
  · simp only [initial_of_max_vars_eq_bot hp hc, degreeOf_one, zero_le]
  have ⟨c, hc⟩ :=  WithBot.ne_bot_iff_exists.mp hc
  rw [initial_of_max_vars_isSome' hc.symm]
  exact p.degreeOf_initialOf_le c i

variable (PS : Finset (MvPolynomial σ R))

/-- The product of initials of a set of polynomials. -/
noncomputable def initialProd : MvPolynomial σ R := ∏ p ∈ PS, p.initial

theorem initialProd_def : initialProd PS = ∏ p ∈ PS, p.initial := Eq.refl _

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

@[simp] theorem initialOf_neg (i : σ) : (-p).initialOf i = -p.initialOf i := by
  classical simp [initialOf_eq_leadingCoeff]

theorem degreeOf_sub_lt_of_initialOf_eq {i : σ} (hi : p.initialOf i = q.initialOf i)
    (hd : p.degreeOf i = q.degreeOf i) : (p - q).degreeOf i ≤ p.degreeOf i - 1 := by
  have hi : p.initialOf i + (-q).initialOf i = 0 := by rw [initialOf_neg i, hi, add_neg_cancel]
  have hd : p.degreeOf i = (-q).degreeOf i := by rw [degreeOf_neg, hd]
  rw [sub_eq_add_neg p q]
  exact degreeOf_add_lt_of_initialOf_cancel hd hi

theorem initialOf_eq_of_degreeOf_sub_lt {i : σ} {p q : MvPolynomial σ R}
    (h : (p - q).degreeOf i < p.degreeOf i) : p.initialOf i = q.initialOf i := by
  have : (p + (-q)).degreeOf i < p.degreeOf i := by rw [← sub_eq_add_neg]; exact h
  rw [← add_zero (p.initialOf i), ← add_neg_cancel ((-q).initialOf i), ← add_assoc,
    initialOf_cancel_of_degreeOf_add_lt this, zero_add, initialOf_neg, neg_neg]

end CommRing

end MvPolynomial
