/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa

! This file was ported from Lean 3 source module data.polynomial.erase_lead
! leanprover-community/mathlib commit fa256f00ce018e7b40e1dc756e403c86680bf448
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Fin
import Mathbin.Data.Polynomial.Degree.Definitions

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `erase_lead f`: the polynomial `f - leading term of f`

`erase_lead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/


noncomputable section

open Classical Polynomial

open Polynomial Finset

namespace Polynomial

variable {R : Type _} [Semiring R] {f : R[X]}

/-- `erase_lead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f
#align polynomial.erase_lead Polynomial.eraseLead

section EraseLead

theorem eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.eraseₓ f.natDegree := by
  simp only [erase_lead, support_erase]
#align polynomial.erase_lead_support Polynomial.eraseLead_support

theorem eraseLead_coeff (i : ℕ) : f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i :=
  by simp only [erase_lead, coeff_erase]
#align polynomial.erase_lead_coeff Polynomial.eraseLead_coeff

@[simp]
theorem eraseLead_coeff_natDegree : f.eraseLead.coeff f.natDegree = 0 := by simp [erase_lead_coeff]
#align polynomial.erase_lead_coeff_nat_degree Polynomial.eraseLead_coeff_natDegree

theorem eraseLead_coeff_of_ne (i : ℕ) (hi : i ≠ f.natDegree) : f.eraseLead.coeff i = f.coeff i := by
  simp [erase_lead_coeff, hi]
#align polynomial.erase_lead_coeff_of_ne Polynomial.eraseLead_coeff_of_ne

@[simp]
theorem eraseLead_zero : eraseLead (0 : R[X]) = 0 := by simp only [erase_lead, erase_zero]
#align polynomial.erase_lead_zero Polynomial.eraseLead_zero

@[simp]
theorem eraseLead_add_monomial_natDegree_leadingCoeff (f : R[X]) :
    f.eraseLead + monomial f.natDegree f.leadingCoeff = f :=
  (add_comm _ _).trans (f.monomial_add_erase _)
#align polynomial.erase_lead_add_monomial_nat_degree_leading_coeff Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff

@[simp]
theorem eraseLead_add_c_mul_x_pow (f : R[X]) :
    f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f := by
  rw [C_mul_X_pow_eq_monomial, erase_lead_add_monomial_nat_degree_leading_coeff]
#align polynomial.erase_lead_add_C_mul_X_pow Polynomial.eraseLead_add_c_mul_x_pow

@[simp]
theorem self_sub_monomial_natDegree_leadingCoeff {R : Type _} [Ring R] (f : R[X]) :
    f - monomial f.natDegree f.leadingCoeff = f.eraseLead :=
  (eq_sub_iff_add_eq.mpr (eraseLead_add_monomial_natDegree_leadingCoeff f)).symm
#align polynomial.self_sub_monomial_nat_degree_leading_coeff Polynomial.self_sub_monomial_natDegree_leadingCoeff

@[simp]
theorem self_sub_c_mul_x_pow {R : Type _} [Ring R] (f : R[X]) :
    f - C f.leadingCoeff * X ^ f.natDegree = f.eraseLead := by
  rw [C_mul_X_pow_eq_monomial, self_sub_monomial_nat_degree_leading_coeff]
#align polynomial.self_sub_C_mul_X_pow Polynomial.self_sub_c_mul_x_pow

theorem eraseLead_ne_zero (f0 : 2 ≤ f.support.card) : eraseLead f ≠ 0 :=
  by
  rw [Ne, ← card_support_eq_zero, erase_lead_support]
  exact
    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).Ne.symm
#align polynomial.erase_lead_ne_zero Polynomial.eraseLead_ne_zero

theorem lt_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a < f.natDegree := by
  rw [erase_lead_support, mem_erase] at h
  exact (le_nat_degree_of_mem_supp a h.2).lt_of_ne h.1
#align polynomial.lt_nat_degree_of_mem_erase_lead_support Polynomial.lt_natDegree_of_mem_eraseLead_support

theorem ne_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a ≠ f.natDegree :=
  (lt_natDegree_of_mem_eraseLead_support h).Ne
#align polynomial.ne_nat_degree_of_mem_erase_lead_support Polynomial.ne_natDegree_of_mem_eraseLead_support

theorem natDegree_not_mem_eraseLead_support : f.natDegree ∉ (eraseLead f).support := fun h =>
  ne_natDegree_of_mem_eraseLead_support h rfl
#align polynomial.nat_degree_not_mem_erase_lead_support Polynomial.natDegree_not_mem_eraseLead_support

theorem eraseLead_support_card_lt (h : f ≠ 0) : (eraseLead f).support.card < f.support.card :=
  by
  rw [erase_lead_support]
  exact card_lt_card (erase_ssubset <| nat_degree_mem_support_of_nonzero h)
#align polynomial.erase_lead_support_card_lt Polynomial.eraseLead_support_card_lt

theorem eraseLead_card_support {c : ℕ} (fc : f.support.card = c) :
    f.eraseLead.support.card = c - 1 := by
  by_cases f0 : f = 0
  · rw [← fc, f0, erase_lead_zero, support_zero, card_empty]
  · rw [erase_lead_support, card_erase_of_mem (nat_degree_mem_support_of_nonzero f0), fc]
#align polynomial.erase_lead_card_support Polynomial.eraseLead_card_support

theorem eraseLead_card_support' {c : ℕ} (fc : f.support.card = c + 1) :
    f.eraseLead.support.card = c :=
  eraseLead_card_support fc
#align polynomial.erase_lead_card_support' Polynomial.eraseLead_card_support'

@[simp]
theorem eraseLead_monomial (i : ℕ) (r : R) : eraseLead (monomial i r) = 0 :=
  by
  by_cases hr : r = 0
  · subst r
    simp only [monomial_zero_right, erase_lead_zero]
  · rw [erase_lead, nat_degree_monomial, if_neg hr, erase_monomial]
#align polynomial.erase_lead_monomial Polynomial.eraseLead_monomial

@[simp]
theorem eraseLead_c (r : R) : eraseLead (C r) = 0 :=
  eraseLead_monomial _ _
#align polynomial.erase_lead_C Polynomial.eraseLead_c

@[simp]
theorem eraseLead_x : eraseLead (X : R[X]) = 0 :=
  eraseLead_monomial _ _
#align polynomial.erase_lead_X Polynomial.eraseLead_x

@[simp]
theorem eraseLead_x_pow (n : ℕ) : eraseLead (X ^ n : R[X]) = 0 := by
  rw [X_pow_eq_monomial, erase_lead_monomial]
#align polynomial.erase_lead_X_pow Polynomial.eraseLead_x_pow

@[simp]
theorem eraseLead_c_mul_x_pow (r : R) (n : ℕ) : eraseLead (C r * X ^ n) = 0 := by
  rw [C_mul_X_pow_eq_monomial, erase_lead_monomial]
#align polynomial.erase_lead_C_mul_X_pow Polynomial.eraseLead_c_mul_x_pow

theorem eraseLead_add_of_natDegree_lt_left {p q : R[X]} (pq : q.natDegree < p.natDegree) :
    (p + q).eraseLead = p.eraseLead + q := by
  ext n
  by_cases nd : n = p.nat_degree
  · rw [nd, erase_lead_coeff, if_pos (nat_degree_add_eq_left_of_nat_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_nat_degree_lt pq).symm
  · rw [erase_lead_coeff, coeff_add, coeff_add, erase_lead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (nat_degree_add_eq_left_of_nat_degree_lt pq)
#align polynomial.erase_lead_add_of_nat_degree_lt_left Polynomial.eraseLead_add_of_natDegree_lt_left

theorem eraseLead_add_of_natDegree_lt_right {p q : R[X]} (pq : p.natDegree < q.natDegree) :
    (p + q).eraseLead = p + q.eraseLead := by
  ext n
  by_cases nd : n = q.nat_degree
  · rw [nd, erase_lead_coeff, if_pos (nat_degree_add_eq_right_of_nat_degree_lt pq).symm]
    simpa using (coeff_eq_zero_of_nat_degree_lt pq).symm
  · rw [erase_lead_coeff, coeff_add, coeff_add, erase_lead_coeff, if_neg, if_neg nd]
    rintro rfl
    exact nd (nat_degree_add_eq_right_of_nat_degree_lt pq)
#align polynomial.erase_lead_add_of_nat_degree_lt_right Polynomial.eraseLead_add_of_natDegree_lt_right

theorem eraseLead_degree_le : (eraseLead f).degree ≤ f.degree :=
  f.degree_erase_le _
#align polynomial.erase_lead_degree_le Polynomial.eraseLead_degree_le

theorem eraseLead_natDegree_le_aux : (eraseLead f).natDegree ≤ f.natDegree :=
  natDegree_le_natDegree eraseLead_degree_le
#align polynomial.erase_lead_nat_degree_le_aux Polynomial.eraseLead_natDegree_le_aux

theorem eraseLead_natDegree_lt (f0 : 2 ≤ f.support.card) : (eraseLead f).natDegree < f.natDegree :=
  lt_of_le_of_ne eraseLead_natDegree_le_aux <|
    ne_natDegree_of_mem_eraseLead_support <|
      natDegree_mem_support_of_nonzero <| eraseLead_ne_zero f0
#align polynomial.erase_lead_nat_degree_lt Polynomial.eraseLead_natDegree_lt

theorem eraseLead_natDegree_lt_or_eraseLead_eq_zero (f : R[X]) :
    (eraseLead f).natDegree < f.natDegree ∨ f.eraseLead = 0 :=
  by
  by_cases h : f.support.card ≤ 1
  · right
    rw [← C_mul_X_pow_eq_self h]
    simp
  · left
    apply erase_lead_nat_degree_lt (lt_of_not_ge h)
#align polynomial.erase_lead_nat_degree_lt_or_erase_lead_eq_zero Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero

theorem eraseLead_natDegree_le (f : R[X]) : (eraseLead f).natDegree ≤ f.natDegree - 1 :=
  by
  rcases f.erase_lead_nat_degree_lt_or_erase_lead_eq_zero with (h | h)
  · exact Nat.le_pred_of_lt h
  · simp only [h, nat_degree_zero, zero_le]
#align polynomial.erase_lead_nat_degree_le Polynomial.eraseLead_natDegree_le

end EraseLead

/-- An induction lemma for polynomials. It takes a natural number `N` as a parameter, that is
required to be at least as big as the `nat_degree` of the polynomial.  This is useful to prove
results where you want to change each term in a polynomial to something else depending on the
`nat_degree` of the polynomial itself and not on the specific `nat_degree` of each term. -/
theorem induction_with_natDegree_le (P : R[X] → Prop) (N : ℕ) (P_0 : P 0)
    (P_C_mul_pow : ∀ n : ℕ, ∀ r : R, r ≠ 0 → n ≤ N → P (C r * X ^ n))
    (P_C_add : ∀ f g : R[X], f.natDegree < g.natDegree → g.natDegree ≤ N → P f → P g → P (f + g)) :
    ∀ f : R[X], f.natDegree ≤ N → P f := by
  intro f df
  generalize hd : card f.support = c
  revert f
  induction' c with c hc
  · intro f df f0
    convert P_0
    simpa only [support_eq_empty, card_eq_zero] using f0
  · intro f df f0
    rw [← erase_lead_add_C_mul_X_pow f]
    cases c
    · convert P_C_mul_pow f.nat_degree f.leading_coeff _ df
      · convert zero_add _
        rw [← card_support_eq_zero, erase_lead_card_support f0]
      · rw [leading_coeff_ne_zero, Ne.def, ← card_support_eq_zero, f0]
        exact zero_ne_one.symm
    refine' P_C_add f.erase_lead _ _ _ _ _
    · refine' (erase_lead_nat_degree_lt _).trans_le (le_of_eq _)
      · exact (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))).trans f0.ge
      · rw [nat_degree_C_mul_X_pow _ _ (leading_coeff_ne_zero.mpr _)]
        rintro rfl
        simpa using f0
    · exact (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree).trans df
    · exact hc _ (erase_lead_nat_degree_le_aux.trans df) (erase_lead_card_support f0)
    · refine' P_C_mul_pow _ _ _ df
      rw [Ne.def, leading_coeff_eq_zero, ← card_support_eq_zero, f0]
      exact Nat.succ_ne_zero _
#align polynomial.induction_with_nat_degree_le Polynomial.induction_with_natDegree_le

/-- Let `φ : R[x] → S[x]` be an additive map, `k : ℕ` a bound, and `fu : ℕ → ℕ` a
"sufficiently monotone" map.  Assume also that
* `φ` maps to `0` all monomials of degree less than `k`,
* `φ` maps each monomial `m` in `R[x]` to a polynomial `φ m` of degree `fu (deg m)`.
Then, `φ` maps each polynomial `p` in `R[x]` to a polynomial of degree `fu (deg p)`. -/
theorem mono_map_natDegree_eq {S F : Type _} [Semiring S] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} (k : ℕ) (fu : ℕ → ℕ) (fu0 : ∀ {n}, n ≤ k → fu n = 0)
    (fc : ∀ {n m}, k ≤ n → n < m → fu n < fu m) (φ_k : ∀ {f : R[X]}, f.natDegree < k → φ f = 0)
    (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = fu n) :
    (φ p).natDegree = fu p.natDegree :=
  by
  refine' induction_with_nat_degree_le (fun p => _ = fu _) p.nat_degree (by simp [fu0]) _ _ _ rfl.le
  · intro n r r0 np
    rw [nat_degree_C_mul_X_pow _ _ r0, C_mul_X_pow_eq_monomial, φ_mon_nat _ _ r0]
  · intro f g fg gp fk gk
    rw [nat_degree_add_eq_right_of_nat_degree_lt fg, _root_.map_add]
    by_cases FG : k ≤ f.nat_degree
    · rw [nat_degree_add_eq_right_of_nat_degree_lt, gk]
      rw [fk, gk]
      exact fc FG fg
    · cases k
      · exact (FG (Nat.zero_le _)).elim
      · rwa [φ_k (not_le.mp FG), zero_add]
#align polynomial.mono_map_nat_degree_eq Polynomial.mono_map_natDegree_eq

theorem map_natDegree_eq_sub {S F : Type _} [Semiring S] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} {k : ℕ} (φ_k : ∀ f : R[X], f.natDegree < k → φ f = 0)
    (φ_mon : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n - k) :
    (φ p).natDegree = p.natDegree - k :=
  mono_map_natDegree_eq k (fun j => j - k) (by simp) (fun m n h => (tsub_lt_tsub_iff_right h).mpr)
    φ_k φ_mon
#align polynomial.map_nat_degree_eq_sub Polynomial.map_natDegree_eq_sub

theorem map_natDegree_eq_natDegree {S F : Type _} [Semiring S] [AddMonoidHomClass F R[X] S[X]]
    {φ : F} (p) (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n) :
    (φ p).natDegree = p.natDegree :=
  (map_natDegree_eq_sub (fun f h => (Nat.not_lt_zero _ h).elim) (by simpa)).trans
    p.natDegree.sub_zero
#align polynomial.map_nat_degree_eq_nat_degree Polynomial.map_natDegree_eq_natDegree

open BigOperators

theorem card_support_eq' {n : ℕ} (k : Fin n → ℕ) (x : Fin n → R) (hk : Function.Injective k)
    (hx : ∀ i, x i ≠ 0) : (∑ i, C (x i) * X ^ k i).support.card = n :=
  by
  suffices (∑ i, C (x i) * X ^ k i).support = image k univ by
    rw [this, univ.card_image_of_injective hk, card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finset_sum_coeff, coeff_C_mul_X_pow, mem_image,
    mem_univ, exists_true_left]
  refine' fun i => ⟨fun h => _, _⟩
  · obtain ⟨j, hj, h⟩ := exists_ne_zero_of_sum_ne_zero h
    exact ⟨j, (ite_ne_right_iff.mp h).1.symm⟩
  · rintro ⟨j, rfl⟩
    rw [sum_eq_single_of_mem j (mem_univ j), if_pos rfl]
    · exact hx j
    · exact fun m hm hmj => if_neg fun h => hmj.symm (hk h)
#align polynomial.card_support_eq' Polynomial.card_support_eq'

theorem card_support_eq {n : ℕ} :
    f.support.card = n ↔
      ∃ (k : Fin n → ℕ)(x : Fin n → R)(hk : StrictMono k)(hx : ∀ i, x i ≠ 0),
        f = ∑ i, C (x i) * X ^ k i :=
  by
  refine' ⟨_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ card_support_eq' k x hk.Injective hx⟩
  induction' n with n hn generalizing f
  · exact fun hf => ⟨0, 0, isEmptyElim, isEmptyElim, card_support_eq_zero.mp hf⟩
  · intro h
    obtain ⟨k, x, hk, hx, hf⟩ := hn (erase_lead_card_support' h)
    have H : ¬∃ k : Fin n, k.cast_succ = Fin.last n :=
      by
      rintro ⟨i, hi⟩
      exact i.cast_succ_lt_last.Ne hi
    refine'
      ⟨Function.extend Fin.castSucc k fun _ => f.nat_degree,
        Function.extend Fin.castSucc x fun _ => f.leading_coeff, _, _, _⟩
    · intro i j hij
      have hi : i ∈ Set.range (Fin.castSucc : Fin n ↪o Fin (n + 1)) :=
        by
        rw [Fin.range_castSucc, Set.mem_def]
        exact lt_of_lt_of_le hij (nat.lt_succ_iff.mp j.2)
      obtain ⟨i, rfl⟩ := hi
      rw [fin.cast_succ.injective.extend_apply]
      by_cases hj : ∃ j₀, Fin.castSucc j₀ = j
      · obtain ⟨j, rfl⟩ := hj
        rwa [fin.cast_succ.injective.extend_apply, hk.lt_iff_lt, ← Fin.castSucc_lt_castSucc_iff]
      · rw [Function.extend_apply' _ _ _ hj]
        apply lt_nat_degree_of_mem_erase_lead_support
        rw [mem_support_iff, hf, finset_sum_coeff]
        rw [sum_eq_single, coeff_C_mul, coeff_X_pow_self, mul_one]
        · exact hx i
        · intro j hj hji
          rw [coeff_C_mul, coeff_X_pow, if_neg (hk.injective.ne hji.symm), mul_zero]
        · exact fun hi => (hi (mem_univ i)).elim
    · intro i
      by_cases hi : ∃ i₀, Fin.castSucc i₀ = i
      · obtain ⟨i, rfl⟩ := hi
        rw [fin.cast_succ.injective.extend_apply]
        exact hx i
      · rw [Function.extend_apply' _ _ _ hi, Ne, leading_coeff_eq_zero, ← card_support_eq_zero, h]
        exact n.succ_ne_zero
    · rw [Fin.sum_univ_castSucc]
      simp only [fin.cast_succ.injective.extend_apply]
      rw [← hf, Function.extend_apply', Function.extend_apply', erase_lead_add_C_mul_X_pow]
      all_goals exact H
#align polynomial.card_support_eq Polynomial.card_support_eq

theorem card_support_eq_one : f.support.card = 1 ↔ ∃ (k : ℕ)(x : R)(hx : x ≠ 0), f = C x * X ^ k :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    exact ⟨k 0, x 0, hx 0, Fin.sum_univ_one _⟩
  · rintro ⟨k, x, hx, rfl⟩
    rw [support_C_mul_X_pow k hx, card_singleton]
#align polynomial.card_support_eq_one Polynomial.card_support_eq_one

theorem card_support_eq_two :
    f.support.card = 2 ↔
      ∃ (k m : ℕ)(hkm : k < m)(x y : R)(hx : x ≠ 0)(hy : y ≠ 0), f = C x * X ^ k + C y * X ^ m :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine' ⟨k 0, k 1, hk Nat.zero_lt_one, x 0, x 1, hx 0, hx 1, _⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    exact card_support_binomial hkm.ne hx hy
#align polynomial.card_support_eq_two Polynomial.card_support_eq_two

theorem card_support_eq_three :
    f.support.card = 3 ↔
      ∃ (k m n : ℕ)(hkm : k < m)(hmn : m < n)(x y z : R)(hx : x ≠ 0)(hy : y ≠ 0)(hz : z ≠ 0),
        f = C x * X ^ k + C y * X ^ m + C z * X ^ n :=
  by
  refine' ⟨fun h => _, _⟩
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    refine'
      ⟨k 0, k 1, k 2, hk Nat.zero_lt_one, hk (Nat.lt_succ_self 1), x 0, x 1, x 2, hx 0, hx 1, hx 2,
        _⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_one]
    rfl
  · rintro ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩
    exact card_support_trinomial hkm hmn hx hy hz
#align polynomial.card_support_eq_three Polynomial.card_support_eq_three

end Polynomial

