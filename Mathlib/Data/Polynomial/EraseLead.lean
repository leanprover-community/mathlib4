/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Polynomial.Degree.Definitions

#align_import data.polynomial.erase_lead from "leanprover-community/mathlib"@"fa256f00ce018e7b40e1dc756e403c86680bf448"

/-!
# Erase the leading term of a univariate polynomial

## Definition

* `eraseLead f`: the polynomial `f - leading term of f`

`eraseLead` serves as reduction step in an induction, shaving off one monomial from a polynomial.
The definition is set up so that it does not mention subtraction in the definition,
and thus works for polynomials over semirings as well as rings.
-/


noncomputable section

open Classical Polynomial

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

/-- `eraseLead f` for a polynomial `f` is the polynomial obtained by
subtracting from `f` the leading term of `f`. -/
def eraseLead (f : R[X]) : R[X] :=
  Polynomial.erase f.natDegree f
#align polynomial.erase_lead Polynomial.eraseLead

section EraseLead

theorem eraseLead_support (f : R[X]) : f.eraseLead.support = f.support.erase f.natDegree := by
  simp only [eraseLead, support_erase]
  -- 🎉 no goals
#align polynomial.erase_lead_support Polynomial.eraseLead_support

theorem eraseLead_coeff (i : ℕ) : f.eraseLead.coeff i = if i = f.natDegree then 0 else f.coeff i :=
  by simp only [eraseLead, coeff_erase]
     -- 🎉 no goals
#align polynomial.erase_lead_coeff Polynomial.eraseLead_coeff

@[simp]
theorem eraseLead_coeff_natDegree : f.eraseLead.coeff f.natDegree = 0 := by simp [eraseLead_coeff]
                                                                            -- 🎉 no goals
#align polynomial.erase_lead_coeff_nat_degree Polynomial.eraseLead_coeff_natDegree

theorem eraseLead_coeff_of_ne (i : ℕ) (hi : i ≠ f.natDegree) : f.eraseLead.coeff i = f.coeff i := by
  simp [eraseLead_coeff, hi]
  -- 🎉 no goals
#align polynomial.erase_lead_coeff_of_ne Polynomial.eraseLead_coeff_of_ne

@[simp]
theorem eraseLead_zero : eraseLead (0 : R[X]) = 0 := by simp only [eraseLead, erase_zero]
                                                        -- 🎉 no goals
#align polynomial.erase_lead_zero Polynomial.eraseLead_zero

@[simp]
theorem eraseLead_add_monomial_natDegree_leadingCoeff (f : R[X]) :
    f.eraseLead + monomial f.natDegree f.leadingCoeff = f :=
  (add_comm _ _).trans (f.monomial_add_erase _)
#align polynomial.erase_lead_add_monomial_nat_degree_leading_coeff Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff

@[simp]
theorem eraseLead_add_C_mul_X_pow (f : R[X]) :
    f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f := by
  rw [C_mul_X_pow_eq_monomial, eraseLead_add_monomial_natDegree_leadingCoeff]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.erase_lead_add_C_mul_X_pow Polynomial.eraseLead_add_C_mul_X_pow

@[simp]
theorem self_sub_monomial_natDegree_leadingCoeff {R : Type*} [Ring R] (f : R[X]) :
    f - monomial f.natDegree f.leadingCoeff = f.eraseLead :=
  (eq_sub_iff_add_eq.mpr (eraseLead_add_monomial_natDegree_leadingCoeff f)).symm
#align polynomial.self_sub_monomial_nat_degree_leading_coeff Polynomial.self_sub_monomial_natDegree_leadingCoeff

@[simp]
theorem self_sub_C_mul_X_pow {R : Type*} [Ring R] (f : R[X]) :
    f - C f.leadingCoeff * X ^ f.natDegree = f.eraseLead := by
  rw [C_mul_X_pow_eq_monomial, self_sub_monomial_natDegree_leadingCoeff]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.self_sub_C_mul_X_pow Polynomial.self_sub_C_mul_X_pow

theorem eraseLead_ne_zero (f0 : 2 ≤ f.support.card) : eraseLead f ≠ 0 := by
  rw [Ne, ← card_support_eq_zero, eraseLead_support]
  -- ⊢ ¬card (Finset.erase (support f) (natDegree f)) = 0
  exact
    (zero_lt_one.trans_le <| (tsub_le_tsub_right f0 1).trans Finset.pred_card_le_card_erase).ne.symm
#align polynomial.erase_lead_ne_zero Polynomial.eraseLead_ne_zero

theorem lt_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a < f.natDegree := by
  rw [eraseLead_support, mem_erase] at h
  -- ⊢ a < natDegree f
  exact (le_natDegree_of_mem_supp a h.2).lt_of_ne h.1
  -- 🎉 no goals
#align polynomial.lt_nat_degree_of_mem_erase_lead_support Polynomial.lt_natDegree_of_mem_eraseLead_support

theorem ne_natDegree_of_mem_eraseLead_support {a : ℕ} (h : a ∈ (eraseLead f).support) :
    a ≠ f.natDegree :=
  (lt_natDegree_of_mem_eraseLead_support h).ne
#align polynomial.ne_nat_degree_of_mem_erase_lead_support Polynomial.ne_natDegree_of_mem_eraseLead_support

theorem natDegree_not_mem_eraseLead_support : f.natDegree ∉ (eraseLead f).support := fun h =>
  ne_natDegree_of_mem_eraseLead_support h rfl
#align polynomial.nat_degree_not_mem_erase_lead_support Polynomial.natDegree_not_mem_eraseLead_support

theorem eraseLead_support_card_lt (h : f ≠ 0) : (eraseLead f).support.card < f.support.card := by
  rw [eraseLead_support]
  -- ⊢ card (Finset.erase (support f) (natDegree f)) < card (support f)
  exact card_lt_card (erase_ssubset <| natDegree_mem_support_of_nonzero h)
  -- 🎉 no goals
#align polynomial.erase_lead_support_card_lt Polynomial.eraseLead_support_card_lt

theorem eraseLead_card_support {c : ℕ} (fc : f.support.card = c) :
    f.eraseLead.support.card = c - 1 := by
  by_cases f0 : f = 0
  -- ⊢ card (support (eraseLead f)) = c - 1
  · rw [← fc, f0, eraseLead_zero, support_zero, card_empty]
    -- 🎉 no goals
  · rw [eraseLead_support, card_erase_of_mem (natDegree_mem_support_of_nonzero f0), fc]
    -- 🎉 no goals
#align polynomial.erase_lead_card_support Polynomial.eraseLead_card_support

theorem eraseLead_card_support' {c : ℕ} (fc : f.support.card = c + 1) :
    f.eraseLead.support.card = c :=
  eraseLead_card_support fc
#align polynomial.erase_lead_card_support' Polynomial.eraseLead_card_support'

@[simp]
theorem eraseLead_monomial (i : ℕ) (r : R) : eraseLead (monomial i r) = 0 := by
  by_cases hr : r = 0
  -- ⊢ eraseLead (↑(monomial i) r) = 0
  · subst r
    -- ⊢ eraseLead (↑(monomial i) 0) = 0
    simp only [monomial_zero_right, eraseLead_zero]
    -- 🎉 no goals
  · rw [eraseLead, natDegree_monomial, if_neg hr, erase_monomial]
    -- 🎉 no goals
#align polynomial.erase_lead_monomial Polynomial.eraseLead_monomial

@[simp]
theorem eraseLead_C (r : R) : eraseLead (C r) = 0 :=
  eraseLead_monomial _ _
set_option linter.uppercaseLean3 false in
#align polynomial.erase_lead_C Polynomial.eraseLead_C

@[simp]
theorem eraseLead_X : eraseLead (X : R[X]) = 0 :=
  eraseLead_monomial _ _
set_option linter.uppercaseLean3 false in
#align polynomial.erase_lead_X Polynomial.eraseLead_X

@[simp]
theorem eraseLead_X_pow (n : ℕ) : eraseLead (X ^ n : R[X]) = 0 := by
  rw [X_pow_eq_monomial, eraseLead_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.erase_lead_X_pow Polynomial.eraseLead_X_pow

@[simp]
theorem eraseLead_C_mul_X_pow (r : R) (n : ℕ) : eraseLead (C r * X ^ n) = 0 := by
  rw [C_mul_X_pow_eq_monomial, eraseLead_monomial]
  -- 🎉 no goals
set_option linter.uppercaseLean3 false in
#align polynomial.erase_lead_C_mul_X_pow Polynomial.eraseLead_C_mul_X_pow

theorem eraseLead_add_of_natDegree_lt_left {p q : R[X]} (pq : q.natDegree < p.natDegree) :
    (p + q).eraseLead = p.eraseLead + q := by
  ext n
  -- ⊢ coeff (eraseLead (p + q)) n = coeff (eraseLead p + q) n
  by_cases nd : n = p.natDegree
  -- ⊢ coeff (eraseLead (p + q)) n = coeff (eraseLead p + q) n
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_left_of_natDegree_lt pq).symm]
    -- ⊢ 0 = coeff (eraseLead p + q) (natDegree p)
    simpa using (coeff_eq_zero_of_natDegree_lt pq).symm
    -- 🎉 no goals
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
    -- ⊢ ¬n = natDegree (p + q)
    rintro rfl
    -- ⊢ False
    exact nd (natDegree_add_eq_left_of_natDegree_lt pq)
    -- 🎉 no goals
#align polynomial.erase_lead_add_of_nat_degree_lt_left Polynomial.eraseLead_add_of_natDegree_lt_left

theorem eraseLead_add_of_natDegree_lt_right {p q : R[X]} (pq : p.natDegree < q.natDegree) :
    (p + q).eraseLead = p + q.eraseLead := by
  ext n
  -- ⊢ coeff (eraseLead (p + q)) n = coeff (p + eraseLead q) n
  by_cases nd : n = q.natDegree
  -- ⊢ coeff (eraseLead (p + q)) n = coeff (p + eraseLead q) n
  · rw [nd, eraseLead_coeff, if_pos (natDegree_add_eq_right_of_natDegree_lt pq).symm]
    -- ⊢ 0 = coeff (p + eraseLead q) (natDegree q)
    simpa using (coeff_eq_zero_of_natDegree_lt pq).symm
    -- 🎉 no goals
  · rw [eraseLead_coeff, coeff_add, coeff_add, eraseLead_coeff, if_neg, if_neg nd]
    -- ⊢ ¬n = natDegree (p + q)
    rintro rfl
    -- ⊢ False
    exact nd (natDegree_add_eq_right_of_natDegree_lt pq)
    -- 🎉 no goals
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
    (eraseLead f).natDegree < f.natDegree ∨ f.eraseLead = 0 := by
  by_cases h : f.support.card ≤ 1
  -- ⊢ natDegree (eraseLead f) < natDegree f ∨ eraseLead f = 0
  · right
    -- ⊢ eraseLead f = 0
    rw [← C_mul_X_pow_eq_self h]
    -- ⊢ eraseLead (↑C (leadingCoeff f) * X ^ natDegree f) = 0
    simp
    -- 🎉 no goals
  · left
    -- ⊢ natDegree (eraseLead f) < natDegree f
    apply eraseLead_natDegree_lt (lt_of_not_ge h)
    -- 🎉 no goals
#align polynomial.erase_lead_nat_degree_lt_or_erase_lead_eq_zero Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero

theorem eraseLead_natDegree_le (f : R[X]) : (eraseLead f).natDegree ≤ f.natDegree - 1 := by
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with (h | h)
  -- ⊢ natDegree (eraseLead f) ≤ natDegree f - 1
  · exact Nat.le_pred_of_lt h
    -- 🎉 no goals
  · simp only [h, natDegree_zero, zero_le]
    -- 🎉 no goals
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
  -- ⊢ P f
  generalize hd : card f.support = c
  -- ⊢ P f
  revert f
  -- ⊢ ∀ (f : R[X]), natDegree f ≤ N → card (support f) = c → P f
  induction' c with c hc
  -- ⊢ ∀ (f : R[X]), natDegree f ≤ N → card (support f) = Nat.zero → P f
  · intro f _ f0
    -- ⊢ P f
    convert P_0
    -- ⊢ f = 0
    simpa [support_eq_empty, card_eq_zero] using f0
    -- 🎉 no goals
  · intro f df f0
    -- ⊢ P f
    rw [← eraseLead_add_C_mul_X_pow f]
    -- ⊢ P (eraseLead f + ↑C (leadingCoeff f) * X ^ natDegree f)
    cases c
    -- ⊢ P (eraseLead f + ↑C (leadingCoeff f) * X ^ natDegree f)
    · convert P_C_mul_pow f.natDegree f.leadingCoeff ?_ df using 1
      -- ⊢ eraseLead f + ↑C (leadingCoeff f) * X ^ natDegree f = ↑C (leadingCoeff f) *  …
      · convert zero_add (C (leadingCoeff f) * X ^ f.natDegree)
        -- ⊢ eraseLead f = 0
        rw [← card_support_eq_zero, eraseLead_card_support f0]
        -- 🎉 no goals
      · rw [leadingCoeff_ne_zero, Ne.def, ← card_support_eq_zero, f0]
        -- ⊢ ¬Nat.succ Nat.zero = 0
        exact zero_ne_one.symm
        -- 🎉 no goals
    refine' P_C_add f.eraseLead _ _ _ _ _
    · refine' (eraseLead_natDegree_lt _).trans_le (le_of_eq _)
      -- ⊢ 2 ≤ card (support f)
      · exact (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))).trans f0.ge
        -- 🎉 no goals
      · rw [natDegree_C_mul_X_pow _ _ (leadingCoeff_ne_zero.mpr _)]
        -- ⊢ f ≠ 0
        rintro rfl
        -- ⊢ False
        simp at f0
        -- 🎉 no goals
    · exact (natDegree_C_mul_X_pow_le f.leadingCoeff f.natDegree).trans df
      -- 🎉 no goals
    · exact hc _ (eraseLead_natDegree_le_aux.trans df) (eraseLead_card_support f0)
      -- 🎉 no goals
    · refine' P_C_mul_pow _ _ _ df
      -- ⊢ leadingCoeff f ≠ 0
      rw [Ne.def, leadingCoeff_eq_zero, ← card_support_eq_zero, f0]
      -- ⊢ ¬Nat.succ (Nat.succ n✝) = 0
      exact Nat.succ_ne_zero _
      -- 🎉 no goals
#align polynomial.induction_with_nat_degree_le Polynomial.induction_with_natDegree_le

/-- Let `φ : R[x] → S[x]` be an additive map, `k : ℕ` a bound, and `fu : ℕ → ℕ` a
"sufficiently monotone" map.  Assume also that
* `φ` maps to `0` all monomials of degree less than `k`,
* `φ` maps each monomial `m` in `R[x]` to a polynomial `φ m` of degree `fu (deg m)`.
Then, `φ` maps each polynomial `p` in `R[x]` to a polynomial of degree `fu (deg p)`. -/
theorem mono_map_natDegree_eq {S F : Type*} [Semiring S] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} (k : ℕ) (fu : ℕ → ℕ) (fu0 : ∀ {n}, n ≤ k → fu n = 0)
    (fc : ∀ {n m}, k ≤ n → n < m → fu n < fu m) (φ_k : ∀ {f : R[X]}, f.natDegree < k → φ f = 0)
    (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = fu n) :
    (φ p).natDegree = fu p.natDegree := by
  refine' induction_with_natDegree_le (fun p => (φ p).natDegree = fu p.natDegree)
    p.natDegree (by simp [fu0]) _ _ _ rfl.le
  · intro n r r0 _
    -- ⊢ natDegree (↑φ (↑C r * X ^ n)) = fu (natDegree (↑C r * X ^ n))
    rw [natDegree_C_mul_X_pow _ _ r0, C_mul_X_pow_eq_monomial, φ_mon_nat _ _ r0]
    -- 🎉 no goals
  · intro f g fg _ fk gk
    -- ⊢ natDegree (↑φ (f + g)) = fu (natDegree (f + g))
    rw [natDegree_add_eq_right_of_natDegree_lt fg, _root_.map_add]
    -- ⊢ natDegree (↑φ f + ↑φ g) = fu (natDegree g)
    by_cases FG : k ≤ f.natDegree
    -- ⊢ natDegree (↑φ f + ↑φ g) = fu (natDegree g)
    · rw [natDegree_add_eq_right_of_natDegree_lt, gk]
      -- ⊢ natDegree (↑φ f) < natDegree (↑φ g)
      rw [fk, gk]
      -- ⊢ fu (natDegree f) < fu (natDegree g)
      exact fc FG fg
      -- 🎉 no goals
    · cases k
      -- ⊢ natDegree (↑φ f + ↑φ g) = fu (natDegree g)
      · exact (FG (Nat.zero_le _)).elim
        -- 🎉 no goals
      · rwa [φ_k (not_le.mp FG), zero_add]
        -- 🎉 no goals
#align polynomial.mono_map_nat_degree_eq Polynomial.mono_map_natDegree_eq

theorem map_natDegree_eq_sub {S F : Type*} [Semiring S] [AddMonoidHomClass F R[X] S[X]] {φ : F}
    {p : R[X]} {k : ℕ} (φ_k : ∀ f : R[X], f.natDegree < k → φ f = 0)
    (φ_mon : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n - k) :
    (φ p).natDegree = p.natDegree - k :=
  mono_map_natDegree_eq k (fun j => j - k) (by simp)
                                               -- 🎉 no goals
    (@fun m n h => (tsub_lt_tsub_iff_right h).mpr)
    (φ_k _) φ_mon
#align polynomial.map_nat_degree_eq_sub Polynomial.map_natDegree_eq_sub

theorem map_natDegree_eq_natDegree {S F : Type*} [Semiring S] [AddMonoidHomClass F R[X] S[X]]
    {φ : F} (p) (φ_mon_nat : ∀ n c, c ≠ 0 → (φ (monomial n c)).natDegree = n) :
    (φ p).natDegree = p.natDegree :=
  (map_natDegree_eq_sub (fun f h => (Nat.not_lt_zero _ h).elim) (by simpa)).trans
                                                                    -- 🎉 no goals
    p.natDegree.sub_zero
#align polynomial.map_nat_degree_eq_nat_degree Polynomial.map_natDegree_eq_natDegree

open BigOperators

theorem card_support_eq' {n : ℕ} (k : Fin n → ℕ) (x : Fin n → R) (hk : Function.Injective k)
    (hx : ∀ i, x i ≠ 0) : (∑ i, C (x i) * X ^ k i).support.card = n := by
  suffices (∑ i, C (x i) * X ^ k i).support = image k univ by
    rw [this, univ.card_image_of_injective hk, card_fin]
  simp_rw [Finset.ext_iff, mem_support_iff, finset_sum_coeff, coeff_C_mul_X_pow, mem_image,
    mem_univ, true_and]
  refine' fun i => ⟨fun h => _, _⟩
  -- ⊢ ∃ a, k a = i
  · obtain ⟨j, _, h⟩ := exists_ne_zero_of_sum_ne_zero h
    -- ⊢ ∃ a, k a = i
    exact ⟨j, (ite_ne_right_iff.mp h).1.symm⟩
    -- 🎉 no goals
  · rintro ⟨j, _, rfl⟩
    -- ⊢ (∑ x_1 : Fin n, if k j = k x_1 then x x_1 else 0) ≠ 0
    rw [sum_eq_single_of_mem j (mem_univ j), if_pos rfl]
    -- ⊢ x j ≠ 0
    · exact hx j
      -- 🎉 no goals
    · exact fun m _ hmj => if_neg fun h => hmj.symm (hk h)
      -- 🎉 no goals
#align polynomial.card_support_eq' Polynomial.card_support_eq'

theorem card_support_eq {n : ℕ} :
    f.support.card = n ↔
      ∃ (k : Fin n → ℕ) (x : Fin n → R) (hk : StrictMono k) (hx : ∀ i, x i ≠ 0),
        f = ∑ i, C (x i) * X ^ k i := by
  refine' ⟨_, fun ⟨k, x, hk, hx, hf⟩ => hf.symm ▸ card_support_eq' k x hk.injective hx⟩
  -- ⊢ card (support f) = n → ∃ k x hk hx, f = ∑ i : Fin n, ↑C (x i) * X ^ k i
  induction' n with n hn generalizing f
  -- ⊢ card (support f) = Nat.zero → ∃ k x hk hx, f = ∑ i : Fin Nat.zero, ↑C (x i)  …
  · exact fun hf => ⟨0, 0, fun x => x.elim0, fun x => x.elim0, card_support_eq_zero.mp hf⟩
    -- 🎉 no goals
  · intro h
    -- ⊢ ∃ k x hk hx, f = ∑ i : Fin (Nat.succ n), ↑C (x i) * X ^ k i
    obtain ⟨k, x, hk, hx, hf⟩ := hn (eraseLead_card_support' h)
    -- ⊢ ∃ k x hk hx, f = ∑ i : Fin (Nat.succ n), ↑C (x i) * X ^ k i
    have H : ¬∃ k : Fin n, Fin.castSucc k = Fin.last n := by
      rintro ⟨i, hi⟩
      exact i.castSucc_lt_last.ne hi
    refine'
      ⟨Function.extend Fin.castSucc k fun _ => f.natDegree,
        Function.extend Fin.castSucc x fun _ => f.leadingCoeff, _, _, _⟩
    · intro i j hij
      -- ⊢ Function.extend Fin.castSucc k (fun x => natDegree f) i < Function.extend Fi …
      have hi : i ∈ Set.range (Fin.castSucc : Fin n → Fin (n + 1)) := by
        rw [Fin.range_castSucc, Set.mem_def]
        exact lt_of_lt_of_le hij (Nat.lt_succ_iff.mp j.2)
      obtain ⟨i, rfl⟩ := hi
      -- ⊢ Function.extend Fin.castSucc k (fun x => natDegree f) (Fin.castSucc i) < Fun …
      rw [Fin.strictMono_castSucc.injective.extend_apply]
      -- ⊢ k i < Function.extend Fin.castSucc k (fun x => natDegree f) j
      by_cases hj : ∃ j₀, Fin.castSucc j₀ = j
      -- ⊢ k i < Function.extend Fin.castSucc k (fun x => natDegree f) j
      · obtain ⟨j, rfl⟩ := hj
        -- ⊢ k i < Function.extend Fin.castSucc k (fun x => natDegree f) (Fin.castSucc j)
        rwa [Fin.strictMono_castSucc.injective.extend_apply, hk.lt_iff_lt,
          ← Fin.castSucc_lt_castSucc_iff]
      · rw [Function.extend_apply' _ _ _ hj]
        -- ⊢ k i < natDegree f
        apply lt_natDegree_of_mem_eraseLead_support
        -- ⊢ k i ∈ support (eraseLead f)
        rw [mem_support_iff, hf, finset_sum_coeff]
        -- ⊢ ∑ b : Fin n, coeff (↑C (x b) * X ^ k b) (k i) ≠ 0
        rw [sum_eq_single, coeff_C_mul, coeff_X_pow_self, mul_one]
        · exact hx i
          -- 🎉 no goals
        · intro j _ hji
          -- ⊢ coeff (↑C (x j) * X ^ k j) (k i) = 0
          rw [coeff_C_mul, coeff_X_pow, if_neg (hk.injective.ne hji.symm), mul_zero]
          -- 🎉 no goals
        · exact fun hi => (hi (mem_univ i)).elim
          -- 🎉 no goals
    · intro i
      -- ⊢ Function.extend Fin.castSucc x (fun x => leadingCoeff f) i ≠ 0
      by_cases hi : ∃ i₀, Fin.castSucc i₀ = i
      -- ⊢ Function.extend Fin.castSucc x (fun x => leadingCoeff f) i ≠ 0
      · obtain ⟨i, rfl⟩ := hi
        -- ⊢ Function.extend Fin.castSucc x (fun x => leadingCoeff f) (Fin.castSucc i) ≠ 0
        rw [Fin.strictMono_castSucc.injective.extend_apply]
        -- ⊢ x i ≠ 0
        exact hx i
        -- 🎉 no goals
      · rw [Function.extend_apply' _ _ _ hi, Ne, leadingCoeff_eq_zero, ← card_support_eq_zero, h]
        -- ⊢ ¬Nat.succ n = 0
        exact n.succ_ne_zero
        -- 🎉 no goals
    · rw [Fin.sum_univ_castSucc]
      -- ⊢ f = ∑ i : Fin n, ↑C (Function.extend Fin.castSucc x (fun x => leadingCoeff f …
      simp only [Fin.strictMono_castSucc.injective.extend_apply]
      -- ⊢ f = ∑ x_1 : Fin n, ↑C (x x_1) * X ^ k x_1 + ↑C (Function.extend Fin.castSucc …
      rw [← hf, Function.extend_apply', Function.extend_apply', eraseLead_add_C_mul_X_pow]
      -- ⊢ ¬∃ a, Fin.castSucc a = Fin.last n
      all_goals exact H
      -- 🎉 no goals
#align polynomial.card_support_eq Polynomial.card_support_eq

theorem card_support_eq_one : f.support.card = 1 ↔
    ∃ (k : ℕ) (x : R) (hx : x ≠ 0), f = C x * X ^ k := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ ∃ k x hx, f = ↑C x * X ^ k
  · obtain ⟨k, x, _, hx, rfl⟩ := card_support_eq.mp h
    -- ⊢ ∃ k_1 x_1 hx, ∑ i : Fin 1, ↑C (x i) * X ^ k i = ↑C x_1 * X ^ k_1
    exact ⟨k 0, x 0, hx 0, Fin.sum_univ_one _⟩
    -- 🎉 no goals
  · rintro ⟨k, x, hx, rfl⟩
    -- ⊢ card (support (↑C x * X ^ k)) = 1
    rw [support_C_mul_X_pow k hx, card_singleton]
    -- 🎉 no goals
#align polynomial.card_support_eq_one Polynomial.card_support_eq_one

theorem card_support_eq_two :
    f.support.card = 2 ↔
      ∃ (k m : ℕ) (hkm : k < m) (x y : R) (hx : x ≠ 0) (hy : y ≠ 0),
        f = C x * X ^ k + C y * X ^ m := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ ∃ k m hkm x y hx hy, f = ↑C x * X ^ k + ↑C y * X ^ m
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    -- ⊢ ∃ k_1 m hkm x_1 y hx hy, ∑ i : Fin 2, ↑C (x i) * X ^ k i = ↑C x_1 * X ^ k_1  …
    refine' ⟨k 0, k 1, hk Nat.zero_lt_one, x 0, x 1, hx 0, hx 1, _⟩
    -- ⊢ ∑ i : Fin 2, ↑C (x i) * X ^ k i = ↑C (x 0) * X ^ k 0 + ↑C (x 1) * X ^ k 1
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_one]
    -- ⊢ ↑C (x (Fin.castSucc 0)) * X ^ k (Fin.castSucc 0) + ↑C (x (Fin.last 1)) * X ^ …
    rfl
    -- 🎉 no goals
  · rintro ⟨k, m, hkm, x, y, hx, hy, rfl⟩
    -- ⊢ card (support (↑C x * X ^ k + ↑C y * X ^ m)) = 2
    exact card_support_binomial hkm.ne hx hy
    -- 🎉 no goals
#align polynomial.card_support_eq_two Polynomial.card_support_eq_two

theorem card_support_eq_three :
    f.support.card = 3 ↔
      ∃ (k m n : ℕ) (hkm : k < m) (hmn : m < n) (x y z : R) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0),
        f = C x * X ^ k + C y * X ^ m + C z * X ^ n := by
  refine' ⟨fun h => _, _⟩
  -- ⊢ ∃ k m n hkm hmn x y z hx hy hz, f = ↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n
  · obtain ⟨k, x, hk, hx, rfl⟩ := card_support_eq.mp h
    -- ⊢ ∃ k_1 m n hkm hmn x_1 y z hx hy hz, ∑ i : Fin 3, ↑C (x i) * X ^ k i = ↑C x_1 …
    refine'
      ⟨k 0, k 1, k 2, hk Nat.zero_lt_one, hk (Nat.lt_succ_self 1), x 0, x 1, x 2, hx 0, hx 1, hx 2,
        _⟩
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_one]
    -- ⊢ ↑C (x (Fin.castSucc (Fin.castSucc 0))) * X ^ k (Fin.castSucc (Fin.castSucc 0 …
    rfl
    -- 🎉 no goals
  · rintro ⟨k, m, n, hkm, hmn, x, y, z, hx, hy, hz, rfl⟩
    -- ⊢ card (support (↑C x * X ^ k + ↑C y * X ^ m + ↑C z * X ^ n)) = 3
    exact card_support_trinomial hkm hmn hx hy hz
    -- 🎉 no goals
#align polynomial.card_support_eq_three Polynomial.card_support_eq_three

end Polynomial
