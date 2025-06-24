/-
Copyright (c) 2021 Stuart Presnell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stuart Presnell
-/
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-!
# Basic lemmas on prime factorizations
-/

open Finset List Finsupp

namespace Nat
variable {a b m n p : ℕ}

/-! ### Basic facts about factorization -/

/-! ## Lemmas characterising when `n.factorization p = 0` -/


theorem factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0 :=
  Finsupp.notMem_support_iff.mp (mt le_of_mem_primeFactors (not_le_of_gt h))

@[simp]
theorem factorization_one_right (n : ℕ) : n.factorization 1 = 0 :=
  factorization_eq_zero_of_non_prime _ not_prime_one

theorem dvd_of_factorization_pos {n p : ℕ} (hn : n.factorization p ≠ 0) : p ∣ n :=
  dvd_of_mem_primeFactorsList <| mem_primeFactors_iff_mem_primeFactorsList.1 <| mem_support_iff.2 hn

theorem factorization_eq_zero_iff_remainder {p r : ℕ} (i : ℕ) (pp : p.Prime) (hr0 : r ≠ 0) :
    ¬p ∣ r ↔ (p * i + r).factorization p = 0 := by
  refine ⟨factorization_eq_zero_of_remainder i, fun h => ?_⟩
  rw [factorization_eq_zero_iff] at h
  contrapose! h
  refine ⟨pp, ?_, ?_⟩
  · rwa [← Nat.dvd_add_iff_right (dvd_mul_right p i)]
  · contrapose! hr0
    exact (add_eq_zero.1 hr0).2

/-- The only numbers with empty prime factorization are `0` and `1` -/
theorem factorization_eq_zero_iff' (n : ℕ) : n.factorization = 0 ↔ n = 0 ∨ n = 1 := by
  rw [factorization_eq_primeFactorsList_multiset n]
  simp [factorization, AddEquiv.map_eq_zero_iff, Multiset.coe_eq_zero]

/-! ## Lemmas about factorizations of products and powers -/


/-- A product over `n.factorization` can be written as a product over `n.primeFactors`; -/
lemma prod_factorization_eq_prod_primeFactors {β : Type*} [CommMonoid β] (f : ℕ → ℕ → β) :
    n.factorization.prod f = ∏ p ∈ n.primeFactors, f p (n.factorization p) := rfl

/-- A product over `n.primeFactors` can be written as a product over `n.factorization`; -/
lemma prod_primeFactors_prod_factorization {β : Type*} [CommMonoid β] (f : ℕ → β) :
    ∏ p ∈ n.primeFactors, f p = n.factorization.prod (fun p _ ↦ f p) := rfl

/-! ## Lemmas about factorizations of primes and prime powers -/


/-- The multiplicity of prime `p` in `p` is `1` -/
theorem Prime.factorization_self {p : ℕ} (hp : Prime p) : p.factorization p = 1 := by simp [hp]

/-- If the factorization of `n` contains just one number `p` then `n` is a power of `p` -/
theorem eq_pow_of_factorization_eq_single {n p k : ℕ} (hn : n ≠ 0)
    (h : n.factorization = Finsupp.single p k) : n = p ^ k := by
  rw [← Nat.factorization_prod_pow_eq_self hn, h]
  simp

/-- The only prime factor of prime `p` is `p` itself. -/
theorem Prime.eq_of_factorization_pos {p q : ℕ} (hp : Prime p) (h : p.factorization q ≠ 0) :
    p = q := by simpa [hp.factorization, single_apply] using h

/-! ### Equivalence between `ℕ+` and `ℕ →₀ ℕ` with support in the primes. -/


theorem eq_factorization_iff {n : ℕ} {f : ℕ →₀ ℕ} (hn : n ≠ 0) (hf : ∀ p ∈ f.support, Prime p) :
    f = n.factorization ↔ f.prod (· ^ ·) = n :=
  ⟨fun h => by rw [h, factorization_prod_pow_eq_self hn], fun h => by
    rw [← h, prod_pow_factorization_eq_self hf]⟩

theorem factorizationEquiv_inv_apply {f : ℕ →₀ ℕ} (hf : ∀ p ∈ f.support, Prime p) :
    (factorizationEquiv.symm ⟨f, hf⟩).1 = f.prod (· ^ ·) :=
  rfl

theorem ordProj_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ordProj[p] n = 1 := by
  simp [hp]

@[deprecated (since := "2024-10-24")] alias ord_proj_of_not_prime := ordProj_of_not_prime

theorem ordCompl_of_not_prime (n p : ℕ) (hp : ¬p.Prime) : ordCompl[p] n = n := by
  simp [hp]

@[deprecated (since := "2024-10-24")] alias ord_compl_of_not_prime := ordCompl_of_not_prime

theorem ordCompl_dvd (n p : ℕ) : ordCompl[p] n ∣ n :=
  div_dvd_of_dvd (ordProj_dvd n p)

@[deprecated (since := "2024-10-24")] alias ord_compl_dvd := ordCompl_dvd

theorem ordProj_pos (n p : ℕ) : 0 < ordProj[p] n := by
  if pp : p.Prime then simp [pow_pos pp.pos] else simp [pp]

@[deprecated (since := "2024-10-24")] alias ord_proj_pos := ordProj_pos

theorem ordProj_le {n : ℕ} (p : ℕ) (hn : n ≠ 0) : ordProj[p] n ≤ n :=
  le_of_dvd hn.bot_lt (Nat.ordProj_dvd n p)

@[deprecated (since := "2024-10-24")] alias ord_proj_le := ordProj_le

theorem ordCompl_pos {n : ℕ} (p : ℕ) (hn : n ≠ 0) : 0 < ordCompl[p] n := by
  if pp : p.Prime then
    exact Nat.div_pos (ordProj_le p hn) (ordProj_pos n p)
  else
    simpa [Nat.factorization_eq_zero_of_non_prime n pp] using hn.bot_lt

@[deprecated (since := "2024-10-24")] alias ord_compl_pos := ordCompl_pos

theorem ordCompl_le (n p : ℕ) : ordCompl[p] n ≤ n :=
  Nat.div_le_self _ _

@[deprecated (since := "2024-10-24")] alias ord_compl_le := ordCompl_le

theorem ordProj_mul_ordCompl_eq_self (n p : ℕ) : ordProj[p] n * ordCompl[p] n = n :=
  Nat.mul_div_cancel' (ordProj_dvd n p)

@[deprecated (since := "2024-10-24")]
alias ord_proj_mul_ord_compl_eq_self := ordProj_mul_ordCompl_eq_self

theorem ordProj_mul {a b : ℕ} (p : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ordProj[p] (a * b) = ordProj[p] a * ordProj[p] b := by
  simp [factorization_mul ha hb, pow_add]

@[deprecated (since := "2024-10-24")] alias ord_proj_mul := ordProj_mul

theorem ordCompl_mul (a b p : ℕ) : ordCompl[p] (a * b) = ordCompl[p] a * ordCompl[p] b := by
  if ha : a = 0 then simp [ha] else
  if hb : b = 0 then simp [hb] else
  simp only [ordProj_mul p ha hb]
  rw [div_mul_div_comm (ordProj_dvd a p) (ordProj_dvd b p)]

@[deprecated (since := "2024-10-24")] alias ord_compl_mul := ordCompl_mul

/-! ### Factorization and divisibility -/

/-- A crude upper bound on `n.factorization p` -/
theorem factorization_lt {n : ℕ} (p : ℕ) (hn : n ≠ 0) : n.factorization p < n := by
  by_cases pp : p.Prime
  · exact (Nat.pow_lt_pow_iff_right pp.one_lt).1 <| (ordProj_le p hn).trans_lt <|
      Nat.lt_pow_self pp.one_lt
  · simpa only [factorization_eq_zero_of_non_prime n pp] using hn.bot_lt

/-- An upper bound on `n.factorization p` -/
theorem factorization_le_of_le_pow {n p b : ℕ} (hb : n ≤ p ^ b) : n.factorization p ≤ b := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then
    exact (Nat.pow_le_pow_iff_right pp.one_lt).1 ((ordProj_le p hn).trans hb)
  else
    simp [factorization_eq_zero_of_non_prime n pp]

theorem factorization_prime_le_iff_dvd {d n : ℕ} (hd : d ≠ 0) (hn : n ≠ 0) :
    (∀ p : ℕ, p.Prime → d.factorization p ≤ n.factorization p) ↔ d ∣ n := by
  rw [← factorization_le_iff_dvd hd hn]
  refine ⟨fun h p => (em p.Prime).elim (h p) fun hp => ?_, fun h p _ => h p⟩
  simp_rw [factorization_eq_zero_of_non_prime _ hp]
  rfl

theorem factorization_le_factorization_mul_left {a b : ℕ} (hb : b ≠ 0) :
    a.factorization ≤ (a * b).factorization := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · simp
  rw [factorization_le_iff_dvd ha <| mul_ne_zero ha hb]
  exact Dvd.intro b rfl

theorem factorization_le_factorization_mul_right {a b : ℕ} (ha : a ≠ 0) :
    b.factorization ≤ (a * b).factorization := by
  rw [mul_comm]
  apply factorization_le_factorization_mul_left ha

theorem Prime.pow_dvd_iff_le_factorization {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ k ≤ n.factorization p := by
  rw [← factorization_le_iff_dvd (pow_pos pp.pos k).ne' hn, pp.factorization_pow, single_le_iff]

theorem Prime.pow_dvd_iff_dvd_ordProj {p k n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ^ k ∣ n ↔ p ^ k ∣ ordProj[p] n := by
  rw [pow_dvd_pow_iff_le_right pp.one_lt, pp.pow_dvd_iff_le_factorization hn]

@[deprecated (since := "2024-10-24")]
alias Prime.pow_dvd_iff_dvd_ord_proj := Prime.pow_dvd_iff_dvd_ordProj

theorem Prime.dvd_iff_one_le_factorization {p n : ℕ} (pp : Prime p) (hn : n ≠ 0) :
    p ∣ n ↔ 1 ≤ n.factorization p :=
  Iff.trans (by simp) (pp.pow_dvd_iff_le_factorization hn)

theorem exists_factorization_lt_of_lt {a b : ℕ} (ha : a ≠ 0) (hab : a < b) :
    ∃ p : ℕ, a.factorization p < b.factorization p := by
  have hb : b ≠ 0 := (ha.bot_lt.trans hab).ne'
  contrapose! hab
  rw [← Finsupp.le_def, factorization_le_iff_dvd hb ha] at hab
  exact le_of_dvd ha.bot_lt hab

@[simp]
theorem factorization_div {d n : ℕ} (h : d ∣ n) :
    (n / d).factorization = n.factorization - d.factorization := by
  rcases eq_or_ne d 0 with (rfl | hd); · simp [zero_dvd_iff.mp h]
  rcases eq_or_ne n 0 with (rfl | hn); · simp [tsub_eq_zero_of_le]
  apply add_left_injective d.factorization
  simp only
  rw [tsub_add_cancel_of_le <| (Nat.factorization_le_iff_dvd hd hn).mpr h, ←
    Nat.factorization_mul (Nat.div_pos (Nat.le_of_dvd hn.bot_lt h) hd.bot_lt).ne' hd,
    Nat.div_mul_cancel h]

theorem dvd_ordProj_of_dvd {n p : ℕ} (hn : n ≠ 0) (pp : p.Prime) (h : p ∣ n) : p ∣ ordProj[p] n :=
  dvd_pow_self p (Prime.factorization_pos_of_dvd pp hn h).ne'

@[deprecated (since := "2024-10-24")] alias dvd_ord_proj_of_dvd := dvd_ordProj_of_dvd

theorem not_dvd_ordCompl {n p : ℕ} (hp : Prime p) (hn : n ≠ 0) : ¬p ∣ ordCompl[p] n := by
  rw [Nat.Prime.dvd_iff_one_le_factorization hp (ordCompl_pos p hn).ne']
  rw [Nat.factorization_div (Nat.ordProj_dvd n p)]
  simp [hp.factorization]

@[deprecated (since := "2024-10-24")] alias not_dvd_ord_compl := not_dvd_ordCompl

theorem coprime_ordCompl {n p : ℕ} (hp : Prime p) (hn : n ≠ 0) : Coprime p (ordCompl[p] n) :=
  (or_iff_left (not_dvd_ordCompl hp hn)).mp <| coprime_or_dvd_of_prime hp _

@[deprecated (since := "2024-10-24")] alias coprime_ord_compl := coprime_ordCompl

theorem factorization_ordCompl (n p : ℕ) :
    (ordCompl[p] n).factorization = n.factorization.erase p := by
  if hn : n = 0 then simp [hn] else
  if pp : p.Prime then ?_ else
    simp [pp]
  ext q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp only [Finsupp.erase_same, factorization_eq_zero_iff, not_dvd_ordCompl pp hn]
    simp
  · rw [Finsupp.erase_ne hqp, factorization_div (ordProj_dvd n p)]
    simp [pp.factorization, hqp.symm]

@[deprecated (since := "2024-10-24")] alias factorization_ord_compl := factorization_ordCompl

-- `ordCompl[p] n` is the largest divisor of `n` not divisible by `p`.
theorem dvd_ordCompl_of_dvd_not_dvd {p d n : ℕ} (hdn : d ∣ n) (hpd : ¬p ∣ d) :
    d ∣ ordCompl[p] n := by
  if hn0 : n = 0 then simp [hn0] else
  if hd0 : d = 0 then simp [hd0] at hpd else
  rw [← factorization_le_iff_dvd hd0 (ordCompl_pos p hn0).ne', factorization_ordCompl]
  intro q
  if hqp : q = p then
    simp [factorization_eq_zero_iff, hqp, hpd]
  else
    simp [hqp, (factorization_le_iff_dvd hd0 hn0).2 hdn q]

@[deprecated (since := "2024-10-24")]
alias dvd_ord_compl_of_dvd_not_dvd := dvd_ordCompl_of_dvd_not_dvd

/-- If `n` is a nonzero natural number and `p ≠ 1`, then there are natural numbers `e`
and `n'` such that `n'` is not divisible by `p` and `n = p^e * n'`. -/
theorem exists_eq_pow_mul_and_not_dvd {n : ℕ} (hn : n ≠ 0) (p : ℕ) (hp : p ≠ 1) :
    ∃ e n' : ℕ, ¬p ∣ n' ∧ n = p ^ e * n' :=
  let ⟨a', h₁, h₂⟩ :=
    (Nat.finiteMultiplicity_iff.mpr ⟨hp, Nat.pos_of_ne_zero hn⟩).exists_eq_pow_mul_and_not_dvd
  ⟨_, a', h₂, h₁⟩

/-- Any nonzero natural number is the product of an odd part `m` and a power of
two `2 ^ k`. -/
theorem exists_eq_two_pow_mul_odd {n : ℕ} (hn : n ≠ 0) :
    ∃ k m : ℕ, Odd m ∧ n = 2 ^ k * m :=
  let ⟨k, m, hm, hn⟩ := exists_eq_pow_mul_and_not_dvd hn 2 (succ_ne_self 1)
  ⟨k, m, not_even_iff_odd.1 (mt Even.two_dvd hm), hn⟩

theorem dvd_iff_div_factorization_eq_tsub {d n : ℕ} (hd : d ≠ 0) (hdn : d ≤ n) :
    d ∣ n ↔ (n / d).factorization = n.factorization - d.factorization := by
  refine ⟨factorization_div, ?_⟩
  rcases eq_or_lt_of_le hdn with (rfl | hd_lt_n); · simp
  have h1 : n / d ≠ 0 := by simp [*]
  intro h
  rw [dvd_iff_le_div_mul n d]
  by_contra h2
  obtain ⟨p, hp⟩ := exists_factorization_lt_of_lt (mul_ne_zero h1 hd) (not_le.mp h2)
  rwa [factorization_mul h1 hd, add_apply, ← lt_tsub_iff_right, h, tsub_apply,
   lt_self_iff_false] at hp

theorem ordProj_dvd_ordProj_of_dvd {a b : ℕ} (hb0 : b ≠ 0) (hab : a ∣ b) (p : ℕ) :
    ordProj[p] a ∣ ordProj[p] b := by
  rcases em' p.Prime with (pp | pp); · simp [pp]
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rw [pow_dvd_pow_iff_le_right pp.one_lt]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab p

@[deprecated (since := "2024-10-24")]
alias ord_proj_dvd_ord_proj_of_dvd := ordProj_dvd_ordProj_of_dvd

theorem ordProj_dvd_ordProj_iff_dvd {a b : ℕ} (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (∀ p : ℕ, ordProj[p] a ∣ ordProj[p] b) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun hab p => ordProj_dvd_ordProj_of_dvd hb0 hab p⟩
  rw [← factorization_le_iff_dvd ha0 hb0]
  intro q
  rcases le_or_gt q 1 with (hq_le | hq1)
  · interval_cases q <;> simp
  exact (pow_dvd_pow_iff_le_right hq1).1 (h q)

@[deprecated (since := "2024-10-24")]
alias ord_proj_dvd_ord_proj_iff_dvd := ordProj_dvd_ordProj_iff_dvd

theorem ordCompl_dvd_ordCompl_of_dvd {a b : ℕ} (hab : a ∣ b) (p : ℕ) :
    ordCompl[p] a ∣ ordCompl[p] b := by
  rcases em' p.Prime with (pp | pp)
  · simp [pp, hab]
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  rcases eq_or_ne a 0 with (rfl | ha0)
  · cases hb0 (zero_dvd_iff.1 hab)
  have ha := (Nat.div_pos (ordProj_le p ha0) (ordProj_pos a p)).ne'
  have hb := (Nat.div_pos (ordProj_le p hb0) (ordProj_pos b p)).ne'
  rw [← factorization_le_iff_dvd ha hb, factorization_ordCompl a p, factorization_ordCompl b p]
  intro q
  rcases eq_or_ne q p with (rfl | hqp)
  · simp
  simp_rw [erase_ne hqp]
  exact (factorization_le_iff_dvd ha0 hb0).2 hab q

@[deprecated (since := "2024-10-24")]
alias ord_compl_dvd_ord_compl_of_dvd := ordCompl_dvd_ordCompl_of_dvd

theorem ordCompl_dvd_ordCompl_iff_dvd (a b : ℕ) :
    (∀ p : ℕ, ordCompl[p] a ∣ ordCompl[p] b) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun hab p => ordCompl_dvd_ordCompl_of_dvd hab p⟩
  rcases eq_or_ne b 0 with (rfl | hb0)
  · simp
  if pa : a.Prime then ?_ else simpa [pa] using h a
  if pb : b.Prime then ?_ else simpa [pb] using h b
  rw [prime_dvd_prime_iff_eq pa pb]
  by_contra hab
  apply pa.ne_one
  rw [← Nat.dvd_one, ← Nat.mul_dvd_mul_iff_left hb0.bot_lt, mul_one]
  simpa [Prime.factorization_self pb, Prime.factorization pa, hab] using h b

@[deprecated (since := "2024-10-24")]
alias ord_compl_dvd_ord_compl_iff_dvd := ordCompl_dvd_ordCompl_iff_dvd

theorem dvd_iff_prime_pow_dvd_dvd (n d : ℕ) :
    d ∣ n ↔ ∀ p k : ℕ, Prime p → p ^ k ∣ d → p ^ k ∣ n := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  rcases eq_or_ne d 0 with (rfl | hd)
  · simp only [zero_dvd_iff, hn, false_iff, not_forall]
    exact ⟨2, n, prime_two, dvd_zero _, mt (le_of_dvd hn.bot_lt) (n.lt_two_pow_self).not_ge⟩
  refine ⟨fun h p k _ hpkd => dvd_trans hpkd h, ?_⟩
  rw [← factorization_prime_le_iff_dvd hd hn]
  intro h p pp
  simp_rw [← pp.pow_dvd_iff_le_factorization hn]
  exact h p _ pp (ordProj_dvd _ _)

theorem prod_primeFactors_dvd (n : ℕ) : ∏ p ∈ n.primeFactors, p ∣ n := by
  by_cases hn : n = 0
  · subst hn
    simp
  · simpa [prod_primeFactorsList hn] using (n.primeFactorsList : Multiset ℕ).toFinset_prod_dvd_prod

theorem factorization_gcd {a b : ℕ} (ha_pos : a ≠ 0) (hb_pos : b ≠ 0) :
    (gcd a b).factorization = a.factorization ⊓ b.factorization := by
  let dfac := a.factorization ⊓ b.factorization
  let d := dfac.prod (· ^ ·)
  have dfac_prime : ∀ p : ℕ, p ∈ dfac.support → Prime p := by
    intro p hp
    have : p ∈ a.primeFactorsList ∧ p ∈ b.primeFactorsList := by simpa [dfac] using hp
    exact prime_of_mem_primeFactorsList this.1
  have h1 : d.factorization = dfac := prod_pow_factorization_eq_self dfac_prime
  have hd_pos : d ≠ 0 := (factorizationEquiv.invFun ⟨dfac, dfac_prime⟩).2.ne'
  suffices d = gcd a b by rwa [← this]
  apply gcd_greatest
  · rw [← factorization_le_iff_dvd hd_pos ha_pos, h1]
    exact inf_le_left
  · rw [← factorization_le_iff_dvd hd_pos hb_pos, h1]
    exact inf_le_right
  · intro e hea heb
    rcases Decidable.eq_or_ne e 0 with (rfl | he_pos)
    · simp only [zero_dvd_iff] at hea
      contradiction
    have hea' := (factorization_le_iff_dvd he_pos ha_pos).mpr hea
    have heb' := (factorization_le_iff_dvd he_pos hb_pos).mpr heb
    simp [dfac, ← factorization_le_iff_dvd he_pos hd_pos, h1, hea', heb']

theorem factorization_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).factorization = a.factorization ⊔ b.factorization := by
  rw [← add_right_inj (a.gcd b).factorization, ←
    factorization_mul (mt gcd_eq_zero_iff.1 fun h => ha h.1) (lcm_ne_zero ha hb), gcd_mul_lcm,
    factorization_gcd ha hb, factorization_mul ha hb]
  ext1
  exact (min_add_max _ _).symm

variable (a b)

@[simp]
lemma factorizationLCMLeft_zero_left : factorizationLCMLeft 0 b = 1 := by
  simp [factorizationLCMLeft]

@[simp]
lemma factorizationLCMLeft_zero_right : factorizationLCMLeft a 0 = 1 := by
  simp [factorizationLCMLeft]

@[simp]
lemma factorizationLCRight_zero_left : factorizationLCMRight 0 b = 1 := by
  simp [factorizationLCMRight]
@[simp]
lemma factorizationLCMRight_zero_right : factorizationLCMRight a 0 = 1 := by
  simp [factorizationLCMRight]

lemma factorizationLCMLeft_pos :
    0 < factorizationLCMLeft a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMLeft, Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p ≤ a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2
  · simp only [h, reduceIte, one_ne_zero] at H

lemma factorizationLCMRight_pos :
    0 < factorizationLCMRight a b := by
  apply Nat.pos_of_ne_zero
  rw [factorizationLCMRight, Finsupp.prod_ne_zero_iff]
  intro p _ H
  by_cases h : b.factorization p ≤ a.factorization p
  · simp only [h, reduceIte, pow_eq_zero_iff', ne_eq, reduceCtorEq] at H
  · simp only [h, ↓reduceIte, pow_eq_zero_iff', ne_eq] at H
    simpa [H.1] using H.2

lemma coprime_factorizationLCMLeft_factorizationLCMRight :
    (factorizationLCMLeft a b).Coprime (factorizationLCMRight a b) := by
  rw [factorizationLCMLeft, factorizationLCMRight]
  refine coprime_prod_left_iff.mpr fun p hp ↦ coprime_prod_right_iff.mpr fun q hq ↦ ?_
  dsimp only; split_ifs with h h'
  any_goals simp only [coprime_one_right_eq_true, coprime_one_left_eq_true]
  refine coprime_pow_primes _ _ (prime_of_mem_primeFactors hp) (prime_of_mem_primeFactors hq) ?_
  contrapose! h'; rwa [← h']

variable {a b}

lemma factorizationLCMLeft_mul_factorizationLCMRight (ha : a ≠ 0) (hb : b ≠ 0) :
    (factorizationLCMLeft a b) * (factorizationLCMRight a b) = lcm a b := by
  rw [← factorization_prod_pow_eq_self (lcm_ne_zero ha hb), factorizationLCMLeft,
    factorizationLCMRight, ← prod_mul]
  congr; ext p n; split_ifs <;> simp

variable (a b)

lemma factorizationLCMLeft_dvd_left : factorizationLCMLeft a b ∣ a := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [dvd_zero]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [factorizationLCMLeft]
  nth_rewrite 2 [← factorization_prod_pow_eq_self ha]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le le_rfl le
    · apply one_dvd
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inl <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]

lemma factorizationLCMRight_dvd_right : factorizationLCMRight a b ∣ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [factorizationLCMRight]
  rcases eq_or_ne b 0 with rfl | hb
  · simp only [dvd_zero]
  nth_rewrite 2 [← factorization_prod_pow_eq_self hb]
  rw [prod_of_support_subset (s := (lcm a b).factorization.support)]
  · apply Finset.prod_dvd_prod_of_dvd; rintro p -; dsimp only; split_ifs with le
    · apply one_dvd
    · rw [factorization_lcm ha hb]; apply pow_dvd_pow; exact sup_le (not_le.1 le).le le_rfl
  · intro p hp; rw [mem_support_iff] at hp ⊢
    rw [factorization_lcm ha hb]; exact (lt_sup_iff.mpr <| .inr <| Nat.pos_of_ne_zero hp).ne'
  · intros; rw [pow_zero]

@[to_additive sum_primeFactors_gcd_add_sum_primeFactors_mul]
theorem prod_primeFactors_gcd_mul_prod_primeFactors_mul {β : Type*} [CommMonoid β] (m n : ℕ)
    (f : ℕ → β) :
    (m.gcd n).primeFactors.prod f * (m * n).primeFactors.prod f =
      m.primeFactors.prod f * n.primeFactors.prod f := by
  obtain rfl | hm₀ := eq_or_ne m 0
  · simp
  obtain rfl | hn₀ := eq_or_ne n 0
  · simp
  · rw [primeFactors_mul hm₀ hn₀, primeFactors_gcd hm₀ hn₀, mul_comm, Finset.prod_union_inter]

theorem setOf_pow_dvd_eq_Icc_factorization {n p : ℕ} (pp : p.Prime) (hn : n ≠ 0) :
    { i : ℕ | i ≠ 0 ∧ p ^ i ∣ n } = Set.Icc 1 (n.factorization p) := by
  ext
  simp [Nat.lt_succ_iff, one_le_iff_ne_zero, pp.pow_dvd_iff_le_factorization hn]

/-- The set of positive powers of prime `p` that divide `n` is exactly the set of
positive natural numbers up to `n.factorization p`. -/
theorem Icc_factorization_eq_pow_dvd (n : ℕ) {p : ℕ} (pp : Prime p) :
    Icc 1 (n.factorization p) = {i ∈ Ico 1 n | p ^ i ∣ n} := by
  rcases eq_or_ne n 0 with (rfl | hn)
  · simp
  ext x
  simp only [mem_Icc, Finset.mem_filter, mem_Ico, and_assoc, and_congr_right_iff,
    pp.pow_dvd_iff_le_factorization hn, iff_and_self]
  exact fun _ H => lt_of_le_of_lt H (factorization_lt p hn)

theorem factorization_eq_card_pow_dvd (n : ℕ) {p : ℕ} (pp : p.Prime) :
    n.factorization p = #{i ∈ Ico 1 n | p ^ i ∣ n} := by
  simp [← Icc_factorization_eq_pow_dvd n pp]

theorem Ico_filter_pow_dvd_eq {n p b : ℕ} (pp : p.Prime) (hn : n ≠ 0) (hb : n ≤ p ^ b) :
    {i ∈ Ico 1 n | p ^ i ∣ n} = {i ∈ Icc 1 b | p ^ i ∣ n} := by
  ext x
  simp only [Finset.mem_filter, mem_Ico, mem_Icc, and_congr_left_iff, and_congr_right_iff]
  rintro h1 -
  exact iff_of_true (lt_of_pow_dvd_right hn pp.two_le h1) <|
    (Nat.pow_le_pow_iff_right pp.one_lt).1 <| (le_of_dvd hn.bot_lt h1).trans hb

/-! ### Factorization and coprimes -/


/-- If `p` is a prime factor of `a` then the power of `p` in `a` is the same that in `a * b`,
for any `b` coprime to `a`. -/
theorem factorization_eq_of_coprime_left {p a b : ℕ} (hab : Coprime a b)
    (hpa : p ∈ a.primeFactorsList) : (a * b).factorization p = a.factorization p := by
  rw [factorization_mul_apply_of_coprime hab, ← primeFactorsList_count_eq,
    ← primeFactorsList_count_eq,
    count_eq_zero_of_not_mem (coprime_primeFactorsList_disjoint hab hpa), add_zero]

/-- If `p` is a prime factor of `b` then the power of `p` in `b` is the same that in `a * b`,
for any `a` coprime to `b`. -/
theorem factorization_eq_of_coprime_right {p a b : ℕ} (hab : Coprime a b)
    (hpb : p ∈ b.primeFactorsList) : (a * b).factorization p = b.factorization p := by
  rw [mul_comm]
  exact factorization_eq_of_coprime_left (coprime_comm.mp hab) hpb

/-- Two positive naturals are equal if their prime padic valuations are equal -/
theorem eq_iff_prime_padicValNat_eq (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    a = b ↔ ∀ p : ℕ, p.Prime → padicValNat p a = padicValNat p b := by
  constructor
  · rintro rfl
    simp
  · intro h
    refine eq_of_factorization_eq ha hb fun p => ?_
    by_cases pp : p.Prime
    · simp [factorization_def, pp, h p pp]
    · simp [factorization_eq_zero_of_non_prime, pp]

theorem prod_pow_prime_padicValNat (n : Nat) (hn : n ≠ 0) (m : Nat) (pr : n < m) :
    ∏ p ∈ range m with p.Prime, p ^ padicValNat p n = n := by
  nth_rw 2 [← factorization_prod_pow_eq_self hn]
  rw [eq_comm]
  apply Finset.prod_subset_one_on_sdiff
  · exact fun p hp => Finset.mem_filter.mpr ⟨Finset.mem_range.2 <| pr.trans_le' <|
      le_of_mem_primeFactors hp, prime_of_mem_primeFactors hp⟩
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
    rw [← factorization_def n (Finset.mem_filter.mp hp1).2]
    simp [Finsupp.notMem_support_iff.mp hp2]
  · intro p hp
    simp [factorization_def n (prime_of_mem_primeFactors hp)]

/-! ### Lemmas about factorizations of particular functions -/


-- TODO: Port lemmas from `Data/Nat/Multiplicity` to here, re-written in terms of `factorization`
/-- Exactly `n / p` naturals in `[1, n]` are multiples of `p`.
See `Nat.card_multiples'` for an alternative spelling of the statement. -/
theorem card_multiples (n p : ℕ) : #{e ∈ range n | p ∣ e + 1} = n / p := by
  induction' n with n hn
  · simp
  simp [Nat.succ_div, add_ite, add_zero, Finset.range_succ, filter_insert, apply_ite card,
    card_insert_of_notMem, hn]

/-- Exactly `n / p` naturals in `(0, n]` are multiples of `p`. -/
theorem Ioc_filter_dvd_card_eq_div (n p : ℕ) : #{x ∈ Ioc 0 n | p ∣ x} = n / p := by
  induction' n with n IH
  · simp
  -- TODO: Golf away `h1` after Yaël PRs a lemma asserting this
  have h1 : Ioc 0 n.succ = insert n.succ (Ioc 0 n) := by
    rcases n.eq_zero_or_pos with (rfl | hn)
    · simp
    simp_rw [← Ico_add_one_add_one_eq_Ioc, Ico_insert_right (add_le_add_right hn.le 1),
      Ico_add_one_right_eq_Icc]
  simp [Nat.succ_div, add_ite, add_zero, h1, filter_insert, apply_ite card, card_insert_eq_ite, IH,
    Finset.mem_filter, mem_Ioc, not_le.2 (lt_add_one n)]

/-- There are exactly `⌊N/n⌋` positive multiples of `n` that are `≤ N`.
See `Nat.card_multiples` for a "shifted-by-one" version. -/
lemma card_multiples' (N n : ℕ) : #{k ∈ range N.succ | k ≠ 0 ∧ n ∣ k} = N / n := by
  induction N with
    | zero => simp [Finset.filter_false_of_mem]
    | succ N ih =>
        rw [Finset.range_succ, Finset.filter_insert]
        by_cases h : n ∣ N.succ
        · simp [h, succ_div_of_dvd, ih]
        · simp [h, succ_div_of_not_dvd, ih]

end Nat
