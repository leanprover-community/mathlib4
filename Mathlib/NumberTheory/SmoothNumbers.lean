/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Smooth numbers

We define the set `Nat.smoothNumbers n` consisting of the positive natural numbers all of
whose prime factors are strictly less than `n`.

We also define the finite set `Nat.primesBelow n` to be the set of prime numbers less than `n`.

The main definition `Nat.equivProdNatSmoothNumbers` establishes the bijection between
`ℕ × (smoothNumbers p)` and `smoothNumbers (p+1)` given by sending `(e, n)` to `p^e * n`.
Here `p` is a prime number.

Additionally, we define `Nat.smoothNumbersUpTo N n` as the `Finset` of `n`-smooth numbers
up to and including `N`, and similarly `Nat.roughNumbersUpTo` for its complement in `{1, ..., N}`,
and we provide some API, in particular bounds for their cardinalities; see
`Nat.smoothNumbersUpTo_card_le` and `Nat.roughNumbersUpTo_card_le`.
-/

namespace Nat

/-- `primesBelow n` is the set of primes less than `n` as a finset. -/
def primesBelow (n : ℕ) : Finset ℕ := (Finset.range n).filter (fun p ↦ p.Prime)

@[simp]
lemma primesBelow_zero : primesBelow 0 = ∅ := by
  rw [primesBelow, Finset.range_zero, Finset.filter_empty]

lemma mem_primesBelow {k n : ℕ} :
    n ∈ primesBelow k ↔ n < k ∧ n.Prime := by simp [primesBelow]

lemma prime_of_mem_primesBelow {p n : ℕ} (h : p ∈ n.primesBelow) : p.Prime :=
  (Finset.mem_filter.mp h).2

lemma lt_of_mem_primesBelow {p n : ℕ} (h : p ∈ n.primesBelow) : p < n :=
  Finset.mem_range.mp <| Finset.mem_of_mem_filter p h

lemma primesBelow_succ (n : ℕ) :
    primesBelow n.succ = if n.Prime then insert n (primesBelow n) else primesBelow n := by
  rw [primesBelow, primesBelow, Finset.range_succ, Finset.filter_insert]

lemma not_mem_primesBelow (n : ℕ) : n ∉ primesBelow n :=
  fun hn ↦ (lt_of_mem_primesBelow hn).false

/-- `smoothNumbers n` is the set of *`n`-smooth positive natural numbers*, i.e., the
positive natural numbers all of whose prime factors are less than `n`. -/
def smoothNumbers (n : ℕ) : Set ℕ := {m | m ≠ 0 ∧ ∀ p ∈ factors m, p < n}

lemma mem_smoothNumbers {n m : ℕ} : m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ∈ factors m, p < n :=
  Iff.rfl

/-- Membership in `Nat.smoothNumbers n` is decidable. -/
instance (n : ℕ) : DecidablePred (· ∈ smoothNumbers n) :=
  inferInstanceAs <| DecidablePred fun x ↦ x ∈ {m | m ≠ 0 ∧ ∀ p ∈ factors m, p < n}

/-- A number that divides an `n`-smooth number is itself `n`-smooth. -/
lemma mem_smoothNumbers_of_dvd {n m k : ℕ} (h : m ∈ smoothNumbers n) (h' : k ∣ m) (hk : k ≠ 0) :
    k ∈ smoothNumbers n := by
  rw [mem_smoothNumbers] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  refine ⟨hk, fun p hp ↦ h₂ p ?_⟩
  rw [mem_factors <| by assumption] at hp ⊢
  exact ⟨hp.1, hp.2.trans h'⟩

/-- `m` is `n`-smooth if and only if `m` is nonzero and all prime divisors `≤ m` of `m`
are less than `n`. -/
lemma mem_smoothNumbers_iff_forall_le  {n m : ℕ} :
    m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ≤ m, p.Prime → p ∣ m → p < n := by
  simp_rw [mem_smoothNumbers, mem_factors']
  exact ⟨fun ⟨H₀, H₁⟩ ↦ ⟨H₀, fun p _ hp₂ hp₃ ↦ H₁ p ⟨hp₂, hp₃, H₀⟩⟩,
    fun ⟨H₀, H₁⟩ ↦
      ⟨H₀, fun p ⟨hp₁, hp₂, hp₃⟩ ↦ H₁ p (Nat.le_of_dvd (Nat.pos_of_ne_zero hp₃) hp₂) hp₁ hp₂⟩⟩

/-- `m` is `n`-smooth if and only if all prime divisors of `m` are less than `n`. -/
lemma mem_smoothNumbers' {n m : ℕ} : m ∈ smoothNumbers n ↔ ∀ p, p.Prime → p ∣ m → p < n := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes n
  rw [mem_smoothNumbers_iff_forall_le]
  exact ⟨fun ⟨H₀, H₁⟩ ↦ fun p hp₁ hp₂ ↦ H₁ p (Nat.le_of_dvd (Nat.pos_of_ne_zero H₀) hp₂) hp₁ hp₂,
         fun H ↦ ⟨fun h ↦ ((H p hp₂ <| h.symm ▸ dvd_zero p).trans_le hp₁).false, fun p _ ↦ H p⟩⟩

lemma ne_zero_of_mem_smoothNumbers {n m : ℕ} (h : m ∈ smoothNumbers n) : m ≠ 0 :=
  (mem_smoothNumbers_iff_forall_le.mp h).1

@[simp]
lemma smoothNumbers_zero : smoothNumbers 0 = {1} := by
  ext m
  rw [Set.mem_singleton_iff, mem_smoothNumbers]
  simp_rw [not_lt_zero]
  rw [← List.eq_nil_iff_forall_not_mem, factors_eq_nil, and_or_left, not_and_self_iff, false_or,
    ne_and_eq_iff_right zero_ne_one]

/-- The product of the prime factors of `n` that are less than `N` is an `N`-smooth number. -/
lemma prod_mem_smoothNumbers (n N : ℕ) : (n.factors.filter (· < N)).prod ∈ smoothNumbers N := by
  have h₀ : (n.factors.filter (· < N)).prod ≠ 0 :=
    List.prod_ne_zero fun h ↦ (pos_of_mem_factors (List.mem_of_mem_filter h)).false
  refine ⟨h₀, fun p hp ↦ ?_⟩
  obtain ⟨H₁, H₂⟩ := (mem_factors h₀).mp hp
  simpa only [decide_eq_true_eq] using List.of_mem_filter <| mem_list_primes_of_dvd_prod H₁.prime
    (fun _ hq ↦ (prime_of_mem_factors (List.mem_of_mem_filter hq)).prime) H₂

/-- The sets of `N`-smooth and of `(N+1)`-smooth numbers are the same when `N` is not prime.
See `Nat.equivProdNatSmoothNumbers` for when `N` is prime. -/
lemma smoothNumbers_succ {N : ℕ} (hN : ¬ N.Prime) : N.succ.smoothNumbers = N.smoothNumbers := by
  ext m
  refine ⟨fun hm ↦ ⟨hm.1, fun p hp ↦ ?_⟩,
         fun hm ↦ ⟨hm.1, fun p hp ↦ (hm.2 p hp).trans <| lt.base N⟩⟩
  exact lt_of_le_of_ne (lt_succ.mp <| hm.2 p hp) fun h ↦ hN <| h ▸ prime_of_mem_factors hp

@[simp] lemma smoothNumbers_one : smoothNumbers 1 = {1} := by
  simp (config := {decide := true}) [smoothNumbers_succ]

@[gcongr] lemma smoothNumbers_mono {N M : ℕ} (hNM : N ≤ M) : N.smoothNumbers ⊆ M.smoothNumbers :=
  fun _ hx ↦ ⟨hx.1, fun p hp => (hx.2 p hp).trans_le hNM⟩

/-- The non-zero non-`N`-smooth numbers are `≥ N`. -/
lemma smoothNumbers_compl (N : ℕ) : (N.smoothNumbers)ᶜ \ {0} ⊆ {n | N ≤ n} := by
  intro n hn
  simp only [Set.mem_compl_iff, mem_smoothNumbers, Set.mem_diff, ne_eq, not_and, not_forall,
    not_lt, exists_prop, Set.mem_singleton_iff] at hn
  obtain ⟨m, hm₁, hm₂⟩ := hn.1 hn.2
  exact hm₂.trans <| le_of_mem_factors hm₁

/-- If `p` is positive and `n` is `p`-smooth, then every product `p^e * n` is `(p+1)`-smooth. -/
lemma pow_mul_mem_smoothNumbers {p n : ℕ} (hp : p ≠ 0) (e : ℕ) (hn : n ∈ smoothNumbers p) :
    p ^ e * n ∈ smoothNumbers (succ p) := by
  have hp' := pow_ne_zero e hp
  refine ⟨mul_ne_zero hp' hn.1, fun q hq ↦ ?_⟩
  rcases (mem_factors_mul hp' hn.1).mp hq with H | H
  · rw [mem_factors hp'] at H
    exact lt_succ.mpr <| le_of_dvd hp.bot_lt <| H.1.dvd_of_dvd_pow H.2
  · exact (hn.2 q H).trans <| lt_succ_self p

/-- If `p` is a prime and `n` is `p`-smooth, then `p` and `n` are coprime. -/
lemma Prime.smoothNumbers_coprime {p n : ℕ} (hp : p.Prime) (hn : n ∈ smoothNumbers p) :
    Nat.Coprime p n := by
  rw [hp.coprime_iff_not_dvd, ← mem_factors_iff_dvd hn.1 hp]
  exact fun H ↦ (hn.2 p H).false

/-- If `f : ℕ → F` is multiplicative on coprime arguments, `p` is a prime and `m` is `p`-smooth,
then `f (p^e * m) = f (p^e) * f m`. -/
lemma map_prime_pow_mul {F : Type*} [CommSemiring F] {f : ℕ → F}
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n) {p : ℕ} (hp : p.Prime) (e : ℕ)
    {m : p.smoothNumbers} :
    f (p ^ e * m) = f (p ^ e) * f m :=
  hmul <| Coprime.pow_left _ <| hp.smoothNumbers_coprime <| Subtype.mem m

open List Perm in
/-- We establish the bijection from `ℕ × smoothNumbers p` to `smoothNumbers (p+1)`
given by `(e, n) ↦ p^e * n` when `p` is a prime. See `Nat.smoothNumbers_succ` for
when `p` is not prime. -/
def equivProdNatSmoothNumbers {p : ℕ} (hp: p.Prime) :
    ℕ × smoothNumbers p ≃ smoothNumbers p.succ where
  toFun := fun ⟨e, n⟩ ↦ ⟨p ^ e * n, pow_mul_mem_smoothNumbers hp.ne_zero e n.2⟩
  invFun := fun ⟨m, _⟩  ↦ (m.factorization p,
                            ⟨(m.factors.filter (· < p)).prod, prod_mem_smoothNumbers ..⟩)
  left_inv := by
    rintro ⟨e, m, hm₀, hm⟩
    simp (config := { etaStruct := .all }) only
      [Set.coe_setOf, Set.mem_setOf_eq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · rw [factorization_mul (pos_iff_ne_zero.mp <| pos_pow_of_pos e hp.pos) hm₀]
      simp only [factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul,
        Pi.coe_nat, cast_id, Pi.add_apply, Pi.mul_apply, hp.factorization_self,
        mul_one, add_right_eq_self]
      rw [← factors_count_eq, count_eq_zero]
      exact fun H ↦ (hm p H).false
    · nth_rw 2 [← prod_factors hm₀]
      refine prod_eq <| (filter _ <| perm_factors_mul (pow_ne_zero e hp.ne_zero) hm₀).trans ?_
      rw [filter_append, hp.factors_pow,
          filter_eq_nil.mpr fun q hq ↦ by rw [mem_replicate] at hq; simp [hq.2],
          nil_append, filter_eq_self.mpr fun q hq ↦ by simp [hm q hq]]
  right_inv := by
    rintro ⟨m, hm₀, hm⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
    rw [← factors_count_eq, ← prod_replicate, ← prod_append]
    nth_rw 3 [← prod_factors hm₀]
    have : m.factors.filter (· = p) = m.factors.filter (¬ · < p)
    · refine (filter_congr' fun q hq ↦ ?_).symm
      have H : ¬ p < q := fun hf ↦ Nat.lt_le_asymm hf <| lt_succ_iff.mp (hm q hq)
      simp only [not_lt, le_iff_eq_or_lt, H, or_false, eq_comm, true_eq_decide_iff]
    refine prod_eq <| (filter_eq m.factors p).symm ▸ this ▸ perm_append_comm.trans ?_
    convert filter_append_perm ..
    simp only [not_lt]
    simp only [decide_not, Bool.not_not, lt_iff_not_ge]

@[simp]
lemma equivProdNatSmoothNumbers_apply {p e m : ℕ} (hp: p.Prime) (hm : m ∈ p.smoothNumbers) :
    equivProdNatSmoothNumbers hp (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
lemma equivProdNatSmoothNumbers_apply' {p : ℕ} (hp: p.Prime) (x : ℕ × p.smoothNumbers) :
    equivProdNatSmoothNumbers hp x = p ^ x.1 * x.2 := rfl

/-- The `k`-smooth numbers up to and including `N` as a `Finset` -/
def smoothNumbersUpTo (N k : ℕ) : Finset ℕ :=
    (Finset.range N.succ).filter (· ∈ smoothNumbers k)

lemma mem_smoothNumbersUpTo {N k n : ℕ} :
    n ∈ smoothNumbersUpTo N k ↔ n ≤ N ∧ n ∈ smoothNumbers k := by
  simp [smoothNumbersUpTo, lt_succ]

/-- The positive non-`k`-smooth (so "`k`-rough") numbers up to and including `N` as a `Finset` -/
def roughNumbersUpTo (N k : ℕ) : Finset ℕ :=
    (Finset.range N.succ).filter (fun n ↦ n ≠ 0 ∧ n ∉ smoothNumbers k)

lemma smoothNumbersUpTo_card_add_roughNumbersUpTo_card (N k : ℕ) :
    (smoothNumbersUpTo N k).card + (roughNumbersUpTo N k).card = N := by
  rw [smoothNumbersUpTo, roughNumbersUpTo,
    ← Finset.card_union_eq <| Finset.disjoint_filter.mpr fun n _ hn₂ h ↦ h.2 hn₂,
    Finset.filter_union_right]
  suffices : Finset.card (Finset.filter (fun x ↦ x ≠ 0) (Finset.range (succ N))) = N
  · convert this with n
    have hn : n ∈ smoothNumbers k → n ≠ 0 := ne_zero_of_mem_smoothNumbers
    tauto
  · rw [Finset.filter_ne', Finset.card_erase_of_mem <| Finset.mem_range_succ_iff.mpr <| zero_le N]
    simp

/-- A `k`-smooth number can be written as a square times a product of distinct primes `< k`. -/
lemma eq_prod_primes_mul_sq_of_mem_smoothNumbers {n k : ℕ} (h : n ∈ smoothNumbers k) :
    ∃ s ∈ k.primesBelow.powerset, ∃ m, n = m ^ 2 * (s.prod id) := by
  obtain ⟨l, m, H₁, H₂⟩ := sq_mul_squarefree n
  have hl : l ∈ smoothNumbers k :=
    mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁) <| Squarefree.ne_zero H₂
  refine ⟨l.factors.toFinset, ?_,  m, ?_⟩
  · simp only [toFinset_factors, Finset.mem_powerset]
    refine fun p hp ↦ mem_primesBelow.mpr ⟨?_, (mem_primeFactors.mp hp).1⟩
    rw [mem_primeFactors] at hp
    exact mem_smoothNumbers'.mp hl p hp.1 hp.2.1
  rw [← H₁]
  congr
  simp only [toFinset_factors]
  exact (prod_primeFactors_of_squarefree H₂).symm

/-- The set of `k`-smooth numbers `≤ N` is contained in the set of numbers of the form `m^2 * P`,
where `m ≤ √N` and `P` is a product of distinct primes `< k`. -/
lemma smoothNumbersUpTo_subset_image (N k : ℕ) :
    smoothNumbersUpTo N k ⊆ Finset.image (fun (s, m) ↦ m ^ 2 * (s.prod id))
      (k.primesBelow.powerset ×ˢ (Finset.range N.sqrt.succ).erase 0) := by
  intro n hn
  obtain ⟨hn₁, hn₂⟩ := mem_smoothNumbersUpTo.mp hn
  obtain ⟨s, hs, m, hm⟩ := eq_prod_primes_mul_sq_of_mem_smoothNumbers hn₂
  simp only [id_eq, Finset.mem_range, zero_lt_succ, not_true_eq_false, Finset.mem_image,
    Finset.mem_product, Finset.mem_powerset, Finset.mem_erase, Prod.exists]
  refine ⟨s, m, ⟨Finset.mem_powerset.mp hs, ?_, ?_⟩, hm.symm⟩
  · have := hm ▸ ne_zero_of_mem_smoothNumbers hn₂
    simp only [ne_eq, _root_.mul_eq_zero, sq_eq_zero_iff, not_or] at this
    exact this.1
  · rw [lt_succ, le_sqrt']
    refine LE.le.trans ?_ (hm ▸ hn₁)
    nth_rw 1 [← mul_one (m ^ 2)]
    exact mul_le_mul_left' (Finset.one_le_prod' fun p hp ↦
      (prime_of_mem_primesBelow <| Finset.mem_powerset.mp hs hp).one_lt.le) _

/-- The cardinality of the set of `k`-smooth numbers `≤ N` is bounded by `2^π(k-1) * √N`. -/
lemma smoothNumbersUpTo_card_le (N k : ℕ) :
    (smoothNumbersUpTo N k).card ≤ 2 ^ k.primesBelow.card * N.sqrt := by
  convert (Finset.card_le_card <| smoothNumbersUpTo_subset_image N k).trans <|
    Finset.card_image_le
  simp

/-- The set of `k`-rough numbers `≤ N` can be written as the union of the sets of multiples `≤ N`
of primes `k ≤ p ≤ N`. -/
lemma roughNumbersUpTo_eq_biUnion (N k) :
    roughNumbersUpTo N k =
      (N.succ.primesBelow \ k.primesBelow).biUnion
        fun p ↦ (Finset.range N.succ).filter (fun m ↦ m ≠ 0 ∧ p ∣ m) := by
  ext m
  simp only [roughNumbersUpTo, mem_smoothNumbers_iff_forall_le, not_and, not_forall,
    not_lt, exists_prop, exists_and_left, Finset.mem_range, not_le, Finset.mem_filter,
    Finset.filter_congr_decidable, Finset.mem_biUnion, Finset.mem_sdiff, mem_primesBelow,
    show ∀ P Q : Prop, P ∧ (P → Q) ↔ P ∧ Q by tauto]
  simp_rw [← exists_and_left, ← not_lt]
  refine exists_congr fun p ↦ ?_
  have H₁ : m ≠ 0 → p ∣ m → m < N.succ → p < N.succ :=
    fun h₁ h₂ h₃ ↦ (le_of_dvd (Nat.pos_of_ne_zero h₁) h₂).trans_lt h₃
  have H₂ : m ≠ 0 → p ∣ m → ¬ m < p :=
    fun h₁ h₂ ↦ not_lt.mpr <| le_of_dvd (Nat.pos_of_ne_zero h₁) h₂
  tauto

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by the sum of `⌊N/p⌋`
over the primes `k ≤ p ≤ N`. -/
lemma roughNumbersUpTo_card_le (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤ (N.succ.primesBelow \ k.primesBelow).sum (fun p ↦ N / p) := by
  rw [roughNumbersUpTo_eq_biUnion]
  exact Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun p _ ↦ (card_multiples' N p).le

end Nat
