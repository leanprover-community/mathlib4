/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Smooth numbers

For `s : Finset ℕ` we define the set `Nat.factoredNumbers s` of "`s`-factored numbers"
consisting of the positive natural numbers all of whose prime factors are in `s`, and
we provide some API for this.

We then define the set `Nat.smoothNumbers n` consisting of the positive natural numbers all of
whose prime factors are strictly less than `n`. This is the special case `s = Finset.range n`
of the set of `s`-factored numbers.

We also define the finite set `Nat.primesBelow n` to be the set of prime numbers less than `n`.

The main definition `Nat.equivProdNatSmoothNumbers` establishes the bijection between
`ℕ × (smoothNumbers p)` and `smoothNumbers (p+1)` given by sending `(e, n)` to `p^e * n`.
Here `p` is a prime number. It is obtained from the more general bijection between
`ℕ × (factoredNumbers s)` and `factoredNumbers (s ∪ {p})`; see `Nat.equivProdNatFactoredNumbers`.

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


/-!
### `s`-factored numbers
-/

/-- `factoredNumbers s`, for a finite set `s` of natural numbers, is the set of positive natural
numbers all of whose prime factors are in `s`. -/
def factoredNumbers (s : Finset ℕ) : Set ℕ := {m | m ≠ 0 ∧ ∀ p ∈ factors m, p ∈ s}

lemma mem_factoredNumbers {s : Finset ℕ} {m : ℕ} :
    m ∈ factoredNumbers s ↔ m ≠ 0 ∧ ∀ p ∈ factors m, p ∈ s :=
  Iff.rfl

/-- Membership in `Nat.factoredNumbers n` is decidable. -/
instance (s : Finset ℕ) : DecidablePred (· ∈ factoredNumbers s) :=
  inferInstanceAs <| DecidablePred fun x ↦ x ∈ {m | m ≠ 0 ∧ ∀ p ∈ factors m, p ∈ s}

/-- A number that divides an `s`-factored number is itself `s`-factored. -/
lemma mem_factoredNumbers_of_dvd {s : Finset ℕ} {m k : ℕ} (h : m ∈ factoredNumbers s)
    (h' : k ∣ m) :
    k ∈ factoredNumbers s := by
  obtain ⟨h₁, h₂⟩ := h
  have hk := ne_zero_of_dvd_ne_zero h₁ h'
  refine ⟨hk, fun p hp ↦ h₂ p ?_⟩
  rw [mem_factors <| by assumption] at hp ⊢
  exact ⟨hp.1, hp.2.trans h'⟩

/-- `m` is `s`-factored if and only if `m` is nonzero and all prime divisors `≤ m` of `m`
are in `s`. -/
lemma mem_factoredNumbers_iff_forall_le {s : Finset ℕ} {m : ℕ} :
    m ∈ factoredNumbers s ↔ m ≠ 0 ∧ ∀ p ≤ m, p.Prime → p ∣ m → p ∈ s := by
  simp_rw [mem_factoredNumbers, mem_factors']
  exact ⟨fun ⟨H₀, H₁⟩ ↦ ⟨H₀, fun p _ hp₂ hp₃ ↦ H₁ p ⟨hp₂, hp₃, H₀⟩⟩,
    fun ⟨H₀, H₁⟩ ↦
      ⟨H₀, fun p ⟨hp₁, hp₂, hp₃⟩ ↦ H₁ p (le_of_dvd (Nat.pos_of_ne_zero hp₃) hp₂) hp₁ hp₂⟩⟩

/-- `m` is `s`-factored if and only if all prime divisors of `m` are in `s`. -/
lemma mem_factoredNumbers' {s : Finset ℕ} {m : ℕ} :
    m ∈ factoredNumbers s ↔ ∀ p, p.Prime → p ∣ m → p ∈ s := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_infinite_primes (1 + Finset.sup s id)
  rw [mem_factoredNumbers_iff_forall_le]
  refine ⟨fun ⟨H₀, H₁⟩ ↦ fun p hp₁ hp₂ ↦ H₁ p (le_of_dvd (Nat.pos_of_ne_zero H₀) hp₂) hp₁ hp₂,
         fun H ↦ ⟨fun h ↦ lt_irrefl p ?_, fun p _ ↦ H p⟩⟩
  calc
    p ≤ s.sup id := Finset.le_sup (f := @id ℕ) <| H p hp₂ <| h.symm ▸ dvd_zero p
    _ < 1 + s.sup id := lt_one_add _
    _ ≤ p := hp₁

lemma ne_zero_of_mem_factoredNumbers {s : Finset ℕ} {m : ℕ} (h : m ∈ factoredNumbers s) : m ≠ 0 :=
  h.1

@[simp]
lemma factoredNumbers_empty : factoredNumbers ∅ = {1} := by
  ext m
  simp only [mem_factoredNumbers, Finset.not_mem_empty, ← List.eq_nil_iff_forall_not_mem,
    factors_eq_nil, and_or_left, not_and_self_iff, ne_and_eq_iff_right zero_ne_one, false_or,
    Set.mem_singleton_iff]

/-- The product of the prime factors of `n` that are in `s` is an `s`-factored number. -/
lemma prod_mem_factoredNumbers (s : Finset ℕ) (n : ℕ) :
    (n.factors.filter (· ∈ s)).prod ∈ factoredNumbers s := by
  have h₀ : (n.factors.filter (· ∈ s)).prod ≠ 0 :=
    List.prod_ne_zero fun h ↦ (pos_of_mem_factors (List.mem_of_mem_filter h)).false
  refine ⟨h₀, fun p hp ↦ ?_⟩
  obtain ⟨H₁, H₂⟩ := (mem_factors h₀).mp hp
  simpa only [decide_eq_true_eq] using List.of_mem_filter <| mem_list_primes_of_dvd_prod H₁.prime
    (fun _ hq ↦ (prime_of_mem_factors (List.mem_of_mem_filter hq)).prime) H₂

/-- The sets of `s`-factored and of `s ∪ {N}`-factored numbers are the same when `N` is not prime.
See `Nat.equivProdNatFactoredNumbers` for when `N` is prime. -/
lemma factoredNumbers_insert (s : Finset ℕ) {N : ℕ} (hN : ¬ N.Prime) :
    factoredNumbers (insert N s) = factoredNumbers s := by
  ext m
  refine ⟨fun hm ↦ ⟨hm.1, fun p hp ↦ ?_⟩,
          fun hm ↦ ⟨hm.1, fun p hp ↦ Finset.mem_insert_of_mem <| hm.2 p hp⟩⟩
  exact Finset.mem_of_mem_insert_of_ne (hm.2 p hp) fun h ↦ hN <| h ▸ prime_of_mem_factors hp

@[gcongr] lemma factoredNumbers_mono {s t : Finset ℕ} (hst : s ≤ t) :
    factoredNumbers s ⊆ factoredNumbers t :=
  fun _ hx ↦ ⟨hx.1, fun p hp ↦ hst <| hx.2 p hp⟩

/-- The non-zero non-`s`-factored numbers are `≥ N` when `s` contains all primes less than `N`. -/
lemma factoredNumbers_compl {N : ℕ} {s : Finset ℕ} (h : primesBelow N ≤ s) :
    (factoredNumbers s)ᶜ \ {0} ⊆ {n | N ≤ n} := by
  intro n hn
  simp only [Set.mem_compl_iff, mem_factoredNumbers, Set.mem_diff, ne_eq, not_and, not_forall,
    not_lt, exists_prop, Set.mem_singleton_iff] at hn
  simp only [Set.mem_setOf_eq]
  obtain ⟨p, hp₁, hp₂⟩ := hn.1 hn.2
  have : N ≤ p := by
    contrapose! hp₂
    exact h <| mem_primesBelow.mpr ⟨hp₂, prime_of_mem_factors hp₁⟩
  exact this.trans <| le_of_mem_factors hp₁

/-- If `p` is a prime and `n` is `s`-factored, then every product `p^e * n`
is `s ∪ {p}`-factored. -/
lemma pow_mul_mem_factoredNumbers {s : Finset ℕ} {p n : ℕ} (hp : p.Prime) (e : ℕ)
    (hn : n ∈ factoredNumbers s) :
    p ^ e * n ∈ factoredNumbers (insert p s) := by
  have hp' := pow_ne_zero e hp.ne_zero
  refine ⟨mul_ne_zero hp' hn.1, fun q hq ↦ ?_⟩
  rcases (mem_factors_mul hp' hn.1).mp hq with H | H
  · rw [mem_factors hp'] at H
    rw [(prime_dvd_prime_iff_eq H.1 hp).mp <| H.1.dvd_of_dvd_pow H.2]
    exact Finset.mem_insert_self p s
  · exact Finset.mem_insert_of_mem <| hn.2 _ H

/-- If `p ∉ s` is a prime and `n` is `s`-factored, then `p` and `n` are coprime. -/
lemma Prime.factoredNumbers_coprime {s : Finset ℕ} {p n : ℕ} (hp : p.Prime) (hs : p ∉ s)
    (hn : n ∈ factoredNumbers s) :
    Nat.Coprime p n := by
  rw [hp.coprime_iff_not_dvd, ← mem_factors_iff_dvd hn.1 hp]
  exact fun H ↦ hs <| hn.2 p H

/-- If `f : ℕ → F` is multiplicative on coprime arguments, `p ∉ s` is a prime and `m`
is `s`-factored, then `f (p^e * m) = f (p^e) * f m`. -/
lemma factoredNumbers.map_prime_pow_mul {F : Type*} [CommSemiring F] {f : ℕ → F}
    (hmul : ∀ {m n}, Coprime m n → f (m * n) = f m * f n) {s : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hs : p ∉ s) (e : ℕ) {m : factoredNumbers s} :
    f (p ^ e * m) = f (p ^ e) * f m :=
  hmul <| Coprime.pow_left _ <| hp.factoredNumbers_coprime hs <| Subtype.mem m

open List Perm in
/-- We establish the bijection from `ℕ × factoredNumbers s` to `factoredNumbers (s ∪ {p})`
given by `(e, n) ↦ p^e * n` when `p ∉ s` is a prime. See `Nat.factoredNumbers_insert` for
when `p` is not prime. -/
def equivProdNatFactoredNumbers {s : Finset ℕ} {p : ℕ} (hp: p.Prime) (hs : p ∉ s) :
    ℕ × factoredNumbers s ≃ factoredNumbers (insert p s) where
  toFun := fun ⟨e, n⟩ ↦ ⟨p ^ e * n, pow_mul_mem_factoredNumbers hp e n.2⟩
  invFun := fun ⟨m, _⟩  ↦ (m.factorization p,
                            ⟨(m.factors.filter (· ∈ s)).prod, prod_mem_factoredNumbers ..⟩)
  left_inv := by
    rintro ⟨e, m, hm₀, hm⟩
    simp (config := { etaStruct := .all }) only
      [Set.coe_setOf, Set.mem_setOf_eq, Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · rw [factorization_mul (pos_iff_ne_zero.mp <| pos_pow_of_pos e hp.pos) hm₀]
      simp only [factorization_pow, Finsupp.coe_add, Finsupp.coe_smul, nsmul_eq_mul,
        Pi.natCast_def, cast_id, Pi.add_apply, Pi.mul_apply, hp.factorization_self,
        mul_one, add_right_eq_self]
      rw [← factors_count_eq, count_eq_zero]
      exact fun H ↦ hs (hm p H)
    · nth_rewrite 2 [← prod_factors hm₀]
      refine prod_eq <| (filter _ <| perm_factors_mul (pow_ne_zero e hp.ne_zero) hm₀).trans ?_
      rw [filter_append, hp.factors_pow,
          filter_eq_nil.mpr fun q hq ↦ by rw [mem_replicate] at hq; simp [hq.2, hs],
          nil_append, filter_eq_self.mpr fun q hq ↦ by simp only [hm q hq, decide_True]]
  right_inv := by
    rintro ⟨m, hm₀, hm⟩
    simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq]
    rw [← factors_count_eq, ← prod_replicate, ← prod_append]
    nth_rewrite 3 [← prod_factors hm₀]
    have : m.factors.filter (· = p) = m.factors.filter (¬ · ∈ s) := by
      refine (filter_congr' fun q hq ↦ ?_).symm
      simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      rcases Finset.mem_insert.mp <| hm _ hq with h | h
      · simp only [h, hs, not_false_eq_true]
      · simp only [h, not_true_eq_false, false_iff]
        exact fun H ↦ hs <| H ▸ h
    refine prod_eq <| (filter_eq m.factors p).symm ▸ this ▸ perm_append_comm.trans ?_
    simp only [decide_not]
    exact filter_append_perm (· ∈ s) (factors m)

@[simp]
lemma equivProdNatFactoredNumbers_apply {s : Finset ℕ} {p e m : ℕ} (hp: p.Prime) (hs : p ∉ s)
    (hm : m ∈ factoredNumbers s) :
    equivProdNatFactoredNumbers hp hs (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
lemma equivProdNatFactoredNumbers_apply' {s : Finset ℕ} {p : ℕ} (hp: p.Prime) (hs : p ∉ s)
    (x : ℕ × factoredNumbers s) :
    equivProdNatFactoredNumbers hp hs x = p ^ x.1 * x.2 := rfl


/-!
### `n`-smooth numbers
-/

/-- `smoothNumbers n` is the set of *`n`-smooth positive natural numbers*, i.e., the
positive natural numbers all of whose prime factors are less than `n`. -/
def smoothNumbers (n : ℕ) : Set ℕ := {m | m ≠ 0 ∧ ∀ p ∈ factors m, p < n}

lemma mem_smoothNumbers {n m : ℕ} : m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ∈ factors m, p < n :=
  Iff.rfl

/-- The `n`-smooth numbers agree with the `Finset.range n`-factored numbers. -/
lemma smoothNumbers_eq_factoredNumbers (n : ℕ) :
    smoothNumbers n = factoredNumbers (Finset.range n) := by
  simp only [smoothNumbers, ne_eq, mem_factors', and_imp, factoredNumbers, Finset.mem_range]

/-- Membership in `Nat.smoothNumbers n` is decidable. -/
instance (n : ℕ) : DecidablePred (· ∈ smoothNumbers n) :=
  inferInstanceAs <| DecidablePred fun x ↦ x ∈ {m | m ≠ 0 ∧ ∀ p ∈ factors m, p < n}

/-- A number that divides an `n`-smooth number is itself `n`-smooth. -/
lemma mem_smoothNumbers_of_dvd {n m k : ℕ} (h : m ∈ smoothNumbers n) (h' : k ∣ m) :
    k ∈ smoothNumbers n := by
  simp only [smoothNumbers_eq_factoredNumbers] at h ⊢
  exact mem_factoredNumbers_of_dvd h h'

/-- `m` is `n`-smooth if and only if `m` is nonzero and all prime divisors `≤ m` of `m`
are less than `n`. -/
lemma mem_smoothNumbers_iff_forall_le {n m : ℕ} :
    m ∈ smoothNumbers n ↔ m ≠ 0 ∧ ∀ p ≤ m, p.Prime → p ∣ m → p < n := by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers_iff_forall_le, Finset.mem_range]

/-- `m` is `n`-smooth if and only if all prime divisors of `m` are less than `n`. -/
lemma mem_smoothNumbers' {n m : ℕ} : m ∈ smoothNumbers n ↔ ∀ p, p.Prime → p ∣ m → p < n := by
  simp only [smoothNumbers_eq_factoredNumbers, mem_factoredNumbers', Finset.mem_range]

lemma ne_zero_of_mem_smoothNumbers {n m : ℕ} (h : m ∈ smoothNumbers n) : m ≠ 0 := h.1

@[simp]
lemma smoothNumbers_zero : smoothNumbers 0 = {1} := by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_zero, factoredNumbers_empty]

/-- The product of the prime factors of `n` that are less than `N` is an `N`-smooth number. -/
lemma prod_mem_smoothNumbers (n N : ℕ) : (n.factors.filter (· < N)).prod ∈ smoothNumbers N := by
  simp only [smoothNumbers_eq_factoredNumbers, ← Finset.mem_range, prod_mem_factoredNumbers]

/-- The sets of `N`-smooth and of `(N+1)`-smooth numbers are the same when `N` is not prime.
See `Nat.equivProdNatSmoothNumbers` for when `N` is prime. -/
lemma smoothNumbers_succ {N : ℕ} (hN : ¬ N.Prime) : N.succ.smoothNumbers = N.smoothNumbers := by
  simp only [smoothNumbers_eq_factoredNumbers, Finset.range_succ, factoredNumbers_insert _ hN]

@[simp] lemma smoothNumbers_one : smoothNumbers 1 = {1} := by
  simp (config := { decide := true }) only [not_false_eq_true, smoothNumbers_succ,
    smoothNumbers_zero]

@[gcongr] lemma smoothNumbers_mono {N M : ℕ} (hNM : N ≤ M) : N.smoothNumbers ⊆ M.smoothNumbers :=
  fun _ hx ↦ ⟨hx.1, fun p hp => (hx.2 p hp).trans_le hNM⟩

/-- The non-zero non-`N`-smooth numbers are `≥ N`. -/
lemma smoothNumbers_compl (N : ℕ) : (N.smoothNumbers)ᶜ \ {0} ⊆ {n | N ≤ n} := by
  simpa only [smoothNumbers_eq_factoredNumbers]
    using factoredNumbers_compl <| Finset.filter_subset _ (Finset.range N)

/-- If `p` is positive and `n` is `p`-smooth, then every product `p^e * n` is `(p+1)`-smooth. -/
lemma pow_mul_mem_smoothNumbers {p n : ℕ} (hp : p ≠ 0) (e : ℕ) (hn : n ∈ smoothNumbers p) :
    p ^ e * n ∈ smoothNumbers (succ p) := by
  -- This cannot be easily reduced to `pow_mul_mem_factoredNumbers`, as there `p.Prime` is needed.
  have : NoZeroDivisors ℕ := inferInstance -- this is needed twice --> speed-up
  have hp' := pow_ne_zero e hp
  refine ⟨mul_ne_zero hp' hn.1, fun q hq ↦ ?_⟩
  rcases (mem_factors_mul hp' hn.1).mp hq with H | H
  · rw [mem_factors hp'] at H
    exact lt_succ.mpr <| le_of_dvd hp.bot_lt <| H.1.dvd_of_dvd_pow H.2
  · exact (hn.2 q H).trans <| lt_succ_self p

/-- If `p` is a prime and `n` is `p`-smooth, then `p` and `n` are coprime. -/
lemma Prime.smoothNumbers_coprime {p n : ℕ} (hp : p.Prime) (hn : n ∈ smoothNumbers p) :
    Nat.Coprime p n := by
  simp only [smoothNumbers_eq_factoredNumbers] at hn
  exact hp.factoredNumbers_coprime Finset.not_mem_range_self hn

/-- If `f : ℕ → F` is multiplicative on coprime arguments, `p` is a prime and `m` is `p`-smooth,
then `f (p^e * m) = f (p^e) * f m`. -/
lemma map_prime_pow_mul {F : Type*} [CommSemiring F] {f : ℕ → F}
    (hmul : ∀ {m n}, Nat.Coprime m n → f (m * n) = f m * f n) {p : ℕ} (hp : p.Prime) (e : ℕ)
    {m : p.smoothNumbers} :
    f (p ^ e * m) = f (p ^ e) * f m :=
  hmul <| Coprime.pow_left _ <| hp.smoothNumbers_coprime <| Subtype.mem m

open List Perm Equiv in
/-- We establish the bijection from `ℕ × smoothNumbers p` to `smoothNumbers (p+1)`
given by `(e, n) ↦ p^e * n` when `p` is a prime. See `Nat.smoothNumbers_succ` for
when `p` is not prime. -/
def equivProdNatSmoothNumbers {p : ℕ} (hp: p.Prime) :
    ℕ × smoothNumbers p ≃ smoothNumbers p.succ :=
  ((prodCongrRight fun _ ↦ setCongr <| smoothNumbers_eq_factoredNumbers p).trans <|
    equivProdNatFactoredNumbers hp Finset.not_mem_range_self).trans <|
    setCongr <| (smoothNumbers_eq_factoredNumbers p.succ) ▸ Finset.range_succ ▸ rfl

@[simp]
lemma equivProdNatSmoothNumbers_apply {p e m : ℕ} (hp: p.Prime) (hm : m ∈ p.smoothNumbers) :
    equivProdNatSmoothNumbers hp (e, ⟨m, hm⟩) = p ^ e * m := rfl

@[simp]
lemma equivProdNatSmoothNumbers_apply' {p : ℕ} (hp: p.Prime) (x : ℕ × p.smoothNumbers) :
    equivProdNatSmoothNumbers hp x = p ^ x.1 * x.2 := rfl


/-!
### Smooth and rough numbers up to a bound

We consider the sets of smooth and non-smooth ("rough") positive natural numbers `≤ N`
and prove bounds for their sizes.
-/

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
    ← Finset.card_union_of_disjoint <| Finset.disjoint_filter.mpr fun n _ hn₂ h ↦ h.2 hn₂,
    Finset.filter_union_right]
  suffices Finset.card (Finset.filter (fun x ↦ x ≠ 0) (Finset.range (succ N))) = N by
    have hn' (n) : n ∈ smoothNumbers k ∨ n ≠ 0 ∧ n ∉ smoothNumbers k ↔ n ≠ 0 := by
      have : n ∈ smoothNumbers k → n ≠ 0 := ne_zero_of_mem_smoothNumbers
      refine ⟨fun H ↦ Or.elim H this fun H ↦ H.1, fun H ↦ ?_⟩
      simp only [ne_eq, H, not_false_eq_true, true_and, or_not]
    rwa [Finset.filter_congr (s := Finset.range (succ N)) fun n _ ↦ hn' n]
  rw [Finset.filter_ne', Finset.card_erase_of_mem <| Finset.mem_range_succ_iff.mpr <| zero_le N]
  simp only [Finset.card_range, succ_sub_succ_eq_sub, tsub_zero]

/-- A `k`-smooth number can be written as a square times a product of distinct primes `< k`. -/
lemma eq_prod_primes_mul_sq_of_mem_smoothNumbers {n k : ℕ} (h : n ∈ smoothNumbers k) :
    ∃ s ∈ k.primesBelow.powerset, ∃ m, n = m ^ 2 * (s.prod id) := by
  obtain ⟨l, m, H₁, H₂⟩ := sq_mul_squarefree n
  have hl : l ∈ smoothNumbers k := mem_smoothNumbers_of_dvd h (Dvd.intro_left (m ^ 2) H₁)
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
  simp only [Finset.card_product, Finset.card_powerset, Finset.mem_range, zero_lt_succ,
    Finset.card_erase_of_mem, Finset.card_range, succ_sub_succ_eq_sub, tsub_zero]

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
  constructor
  · rintro ⟨h₁, h₂, _, h₄, h₅, h₆⟩
    exact ⟨⟨⟨H₁ h₂ h₅ h₁, h₄⟩, fun h _ ↦ h₆ h⟩, h₁, h₂, h₅⟩
  · rintro ⟨⟨⟨_, h₂⟩, h₃⟩, h₄, h₅, h₆⟩
    exact ⟨h₄, h₅, H₂ h₅ h₆, h₂, h₆, fun h ↦ h₃ h h₂⟩

/-- The cardinality of the set of `k`-rough numbers `≤ N` is bounded by the sum of `⌊N/p⌋`
over the primes `k ≤ p ≤ N`. -/
lemma roughNumbersUpTo_card_le (N k : ℕ) :
    (roughNumbersUpTo N k).card ≤ (N.succ.primesBelow \ k.primesBelow).sum (fun p ↦ N / p) := by
  rw [roughNumbersUpTo_eq_biUnion]
  exact Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun p _ ↦ (card_multiples' N p).le

end Nat
