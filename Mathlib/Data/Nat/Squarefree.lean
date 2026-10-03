/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat

/-!
# Lemmas about squarefreeness of natural numbers

A number is squarefree when it is not divisible by any squares except the squares of units.

## Main Results
- `Nat.squarefree_iff_nodup_primeFactorsList`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/

@[expose] public section

open Finset

namespace Nat

theorem squarefree_iff_nodup_primeFactorsList {n : ℕ} (h0 : n ≠ 0) :
    Squarefree n ↔ n.primeFactorsList.Nodup := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0, Nat.factors_eq]
  simp

end Nat

theorem Squarefree.nodup_primeFactorsList {n : ℕ} (hn : Squarefree n) : n.primeFactorsList.Nodup :=
  (Nat.squarefree_iff_nodup_primeFactorsList hn.ne_zero).mp hn

namespace Nat
variable {s : Finset ℕ} {m n p : ℕ}

theorem squarefree_iff_prime_squarefree {n : ℕ} : Squarefree n ↔ ∀ x, Prime x → ¬x * x ∣ n :=
  squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩

theorem _root_.Squarefree.natFactorization_le_one {n : ℕ} (p : ℕ) (hn : Squarefree n) :
    n.factorization p ≤ 1 := by
  rcases eq_or_ne n 0 with (rfl | hn')
  · simp
  rw [squarefree_iff_emultiplicity_le_one] at hn
  by_cases hp : p.Prime
  · have := hn p
    rw [← multiplicity_eq_factorization hp]
    simp only [Nat.isUnit_iff, hp.ne_one, or_false] at this
    exact multiplicity_le_of_emultiplicity_le this
  · rw [factorization_eq_zero_of_not_prime _ hp]
    exact zero_le_one

lemma factorization_eq_one_of_squarefree (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n) :
    factorization n p = 1 :=
  (hn.natFactorization_le_one _).antisymm <| (hp.dvd_iff_one_le_factorization hn.ne_zero).1 hpn

theorem squarefree_of_factorization_le_one {n : ℕ} (hn : n ≠ 0) (hn' : ∀ p, n.factorization p ≤ 1) :
    Squarefree n := by
  rw [squarefree_iff_nodup_primeFactorsList hn, List.nodup_iff_count_le_one]
  intro a
  rw [primeFactorsList_count_eq]
  apply hn'

theorem squarefree_iff_factorization_le_one {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ p, n.factorization p ≤ 1 :=
  ⟨fun hn => hn.natFactorization_le_one, squarefree_of_factorization_le_one hn⟩

theorem Squarefree.ext_iff {n m : ℕ} (hn : Squarefree n) (hm : Squarefree m) :
    n = m ↔ ∀ p, Prime p → (p ∣ n ↔ p ∣ m) := by
  refine ⟨by rintro rfl; simp, fun h => eq_of_factorization_eq hn.ne_zero hm.ne_zero fun p => ?_⟩
  by_cases hp : p.Prime
  · have h₁ := h _ hp
    rw [← not_iff_not, hp.dvd_iff_one_le_factorization hn.ne_zero, not_le, lt_one_iff,
      hp.dvd_iff_one_le_factorization hm.ne_zero, not_le, lt_one_iff] at h₁
    have h₂ := hn.natFactorization_le_one p
    have h₃ := hm.natFactorization_le_one p
    lia
  rw [factorization_eq_zero_of_not_prime _ hp, factorization_eq_zero_of_not_prime _ hp]

theorem squarefree_pow_iff {n k : ℕ} (hn : n ≠ 1) (hk : k ≠ 0) :
    Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1 := by
  refine ⟨fun h => ?_, by rintro ⟨hn, rfl⟩; simpa⟩
  rcases eq_or_ne n 0 with (rfl | -)
  · simp [zero_pow hk] at h
  refine ⟨h.squarefree_of_dvd (dvd_pow_self _ hk), by_contradiction fun h₁ => ?_⟩
  have : 2 ≤ k := k.two_le_iff.mpr ⟨hk, h₁⟩
  apply hn (Nat.isUnit_iff.1 (h _ _))
  rw [← sq]
  exact pow_dvd_pow _ this

theorem squarefree_and_prime_pow_iff_prime {n : ℕ} : Squarefree n ∧ IsPrimePow n ↔ Prime n := by
  refine ⟨?_, fun hn => ⟨hn.squarefree, hn.isPrimePow⟩⟩
  rw [isPrimePow_nat_iff]
  rintro ⟨h, p, k, hp, hk, rfl⟩
  rw [squarefree_pow_iff hp.ne_one hk.ne'] at h
  rwa [h.2, pow_one]

/-- Assuming that `n` has no factors less than `k`, returns the smallest prime `p` such that
  `p^2 ∣ n`. -/
def minSqFacAux : ℕ → ℕ → Option ℕ
  | n, k =>
    if h : n < k * k then none
    else
      have : Nat.sqrt n - k < Nat.sqrt n + 2 - k := by
        exact Nat.minFac_lemma n k h
      if k ∣ n then
        let n' := n / k
        have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr; apply div_le_self) this
        if k ∣ n' then some k else minSqFacAux n' (k + 2)
      else minSqFacAux n (k + 2)
termination_by n k => sqrt n + 2 - k

/-- Returns the smallest prime factor `p` of `n` such that `p^2 ∣ n`, or `none` if there is no
  such `p` (that is, `n` is squarefree). See also `Nat.squarefree_iff_minSqFac`. -/
def minSqFac (n : ℕ) : Option ℕ :=
  if 2 ∣ n then
    let n' := n / 2
    if 2 ∣ n' then some 2 else minSqFacAux n' 3
  else minSqFacAux n 3

/-- The correctness property of the return value of `minSqFac`.
  * If `none`, then `n` is squarefree;
  * If `some d`, then `d` is a minimal square factor of `n` -/
def MinSqFacProp (n : ℕ) : Option ℕ → Prop
  | none => Squarefree n
  | some d => Prime d ∧ d * d ∣ n ∧ ∀ p, Prime p → p * p ∣ n → d ≤ p

theorem minSqFacProp_div (n) {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o}
    (H : MinSqFacProp (n / k) o) : MinSqFacProp n o := by
  have : ∀ p, Prime p → p * p ∣ n → k * (p * p) ∣ n := fun p pp dp =>
    have :=
      (coprime_primes pk pp).2 fun e => by
        subst e
        contradiction
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp
  rcases o with - | d
  · rw [MinSqFacProp, squarefree_iff_prime_squarefree] at H ⊢
    exact fun p pp dp => H p pp ((dvd_div_iff_mul_dvd dk).2 (this _ pp dp))
  · obtain ⟨H1, H2, H3⟩ := H
    simp only [dvd_div_iff_mul_dvd dk] at H2 H3
    exact ⟨H1, dvd_trans (dvd_mul_left _ _) H2, fun p pp dp => H3 _ pp (this _ pp dp)⟩

theorem minSqFacAux_has_prop {n : ℕ} (k) (n0 : 0 < n) (i) (e : k = 2 * i + 3)
    (ih : ∀ m, Prime m → m ∣ n → k ≤ m) : MinSqFacProp n (minSqFacAux n k) := by
  rw [minSqFacAux]
  by_cases h : n < k * k <;> simp only [h, ↓reduceDIte]
  · refine squarefree_iff_prime_squarefree.2 fun p pp d => ?_
    have := ih p pp (dvd_trans ⟨_, rfl⟩ d)
    have := Nat.mul_le_mul this this
    exact not_le_of_gt h (le_trans this (le_of_dvd n0 d))
  have k2 : 2 ≤ k := by lia
  have k0 : 0 < k := lt_of_lt_of_le (by decide) k2
  have IH : ∀ n', n' ∣ n → ¬k ∣ n' → MinSqFacProp n' (n'.minSqFacAux (k + 2)) := by
    intro n' nd' nk
    have hn' := le_of_dvd n0 nd'
    refine
      have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (by gcongr) (Nat.minFac_lemma n k h)
      @minSqFacAux_has_prop n' (k + 2) (pos_of_dvd_of_pos nd' n0) (i + 1)
        (by simp [e, left_distrib]) fun m m2 d => ?_
    rcases Nat.eq_or_lt_of_le (ih m m2 (dvd_trans d nd')) with rfl | ml
    · contradiction
    apply (Nat.eq_or_lt_of_le ml).resolve_left
    intro me
    rw [← me, e] at d
    change 2 * (i + 2) ∣ n' at d
    have := ih _ prime_two (dvd_trans (dvd_of_mul_right_dvd d) nd')
    rw [e] at this
    exact absurd this (by lia)
  have pk : k ∣ n → Prime k := by
    refine fun dk => prime_def_minFac.2 ⟨k2, le_antisymm (minFac_le k0) ?_⟩
    exact ih _ (minFac_prime (ne_of_gt k2)) (dvd_trans (minFac_dvd _) dk)
  split_ifs with dk dkk
  · exact ⟨pk dk, (Nat.dvd_div_iff_mul_dvd dk).1 dkk, fun p pp d => ih p pp (dvd_trans ⟨_, rfl⟩ d)⟩
  · specialize IH (n / k) (div_dvd_of_dvd dk) dkk
    exact minSqFacProp_div _ (pk dk) dk (mt (Nat.dvd_div_iff_mul_dvd dk).2 dkk) IH
  · exact IH n (dvd_refl _) dk
termination_by n.sqrt + 2 - k

theorem minSqFac_has_prop (n : ℕ) : MinSqFacProp n (minSqFac n) := by
  dsimp only [minSqFac]; split_ifs with d2 d4
  · exact ⟨prime_two, (dvd_div_iff_mul_dvd d2).1 d4, fun p pp _ => pp.two_le⟩
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d4 (by decide)
    refine minSqFacProp_div _ prime_two d2 (mt (dvd_div_iff_mul_dvd d2).2 d4) ?_
    refine minSqFacAux_has_prop 3 (Nat.div_pos (le_of_dvd n0 d2) (by decide)) 0 rfl ?_
    refine fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le ?_)
    rintro rfl
    contradiction
  · rcases Nat.eq_zero_or_pos n with rfl | n0
    · cases d2 (by decide)
    refine minSqFacAux_has_prop _ n0 0 rfl ?_
    refine fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le ?_)
    rintro rfl
    contradiction

theorem minSqFac_prime {n d : ℕ} (h : n.minSqFac = some d) : Prime d := by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.1

theorem minSqFac_dvd {n d : ℕ} (h : n.minSqFac = some d) : d * d ∣ n := by
  have := minSqFac_has_prop n
  rw [h] at this
  exact this.2.1

theorem minSqFac_le_of_dvd {n d : ℕ} (h : n.minSqFac = some d) {m} (m2 : 2 ≤ m) (md : m * m ∣ n) :
    d ≤ m := by
  have := minSqFac_has_prop n; rw [h] at this
  have fd := minFac_dvd m
  exact
    le_trans (this.2.2 _ (minFac_prime <| ne_of_gt m2) (dvd_trans (mul_dvd_mul fd fd) md))
      (minFac_le <| lt_of_lt_of_le (by decide) m2)

theorem squarefree_iff_minSqFac {n : ℕ} : Squarefree n ↔ n.minSqFac = none := by
  have := minSqFac_has_prop n
  constructor <;> intro H
  · rcases e : n.minSqFac with - | d
    · rfl
    rw [e] at this
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1
  · rwa [H] at this

instance : DecidablePred (Squarefree : ℕ → Prop) := fun _ =>
  decidable_of_iff' _ squarefree_iff_minSqFac

theorem squarefree_two : Squarefree 2 := by
  rw [squarefree_iff_nodup_primeFactorsList] <;> simp

theorem divisors_filter_squarefree_of_squarefree {n : ℕ} (hn : Squarefree n) :
    {d ∈ n.divisors | Squarefree d} = n.divisors :=
  Finset.ext fun d => ⟨@Finset.filter_subset _ _ _ _ d, fun hd =>
    Finset.mem_filter.mpr ⟨hd, hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) ⟩⟩

open UniqueFactorizationMonoid

theorem divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
    {d ∈ n.divisors | Squarefree d}.val =
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset.val.map fun x =>
        x.val.prod := by
  rw [(Finset.nodup _).ext ((Finset.nodup _).map_on _)]
  · intro a
    simp only [Multiset.mem_filter, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def,
      mem_divisors]
    constructor
    · rintro ⟨⟨an, h0⟩, hsq⟩
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      simp only [Finset.mem_powerset]
      rcases an with ⟨b, rfl⟩
      rw [mul_ne_zero_iff] at h0
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0.1] at hsq
      rw [Multiset.toFinset_subset, Multiset.toFinset_val, hsq.dedup, ← associated_iff_eq,
        normalizedFactors_mul h0.1 h0.2]
      exact ⟨Multiset.subset_of_le (Multiset.le_add_right _ _), prod_normalizedFactors h0.1⟩
    · rintro ⟨s, hs, rfl⟩
      rw [Finset.mem_powerset, ← Finset.val_le_iff, Multiset.toFinset_val] at hs
      have hs0 : s.val.prod ≠ 0 := by
        rw [Ne, Multiset.prod_eq_zero_iff]
        intro con
        apply
          not_irreducible_zero
            (irreducible_of_normalized_factor 0 (Multiset.mem_dedup.1 (Multiset.mem_of_le hs con)))
      rw [(prod_normalizedFactors h0).symm.dvd_iff_dvd_right]
      refine ⟨⟨Multiset.prod_dvd_prod_of_le (le_trans hs (Multiset.dedup_le _)), h0⟩, ?_⟩
      have h :=
        UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor
          (fun x hx =>
            irreducible_of_normalized_factor x
              (Multiset.mem_of_le (le_trans hs (Multiset.dedup_le _)) hx))
          (prod_normalizedFactors hs0)
      rw [associated_eq_eq, Multiset.rel_eq] at h
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hs0, h]
      apply s.nodup
  · intro x hx y hy h
    rw [← Finset.val_inj, ← Multiset.rel_eq, ← associated_eq_eq]
    rw [← Finset.mem_def, Finset.mem_powerset] at hx hy
    apply UniqueFactorizationMonoid.factors_unique _ _ (associated_iff_eq.2 h)
    · intro z hz
      apply irreducible_of_normalized_factor z
      · rw [← Multiset.mem_toFinset]
        apply hx hz
    · intro z hz
      apply irreducible_of_normalized_factor z
      · rw [← Multiset.mem_toFinset]
        apply hy hz

theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type*} [AddCommMonoid α]
    {f : ℕ → α} :
    ∑ d ∈ n.divisors with Squarefree d, f d =
      ∑ i ∈ (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset, f i.val.prod := by
  rw [Finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl

@[deprecated "Use `exists_sq_mul_squarefree` instead, which binds the witnesses in the order in \
which they appear." (since := "2026-08-17")]
protected theorem sq_mul_squarefree (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ Squarefree a := by
  obtain ⟨b, a, h, hs⟩ := exists_sq_mul_squarefree n
  exact ⟨a, b, h, hs⟩

theorem sq_mul_squarefree_of_pos {n : ℕ} (hn : 0 < n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a := by
  obtain ⟨b, a, h, hs⟩ := exists_sq_mul_squarefree n
  exact ⟨a, b, Nat.pos_of_ne_zero hs.ne_zero, Nat.pos_of_ne_zero (by grind), h, hs⟩

theorem sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) :
    ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1) := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h
  refine ⟨a₁.pred, b₁.pred, ?_, ?_⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]

/-- `Squarefree` is multiplicative. Note that the → direction does not require `hmn`
and generalizes to arbitrary commutative monoids. See `Squarefree.of_mul_left` and
`Squarefree.of_mul_right` above for auxiliary lemmas. -/
theorem squarefree_mul {m n : ℕ} (hmn : m.Coprime n) :
    Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simp [squarefree_mul_iff, Nat.coprime_iff_isRelPrime.mp hmn]

theorem coprime_of_squarefree_mul {m n : ℕ} (h : Squarefree (m * n)) : m.Coprime n :=
  coprime_of_dvd fun p hp hm hn => squarefree_iff_prime_squarefree.mp h p hp (mul_dvd_mul hm hn)

theorem squarefree_mul_iff {m n : ℕ} :
    Squarefree (m * n) ↔ m.Coprime n ∧ Squarefree m ∧ Squarefree n := by
  rw [_root_.squarefree_mul_iff, Nat.coprime_iff_isRelPrime]

lemma coprime_div_gcd_of_squarefree (hm : Squarefree m) (hn : n ≠ 0) : Coprime (m / gcd m n) n := by
  have : Coprime (m / gcd m n) (gcd m n) :=
    coprime_of_squarefree_mul <| by simpa [Nat.div_mul_cancel, gcd_dvd_left]
  simpa [Nat.div_mul_cancel, gcd_dvd_right] using
    (coprime_div_gcd_div_gcd (m := m) (gcd_ne_zero_right hn).bot_lt).mul_right this

lemma prod_primeFactors_of_squarefree (hn : Squarefree n) : ∏ p ∈ n.primeFactors, p = n := by
  rw [← toFinset_factors, List.prod_toFinset _ hn.nodup_primeFactorsList,
    List.map_id', Nat.prod_primeFactorsList hn.ne_zero]

theorem squarefree_and_primeFactors_card_eq_two_iff (n : ℕ) :
    Squarefree n ∧ (primeFactors n).card = 2 ↔
      ∃ p q : ℕ, p < q ∧ p.Prime ∧ q.Prime ∧ p * q = n := by
  refine ⟨fun ⟨sq, nc⟩ ↦ ?_, fun ⟨p, q, pq, hp, hq, hn⟩ ↦ ?_⟩
  · obtain ⟨p, q, pq, eq⟩ := Finset.card_eq_two.mp nc
    wlog pq' : p < q
    · exact this n ⟨sq, nc⟩ sq nc q p pq.symm (by grind) (by grind)
    refine ⟨p, q, pq', prime_of_mem_primeFactors (n := n) (by grind),
      prime_of_mem_primeFactors (n := n) (by grind), ?_⟩
    rw [← prod_primeFactors_of_squarefree sq, eq, prod_insert (by simp [pq]), prod_singleton]
  · rw [← hn, squarefree_mul <| (coprime_primes hp hq).mpr pq.ne,
      primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors]
    exact ⟨⟨hp.squarefree, hq.squarefree⟩, by grind⟩

lemma primeFactors_prod (hs : ∀ p ∈ s, p.Prime) : primeFactors (∏ p ∈ s, p) = s := by
  have hn : ∏ p ∈ s, p ≠ 0 := prod_ne_zero_iff.2 fun p hp ↦ (hs _ hp).ne_zero
  ext p
  rw [mem_primeFactors_of_ne_zero hn, and_congr_right (fun hp ↦ hp.prime.dvd_finsetProd_iff _)]
  refine ⟨?_, fun hp ↦ ⟨hs _ hp, _, hp, dvd_rfl⟩⟩
  rintro ⟨hp, q, hq, hpq⟩
  rwa [← ((hs _ hq).dvd_iff_eq hp.ne_one).1 hpq]

theorem primeFactors_prod_primeFactors (n : ℕ) :
    (∏ p ∈ n.primeFactors, p).primeFactors = n.primeFactors :=
  primeFactors_prod fun _ hp ↦ n.mem_primeFactors.mp hp |>.left

theorem prod_primeFactors_dvd_iff {n k : ℕ} (hk : k ≠ 0) :
    (∏ p ∈ n.primeFactors, p) ∣ k ↔ n.primeFactors ⊆ k.primeFactors := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · grw [← Nat.primeFactors_mono h hk, primeFactors_prod_primeFactors]
  · grw [← k.prod_primeFactors_dvd, Finset.prod_dvd_prod_of_subset _ _ _ h]

lemma primeFactors_div_gcd (hm : Squarefree m) (hn : n ≠ 0) :
    primeFactors (m / m.gcd n) = primeFactors m \ primeFactors n := by
  ext p
  have : m / m.gcd n ≠ 0 := by simp [gcd_ne_zero_right hn, gcd_le_left _ hm.ne_zero.bot_lt]
  simp only [mem_primeFactors, ne_eq, this, not_false_eq_true, and_true, not_and, mem_sdiff,
    hm.ne_zero, hn, dvd_div_iff_mul_dvd (gcd_dvd_left _ _)]
  refine ⟨fun hp ↦ ⟨⟨hp.1, dvd_of_mul_left_dvd hp.2⟩, fun _ hpn ↦ hp.1.not_isUnit <| hm _ <|
    (mul_dvd_mul_right (dvd_gcd (dvd_of_mul_left_dvd hp.2) hpn) _).trans hp.2⟩, fun hp ↦
      ⟨hp.1.1, Coprime.mul_dvd_of_dvd_of_dvd ?_ (gcd_dvd_left _ _) hp.1.2⟩⟩
  rw [coprime_comm, hp.1.1.coprime_iff_not_dvd]
  exact fun hpn ↦ hp.2 hp.1.1 <| hpn.trans <| gcd_dvd_right _ _

lemma prod_primeFactors_invOn_squarefree :
    Set.InvOn (fun n : ℕ ↦ (factorization n).support) (fun s ↦ ∏ p ∈ s, p)
      {s | ∀ p ∈ s, p.Prime} {n | Squarefree n} :=
  ⟨fun _s ↦ primeFactors_prod, fun _n ↦ prod_primeFactors_of_squarefree⟩

theorem prod_primeFactors_sdiff_of_squarefree {n : ℕ} (hn : Squarefree n) {t : Finset ℕ}
    (ht : t ⊆ n.primeFactors) :
    ∏ a ∈ (n.primeFactors \ t), a = n / ∏ a ∈ t, a := by
  refine symm <| Nat.div_eq_of_eq_mul_left (Finset.prod_pos
    fun p hp => (prime_of_mem_primeFactorsList (List.mem_toFinset.mp (ht hp))).pos) ?_
  rw [Finset.prod_sdiff ht, prod_primeFactors_of_squarefree hn]

end Nat

namespace Int

-- TODO: state this uniformly in a `NormalizationMonoid`, quantifying over normalized primes, so
-- that this version and the one for monic polynomials over a field both follow from it.
/-- An integer is squarefree iff no prime square divides it. -/
theorem squarefree_iff_prime_sq_not_dvd {n : ℤ} :
    Squarefree n ↔ ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ^ 2 ∣ n := by
  simp [← Int.squarefree_natAbs, Nat.squarefree_iff_prime_squarefree, ← Int.natCast_dvd,
    pow_two]

end Int
