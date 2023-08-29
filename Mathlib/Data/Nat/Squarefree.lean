/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Squarefree
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.PrimeNormNum
import Mathlib.RingTheory.Int.Basic

#align_import data.nat.squarefree from "leanprover-community/mathlib"@"3c1368cac4abd5a5cbe44317ba7e87379d51ed88"

/-!
# Lemmas about squarefreeness of natural numbers
A number is squarefree when it is not divisible by any squares except the squares of units.

## Main Results
 - `Nat.squarefree_iff_nodup_factors`: A positive natural number `x` is squarefree iff
  the list `factors x` has no duplicate factors.

## Tags
squarefree, multiplicity

-/


namespace Nat

theorem squarefree_iff_nodup_factors {n : ℕ} (h0 : n ≠ 0) : Squarefree n ↔ n.factors.Nodup := by
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0, Nat.factors_eq]
  -- ⊢ Multiset.Nodup ↑(factors n) ↔ List.Nodup (factors n)
  simp
  -- 🎉 no goals
#align nat.squarefree_iff_nodup_factors Nat.squarefree_iff_nodup_factors

end Nat

theorem Squarefree.nodup_factors {n : ℕ} (hn : Squarefree n) : n.factors.Nodup :=
    (Nat.squarefree_iff_nodup_factors hn.ne_zero).mp hn

namespace Nat

theorem squarefree_iff_prime_squarefree {n : ℕ} : Squarefree n ↔ ∀ x, Prime x → ¬x * x ∣ n :=
  squarefree_iff_irreducible_sq_not_dvd_of_exists_irreducible ⟨_, prime_two⟩
#align nat.squarefree_iff_prime_squarefree Nat.squarefree_iff_prime_squarefree

theorem Squarefree.factorization_le_one {n : ℕ} (p : ℕ) (hn : Squarefree n) :
    n.factorization p ≤ 1 := by
  rcases eq_or_ne n 0 with (rfl | hn')
  -- ⊢ ↑(factorization 0) p ≤ 1
  · simp
    -- 🎉 no goals
  rw [multiplicity.squarefree_iff_multiplicity_le_one] at hn
  -- ⊢ ↑(factorization n) p ≤ 1
  by_cases hp : p.Prime
  -- ⊢ ↑(factorization n) p ≤ 1
  · have := hn p
    -- ⊢ ↑(factorization n) p ≤ 1
    simp only [multiplicity_eq_factorization hp hn', Nat.isUnit_iff, hp.ne_one, or_false_iff]
      at this
    exact_mod_cast this
    -- 🎉 no goals
  · rw [factorization_eq_zero_of_non_prime _ hp]
    -- ⊢ 0 ≤ 1
    exact zero_le_one
    -- 🎉 no goals
#align nat.squarefree.factorization_le_one Nat.Squarefree.factorization_le_one

theorem squarefree_of_factorization_le_one {n : ℕ} (hn : n ≠ 0) (hn' : ∀ p, n.factorization p ≤ 1) :
    Squarefree n := by
  rw [squarefree_iff_nodup_factors hn, List.nodup_iff_count_le_one]
  -- ⊢ ∀ (a : ℕ), List.count a (factors n) ≤ 1
  intro a
  -- ⊢ List.count a (factors n) ≤ 1
  rw [factors_count_eq]
  -- ⊢ ↑(factorization n) a ≤ 1
  apply hn'
  -- 🎉 no goals
#align nat.squarefree_of_factorization_le_one Nat.squarefree_of_factorization_le_one

theorem squarefree_iff_factorization_le_one {n : ℕ} (hn : n ≠ 0) :
    Squarefree n ↔ ∀ p, n.factorization p ≤ 1 :=
  ⟨fun p hn => Squarefree.factorization_le_one hn p, squarefree_of_factorization_le_one hn⟩
#align nat.squarefree_iff_factorization_le_one Nat.squarefree_iff_factorization_le_one

theorem Squarefree.ext_iff {n m : ℕ} (hn : Squarefree n) (hm : Squarefree m) :
    n = m ↔ ∀ p, Prime p → (p ∣ n ↔ p ∣ m) := by
  refine' ⟨by rintro rfl; simp, fun h => eq_of_factorization_eq hn.ne_zero hm.ne_zero fun p => _⟩
  -- ⊢ ↑(factorization n) p = ↑(factorization m) p
  by_cases hp : p.Prime
  -- ⊢ ↑(factorization n) p = ↑(factorization m) p
  · have h₁ := h _ hp
    -- ⊢ ↑(factorization n) p = ↑(factorization m) p
    rw [← not_iff_not, hp.dvd_iff_one_le_factorization hn.ne_zero, not_le, lt_one_iff,
      hp.dvd_iff_one_le_factorization hm.ne_zero, not_le, lt_one_iff] at h₁
    have h₂ := Squarefree.factorization_le_one p hn
    -- ⊢ ↑(factorization n) p = ↑(factorization m) p
    have h₃ := Squarefree.factorization_le_one p hm
    -- ⊢ ↑(factorization n) p = ↑(factorization m) p
    rw [Nat.le_add_one_iff, le_zero_iff] at h₂ h₃
    -- ⊢ ↑(factorization n) p = ↑(factorization m) p
    cases' h₂ with h₂ h₂
    -- ⊢ ↑(factorization n) p = ↑(factorization m) p
    · rwa [h₂, eq_comm, ← h₁]
      -- 🎉 no goals
    · rw [h₂, h₃.resolve_left]
      -- ⊢ ¬↑(factorization m) p = 0
      rw [← h₁, h₂]
      -- ⊢ ¬0 + 1 = 0
      simp only [Nat.one_ne_zero, not_false_iff]
      -- 🎉 no goals
  rw [factorization_eq_zero_of_non_prime _ hp, factorization_eq_zero_of_non_prime _ hp]
  -- 🎉 no goals
#align nat.squarefree.ext_iff Nat.Squarefree.ext_iff

theorem squarefree_pow_iff {n k : ℕ} (hn : n ≠ 1) (hk : k ≠ 0) :
    Squarefree (n ^ k) ↔ Squarefree n ∧ k = 1 := by
  refine' ⟨fun h => _, by rintro ⟨hn, rfl⟩; simpa⟩
  -- ⊢ Squarefree n ∧ k = 1
  rcases eq_or_ne n 0 with (rfl | -)
  -- ⊢ Squarefree 0 ∧ k = 1
  · simp [zero_pow hk.bot_lt] at h
    -- 🎉 no goals
  refine' ⟨h.squarefree_of_dvd (dvd_pow_self _ hk), by_contradiction fun h₁ => _⟩
  -- ⊢ False
  have : 2 ≤ k := k.two_le_iff.mpr ⟨hk, h₁⟩
  -- ⊢ False
  apply hn (Nat.isUnit_iff.1 (h _ _))
  -- ⊢ n * n ∣ n ^ k
  rw [← sq]
  -- ⊢ n ^ 2 ∣ n ^ k
  exact pow_dvd_pow _ this
  -- 🎉 no goals
#align nat.squarefree_pow_iff Nat.squarefree_pow_iff

theorem squarefree_and_prime_pow_iff_prime {n : ℕ} : Squarefree n ∧ IsPrimePow n ↔ Prime n := by
  refine' ⟨_, fun hn => ⟨hn.squarefree, hn.isPrimePow⟩⟩
  -- ⊢ Squarefree n ∧ IsPrimePow n → Prime n
  rw [isPrimePow_nat_iff]
  -- ⊢ (Squarefree n ∧ ∃ p k, Prime p ∧ 0 < k ∧ p ^ k = n) → Prime n
  rintro ⟨h, p, k, hp, hk, rfl⟩
  -- ⊢ Prime (p ^ k)
  rw [squarefree_pow_iff hp.ne_one hk.ne'] at h
  -- ⊢ Prime (p ^ k)
  rwa [h.2, pow_one]
  -- 🎉 no goals
#align nat.squarefree_and_prime_pow_iff_prime Nat.squarefree_and_prime_pow_iff_prime

/-- Assuming that `n` has no factors less than `k`, returns the smallest prime `p` such that
  `p^2 ∣ n`. -/
def minSqFacAux : ℕ → ℕ → Option ℕ
  | n, k =>
    if h : n < k * k then none
    else
      have : Nat.sqrt n - k < Nat.sqrt n + 2 - k := by
        exact Nat.minFac_lemma n k h
        -- 🎉 no goals
      if k ∣ n then
        let n' := n / k
        have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (Nat.sub_le_sub_right (Nat.sqrt_le_sqrt <| Nat.div_le_self _ _) k) this
        if k ∣ n' then some k else minSqFacAux n' (k + 2)
      else minSqFacAux n (k + 2)
termination_by _ n k => sqrt n + 2 - k
#align nat.min_sq_fac_aux Nat.minSqFacAux

/-- Returns the smallest prime factor `p` of `n` such that `p^2 ∣ n`, or `none` if there is no
  such `p` (that is, `n` is squarefree). See also `Nat.squarefree_iff_minSqFac`. -/
def minSqFac (n : ℕ) : Option ℕ :=
  if 2 ∣ n then
    let n' := n / 2
    if 2 ∣ n' then some 2 else minSqFacAux n' 3
  else minSqFacAux n 3
#align nat.min_sq_fac Nat.minSqFac

/-- The correctness property of the return value of `minSqFac`.
  * If `none`, then `n` is squarefree;
  * If `some d`, then `d` is a minimal square factor of `n` -/
def MinSqFacProp (n : ℕ) : Option ℕ → Prop
  | none => Squarefree n
  | some d => Prime d ∧ d * d ∣ n ∧ ∀ p, Prime p → p * p ∣ n → d ≤ p
#align nat.min_sq_fac_prop Nat.MinSqFacProp

theorem minSqFacProp_div (n) {k} (pk : Prime k) (dk : k ∣ n) (dkk : ¬k * k ∣ n) {o}
    (H : MinSqFacProp (n / k) o) : MinSqFacProp n o := by
  have : ∀ p, Prime p → p * p ∣ n → k * (p * p) ∣ n := fun p pp dp =>
    have :=
      (coprime_primes pk pp).2 fun e => by
        subst e
        contradiction
    (coprime_mul_iff_right.2 ⟨this, this⟩).mul_dvd_of_dvd_of_dvd dk dp
  cases' o with d
  -- ⊢ MinSqFacProp n none
  · rw [MinSqFacProp, squarefree_iff_prime_squarefree] at H ⊢
    -- ⊢ match none with
    exact fun p pp dp => H p pp ((dvd_div_iff dk).2 (this _ pp dp))
    -- 🎉 no goals
  · obtain ⟨H1, H2, H3⟩ := H
    -- ⊢ MinSqFacProp n (some d)
    simp only [dvd_div_iff dk] at H2 H3
    -- ⊢ MinSqFacProp n (some d)
    exact ⟨H1, dvd_trans (dvd_mul_left _ _) H2, fun p pp dp => H3 _ pp (this _ pp dp)⟩
    -- 🎉 no goals
#align nat.min_sq_fac_prop_div Nat.minSqFacProp_div

--Porting note: I had to replace two uses of `by decide` by `linarith`.
theorem minSqFacAux_has_prop {n : ℕ} (k) (n0 : 0 < n) (i) (e : k = 2 * i + 3)
    (ih : ∀ m, Prime m → m ∣ n → k ≤ m) : MinSqFacProp n (minSqFacAux n k) := by
  rw [minSqFacAux]
  -- ⊢ MinSqFacProp n
  by_cases h : n < k * k <;> simp [h]
                             -- ⊢ MinSqFacProp n none
                             -- ⊢ MinSqFacProp n (if k ∣ n then if k ∣ n / k then some k else minSqFacAux (n / …
  · refine' squarefree_iff_prime_squarefree.2 fun p pp d => _
    -- ⊢ False
    have := ih p pp (dvd_trans ⟨_, rfl⟩ d)
    -- ⊢ False
    have := Nat.mul_le_mul this this
    -- ⊢ False
    exact not_le_of_lt h (le_trans this (le_of_dvd n0 d))
    -- 🎉 no goals
  have k2 : 2 ≤ k := by
    subst e
    linarith
  have k0 : 0 < k := lt_of_lt_of_le (by decide) k2
  -- ⊢ MinSqFacProp n (if k ∣ n then if k ∣ n / k then some k else minSqFacAux (n / …
  have IH : ∀ n', n' ∣ n → ¬k ∣ n' → MinSqFacProp n' (n'.minSqFacAux (k + 2)) := by
    intro n' nd' nk
    have hn' := le_of_dvd n0 nd'
    refine'
      have : Nat.sqrt n' - k < Nat.sqrt n + 2 - k :=
        lt_of_le_of_lt (Nat.sub_le_sub_right (Nat.sqrt_le_sqrt hn') _) (Nat.minFac_lemma n k h)
      @minSqFacAux_has_prop n' (k + 2) (pos_of_dvd_of_pos nd' n0) (i + 1)
        (by simp [e, left_distrib]) fun m m2 d => _
    cases' Nat.eq_or_lt_of_le (ih m m2 (dvd_trans d nd')) with me ml
    · subst me
      contradiction
    apply (Nat.eq_or_lt_of_le ml).resolve_left
    intro me
    rw [← me, e] at d
    change 2 * (i + 2) ∣ n' at d
    have := ih _ prime_two (dvd_trans (dvd_of_mul_right_dvd d) nd')
    rw [e] at this
    exact absurd this (by linarith)
  have pk : k ∣ n → Prime k := by
    refine' fun dk => prime_def_minFac.2 ⟨k2, le_antisymm (minFac_le k0) _⟩
    exact ih _ (minFac_prime (ne_of_gt k2)) (dvd_trans (minFac_dvd _) dk)
  split_ifs with dk dkk
  · exact ⟨pk dk, (Nat.dvd_div_iff dk).1 dkk, fun p pp d => ih p pp (dvd_trans ⟨_, rfl⟩ d)⟩
    -- 🎉 no goals
  · specialize IH (n / k) (div_dvd_of_dvd dk) dkk
    -- ⊢ MinSqFacProp n (minSqFacAux (n / k) (k + 2))
    exact minSqFacProp_div _ (pk dk) dk (mt (Nat.dvd_div_iff dk).2 dkk) IH
    -- 🎉 no goals
  · exact IH n (dvd_refl _) dk
    -- 🎉 no goals
termination_by _ => n.sqrt + 2 - k
#align nat.min_sq_fac_aux_has_prop Nat.minSqFacAux_has_prop

theorem minSqFac_has_prop (n : ℕ) : MinSqFacProp n (minSqFac n) := by
  dsimp only [minSqFac]; split_ifs with d2 d4
  -- ⊢ MinSqFacProp n (if 2 ∣ n then if 2 ∣ n / 2 then some 2 else minSqFacAux (n / …
  · exact ⟨prime_two, (dvd_div_iff d2).1 d4, fun p pp _ => pp.two_le⟩
    -- 🎉 no goals
  · cases' Nat.eq_zero_or_pos n with n0 n0
    -- ⊢ MinSqFacProp n (minSqFacAux (n / 2) 3)
    · subst n0
      -- ⊢ MinSqFacProp 0 (minSqFacAux (0 / 2) 3)
      cases d4 (by decide)
      -- 🎉 no goals
    refine' minSqFacProp_div _ prime_two d2 (mt (dvd_div_iff d2).2 d4) _
    -- ⊢ MinSqFacProp (n / 2) (minSqFacAux (n / 2) 3)
    refine' minSqFacAux_has_prop 3 (Nat.div_pos (le_of_dvd n0 d2) (by decide)) 0 rfl _
    -- ⊢ ∀ (m : ℕ), Prime m → m ∣ n / 2 → 3 ≤ m
    refine' fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
    -- ⊢ 2 ≠ p
    rintro rfl
    -- ⊢ False
    contradiction
    -- 🎉 no goals
  · cases' Nat.eq_zero_or_pos n with n0 n0
    -- ⊢ MinSqFacProp n (minSqFacAux n 3)
    · subst n0
      -- ⊢ MinSqFacProp 0 (minSqFacAux 0 3)
      cases d2 (by decide)
      -- 🎉 no goals
    refine' minSqFacAux_has_prop _ n0 0 rfl _
    -- ⊢ ∀ (m : ℕ), Prime m → m ∣ n → 3 ≤ m
    refine' fun p pp dp => succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
    -- ⊢ 2 ≠ p
    rintro rfl
    -- ⊢ False
    contradiction
    -- 🎉 no goals
#align nat.min_sq_fac_has_prop Nat.minSqFac_has_prop

theorem minSqFac_prime {n d : ℕ} (h : n.minSqFac = some d) : Prime d := by
  have := minSqFac_has_prop n
  -- ⊢ Prime d
  rw [h] at this
  -- ⊢ Prime d
  exact this.1
  -- 🎉 no goals
#align nat.min_sq_fac_prime Nat.minSqFac_prime

theorem minSqFac_dvd {n d : ℕ} (h : n.minSqFac = some d) : d * d ∣ n := by
  have := minSqFac_has_prop n
  -- ⊢ d * d ∣ n
  rw [h] at this
  -- ⊢ d * d ∣ n
  exact this.2.1
  -- 🎉 no goals
#align nat.min_sq_fac_dvd Nat.minSqFac_dvd

theorem minSqFac_le_of_dvd {n d : ℕ} (h : n.minSqFac = some d) {m} (m2 : 2 ≤ m) (md : m * m ∣ n) :
    d ≤ m := by
  have := minSqFac_has_prop n; rw [h] at this
  -- ⊢ d ≤ m
                               -- ⊢ d ≤ m
  have fd := minFac_dvd m
  -- ⊢ d ≤ m
  exact
    le_trans (this.2.2 _ (minFac_prime <| ne_of_gt m2) (dvd_trans (mul_dvd_mul fd fd) md))
      (minFac_le <| lt_of_lt_of_le (by decide) m2)
#align nat.min_sq_fac_le_of_dvd Nat.minSqFac_le_of_dvd

theorem squarefree_iff_minSqFac {n : ℕ} : Squarefree n ↔ n.minSqFac = none := by
  have := minSqFac_has_prop n
  -- ⊢ Squarefree n ↔ minSqFac n = none
  constructor <;> intro H
  -- ⊢ Squarefree n → minSqFac n = none
                  -- ⊢ minSqFac n = none
                  -- ⊢ Squarefree n
  · cases' e : n.minSqFac with d
    -- ⊢ none = none
    · rfl
      -- 🎉 no goals
    rw [e] at this
    -- ⊢ some d = none
    cases squarefree_iff_prime_squarefree.1 H _ this.1 this.2.1
    -- 🎉 no goals
  · rwa [H] at this
    -- 🎉 no goals
#align nat.squarefree_iff_min_sq_fac Nat.squarefree_iff_minSqFac

instance : DecidablePred (Squarefree : ℕ → Prop) := fun _ =>
  decidable_of_iff' _ squarefree_iff_minSqFac

theorem squarefree_two : Squarefree 2 := by
  rw [squarefree_iff_nodup_factors] <;> norm_num
                                        -- 🎉 no goals
                                        -- 🎉 no goals
#align nat.squarefree_two Nat.squarefree_two

theorem divisors_filter_squarefree_of_squarefree {n : ℕ} (hn : Squarefree n) :
    n.divisors.filter Squarefree = n.divisors :=
  Finset.ext fun d => ⟨@Finset.filter_subset _ _ _ _ d, fun hd =>
    Finset.mem_filter.mpr ⟨hd, hn.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) ⟩⟩

open UniqueFactorizationMonoid

theorem divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) :
    (n.divisors.filter Squarefree).val =
      (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset.val.map fun x =>
        x.val.prod := by
  rw [(Finset.nodup _).ext ((Finset.nodup _).map_on _)]
  -- ⊢ ∀ (a : ℕ), a ∈ (Finset.filter Squarefree (divisors n)).val ↔ a ∈ Multiset.ma …
  · intro a
    -- ⊢ a ∈ (Finset.filter Squarefree (divisors n)).val ↔ a ∈ Multiset.map (fun x => …
    simp only [Multiset.mem_filter, id.def, Multiset.mem_map, Finset.filter_val, ← Finset.mem_def,
      mem_divisors]
    constructor
    -- ⊢ (a ∣ n ∧ n ≠ 0) ∧ Squarefree a → ∃ a_2, a_2 ∈ Finset.powerset (Multiset.toFi …
    · rintro ⟨⟨an, h0⟩, hsq⟩
      -- ⊢ ∃ a_1, a_1 ∈ Finset.powerset (Multiset.toFinset (normalizedFactors n)) ∧ Mul …
      use (UniqueFactorizationMonoid.normalizedFactors a).toFinset
      -- ⊢ Multiset.toFinset (normalizedFactors a) ∈ Finset.powerset (Multiset.toFinset …
      simp only [id.def, Finset.mem_powerset]
      -- ⊢ Multiset.toFinset (normalizedFactors a) ⊆ Multiset.toFinset (normalizedFacto …
      rcases an with ⟨b, rfl⟩
      -- ⊢ Multiset.toFinset (normalizedFactors a) ⊆ Multiset.toFinset (normalizedFacto …
      rw [mul_ne_zero_iff] at h0
      -- ⊢ Multiset.toFinset (normalizedFactors a) ⊆ Multiset.toFinset (normalizedFacto …
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0.1] at hsq
      -- ⊢ Multiset.toFinset (normalizedFactors a) ⊆ Multiset.toFinset (normalizedFacto …
      rw [Multiset.toFinset_subset, Multiset.toFinset_val, hsq.dedup, ← associated_iff_eq,
        normalizedFactors_mul h0.1 h0.2]
      exact ⟨Multiset.subset_of_le (Multiset.le_add_right _ _), normalizedFactors_prod h0.1⟩
      -- 🎉 no goals
    · rintro ⟨s, hs, rfl⟩
      -- ⊢ (Multiset.prod s.val ∣ n ∧ n ≠ 0) ∧ Squarefree (Multiset.prod s.val)
      rw [Finset.mem_powerset, ← Finset.val_le_iff, Multiset.toFinset_val] at hs
      -- ⊢ (Multiset.prod s.val ∣ n ∧ n ≠ 0) ∧ Squarefree (Multiset.prod s.val)
      have hs0 : s.val.prod ≠ 0 := by
        rw [Ne.def, Multiset.prod_eq_zero_iff]
        intro con
        apply
          not_irreducible_zero
            (irreducible_of_normalized_factor 0 (Multiset.mem_dedup.1 (Multiset.mem_of_le hs con)))
      rw [(normalizedFactors_prod h0).symm.dvd_iff_dvd_right]
      -- ⊢ (Multiset.prod s.val ∣ Multiset.prod (normalizedFactors n) ∧ n ≠ 0) ∧ Square …
      refine' ⟨⟨Multiset.prod_dvd_prod_of_le (le_trans hs (Multiset.dedup_le _)), h0⟩, _⟩
      -- ⊢ Squarefree (Multiset.prod s.val)
      have h :=
        UniqueFactorizationMonoid.factors_unique irreducible_of_normalized_factor
          (fun x hx =>
            irreducible_of_normalized_factor x
              (Multiset.mem_of_le (le_trans hs (Multiset.dedup_le _)) hx))
          (normalizedFactors_prod hs0)
      rw [associated_eq_eq, Multiset.rel_eq] at h
      -- ⊢ Squarefree (Multiset.prod s.val)
      rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hs0, h]
      -- ⊢ Multiset.Nodup s.val
      apply s.nodup
      -- 🎉 no goals
  · intro x hx y hy h
    -- ⊢ x = y
    rw [← Finset.val_inj, ← Multiset.rel_eq, ← associated_eq_eq]
    -- ⊢ Multiset.Rel (fun x x_1 => Associated x x_1) x.val y.val
    rw [← Finset.mem_def, Finset.mem_powerset] at hx hy
    -- ⊢ Multiset.Rel (fun x x_1 => Associated x x_1) x.val y.val
    apply UniqueFactorizationMonoid.factors_unique _ _ (associated_iff_eq.2 h)
    -- ⊢ ∀ (x_1 : ℕ), x_1 ∈ x.val → Irreducible x_1
    · intro z hz
      -- ⊢ Irreducible z
      apply irreducible_of_normalized_factor z
      -- ⊢ z ∈ normalizedFactors ?m.123736
      rw [← Multiset.mem_toFinset]
      apply hx hz
      -- 🎉 no goals
    · intro z hz
      -- ⊢ Irreducible z
      apply irreducible_of_normalized_factor z
      -- ⊢ z ∈ normalizedFactors ?m.123977
      rw [← Multiset.mem_toFinset]
      apply hy hz
      -- 🎉 no goals
#align nat.divisors_filter_squarefree Nat.divisors_filter_squarefree

open BigOperators

theorem sum_divisors_filter_squarefree {n : ℕ} (h0 : n ≠ 0) {α : Type*} [AddCommMonoid α]
    {f : ℕ → α} :
    ∑ i in n.divisors.filter Squarefree, f i =
      ∑ i in (UniqueFactorizationMonoid.normalizedFactors n).toFinset.powerset, f i.val.prod := by
  rw [Finset.sum_eq_multiset_sum, divisors_filter_squarefree h0, Multiset.map_map,
    Finset.sum_eq_multiset_sum]
  rfl
  -- 🎉 no goals
#align nat.sum_divisors_filter_squarefree Nat.sum_divisors_filter_squarefree

theorem sq_mul_squarefree_of_pos {n : ℕ} (hn : 0 < n) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ^ 2 * a = n ∧ Squarefree a := by
  classical -- Porting note: This line is not needed in Lean 3
  set S := (Finset.range (n + 1)).filter (fun s => s ∣ n ∧ ∃ x, s = x ^ 2)
  have hSne : S.Nonempty := by
    use 1
    have h1 : 0 < n ∧ ∃ x : ℕ, 1 = x ^ 2 := ⟨hn, ⟨1, (one_pow 2).symm⟩⟩
    simp [h1]
  let s := Finset.max' S hSne
  have hs : s ∈ S := Finset.max'_mem S hSne
  simp only [Finset.mem_filter, Finset.mem_range] at hs
  obtain ⟨-, ⟨a, hsa⟩, ⟨b, hsb⟩⟩ := hs
  rw [hsa] at hn
  obtain ⟨hlts, hlta⟩ := CanonicallyOrderedCommSemiring.mul_pos.mp hn
  rw [hsb] at hsa hn hlts
  refine' ⟨a, b, hlta, (pow_pos_iff zero_lt_two).mp hlts, hsa.symm, _⟩
  rintro x ⟨y, hy⟩
  rw [Nat.isUnit_iff]
  by_contra hx
  refine' lt_le_antisymm _ (Finset.le_max' S ((b * x) ^ 2) _)
  -- Porting note: these two goals were in the opposite order in Lean 3
  · convert lt_mul_of_one_lt_right hlts
      (one_lt_pow 2 x zero_lt_two (one_lt_iff_ne_zero_and_ne_one.mpr ⟨fun h => by simp_all, hx⟩))
      using 1
    rw [mul_pow]
  · simp_rw [hsa, Finset.mem_filter, Finset.mem_range]
    refine' ⟨lt_succ_iff.mpr (le_of_dvd hn _), _, ⟨b * x, rfl⟩⟩ <;> use y <;> rw [hy] <;> ring
#align nat.sq_mul_squarefree_of_pos Nat.sq_mul_squarefree_of_pos

theorem sq_mul_squarefree_of_pos' {n : ℕ} (h : 0 < n) :
    ∃ a b : ℕ, (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1) := by
  obtain ⟨a₁, b₁, ha₁, hb₁, hab₁, hab₂⟩ := sq_mul_squarefree_of_pos h
  -- ⊢ ∃ a b, (b + 1) ^ 2 * (a + 1) = n ∧ Squarefree (a + 1)
  refine' ⟨a₁.pred, b₁.pred, _, _⟩ <;> simpa only [add_one, succ_pred_eq_of_pos, ha₁, hb₁]
  -- ⊢ (pred b₁ + 1) ^ 2 * (pred a₁ + 1) = n
                                       -- 🎉 no goals
                                       -- 🎉 no goals
#align nat.sq_mul_squarefree_of_pos' Nat.sq_mul_squarefree_of_pos'

theorem sq_mul_squarefree (n : ℕ) : ∃ a b : ℕ, b ^ 2 * a = n ∧ Squarefree a := by
  cases' n with n
  -- ⊢ ∃ a b, b ^ 2 * a = zero ∧ Squarefree a
  · exact ⟨1, 0, by simp, squarefree_one⟩
    -- 🎉 no goals
  · obtain ⟨a, b, -, -, h₁, h₂⟩ := sq_mul_squarefree_of_pos (succ_pos n)
    -- ⊢ ∃ a b, b ^ 2 * a = succ n ∧ Squarefree a
    exact ⟨a, b, h₁, h₂⟩
    -- 🎉 no goals
#align nat.sq_mul_squarefree Nat.sq_mul_squarefree

/-- `squarefree` is multiplicative. Note that the → direction does not require `hmn`
and generalizes to arbitrary commutative monoids. See `squarefree.of_mul_left` and
`squarefree.of_mul_right` above for auxiliary lemmas. -/
theorem squarefree_mul {m n : ℕ} (hmn : m.coprime n) :
    Squarefree (m * n) ↔ Squarefree m ∧ Squarefree n := by
  simp only [squarefree_iff_prime_squarefree, ← sq, ← forall_and]
  -- ⊢ (∀ (x : ℕ), Prime x → ¬x ^ 2 ∣ m * n) ↔ ∀ (x : ℕ), Prime x → ¬x ^ 2 ∣ m ∧ ¬x …
  refine' ball_congr fun p hp => _
  -- ⊢ ¬p ^ 2 ∣ m * n ↔ ¬p ^ 2 ∣ m ∧ ¬p ^ 2 ∣ n
  simp only [hmn.isPrimePow_dvd_mul (hp.isPrimePow.pow two_ne_zero), not_or]
  -- 🎉 no goals
#align nat.squarefree_mul Nat.squarefree_mul

theorem coprime_of_squarefree_mul {m n : ℕ} (h : Squarefree (m * n)) : m.coprime n :=
  coprime_of_dvd fun p hp hm hn => squarefree_iff_prime_squarefree.mp h p hp (mul_dvd_mul hm hn)

theorem squarefree_mul_iff {m n : ℕ} :
    Squarefree (m * n) ↔ m.coprime n ∧ Squarefree m ∧ Squarefree n :=
  ⟨fun h => ⟨coprime_of_squarefree_mul h, (squarefree_mul $ coprime_of_squarefree_mul h).mp h⟩,
    fun h => (squarefree_mul h.1).mpr h.2⟩

theorem prod_factors_toFinset_of_squarefree {n : ℕ} (hn : Squarefree n) :
    ∏ p in n.factors.toFinset, p = n := by
  erw [List.prod_toFinset _ hn.nodup_factors, List.map_id, Nat.prod_factors hn.ne_zero]
  -- 🎉 no goals

end Nat

-- Porting note: comment out NormNum tactic, to be moved to another file.
/-

/-! ### Square-free prover -/


open NormNum

namespace Tactic

namespace NormNum

/-- A predicate representing partial progress in a proof of `squarefree`. -/
def SquarefreeHelper (n k : ℕ) : Prop :=
  0 < k → (∀ m, Nat.Prime m → m ∣ bit1 n → bit1 k ≤ m) → Squarefree (bit1 n)
#align tactic.norm_num.squarefree_helper Tactic.NormNum.SquarefreeHelper

theorem squarefree_bit10 (n : ℕ) (h : SquarefreeHelper n 1) : Squarefree (bit0 (bit1 n)) := by
  refine' @Nat.minSqFacProp_div _ _ Nat.prime_two two_dvd_bit0 _ none _
  · rw [bit0_eq_two_mul (bit1 n), mul_dvd_mul_iff_left (two_ne_zero' ℕ)]
    exact Nat.not_two_dvd_bit1 _
  · rw [bit0_eq_two_mul, Nat.mul_div_right _ (by decide : 0 < 2)]
    refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
    rintro rfl
    exact Nat.not_two_dvd_bit1 _ dp
#align tactic.norm_num.squarefree_bit10 Tactic.NormNum.squarefree_bit10

theorem squarefree_bit1 (n : ℕ) (h : SquarefreeHelper n 1) : Squarefree (bit1 n) := by
  refine' h (by decide) fun p pp dp => Nat.succ_le_of_lt (lt_of_le_of_ne pp.two_le _)
  rintro rfl; exact Nat.not_two_dvd_bit1 _ dp
#align tactic.norm_num.squarefree_bit1 Tactic.NormNum.squarefree_bit1

theorem squarefree_helper_0 {k} (k0 : 0 < k) {p : ℕ} (pp : Nat.Prime p) (h : bit1 k ≤ p) :
    bit1 (k + 1) ≤ p ∨ bit1 k = p := by
  rcases lt_or_eq_of_le h with ((hp : _ + 1 ≤ _) | hp)
  · rw [bit1, bit0_eq_two_mul] at hp
    change 2 * (_ + 1) ≤ _ at hp
    rw [bit1, bit0_eq_two_mul]
    refine' Or.inl (lt_of_le_of_ne hp _)
    rintro rfl
    exact Nat.not_prime_mul (by decide) (lt_add_of_pos_left _ k0) pp
  · exact Or.inr hp
#align tactic.norm_num.squarefree_helper_0 Tactic.NormNum.squarefree_helper_0

theorem squarefreeHelper_1 (n k k' : ℕ) (e : k + 1 = k')
    (hk : Nat.Prime (bit1 k) → ¬bit1 k ∣ bit1 n) (H : SquarefreeHelper n k') :
    SquarefreeHelper n k := fun k0 ih => by
  subst e
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp dp)).resolve_right fun hp => _
  subst hp; cases hk pp dp
#align tactic.norm_num.squarefree_helper_1 Tactic.NormNum.squarefreeHelper_1

theorem squarefreeHelper_2 (n k k' c : ℕ) (e : k + 1 = k') (hc : bit1 n % bit1 k = c) (c0 : 0 < c)
    (h : SquarefreeHelper n k') : SquarefreeHelper n k := by
  refine' squarefree_helper_1 _ _ _ e (fun _ => _) h
  refine' mt _ (ne_of_gt c0); intro e₁
  rwa [← hc, ← Nat.dvd_iff_mod_eq_zero]
#align tactic.norm_num.squarefree_helper_2 Tactic.NormNum.squarefreeHelper_2

theorem squarefreeHelper_3 (n n' k k' c : ℕ) (e : k + 1 = k') (hn' : bit1 n' * bit1 k = bit1 n)
    (hc : bit1 n' % bit1 k = c) (c0 : 0 < c) (H : SquarefreeHelper n' k') : SquarefreeHelper n k :=
  fun k0 ih => by
  subst e
  have k0' : 0 < bit1 k := bit1_pos (Nat.zero_le _)
  have dn' : bit1 n' ∣ bit1 n := ⟨_, hn'.symm⟩
  have dk : bit1 k ∣ bit1 n := ⟨_, ((mul_comm _ _).trans hn').symm⟩
  have : bit1 n / bit1 k = bit1 n' := by rw [← hn', Nat.mul_div_cancel _ k0']
  have k2 : 2 ≤ bit1 k := Nat.succ_le_succ (bit0_pos k0)
  have pk : (bit1 k).Prime := by
    refine' Nat.prime_def_minFac.2 ⟨k2, le_antisymm (Nat.minFac_le k0') _⟩
    exact ih _ (Nat.minFac_prime (ne_of_gt k2)) (dvd_trans (Nat.minFac_dvd _) dk)
  have dkk' : ¬bit1 k ∣ bit1 n' := by
    rw [Nat.dvd_iff_mod_eq_zero, hc]
    exact ne_of_gt c0
  have dkk : ¬bit1 k * bit1 k ∣ bit1 n := by rwa [← Nat.dvd_div_iff dk, this]
  refine' @Nat.minSqFacProp_div _ _ pk dk dkk none _
  rw [this]
  refine' H (Nat.succ_pos _) fun p pp dp => _
  refine' (squarefree_helper_0 k0 pp (ih p pp <| dvd_trans dp dn')).resolve_right fun e => _
  subst e
  contradiction
#align tactic.norm_num.squarefree_helper_3 Tactic.NormNum.squarefreeHelper_3

theorem squarefreeHelper_4 (n k k' : ℕ) (e : bit1 k * bit1 k = k') (hd : bit1 n < k') :
    SquarefreeHelper n k := by
  cases' Nat.eq_zero_or_pos n with h h
  · subst n
    exact fun _ _ => squarefree_one
  subst e
  refine' fun k0 ih => Irreducible.squarefree (Nat.prime_def_le_sqrt.2 ⟨bit1_lt_bit1.2 h, _⟩)
  intro m m2 hm md
  obtain ⟨p, pp, hp⟩ := Nat.exists_prime_and_dvd (ne_of_gt m2)
  have :=
    (ih p pp (dvd_trans hp md)).trans
      (le_trans (Nat.le_of_dvd (lt_of_lt_of_le (by decide) m2) hp) hm)
  rw [Nat.le_sqrt] at this
  exact not_le_of_lt hd this
#align tactic.norm_num.squarefree_helper_4 Tactic.NormNum.squarefreeHelper_4

theorem not_squarefree_mul (a aa b n : ℕ) (ha : a * a = aa) (hb : aa * b = n) (h₁ : 1 < a) :
    ¬Squarefree n := by
  rw [← hb, ← ha]
  exact fun H => ne_of_gt h₁ (Nat.isUnit_iff.1 <| H _ ⟨_, rfl⟩)
#align tactic.norm_num.not_squarefree_mul Tactic.NormNum.not_squarefree_mul

/-- Given `e` a natural numeral and `a : nat` with `a^2 ∣ n`, return `⊢ ¬ squarefree e`. -/
unsafe def prove_non_squarefree (e : expr) (n a : ℕ) : tactic expr := do
  let ea := reflect a
  let eaa := reflect (a * a)
  let c ← mk_instance_cache q(Nat)
  let (c, p₁) ← prove_lt_nat c q(1) ea
  let b := n / (a * a)
  let eb := reflect b
  let (c, eaa, pa) ← prove_mul_nat c ea ea
  let (c, e', pb) ← prove_mul_nat c eaa eb
  guard (e' == e)
  return <| q(@not_squarefree_mul).mk_app [ea, eaa, eb, e, pa, pb, p₁]
#align tactic.norm_num.prove_non_squarefree tactic.norm_num.prove_non_squarefree

/-- Given `en`,`en1 := bit1 en`, `n1` the value of `en1`, `ek`,
  returns `⊢ squarefree_helper en ek`. -/
unsafe def prove_squarefree_aux :
    ∀ (ic : instance_cache) (en en1 : expr) (n1 : ℕ) (ek : expr) (k : ℕ), tactic expr
  | ic, en, en1, n1, ek, k => do
    let k1 := bit1 k
    let ek1 := q((bit1 : ℕ → ℕ)).mk_app [ek]
    if n1 < k1 * k1 then do
        let (ic, ek', p₁) ← prove_mul_nat ic ek1 ek1
        let (ic, p₂) ← prove_lt_nat ic en1 ek'
        pure <| q(squarefreeHelper_4).mk_app [en, ek, ek', p₁, p₂]
      else do
        let c := n1 % k1
        let k' := k + 1
        let ek' := reflect k'
        let (ic, p₁) ← prove_succ ic ek ek'
        if c = 0 then do
            let n1' := n1 / k1
            let n' := n1' / 2
            let en' := reflect n'
            let en1' := q((bit1 : ℕ → ℕ)).mk_app [en']
            let (ic, _, pn') ← prove_mul_nat ic en1' ek1
            let c := n1' % k1
            guard (c ≠ 0)
            let (ic, ec, pc) ← prove_div_mod ic en1' ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en' en1' n1' ek' k'
            pure <| q(squarefreeHelper_3).mk_app [en, en', ek, ek', ec, p₁, pn', pc, p₀, p₂]
          else do
            let (ic, ec, pc) ← prove_div_mod ic en1 ek1 tt
            let (ic, p₀) ← prove_pos ic ec
            let p₂ ← prove_squarefree_aux ic en en1 n1 ek' k'
            pure <| q(squarefreeHelper_2).mk_app [en, ek, ek', ec, p₁, pc, p₀, p₂]
#align tactic.norm_num.prove_squarefree_aux tactic.norm_num.prove_squarefree_aux

/-- Given `n > 0` a squarefree natural numeral, returns `⊢ squarefree n`. -/
unsafe def prove_squarefree (en : expr) (n : ℕ) : tactic expr :=
  match match_numeral en with
  | match_numeral_result.one => pure q(@squarefree_one ℕ _)
  | match_numeral_result.bit0 en1 =>
    match match_numeral en1 with
    | match_numeral_result.one => pure q(Nat.squarefree_two)
    | match_numeral_result.bit1 en => do
      let ic ← mk_instance_cache q(ℕ)
      let p ← prove_squarefree_aux ic en en1 (n / 2) q((1 : ℕ)) 1
      pure <| q(squarefree_bit10).mk_app [en, p]
    | _ => failed
  | match_numeral_result.bit1 en' => do
    let ic ← mk_instance_cache q(ℕ)
    let p ← prove_squarefree_aux ic en' en n q((1 : ℕ)) 1
    pure <| q(squarefree_bit1).mk_app [en', p]
  | _ => failed
#align tactic.norm_num.prove_squarefree tactic.norm_num.prove_squarefree

/-- Evaluates the `squarefree` predicate on naturals. -/
@[norm_num]
unsafe def eval_squarefree : expr → tactic (expr × expr)
  | q(@Squarefree ℕ $(inst) $(e)) => do
    is_def_eq inst q(Nat.monoid)
    let n ← e.toNat
    match n with
      | 0 => false_intro q(@not_squarefree_zero ℕ _ _)
      | 1 => true_intro q(@squarefree_one ℕ _)
      | _ =>
        match n with
        | some d => prove_non_squarefree e n d >>= false_intro
        | none => prove_squarefree e n >>= true_intro
  | _ => failed
#align tactic.norm_num.eval_squarefree tactic.norm_num.eval_squarefree

end NormNum

end Tactic

-/
