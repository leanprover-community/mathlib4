/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Data.Nat.Factorization.PrimePow
public import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
public import Mathlib.NumberTheory.FermatPsp
public import Mathlib.Tactic.Simproc.Factors

/-!
# Carmichael numbers

This file defines Carmichael numbers and proves Korselt's criterion about them.

## Main definitions

* `Nat.IsCarmichael`: a predicate for Carmicheal numbers

## Main results

* `Nat.isCarmichael_iff_korselt`: Korselt's criterion for Carmichael numbers
* `Nat.isCarmichael_561`: `561` is a Carmichael number

`decide`, `#eval` and `norm_num` know how to efficiently decide whether a number is Carmichael
by leveraging Korselt's criterion.

## References

https://en.wikipedia.org/wiki/Carmichael_number

-/

public section

namespace Nat

open ArithmeticFunction

/-- We say a natural number `n` is a Carmichael number if it is greater than 2, composite and
for all natural numbers `b` coprime to `n` we have `n ∣ b ^ (n - 1) - 1`. -/
@[expose]
def IsCarmichael (n : ℕ) : Prop :=
  2 < n ∧ ¬ n.Prime ∧ ∀ b, b.Coprime n → ProbablePrime n b

variable {n : ℕ}

theorem IsCarmichael.two_lt (h : n.IsCarmichael) : 2 < n := h.1

theorem IsCarmichael.neZero (h : n.IsCarmichael) : NeZero n :=
  ⟨by grind [h.two_lt]⟩

theorem IsCarmichael.not_prime (h : n.IsCarmichael) : ¬ n.Prime := h.2.1

theorem IsCarmichael.probablePrime_of_coprime {b : ℕ} (h : n.IsCarmichael) (hb : b.Coprime n) :
    ProbablePrime n b := h.2.2 b hb

theorem Prime.not_isCarmichael (hn : n.Prime) : ¬ n.IsCarmichael := by
  contrapose hn
  exact hn.not_prime

@[simp]
theorem not_isCarmichael_zero : ¬ IsCarmichael 0 := by
  intro h
  simpa using h.two_lt

@[simp]
theorem not_isCarmichael_one : ¬ IsCarmichael 1 := by
  intro h
  simpa using h.two_lt

lemma IsCarmichael.zmod_unit_pow_sub_one (s : (ZMod n)ˣ) (hn : n.IsCarmichael) :
  s ^ (n - 1) = 1 := by
  have : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr (by grind [hn.two_lt])
  ext
  have : NeZero n := hn.neZero
  rw [Units.val_one, Units.val_pow_eq_pow_val, ← ZMod.natCast_zmod_val s.val,
    ← probablePrime_iff_zmod_one n (by simp [Units.ne_zero s])]
  exact hn.probablePrime_of_coprime <| ZMod.val_coe_unit_coprime s

/-- A Carmichael number is odd. -/
theorem IsCarmichael.odd (h : n.IsCarmichael) : Odd n := by
  match n with
  | 0 => exact (not_isCarmichael_zero h).elim
  | n + 1 =>
    have H := h.zmod_unit_pow_sub_one (-1)
    rw [Nat.add_one_sub_one, neg_one_pow_eq_ite] at H
    contrapose! H
    rw [ite_eq_right (by grind), ne_eq, Units.ext_iff, Units.val_one, Units.coe_neg_one,
      ZMod.neg_one_eq_one_iff]
    grind [h.two_lt]

/-- A Carmichael number is squarefree. -/
theorem IsCarmichael.squarefree (h : n.IsCarmichael) : Squarefree n := by
  refine squarefree_iff_prime_squarefree.mpr fun p hp p_dvd ↦ ?_
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have p_odd : Odd p := h.odd.of_dvd_nat <| dvd_trans (p.dvd_mul_left p) p_dvd
  obtain ⟨r, hr⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp <|
    (ZMod.isCyclic_units_iff_of_odd p_odd.pow).mpr ⟨p, 2, hp, p_odd, rfl⟩
  rw [card_eq_fintype_card, ZMod.card_units_eq_totient] at hr
  have : NeZero n := h.neZero
  obtain ⟨s, hs⟩ := ZMod.unitsMap_surjective (pow_two p ▸ p_dvd) r
  have phi_dvd : φ (p ^ 2) ∣ n - 1 := by
    rw [← hr, ← hs]
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, h.zmod_unit_pow_sub_one, map_one]
  have p_dvd_n : p ∣ n := dvd_trans (dvd_mul_left p p) p_dvd
  refine hp.not_dvd_one <| dvd_sub_iff_right (by grind [h.two_lt]) p_dvd_n |>.mp ?_
  exact dvd_trans (by simp [totient_prime_pow_succ hp 1]) phi_dvd

theorem IsCarmichael.carmichael_dvd_sub_one (h : n.IsCarmichael) : carmichael n ∣ n - 1 := by
  rw [@carmichael_eq_exponent' n h.neZero]
  exact Monoid.exponent_dvd_of_forall_pow_eq_one h.zmod_unit_pow_sub_one

theorem IsCarmichael.prime_sub_one_dvd {p : ℕ} (h : n.IsCarmichael) (hp : p.Prime) (hpn : p ∣ n) :
    p - 1 ∣ n - 1 := by
  refine dvd_trans ?_ h.carmichael_dvd_sub_one
  rw [← carmichael_of_prime hp]
  exact carmichael_dvd (by simpa using hpn)

/-- **Korselt's criterion** for Carmichael numbers:
`n` is a Carmichael number if and only if it is greater than two, composite, squarefree, and for
each prime divisor `p` of `n`, we have `p - 1 ∣ n - 1`. -/
theorem isCarmichael_iff_korselt :
    n.IsCarmichael ↔ 2 < n ∧ ¬n.Prime ∧ Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
  refine ⟨fun h ↦ ⟨h.two_lt, h.not_prime, h.squarefree, fun _ ↦ h.prime_sub_one_dvd⟩, ?_⟩
  intro ⟨hn, hn_prime, hn_squarefree, h_dvd⟩
  refine ⟨hn, hn_prime, fun b hb ↦ ?_⟩
  obtain ⟨d, hd⟩ : carmichael n ∣ n - 1 := by
    rw [@carmichael_factorization n ⟨by lia⟩]
    refine Finset.lcm_dvd fun p hp_mem ↦ ?_
    rw [mem_primeFactors] at hp_mem
    rw [factorization_eq_one_of_squarefree hn_squarefree hp_mem.1 hp_mem.2.1, pow_one,
      carmichael_of_prime hp_mem.1]
    exact h_dvd p hp_mem.1 hp_mem.2.1
  rw [probablePrime_iff_zmod_one n (by grind), ← ZMod.coe_unitOfCoprime b hb,
    ← Units.val_pow_eq_pow_val, hd, pow_mul, pow_carmichael, one_pow, Units.val_one]

theorem IsCarmichael.three_le_card_primeFactors (h : IsCarmichael n) :
    3 ≤ n.primeFactors.card := by
  obtain ⟨_, _, hs, h⟩ := isCarmichael_iff_korselt.mp h
  have h0 : n.primeFactors.card ≠ 0 := by grind [primeFactors_eq_empty]
  have h1 : n.primeFactors.card ≠ 1 := by
    grind [squarefree_and_prime_pow_iff_prime, isPrimePow_iff_card_primeFactors_eq_one]
  by_contra h3
  have h2 : n.primeFactors.card = 2 := by grind
  obtain ⟨p, q, pq, hp, hq, hn⟩ := (squarefree_and_primeFactors_card_eq_two_iff n).mp ⟨hs, h2⟩
  contrapose! pq
  have eq : p - 1 + (q - 1) * p = p * q - 1 := by zify; grind
  rw [← tsub_le_tsub_iff_right hp.one_le]
  refine le_of_dvd (tsub_pos_of_lt hp.one_lt) ((Nat.dvd_add_left ⟨p, rfl⟩).mp ?_)
  rw [eq, hn]
  exact h q hq (Dvd.intro_left p hn)

/-- **Korselt's criterion** stated in a form suitable for concrete calculations. -/
@[deprecated "Use `norm_num` or `decide` to decide whether a fixed natural number is Carmichael."
  (since := "2026-09-19")]
theorem isCarmichael_iff_korselt_primeFactorsList :
    n.IsCarmichael ↔
      2 < n ∧ ¬n.Prime ∧ n.primeFactorsList.Nodup ∧ ∀ p ∈ n.primeFactorsList, p - 1 ∣ n - 1 := by
  simp only [isCarmichael_iff_korselt, mem_primeFactorsList', ne_eq, and_imp, and_congr_right_iff]
  intro hn
  rw [squarefree_iff_nodup_primeFactorsList] <;> grind

/-- Auxiliary function for the decidability of `IsCarmichael`.

`korseltAux n fuel m d c` checks, by trial division of `m` starting at `d`, that `m` is squarefree
and that `p - 1 ∣ n - 1` for all prime factors `p` of `m`, returning `false` as soon as a prime
factor is repeated or does not satisfy the divisibility condition. It also checks that `c` is
`true` or `m` is not prime. Here `c` records whether a prime factor has already been removed.

It is defined by structural recursion on `fuel`, so that it can be evaluated by `decide`. See
`Nat.korseltAux_eq_true_iff` for the conditions under which it is correct. -/
def korseltAux (n fuel m d : ℕ) (c : Bool) : Bool :=
  if m ≤ 1 then m == 1
  else if m < d * d then c && (n - 1) % (m - 1) == 0
  else match fuel with
    | 0 => false
    | fuel + 1 =>
      if m % d = 0 then
        (n - 1) % (d - 1) == 0 && m / d % d != 0 && korseltAux n fuel (m / d) (d + 2) true
      else korseltAux n fuel m (d + 2) c

/-- If all prime factors of `m` are at least `d`, where `d ≥ 3` is odd, and `d ∤ m`, then all prime
factors of `m` are at least `d + 2`. -/
private lemma add_two_le_of_forall_prime_dvd {m d : ℕ} (hd : 3 ≤ d) (hdo : d % 2 = 1)
    (hm : ∀ p, p.Prime → p ∣ m → d ≤ p) (hdm : ¬ d ∣ m) :
    ∀ p, p.Prime → p ∣ m → d + 2 ≤ p := by
  intro p hp hpm
  have := hm p hp hpm
  have : p ≠ d := by rintro rfl; exact hdm hpm
  have : p ≠ d + 1 := by rintro rfl; have := hp.eq_two_or_odd; lia
  lia

theorem korseltAux_eq_true_iff {n fuel m d : ℕ} {c : Bool} (hd : 3 ≤ d) (hdo : d % 2 = 1)
    (hm : ∀ p, p.Prime → p ∣ m → d ≤ p) (hfuel : m < fuel + d) :
    korseltAux n fuel m d c = true ↔
      (c = true ∨ ¬ m.Prime) ∧ Squarefree m ∧ ∀ p, p.Prime → p ∣ m → p - 1 ∣ n - 1 := by
  induction fuel generalizing m d c with
  | zero | succ fuel ih =>
  unfold korseltAux
  split_ifs with h₁ h₂
  · obtain rfl | rfl : m = 0 ∨ m = 1 := by lia
    · simp
    · exact ⟨fun _ ↦ ⟨.inr not_prime_one, squarefree_one,
        fun p hp h ↦ (hp.ne_one (Nat.dvd_one.1 h)).elim⟩, fun _ ↦ rfl⟩
  · have hmp : m.Prime := by
      by_contra hmp
      have h := hm _ (minFac_prime (by lia)) (minFac_dvd m)
      have := (Nat.mul_le_mul h h).trans ((sq _).symm.trans_le (minFac_sq_le_self (by lia) hmp))
      lia
    rw [Bool.and_eq_true, beq_iff_eq, ← Nat.dvd_iff_mod_eq_zero]
    simp only [hmp, not_true_eq_false, or_false, hmp.prime.squarefree, true_and]
    exact and_congr_right fun _ ↦ ⟨fun h p hp hpm ↦ (prime_dvd_prime_iff_eq hp hmp).1 hpm ▸ h,
      fun h ↦ h m hmp dvd_rfl⟩
  -- when `fuel = 0`, the remaining goal contradicts `hfuel`
  all_goals try exact absurd hfuel (by have := Nat.le_mul_self d; lia)
  all_goals first
  | exact ih (by lia) (by lia) (add_two_le_of_forall_prime_dvd hd hdo hm
      fun h ↦ ‹¬ m % d = 0› (Nat.mod_eq_zero_of_dvd h)) (by lia)
  | have hdm : d ∣ m := Nat.dvd_of_mod_eq_zero ‹_›
    have hdp : d.Prime := by
      have := hm _ (minFac_prime (by lia : d ≠ 1)) ((minFac_dvd d).trans hdm)
      exact prime_def_minFac.2 ⟨by lia, le_antisymm (minFac_le (by lia)) this⟩
    obtain ⟨k, rfl⟩ := hdm
    rw [Nat.mul_div_cancel_left _ (by lia)]
    have hk : d ≤ k := Nat.le_of_mul_le_mul_left (not_lt.1 h₂) (by lia)
    have hkdk : k < d * k := by nlinarith
    have hnp : ¬ (d * k).Prime := not_prime_mul (by lia) (by lia)
    by_cases hdk : d ∣ k
    · have : ¬ Squarefree (d * k) := by
        rw [squarefree_mul_iff, hdp.coprime_iff_not_dvd]
        tauto
      simp [Nat.dvd_iff_mod_eq_zero.1 hdk, this]
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, ← Nat.dvd_iff_mod_eq_zero, hdk,
      not_false_eq_true, and_true]
    rw [ih (by lia) (by lia) (add_two_le_of_forall_prime_dvd hd hdo
      (fun p hp hpk ↦ hm p hp (dvd_mul_of_dvd_right hpk _)) hdk) (by lia)]
    simp only [true_or, true_and, hnp, not_false_eq_true, or_true, squarefree_mul_iff,
      hdp.coprime_iff_not_dvd, hdk, hdp.prime.squarefree]
    constructor
    · rintro ⟨hn, hsq, h⟩
      exact ⟨hsq, fun q hq hqd ↦ (hq.dvd_mul.1 hqd).elim
        (fun h' ↦ (prime_dvd_prime_iff_eq hq hdp).1 h' ▸ hn) (h q hq)⟩
    · rintro ⟨hsq, h⟩
      exact ⟨h d hdp (dvd_mul_right _ _), hsq, fun q hq hqd ↦ h q hq (dvd_mul_of_dvd_right hqd _)⟩

/-- Decidability of `IsCarmichael` via Korselt's criterion.

This instance is suitable both for `#eval` and for `decide`. -/
instance : DecidablePred IsCarmichael := fun n ↦
  decidable_of_iff (2 < n ∧ n % 2 = 1 ∧ korseltAux n n n 3 false = true) <| by
    have (h : n % 2 = 1) : korseltAux n n n 3 false = true ↔
        ¬ n.Prime ∧ Squarefree n ∧ ∀ p, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
      rw [korseltAux_eq_true_iff le_rfl rfl _ (by lia)]
      · simp
      intro p hp hpn
      have : p ≠ 2 := by rintro rfl; lia
      grind [hp.two_le]
    rw [isCarmichael_iff_korselt]
    constructor
    · rintro ⟨h2, hn, h⟩
      exact ⟨h2, (this hn).1 h⟩
    · rintro ⟨h2, h⟩
      have hn := Nat.odd_iff.1 (isCarmichael_iff_korselt.2 ⟨h2, h⟩).odd
      exact ⟨h2, hn, (this hn).2 h⟩

end Nat

/-! ### `norm_num` extension -/

namespace Mathlib.Meta.NormNum
open Lean Meta Qq Nat

/-- A predicate representing partial progress in a proof that `n` is a Carmichael number.

`KorseltHelper n m a` asserts that, provided `a` is prime, `m` is squarefree and all prime factors
`q` of `m` satisfy `a < q` and `q - 1 ∣ n - 1`. -/
def KorseltHelper (n m a : ℕ) : Prop :=
  a.Prime → Squarefree m ∧ ∀ q, q.Prime → q ∣ m → a < q ∧ q - 1 ∣ n - 1

lemma KorseltHelper.one (n a : ℕ) : KorseltHelper n (nat_lit 1) a :=
  fun _ ↦ ⟨squarefree_one, fun _ hq h ↦ (hq.not_dvd_one h).elim⟩

/-! The argument explicitness here is chosen to make only the numerals in the factorisation appear
in the proof term. -/

lemma KorseltHelper.mul {n m m' a : ℕ} (b : ℕ) (h₁ : b * m' = m) (h₂ : Nat.blt a b = true)
    (h₃ : IsNat (minFac b) b) (h₄ : Nat.beq ((n - 1) % (b - 1)) 0 = true)
    (H : KorseltHelper n m' b) : KorseltHelper n m a := fun ha ↦ by
  have hab := Nat.blt_eq.mp h₂
  have hb : b.Prime := prime_def_minFac.2 ⟨by grind [ha.two_le], by simpa using h₃.out⟩
  obtain ⟨hsq, hm'⟩ := H hb
  subst h₁
  refine ⟨squarefree_mul_iff.2 ⟨hb.coprime_iff_not_dvd.2 fun h ↦ (hm' b hb h).1.false,
    hb.prime.squarefree, hsq⟩, fun q hq hqd ↦ (hq.dvd_mul.1 hqd).elim (fun h ↦ ?_) fun h ↦ ?_⟩
  · obtain rfl := (prime_dvd_prime_iff_eq hq hb).1 h
    exact ⟨hab, Nat.dvd_of_mod_eq_zero (by simpa using h₄)⟩
  · exact ⟨hab.trans (hm' q hq h).1, (hm' q hq h).2⟩

lemma isCarmichael_of_korseltHelper {n : ℕ} (h₂ : Nat.blt 2 n = true) (hp : ¬ n.Prime)
    (H : KorseltHelper n n 2) : IsCarmichael n := by
  obtain ⟨hsq, h⟩ := H prime_two
  exact isCarmichael_iff_korselt.2 ⟨Nat.blt_eq.mp h₂, hp, hsq, fun q hq hd ↦ (h q hq hd).2⟩

lemma not_isCarmichael_of_ble_two {n : ℕ} (h : Nat.ble n 2 = true) : ¬ IsCarmichael n :=
  fun hn ↦ by grind [hn.two_lt, Nat.ble_eq]

lemma not_isCarmichael_of_mod_two_eq_zero {n : ℕ} (h : n % 2 = 0) : ¬ IsCarmichael n :=
  fun hn ↦ by grind [hn.odd]

lemma not_isCarmichael_of_mul_mul_eq {n : ℕ} (p k : ℕ) (h : p * p * k = n)
    (hp : Nat.blt 1 p = true) : ¬ IsCarmichael n := fun hn ↦ by
  have := Nat.isUnit_iff.mp <| hn.squarefree p ⟨k, h.symm⟩
  grind [Nat.blt_eq]

lemma not_isCarmichael_of_mul_eq {n : ℕ} (p k : ℕ) (h : p * k = n) (hp : p.Prime)
    (hd : Nat.beq ((n - 1) % (p - 1)) 0 = false) : ¬ IsCarmichael n := fun hn ↦ by
  have := hn.prime_sub_one_dvd hp ⟨k, h.symm⟩
  simp_all [Nat.dvd_iff_mod_eq_zero]

lemma isNat_isCarmichael : {n n' : ℕ} → IsNat n n' → IsCarmichael n' → IsCarmichael n
  | _, _, ⟨rfl⟩, h => h

lemma isNat_not_isCarmichael : {n n' : ℕ} → IsNat n n' → ¬ IsCarmichael n' → ¬ IsCarmichael n
  | _, _, ⟨rfl⟩, h => h

/-- Given a raw natural literal `ep` which is prime, produce a proof of `Nat.Prime ep`. -/
meta def deriveNatPrime (ep : Q(ℕ)) : MetaM Q($(ep).Prime) := do
  let p := ep.natLit!
  let r : Q(Nat.ble 2 $ep = true) := (q(Eq.refl true) : Expr)
  let .isNat _ _lit (h : Q(IsNat (minFac $ep) $ep)) ← evalMinFac.core ep ep q(.raw_refl _) p
    | failure
  return q(isNat_prime_2 (.raw_refl _) $r $h)

/-- The `norm_num` extension which computes expressions of the form `Nat.IsCarmichael n`
using Korselt's criterion. -/
@[norm_num Nat.IsCarmichael _]
meta def evalNatIsCarmichael : NormNumExt where eval {_ _} e := do
  let .app (.const ``Nat.IsCarmichael _) (n : Q(ℕ)) ← whnfR e | failure
  let ⟨nn, pn⟩ ← deriveNat n q(Nat.instAddMonoidWithOne)
  let n' := nn.natLit!
  let core : MetaM (Result q(Nat.IsCarmichael $nn)) := do
    if n' ≤ 2 then
      let r : Q(Nat.ble $nn 2 = true) := (q(Eq.refl true) : Expr)
      return .isFalse q(not_isCarmichael_of_ble_two $r)
    if n' % 2 = 0 then
      let r : Q($nn % 2 = 0) := (q(Eq.refl 0) : Expr)
      return .isFalse q(not_isCarmichael_of_mod_two_eq_zero $r)
    -- Trial division of `n`, exiting as soon as we find a prime factor that is repeated or doesn't
    -- satisfy Korselt's criterion.
    -- We maintain the invariant that `m` is the part of `n` not yet factored,
    -- that `m` has no prime factor less than `d` and that `prev` is the last prime factor found.
    let mut m := n'
    let mut d := 3
    let mut prev := 0
    let mut factors : Array ℕ := #[]
    while 1 < m do
      while d * d ≤ m && m % d ≠ 0 do
        d := d + 2
      let p' := if m % d = 0 then d else m
      if p' = prev then
        have ep : Q(ℕ) := mkRawNatLit p'
        have ek : Q(ℕ) := mkRawNatLit (n' / (p' * p'))
        let h : Q($ep * $ep * $ek = $nn) := (q(Eq.refl $nn) : Expr)
        let r : Q(Nat.blt 1 $ep = true) := (q(Eq.refl true) : Expr)
        return .isFalse q(not_isCarmichael_of_mul_mul_eq $ep $ek $h $r)
      if (n' - 1) % (p' - 1) ≠ 0 then
        have ep : Q(ℕ) := mkRawNatLit p'
        have ek : Q(ℕ) := mkRawNatLit (n' / p')
        let h : Q($ep * $ek = $nn) := (q(Eq.refl $nn) : Expr)
        let hp : Q($(ep).Prime) ← deriveNatPrime ep
        let r : Q(Nat.beq (($nn - 1) % ($ep - 1)) 0 = false) := (q(Eq.refl false) : Expr)
        return .isFalse q(not_isCarmichael_of_mul_eq $ep $ek $h $hp $r)
      prev := p'
      m := m / p'
      factors := factors.push p'
    if factors.size = 1 then
      -- `n` is prime
      let hp : Q($(nn).Prime) ← deriveNatPrime nn
      return .isFalse q(Nat.Prime.not_isCarmichael $hp)
    -- `n` has at least two distinct prime factors, hence is composite. We build
    -- the proof of `KorseltHelper n n 2` from the factors found, starting from the largest one.
    have elast : Q(ℕ) := mkRawNatLit factors.back!
    let mut em : Q(ℕ) := mkRawNatLit 1
    let mut pf : Expr := q(KorseltHelper.one $nn $elast)
    for i in [0:factors.size].toList.reverse do
      let b := factors[i]!
      have eb : Q(ℕ) := mkRawNatLit b
      have ea : Q(ℕ) := mkRawNatLit (if i = 0 then 2 else factors[i - 1]!)
      have em' : Q(ℕ) := em
      have em'' : Q(ℕ) := mkRawNatLit (b * em'.natLit!)
      let H : Q(KorseltHelper $nn $em' $eb) := pf
      let h₁ : Q($eb * $em' = $em'') := (q(Eq.refl $em'') : Expr)
      let h₂ : Q(Nat.blt $ea $eb = true) := (q(Eq.refl true) : Expr)
      let .isNat _ _lit (h₃ : Q(IsNat (minFac $eb) $eb)) ← evalMinFac.core eb eb q(.raw_refl _) b
        | failure
      let h₄ : Q(Nat.beq (($nn - 1) % ($eb - 1)) 0 = true) := (q(Eq.refl true) : Expr)
      pf := q(KorseltHelper.mul (a := $ea) $eb $h₁ $h₂ $h₃ $h₄ $H)
      em := em''
    let H : Q(KorseltHelper $nn $nn 2) := pf
    let h₂ : Q(Nat.blt 2 $nn = true) := (q(Eq.refl true) : Expr)
    let hp : Q(¬ Nat.Prime $nn) := deriveNotPrime n' factors[0]! nn
    return .isTrue q(isCarmichael_of_korseltHelper $h₂ $hp $H)
  match ← core with
  | .isTrue pf => return .isTrue q(isNat_isCarmichael $pn $pf)
  | .isFalse pf => return .isFalse q(isNat_not_isCarmichael $pn $pf)
  | _ => failure

end Mathlib.Meta.NormNum

namespace Nat

/-- 561 is a Carmichael number. -/
lemma isCarmichael_561 : IsCarmichael 561 := by norm_num

/-- 1105 is a Carmichael number. -/
lemma isCarmichael_1105 : IsCarmichael 1105 := by norm_num

/-- 561 is the smallest Carmichael number. -/
lemma isLeast_isCarmichael_561 : IsLeast {n | IsCarmichael n} 561 := by decide +kernel

end Nat
