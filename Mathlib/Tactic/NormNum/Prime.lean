/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.NormNum.Basic

#align_import data.nat.prime_norm_num from "leanprover-community/mathlib"@"10b4e499f43088dd3bb7b5796184ad5216648ab1"

/-!
# `norm_num` extensions on natural numbers

This file provides a `norm_num` extension to prove that natural numbers are prime and compute
its minimal factor. Todo: compute the list of all factors.


## Implementation Notes

For numbers larger than 25 bits, the primality proof produced by `norm_num` is an expression
that is thousands of levels deep, and the Lean kernel seems to raise a stack overflow when
type-checking that proof. If we want an implementation that works for larger primes, we should
generate a proof that has a smaller depth.

Note: `evalMinFac.aux` does not raise a stack overflow, which can be checked by replacing the
`prf'` in the recursive call by something like `(.sort .zero)`
-/

open Nat Qq Lean Meta

namespace Mathlib.Meta.NormNum

theorem not_prime_mul_of_ble (a b n : ℕ) (h : a * b = n) (h₁ : a.ble 1 = false)
    (h₂ : b.ble 1 = false) : ¬ n.Prime :=
  not_prime_mul' h (ble_eq_false.mp h₁) (ble_eq_false.mp h₂)

/-- Produce a proof that `n` is not prime from a factor `1 < d < n`. `en` should be the expression
  that is the natural number literal `n`. -/
def deriveNotPrime (n d : ℕ) (en : Q(ℕ)) : Q(¬ Nat.Prime $en) := Id.run <| do
  let d' : ℕ := n / d
  let prf : Q($d * $d' = $en) := (q(Eq.refl $en) : Expr)
  let r : Q(Nat.ble $d 1 = false) := (q(Eq.refl false) : Expr)
  let r' : Q(Nat.ble $d' 1 = false) := (q(Eq.refl false) : Expr)
  return q(not_prime_mul_of_ble _ _ _ $prf $r $r')

/-- A predicate representing partial progress in a proof of `minFac`. -/
def MinFacHelper (n k : ℕ) : Prop :=
  2 < k ∧ k % 2 = 1 ∧ k ≤ minFac n

theorem MinFacHelper.one_lt {n k : ℕ} (h : MinFacHelper n k) : 1 < n := by
  have : 2 < minFac n := h.1.trans_le h.2.2
  -- ⊢ 1 < n
  rcases eq_zero_or_pos n with rfl|h
  -- ⊢ 1 < 0
  · contradiction
    -- 🎉 no goals
  rcases (succ_le_of_lt h).eq_or_lt with rfl|h
  -- ⊢ 1 < succ 0
  · contradiction
    -- 🎉 no goals
  exact h
  -- 🎉 no goals

theorem minFacHelper_0 (n : ℕ)
    (h1 : Nat.ble (nat_lit 2) n = true) (h2 : nat_lit 1 = n % (nat_lit 2)) :
    MinFacHelper n (nat_lit 3) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  -- ⊢ 3 ≤ minFac n
  refine (le_minFac'.mpr λ p hp hpn ↦ ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))
  -- ⊢ 3 ≤ p
  rcases hp.eq_or_lt with rfl|h
  -- ⊢ 3 ≤ 2
  · simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2
    -- 🎉 no goals
  · exact h
    -- 🎉 no goals

theorem minFacHelper_1 {n k k' : ℕ} (e : k + 2 = k') (h : MinFacHelper n k)
  (np : minFac n ≠ k) : MinFacHelper n k' := by
  rw [← e]
  -- ⊢ MinFacHelper n (k + 2)
  refine ⟨Nat.lt_add_right _ _ _ h.1, ?_, ?_⟩
  -- ⊢ (k + 2) % 2 = 1
  · rw [add_mod, mod_self, add_zero, mod_mod]
    -- ⊢ k % 2 = 1
    exact h.2.1
    -- 🎉 no goals
  rcases h.2.2.eq_or_lt with rfl|h2
  -- ⊢ minFac n + 2 ≤ minFac n
  · exact (np rfl).elim
    -- 🎉 no goals
  rcases (succ_le_of_lt h2).eq_or_lt with h2|h2
  -- ⊢ k + 2 ≤ minFac n
  · refine ((h.1.trans_le h.2.2).ne ?_).elim
    -- ⊢ 2 = minFac n
    have h3 : 2 ∣ minFac n
    -- ⊢ 2 ∣ minFac n
    · rw [Nat.dvd_iff_mod_eq_zero, ← h2, succ_eq_add_one, add_mod, h.2.1]
      -- ⊢ (1 + 1 % 2) % 2 = 0
      norm_num
      -- 🎉 no goals
    rw [dvd_prime <| minFac_prime h.one_lt.ne'] at h3
    -- ⊢ 2 = minFac n
    norm_num at h3
    -- ⊢ 2 = minFac n
    exact h3
    -- 🎉 no goals
  exact h2
  -- 🎉 no goals

theorem minFacHelper_2 {n k k' : ℕ} (e : k + 2 = k') (nk : ¬ Nat.Prime k)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h λ h2 ↦ ?_
  -- ⊢ False
  rw [← h2] at nk
  -- ⊢ False
  exact nk <| minFac_prime h.one_lt.ne'
  -- 🎉 no goals

theorem minFacHelper_3 {n k k' : ℕ} (e : k + 2 = k') (nk : (n % k).beq 0 = false)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h λ h2 ↦ ?_
  -- ⊢ False
  have nk := Nat.ne_of_beq_eq_false nk
  -- ⊢ False
  rw [← Nat.dvd_iff_mod_eq_zero, ← h2] at nk
  -- ⊢ False
  exact nk <| minFac_dvd n
  -- 🎉 no goals

theorem isNat_minFac_1 : {a : ℕ} → IsNat a (nat_lit 1) → IsNat a.minFac 1
  | _, ⟨rfl⟩ => ⟨minFac_one⟩

theorem isNat_minFac_2 : {a a' : ℕ} → IsNat a a' → a' % 2 = 0 → IsNat a.minFac 2
  | a, _, ⟨rfl⟩, h => ⟨by rw [cast_ofNat, minFac_eq_two_iff, Nat.dvd_iff_mod_eq_zero, h]⟩
                          -- 🎉 no goals

theorem isNat_minFac_3 : {n n' : ℕ} → (k : ℕ) →
    IsNat n n' → MinFacHelper n' k → nat_lit 0 = n' % k → IsNat (minFac n) k
  | n, _, k, ⟨rfl⟩, h1, h2 => by
    rw [eq_comm, ← Nat.dvd_iff_mod_eq_zero] at h2
    -- ⊢ IsNat (minFac n) k
    exact ⟨le_antisymm (minFac_le_of_dvd h1.1.le h2) h1.2.2⟩
    -- 🎉 no goals

theorem isNat_minFac_4 : {n n' k : ℕ} →
    IsNat n n' → MinFacHelper n' k → (k * k).ble n' = false → IsNat (minFac n) n'
  | n, _, k, ⟨rfl⟩, h1, h2 => by
    refine ⟨(Nat.prime_def_minFac.mp ?_).2⟩
    -- ⊢ Nat.Prime n
    rw [Nat.prime_def_le_sqrt]
    -- ⊢ 2 ≤ n ∧ ∀ (m : ℕ), 2 ≤ m → m ≤ sqrt n → ¬m ∣ n
    refine ⟨h1.one_lt, λ m hm hmn h2mn ↦ ?_⟩
    -- ⊢ False
    exact lt_irrefl m <| calc
      m ≤ sqrt n   := hmn
      _ < k        := sqrt_lt.mpr (ble_eq_false.mp h2)
      _ ≤ n.minFac := h1.2.2
      _ ≤ m        := Nat.minFac_le_of_dvd hm h2mn

/-- The `norm_num` extension which identifies expressions of the form `minFac n`. -/
@[norm_num Nat.minFac _] partial def evalMinFac :
  NormNumExt where eval {u α} e := do
  let .app (.const ``Nat.minFac _) (n : Q(ℕ)) ← whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨nn, pn⟩ ← deriveNat n sℕ
  let n' := nn.natLit!
  let rec aux (ek : Q(ℕ)) (prf : Q(MinFacHelper $nn $ek)) :
      (c : Q(ℕ)) × Q(IsNat (Nat.minFac $n) $c) :=
    let k := ek.natLit!
    -- remark: `deriveBool q($nn < $ek * $ek)` is 2x slower than the following test.
    if n' < k * k then
      let r : Q(Nat.ble ($ek * $ek) $nn = false) := (q(Eq.refl false) : Expr)
      ⟨nn, q(isNat_minFac_4 $pn $prf $r)⟩
    else
      let d : ℕ := k.minFac
      -- the following branch is not necessary for the correctness,
      -- but makes the algorithm 2x faster
      if d < k then
        have ek' : Q(ℕ) := mkRawNatLit <| k + 2
        let pk' : Q($ek + 2 = $ek') := (q(Eq.refl $ek') : Expr)
        let pd := deriveNotPrime k d ek
        aux ek' q(minFacHelper_2 $pk' $pd $prf)
      -- remark: `deriveBool q($nn % $ek = 0)` is 5x slower than the following test
      else if n' % k = 0 then
        let r : Q(nat_lit 0 = $nn % $ek) := (q(Eq.refl 0) : Expr)
        let r' : Q(IsNat (minFac $n) $ek) := q(isNat_minFac_3 _ $pn $prf $r)
        ⟨ek, r'⟩
      else
        let r : Q(Nat.beq ($nn % $ek) 0 = false) := (q(Eq.refl false) : Expr)
        have ek' : Q(ℕ) := mkRawNatLit <| k + 2
        let pk' : Q($ek + 2 = $ek') := (q(Eq.refl $ek') : Expr)
        aux ek' q(minFacHelper_3 $pk' $r $prf)
  let rec core : MetaM <| Result q(Nat.minFac $n) := do
    if n' = 1 then
      let pn : Q(IsNat $n (nat_lit 1)) := pn
      return .isNat sℕ q(nat_lit 1) q(isNat_minFac_1 $pn)
    if n' % 2 = 0 then
      let pq : Q($nn % 2 = 0) := (q(Eq.refl 0) : Expr)
      return .isNat sℕ q(nat_lit 2) q(isNat_minFac_2 $pn $pq)
    let pp : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
    let pq : Q(1 = $nn % 2) := (q(Eq.refl (nat_lit 1)) : Expr)
    let ⟨c, pc⟩ := aux q(nat_lit 3) q(minFacHelper_0 $nn $pp $pq)
    return .isNat sℕ c pc
  core

theorem isNat_prime_0 : {n : ℕ} → IsNat n (nat_lit 0) → ¬ n.Prime
  | _, ⟨rfl⟩ => not_prime_zero

theorem isNat_prime_1 : {n : ℕ} → IsNat n (nat_lit 1) → ¬ n.Prime
  | _, ⟨rfl⟩ => not_prime_one

theorem isNat_prime_2 : {n n' : ℕ} →
    IsNat n n' → Nat.ble 2 n' = true → IsNat (minFac n') n' → n.Prime
  | _, _, ⟨rfl⟩, h1, ⟨h2⟩ => prime_def_minFac.mpr ⟨ble_eq.mp h1, h2⟩

theorem isNat_not_prime {n n' : ℕ} (h : IsNat n n') : ¬n'.Prime → ¬n.Prime := isNat.natElim h

/-- The `norm_num` extension which identifies expressions of the form `Nat.Prime n`. -/
@[norm_num Nat.Prime _] def evalNatPrime : NormNumExt where eval {u α} e := do
  let .app (.const `Nat.Prime _) (n : Q(ℕ)) ← whnfR e | failure
  let ⟨nn, pn⟩ ← deriveNat n _
  let n' := nn.natLit!
  -- note: if `n` is not prime, we don't have to verify the calculation of `n.minFac`, we just have
  -- to compute it, which is a lot quicker
  let rec core : MetaM (Result q(Nat.Prime $n)) := do
    match n' with
    | 0 => haveI' : $nn =Q 0 := ⟨⟩; return .isFalse q(isNat_prime_0 $pn)
    | 1 => haveI' : $nn =Q 1 := ⟨⟩; return .isFalse q(isNat_prime_1 $pn)
    | _ =>
      let d := n'.minFac
      if d < n' then
        let prf : Q(¬ Nat.Prime $nn) := deriveNotPrime n' d nn
        return .isFalse q(isNat_not_prime $pn $prf)
      let r : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
      let .isNat _ _lit (p2n : Q(IsNat (minFac $nn) $nn)) ←
        evalMinFac.core nn _ nn q(.raw_refl _) nn.natLit! | failure
      return .isTrue q(isNat_prime_2 $pn $r $p2n)
  core

/-
/-- A partial proof of `factors`. Asserts that `l` is a sorted list of primes, lower bounded by a
prime `p`, which multiplies to `n`. -/
def FactorsHelper (n p : ℕ) (l : List ℕ) : Prop :=
  p.Prime → List.Chain (· ≤ ·) p l ∧ (∀ a ∈ l, Nat.Prime a) ∧ List.prod l = n

theorem factorsHelper_nil (a : ℕ) : FactorsHelper 1 a [] := fun _ =>
  ⟨List.Chain.nil, by rintro _ ⟨⟩, List.prod_nil⟩

theorem factorsHelper_cons' (n m a b : ℕ) (l : List ℕ) (h₁ : b * m = n) (h₂ : a ≤ b)
    (h₃ : minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) := fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.Chain.cons h₂ f₁,
    fun c h => (List.eq_or_mem_of_mem_cons h).elim (fun e => e.symm ▸ pb) (f₂ _),
    by rw [List.prod_cons, f₃, h₁]⟩

theorem factorsHelper_cons (n m a b : ℕ) (l : List ℕ) (h₁ : b * m = n) (h₂ : a < b)
    (h₃ : minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) :=
  factorsHelper_cons' _ _ _ _ _ h₁ h₂.le h₃ H

theorem factorsHelper_sn (n a : ℕ) (h₁ : a < n) (h₂ : minFac n = n) : FactorsHelper n a [n] :=
  factorsHelper_cons _ _ _ _ _ (mul_one _) h₁ h₂ (factorsHelper_nil _)

theorem factorsHelper_same (n m a : ℕ) (l : List ℕ) (h : a * m = n) (H : FactorsHelper m a l) :
    FactorsHelper n a (a :: l) := fun pa =>
  factorsHelper_cons' _ _ _ _ _ h le_rfl (Nat.prime_def_minFac.1 pa).2 H pa

theorem factorsHelper_same_sn (a : ℕ) : FactorsHelper a a [a] :=
  factorsHelper_same _ _ _ _ (mul_one _) (factorsHelper_nil _)

theorem factorsHelper_end (n : ℕ) (l : List ℕ) (H : FactorsHelper n 2 l) : Nat.factors n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.chain'_iff_pairwise.1 (@List.Chain'.tail _ _ (_ :: _) h₁)
  (List.eq_of_perm_of_sorted (Nat.factors_unique h₃ h₂) this (Nat.factors_sorted _)).symm
-/
