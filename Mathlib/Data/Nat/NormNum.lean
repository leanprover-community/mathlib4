/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.prime_norm_num
! leanprover-community/mathlib commit 10b4e499f43088dd3bb7b5796184ad5216648ab1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Propose
/-!
# Primality prover

This file provides a `norm_num` extention to prove that natural numbers are prime and compute
its minimal factor. Todo: compute the list of all factors.

-/

open Nat Qq Lean Meta

namespace Mathlib.Meta.NormNum

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def MinFacHelper (n k : ℕ) : Prop :=
  2 < k ∧ k % 2 = 1 ∧ k ≤ minFac n

set_option maxHeartbeats 0 in
theorem MinFacHelper.one_lt {n k : ℕ} (h : MinFacHelper n k) : 1 < n := by
  have : 2 < minFac n := h.1.trans_le h.2.2
  rcases eq_zero_or_pos n with rfl|h
  · contradiction
  rcases (succ_le_of_lt h).eq_or_lt with rfl|h
  · contradiction
  exact h

theorem minFacHelper_0 (n : ℕ) (h1 : ¬ n = 1) (h2 : ¬ n % 2 = 0) : MinFacHelper n 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  refine (le_minFac'.mpr λ p hp hpn ↦ ?_).resolve_left h1
  rw [← Nat.dvd_iff_mod_eq_zero] at h2
  rcases hp.eq_or_lt with rfl|h
  · exact (h2 hpn).elim
  exact h

theorem minFacHelper_1 {n k k' : ℕ} (e : k + 2 = k') (h : MinFacHelper n k)
  (np : minFac n ≠ k) : MinFacHelper n k' := by
  rw [← e]
  refine ⟨Nat.lt_add_right _ _ _ h.1, ?_, ?_⟩
  · rw [add_mod, mod_self, add_zero, mod_mod]
    exact h.2.1
  rcases h.2.2.eq_or_lt with rfl|h2
  · exact (np rfl).elim
  rcases (succ_le_of_lt h2).eq_or_lt with h2|h2
  · refine ((h.1.trans_le h.2.2).ne ?_).elim
    have h3 : 2 ∣ minFac n
    · rw [Nat.dvd_iff_mod_eq_zero, ← h2, succ_eq_add_one, add_mod, h.2.1]
      norm_num
    rw [dvd_prime <| minFac_prime h.one_lt.ne'] at h3
    norm_num at h3
    exact h3
  exact h2

theorem minFacHelper_2 {n k k' : ℕ} (e : k + 2 = k') (nk : ¬ Nat.Prime k)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h λ h2 ↦ ?_
  rw [← h2] at nk
  exact nk <| minFac_prime h.one_lt.ne'

theorem minFacHelper_3 {n k k' : ℕ} (e : k + 2 = k') (nk : ¬ n % k = 0)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h λ h2 ↦ ?_
  rw [← Nat.dvd_iff_mod_eq_zero, ← h2] at nk
  exact nk <| minFac_dvd n

theorem isNat_minFac_1 : {a : ℕ} → {a' : ℕ} →
    IsNat a a' → a' = 1 → IsNat a.minFac 1
  | _, _, ⟨rfl⟩, rfl => ⟨minFac_one⟩

theorem isNat_minFac_2 : {a : ℕ} → {a' : ℕ} →
    IsNat a a' → a' % 2 = 0 → IsNat a.minFac 2
  | a, _, ⟨rfl⟩, h => ⟨by rw [cast_ofNat, minFac_eq_two_iff, Nat.dvd_iff_mod_eq_zero, h]⟩

theorem isNat_minFac_3 : {n : ℕ} → {n' : ℕ} → {k : ℕ} → {k' : ℕ} →
    IsNat n n' → IsNat k k' → MinFacHelper n' k → n' % k = 0 → IsNat (minFac n) k'
  | n, _, k, _, ⟨rfl⟩, ⟨rfl⟩, h1, h2 => by
    rw [← Nat.dvd_iff_mod_eq_zero] at h2
    exact ⟨le_antisymm (minFac_le_of_dvd h1.1.le h2) h1.2.2⟩

theorem isNat_minFac_4 : {n : ℕ} → {n' : ℕ} → {k : ℕ} →
    IsNat n n' → MinFacHelper n' k → n' < k * k → IsNat (minFac n) n'
  | n, _, k, ⟨rfl⟩, h1, h2 => by
    refine ⟨(Nat.prime_def_minFac.mp ?_).2⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h1.one_lt, λ m hm hmn h2mn ↦ ?_⟩
    exact lt_irrefl m <| calc
      m ≤ sqrt n   := hmn
      _ < k        := sqrt_lt.mpr h2
      _ ≤ n.minFac := h1.2.2
      _ ≤ m        := Nat.minFac_le_of_dvd hm h2mn

@[elab_as_elim]
theorem isNat.natElim {p : ℕ → Prop} : {n : ℕ} → {n' : ℕ} → IsNat n n' → p n' → p n
  | _, _, ⟨rfl⟩, h => h

theorem not_prime_of_lt_two (h : n < 2) : ¬ n.Prime :=
  fun hn => hn.two_le.not_lt h

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

open NormNum

/-- Given `Mathlib.Meta.NormNum.Result.isBool p b`, this is the type of `p`.
  Note that `BoolResult p b` is definitionally equal to `Expr`, and if you write `match b with ...`,
  then in the `true` branch `BoolResult p true` is reducibly equal to `Q($p)` and
  in the `false` branch it is reducibly equal to `Q(¬ $p)`. -/
@[reducible]
def BoolResult (p : Q(Prop)) (b : Bool) : Type :=
Q(Bool.rec (¬ $p) ($p) $b)

/-- Run each registered `norm_num` extension on a typed expression `p : Prop`,
and returning the truth or falsity of `p' : Prop` from an equivalence `p ↔ p'`. -/
def deriveBool (p : Q(Prop)) : MetaM ((b : Bool) × BoolResult p b) := do
  let .isBool b prf ← derive (α := (q(Prop) : Q(Type))) p | failure
  pure ⟨b, prf⟩

/-- Obtain a `Result` from a `BoolResult`. -/
def Result.ofBoolResult {p : Q(Prop)} {b : Bool} (prf : BoolResult p b) :
  Result q(Prop) :=
  Result'.isBool b prf

/-- Run each registered `norm_num` extension on a typed expression `p : Prop`,
and returning the truth or falsity of `p' : Prop` from an equivalence `p ↔ p'`. -/
def deriveBoolOfIff (p p' : Q(Prop)) (hp : Q($p ↔ $p')) :
    MetaM ((b : Bool) × BoolResult p' b) := do
  let ⟨b, pb⟩ ← deriveBool p
  match b with
  | true  => return ⟨true, q(Iff.mp $hp $pb)⟩
  | false => return ⟨false, q((Iff.not $hp).mp $pb)⟩

/-- Produce a proof that `n` is not prime from a factor `1 < d < n`. -/
def deriveNotPrime (n d : ℕ) : MetaM <| Q(¬ Nat.Prime $n) := do
  let d' : ℕ := n / d
  let prf : Q($d * $d' = $n) := (q(Eq.refl $n) : Expr)
  let r : Q(Nat.ble $d 1 = false) := (q(Eq.refl false) : Expr)
  let r' : Q(Nat.ble $d' 1 = false) := (q(Eq.refl false) : Expr)
  return q(Nat.not_prime_mul' $prf (isNat_lt_true (.raw_refl _) (.raw_refl _) $r)
    (isNat_lt_true (.raw_refl _) (.raw_refl _) $r'))

/-- The `norm_num` extension which identifies expressions of the form `minFac n`. -/
@[norm_num Nat.minFac _] partial def evalMinFac :
  NormNumExt where eval {u α} e := do
  let .app (.const `Nat.minFac _) (n : Q(ℕ)) ← whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨nn, pn⟩ ← deriveNat n sℕ
  let n' := nn.natLit!
  let rec aux (k : ℕ) (prf : Q(MinFacHelper $nn $k)) :
    MetaM <| (c : Q(ℕ)) × Q(IsNat (Nat.minFac $n) $c) := do
    -- remark: `deriveBool q($nn < $k * $k)` is 2x slower than the following test.
    if n' < k * k then
      let r : Q(Nat.ble ($k * $k) $nn = false) := (q(Eq.refl false) : Expr)
      return ⟨nn, q(isNat_minFac_4 $pn $prf (isNat_lt_true (.raw_refl _) (.raw_refl _) $r))⟩
    -- the following branch is not necessary for the correctness, but makes the algorithm 2x faster
    let d : ℕ := k.minFac
    if d < k then
      let k' : ℕ := k + 2
      let pk' : Q($k + 2 = $k') := (q(Eq.refl $k') : Expr)
      let pd ← deriveNotPrime k d
      have prf' : Q(MinFacHelper $nn $k') := q(minFacHelper_2 $pk' $pd $prf)
      return ← aux (k + 2) prf'
    -- remark: `deriveBool q($nn % $k = 0)` is 5x slower than the following test
    if n' % k = 0 then
      let r : Q($nn % $k = 0) := (q(Eq.refl 0) : Expr)
      let r' : Q(IsNat (minFac $n) $k) := q(isNat_minFac_3 $pn (.raw_refl _) $prf $r)
      -- note: `q($k)` produces a `NatCast` expression, but we want a natural number literal here.
      return ⟨mkRawNatLit k, r'⟩
    let some (i : Q(@CharZero ℕ $sℕ)) ← inferCharZeroOfAddMonoidWithOne? | failure
    let r : Q(Nat.beq ($nn % $k) 0 = false) := (q(Eq.refl false) : Expr)
    let pq : Q(¬ $nn % $k = 0) :=
    -- for some reason giving `instAddMonoidWithOneNat` explicitly is necessary.
      q(@isNat_eq_false _ instAddMonoidWithOneNat $i _ _ _ _ (.raw_refl _) (.raw_refl _) $r)
    let k' : ℕ := k + 2
    let pk' : Q($k + 2 = $k') := (q(Eq.refl $k') : Expr)
    have prf' : Q(MinFacHelper $nn $k') := q(minFacHelper_3 $pk' $pq $prf)
    aux (k + 2) prf'
  let rec core : MetaM (Result (q(Nat.minFac $n) : Q(ℕ))) := do
    let ⟨bp, pp⟩ ← deriveBool q($nn = 1)
    match bp with
    | true  => return .isNat sℕ q(1) (q(isNat_minFac_1 $pn $pp) : Q(IsNat (minFac $n) 1))
    | false =>
    let ⟨bq, pq⟩ ← deriveBool q($nn % 2 = 0)
    match bq with
    | true  => return .isNat sℕ q(2) (q(isNat_minFac_2 $pn $pq) : Q(IsNat (minFac $n) 2))
    | false =>
    let ⟨c, pc⟩ ← aux 3 q(minFacHelper_0 $nn $pp $pq)
    return .isNat sℕ c pc
  core

/-- The `norm_num` extension which identifies expressions of the form `Nat.Prime n`. -/
@[norm_num Nat.Prime _] def evalNatPrime : NormNumExt where eval {u α} e := do
  let .app (.const `Nat.Prime _) (n : Q(ℕ)) ← whnfR e | failure
  let sℕ : Q(AddMonoidWithOne ℕ) := q(instAddMonoidWithOneNat)
  let ⟨nn, pn⟩ ← deriveNat n sℕ
  let n' := nn.natLit!
  -- note: if `n` is not prime, we don't have to verify the calculation of `n.minFac`, we just have
  -- to compute it, which is a lot quicker
  let rec core : MetaM (Result q(Nat.Prime $n)) := do
    if n' < 2 then
      let r : Q(Nat.ble 2 $nn = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(not_prime_of_lt_two (isNat_lt_true $pn (.raw_refl _) $r))
    let d := n'.minFac
    if d < n' then
      let prf : Q(¬ Nat.Prime $nn) ← deriveNotPrime n' d
      return .isFalse q(isNat.natElim $pn $prf)
    let r : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
    let ⟨true, p2n⟩ ← deriveBool q(Nat.minFac $n = $n) | failure
    return .isTrue q(Nat.prime_def_minFac.mpr ⟨isNat_le_true (.raw_refl _) $pn $r, $p2n⟩)
  core

/-- The `norm_num` extension which identifies expressions of the form `a ∧ b`,
such that `norm_num` successfully recognises `a` and `b`. -/
@[norm_num _ ∧ _] def evalAnd : NormNumExt where eval {u α} e := do
  let .app (.app (.const ``And _) (p : Q($α))) (q : Q($α)) ← whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq α q(Prop)
  have p : Q(Prop) := p; have q : Q(Prop) := q
  let ⟨bp, pp⟩ ← deriveBool p
  match bp with
  | false => return .isFalse (q(not_and_of_not_left $q $pp) : Q(¬($p ∧ $q)))
  | true =>
    let ⟨bq, pq⟩ ← deriveBool q
    match bq with
    | false => return .isFalse (q(not_and_of_not_right $p $pq) : Q(¬($p ∧ $q)))
    | true  => return .isTrue (q(⟨$pp, $pq⟩) : Q($p ∧ $q))

/-- The `norm_num` extension which identifies expressions of the form `a ∨ b`,
such that `norm_num` successfully recognises `a` and `b`. -/
@[norm_num _ ∨ _] def evalOr : NormNumExt where eval {u α} e := do
  let .app (.app (.const ``Or _) (p : Q($α))) (q : Q($α)) ← whnfR e | failure
  guard <| ← withNewMCtxDepth <| isDefEq α q(Prop)
  have p : Q(Prop) := p; have q : Q(Prop) := q
  let ⟨bp, pp⟩ ← deriveBool p
  match bp with
  | true  => return .isTrue (q(Or.inl $pp) : Q($p ∨ $q))
  | false =>
    let ⟨bq, pq⟩ ← deriveBool q
    match bq with
    | true  => return .isTrue (q(Or.inr $pq) : Q($p ∨ $q))
    | false => return .isFalse (q(not_or_of_not $pp $pq) : Q(¬($p ∨ $q)))

end Mathlib.Meta.NormNum
