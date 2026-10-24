/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Xavier Roblot
-/
module

public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Data.Nat.Squarefree

/-!
# `norm_num` extension for `Squarefree`

This file provides a `norm_num` extension to decide whether a natural number or an integer
is squarefree.

If `n` is not squarefree, the proof is given by a witness `a > 1` with `a * a ∣ n`. If `n` is
squarefree, the proof is a trial division of `n` by the odd numbers `k = 3, 5, 7, …`, keeping the
invariant that every prime divisor of the current cofactor is at least `k`.

This is adapted from the Mathlib 3 `norm_num` extension for `squarefree`, written by Mario Carneiro.

## Implementation Notes

The proof that `n` is squarefree has depth about `√n / 2`. As for the primality proofs of
`Mathlib.Tactic.NormNum.Prime`, type-checking it for large `n` requires increasing `maxRecDepth`.
-/

public meta section

open Nat Qq Lean Meta

namespace Mathlib.Meta.NormNum

/-- A predicate representing partial progress in a proof of `Squarefree n`: if `n` and `k` are odd,
`k ≥ 3` and every prime divisor of `n` is at least `k`, then `n` is squarefree. The parity and size
conditions are part of the predicate so that they are only checked once, at the start of the trial
division. -/
def SquarefreeHelper (n k : ℕ) : Prop :=
  n % 2 = 1 → k % 2 = 1 → 3 ≤ k → (∀ p, p.Prime → p ∣ n → k ≤ p) → Squarefree n

theorem not_squarefree_mul (a b n : ℕ) (h : a * a * b = n) (h₁ : ble a 1 = false) :
    ¬ Squarefree n :=
  fun H ↦ (ble_eq_false.mp h₁).ne' (Nat.isUnit_iff.mp <| H a ⟨b, h.symm⟩)

/-- If `n` is odd, its prime divisors are at least `3`, so `SquarefreeHelper n 3` implies that
`n` is squarefree. This starts the trial division at `k = 3`. -/
theorem squarefree_of_odd (n : ℕ) (hn : n % 2 = 1) (h : SquarefreeHelper n 3) :
    Squarefree n :=
  h hn rfl le_rfl fun p hp hpn ↦ by obtain ⟨rfl | _⟩ := LE.le.eq_or_lt (hp.two_le) <;> lia

/-- Start of the trial division for an even `n = 2 * m` with `m` odd. -/
theorem squarefree_two_mul (n m : ℕ) (e : 2 * m = n) (hm : m % 2 = 1) (h : SquarefreeHelper m 3) :
    Squarefree n :=
  e ▸ squarefree_mul_iff.mpr ⟨coprime_two_left.mpr (odd_iff.mpr hm), prime_two.squarefree,
    squarefree_of_odd m hm h⟩

/-- If `k` does not divide `n`, a prime divisor of `n` which is at least `k` is at least `k + 2`
(both being odd), so `SquarefreeHelper n (k + 2)` implies `SquarefreeHelper n k`. This is the step
of the trial division when `k` does not divide `n`. -/
theorem squarefreeHelper_1 (n k k' : ℕ) (e : k' = k + 2) (hnk : (n % k).beq 0 = false)
    (h : SquarefreeHelper n k') : SquarefreeHelper n k :=
  fun hn hk _ H ↦ h hn (by lia) (by lia) fun p hp hpn ↦ by
    have : k ≤ p := H p hp hpn
    have : p ≠ k := fun h ↦ ne_of_beq_eq_false hnk (dvd_iff_mod_eq_zero.mp (h ▸ hpn))
    have : p % 2 = 1 := by
      obtain ⟨rfl | h2⟩ := hp.eq_two_or_odd <;> lia
    lia

/-- Step of the trial division when `k` divides `n`: `n = k * m` with `k` not dividing `m`. -/
theorem squarefreeHelper_2 (n m k k' : ℕ) (e : k' = k + 2) (hm : k * m = n)
    (hmk : (m % k).beq 0 = false) (h : SquarefreeHelper m k') : SquarefreeHelper n k :=
    fun hn hk hk₃ H ↦ by
  have hkp : k.Prime :=
    prime_def_minFac.mpr ⟨by lia, le_antisymm (minFac_le (by lia))
      (H _ (minFac_prime (by lia)) ((minFac_dvd k).trans ⟨m, hm.symm⟩))⟩
  refine hm ▸ squarefree_mul_iff.mpr ⟨hkp.coprime_iff_not_dvd.mpr fun h ↦ ?_,
    hkp.squarefree, squarefreeHelper_1 m k k' e hmk h ?_ hk hk₃
      fun p hp hpm ↦ H p hp (hpm.trans ⟨k, by rw [← hm, mul_comm]⟩)⟩
  · exact ne_of_beq_eq_false hmk <| mod_eq_zero_of_dvd h
  · exact odd_iff.mp (odd_mul.mp (odd_iff.mpr (hm ▸ hn))).2

/-- End of the trial division: if `n < k * k`, a prime `p ≥ k` cannot have `p * p ∣ n`. -/
theorem squarefreeHelper_3 (n k : ℕ) (h : ble (k * k) n = false) :
    SquarefreeHelper n k := fun hn _ _ H ↦ squarefree_iff_prime_squarefree.mpr fun p hp hpp ↦ by
  have : k * k ≤ p * p := by
    gcongr <;>
    exact H p hp ((Dvd.intro _ rfl).trans hpp)
  have : p * p ≤ n := le_of_dvd (by lia) hpp
  have : n < k * k := ble_eq_false.mp h
  lia

theorem isNat_squarefree {n n' : ℕ} (h : IsNat n n') : Squarefree n' → Squarefree n :=
  isNat.natElim h

theorem isNat_not_squarefree {n n' : ℕ} (h : IsNat n n') : ¬ Squarefree n' → ¬ Squarefree n :=
  isNat.natElim h

theorem isInt_squarefree {n n' : ℤ} {m : ℕ} (h : IsInt n n') (hm : n'.natAbs = m) :
    Squarefree m → Squarefree n := by
  obtain ⟨rfl⟩ := h
  exact hm ▸ Int.squarefree_natAbs.mp

theorem isInt_not_squarefree {n n' : ℤ} {m : ℕ} (h : IsInt n n') (hm : n'.natAbs = m) :
    ¬ Squarefree m → ¬ Squarefree n := by
  obtain ⟨rfl⟩ := h
  exact hm ▸ mt Int.squarefree_natAbs.mpr

/-- Given an odd numeral `en` with value `n` and an odd numeral `ek` with value `k ≥ 3`, such that
`n` is squarefree, produce a proof of `SquarefreeHelper n k`. -/
partial def proveSquarefreeHelper (en : Q(ℕ)) (n : ℕ) (ek : Q(ℕ)) (k : ℕ) :
    Q(SquarefreeHelper $en $ek) :=
  if n < k * k then
    have h : Q(Nat.ble ($ek * $ek) $en = false) := (q(Eq.refl false) : Expr)
    q(squarefreeHelper_3 $en $ek $h)
  else
    have ek' : Q(ℕ) := mkRawNatLit (k + 2)
    have e : Q($ek' = $ek + 2) := (q(Eq.refl $ek') : Expr)
    if n % k = 0 then
      have em : Q(ℕ) := mkRawNatLit (n / k)
      have hm : Q($ek * $em = $en) := (q(Eq.refl $en) : Expr)
      have hmk : Q(Nat.beq ($em % $ek) 0 = false) := (q(Eq.refl false) : Expr)
      let h := proveSquarefreeHelper em (n / k) ek' (k + 2)
      q(squarefreeHelper_2 $en $em $ek $ek' $e $hm $hmk $h)
    else
      have hnk : Q(Nat.beq ($en % $ek) 0 = false) := (q(Eq.refl false) : Expr)
      let h := proveSquarefreeHelper en n ek' (k + 2)
      q(squarefreeHelper_1 $en $ek $ek' $e $hnk $h)

/-- Given a numeral `en` with value `n ≥ 1` such that `n` is squarefree, produce a proof of
`Squarefree n`. -/
def proveSquarefree (en : Q(ℕ)) (n : ℕ) : Q(Squarefree $en) :=
  if n % 2 = 1 then
    have hn : Q($en % 2 = 1) := (q(Eq.refl 1) : Expr)
    let h := proveSquarefreeHelper en n q(nat_lit 3) 3
    q(squarefree_of_odd $en $hn $h)
  else
    have em : Q(ℕ) := mkRawNatLit (n / 2)
    have e : Q(2 * $em = $en) := (q(Eq.refl $en) : Expr)
    have hm : Q($em % 2 = 1) := (q(Eq.refl 1) : Expr)
    let h := proveSquarefreeHelper em (n / 2) q(nat_lit 3) 3
    q(squarefree_two_mul $en $em $e $hm $h)

/-- Given a numeral `en`, decide whether it is squarefree. -/
def evalSquarefreeLit (en : Q(ℕ)) : Result q(Squarefree $en) :=
  let n := en.natLit!
  match n.minSqFac with
  | some d =>
    have ed : Q(ℕ) := mkRawNatLit d
    have eb : Q(ℕ) := mkRawNatLit (n / (d * d))
    have h : Q($ed * $ed * $eb = $en) := (q(Eq.refl $en) : Expr)
    have h₁ : Q(Nat.ble $ed 1 = false) := (q(Eq.refl false) : Expr)
    .isFalse q(not_squarefree_mul $ed $eb $en $h $h₁)
  | none =>
    if n = 0 then
      have : $en =Q 0 := ⟨⟩
      .isFalse q(not_squarefree_zero)
    else .isTrue (proveSquarefree en n)

/-- The `norm_num` extension which identifies expressions of the form `Squarefree (n : ℕ)`. -/
@[norm_num @Squarefree ℕ _ _]
def evalNatSquarefree : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Squarefree ℕ $inst $a) => do
    let ⟨nn, pa⟩ ← deriveNat (u := 0) (α := q(ℕ)) a q(inferInstance)
    assertInstancesCommute
    match evalSquarefreeLit nn with
    | .isTrue p => return .isTrue q(isNat_squarefree $pa $p)
    | .isFalse p => return .isFalse q(isNat_not_squarefree $pa $p)
    | _ => failure
  | _ => failure

/-- The `norm_num` extension which identifies expressions of the form `Squarefree (n : ℤ)`. -/
@[norm_num @Squarefree ℤ _ _]
def evalIntSquarefree : NormNumExt where eval {u αP} e := do
  match u, αP, e with
  | 0, ~q(Prop), ~q(@Squarefree ℤ $inst $a) => do
    let ⟨na, pa⟩ ← deriveInt (u := 0) (α := q(ℤ)) a q(inferInstance)
    let ⟨nn, pn⟩ := rawIntLitNatAbs na
    assertInstancesCommute
    match evalSquarefreeLit nn with
    | .isTrue p => return .isTrue q(isInt_squarefree $pa $pn $p)
    | .isFalse p => return .isFalse q(isInt_not_squarefree $pa $pn $p)
    | _ => failure
  | _ => failure

end Mathlib.Meta.NormNum
