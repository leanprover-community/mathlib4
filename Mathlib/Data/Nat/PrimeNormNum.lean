/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module data.nat.prime_norm_num
! leanprover-community/mathlib commit 10b4e499f43088dd3bb7b5796184ad5216648ab1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Factors
import Mathbin.Data.Nat.Prime
import Mathbin.Tactic.NormNum

/-!
# Primality prover

This file provides a `norm_num` extention to prove that natural numbers are prime.

-/


namespace Tactic

namespace NormNum

theorem is_prime_helper (n : ℕ) (h₁ : 1 < n) (h₂ : Nat.minFac n = n) : Nat.Prime n :=
  Nat.prime_def_minFac.2 ⟨h₁, h₂⟩
#align tactic.norm_num.is_prime_helper Tactic.NormNum.is_prime_helper

theorem minFac_bit0 (n : ℕ) : Nat.minFac (bit0 n) = 2 := by
  simp [Nat.minFac_eq, show 2 ∣ bit0 n by simp [bit0_eq_two_mul n]]
#align tactic.norm_num.min_fac_bit0 Tactic.NormNum.minFac_bit0

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def MinFacHelper (n k : ℕ) : Prop :=
  0 < k ∧ bit1 k ≤ Nat.minFac (bit1 n)
#align tactic.norm_num.min_fac_helper Tactic.NormNum.MinFacHelper

theorem MinFacHelper.n_pos {n k : ℕ} (h : MinFacHelper n k) : 0 < n :=
  pos_iff_ne_zero.2 fun e => by rw [e] at h <;> exact not_le_of_lt (Nat.bit1_lt h.1) h.2
#align tactic.norm_num.min_fac_helper.n_pos Tactic.NormNum.MinFacHelper.n_pos

theorem minFac_ne_bit0 {n k : ℕ} : Nat.minFac (bit1 n) ≠ bit0 k :=
  by
  rw [bit0_eq_two_mul]
  refine' fun e => absurd ((Nat.dvd_add_iff_right _).2 (dvd_trans ⟨_, e⟩ (Nat.minFac_dvd _))) _ <;>
    simp
#align tactic.norm_num.min_fac_ne_bit0 Tactic.NormNum.minFac_ne_bit0

theorem minFacHelper_0 (n : ℕ) (h : 0 < n) : MinFacHelper n 1 :=
  by
  refine' ⟨zero_lt_one, lt_of_le_of_ne _ min_fac_ne_bit0.symm⟩
  rw [Nat.succ_le_iff]
  refine' lt_of_le_of_ne (Nat.minFac_pos _) fun e => Nat.not_prime_one _
  rw [e]
  exact Nat.minFac_prime (Nat.bit1_lt h).ne'
#align tactic.norm_num.min_fac_helper_0 Tactic.NormNum.minFacHelper_0

theorem minFacHelper_1 {n k k' : ℕ} (e : k + 1 = k') (np : Nat.minFac (bit1 n) ≠ bit1 k)
    (h : MinFacHelper n k) : MinFacHelper n k' :=
  by
  rw [← e]
  refine'
    ⟨Nat.succ_pos _,
      (lt_of_le_of_ne (lt_of_le_of_ne _ _ : k + 1 + k < _) min_fac_ne_bit0.symm : bit0 (k + 1) < _)⟩
  · rw [add_right_comm]
    exact h.2
  · rw [add_right_comm]
    exact np.symm
#align tactic.norm_num.min_fac_helper_1 Tactic.NormNum.minFacHelper_1

theorem minFacHelper_2 (n k k' : ℕ) (e : k + 1 = k') (np : ¬Nat.Prime (bit1 k))
    (h : MinFacHelper n k) : MinFacHelper n k' :=
  by
  refine' min_fac_helper_1 e _ h
  intro e₁; rw [← e₁] at np
  exact np (Nat.minFac_prime <| ne_of_gt <| Nat.bit1_lt h.n_pos)
#align tactic.norm_num.min_fac_helper_2 Tactic.NormNum.minFacHelper_2

theorem minFacHelper_3 (n k k' c : ℕ) (e : k + 1 = k') (nc : bit1 n % bit1 k = c) (c0 : 0 < c)
    (h : MinFacHelper n k) : MinFacHelper n k' :=
  by
  refine' min_fac_helper_1 e _ h
  refine' mt _ (ne_of_gt c0); intro e₁
  rw [← nc, ← Nat.dvd_iff_mod_eq_zero, ← e₁]
  apply Nat.minFac_dvd
#align tactic.norm_num.min_fac_helper_3 Tactic.NormNum.minFacHelper_3

theorem minFacHelper_4 (n k : ℕ) (hd : bit1 n % bit1 k = 0) (h : MinFacHelper n k) :
    Nat.minFac (bit1 n) = bit1 k :=
  by
  rw [← Nat.dvd_iff_mod_eq_zero] at hd
  exact le_antisymm (Nat.minFac_le_of_dvd (Nat.bit1_lt h.1) hd) h.2
#align tactic.norm_num.min_fac_helper_4 Tactic.NormNum.minFacHelper_4

theorem minFacHelper_5 (n k k' : ℕ) (e : bit1 k * bit1 k = k') (hd : bit1 n < k')
    (h : MinFacHelper n k) : Nat.minFac (bit1 n) = bit1 n :=
  by
  refine' (Nat.prime_def_minFac.1 (Nat.prime_def_le_sqrt.2 ⟨Nat.bit1_lt h.n_pos, _⟩)).2
  rw [← e] at hd
  intro m m2 hm md
  have := le_trans h.2 (le_trans (Nat.minFac_le_of_dvd m2 md) hm)
  rw [Nat.le_sqrt] at this
  exact not_le_of_lt hd this
#align tactic.norm_num.min_fac_helper_5 Tactic.NormNum.minFacHelper_5

open _Root_.NormNum

/-- Given `e` a natural numeral and `d : nat` a factor of it, return `⊢ ¬ prime e`. -/
unsafe def prove_non_prime (e : expr) (n d₁ : ℕ) : tactic expr := do
  let e₁ := reflect d₁
  let c ← mk_instance_cache q(Nat)
  let (c, p₁) ← prove_lt_nat c q(1) e₁
  let d₂ := n / d₁
  let e₂ := reflect d₂
  let (c, e', p) ← prove_mul_nat c e₁ e₂
  guard (e' == e)
  let (c, p₂) ← prove_lt_nat c q(1) e₂
  return <| q(@Nat.not_prime_mul').mk_app [e₁, e₂, e, p, p₁, p₂]
#align tactic.norm_num.prove_non_prime tactic.norm_num.prove_non_prime

/-- Given `a`,`a1 := bit1 a`, `n1` the value of `a1`, `b` and `p : min_fac_helper a b`,
  returns `(c, ⊢ min_fac a1 = c)`. -/
unsafe def prove_min_fac_aux (a a1 : expr) (n1 : ℕ) :
    instance_cache → expr → expr → tactic (instance_cache × expr × expr)
  | ic, b, p => do
    let k ← b.toNat
    let k1 := bit1 k
    let b1 := q((bit1 : ℕ → ℕ)).mk_app [b]
    if n1 < k1 * k1 then do
        let (ic, e', p₁) ← prove_mul_nat ic b1 b1
        let (ic, p₂) ← prove_lt_nat ic a1 e'
        return (ic, a1, q(minFacHelper_5).mk_app [a, b, e', p₁, p₂, p])
      else
        let d := k1
        if to_bool (d < k1) then do
          let k' := k + 1
          let e' := reflect k'
          let (ic, p₁) ← prove_succ ic b e'
          let p₂ ← prove_non_prime b1 k1 d
          prove_min_fac_aux ic e' <| q(minFacHelper_2).mk_app [a, b, e', p₁, p₂, p]
        else do
          let nc := n1 % k1
          let (ic, c, pc) ← prove_div_mod ic a1 b1 tt
          if nc = 0 then return (ic, b1, q(minFacHelper_4).mk_app [a, b, pc, p])
            else do
              let (ic, p₀) ← prove_pos ic c
              let k' := k + 1
              let e' := reflect k'
              let (ic, p₁) ← prove_succ ic b e'
              prove_min_fac_aux ic e' <| q(minFacHelper_3).mk_app [a, b, e', c, p₁, pc, p₀, p]
#align tactic.norm_num.prove_min_fac_aux tactic.norm_num.prove_min_fac_aux

/-- Given `a` a natural numeral, returns `(b, ⊢ min_fac a = b)`. -/
unsafe def prove_min_fac (ic : instance_cache) (e : expr) : tactic (instance_cache × expr × expr) :=
  match match_numeral e with
  | match_numeral_result.zero => return (ic, q((2 : ℕ)), q(Nat.minFac_zero))
  | match_numeral_result.one => return (ic, q((1 : ℕ)), q(Nat.minFac_one))
  | match_numeral_result.bit0 e => return (ic, q(2), q(minFac_bit0).mk_app [e])
  | match_numeral_result.bit1 e => do
    let n ← e.toNat
    let c ← mk_instance_cache q(Nat)
    let (c, p) ← prove_pos c e
    let a1 := q((bit1 : ℕ → ℕ)).mk_app [e]
    prove_min_fac_aux e a1 (bit1 n) c q(1) (q(minFacHelper_0).mk_app [e, p])
  | _ => failed
#align tactic.norm_num.prove_min_fac tactic.norm_num.prove_min_fac

/-- A partial proof of `factors`. Asserts that `l` is a sorted list of primes, lower bounded by a
prime `p`, which multiplies to `n`. -/
def FactorsHelper (n p : ℕ) (l : List ℕ) : Prop :=
  p.Prime → List.Chain (· ≤ ·) p l ∧ (∀ a ∈ l, Nat.Prime a) ∧ List.prod l = n
#align tactic.norm_num.factors_helper Tactic.NormNum.FactorsHelper

theorem factorsHelper_nil (a : ℕ) : FactorsHelper 1 a [] := fun pa =>
  ⟨List.Chain.nil, by rintro _ ⟨⟩, List.prod_nil⟩
#align tactic.norm_num.factors_helper_nil Tactic.NormNum.factorsHelper_nil

theorem factorsHelper_cons' (n m a b : ℕ) (l : List ℕ) (h₁ : b * m = n) (h₂ : a ≤ b)
    (h₃ : Nat.minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) := fun pa =>
  have pb : b.Prime := Nat.prime_def_minFac.2 ⟨le_trans pa.two_le h₂, h₃⟩
  let ⟨f₁, f₂, f₃⟩ := H pb
  ⟨List.Chain.cons h₂ f₁, fun c h => h.elim (fun e => e.symm ▸ pb) (f₂ _), by
    rw [List.prod_cons, f₃, h₁]⟩
#align tactic.norm_num.factors_helper_cons' Tactic.NormNum.factorsHelper_cons'

theorem factorsHelper_cons (n m a b : ℕ) (l : List ℕ) (h₁ : b * m = n) (h₂ : a < b)
    (h₃ : Nat.minFac b = b) (H : FactorsHelper m b l) : FactorsHelper n a (b :: l) :=
  factorsHelper_cons' _ _ _ _ _ h₁ h₂.le h₃ H
#align tactic.norm_num.factors_helper_cons Tactic.NormNum.factorsHelper_cons

theorem factorsHelper_sn (n a : ℕ) (h₁ : a < n) (h₂ : Nat.minFac n = n) : FactorsHelper n a [n] :=
  factorsHelper_cons _ _ _ _ _ (mul_one _) h₁ h₂ (factorsHelper_nil _)
#align tactic.norm_num.factors_helper_sn Tactic.NormNum.factorsHelper_sn

theorem factorsHelper_same (n m a : ℕ) (l : List ℕ) (h : a * m = n) (H : FactorsHelper m a l) :
    FactorsHelper n a (a :: l) := fun pa =>
  factorsHelper_cons' _ _ _ _ _ h le_rfl (Nat.prime_def_minFac.1 pa).2 H pa
#align tactic.norm_num.factors_helper_same Tactic.NormNum.factorsHelper_same

theorem factorsHelper_same_sn (a : ℕ) : FactorsHelper a a [a] :=
  factorsHelper_same _ _ _ _ (mul_one _) (factorsHelper_nil _)
#align tactic.norm_num.factors_helper_same_sn Tactic.NormNum.factorsHelper_same_sn

theorem factorsHelper_end (n : ℕ) (l : List ℕ) (H : FactorsHelper n 2 l) : Nat.factors n = l :=
  let ⟨h₁, h₂, h₃⟩ := H Nat.prime_two
  have := List.chain'_iff_pairwise.1 (@List.Chain'.tail _ _ (_ :: _) h₁)
  (List.eq_of_perm_of_sorted (Nat.factors_unique h₃ h₂) this (Nat.factors_sorted _)).symm
#align tactic.norm_num.factors_helper_end Tactic.NormNum.factorsHelper_end

-- failed to format: unknown constant 'term.pseudo.antiquot'
/-- Given `n` and `a` natural numerals, returns `(l, ⊢ factors_helper n a l)`. -/ unsafe
  def
    prove_factors_aux
    : instance_cache → expr → expr → ℕ → ℕ → tactic ( instance_cache × expr × expr )
    |
      c , en , ea , n , a
      =>
      let
        b := n . minFac
        if
          b < n
          then
          do
            let m := n / b
              let ( c , em ) ← c . ofNat m
              if
                b = a
                then
                do
                  let ( c , _ , p₁ ) ← prove_mul_nat c ea em
                    let ( c , l , p₂ ) ← prove_factors_aux c em ea m a
                    pure
                      (
                        c
                          ,
                          q( ( $ ( ea ) :: $ ( l ) : List ℕ ) )
                            ,
                            q( factorsHelper_same ) . mk_app [ en , em , ea , l , p₁ , p₂ ]
                        )
                else
                do
                  let ( c , eb ) ← c b
                    let ( c , _ , p₁ ) ← prove_mul_nat c eb em
                    let ( c , p₂ ) ← prove_lt_nat c ea eb
                    let ( c , _ , p₃ ) ← prove_min_fac c eb
                    let ( c , l , p₄ ) ← prove_factors_aux c em eb m b
                    pure
                      (
                        c
                          ,
                          q( ( $ ( eb ) :: $ ( l ) : List ℕ ) )
                            ,
                            q( factorsHelper_cons ) . mk_app
                              [ en , em , ea , eb , l , p₁ , p₂ , p₃ , p₄ ]
                        )
          else
          if
            b = a
            then
            pure ( c , q( ( [ $ ( ea ) ] : List ℕ ) ) , q( factorsHelper_same_sn ) . mk_app [ ea ] )
            else
            do
              let ( c , p₁ ) ← prove_lt_nat c ea en
                let ( c , _ , p₂ ) ← prove_min_fac c en
                pure
                  (
                    c
                      ,
                      q( ( [ $ ( en ) ] : List ℕ ) )
                        ,
                        q( factorsHelper_sn ) . mk_app [ en , ea , p₁ , p₂ ]
                    )
#align tactic.norm_num.prove_factors_aux tactic.norm_num.prove_factors_aux

/-- Evaluates the `prime` and `min_fac` functions. -/
@[norm_num]
unsafe def eval_prime : expr → tactic (expr × expr)
  | q(Nat.Prime $(e)) => do
    let n ← e.toNat
    match n with
      | 0 => false_intro q(Nat.not_prime_zero)
      | 1 => false_intro q(Nat.not_prime_one)
      | _ =>
        let d₁ := n
        if d₁ < n then prove_non_prime e n d₁ >>= false_intro
        else do
          let e₁ := reflect d₁
          let c ← mk_instance_cache q(ℕ)
          let (c, p₁) ← prove_lt_nat c q(1) e₁
          let (c, e₁, p) ← prove_min_fac c e
          true_intro <| q(is_prime_helper).mk_app [e, p₁, p]
  | q(Nat.minFac $(e)) => do
    let ic ← mk_instance_cache q(ℕ)
    Prod.snd <$> prove_min_fac ic e
  | q(Nat.factors $(e)) => do
    let n ← e.toNat
    match n with
      | 0 => pure (q(@List.nil ℕ), q(Nat.factors_zero))
      | 1 => pure (q(@List.nil ℕ), q(Nat.factors_one))
      | _ => do
        let c ← mk_instance_cache q(ℕ)
        let (c, l, p) ← prove_factors_aux c e q(2) n 2
        pure (l, q(factorsHelper_end).mk_app [e, l, p])
  | _ => failed
#align tactic.norm_num.eval_prime tactic.norm_num.eval_prime

end NormNum

end Tactic

