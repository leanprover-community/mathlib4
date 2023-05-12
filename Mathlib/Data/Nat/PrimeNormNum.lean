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

/-!
# Primality prover

This file provides a `norm_num` extention to prove that natural numbers are prime.

-/

open Nat Qq Lean Meta

namespace Mathlib.Meta.NormNum

/-- A predicate representing partial progress in a proof of `min_fac`. -/
def MinFacHelper (n k : ℕ) : Prop :=
  2 < k ∧ k % 2 = 1 ∧ k ≤ minFac n

theorem MinFacHelper.one_lt {n k : ℕ} (h : MinFacHelper n k) : 1 < n :=
  sorry --pos_iff_ne_zero.2 fun e => by rw [e] at h <;> exact not_le_of_lt (Nat.bit1_lt h.1) h.2

-- theorem minFac_ne_bit0 {n k : ℕ} : minFac (bit1 n) ≠ bit0 k := by
--   rw [bit0_eq_two_mul]
--   refine' fun e => absurd ((Nat.dvd_add_iff_right _).2 (dvd_trans ⟨_, e⟩ (minFac_dvd _))) _ <;>
--     simp

theorem minFacHelper_0 (n : ℕ) (h1 : ¬ n = 1) (h2 : ¬ n % 2 = 0) : MinFacHelper n 3 := by
  sorry
  -- refine' ⟨zero_lt_one, lt_of_le_of_ne _ minFac_ne_bit0.symm⟩
  -- rw [Nat.succ_le_iff]
  -- refine' lt_of_le_of_ne (minFac_pos _) fun e => Nat.not_prime_one _
  -- rw [e]
  -- exact minFac_prime (Nat.bit1_lt h).ne'

theorem minFacHelper_1 {n k k' : ℕ} (e : k + 2 = k') (np : minFac n ≠ k)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  sorry
  -- rw [← e]
  -- refine'
  --   ⟨Nat.succ_pos _,
  --     (lt_of_le_of_ne (lt_of_le_of_ne _ _ : k + 1 + k < _) min_fac_ne_bit0.symm : bit0 (k + 1) < _)⟩
  -- · rw [add_right_comm]
  --   exact h.2
  -- · rw [add_right_comm]
  --   exact np.symm

theorem minFacHelper_2 {n k k' : ℕ} (e : k + 2 = k') (nk : ¬ Nat.Prime k)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  sorry
  -- refine' minFacHelper_1 e _ h
  -- intro e₁
  -- rw [← e₁] at np
  -- exact np (minFac_prime <| ne_of_gt <| Nat.bit1_lt h.n_pos)

theorem minFacHelper_3 {n k k' : ℕ} (e : k + 2 = k') (nc : ¬ n % k = 0)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  sorry
  -- refine' minFacHelper_1 e _ h
  -- refine' mt _ (ne_of_gt c0); intro e₁
  -- rw [← nc, ← Nat.dvd_iff_mod_eq_zero, ← e₁]
  -- apply minFac_dvd

  -- refine' (Nat.prime_def_minFac.1 (Nat.prime_def_le_sqrt.2 ⟨Nat.bit1_lt h.n_pos, _⟩)).2
  -- rw [← e] at hd
  -- intro m m2 hm md
  -- have := le_trans h.2 (le_trans (minFac_le_of_dvd m2 md) hm)
  -- rw [Nat.le_sqrt] at this
  -- exact not_le_of_lt hd this

theorem prime_helper (n : ℕ) : 1 < n ∧ minFac n = n ↔ Nat.Prime n :=
  Nat.prime_def_minFac.symm

-- theorem prime_helper_1 (n : ℕ) (h₁ : 1 < n) (h₂ : minFac n = n) : Nat.Prime n :=
--   Nat.prime_def_minFac.2 ⟨succ_le_of_lt h₁, h₂⟩

-- theorem prime_helper_2 (n : ℕ) : (h : ¬ 1 < n) → ¬ Nat.Prime n :=
--   mt fun h => (prime_def_minFac.mp h).1

-- theorem prime_helper_3 (n : ℕ) : ¬ minFac n = n → ¬ Nat.Prime n :=
--   mt fun h => (prime_def_minFac.mp h).2

open NormNum

-- /-- Given `e` a natural numeral and `d : nat` a factor of it, return `⊢ ¬ prime e`. -/
-- unsafe def prove_non_prime (e : expr) (n d₁ : ℕ) : tactic expr := do
--   let e₁ := reflect d₁
--   let c ← mk_instance_cache q(Nat)
--   let (c, p₁) ← prove_lt_nat c q(1) e₁
--   let d₂ := n / d₁
--   let e₂ := reflect d₂
--   let (c, e', p) ← prove_mul_nat c e₁ e₂
--   guard (e' == e)
--   let (c, p₂) ← prove_lt_nat c q(1) e₂
--   return <| q(@Nat.not_prime_mul').mk_app [e₁, e₂, e, p, p₁, p₂]


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
  | q(minFac $(e)) => do
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

-- /-- Given `a`,`a1 := bit1 a`, `n1` the value of `a1`, `b` and `p : min_fac_helper a b`,
--   returns `(c, ⊢ min_fac a1 = c)`. -/
-- unsafe def prove_min_fac_aux (a : Q(ℕ)) (n1 : ℕ) :
--     instance_cache → expr → expr → tactic (instance_cache × expr × expr)
--   | ic, b, p => do
--     let k ← b.toNat
--     let k1 := bit1 k
--     let b1 := q((bit1 : ℕ → ℕ)).mk_app [b]
--     if n1 < k1 * k1 then do
--         let (ic, e', p₁) ← prove_mul_nat ic b1 b1
--         let (ic, p₂) ← prove_lt_nat ic a1 e'
--         return (ic, a1, q(minFacHelper_5).mk_app [a, b, e', p₁, p₂, p])
--       else
--         let d := k1
--         if to_bool (d < k1) then do
--           let k' := k + 1
--           let e' := reflect k'
--           let (ic, p₁) ← prove_succ ic b e'
--           let p₂ ← prove_non_prime b1 k1 d
--           prove_min_fac_aux ic e' <| q(minFacHelper_2).mk_app [a, b, e', p₁, p₂, p]
--         else do
--           let nc := n1 % k1
--           let (ic, c, pc) ← prove_div_mod ic a1 b1 tt
--           if nc = 0 then return (ic, b1, q(minFacHelper_4).mk_app [a, b, pc, p])
--             else do
--               let (ic, p₀) ← prove_pos ic c
--               let k' := k + 1
--               let e' := reflect k'
--               let (ic, p₁) ← prove_succ ic b e'
--               prove_min_fac_aux ic e' <| q(minFacHelper_3).mk_app [a, b, e', c, p₁, pc, p₀, p]

theorem isNat_minFac_1 : {a : ℕ} → {a' : ℕ} →
    IsNat a a' → a' = 1 → IsNat a.minFac 1
  | _, _, ⟨rfl⟩, rfl => ⟨minFac_one⟩

theorem isNat_minFac_2 : {a : ℕ} → {a' : ℕ} →
    IsNat a a' → a' % 2 = 0 → IsNat a.minFac 2
  | a, _, ⟨rfl⟩, h => ⟨show a.minFac = 2 by rw [minFac_eq_two_iff, Nat.dvd_iff_mod_eq_zero, h]⟩

theorem isNat_minFac_3 : {n : ℕ} → {n' : ℕ} → {k : ℕ} → {k' : ℕ} →
    IsNat n n' → IsNat k k' → MinFacHelper n' k → n' % k = 0 → IsNat (minFac n) k' := by
  sorry
  -- rw [← Nat.dvd_iff_mod_eq_zero] at hd
  -- exact le_antisymm (minFac_le_of_dvd (Nat.bit1_lt h.1) hd) h.2

theorem isNat_minFac_4 : {n : ℕ} → {n' : ℕ} → {k : ℕ} →
    IsNat n n' → MinFacHelper n' k → n' < k * k → IsNat (minFac n) n' := by
  sorry

-- theorem isNat_minFac : {a : ℕ} → {a' c : ℕ} →
--     IsNat a a' → Nat.minFac a' = c → IsNat a.minFac c
--   | _, _, _, ⟨rfl⟩, rfl => ⟨by simp⟩


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
      aux (k + 2) prf'
    -- remark: `deriveBool q($nn % $k = 0)` is 5x slower than the following test
    else
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
  -- to compute it, and that speeds up this case
  let rec core : MetaM (Result q(Nat.Prime $n)) := do
    if n' < 2 then
      let r : Q(Nat.ble ($k * $k) $nn = false) := (q(Eq.refl false) : Expr)
      return .isFalse q(_)
    let d := n'.minFac
    if n ≤ 1 ∨ n.minFac < n then

    -- todo: don't verify computation of `Nat.minFac` if `n` is not prime.
    let ⟨b, pn⟩ ← deriveBoolOfIff q(1 < $n ∧ Nat.minFac $n = $n) q(Nat.Prime $n) q(prime_helper $n)
    return .ofBoolResult pn
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

-- set_option trace.Tactic.norm_num true

set_option profiler true
set_option trace.profiler true
-- efficiency is worse than in Lean 3. In Lean 4 `2 ^ 19 - 1` takes ~3.0s, while in Lean 3 it takes 330ms and testing `2 ^ 25 - 39` takes ~3.3s, .
/-
attempt 1: 3000ms
speed-up `n<k*k`: 1580ms
speed-up `n%k`: 298ms
speed-up not prime k: 154ms
Lean 3: 330ms
Lean 3 `2 ^ 25 - 39`: 3300ms. Lean 4: 700ms + 130ms type-checking
-/
-- example : Nat.Prime (2 ^ 19 - 1) := by norm_num1
-- set_option maxRecDepth 8000 in
-- example : Nat.Prime (2 ^ 25 - 39) := by norm_num1
-- -- set_option maxRecDepth 80000 in
-- -- example : Nat.Prime (2 ^ 27 - 39) := by norm_num1
-- example : ¬ Nat.Prime (17 * (2 ^ 25 - 39)) := by norm_num1
-- -- example : Nat.minFac (17 * (2 ^ 25 - 39)) = 17 := by norm_num
-- example : Nat.minFac (17 * 19) / 3 = 5 := by norm_num

end Mathlib.Meta.NormNum
