/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Algebra.Field.Basic

/-!
# `norm_num` plugins for `Rat.cast` and `⁻¹`.
-/

variable {u : Lean.Level}

namespace Mathlib.Meta.NormNum

open Lean Meta Qq

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`. -/
def inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`, if it exists. -/
def inferCharZeroOfRing? {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`. -/
def inferCharZeroOfAddMonoidWithOne {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero AddMonoidWithOne"

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`, if it
exists. -/
def inferCharZeroOfAddMonoidWithOne? {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
      MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`. -/
def inferCharZeroOfDivisionRing {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ q(CharZero $α) <|>
    throwError "not a characteristic zero division ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`, if it
exists. -/
def inferCharZeroOfDivisionRing? {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ q(CharZero $α)).toOption

section CharP

open Nat in
def invMod (x n : ℕ) : ℕ :=
  if x % n = 0 then 0 else
  match (xgcdAux x 1 0 n 0 1).2.1 % n with
  | .ofNat r => r
  | .negSucc r => n - r - 1
  where
  xgcdAux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
  | 0, _, _, r', s', t' => (r', s', t')
  | succ k, s, t, r', s', t' =>
    let q := r' / succ k
    xgcdAux (r' % succ k) (s' - q * s) (t' - q * t) (succ k) s t
termination_by k => k
decreasing_by exact mod_lt _ <| (succ_pos _).gt

lemma IsNat.inv (p : ℕ) {α : Type*} [DivisionRing α] [CharP α p] {e : α} {n n' : ℕ}
    (hn' : (n = 0 ∧ n' = 0) ∨ n * n' % p = 1)
    (H : IsNat e n) :
    IsNat e⁻¹ n' := by
  obtain ⟨rfl⟩ := H
  obtain rfl | hn := eq_or_ne n 0
  · obtain rfl : n' = 0 := by simpa using hn'
    exact ⟨by simp⟩
  replace hn' : n * n' % p = 1 := by simpa [hn] using hn'
  refine ⟨inv_eq_of_mul_eq_one_right ?_⟩
  simpa [hn'] using congr_arg (Nat.cast (R := α)) (Nat.mod_add_div (n * n') p).symm

lemma IsNat.ratCast_of_charP (p : ℕ) {α : Type*} [DivisionRing α] [CharP α p]
    {x x' : ℚ} {n : ℤ} {d n' : ℕ}
    (hx : IsRat x n d) (hx' : x' = n / d)
    (hn' : if x'.den % p = 0 then n' = 0 else (n' * x'.den - x'.num) % p = 0) :
    IsNat (x : α) n' := by
  obtain rfl : x = x' := by
    obtain ⟨_, rfl⟩ := hx
    simp [hx', div_eq_mul_inv]
  classical
  simp_rw [← Nat.dvd_iff_mod_eq_zero, ← CharP.cast_eq_zero_iff α p,
    ← Int.dvd_iff_emod_eq_zero, ← CharP.intCast_eq_zero_iff (R := α), Int.cast_sub,
    sub_eq_zero] at hn'
  split_ifs at hn' with h
  · exact ⟨by simp [DivisionRing.ratCast_def, h, hn']⟩
  · exact ⟨by simp [DivisionRing.ratCast_def, ← hn', h]⟩

def evalInvCharP (p : ℕ) {u : Level} {α : Q(Type u)} {inst : Q(DivisionRing $α)}
    {e : Q($α)} (res : Result q($e)) :
    MetaM (Result q($e⁻¹)) := do
  let .isNat inst' lit proof ← reduceCharP p e res | failure
  let _ ← synthInstanceQ q(CharP $α $p)
  have : $inst' =Q ($inst).toRing.toAddGroupWithOne.toAddMonoidWithOne := ⟨⟩
  have n' : Q(ℕ) := mkRawNatLit (invMod lit.natLit! p)
  let pf ← mkDecideProofQ q($lit = 0 ∧ $n' = 0 ∨ $lit * $n' % $p = 1)
  return .isNat _ n' q(IsNat.inv $p $pf $proof)

def evalRatCastCharP (p : ℕ) {u : Level} {α : Q(Type u)} {inst : Q(DivisionRing $α)}
    (e : Q(ℚ)) (ne : Q(ℤ)) (de : Q(ℕ)) (he : Q(IsRat $e $ne $de)) :
    MetaM (Result q(Rat.cast (K := $α) $e)) := do
  trace[debug] m!"got {he}"
  let _ ← synthInstanceQ q(CharP $α $p)
  let x : ℚ := ne.intLit! / de.natLit!
  have xe : Q(ℚ) := mkRawRatLit x
  trace[debug] m!"parsed into {x}"
  have n' : Q(ℕ) := mkRawNatLit ((invMod x.den p * (x.num % p + p).natAbs) % p)
  trace[debug] m!"start to show {e} ==> {n'}"
  let pf ← mkDecideProofQ
    q(if ($xe).den % $p = 0 then $n' = 0 else ($n' * ($xe).den - ($xe).num) % $p = 0)
  let pf₂ ← mkDecideProofQ q($xe = $ne / $de)
  trace[debug] m!"decide succeeded on {e} ==> {n'}"
  return .isNat _ n' q(IsNat.ratCast_of_charP $p $he $pf₂ $pf)

end CharP

theorem isRat_mkRat : {a na n : ℤ} → {b nb d : ℕ} → IsInt a na → IsNat b nb →
    IsRat (na / nb : ℚ) n d → IsRat (mkRat a b) n d
  | _, _, _, _, _, _, ⟨rfl⟩, ⟨rfl⟩, ⟨_, h⟩ => by rw [Rat.mkRat_eq_div]; exact ⟨_, h⟩

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `mkRat a b`,
such that `norm_num` successfully recognises both `a` and `b`, and returns `a / b`. -/
@[norm_num mkRat _ _]
def evalMkRat : NormNumExt where eval {u α} (e : Q(ℚ)) : NormNumM (Result e) := do
  let .app (.app (.const ``mkRat _) (a : Q(ℤ))) (b : Q(ℕ)) ← whnfR e | failure
  haveI' : $e =Q mkRat $a $b := ⟨⟩
  let ra ← derive a
  let some ⟨_, na, pa⟩ := ra.toInt (q(Int.instRing) : Q(Ring Int)) | failure
  let ⟨nb, pb⟩ ← deriveNat q($b) q(AddCommMonoidWithOne.toAddMonoidWithOne)
  let rab ← derive q($na / $nb : Rat)
  let ⟨q, n, d, p⟩ ← rab.toRat' q(Rat.instDivisionRing)
  return .isRat' _ q n d q(isRat_mkRat $pa $pb $p)

theorem isNat_ratCast {R : Type*} [DivisionRing R] : {q : ℚ} → {n : ℕ} →
    IsNat q n → IsNat (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isInt_ratCast {R : Type*} [DivisionRing R] : {q : ℚ} → {n : ℤ} →
    IsInt q n → IsInt (q : R) n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_ratCast {R : Type*} [DivisionRing R] [CharZero R] : {q : ℚ} → {n : ℤ} → {d : ℕ} →
    IsRat q n d → IsRat (q : R) n d
  | _, _, _, ⟨⟨qi,_,_⟩, rfl⟩ => ⟨⟨qi, by norm_cast, by norm_cast⟩, by simp only []; norm_cast⟩

/-- The `norm_num` extension which identifies an expression `RatCast.ratCast q` where `norm_num`
recognizes `q`, returning the cast of `q`. -/
@[norm_num Rat.cast _, RatCast.ratCast _] def evalRatCast : NormNumExt where eval {u α} e := do
  let dα ← inferDivisionRing α
  let .app r (a : Q(ℚ)) ← whnfR e | failure
  guard <|← withNewMCtxDepth <| isDefEq r q(Rat.cast (K := $α))
  let r ← derive q($a)
  haveI' : $e =Q Rat.cast $a := ⟨⟩
  match r with
  | .isNat _ na pa =>
    assumeInstancesCommute
    return .isNat _ na q(isNat_ratCast $pa)
  | .isNegNat _ na pa =>
    assumeInstancesCommute
    return .isNegNat _ na q(isInt_ratCast $pa)
  | .isRat _ qa na da pa =>
    assumeInstancesCommute
    for p in (← readThe NormNum.Config).char do
      try return ← evalRatCastCharP p (inst := dα) a na da pa
      catch _ => continue
    let i ← inferCharZeroOfDivisionRing dα
    return .isRat dα qa na da q(isRat_ratCast $pa)
  | _ => failure

theorem isRat_inv_pos {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.ofNat (Nat.succ n)) d → IsRat a⁻¹ (.ofNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  exact ⟨this, by simp⟩

theorem isRat_inv_one {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 1) → IsNat a⁻¹ (nat_lit 1)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_zero {α} [DivisionRing α] : {a : α} →
    IsNat a (nat_lit 0) → IsNat a⁻¹ (nat_lit 0)
  | _, ⟨rfl⟩ => ⟨by simp⟩

theorem isRat_inv_neg_one {α} [DivisionRing α] : {a : α} →
    IsInt a (.negOfNat (nat_lit 1)) → IsInt a⁻¹ (.negOfNat (nat_lit 1))
  | _, ⟨rfl⟩ => ⟨by simp [inv_neg_one]⟩

theorem isRat_inv_neg {α} [DivisionRing α] [CharZero α] {a : α} {n d : ℕ} :
    IsRat a (.negOfNat (Nat.succ n)) d → IsRat a⁻¹ (.negOfNat d) (Nat.succ n) := by
  rintro ⟨_, rfl⟩
  simp only [Int.negOfNat_eq]
  have := invertibleOfNonzero (α := α) (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))
  generalize Nat.succ n = n at *
  use this; simp only [Int.ofNat_eq_coe, Int.cast_neg,
    Int.cast_natCast, invOf_eq_inv, inv_neg, neg_mul, mul_inv_rev, inv_inv]

attribute [local instance] monadLiftOptionMetaM in
/-- The `norm_num` extension which identifies expressions of the form `a⁻¹`,
such that `norm_num` successfully recognises `a`. -/
@[norm_num _⁻¹] def evalInv : NormNumExt where eval {u α} e := do
  let .app f (a : Q($α)) ← whnfR e | failure
  let ra ← derive a
  let dα ← inferDivisionRing α
  guard <|← withNewMCtxDepth <| isDefEq f q(Inv.inv (α := $α))
  haveI' : $e =Q $a⁻¹ := ⟨⟩
  for p in (← readThe NormNum.Config).char do
    try return ← evalInvCharP p (inst := dα) ra
    catch _ => continue
  let i ← inferCharZeroOfDivisionRing? dα
  assumeInstancesCommute
  let rec
  /-- Main part of `evalInv`. -/
  core : Option (Result e) := do
    let ⟨qa, na, da, pa⟩ ← ra.toRat' dα
    let qb := qa⁻¹
    if qa > 0 then
      if let some i := i then
        have lit : Q(ℕ) := na.appArg!
        haveI : $na =Q Int.ofNat $lit := ⟨⟩
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        haveI : $lit =Q ($lit2).succ := ⟨⟩
        return .isRat' dα qb q(.ofNat $da) lit q(isRat_inv_pos $pa)
      else
        guard (qa = 1)
        let .isNat inst n pa := ra | failure
        haveI' : $n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNat inst n q(isRat_inv_one $pa)
    else if qa < 0 then
      if let some i := i then
        have lit : Q(ℕ) := na.appArg!
        haveI : $na =Q Int.negOfNat $lit := ⟨⟩
        have lit2 : Q(ℕ) := mkRawNatLit (lit.natLit! - 1)
        haveI : $lit =Q ($lit2).succ := ⟨⟩
        return .isRat' dα qb q(.negOfNat $da) lit q(isRat_inv_neg $pa)
      else
        guard (qa = -1)
        let .isNegNat inst n pa := ra | failure
        haveI' : $n =Q nat_lit 1 := ⟨⟩
        assumeInstancesCommute
        return .isNegNat inst n q(isRat_inv_neg_one $pa)
    else
      let .isNat inst n pa := ra | failure
      haveI' : $n =Q nat_lit 0 := ⟨⟩
      assumeInstancesCommute
      return .isNat inst n q(isRat_inv_zero $pa)
  core

end Mathlib.Meta.NormNum
