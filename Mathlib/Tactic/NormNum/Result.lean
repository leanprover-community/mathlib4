/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Invertible
import Mathlib.Data.Sigma.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Data.Int.Cast.Basic
import Qq.MetaM

/-!
## The `Result` type for `norm_num`

We set up predicates `IsNat`, `IsInt`, and `IsRat`,
stating that an element of a ring is equal to the "normal form" of a natural number, integer,
or rational number coerced into that ring.

We then define `Result e`, which contains a proof that a typed expression `e : Q($α)`
is equal to the coercion of an explicit natural number, integer, or rational number,
or is either `true` or `false`.

-/


set_option autoImplicit true

open Lean hiding Rat mkRat
open Lean.Meta Qq Lean.Elab Term

namespace Mathlib
namespace Meta.NormNum

/-- A shortcut (non)instance for `AddMonoidWithOne ℕ` to shrink generated proofs. -/
def instAddMonoidWithOneNat : AddMonoidWithOne ℕ := inferInstance

/-- A shortcut (non)instance for `AddMonoidWithOne α` from `Ring α` to shrink generated proofs. -/
def instAddMonoidWithOne [Ring α] : AddMonoidWithOne α := inferInstance

/-- Helper function to synthesize a typed `AddMonoidWithOne α` expression. -/
def inferAddMonoidWithOne (α : Q(Type u)) : MetaM Q(AddMonoidWithOne $α) :=
  return ← synthInstanceQ (q(AddMonoidWithOne $α) : Q(Type u)) <|>
    throwError "not an AddMonoidWithOne"

/-- Helper function to synthesize a typed `Semiring α` expression. -/
def inferSemiring (α : Q(Type u)) : MetaM Q(Semiring $α) :=
  return ← synthInstanceQ (q(Semiring $α) : Q(Type u)) <|> throwError "not a semiring"

/-- Helper function to synthesize a typed `Ring α` expression. -/
def inferRing (α : Q(Type u)) : MetaM Q(Ring $α) :=
  return ← synthInstanceQ (q(Ring $α) : Q(Type u)) <|> throwError "not a ring"

/--
Represent an integer as a "raw" typed expression.

This uses `.lit (.natVal n)` internally to represent a natural number,
rather than the preferred `OfNat.ofNat` form.
We use this internally to avoid unnecessary typeclass searches.

This function is the inverse of `Expr.intLit!`.
-/
def mkRawIntLit (n : ℤ) : Q(ℤ) :=
  let lit : Q(ℕ) := mkRawNatLit n.natAbs
  if 0 ≤ n then q(.ofNat $lit) else q(.negOfNat $lit)

/--
Represent an integer as a "raw" typed expression.

This `.lit (.natVal n)` internally to represent a natural number,
rather than the preferred `OfNat.ofNat` form.
We use this internally to avoid unnecessary typeclass searches.
-/
def mkRawRatLit (q : ℚ) : Q(ℚ) :=
  let nlit : Q(ℤ) := mkRawIntLit q.num
  let dlit : Q(ℕ) := mkRawNatLit q.den
  q(mkRat $nlit $dlit)

/-- Extract the raw natlit representing the absolute value of a raw integer literal
(of the type produced by `Mathlib.Meta.NormNum.mkRawIntLit`) along with an equality proof. -/
def rawIntLitNatAbs (n : Q(ℤ)) : (m : Q(ℕ)) × Q(Int.natAbs $n = $m) :=
  if n.isAppOfArity ``Int.ofNat 1 then
    have m : Q(ℕ) := n.appArg!
    ⟨m, show Q(Int.natAbs (Int.ofNat $m) = $m) from q(Int.natAbs_ofNat $m)⟩
  else if n.isAppOfArity ``Int.negOfNat 1 then
    have m : Q(ℕ) := n.appArg!
    ⟨m, show Q(Int.natAbs (Int.negOfNat $m) = $m) from q(Int.natAbs_neg $m)⟩
  else
    panic! "not a raw integer literal"

/--
Constructs an `ofNat` application `a'` with the canonical instance, together with a proof that
the instance is equal to the result of `Nat.cast` on the given `AddMonoidWithOne` instance.

This function is performance-critical, as many higher level tactics have to construct numerals.
So rather than using typeclass search we hardcode the (relatively small) set of solutions
to the typeclass problem.
-/
def mkOfNat (α : Q(Type u)) (_sα : Q(AddMonoidWithOne $α)) (lit : Q(ℕ)) :
    MetaM ((a' : Q($α)) × Q($lit = $a')) := do
  if α.isConstOf ``Nat then
    let a' : Q(ℕ) := q(OfNat.ofNat $lit : ℕ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else if α.isConstOf ``Int then
    let a' : Q(ℤ) := q(OfNat.ofNat $lit : ℤ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else if α.isConstOf ``Rat then
    let a' : Q(ℚ) := q(OfNat.ofNat $lit : ℚ)
    pure ⟨a', (q(Eq.refl $a') : Expr)⟩
  else
    let some n := lit.rawNatLit? | failure
    match n with
    | 0 => pure ⟨q(0 : $α), (q(Nat.cast_zero (R := $α)) : Expr)⟩
    | 1 => pure ⟨q(1 : $α), (q(Nat.cast_one (R := $α)) : Expr)⟩
    | k+2 =>
      let k : Q(ℕ) := mkRawNatLit k
      let _x : Q(Nat.AtLeastTwo $lit) :=
        (q(instNatAtLeastTwo (n := $k)) : Expr)
      let a' : Q($α) := q(OfNat.ofNat $lit)
      pure ⟨a', (q(Eq.refl $a') : Expr)⟩

/-- Assert that an element of a semiring is equal to the coercion of some natural number. -/
structure IsNat [AddMonoidWithOne α] (a : α) (n : ℕ) : Prop where
  /-- The element is equal to the coercion of the natural number. -/
  out : a = n

theorem IsNat.raw_refl (n : ℕ) : IsNat n n := ⟨rfl⟩

/--
A "raw nat cast" is an expression of the form `(Nat.rawCast lit : α)` where `lit` is a raw
natural number literal. These expressions are used by tactics like `ring` to decrease the number
of typeclass arguments required in each use of a number literal at type `α`.
-/
@[simp] def _root_.Nat.rawCast [AddMonoidWithOne α] (n : ℕ) : α := n

theorem IsNat.to_eq [AddMonoidWithOne α] {n} : {a a' : α} → IsNat a n → n = a' → a = a'
  | _, _, ⟨rfl⟩, rfl => rfl

theorem IsNat.to_raw_eq [AddMonoidWithOne α] : IsNat (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsNat.of_raw (α) [AddMonoidWithOne α] (n : ℕ) : IsNat (n.rawCast : α) n := ⟨rfl⟩

@[elab_as_elim]
theorem isNat.natElim {p : ℕ → Prop} : {n : ℕ} → {n' : ℕ} → IsNat n n' → p n' → p n
  | _, _, ⟨rfl⟩, h => h

/-- Assert that an element of a ring is equal to the coercion of some integer. -/
structure IsInt [Ring α] (a : α) (n : ℤ) : Prop where
  /-- The element is equal to the coercion of the integer. -/
  out : a = n

/--
A "raw int cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural number literal

(That is, we only actually use this function for negative integers.) This representation is used by
tactics like `ring` to decrease the number of typeclass arguments required in each use of a number
literal at type `α`.
-/
@[simp] def _root_.Int.rawCast [Ring α] (n : ℤ) : α := n

theorem IsInt.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsInt a (.ofNat n) → IsNat a n
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsNat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsInt a (.ofNat n)
  | _, _, ⟨rfl⟩ => ⟨by simp⟩

theorem IsInt.to_raw_eq [Ring α] : IsInt (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsInt.of_raw (α) [Ring α] (n : ℤ) : IsInt (n.rawCast : α) n := ⟨rfl⟩

theorem IsInt.neg_to_eq {α} [Ring α] {n} :
    {a a' : α} → IsInt a (.negOfNat n) → n = a' → a = -a'
  | _, _, ⟨rfl⟩, rfl => by simp [Int.negOfNat_eq, Int.cast_neg]

theorem IsInt.nonneg_to_eq {α} [Ring α] {n}
    {a a' : α} (h : IsInt a (.ofNat n)) (e : n = a') : a = a' := h.to_isNat.to_eq e

/--
Assert that an element of a ring is equal to `num / denom`
(and `denom` is invertible so that this makes sense).
We will usually also have `num` and `denom` coprime,
although this is not part of the definition.
-/
inductive IsRat [Ring α] (a : α) (num : ℤ) (denom : ℕ) : Prop
  | mk (inv : Invertible (denom : α)) (eq : a = num * ⅟(denom : α))

/--
A "raw rat cast" is an expression of the form:

* `(Nat.rawCast lit : α)` where `lit` is a raw natural number literal
* `(Int.rawCast (Int.negOfNat lit) : α)` where `lit` is a nonzero raw natural number literal
* `(Rat.rawCast n d : α)` where `n` is a raw int literal, `d` is a raw nat literal, and `d` is not
  `1` or `0`.

(where a raw int literal is of the form `Int.ofNat lit` or `Int.negOfNat nzlit` where `lit` is a raw
nat literal)

This representation is used by tactics like `ring` to decrease the number of typeclass arguments
required in each use of a number literal at type `α`.
-/
@[simp]
def _root_.Rat.rawCast [DivisionRing α] (n : ℤ) (d : ℕ) : α := n / d

theorem IsRat.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsRat a (.ofNat n) (nat_lit 1) → IsNat a n
  | _, _, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩

theorem IsNat.to_isRat {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsRat a (.ofNat n) (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩

theorem IsRat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsRat a n (nat_lit 1) → IsInt a n
  | _, _, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩

theorem IsInt.to_isRat {α} [Ring α] : ∀ {a : α} {n}, IsInt a n → IsRat a n (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩

theorem IsRat.to_raw_eq [DivisionRing α] : ∀ {a}, IsRat (a : α) n d → a = Rat.rawCast n d
  | _, ⟨inv, rfl⟩ => by simp [div_eq_mul_inv]

theorem IsRat.neg_to_eq {α} [DivisionRing α] {n d} :
    {a n' d' : α} → IsRat a (.negOfNat n) d → n = n' → d = d' → a = -(n' / d')
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]

theorem IsRat.nonneg_to_eq {α} [DivisionRing α] {n d} :
    {a n' d' : α} → IsRat a (.ofNat n) d → n = n' → d = d' → a = n' / d'
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]

theorem IsRat.of_raw (α) [DivisionRing α] (n : ℤ) (d : ℕ)
    (h : (d : α) ≠ 0) : IsRat (Rat.rawCast n d : α) n d :=
  have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩

theorem IsRat.den_nz {α} [DivisionRing α] {a n d} : IsRat (a : α) n d → (d : α) ≠ 0
  | ⟨_, _⟩ => nonzero_of_invertible (d : α)

/-- The result of `norm_num` running on an expression `x` of type `α`.
Untyped version of `Result`. -/
inductive Result' where
  /-- Untyped version of `Result.isBool`. -/
  | isBool (val : Bool) (proof : Expr)
  /-- Untyped version of `Result.isNat`. -/
  | isNat (inst lit proof : Expr)
  /-- Untyped version of `Result.isNegNat`. -/
  | isNegNat (inst lit proof : Expr)
  /-- Untyped version of `Result.isRat`. -/
  | isRat (inst : Expr) (q : Rat) (n d proof : Expr)
  deriving Inhabited

section
set_option linter.unusedVariables false

/-- The result of `norm_num` running on an expression `x` of type `α`. -/
@[nolint unusedArguments] def Result {α : Q(Type u)} (x : Q($α)) := Result'

instance : Inhabited (Result x) := inferInstanceAs (Inhabited Result')

/-- The result is `proof : x`, where `x` is a (true) proposition. -/
@[match_pattern, inline] def Result.isTrue {x : Q(Prop)} :
    ∀ (proof : Q($x)), @Result _ (q(Prop) : Q(Type)) x := Result'.isBool true

/-- The result is `proof : ¬x`, where `x` is a (false) proposition. -/
@[match_pattern, inline] def Result.isFalse {x : Q(Prop)} :
    ∀ (proof : Q(¬$x)), @Result _ (q(Prop) : Q(Type)) x := Result'.isBool false

/-- The result is `lit : ℕ` (a raw nat literal) and `proof : isNat x lit`. -/
@[match_pattern, inline] def Result.isNat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(AddMonoidWithOne $α) := by assumption) (lit : Q(ℕ)) (proof : Q(IsNat $x $lit)),
      Result x := Result'.isNat

/-- The result is `-lit` where `lit` is a raw nat literal
and `proof : isInt x (.negOfNat lit)`. -/
@[match_pattern, inline] def Result.isNegNat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(Ring $α) := by assumption) (lit : Q(ℕ)) (proof : Q(IsInt $x (.negOfNat $lit))),
      Result x := Result'.isNegNat

/-- The result is `proof : isRat x n d`, where `n` is either `.ofNat lit` or `.negOfNat lit`
with `lit` a raw nat literal and `d` is a raw nat literal (not 0 or 1),
and `q` is the value of `n / d`. -/
@[match_pattern, inline] def Result.isRat {α : Q(Type u)} {x : Q($α)} :
    ∀ (inst : Q(DivisionRing $α) := by assumption) (q : Rat) (n : Q(ℤ)) (d : Q(ℕ))
      (proof : Q(IsRat $x $n $d)), Result x := Result'.isRat

end

/-- The result is `z : ℤ` and `proof : isNat x z`. -/
-- Note the independent arguments `z : Q(ℤ)` and `n : ℤ`.
-- We ensure these are "the same" when calling.
def Result.isInt {α : Q(Type u)} {x : Q($α)} (inst : Q(Ring $α) := by assumption)
    (z : Q(ℤ)) (n : ℤ) (proof : Q(IsInt $x $z)) : Result x :=
  have lit : Q(ℕ) := z.appArg!
  if 0 ≤ n then
    let proof : Q(IsInt $x (.ofNat $lit)) := proof
    .isNat q(instAddMonoidWithOne) lit q(IsInt.to_isNat $proof)
  else
    .isNegNat inst lit proof

/-- The result depends on whether `q : ℚ` happens to be an integer, in which case the result is
`.isInt ..` whereas otherwise it's `.isRat ..`. -/
def Result.isRat' {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionRing $α) := by assumption)
    (q : Rat) (n : Q(ℤ)) (d : Q(ℕ)) (proof : Q(IsRat $x $n $d)) : Result x :=
  if q.den = 1 then
    have proof : Q(IsRat $x $n (nat_lit 1)) := proof
    .isInt q(DivisionRing.toRing) n q.num q(IsRat.to_isInt $proof)
  else
    .isRat inst q n d proof

instance : ToMessageData (Result x) where
  toMessageData
  | .isBool true proof => m!"isTrue ({proof})"
  | .isBool false proof => m!"isFalse ({proof})"
  | .isNat _ lit proof => m!"isNat {lit} ({proof})"
  | .isNegNat _ lit proof => m!"isNegNat {lit} ({proof})"
  | .isRat _ q _ _ proof => m!"isRat {q} ({proof})"

/-- Returns the rational number that is the result of `norm_num` evaluation. -/
def Result.toRat : Result e → Option Rat
  | .isBool .. => none
  | .isNat _ lit _ => some lit.natLit!
  | .isNegNat _ lit _ => some (-lit.natLit!)
  | .isRat _ q .. => some q

/-- Returns the rational number that is the result of `norm_num` evaluation, along with a proof
that the denominator is nonzero in the `isRat` case. -/
def Result.toRatNZ : Result e → Option (Rat × Option Expr)
  | .isBool .. => none
  | .isNat _ lit _ => some (lit.natLit!, none)
  | .isNegNat _ lit _ => some (-lit.natLit!, none)
  | .isRat _ q _ _ p => some (q, q(IsRat.den_nz $p))

/--
Extract from a `Result` the integer value (as both a term and an expression),
and the proof that the original expression is equal to this integer.
-/
def Result.toInt {α : Q(Type u)} {e : Q($α)} (_i : Q(Ring $α) := by with_reducible assumption) :
    Result e → Option (ℤ × (lit : Q(ℤ)) × Q(IsInt $e $lit))
  | .isNat _ lit proof => do
    have proof : Q(@IsNat _ instAddMonoidWithOne $e $lit) := proof
    pure ⟨lit.natLit!, q(.ofNat $lit), q(($proof).to_isInt)⟩
  | .isNegNat _ lit proof => pure ⟨-lit.natLit!, q(.negOfNat $lit), proof⟩
  | _ => failure

/--
Extract from a `Result` the rational value (as both a term and an expression),
and the proof that the original expression is equal to this rational number.
-/
def Result.toRat' {α : Q(Type u)} {e : Q($α)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) :
    Result e → Option (ℚ × (n : Q(ℤ)) × (d : Q(ℕ)) × Q(IsRat $e $n $d))
  | .isBool .. => none
  | .isNat _ lit proof =>
    have proof : Q(@IsNat _ instAddMonoidWithOne $e $lit) := proof
    some ⟨lit.natLit!, q(.ofNat $lit), q(nat_lit 1), q(($proof).to_isRat)⟩
  | .isNegNat _ lit proof =>
    have proof : Q(@IsInt _ DivisionRing.toRing $e (.negOfNat $lit)) := proof
    some ⟨-lit.natLit!, q(.negOfNat $lit), q(nat_lit 1),
      (q(@IsInt.to_isRat _ DivisionRing.toRing _ _ $proof) : Expr)⟩
  | .isRat _ q n d proof => some ⟨q, n, d, proof⟩

/--
Given a `NormNum.Result e` (which uses `IsNat`, `IsInt`, `IsRat` to express equality to a rational
numeral), converts it to an equality `e = Nat.rawCast n`, `e = Int.rawCast n`, or
`e = Rat.rawCast n d` to a raw cast expression, so it can be used for rewriting.
-/
def Result.toRawEq {α : Q(Type u)} {e : Q($α)} : Result e → (e' : Q($α)) × Q($e = $e')
  | .isBool false p =>
    have e : Q(Prop) := e; have p : Q(¬$e) := p
    ⟨(q(False) : Expr), (q(eq_false $p) : Expr)⟩
  | .isBool true p =>
    have e : Q(Prop) := e; have p : Q($e) := p
    ⟨(q(True) : Expr), (q(eq_true $p) : Expr)⟩
  | .isNat _ lit p => ⟨q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => ⟨q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isRat _ _ n d p => ⟨q(Rat.rawCast $n $d), q(IsRat.to_raw_eq $p)⟩

/--
`Result.toRawEq` but providing an integer. Given a `NormNum.Result e` for something known to be an
integer (which uses `IsNat` or `IsInt` to express equality to an integer numeral), converts it to
an equality `e = Nat.rawCast n` or `e = Int.rawCast n` to a raw cast expression, so it can be used
for rewriting. Gives `none` if not an integer.
-/
def Result.toRawIntEq {α : Q(Type u)} {e : Q($α)} : Result e →
    Option (ℤ × (e' : Q($α)) × Q($e = $e'))
  | .isNat _ lit p => some ⟨lit.natLit!, q(Nat.rawCast $lit), q(IsNat.to_raw_eq $p)⟩
  | .isNegNat _ lit p => some ⟨-lit.natLit!, q(Int.rawCast (.negOfNat $lit)), q(IsInt.to_raw_eq $p)⟩
  | .isRat _ .. | .isBool .. => none

/-- Constructs a `Result` out of a raw nat cast. Assumes `e` is a raw nat cast expression. -/
def Result.ofRawNat {α : Q(Type u)} (e : Q($α)) : Result e := Id.run do
  let .app (.app _ (sα : Q(AddMonoidWithOne $α))) (lit : Q(ℕ)) := e | panic! "not a raw nat cast"
  .isNat sα lit (q(IsNat.of_raw $α $lit) : Expr)

/-- Constructs a `Result` out of a raw int cast.
Assumes `e` is a raw int cast expression denoting `n`. -/
def Result.ofRawInt {α : Q(Type u)} (n : ℤ) (e : Q($α)) : Result e :=
  if 0 ≤ n then
    Result.ofRawNat e
  else Id.run do
    let .app (.app _ (rα : Q(Ring $α))) (.app _ (lit : Q(ℕ))) := e | panic! "not a raw int cast"
    .isNegNat rα lit (q(IsInt.of_raw $α (.negOfNat $lit)) : Expr)

/-- Constructs a `Result` out of a raw rat cast.
Assumes `e` is a raw rat cast expression denoting `n`. -/
def Result.ofRawRat {α : Q(Type u)} (q : ℚ) (e : Q($α)) (hyp : Option Expr := none) : Result e :=
  if q.den = 1 then
    Result.ofRawInt q.num e
  else Id.run do
    let .app (.app (.app _ (dα : Q(DivisionRing $α))) (n : Q(ℤ))) (d : Q(ℕ)) := e
      | panic! "not a raw rat cast"
    let hyp : Q(($d : $α) ≠ 0) := hyp.get!
    .isRat dα q n d (q(IsRat.of_raw $α $n $d $hyp) : Expr)

/-- Convert a `Result` to a `Simp.Result`. -/
def Result.toSimpResult {α : Q(Type u)} {e : Q($α)} : Result e → MetaM Simp.Result
  | r@(.isBool ..) => let ⟨expr, proof?⟩ := r.toRawEq; pure { expr, proof? }
  | .isNat sα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α sα lit
    return { expr := a', proof? := q(IsNat.to_eq $p $pa') }
  | .isNegNat _rα lit p => do
    let ⟨a', pa'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) lit
    return { expr := q(-$a'), proof? := q(IsInt.neg_to_eq $p $pa') }
  | .isRat _ q n d p => do
    have lit : Q(ℕ) := n.appArg!
    if q < 0 then
      let p : Q(IsRat $e (.negOfNat $lit) $d) := p
      let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) lit
      let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
      return { expr := q(-($n' / $d')), proof? := q(IsRat.neg_to_eq $p $pn' $pd') }
    else
      let p : Q(IsRat $e (.ofNat $lit) $d) := p
      let ⟨n', pn'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) lit
      let ⟨d', pd'⟩ ← mkOfNat α q(AddCommMonoidWithOne.toAddMonoidWithOne) d
      return { expr := q($n' / $d'), proof? := q(IsRat.nonneg_to_eq $p $pn' $pd') }

/-- Given `Mathlib.Meta.NormNum.Result.isBool p b`, this is the type of `p`.
  Note that `BoolResult p b` is definitionally equal to `Expr`, and if you write `match b with ...`,
  then in the `true` branch `BoolResult p true` is reducibly equal to `Q($p)` and
  in the `false` branch it is reducibly equal to `Q(¬ $p)`. -/
abbrev BoolResult (p : Q(Prop)) (b : Bool) : Type :=
  Q(Bool.rec (¬ $p) ($p) $b)

/-- Obtain a `Result` from a `BoolResult`. -/
def Result.ofBoolResult {p : Q(Prop)} {b : Bool} (prf : BoolResult p b) : Result q(Prop) :=
  Result'.isBool b prf

/-- If `a = b` and we can evaluate `b`, then we can evaluate `a`. -/
def Result.eqTrans {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b)) : Result b → Result a
  | .isBool true proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q($b) := proof
    Result.isTrue (x := a) q($eq ▸ $proof)
  | .isBool false proof =>
    have a : Q(Prop) := a
    have b : Q(Prop) := b
    have eq : Q($a = $b) := eq
    have proof : Q(¬ $b) := proof
    Result.isFalse (x := a) q($eq ▸ $proof)
  | .isNat inst lit proof => Result.isNat inst lit q($eq ▸ $proof)
  | .isNegNat inst lit proof => Result.isNegNat inst lit q($eq ▸ $proof)
  | .isRat inst q n d proof => Result.isRat inst q n d q($eq ▸ $proof)

end Meta.NormNum
