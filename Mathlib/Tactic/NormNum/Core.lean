/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Std.Lean.Parser
import Std.Lean.Meta.DiscrTree
import Mathlib.Algebra.Invertible
import Mathlib.Data.Rat.Cast
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Conv
import Mathlib.Util.Qq

/-!
## `norm_num` core functionality

This file sets up the `norm_num` tactic and the `@[norm_num]` attribute,
which allow for plugging in new normalization functionality around a simp-based driver.
The actual behavior is in `@[norm_num]`-tagged definitions in `Tactic.NormNum.Basic`
and elsewhere.
-/

set_option autoImplicit true

open Lean hiding Rat mkRat
open Lean.Meta Qq Lean.Elab Term

/-- Attribute for identifying `norm_num` extensions. -/
syntax (name := norm_num) "norm_num " term,+ : attr

namespace Mathlib
namespace Meta.NormNum

initialize registerTraceClass `Tactic.norm_num

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
                       -- 🎉 no goals

theorem IsNat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsInt a (.ofNat n)
  | _, _, ⟨rfl⟩ => ⟨by simp⟩
                       -- 🎉 no goals

theorem IsInt.to_raw_eq [Ring α] : IsInt (a : α) n → a = n.rawCast
  | ⟨e⟩ => e

theorem IsInt.of_raw (α) [Ring α] (n : ℤ) : IsInt (n.rawCast : α) n := ⟨rfl⟩

theorem IsInt.neg_to_eq {α} [Ring α] {n} :
    {a a' : α} → IsInt a (.negOfNat n) → n = a' → a = -a'
  | _, _, ⟨rfl⟩, rfl => by simp [Int.negOfNat_eq, Int.cast_neg]
                           -- 🎉 no goals

theorem IsInt.nonneg_to_eq {α} [Ring α] {n}
    {a a' : α} (h : IsInt a (.ofNat n)) (e : n = a') : a = a' := h.to_isNat.to_eq e

/-- Represent an integer as a typed expression. -/
def mkRawIntLit (n : ℤ) : Q(ℤ) :=
  let lit : Q(ℕ) := mkRawNatLit n.natAbs
  if 0 ≤ n then q(.ofNat $lit) else q(.negOfNat $lit)

/-- Extract the integer from a raw integer literal, as produced by
`Mathlib.Meta.NormNum.mkRawIntLit`. -/
def _root_.Lean.Expr.intLit! (e : Expr) : ℤ :=
  if e.isAppOfArity ``Int.ofNat 1 then
    e.appArg!.natLit!
  else if e.isAppOfArity ``Int.negOfNat 1 then
    .negOfNat e.appArg!.natLit!
  else
    panic! "not a raw integer literal"

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

/-- A shortcut (non)instance for `AddMonoidWithOne ℕ` to shrink generated proofs. -/
def instAddMonoidWithOneNat : AddMonoidWithOne ℕ := inferInstance

/-- A shortcut (non)instance for `Ring ℤ` to shrink generated proofs. -/
def instRingInt : Ring ℤ := inferInstance

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
* `(Rat.rawCast n d : α)` where `n` is a raw int cast, `d` is a raw nat cast, and `d` is not 1 or 0.

This representation is used by tactics like `ring` to decrease the number of typeclass arguments
required in each use of a number literal at type `α`.
-/
@[simp]
def _root_.Rat.rawCast [DivisionRing α] (n : ℤ) (d : ℕ) : α := n / d

theorem IsRat.to_isNat {α} [Ring α] : ∀ {a : α} {n}, IsRat a (.ofNat n) (nat_lit 1) → IsNat a n
  | _, _, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩
                                                        -- 🎉 no goals

theorem IsNat.to_isRat {α} [Ring α] : ∀ {a : α} {n}, IsNat a n → IsRat a (.ofNat n) (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩
                           -- 🎉 no goals
                                    -- 🎉 no goals
                                              -- 🎉 no goals

theorem IsRat.to_isInt {α} [Ring α] : ∀ {a : α} {n}, IsRat a n (nat_lit 1) → IsInt a n
  | _, _, ⟨inv, rfl⟩ => have := @invertibleOne α _; ⟨by simp⟩
                                                        -- 🎉 no goals

theorem IsInt.to_isRat {α} [Ring α] : ∀ {a : α} {n}, IsInt a n → IsRat a n (nat_lit 1)
  | _, _, ⟨rfl⟩ => ⟨⟨1, by simp, by simp⟩, by simp⟩
                           -- 🎉 no goals
                                    -- 🎉 no goals
                                              -- 🎉 no goals

theorem IsRat.to_raw_eq [DivisionRing α] : ∀ {a}, IsRat (a : α) n d → a = Rat.rawCast n d
  | _, ⟨inv, rfl⟩ => by simp [div_eq_mul_inv]
                        -- 🎉 no goals

theorem IsRat.neg_to_eq {α} [DivisionRing α] {n d} :
    {a n' d' : α} → IsRat a (.negOfNat n) d → n = n' → d = d' → a = -(n' / d')
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]
                                      -- 🎉 no goals

theorem IsRat.nonneg_to_eq {α} [DivisionRing α] {n d} :
    {a n' d' : α} → IsRat a (.ofNat n) d → n = n' → d = d' → a = n' / d'
  | _, _, _, ⟨_, rfl⟩, rfl, rfl => by simp [div_eq_mul_inv]
                                      -- 🎉 no goals

theorem IsRat.of_raw (α) [DivisionRing α] (n : ℤ) (d : ℕ)
    (h : (d : α) ≠ 0) : IsRat (Rat.rawCast n d : α) n d :=
  have := invertibleOfNonzero h
  ⟨this, by simp [div_eq_mul_inv]⟩
            -- 🎉 no goals

theorem IsRat.den_nz {α} [DivisionRing α] {a n d} : IsRat (a : α) n d → (d : α) ≠ 0
  | ⟨_, _⟩ => nonzero_of_invertible (d : α)

/-- Represent an integer as a typed expression. -/
def mkRawRatLit (q : ℚ) : Q(ℚ) :=
  let nlit : Q(ℤ) := mkRawIntLit q.num
  let dlit : Q(ℕ) := mkRawNatLit q.den
  q(mkRat $nlit $dlit)

/-- A shortcut (non)instance for `Ring ℚ` to shrink generated proofs. -/
def instRingRat : Ring ℚ := inferInstance

/-- A shortcut (non)instance for `DivisionRing ℚ` to shrink generated proofs. -/
def instDivisionRingRat : DivisionRing ℚ := inferInstance

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

/-- A shortcut (non)instance for `AddMonoidWithOne α` from `Ring α` to shrink generated proofs. -/
def instAddMonoidWithOne [Ring α] : AddMonoidWithOne α := inferInstance

/-- A shortcut (non)instance for `AddMonoidWithOne α` from `DivisionRing α` to shrink generated
proofs. -/
def instAddMonoidWithOne' [DivisionRing α] : AddMonoidWithOne α := inferInstance

/-- A shortcut (non)instance for `Ring α` from `DivisionRing α` to shrink generated proofs. -/
def instRing [DivisionRing α] : Ring α := inferInstance

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

/-- Returns the rational number that is the result of `norm_num` evaluation. -/
def Result.toRat : Result e → Option Rat
  | .isBool .. => none
  | .isNat _ lit _ => some lit.natLit!
  | .isNegNat _ lit _ => some (-lit.natLit!)
  | .isRat _ q .. => some q

end

/-- Convert `undef` to `none` to make an `LOption` into an `Option`. -/
def _root_.Lean.LOption.toOption {α} : Lean.LOption α → Option α
  | .some a => some a
  | _ => none

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

/-- Helper function to synthesize a typed `DivisionRing α` expression. -/
def inferDivisionRing (α : Q(Type u)) : MetaM Q(DivisionRing $α) :=
  return ← synthInstanceQ (q(DivisionRing $α) : Q(Type u)) <|> throwError "not a division ring"

/-- Helper function to synthesize a typed `OrderedSemiring α` expression. -/
def inferOrderedSemiring (α : Q(Type u)) : MetaM Q(OrderedSemiring $α) :=
  return ← synthInstanceQ (q(OrderedSemiring $α) : Q(Type u)) <|>
    throwError "not an ordered semiring"

/-- Helper function to synthesize a typed `OrderedRing α` expression. -/
def inferOrderedRing (α : Q(Type u)) : MetaM Q(OrderedRing $α) :=
  return ← synthInstanceQ (q(OrderedRing $α) : Q(Type u)) <|> throwError "not an ordered ring"

/-- Helper function to synthesize a typed `LinearOrderedField α` expression. -/
def inferLinearOrderedField (α : Q(Type u)) : MetaM Q(LinearOrderedField $α) :=
  return ← synthInstanceQ (q(LinearOrderedField $α) : Q(Type u)) <|>
    throwError "not a linear ordered field"

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`. -/
def inferCharZeroOfRing {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero ring"

/-- Helper function to synthesize a typed `CharZero α` expression given `Ring α`, if it exists. -/
def inferCharZeroOfRing? {α : Q(Type u)} (_i : Q(Ring $α) := by with_reducible assumption) :
    MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`. -/
def inferCharZeroOfAddMonoidWithOne {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero AddMonoidWithOne"

/-- Helper function to synthesize a typed `CharZero α` expression given `AddMonoidWithOne α`, if it
exists. -/
def inferCharZeroOfAddMonoidWithOne? {α : Q(Type u)}
    (_i : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
      MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`. -/
def inferCharZeroOfDivisionRing {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM Q(CharZero $α) :=
  return ← synthInstanceQ (q(CharZero $α) : Q(Prop)) <|>
    throwError "not a characteristic zero division ring"

/-- Helper function to synthesize a typed `OfScientific α` expression given `DivisionRing α`. -/
def inferOfScientific (α : Q(Type u)) : MetaM Q(OfScientific $α) :=
  return ← synthInstanceQ (q(OfScientific $α) : Q(Type u)) <|>
    throwError "does not support scientific notation"

/-- Helper function to synthesize a typed `CharZero α` expression given `DivisionRing α`, if it
exists. -/
def inferCharZeroOfDivisionRing? {α : Q(Type u)}
    (_i : Q(DivisionRing $α) := by with_reducible assumption) : MetaM (Option Q(CharZero $α)) :=
  return (← trySynthInstanceQ (q(CharZero $α) : Q(Prop))).toOption

/-- Helper function to synthesize a typed `RatCast α` expression. -/
def inferRatCast (α : Q(Type u)) : MetaM Q(RatCast $α) :=
  return ← synthInstanceQ (q(RatCast $α) : Q(Type u)) <|> throwError "does not support a rat cast"

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

instance : ToMessageData (Result x) where
  toMessageData
  | .isBool true proof => m!"isTrue ({proof})"
  | .isBool false proof => m!"isFalse ({proof})"
  | .isNat _ lit proof => m!"isNat {lit} ({proof})"
  | .isNegNat _ lit proof => m!"isNegNat {lit} ({proof})"
  | .isRat _ q _ _ proof => m!"isRat {q} ({proof})"

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

/-- The result depends on whether `q : ℚ` happens to be an integer, in which case the result is
`.isInt ..` whereas otherwise it's `.isRat ..`. -/
def Result.isRat' {α : Q(Type u)} {x : Q($α)} (inst : Q(DivisionRing $α) := by assumption)
    (q : Rat) (n : Q(ℤ)) (d : Q(ℕ)) (proof : Q(IsRat $x $n $d)) : Result x :=
  if q.den = 1 then
    have proof : Q(IsRat $x $n (nat_lit 1)) := proof
    .isInt q(DivisionRing.toRing) n q.num q(IsRat.to_isInt $proof)
  else
    .isRat inst q n d proof

/-- Returns the rational number that is the result of `norm_num` evaluation, along with a proof
that the denominator is nonzero in the `isRat` case. -/
def Result.toRatNZ : Result e → Option (Rat × Option Expr)
  | .isBool .. => none
  | .isNat _ lit _ => some (lit.natLit!, none)
  | .isNegNat _ lit _ => some (-lit.natLit!, none)
  | .isRat _ q _ _ p => some (q, q(IsRat.den_nz $p))

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
    let some n := lit.natLit? | failure
    match n with
    | 0 => pure ⟨q(0 : $α), (q(Nat.cast_zero (R := $α)) : Expr)⟩
    | 1 => pure ⟨q(1 : $α), (q(Nat.cast_one (R := $α)) : Expr)⟩
    | k+2 =>
      let k : Q(ℕ) := mkRawNatLit k
      let _x : Q(Nat.AtLeastTwo $lit) :=
        (q(instNatAtLeastTwo (n := $k)) : Expr)
      let a' : Q($α) := q(OfNat.ofNat $lit)
      pure ⟨a', (q(Eq.refl $a') : Expr)⟩

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

/--
An extension for `norm_num`.
-/
structure NormNumExt where
  /-- The extension should be run in the `pre` phase when used as simp plugin. -/
  pre := true
  /-- The extension should be run in the `post` phase when used as simp plugin. -/
  post := true
  /-- Attempts to prove an expression is equal to some explicit number of the relevant type. -/
  eval {α : Q(Type u)} (e : Q($α)) : MetaM (Result e)
  /-- The name of the `norm_num` extension. -/
  name : Name := by exact decl_name%

/-- Read a `norm_num` extension from a declaration of the right type. -/
def mkNormNumExt (n : Name) : ImportM NormNumExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck NormNumExt opts ``NormNumExt n

/-- Each `norm_num` extension is labelled with a collection of patterns
which determine the expressions to which it should be applied. -/
abbrev Entry := Array (Array (DiscrTree.Key true)) × Name

/-- The state of the `norm_num` extension environment -/
structure NormNums where
  /-- The tree of `norm_num` extensions. -/
  tree   : DiscrTree NormNumExt true := {}
  /-- Erased `norm_num`s. -/
  erased  : PHashSet Name := {}
  deriving Inhabited

/-- Environment extensions for `norm_num` declarations -/
initialize normNumExt : ScopedEnvExtension Entry (Entry × NormNumExt) NormNums ←
  -- we only need this to deduplicate entries in the DiscrTree
  have : BEq NormNumExt := ⟨fun _ _ ↦ false⟩
  /- Insert `v : NormNumExt` into the tree `dt` on all key sequences given in `kss`. -/
  let insert kss v dt := kss.foldl (fun dt ks ↦ dt.insertCore ks v) dt
  registerScopedEnvExtension {
    mkInitial := pure {}
    ofOLeanEntry := fun _ e@(_, n) ↦ return (e, ← mkNormNumExt n)
    toOLeanEntry := (·.1)
    addEntry := fun { tree, erased } ((kss, n), ext) ↦
      { tree := insert kss ext tree, erased := erased.erase n }
  }

/-- Run each registered `norm_num` extension on an expression, returning a `NormNum.Result`. -/
def derive {α : Q(Type u)} (e : Q($α)) (post := false) : MetaM (Result e) := do
  if e.isNatLit then
    let lit : Q(ℕ) := e
    return .isNat (q(instAddMonoidWithOneNat) : Q(AddMonoidWithOne ℕ))
      lit (q(IsNat.raw_refl $lit) : Expr)
  profileitM Exception "norm_num" (← getOptions) do
    let s ← saveState
    let normNums := normNumExt.getState (← getEnv)
    let arr ← normNums.tree.getMatch e
    for ext in arr do
      if (bif post then ext.post else ext.pre) && ! normNums.erased.contains ext.name then
        try
          let new ← withReducibleAndInstances <| ext.eval e
          trace[Tactic.norm_num] "{ext.name}:\n{e} ==> {new}"
          return new
        catch err =>
          trace[Tactic.norm_num] "{e} failed: {err.toMessageData}"
          s.restore
    throwError "{e}: no norm_nums apply"

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℕ`, and a proof of `isNat e lit`. -/
def deriveNat' {α : Q(Type u)} (e : Q($α)) :
    MetaM ((_inst : Q(AddMonoidWithOne $α)) × (lit : Q(ℕ)) × Q(IsNat $e $lit)) := do
  let .isNat inst lit proof ← derive e | failure
  pure ⟨inst, lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℕ`, and a proof of `isNat e lit`. -/
def deriveNat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(AddMonoidWithOne $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℕ)) × Q(IsNat $e $lit)) := do
  let .isNat _ lit proof ← derive e | failure
  pure ⟨lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a typed expression `lit : ℤ`, and a proof of `IsInt e lit` in expression form. -/
def deriveInt {α : Q(Type u)} (e : Q($α))
    (_inst : Q(Ring $α) := by with_reducible assumption) :
    MetaM ((lit : Q(ℤ)) × Q(IsInt $e $lit)) := do
  let some ⟨_, lit, proof⟩ := (← derive e).toInt | failure
  pure ⟨lit, proof⟩

/-- Run each registered `norm_num` extension on a typed expression `e : α`,
returning a rational number, typed expressions `n : ℚ` and `d : ℚ` for the numerator and
denominator, and a proof of `IsRat e n d` in expression form. -/
def deriveRat {α : Q(Type u)} (e : Q($α))
    (_inst : Q(DivisionRing $α) := by with_reducible assumption) :
    MetaM (ℚ × (n : Q(ℤ)) × (d : Q(ℕ)) × Q(IsRat $e $n $d)) := do
  let some res := (← derive e).toRat' | failure
  pure res

/-- Extract the natural number `n` if the expression is of the form `OfNat.ofNat n`. -/
def isNatLit (e : Expr) : Option ℕ := do
  guard <| e.isAppOfArity ``OfNat.ofNat 3
  let .lit (.natVal lit) := e.appFn!.appArg! | none
  lit

/-- Extract the integer `i` if the expression is either a natural number literal
or the negation of one. -/
def isIntLit (e : Expr) : Option ℤ :=
  if e.isAppOfArity ``Neg.neg 3 then
    (- ·) <$> isNatLit e.appArg!
  else
    isNatLit e

/-- Extract the numerator `n : ℤ` and denominator `d : ℕ` if the expression is either
an integer literal, or the division of one integer literal by another. -/
def isRatLit (e : Expr) : Option ℚ := do
  if e.isAppOfArity ``Div.div 4 then
    let d ← isNatLit e.appArg!
    guard (d ≠ 1)
    let n ← isIntLit e.appFn!.appArg!
    let q := mkRat n d
    guard (q.den = d)
    pure q
  else
    isIntLit e

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

/-- Test if an expression represents an explicit number written in normal form. -/
def isNormalForm : Expr → Bool
  | .lit _ => true
  | .mdata _ e => isNormalForm e
  | e => (isRatLit e).isSome

/-- Run each registered `norm_num` extension on an expression,
returning a `Simp.Result`. -/
def eval (e : Expr) (post := false) : MetaM Simp.Result := do
  if isNormalForm e then return { expr := e }
  let ⟨_, _, e⟩ ← inferTypeQ' e
  (← derive e post).toSimpResult

/-- Erases a name marked `norm_num` by adding it to the state's `erased` field and
  removing it from the state's list of `Entry`s. -/
def NormNums.eraseCore (d : NormNums) (declName : Name) : NormNums :=
 { d with erased := d.erased.insert declName }

/--
  Erase a name marked as a `norm_num` attribute.

  Check that it does in fact have the `norm_num` attribute by making sure it names a `NormNumExt`
  found somewhere in the state's tree, and is not erased.
-/
def NormNums.erase [Monad m] [MonadError m] (d : NormNums) (declName : Name) : m NormNums := do
  unless d.tree.values.any (·.name == declName) && ! d.erased.contains declName
  do
    throwError "'{declName}' does not have [norm_num] attribute"
  return d.eraseCore declName

initialize registerBuiltinAttribute {
  name := `norm_num
  descr := "adds a norm_num extension"
  applicationTime := .afterCompilation
  add := fun declName stx kind ↦ match stx with
    | `(attr| norm_num $es,*) => do
      let env ← getEnv
      unless (env.getModuleIdxFor? declName).isNone do
        throwError "invalid attribute 'norm_num', declaration is in an imported module"
      if (IR.getSorryDep env declName).isSome then return -- ignore in progress definitions
      let ext ← mkNormNumExt declName
      let keys ← MetaM.run' <| es.getElems.mapM fun stx ↦ do
        let e ← TermElabM.run' <| withSaveInfoContext <| withAutoBoundImplicit <|
          withReader ({ · with ignoreTCFailures := true }) do
            let e ← elabTerm stx none
            let (_, _, e) ← lambdaMetaTelescope (← mkLambdaFVars (← getLCtx).getFVars e)
            return e
        DiscrTree.mkPath e
      normNumExt.add ((keys, declName), ext) kind
    | _ => throwUnsupportedSyntax
  erase := fun declName => do
    let s := normNumExt.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => normNumExt.modifyState env fun _ => s
}

/-- A simp plugin which calls `NormNum.eval`. -/
def tryNormNum? (post := false) (e : Expr) : SimpM (Option Simp.Step) := do
  try return some (.done (← eval e post))
  catch _ => return none

/--
Constructs a proof that the original expression is true
given a simp result which simplifies the target to `True`.
-/
def _root_.Lean.Meta.Simp.Result.ofTrue (r : Simp.Result) : MetaM (Option Expr) :=
  if r.expr.isConstOf ``True then
    some <$> match r.proof? with
    | some proof => mkOfEqTrue proof
    | none => pure (mkConst ``True.intro)
  else
    pure none

variable (ctx : Simp.Context) (useSimp := true) in
mutual
  /-- A discharger which calls `norm_num`. -/
  partial def discharge (e : Expr) : SimpM (Option Expr) := do (← deriveSimp e).ofTrue

  /-- A `Methods` implementation which calls `norm_num`. -/
  partial def methods : Simp.Methods :=
    if useSimp then {
      pre := fun e ↦ do
        Simp.andThen (← Simp.preDefault e discharge) tryNormNum?
      post := fun e ↦ do
        Simp.andThen (← Simp.postDefault e discharge) (tryNormNum? (post := true))
      discharge? := discharge
    } else {
      pre := fun e ↦ Simp.andThen (.visit { expr := e }) tryNormNum?
      post := fun e ↦ Simp.andThen (.visit { expr := e }) (tryNormNum? (post := true))
      discharge? := discharge
    }

  /-- Traverses the given expression using simp and normalises any numbers it finds. -/
  partial def deriveSimp (e : Expr) : MetaM Simp.Result :=
    (·.1) <$> Simp.main e ctx (methods := methods)
end

-- FIXME: had to inline a bunch of stuff from `simpGoal` here
/--
The core of `norm_num` as a tactic in `MetaM`.

* `g`: The goal to simplify
* `ctx`: The simp context, constructed by `mkSimpContext` and
  containing any additional simp rules we want to use
* `fvarIdsToSimp`: The selected set of hypotheses used in the location argument
* `simplifyTarget`: true if the target is selected in the location argument
* `useSimp`: true if we used `norm_num` instead of `norm_num1`
-/
def normNumAt (g : MVarId) (ctx : Simp.Context) (fvarIdsToSimp : Array FVarId)
    (simplifyTarget := true) (useSimp := true) :
    MetaM (Option (Array FVarId × MVarId)) := g.withContext do
  g.checkNotAssigned `norm_num
  let mut g := g
  let mut toAssert := #[]
  let mut replaced := #[]
  for fvarId in fvarIdsToSimp do
    let localDecl ← fvarId.getDecl
    let type ← instantiateMVars localDecl.type
    let ctx := { ctx with simpTheorems := ctx.simpTheorems.eraseTheorem (.fvar localDecl.fvarId) }
    let r ← deriveSimp ctx useSimp type
    match r.proof? with
    | some _ =>
      let some (value, type) ← applySimpResultToProp g (mkFVar fvarId) type r
        | return none
      toAssert := toAssert.push { userName := localDecl.userName, type, value }
    | none =>
      if r.expr.isConstOf ``False then
        g.assign (← mkFalseElim (← g.getType) (mkFVar fvarId))
        return none
      g ← g.replaceLocalDeclDefEq fvarId r.expr
      replaced := replaced.push fvarId
  if simplifyTarget then
    let res ← g.withContext do
      let target ← instantiateMVars (← g.getType)
      let r ← deriveSimp ctx useSimp target
      let some proof ← r.ofTrue
        | some <$> applySimpResultToTarget g target r
      g.assign proof
      pure none
    let some gNew := res | return none
    g := gNew
  let (fvarIdsNew, gNew) ← g.assertHypotheses toAssert
  let toClear := fvarIdsToSimp.filter fun fvarId ↦ !replaced.contains fvarId
  let gNew ← gNew.tryClearMany toClear
  return some (fvarIdsNew, gNew)

open Qq Lean Meta Elab Tactic Term

/-- Constructs a simp context from the simp argument syntax. -/
def getSimpContext (args : Syntax) (simpOnly := false) :
    TacticM Simp.Context := do
  let simpTheorems ←
    if simpOnly then simpOnlyBuiltins.foldlM (·.addConst ·) {} else getSimpTheorems
  let mut { ctx, starArg } ← elabSimpArgs args[0] (eraseLocal := false) (kind := .simp)
    { simpTheorems := #[simpTheorems], congrTheorems := ← getSimpCongrTheorems }
  unless starArg do return ctx
  let mut simpTheorems := ctx.simpTheorems
  for h in ← getPropHyps do
    unless simpTheorems.isErased (.fvar h) do
      simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
  pure { ctx with simpTheorems }

open Elab.Tactic in
/--
Elaborates a call to `norm_num only? [args]` or `norm_num1`.
* `args`: the `(simpArgs)?` syntax for simp arguments
* `loc`: the `(location)?` syntax for the optional location argument
* `simpOnly`: true if `only` was used in `norm_num`
* `useSimp`: false if `norm_num1` was used, in which case only the structural parts
  of `simp` will be used, not any of the post-processing that `simp only` does without lemmas
-/
-- FIXME: had to inline a bunch of stuff from `mkSimpContext` and `simpLocation` here
def elabNormNum (args : Syntax) (loc : Syntax)
    (simpOnly := false) (useSimp := true) : TacticM Unit := do
  let ctx ← getSimpContext args (!useSimp || simpOnly)
  let g ← getMainGoal
  let res ← match expandOptLocation loc with
  | .targets hyps simplifyTarget => normNumAt g ctx (← getFVarIds hyps) simplifyTarget useSimp
  | .wildcard => normNumAt g ctx (← g.getNondepPropHyps) (simplifyTarget := true) useSimp
  match res with
  | none => replaceMainGoal []
  | some (_, g) => replaceMainGoal [g]

end Meta.NormNum

namespace Tactic
open Lean.Parser.Tactic Meta.NormNum

/--
Normalize numerical expressions. Supports the operations `+` `-` `*` `/` `⁻¹` `^` and `%`
over numerical types such as `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` and some general algebraic types,
and can prove goals of the form `A = B`, `A ≠ B`, `A < B` and `A ≤ B`, where `A` and `B` are
numerical expressions. It also has a relatively simple primality prover.
-/
elab (name := normNum) "norm_num" only:&" only"? args:(simpArgs ?) loc:(location ?) : tactic =>
  elabNormNum args loc (simpOnly := only.isSome) (useSimp := true)

/-- Basic version of `norm_num` that does not call `simp`. -/
elab (name := normNum1) "norm_num1" loc:(location ?) : tactic =>
  elabNormNum mkNullNode loc (simpOnly := true) (useSimp := false)

open Lean Elab Tactic

@[inherit_doc normNum1] syntax (name := normNum1Conv) "norm_num1" : conv

/-- Elaborator for `norm_num1` conv tactic. -/
@[tactic normNum1Conv] def elabNormNum1Conv : Tactic := fun _ ↦ withMainContext do
  let ctx ← getSimpContext mkNullNode true
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := false))

@[inherit_doc normNum] syntax (name := normNumConv) "norm_num" &" only"? (simpArgs)? : conv

/-- Elaborator for `norm_num` conv tactic. -/
@[tactic normNumConv] def elabNormNumConv : Tactic := fun stx ↦ withMainContext do
  let ctx ← getSimpContext stx[2] !stx[1].isNone
  Conv.applySimpResult (← deriveSimp ctx (← instantiateMVars (← Conv.getLhs)) (useSimp := true))

/--
The basic usage is `#norm_num e`, where `e` is an expression,
which will print the `norm_num` form of `e`.

Syntax: `#norm_num` (`only`)? (`[` simp lemma list `]`)? `:`? expression

This accepts the same options as the `#simp` command.
You can specify additional simp lemmas as usual, for example using `#norm_num [f, g] : e`.
(The colon is optional but helpful for the parser.)
The `only` restricts `norm_num` to using only the provided lemmas, and so
`#norm_num only : e` behaves similarly to `norm_num1`.

Unlike `norm_num`, this command does not fail when no simplifications are made.

`#norm_num` understands local variables, so you can use them to introduce parameters.
-/
macro (name := normNumCmd) "#norm_num" o:(&" only")?
    args:(Parser.Tactic.simpArgs)? " :"? ppSpace e:term : command =>
  `(command| #conv norm_num $[only%$o]? $(args)? => $e)
