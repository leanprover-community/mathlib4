/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Tactic.Echelon.Core

public meta import Mathlib.Util.Qq

public meta import Mathlib.Tactic.NormNum.Basic

/-!
# The rational model for the Bareiss elimination

The rational model of a ring: entries evaluate to rational numerals via `norm_num`,
denominators are cleared by row scaling, and the elimination runs on integer values. It
is the fallback model the tactic uses when no ring-specific model matches the ring.
-/

public meta section

open Lean Meta Qq

namespace Mathlib.Tactic.Echelon

/-- Data-only evaluation of a matrix entry to its rational value via `norm_num`.
Fraction values are accepted only in characteristic zero. -/
def evalEntry (charZero : Bool) (e : Expr) : MetaM Rat := do
  unless charZero do
    let stripped := match_expr e with
      | Neg.neg _ _ a => a
      | _ => e
    if stripped.isAppOf ``HDiv.hDiv then
      throwError "the rational model supports division entries only in characteristic \
        zero{indentExpr e}"
  let ⟨_, _, eQ⟩ ← inferTypeQ' e
  let r ← try some <$> Meta.NormNum.derive eQ catch _ => pure none
  let some v := r.bind (·.toRat)
    | throwError "the entry does not evaluate to a rational numeral{indentExpr e}"
  unless v.den == 1 || charZero do
    throwError "the rational model supports division entries only in characteristic \
      zero{indentExpr e}"
  return v

/-- Scale each row by the lcm of its denominators to clear them. Returns the integer
matrix together with the row scales, which are later folded back into `L`. -/
def scaleRowsIntegral (ratRows : Array (Array Rat)) : Array (Array Int) × Array Nat :=
  let scales : Array Nat := ratRows.map fun row => row.foldl (fun l v => Nat.lcm l v.den) 1
  (((ratRows.zip scales).map fun (row, s) => row.map fun v => (mkRat s 1 * v).num), scales)

/-- Build the numeral of an integer in `R`: `mkNumeral` on the absolute value, negated if
`i` is negative. -/
def mkIntNumeral {u : Level} (R : Q(Type u)) (i : Int) : MetaM Q($R) := do
  let n ← mkNumeral R i.natAbs
  have n : Q($R) := n
  if i < 0 then
    let _ ← synthInstanceQ q(Neg $R)
    return q(-$n)
  else
    return n

/-- Whether the integer value `v` is zero in `R`, by reducing the `Decidable` instance of
`(v : R) = 0` in the kernel, matching the semantics of the final certificate check. -/
def isZeroInRing {u : Level} (R : Q(Type u)) (v : Int) : MetaM Bool := do
  if v == 0 then return true
  -- MetaM caches the synthesised instances (including failures), so these are fine.
  let _instCast ← synthInstanceQ q(IntCast $R)
  let _instZero ← synthInstanceQ q(Zero $R)
  have vE : Q(Int) := mkIntLitQ v
  let eq : Q(Prop) := q((Int.cast $vE : $R) = 0)
  /- this instance is synthesised for every value which is repeated.
    technically it's possible to synthesise a DecidableEq instance once and then use it
    for all checks, but there can be rings where eq is only partially decidable (for 0 only).
    The cost here is also negligible (~1%) compared to the kernel check itself.
  -/
  let some inst ← synthInstance? q(Decidable $eq)
    | throwError "equality with zero in the element type is not decidable{indentExpr R}"
  if let .ok r := Kernel.whnf (← getEnv) (← getLCtx) inst then
    if r.isAppOf ``Decidable.isTrue then return true
    if r.isAppOf ``Decidable.isFalse then return false
  throwError "equality in the element type does not reduce in the kernel{indentExpr R}"

/-- The rational model of a ring: entries evaluate to rational numerals, denominators
are cleared by row scaling, and the elimination runs on integer values. It applies to
every ring, as the fallback model. -/
def ratProducer (R : Expr) : MetaM Producer := do
  let u ← getDecLevel R
  have R : Q(Type u) := R
  let charZero ← do
    match ← trySynthInstanceQ q(AddMonoidWithOne $R) with
    | .some _amo => pure (← trySynthInstanceQ q(CharZero $R)).toOption.isSome
    | _ => pure false
  let ops : RingOps Int := {
    zero := 0
    one := 1
    mul := (· * ·)
    sub := (· - ·)
    divExact := (· / ·)
    isZero := if charZero then fun v => pure (v == 0) else isZeroInRing R }
  let prepare (entries : Array (Array Expr)) :
      MetaM (Array (Array Int) × (BareissData Int → BareissData Int)) := do
    let ratRows ← entries.mapM (·.mapM (evalEntry charZero))
    let (values, scales) := scaleRowsIntegral ratRows
    return (values, foldScales ops (scales.map Int.ofNat))
  return mkProducer ops prepare (mkIntNumeral R)

end Mathlib.Tactic.Echelon
