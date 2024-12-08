/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathlib.Lean.Expr.Basic
import Qq
import Mathlib.Order.Basic
import Mathlib.Util.Qq

/-!
# `Ineq` datatype

This file contains an enum `Ineq` (whose constructors are `eq`, `le`, `lt`), and operations
involving it. The type `Ineq` is one of the fundamental objects manipulated by the `linarith` and
`linear_combination` tactics.
-/

open Lean Elab Tactic Meta

namespace Mathlib

/-! ### Inequalities -/

/-- The three-element type `Ineq` is used to represent the strength of a comparison between
terms. -/
inductive Ineq : Type
  | eq | le | lt
deriving DecidableEq, Inhabited, Repr

namespace Ineq

/--
`max R1 R2` computes the strength of the sum of two inequalities. If `t1 R1 0` and `t2 R2 0`,
then `t1 + t2 (max R1 R2) 0`.
-/
def max : Ineq → Ineq → Ineq
  | lt, _ => lt
  | _, lt => lt
  | le, _ => le
  | _, le => le
  | eq, eq => eq

/-- `Ineq` is ordered `eq < le < lt`. -/
def cmp : Ineq → Ineq → Ordering
  | eq, eq => Ordering.eq
  | eq, _ => Ordering.lt
  | le, le => Ordering.eq
  | le, lt => Ordering.lt
  | lt, lt => Ordering.eq
  | _, _ => Ordering.gt

/-- Prints an `Ineq` as the corresponding infix symbol. -/
def toString : Ineq → String
  | eq => "="
  | le => "≤"
  | lt => "<"

instance : ToString Ineq := ⟨toString⟩

instance : ToFormat Ineq := ⟨fun i => Ineq.toString i⟩

end Mathlib.Ineq

/-


private inductive Mathlib.IneqQ' :
    Ineq → Type
  | lt' (h : Expr) : IneqQ' .lt
  | le' (h : Expr) : IneqQ' .le
  | eq' (h : Expr) : IneqQ' .eq

variable {u : Level}

/-- A version of `Ineq` that carries a proof` -/
def Mathlib.IneqQ {α : Q(Type u)} (inst : Q(PartialOrder $α)) (a b : Q($α)) :
    Ineq → Type := Mathlib.IneqQ'

def Mathlib.IneqQ.eq {α : Q(Type u)} (inst : Q(PartialOrder $α)) (a b : Q($α))
    (h : Q($a = $b)) : IneqQ inst a b .eq := .eq' h
def Mathlib.IneqQ.le {α : Q(Type u)} (inst : Q(PartialOrder $α)) (a b : Q($α))
    (h : Q($a ≤ $b)) : IneqQ inst a b .le := .le' h
def Mathlib.IneqQ.lt {α : Q(Type u)} (inst : Q(PartialOrder $α)) (a b : Q($α))
    (h : Q($a < $b)) : IneqQ inst a b .lt := .lt' h

-/

open scoped Qq
/-- A version of `Ineq` that carries a proof` -/
inductive Mathlib.IneqQ {u : Level} {α : Q(Type u)} (inst : Q(PartialOrder $α)) (a b : Q($α)) :
    Ineq → Type
  | eq (h : Q($a = $b)) : IneqQ inst a b .eq
  | le (h : Q($a ≤ $b)) : IneqQ inst a b .le
  | lt (h : Q($a < $b)) : IneqQ inst a b .lt

def Mathlib.IneqQ.raw {u : Level} {α : Q(Type u)} {inst : Q(PartialOrder $α)} {a b : Q($α)}
    {ineq}
    (h : Mathlib.IneqQ inst a b ineq) : Expr :=
  match h with
  | .eq h | .le h | .lt h => h

set_option linter.unusedVariables.funArgs false in
/-- Use this to deal with instance diamonds in the `inst` argument, after calling
`(assert|assume)InstancesCommute`. -/
def Mathlib.IneqQ.cast
    {u₁ u₂ : Level} {α₁ : Q(Type u₁)} {α₂ : Q(Type u₂)}
    {inst₁ : Q(PartialOrder $α₁)}
    {inst₂ : Q(PartialOrder $α₂)}
    {a₁ b₁ : Q($α₁)}
    {a₂ b₂ : Q($α₂)}
    {ineq : Ineq}
    (h : Mathlib.IneqQ inst₁ a₁ b₁ ineq)
    (hu : u₁ =QL u₂ := by first | exact .rfl | assumption)
    (hα : $α₁ =Q $α₂ := by first | exact .rfl | assumption)
    (hinst : $inst₁ =Q $inst₂ := by first | exact .rfl | assumption)
    (ha : $a₁ =Q $a₂ := by first | exact .rfl | assumption)
    (hb : $b₁ =Q $b₂ := by first | exact .rfl | assumption) :
    Mathlib.IneqQ inst₂ a₂ b₂ ineq :=
  match h with
  | .le h => .le q($h)
  | .eq h => .eq q($h)
  | .lt h => .lt q($h)

structure Mathlib.IneqResult {u : Level} (α : Q(Type u)) (inst : Q(PartialOrder $α)) : Type where
  ineq : Ineq
  a : Q($α)
  b : Q($α)
  pf : IneqQ inst a b ineq

/-- Use this to deal with instance diamonds in the `inst` argument, after calling
`(assert|assume)InstancesCommute`. -/
def Mathlib.IneqResult.cast
    {u₁ u₂ : Level} {α₁ : Q(Type u₁)} {α₂ : Q(Type u₂)}
    {inst₁ : Q(PartialOrder $α₁)}
    {inst₂ : Q(PartialOrder $α₂)}
    (hu : u₁ =QL u₂ := by first | exact .rfl | assumption)
    (hα : $α₁ =Q $α₂ := by first | exact .rfl | assumption)
    (hinst : $inst₁ =Q $inst₂ := by first | exact .rfl | assumption)
    (h : Mathlib.IneqResult α₁ inst₁):
    Mathlib.IneqResult α₂ inst₂ :=
  let ⟨ineq, a, b, h⟩ := h
  { ineq, a, b, pf := h.cast }

/-! ### Parsing inequalities -/

namespace Lean.Expr
open Mathlib

/-- Like `Lean.Expr.eq?`, but for `Qq`. -/
def eqQ? {P : Q(Prop)} (e : Q($P)) :
    MetaM <| Option <|
      (u : Level) × (α : Q(Sort u)) × (a b : Q($α)) × Q($a = $b) := do
  if let ~q(($a : $α) = $b) := P then
    return .some ⟨u_1, α, a, b, e⟩
  else
    return .none

/-- Like `Lean.Expr.le?`, but for `Qq`. -/
def leQ? {P : Q(Prop)} (e : Q($P)) :
    MetaM <| Option <|
      (u : Level) × (α : Q(Type u)) × (a b : Q($α)) × (_ : Q(LE $α)) × Q($a ≤ $b) := do
  if let ~q(@LE.le $α $inst $a $b) := P then
    return .some ⟨u_1, α, a, b, inst, q($e)⟩
  else
    return .none

/-- Like `Lean.Expr.lt?`, but for `Qq`. -/
def ltQ? {P : Q(Prop)} (e : Q($P)) :
    MetaM <| Option <|
      (u : Level) × (α : Q(Type u)) × (a b : Q($α)) × (_ : Q(LT $α)) × Q($a < $b) := do
  if let ~q(@LT.lt $α $inst $a $b) := P then
    return .some ⟨u_1, α, a, b, inst, q($e)⟩
  else
    return .none

/-- Given an expression `e`, parse it as a `=`, `≤` or `<`, and return this relation (as a
`Linarith.Ineq`) together with the type in which the (in)equality occurs and the two sides of the
(in)equality.

This function is more naturally in the `Option` monad, but it is convenient to put in `MetaM`
for compositionality.
-/
def ineqQ? {p : Q(Prop)} (e : Q($p)) :
    MetaM <| ((u : Level) × (α : Q(Type $u)) × (inst : _) × IneqResult α inst) := do
  if let .some ⟨.succ u, α, a, b, e⟩ ← eqQ? q($e) then
    let inst ← Qq.synthInstanceQ q(PartialOrder $α)
    pure ⟨u, α, inst, {a := a, b:= b, pf := .eq q($e)} ⟩
  else if let .some ⟨u, α, a, b, _iLE, e⟩ ← leQ? q($e) then
    let inst ← Qq.synthInstanceQ q(PartialOrder $α)
    assertInstancesCommute
    pure ⟨u, α, inst, {a := a, b:= b, pf := .le q($e)} ⟩
  else if let .some ⟨u, α, a, b, _iLT, e⟩ ← ltQ? q($e) then
    let inst ← Qq.synthInstanceQ q(PartialOrder $α)
    assertInstancesCommute
    pure ⟨u, α, inst, {a := a, b:= b, pf := .lt q($e)} ⟩
  else
    throwError "Not a comparison: {e}"

/-- Given an expression `e`, parse it as a `=`, `≤` or `<`, and return this relation (as a
`Linarith.Ineq`) together with the type in which the (in)equality occurs and the two sides of the
(in)equality.

This function is more naturally in the `Option` monad, but it is convenient to put in `MetaM`
for compositionality.
-/
def ineq? (e : Expr) : MetaM (Ineq × Expr × Expr × Expr) := do
  let e ← whnfR (← instantiateMVars e)
  match e.eq? with
  | some p => return (Ineq.eq, p)
  | none =>
  match e.le? with
  | some p => return (Ineq.le, p)
  | none =>
  match e.lt? with
  | some p => return (Ineq.lt, p)
  | none => throwError "Not a comparison: {e}"

/-- Given an expression `e`, parse it as a `=`, `≤` or `<`, or the negation of such, and return this
relation (as a `Linarith.Ineq`) together with the type in which the (in)equality occurs, the two
sides of the (in)equality, and a boolean flag indicating the presence or absence of the `¬`.

This function is more naturally in the `Option` monad, but it is convenient to put in `MetaM`
for compositionality.
-/
def ineqOrNotIneq? (e : Expr) : MetaM (Bool × Ineq × Expr × Expr × Expr) := do
  try
    return (true, ← e.ineq?)
  catch _ =>
    let some e' := e.not? | throwError "Not a comparison: {e}"
    return (false, ← e'.ineq?)

end Lean.Expr
