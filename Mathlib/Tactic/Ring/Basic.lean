/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue, Anne Baanen
-/
module

public meta import Mathlib.Util.AtomM
public meta import Mathlib.Algebra.Order.Ring.Unbundled.Rat
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public meta import Mathlib.Tactic.NormNum.Result
public meta import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.Common

/-!
# `ring` tactic

A tactic for solving equations in commutative (semi)rings,
where the exponents can also contain variables.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .

More precisely, expressions of the following form are supported:
- constants (non-negative integers)
- variables
- coefficients (any rational number, embedded into the (semi)ring)
- addition of expressions
- multiplication of expressions (`a * b`)
- scalar multiplication of expressions (`n • a`; the multiplier must have type `ℕ`)
- exponentiation of expressions (the exponent must have type `ℕ`)
- subtraction and negation of expressions (if the base is a full ring)

The normalization procedure is implemented in `Mathlib.Tactic.Ring.Common`.

## Tags

ring, semiring, exponent, power
-/

@[expose] public meta section

assert_not_exists IsOrderedMonoid

namespace Mathlib.Tactic
namespace Ring

open Mathlib.Meta Qq NormNum Lean.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

open Lean (MetaM Expr mkRawNatLit)

universe u

/-- `CSLift α β` is a typeclass used by `ring` for lifting operations from `α`
(which is not a commutative semiring) into a commutative semiring `β` by using an injective map
`lift : α → β`. -/
class CSLift (α : Type u) (β : outParam (Type u)) where
  /-- `lift` is the "canonical injection" from `α` to `β` -/
  lift : α → β
  /-- `lift` is an injective function -/
  inj : Function.Injective lift

/-- `CSLiftVal a b` means that `b = lift a`. This is used by `ring` to construct an expression `b`
from the input expression `a`, and then run the usual ring algorithm on `b`. -/
class CSLiftVal {α} {β : outParam (Type u)} [CSLift α β] (a : α) (b : outParam β) : Prop where
  /-- The output value `b` is equal to the lift of `a`. This can be supplied by the default
  instance which sets `b := lift a`, but `ring` will treat this as an atom so it is more useful
  when there are other instances which distribute addition or multiplication. -/
  eq : b = CSLift.lift a

instance (priority := low) {α β} [CSLift α β] (a : α) : CSLiftVal a (CSLift.lift a) := ⟨rfl⟩

theorem of_lift {α β} [inst : CSLift α β] {a b : α} {a' b' : β}
    [h1 : CSLiftVal a a'] [h2 : CSLiftVal b b'] (h : a' = b') : a = b :=
  inst.2 <| by rwa [← h1.1, ← h2.1]

open Lean Parser.Tactic Elab Command Elab.Tactic

theorem of_eq {α} {a b c : α} (_ : (a : α) = c) (_ : b = c) : a = b := by subst_vars; rfl

/--
This is a routine which is used to clean up the unsolved subgoal
of a failed `ring1` application. It is overridden in `Mathlib/Tactic/Ring/RingNF.lean`
to apply the `ring_nf` simp set to the goal.
-/
initialize ringCleanupRef : IO.Ref (Expr → MetaM Expr) ← IO.mkRef pure

/-- Frontend of `ring1`: attempt to close a goal `g`, assuming it is an equation of semirings. -/
def proveEq (g : MVarId) : AtomM Unit := do
  let some (α, e₁, e₂) := (← whnfR <|← instantiateMVars <|← g.getType).eq?
    | throwError "ring failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  let sα ←
    try Except.ok <$> synthInstanceQ q(CommSemiring $α)
    catch e => pure (.error e)
  have e₁ : Q($α) := e₁; have e₂ : Q($α) := e₂
  let eq ← match sα with
  | .ok sα => ringCore sα e₁ e₂
  | .error e =>
    let β ← mkFreshExprMVarQ q(Type v)
    let e₁' ← mkFreshExprMVarQ q($β)
    let e₂' ← mkFreshExprMVarQ q($β)
    let (sβ, (pf : Q($e₁' = $e₂' → $e₁ = $e₂))) ← try
      let _l ← synthInstanceQ q(CSLift $α $β)
      let sβ ← synthInstanceQ q(CommSemiring $β)
      let _ ← synthInstanceQ q(CSLiftVal $e₁ $e₁')
      let _ ← synthInstanceQ q(CSLiftVal $e₂ $e₂')
      pure (sβ, q(of_lift (a := $e₁) (b := $e₂)))
    catch _ => throw e
    pure q($pf $(← ringCore sβ e₁' e₂'))
  g.assign eq
where
  /-- The core of `proveEq` takes expressions `e₁ e₂ : α` where `α` is a `CommSemiring`,
  and returns a proof that they are equal (or fails). -/
  ringCore {v : Level} {α : Q(Type v)} (sα : Q(CommSemiring $α))
      (e₁ e₂ : Q($α)) : AtomM Q($e₁ = $e₂) := do
    let c ← mkCache sα
    profileitM Exception "ring" (← getOptions) do
      let ⟨a, va, pa⟩ ← eval sα c e₁
      let ⟨b, vb, pb⟩ ← eval sα c e₂
      unless va.eq vb do
        let g ← mkFreshExprMVar (← (← ringCleanupRef.get) q($a = $b))
        throwError "ring failed, ring expressions not equal\n{g.mvarId!}"
      have : $a =Q $b := ⟨⟩
      return q(of_eq $pa $pb)

/--
`ring1` solves the goal when it is an equality in *commutative* (semi)rings,
allowing variables in the exponent.

This version of `ring` fails if the target is not an equality.

* `ring1!` uses a more aggressive reducibility setting to determine equality of atoms.
-/
elab (name := ring1) "ring1" tk:"!"? : tactic => liftMetaMAtMain fun g ↦ do
  AtomM.run (if tk.isSome then .default else .reducible) (proveEq g)

@[tactic_alt ring1] macro "ring1!" : tactic => `(tactic| ring1 !)

end Ring

end Mathlib.Tactic
