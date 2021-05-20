/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Elab.Tactic.Basic

class Numeric (α : Type _) where
  ofNat : Nat → α

instance Numeric.OfNat (α) [Numeric α] (n) : OfNat α n := ⟨Numeric.ofNat n⟩

-- TODO: replace this with the real thing
class Semiring (α : Type _) extends Add α, Mul α, Numeric α where
  add_assoc (a b c : α) : a + b + c = a + (b + c)
  add_zero (a : α) : a + 0 = a
  add_comm (a : α) : a + b = b + a
  mul_assoc (a b c : α) : a * b * c = a * (b * c)
  one_mul (a b c : α) : 1 * a = a
  mul_one (a b c : α) : a * 1 = a
  zero_mul (a b c : α) : 0 * a = a
  mul_zero (a b c : α) : a * 0 = a
  mul_add (a b c : α) : a * (b + c) = a * b + a * c
  add_mul (a b c : α) : (a + b) * c = a * c + b * c
  ofNat_add (a b : Nat) : ofNat (a + b) = ofNat a + ofNat b
  ofNat_mul (a b : Nat) : ofNat (a * b) = ofNat a * ofNat b

instance Semiring.OfNat (α) [Semiring α] (n) : OfNat α n := Numeric.OfNat _ _

namespace Lean
namespace Meta

def mkOfNatLit (u : Level) (α sα n : Expr) : Expr :=
  let inst := mkApp3 (mkConst `Semiring.OfNat [u]) α sα n
  mkApp3 (mkConst `OfNat.ofNat [u]) α n inst

namespace NormNum

theorem ofNat_add {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  a = OfNat.ofNat a' → b = OfNat.ofNat b' → a' + b' = c → a + b = OfNat.ofNat c
| _, _, _, _, _, rfl, rfl, rfl => (Semiring.ofNat_add _ _).symm

theorem ofNat_mul {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  a = OfNat.ofNat a' → b = OfNat.ofNat b' → a' * b' = c → a * b = OfNat.ofNat c
| _, _, _, _, _, rfl, rfl, rfl => (Semiring.ofNat_mul _ _).symm

partial def eval : Expr → MetaM (Expr × Expr)
| e => e.withApp fun f args => do
  if f.isConstOf `HAdd.hAdd then
    evalB `NormNum.ofNat_add (·+·) args
  else if f.isConstOf `HMul.hMul then
    evalB `NormNum.ofNat_mul (·*·) args
  else if f.isConstOf `OfNat.ofNat then pure (e, ← mkEqRefl e)
  else throwError "fail"
where
  evalB (name : Name) (f : Nat → Nat → Nat)
    (args : Array Expr) : MetaM (Expr × Expr) := do
    if let #[_, _, α, _, a, b] ← args then
      let Level.succ u _ ← getLevel α | throwError "fail"
      let sα ← synthInstance (mkApp (mkConst `Semiring [u]) α)
      let (a', pa) ← eval a
      let (b', pb) ← eval b
      let la := Expr.getRevArg! a' 1
      let some na ← la.natLit? | throwError "fail"
      let lb := Expr.getRevArg! b' 1
      let some nb ← lb.natLit? | throwError "fail"
      let lc := mkNatLit (f na nb)
      let c := mkOfNatLit u α sα lc
      pure (c, mkApp10 (mkConst name [u]) α sα a b la lb lc pa pb (← mkEqRefl lc))
    else throwError "fail"

end NormNum
end Meta

syntax (name := Parser.Tactic.normNum) "normNum" : tactic

open Meta Elab Tactic

@[tactic normNum] def Tactic.evalNormNum : Tactic := fun stx =>
  liftMetaTactic fun g => do
    let some (α, lhs, rhs) ← matchEq? (← getMVarType g) | throwError "fail"
    let (lhs2, p) ← NormNum.eval lhs
    unless ← isDefEq lhs2 rhs do throwError "fail"
    assignExprMVar g p
    pure []

end Lean

/-
variable (α) [Semiring α]
example : (2 + 2 + 2 : α) = 6 := by normNum
example : (0 + (2 + 3) + 7 : α) = 12 := by normNum
example : (70 * (33 + 2) : α) = 2450 := by normNum
-/
