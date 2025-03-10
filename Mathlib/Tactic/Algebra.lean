/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Tactic.Module

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List Mathlib.Tactic.Module

namespace Mathlib.Tactic.Algebra

open Mathlib.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

-- /-- This definition is copied from Mathlib.Tactic.Module.NF --
--   perhaps we should just reuse that code. -/
-- def NF (R : Type*) (M : Type*) := List (R × M)

section ExSum

set_option linter.style.longLine false
open Ring in
/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum : ∀ {v: Lean.Level} {A : Q(Type v)}, (e : Q($A)) → Type
  | ofNat {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} {sAlg : Q(CommSemiring $A)} (n : ℕ): ExSum q($n : $A)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {u v w: Lean.Level} {R₀ : Q(Type u)} {R₁ : Q(Type v)} {A : Q(Type w)}
    {sR₀ : Q(CommSemiring $R₀)} {sR₁ : Q(CommSemiring $R₁)} {sA : Q(CommSemiring $A)} {r : Q($R₁)}
    {a b : Q($A)} {sAlg₀ : Q(Algebra $R₀ $R₁)} {sAlg₁ : Q(Algebra $R₁ $A)} (sAlg : Q(Algebra $R₀ $A))
      (sTower : Q(IsScalarTower $R₀ $R₁ $A)) :
    ExSum q($r) → ExProd sA q($a) → ExSum q($b) →
      ExSum q($r • $a + $b)

end ExSum

structure Result {u : Lean.Level} {A : Q(Type u)} (E : Q($A) → Type) (e : Q($A)) where
  /-- The normalized result. -/
  expr : Q($A)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

partial def eval {u : Lean.Level} {α : Q(Type u)} (sα : Q(CommSemiring $α))
    (e : Q($α)) : MetaM (Result (u := u) (ExSum ) e) := Lean.withIncRecDepth do
  let els : MetaM (Result (u := u) ExSum e) := do
    throwError m!"poly failed : unsupported expression : {e}"
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HAdd.hAdd | ``Add.add => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval sα a
      let ⟨_, vb, pb⟩ ← eval sα b
      sorry
      -- let ⟨c, vc, p⟩ ← evalAdd sα va vb
      -- pure ⟨c, vc, (q(add_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | _ => els

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

def normalize : TacticM Unit := withMainContext do
  let goal ← try getMainGoal catch
    | _ => return
  let some (α, e₁, e₂) :=
    (← whnfR <|← instantiateMVars <|← goal.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType α) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr α}"
  have α : Q(Type v) := α
  have sα : Q(CommSemiring $α) := ← synthInstanceQ q(CommSemiring $α)
  let ⟨a, exa, pa⟩ ← eval sα e₁
  let ⟨b, exb, pb⟩ ← eval sα e₂
  -- let g' ← mkFreshExprMVarQ q($a = $b)
  -- goal.assign q(eq_congr $pa $pb $g' : $e₁ = $e₂)
  -- let l ← ExSum.eq_exSum g'.mvarId! a b exa exb
  -- Tactic.pushGoals l
  /- TODO: we probably want to do some sort of normalization of intermediate expressions.
    `norm_num` does not seem set up to do this very well. Much of the work is actually done by
    `simp`, namely `a+0 -> a` and `a*1 -> a`. -/
  -- for g in l do
  --   let l ← evalTacticAt (← `(tactic| norm_num)) g
  --   Tactic.pushGoals l
    -- NormNum.normNumAt g (← getSimpContext)

elab (name := poly) "poly" : tactic => normalize


end Mathlib.Tactic.Algebra
