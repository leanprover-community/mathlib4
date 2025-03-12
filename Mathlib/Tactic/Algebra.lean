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

/-
QUESTIONS:

How does one normalize e.g. (3 + n : ℕ) • (4/3 : ℚ) • (x^2 : ℝ)

what happens to the constants??

options:
don't do recursive normalization (you will run into performance problems, but maybe good enough)

expand out additions on the LHS too?

-/

section ExSum

set_option linter.style.longLine false

open Ring in
/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum : ∀ {v: Lean.Level} (A : Q(Type v)), (e : Q($A)) → Type
  | ofNat {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
    {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (n : ℕ) {e : Q($A)}: ExSum A q($e : $A)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {v w: Lean.Level} {R : Q(Type v)} {A : Q(Type w)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)} {r : Q($R)}
    {a b : Q($A)} (sAlg : Q(Algebra $R $A)) :
    ExSum R q($r) → ExProd sA q($a) → ExSum A q($b) →
      ExSum A q($r • $a + $b)


def test {A : Type*} [CommSemiring A] : Algebra ℕ A := inferInstance

def ofProd {u v : Level} {R : Q(Type v)} {A : Q(Type u)} (sR : Q(CommSemiring $R)) (sA : Q(CommSemiring $A))
  (sAlg : Q(Algebra $R $A)) {e : Q($A)} (prod : Ring.ExProd sA e) :
    ExSum A q(((nat_lit 1).rawCast : $R) • $e + (nat_lit 0).rawCast) :=
  .add sAlg (.ofNat q(Semiring.toNatAlgebra : Algebra ℕ $R) 1) prod (.ofNat sAlg 0)

#check ofProd
end ExSum



-- def mkAtom {u : Level} {A : Q(Type u)} (sA : Q(CommRing $A)) {e : Q($A)} : ExSum q((1 : ℕ) • $e + 0) :=
--   let ve' := (Ring.ExBase.atom i (e := a')).toProd (ExProd.mkNat sℕ 1).2 |>.toSum
--   .add  sorry sorry (.ofNat 1) () sorry

structure Result {u : Lean.Level} {A : Q(Type u)} (E : Q($A) → Type) (e : Q($A)) where
  /-- The normalized result. -/
  expr : Q($A)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

section Proofs
variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {e a a' : A} {r : R}

theorem atom_pf (h : e = a):
    e = ((nat_lit 1).rawCast : R) • (a ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast) +
      (Nat.rawCast 0) := by
  simp [h]

end Proofs

variable {u v w : Level} {R : Q(Type u)} {A : Q(Type v)} (sA : Q(CommSemiring $A))
  (sR : Q(CommSemiring $R)) (sAlg : Q(Algebra $R $A))

def evalAtom (sA : Q(CommSemiring $A)) (e : Q($A)) : AtomM (Result (ExSum A) e) := do
  let r ← (← read).evalAtom e
  have e' : Q($A) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ve' := ofProd Ring.sℕ sA q(inferInstance) <|
    (Ring.ExBase.atom i (e := a')).toProd (Ring.ExProd.mkNat Ring.sℕ 1).2
  pure ⟨_, ve', match r.proof? with
  | none =>
      have : $e =Q $a' := ⟨⟩
      (q(atom_pf rfl))
  | some (p : Q($e = $a')) => (q(atom_pf $p))⟩


partial def evalSMul {r : Q($R)} {a : Q($A)} (vr : ExSum R r) (va : ExSum A a) :
    Lean.Core.CoreM <| Result (ExSum A) q($r • $a) := do
  Lean.Core.checkSystem decl_name%.toString
  match va with
  | .ofNat _ _ => sorry
  | .add .. => sorry

partial def eval {u : Lean.Level} {A : Q(Type u)} (sA : Q(CommSemiring $A))
    (e : Q($A)) : AtomM (Result (ExSum A) e) := Lean.withIncRecDepth do
  let els := do
    evalAtom sA e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HSMul.hSMul | ``SMul.smul => match e with
    | ~q(@SMul.smul $R _ $inst $r $a) =>
      have sR : Q(CommSemiring $R) := ← synthInstanceQ q(CommSemiring $R)
      let ⟨_, vr, pr⟩ ← eval sR r
      let ⟨_, va, pa⟩ ← eval sA a
      let res ← evalSMul sR sA vr va
      sorry
  | ``HAdd.hAdd | ``Add.add => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval sA a
      let ⟨_, vb, pb⟩ ← eval sA b
      throwError ""
      -- let ⟨c, vc, p⟩ ← evalAdd sα va vb
      -- pure ⟨c, vc, (q(add_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | _ =>
    els

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

theorem eq_congr {R : Type*} {a b a' b' : R} (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  subst ha hb
  exact h

def normalize (goal : MVarId) : AtomM MVarId := do
  -- let goal ← try getMainGoal catch
  --   | _ => return
  let some (A, e₁, e₂) :=
    (← whnfR <|← instantiateMVars <|← goal.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType A) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr A}"
  have A : Q(Type v) := A
  have sA : Q(CommSemiring $A) := ← synthInstanceQ q(CommSemiring $A)
  have e₁ : Q($A) := e₁
  have e₂ : Q($A) := e₂
  let (⟨a, exa, pa⟩ : Result (ExSum A) e₁) ← eval sA e₁
  let (⟨b, exb, pb⟩ : Result (ExSum A) e₂) ← eval sA e₂
  let g' ← mkFreshExprMVarQ q($a = $b)
  goal.assign q(eq_congr $pa $pb $g' : $e₁ = $e₂)
  -- if ← isDefEq a b then
    -- have : $a =Q $b := ⟨⟩
    -- g'.mvarId!.assign (q(rfl : $a = $b) : Expr)
    return g'.mvarId!
  -- else throwError "algebra failed to normalize expression."
  -- let l ← ExSum.eq_exSum g'.mvarId! a b exa exb
  -- Tactic.pushGoals l
  /- TODO: we probably want to do some sort of normalization of intermediate expressions.
    `norm_num` does not seem set up to do this very well. Much of the work is actually done by
    `simp`, namely `a+0 -> a` and `a*1 -> a`. -/
  -- for g in l do
  --   let l ← evalTacticAt (← `(tactic| norm_num)) g
  --   Tactic.pushGoals l
    -- NormNum.normNumAt g (← getSimpContext)

elab (name := algebra) "algebra" : tactic =>
  withMainContext do
    let g ← getMainGoal
    let g ← AtomM.run .default (normalize g)
    Tactic.pushGoal g



end Mathlib.Tactic.Algebra

example (x : ℚ) : x = (1 : ℤ) • x := by
  algebra
  sorry
