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
  -- | ofNat {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  --   {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (n : ℕ) {e : Q($A)}: ExSum A q($e : $A)
  | zero {w : Lean.Level} {A : Q(Type w)} (sA : Q(CommSemiring $A)) : ExSum  A q(((nat_lit 0).rawCast:$A))
  | one : ExSum q(ℕ) q((1 : ℕ))
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {v w: Lean.Level} {R : Q(Type v)} {A : Q(Type w)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)} {r : Q($R)}
    {a b : Q($A)} (sAlg : Q(Algebra $R $A)) :
    ExSum R q($r) → ExProd sA q($a) → ExSum A q($b) →
      ExSum A q($r • $a + $b)


def sℕ : Q(CommSemiring ℕ) := q(Nat.instCommSemiring)

def test {A : Type*} [CommSemiring A] : Algebra ℕ A := inferInstance

def ofProd {u : Level}  {A : Q(Type u)} (sA : Q(CommSemiring $A))
  {e : Q($A)} (prod : Ring.ExProd sA e) :=
  ExSum.add (q(Semiring.toNatAlgebra) : Q(Algebra ℕ $A)) .one prod (.zero sA)

-- #check ofProd
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
variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {e e' ea a a' : A} {r er : R}

theorem atom_pf (h : e = a):
    e = ((nat_lit 1).rawCast : R) • (a ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast) +
      (Nat.rawCast 0) := by
  simp [h]

theorem smul_zero_rawCast : r • ((nat_lit 0).rawCast : A) = (nat_lit 0).rawCast := by
  simp

theorem smul_congr (hr : r = er) (ha : a = ea) (h : er • ea = e'): r • a = e' := by
  rw [hr, ha, h]

theorem add_rawCast_zero : a + Nat.rawCast 0 = a := by
  simp

-- theorem test [Algebra R ℕ] : r • 1 =

end Proofs

-- variable {u v w : Level} {R : Q(Type u)} {A : Q(Type v)} (sA : Q(CommSemiring $A))
--   (sR : Q(CommSemiring $R)) (sAlg : Q(Algebra $R $A))

def evalAtom {v : Level}  {A : Q(Type v)} (sA : Q(CommSemiring $A)) (e : Q($A)) :
    AtomM (Result (ExSum A) e) := do
  let r ← (← read).evalAtom e
  have e' : Q($A) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ve' := ofProd sA <|
    (Ring.ExBase.atom i (e := a')).toProd (Ring.ExProd.mkNat Ring.sℕ 1).2
  pure ⟨_, ve', match r.proof? with
  | none =>
      have : $e =Q $a' := ⟨⟩
      (q(atom_pf rfl))
  | some (p : Q($e = $a')) => (q(atom_pf $p))⟩
/- Implementation taken from Tactic.Module -/

variable {u v : Level} {A : Q(Type v)} {R : Q(Type u)} in
variable {iA : Q(Semiring $A)}
  {u₁ : Level} {R₁ : Q(Type u₁)} (iR₁ : Q(CommSemiring $R₁)) (iRA₁ : Q(@Algebra $R₁ $A $iR₁ $iA))
  {u₂ : Level} {R₂ : Q(Type u₂)} (iR₂ : Q(CommSemiring $R₂)) (iRA₂ : Q(@Algebra $R₂ $A $iR₂ $iA)) in
def matchRingsSMul {r₁ : Q($R₁)} {r₂ : Q($R₂)} (vr₁ : ExSum R₁ r₁) (vr₂ : ExSum R₂ r₂) (a : Q($A)) :
    MetaM <|
      Σ u : Level, Σ R : Q(Type u), Σ iR : Q(CommSemiring $R),
      -- Σ v : Level, Σ R₂ : Q(Type v), Σ iR₂ : Q(CommSemiring $R₂),
      -- Σ _ : Q(@Algebra $R $R₂ $iR inferInstance),
      Σ _ : Q(@Algebra $R $A $iR $iA),
      Σ r' : Q($R),
        (ExSum R r' ×
        Q($r₁ • ($r₂ • $a) = $r' • $a)) := do
  if ← withReducible <| isDefEq R₁ R₂ then
  -- the case when `R₁ = R₂` is handled separately, so as not to require commutativity of that ring
    -- have : Type $u₁ =Q Type $u₂ := ⟨⟩
    -- have : $R₁ =Q $R₂ := ⟨⟩
    pure ⟨u₁, R₁, iR₁, iRA₁, q(sorry /- Want `r₁ * r₂` but type issues -/), sorry, q(sorry)⟩
  -- otherwise the "smaller" of the two rings must be commutative
  else try
    -- first try to exhibit `R₂` as an `R₁`-algebra
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $A)
    assumeInstancesCommute
    pure ⟨u₂, R₂, iR₂, iRA₂, q($r₁ • $r₂), sorry, q((smul_assoc $r₁ $r₂ $a).symm)⟩
  catch _ => try
    -- then if that fails, try to exhibit `R₁` as an `R₂`-algebra
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $A)
    assumeInstancesCommute
    pure ⟨u₁, R₁, iR₁, iRA₁, q($r₂ • $r₁), sorry,
      q(smul_algebra_smul_comm $r₂ $r₁ $a ▸ (smul_assoc $r₂ $r₁ $a).symm)⟩
  catch _ =>
    throwError "match_scalars failed: {R₁} is not an {R₂}-algebra and {R₂} is not an {R₁}-algebra"


partial def evalSMul {u v : Level} {R : Q(Type u)} {A : Q(Type v)} (sA : Q(CommSemiring $A))
  (sR : Q(CommSemiring $R)) (sRA : Q(Algebra $R $A)) {r : Q($R)} {a : Q($A)} (vr : ExSum R r)
    (va : ExSum A a) :
    MetaM <| Result (ExSum A) q($r • $a) := do
  Lean.Core.checkSystem decl_name%.toString
  match va with
  | .zero sA => do
    -- TODO: is this the right way to do this?
    assumeInstancesCommute
    return ⟨_, .zero sA, q(smul_zero_rawCast (r := $r) (A := $A))⟩
  | .one =>
    return ⟨_, .add sRA vr (.const (e := q(1)) 1 .none) (.zero sA) , q(add_rawCast_zero.symm)⟩
  | .add (R := S) (sR := sS) sSA vs va vt =>
    assumeInstancesCommute
    let ⟨et, vt, pt⟩ ← evalSMul sA sR sRA vr vt
    let x ← matchRingsSMul sS sSA sR sRA vs vr a
    let ⟨u₁, R₁, iR₁, sR₁A, r₁, vr₁, pr₁⟩ := x
    return ⟨_, .add sorry sorry va vt, sorry⟩

    -- throwError "smul add not implemented."

partial def eval {u : Lean.Level} {A : Q(Type u)} (sA : Q(CommSemiring $A))
    (e : Q($A)) : AtomM (Result (ExSum A) e) := Lean.withIncRecDepth do
  let els := do
    evalAtom sA e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HSMul.hSMul | ``SMul.smul => match e with
    | ~q(@SMul.smul $R _ $inst $r $a) =>
      have sR : Q(CommSemiring $R) := ← synthInstanceQ q(CommSemiring $R)
      have sAlg : Q(Algebra $R $A) := ← synthInstanceQ q(Algebra $R $A)
      assumeInstancesCommute
      let ⟨_, vr, pr⟩ ← eval sR r
      let ⟨_, va, pa⟩ ← eval sA a
      let ⟨ef, vf, pf⟩ ← evalSMul sA sR sAlg vr va
      return ⟨ef, vf, q(smul_congr $pr $pa $pf)⟩
    | ~q(@HSMul.hSMul $R _ _ $inst $r $a) =>
      throwError "hsmul not implemented"
    | _ => els
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

example (x : ℚ) :  x = (1 : ℤ) • x := by
  simp_rw [← SMul.smul_eq_hSMul]
  algebra
  sorry
