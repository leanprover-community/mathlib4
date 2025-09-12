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

Comments:

To implement `smul` need `mul` to handle the case where the two scalar rings are equal
To implement `mul` need `smul` to handle $(r₁ • s) * (r₂ • s') = (r₁ • r₂) • (s * s'), so is this
one big mutually inductive family?

Also need `add` to implement `mul` properly, so some work to be done.

There's a problem in `matchRingsSMul` when the two rings are defeq. I don't think there is a great
way to cast one of the ExProds to the other.
-/

section ExSum

set_option linter.style.longLine false


open Ring in
mutual

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum : ∀ {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {_ : Q(CommSemiring $R)}
  {_ : Q(CommSemiring $A)} (_ : Q(Algebra $R $A)), (a : Q($A)) → Type
  -- | unsafeCast {u v : Lean.Level} {A : Q(Type u)} (B : Q(Type v))
  --   {a : Q($A)} (va : ExSum A a) : ExSum q($B) (q($a):)
  | zero {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)}
      {sR : Q(CommSemiring $R)}
      {sA : Q(CommSemiring $A)}
      (sAlg : Q(Algebra $R $A)) : ExSum q($sAlg) q(0:$A)
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {v w: Lean.Level} {R : Q(Type v)} {A : Q(Type w)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)} {r : Q($R)}
    {a b : Q($A)} (sAlg : Q(Algebra $R $A)) :
    Ring.ExSum q($sR) q($r) → Ring.ExProd q($sA) q($a) → ExSum q($sAlg) q($b) →
      ExSum q($sAlg) q($r • $a + $b)

end

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A))

def one : Ring.ExSum q($sA) q(1 + 0 : $A) :=
  .add (.const (e := q(1 : $A)) 1 none) .zero

namespace ExSum

end ExSum
end ExSum

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


lemma mul_natCast_zero {R : Type*} [CommSemiring R] (r : R):
    r * (Nat.rawCast 0 : R) = Nat.rawCast 0 := by
  simp

class LawfulHMul (R₁ R₂ : Type*) [CommSemiring R₁] [CommSemiring R₂]  [HMul R₁ R₂ R₁] where
  mul_zero : ∀ r₁ : R₁, r₁ * (0 : R₂) = 0
  zero_mul : ∀ r₂ : R₂, (0 : R₁) * r₂ = 0
  mul_one : ∀ r₁ : R₁, r₁ * (1 : R₂) = r₁
  cast : R₁ → R₂
  cast_mul : ∀ r₁ : R₁, ∀ r₂ : R₂, cast (r₁ * r₂) = cast r₁ * r₂
  cast_one : cast 1 = 1
  cast_zero : cast 0 = 0

attribute [local simp] LawfulHMul.mul_zero LawfulHMul.zero_mul LawfulHMul.cast_mul
  LawfulHMul.cast_one LawfulHMul.cast_zero

-- theorem test [Algebra R ℕ] : r • 1 =

lemma hmul_zero_natCast {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₁ : R₁):
  r₁ * (Nat.rawCast 0 : R₂) = Nat.rawCast 0 := by
  simp [LawfulHMul.mul_zero]

lemma hmul_cast_one_mul {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₂ : R₂) :
    (LawfulHMul.cast ((1:R₁) * r₂) : R₂) = (1 : ℕ) •  r₂ + (Nat.rawCast 0:R₂) := by
  simp

lemma hmul_cast_zero_mul {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₂ : R₂) :
    (LawfulHMul.cast ((Nat.rawCast 0:R₁) * r₂) : R₂) = (Nat.rawCast 0:R₂) := by
  simp

local instance {R : Type*} [CommSemiring R] : LawfulHMul R R where
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_one := mul_one
  cast := id
  cast_mul := fun _ _ ↦ rfl
  cast_one := rfl
  cast_zero := rfl

end Proofs

-- variable {u v w : Level} {R : Q(Type u)} {A : Q(Type v)} (sA : Q(CommSemiring $A))
--   (sR : Q(CommSemiring $R)) (sAlg : Q(Algebra $R $A))

variable {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} {sR : Q(CommSemiring $R)}
  {sA : Q(CommSemiring $A)} (sAlg : Q(Algebra $R $A)) (a : Q($A))

def evalAtom :
    AtomM (Result (ExSum q($sAlg)) q($a)) := do
  let r ← (← read).evalAtom a
  have e' : Q($A) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ve' : ExSum _ _ := ExSum.add sAlg (one (sA := q($sR)))
    ((Ring.ExBase.atom i (e := a')).toProd (Ring.ExProd.mkNat Ring.sℕ 1).2) (.zero sAlg)
  pure ⟨_, ve', q(sorry)

  -- match r.proof? with
  -- | none =>
  --     have : $e =Q $a' := ⟨⟩
  --     (q(atom_pf rfl))
  -- | some (p : Q($e = $a')) => (q(atom_pf $p))

  ⟩
/- Implementation taken from Tactic.Module -/

-- TODO: decide if this is a good idea globally in
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60MonadLift.20Option.20.28OptionT.20m.29.60/near/469097834
private local instance {m : Type* → Type*} [Pure m] : MonadLift Option (OptionT m) where
  monadLift f := .mk <| pure f


partial def eval {u v : Lean.Level} {R : Q(Type u)} {A : Q(Type v)} (sR : Q(CommSemiring $R))
    (sA : Q(CommSemiring $A)) (sAlg : Q(Algebra $R $A)) (e : Q($A)) :
    AtomM (Result (ExSum sAlg) e) := Lean.withIncRecDepth do
  let els := do
    evalAtom sAlg e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HSMul.hSMul | ``SMul.smul => match e with
    | ~q(@SMul.smul $R _ $inst $r $a) =>
      throwError "smul not implemented"
      -- have sR : Q(CommSemiring $R) := ← synthInstanceQ q(CommSemiring $R)
      -- have sAlg : Q(Algebra $R $A) := ← synthInstanceQ q(Algebra $R $A)
      -- assumeInstancesCommute
      -- let ⟨_, vr, pr⟩ ← eval sR r
      -- let ⟨_, va, pa⟩ ← eval sA a
      -- let ⟨ef, vf, pf⟩ ← evalSMul sA sR sAlg (.sum vr) va
      -- return ⟨ef, vf, q(smul_congr $pr $pa $pf)⟩

    | ~q(@HSMul.hSMul $R _ _ $inst $r $a) =>
      throwError "hsmul not implemented"
    | _ => els
  | ``HAdd.hAdd | ``Add.add => match e with
    | ~q($a + $b) =>
      throwError "add not implemented"

      -- let ⟨_, va, pa⟩ ← eval sA a
      -- let ⟨_, vb, pb⟩ ← eval sA b
      -- let ⟨_, vab, pab⟩ ← evalAdd sA va vb
      -- return ⟨_, vab, q(sorry)⟩

    | _ => els
  | ``HMul.hMul | ``Mul.mul => match e with
    | ~q($a * $b) =>
      throwError "mul not implemented"

      -- let ⟨_, va, pa⟩ ← eval sA a
      -- let ⟨_, vb, pb⟩ ← eval sA b
      -- let ⟨_, vab, pab⟩ ← evalMul sA va vb
      -- return ⟨_, vab, q(sorry)⟩

    | _ =>
      els
  | _ =>
    els

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

theorem eq_congr {R : Type*} {a b a' b' : R} (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  subst ha hb
  exact h

def normalize (goal : MVarId) {u v : Lean.Level} (R : Q(Type u)) (A : Q(Type v)) : AtomM MVarId := do
  -- let goal ← try getMainGoal catch
  --   | _ => return
  let some (A', e₁, e₂) :=
    (← whnfR <|← instantiateMVars <|← goal.getType).eq?
    | throwError "algebra failed: not an equality"
  IO.println s!"A' = {← ppExpr A'}"
  IO.println s!"A = {← ppExpr A}"
  guard (←isDefEq A A')
  have sA : Q(CommSemiring $A) := ← synthInstanceQ q(CommSemiring $A)
  have sR : Q(CommSemiring $R) := ← synthInstanceQ q(CommSemiring $R)
  have sAlg : Q(Algebra $R $A) := ← synthInstanceQ q(Algebra $R $A)
  IO.println "synthed"
  have e₁ : Q($A) := e₁
  have e₂ : Q($A) := e₂
  IO.println "test"
  let (⟨a, exa, pa⟩ : Result (ExSum sAlg) e₁) ← eval sR sA sAlg e₁
  let (⟨b, exb, pb⟩ : Result (ExSum sAlg) e₂) ← eval sR sA sAlg e₂

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


def inferLevelQ (e : Expr) : MetaM (Σ u : Lean.Level, Q(Type u)) := do
  let .sort u ← whnf (← inferType e) | throwError "not a type{indentExpr e}"
  let some v := (← instantiateLevelMVars u).dec | throwError "not a Type{indentExpr e}"
  return ⟨v, e⟩

elab (name := algebra) "algebra " R:term ", " A:term : tactic =>
  withMainContext do
    let ⟨u, R⟩ ← inferLevelQ (← elabTerm R none)
    let ⟨v, A⟩ ← inferLevelQ (← elabTerm A none)
    IO.println s!"Rings are {← ppExpr R} : Type {u} and {← ppExpr A} : Type {v}"

    let g ← getMainGoal
    let g ← AtomM.run .default (normalize g R A)
    Tactic.pushGoal g


example {x : ℚ} {y : ℤ} : y • x + (1:ℤ) • x = (1 + y) • x := by
  algebra ℕ, ℚ
  trivial

example {S R A : Type*} [CommSemiring S] [CommSemiring R] [CommSemiring A] [Algebra S R]
    [Algebra R A] [Algebra S A] [IsScalarTower S R A] {r : R} {s : S} {a₁ a₂ : A} :
    (s • a₁) * (r • a₂) = (s • r) • (a₁ * a₂) := by
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_assoc]
  rw [smul_comm]


end Mathlib.Tactic.Algebra


example (x : ℚ) :  x = (1 : ℤ) • x := by
  simp_rw [← SMul.smul_eq_hSMul]
  algebra
  match_scalars <;> simp

example (x : ℚ) : x = 1 := by
  algebra ℕ, ℚ
  sorry

-- BUG: ExProd.one doesn't match with the empty product in sums.
example (x : ℚ) : x + x + x  = 3 * x := by
  algebra ℕ, ℚ
  sorry

example (x : ℚ) : (x + x) + (x + x)  = 4 * x := by
  algebra ℕ, ℚ
  -- simp
  simp only [Nat.rawCast, Nat.cast_one, pow_one, Nat.cast_ofNat, one_smul, Nat.cast_zero, add_zero,
    mul_one]

example (x y : ℚ) : (x + y)*(x+y) = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra ℕ, ℚ
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]

--   sorry

--   -- match_scalars <;> simp

example (x y : ℚ) : (x+y)*x = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]
  sorry

example (x y : ℚ) : (x+y)*y  = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]
  sorry
