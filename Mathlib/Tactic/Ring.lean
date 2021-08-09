/-
Copyright (c) 2021 Aurélien Saue. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Saue
-/


import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum

open Lean Parser.Tactic Elab Command Elab.Tactic Meta

open Expr in
private def getAppFnAndArgsAux : Expr → Array Expr → Nat → Option (Name × Array Expr)
  | app f a _,   as, i => getAppFnAndArgsAux f (as.set! i a) (i-1)
  | const n _ _, as, i => some (n,as)
  | _,           as, _ => none

def Lean.Expr.getAppFnAndArgs (e : Expr) : Option (Name × Array Expr) :=
  let dummy := mkSort levelZero
  let nargs := e.getAppNumArgs
  getAppFnAndArgsAux e (mkArray nargs dummy) (nargs-1)

/--
  Return true if `e` is one of the following
  - A nat literal (numeral)
  - `Nat.zero`
  - `Nat.succ x` where `isNumeral x`
  - `OfNat.ofNat _ x _` where `isNumeral x` -/
partial def numeral? (e : Expr) : Option Nat :=
  if let some n := e.natLit? then n
  else
    let f := e.getAppFn
    if !f.isConst then none
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then (numeral? e.appArg!).map Nat.succ
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then numeral? (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then some 0
      else none

def spaces (n : Nat) : String := do
  let mut res := ""
  for i in [:n] do
    res := res ++ " "
  return res

open Expr in
def rip (k : Nat)(e: Expr) : IO Unit := do
  IO.print (spaces k)
  match e with
  | bvar x _        => println! "bvar {x}"
  | fvar x _        => println! "fvar {x}"
  | mvar _ _        => println! "mvar"
  | Expr.sort u _   => println! "sort {u}"
  | const n _ _     => println! "const {n}"
  | app a b _       =>
    println! "app"
    rip (k+2) a
    IO.print (spaces k)
    println! "to"
    rip (k+2) b
  | lam x ty e _    => do
    println! "lam {x}"
    rip (k+2) ty
    rip (k+2) e
  | forallE x ty e d => do
    println! "forallE {x} {d.hash}"
    rip (k+2) ty
    rip (k+2) e
  | letE _ _ _ _ _  => println! "letE"
  | lit _ _         => println! "lit"
  | mdata _ _ _     => println! "mdata"
  | proj _ _ _ _    => println! "proj"


def test {α : Type} [One α ] (x : α) : α :=  x

def a := TransparencyMode

instance : Numeric Nat := ⟨id⟩
@[simp] theorem ofNatNat (n : Nat ): Numeric.ofNat n = n := rfl

instance : CommSemiring Nat where
  mul_comm := Nat.mul_comm
  mul_add := Nat.mul_add
  add_mul := Nat.add_mul
  ofNat_add := by simp
  ofNat_mul := by simp
  ofNat_one := rfl
  ofNat_zero := rfl
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  npow := Nat.pow
  npow_zero' := sorry
  npow_succ' := sorry
  one := 1
  zero := 0
  mul_assoc := Nat.mul_assoc
  add_comm := Nat.add_comm
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add
  nsmul := Nat.mul
  nsmul_zero' := sorry
  nsmul_succ' := sorry
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero

















def Lean.Expr.pp (e : Expr) : MetaM Format := do
  return (← PrettyPrinter.ppExpr Name.anonymous [] e)

theorem ofNat_add {α} [Semiring α] : (a b : α) → (a' b' c : Nat) →
  a = OfNat.ofNat a' → b = OfNat.ofNat b' → a' + b' = c → a + b = OfNat.ofNat c
| _, _, _, _, _, rfl, rfl, rfl => (Semiring.ofNat_add _ _).symm


namespace Tactic
namespace Ring
-- set_option pp.all true
-- set_option pp.
variable {α} [CommSemiring α]
-- #eval (OfNat.ofNat 2 : α)
theorem one {α} [CommSemiring α] :  (2 : α ) = OfNat.ofNat 2 := rfl

theorem x {α} [CommSemiring α] :  (2 : α) + 2 = 4:=
ofNat_add (2: α) (2 : α) 2 2 4 rfl rfl rfl
#print x

/-- This cache contains data required by the `ring` tactic during execution. -/
structure Cache :=
  α : Expr
  univ : Level

structure State :=
  atoms : Array Expr := #[]
  numAtoms : Nat     := 0

abbrev RingM := ReaderT Cache $ StateRefT State TacticM

def run (e : Expr) {α} (m : RingM α): TacticM α := do
  let ty ← inferType e
  let u ← getLevel ty
  (m {α := ty, univ := u}).run' {}

def addAtom (e : Expr) : RingM Nat := do
  let c ← get
  for i in [:c.numAtoms] do
    if ← isDefEq e c.atoms[i] then
      return i
  modify λ c => { c with atoms := c.atoms.push e, numAtoms := c.numAtoms + 1}
  return c.numAtoms

/-- The normal form that `ring` uses is mediated by the function `horner a x n b := a * x ^ n + b`.
The reason we use a definition rather than the (more readable) expression on the right is because
this expression contains a number of typeclass arguments in different positions, while `horner`
contains only one `comm_semiring` instance at the top level. See also `horner_expr` for a
description of normal form. -/
@[reducible] def horner {α} [CommSemiring α] (a x : α) (n : ℕ) (b : α) := a * (x ^ n) + b

inductive HornerExpr : Type
| const (e : Expr) (coeff : ℕ) : HornerExpr
| xadd (e : Expr) (a : HornerExpr) (x : Expr × ℕ) (n : Expr × ℕ) (b : HornerExpr) : HornerExpr

instance : Inhabited HornerExpr := ⟨HornerExpr.const (mkNatLit 0) 0⟩

namespace HornerExpr

def e : HornerExpr → Expr
| (HornerExpr.const e _) => e
| (HornerExpr.xadd e _ _ _ _) => e

instance : Coe HornerExpr Expr := ⟨e⟩

def xadd' (a : HornerExpr) (x : Expr × ℕ) (n : Expr × ℕ) (b : HornerExpr) : RingM HornerExpr := do
  xadd (← mkAppM ``horner #[a, x.1, n.1, b]) a x n b


def reflConv (e : HornerExpr) : RingM (HornerExpr × Expr) := do (e, ← mkEqRefl e)


/-- Pretty printer for `horner_expr`. -/
def pp : HornerExpr → TacticM Format
| (const e c) => do
  let pe ← PrettyPrinter.ppExpr Name.anonymous [] e
  return "[" ++ pe ++ ", " ++ toString c ++ "]"
| (xadd e a x (_, n) b) => do
  let pa ← a.pp
  let pb ← b.pp
  let px ← PrettyPrinter.ppExpr Name.anonymous [] x.1
  return "(" ++ pa ++ ") * (" ++ px ++ ")^" ++ toString n ++ " + " ++ pb


end HornerExpr

open HornerExpr

theorem horner_atom {α} [CommSemiring α] (x : α) : x = horner 1 x 1 0 := by
  simp [horner]
  rw [← npow_eq_pow, npow_succ', npow_zero', mul_one]

theorem const_add_horner {α} [CommSemiring α] (k a x n b b') (h : k + b = b') :
  k + @horner α _ a x n b = horner a x n b' :=
by
  simp [horner, h.symm, add_comm k, add_assoc]

theorem horner_add_const {α} [CommSemiring α] (a x n b k b') (h : b + k = b') :
  @horner α _ a x n b + k = horner a x n b' :=
by
  simp [horner, h.symm ,add_left_comm k, add_assoc]

theorem subst_into_add {α} [Add α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t :=
by rw [prl, prr, prt]

def evalAtom (e : Expr) : RingM (HornerExpr × Expr) := do
  let i ← addAtom e
  let one := const (← mkNumeral (← read).α 1) 1
  let zero := const (← mkNumeral (← read).α 0)  0
  return (← xadd' one (e,i) (mkNatLit 1,1) zero, ← mkAppM ``horner_atom #[e])


partial def evalAdd : HornerExpr → HornerExpr → RingM (HornerExpr × Expr)
| (const e₁ c₁), (const e₂ c₂) => do
  let e ← mkNumeral (← read).α (c₁ + c₂)
  let (p,ee) ← NormNum.eval $ ← mkAdd e₁ e₂
  let ty ← inferType ee
  (const e (c₁ + c₂), ee)
| he₁@(const e₁ c₁), he₂@(xadd e₂ a x n b) => do

  if c₁ = 0 then
    let p ← mkAppM ``zero_add #[e₂]
    return (he₂, p)
  else
    let (b', h) ← evalAdd he₁ b
    return (← xadd' a x n b',
      ← mkAppM ``const_add_horner #[e₁, a, x.1, n.1, b, b', h])
| he₁@(xadd e₁ a x n b), he₂@(const e₂ c₂) => do
  if c₂ = 0 then
    let p ← mkAppM ``zero_add #[e₁]
    return (he₁, p)
  else
    let (b', h) ← evalAdd b he₂
    return (← xadd' a x n b',
      ← mkAppM ``horner_add_const #[a, x.1, n.1, b, e₂, b', h])
| he₁@(xadd e₁ a₁ x₁ n₁ b₁), he₂@(xadd e₂ a₂ x₂ n₂ b₂) => do
  throwError "unsupported"
  -- let c ← get
  -- if x₁.2 < x₂.2 then
  --   let (b', h) ← evalAdd b₁ he₂
  --   return (← xadd' a₁ x₁ n₁ b',
  --     ← mkAppM ``horner_add_const #[a₁, x₁.1, n₁.1, b₁, e₂, b', h])
  -- else if x₁.2 ≠ x₂.2 then
  --   let (b', h) ← evalAdd he₁ b₂
  --   return (← xadd' a₂ x₂ n₂ b',
  --     ← mkAppM ``const_add_horner #[e₁, a₂, x₂.1, n₂.1, b₂, b', h])
  -- else if n₁.2 < n₂.2 then do
  --   let k := n₂.2 - n₁.2
  --   (ek, h₁) ← nc_lift (λ nc => do
  --     (nc, ek) ← nc.of_nat k,
  --     (nc, h₁) ← norm_num.prove_add_nat nc n₁.1 ek n₂.1,
  --     return (nc, ek, h₁)),
  --   α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
  --   (a', h₂) ← eval_add a₁ (xadd' c a₂ x₁ (ek, k) (const α0 0)),
  --   (b', h₃) ← eval_add b₁ b₂,
  --   return (xadd' c a' x₁ n₁ b',
  --     c.cs_app ``horner_add_horner_lt [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  -- else if n₁.2 ≠ n₂.2 then do
  --   let k := n₁.2 - n₂.2,
  --   (ek, h₁) ← nc_lift (λ nc, do
  --     (nc, ek) ← nc.of_nat k,
  --     (nc, h₁) ← norm_num.prove_add_nat nc n₂.1 ek n₁.1,
  --     return (nc, ek, h₁)),
  --   α0 ← ic_lift $ λ ic, ic.mk_app ``has_zero.zero [],
  --   (a', h₂) ← eval_add (xadd' c a₁ x₁ (ek, k) (const α0 0)) a₂,
  --   (b', h₃) ← eval_add b₁ b₂,
  --   return (xadd' c a' x₁ n₂ b',
  --     c.cs_app ``horner_add_horner_gt [a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  -- else do
  --   (a', h₁) ← eval_add a₁ a₂,
  --   (b', h₂) ← eval_add b₁ b₂,
  --   (t, h₃) ← eval_horner a' x₁ n₁ b',
  --   return (t, c.cs_app ``horner_add_horner_eq
  --     [a₁, x₁.1, n₁.1, b₁, a₂, b₂, a', b', t, h₁, h₂, h₃])


partial def eval (e : Expr) : RingM (HornerExpr × Expr) :=
  match e.getAppFnAndArgs with
  | some (``HAdd.hAdd, #[_,_,_,_,e₁,e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    let p ← mkAppM ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    (e',p)
  | _ =>
    match numeral? e with
    | some n => (const e n).reflConv
    | _ => (evalAtom e)


elab "ring" : tactic => do
  let g ← getMainTarget
  match g.getAppFnAndArgs with
  | some (`Eq, #[ty, e₁, e₂]) =>
    let ((e₁', p₁), (e₂', p₂)) ← run e₁ $ Prod.mk <$> eval e₁ <*> eval e₂
    if (← isDefEq e₁' e₂') then
      let p ← mkEqTrans p₁ (← mkEqSymm p₂)
      ensureHasNoMVars p
      assignExprMVar (← getMainGoal) p

      replaceMainGoal []
    else
      throwError "failed \n{← e₁'.pp}\n{← e₂'.pp}"
  | _ => throwError "not eq"

def b := Eq.trans (Tactic.Ring.horner_atom 1) (Eq.symm (Tactic.Ring.horner_atom 1))
-- set_option pp.notation false

def test {α} [CommSemiring α] (x y : α) : 6 + x + 1 = 4 + (x + 3) := by ring; done


#print test.proof_1

#check Eq.trans (Tactic.Ring.horner_atom 1) (Eq.symm (Tactic.Ring.horner_atom 1))
#eval horner 1 1 1 0
-- set_option pp.all true

variable {α} [CommSemiring α]
#check (1 : α )
#check horner 1 1 1 0
