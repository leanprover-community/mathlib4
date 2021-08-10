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

theorem pow_mul_comm {M} [Monoid M] (a : M) (n : ℕ) : a^n * a = a * a^n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, pow_succ, mul_assoc]

theorem pow_add {M} [Monoid M] (a : M) (m n : ℕ) : a^(m + n) = a^m * a^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, pow_succ,ih, pow_succ, ← mul_assoc, ← mul_assoc, pow_mul_comm]
    done

theorem mul_add {R} [Semiring R] (a b c : R) : a * (b + c) = a * b + a * c := Semiring.mul_add a b c

theorem add_mul {R} [Semiring R] (a b c : R) : (a + b) * c = a * c + b * c := Semiring.add_mul a b c

@[simp] theorem mul_zero {R} [Semiring R] (a : R) : a * 0 = 0 := Semiring.mul_zero a

@[simp] theorem zero_mul {R} [Semiring R] (a : R) : 0 * a = 0 := Semiring.zero_mul a




def Lean.Expr.pp (e : Expr) : MetaM Format := do
  return (← PrettyPrinter.ppExpr Name.anonymous [] e)


namespace Tactic
namespace Ring

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

/-- Is this expr the constant `0`? -/
def isZero : HornerExpr → Bool
| (HornerExpr.const _ c) => c = 0
| _ => false

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
  rw [pow_succ, pow_zero, mul_one]

theorem const_add_horner {α} [CommSemiring α] (k a x n b b') (h : k + b = b') :
  k + @horner α _ a x n b = horner a x n b' :=
by
  simp [horner, h.symm, add_comm k, add_assoc]

theorem horner_add_const {α} [CommSemiring α] (a x n b k b') (h : b + k = b') :
  @horner α _ a x n b + k = horner a x n b' :=
by
  simp [horner, h.symm ,add_left_comm k, add_assoc]

theorem horner_add_horner_lt {α} [CommSemiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
  (h₁ : n₁ + k = n₂) (h₂ : (a₁ + horner a₂ x k 0 : α) = a') (h₃ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₁ b' :=
by
  rw [← h₁, ← h₂, ← h₃]
  simp [horner, add_mul, mul_assoc, (pow_add x k n₁).symm, add_comm k, @add_comm α _, @add_assoc α ]

theorem horner_add_horner_gt {α} [CommSemiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
  (h₁ : n₂ + k = n₁) (h₂ : (horner a₁ x k 0 + a₂ : α) = a') (h₃ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₂ b' :=
by
  rw [← h₁, ← h₂, ← h₃]
  simp [horner, add_mul, mul_assoc, (pow_add x k n₂).symm, add_comm k, @add_comm α _, @add_assoc α ]

theorem horner_add_horner_eq {α} [CommSemiring α] (a₁ x n b₁ a₂ b₂ a' b' t)
  (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b') (h₃ : horner a' x n b' = t) :
  @horner α _ a₁ x n b₁ + horner a₂ x n b₂ = t :=
by
  rw [← h₃, ← h₁, ← h₂]
  simp [horner, add_mul, @add_comm α _, @add_assoc α]

theorem subst_into_add {α} [Add α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t :=
by rw [prl, prr, prt]

theorem subst_into_mul {α} [Mul α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl * tr = t) : l * r = t :=
by rw [prl, prr, prt]

theorem zero_horner {α} [CommSemiring α] (x n b) :
  @horner α _ 0 x n b = b :=
by simp [horner]

theorem horner_horner {α} [CommSemiring α] (a₁ x n₁ n₂ b n')
  (h : n₁ + n₂ = n') :
  @horner α _ (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
by simp [h.symm, horner, pow_add, mul_assoc]

def evalAtom (e : Expr) : RingM (HornerExpr × Expr) := do
  let i ← addAtom e
  let one := const (← mkNumeral (← read).α 1) 1
  let zero := const (← mkNumeral (← read).α 0)  0
  return (← xadd' one (e,i) (mkNatLit 1,1) zero, ← mkAppM ``horner_atom #[e])

/-- Evaluate `horner a n x b` where `a` and `b` are already in normal form. -/
def evalHorner : HornerExpr → Expr × ℕ → Expr × ℕ → HornerExpr → RingM (HornerExpr × Expr)
| ha@(const a coeff), x, n, b => do
  if coeff = 0 then
    return (b, ← mkAppM ``zero_horner #[x.1, n.1, b])
  else (← xadd' ha x n b).reflConv
| ha@(xadd a a₁ x₁ n₁ b₁), x, n, b => do
  if x₁.2 = x.2 ∧ numeral? b₁.e = some 0 then do
    let (n', h) ← NormNum.eval $ ← mkAdd n₁.1 n.1
    return (← xadd' a₁ x (n', n₁.2 + n.2) b,
      ← mkAppM ``horner_horner #[a₁, x.1, n₁.1, n.1, b, n', h])
  else (← xadd' ha x n b).reflConv

partial def evalAdd : HornerExpr → HornerExpr → RingM (HornerExpr × Expr)
| (const e₁ c₁), (const e₂ c₂) => do
  let (e', p) ← NormNum.eval $ ← mkAdd e₁ e₂
  (const e' (c₁ + c₂), p)
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
    let p ← mkAppM ``add_zero #[e₁]
    return (he₁, p)
  else
    let (b', h) ← evalAdd b he₂
    return (← xadd' a x n b',
      ← mkAppM ``horner_add_const #[a, x.1, n.1, b, e₂, b', h])
| he₁@(xadd e₁ a₁ x₁ n₁ b₁), he₂@(xadd e₂ a₂ x₂ n₂ b₂) => do
  let c ← get
  if x₁.2 < x₂.2 then
    let (b', h) ← evalAdd b₁ he₂
    return (← xadd' a₁ x₁ n₁ b',
      ← mkAppM ``horner_add_const #[a₁, x₁.1, n₁.1, b₁, e₂, b', h])
  else if x₁.2 ≠ x₂.2 then
    let (b', h) ← evalAdd he₁ b₂
    return (← xadd' a₂ x₂ n₂ b',
      ← mkAppM ``const_add_horner #[e₁, a₂, x₂.1, n₂.1, b₂, b', h])
  else if n₁.2 < n₂.2 then do
    let k := n₂.2 - n₁.2
    let ek ← mkNatLit k
    let (p, h₁) ← NormNum.eval $ ← mkAdd n₁.1 ek
    let c ← read
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkNatLit 0, none]
    let (a', h₂) ← evalAdd a₁ (← xadd' a₂ x₁ (ek, k) (const α0 0))
    let (b', h₃) ← evalAdd b₁ b₂
    return (← xadd' a' x₁ n₁ b',
      ← mkAppM ``horner_add_horner_lt #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  else if n₁.2 ≠ n₂.2 then do
    let k := n₁.2 - n₂.2
    let ek ← mkNatLit k
    let (p, h₁) ← NormNum.eval $ ← mkAdd n₂.1 ek
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkNatLit 0, none]
    let (a', h₂) ← evalAdd (← xadd' a₁ x₁ (ek, k) (const α0 0)) a₂
    let (b', h₃) ← evalAdd b₁ b₂
    return (← xadd' a' x₁ n₂ b',
      ← mkAppM ``horner_add_horner_gt #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  else do
    let (a', h₁) ← evalAdd a₁ a₂
    let (b', h₂) ← evalAdd b₁ b₂
    let (t, h₃) ← evalHorner a' x₁ n₁ b'
    return (t, ← mkAppM ``horner_add_horner_eq
      #[a₁, x₁.1, n₁.1, b₁, a₂, b₂, a', b', t, h₁, h₂, h₃])


theorem horner_const_mul {α} [CommSemiring α] (c a x n b a' b')
  (h₁ : c * a = a') (h₂ : c * b = b') :
  c * @horner α _ a x n b = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, mul_add, mul_assoc]

theorem horner_mul_const {α} [CommSemiring α] (a x n b c a' b')
  (h₁ : a * c = a') (h₂ : b * c = b') :
  @horner α _ a x n b * c = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, add_mul, @mul_right_comm α _]

/-- Evaluate `k * a` where `k` is a rational numeral and `a` is in normal form. -/
def evalConstMul (k : Expr × ℕ) : HornerExpr → RingM (HornerExpr × Expr)
| (const e coeff) => do
  let (e', p) ← NormNum.eval $ ← mkMul k.1 e
  return (const e' (k.2 * coeff), p)
| (xadd e a x n b) => do
  let (a', h₁) ← evalConstMul k a
  let (b', h₂) ← evalConstMul k b
  return (← xadd' a' x n b',
    ← mkAppM ``horner_const_mul #[k.1, a, x.1, n.1, b, a', b', h₁, h₂])


theorem horner_mul_horner_zero {α} [CommSemiring α] (a₁ x n₁ b₁ a₂ n₂ aa t)
  (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
  (h₂ : horner aa x n₂ 0 = t) :
  horner a₁ x n₁ b₁ * horner a₂ x n₂ 0 = t :=
by
  rw [← h₂, ← h₁]
  simp [horner, mul_add, mul_comm, mul_left_comm, mul_assoc]

theorem horner_mul_horner {α} [CommSemiring α]
  (a₁ x n₁ b₁ a₂ n₂ b₂ aa haa ab bb t)
  (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
  (h₂ : horner aa x n₂ 0 = haa)
  (h₃ : a₁ * b₂ = ab) (h₄ : b₁ * b₂ = bb)
  (H : haa + horner ab x n₁ bb = t) :
  horner a₁ x n₁ b₁ * horner a₂ x n₂ b₂ = t :=
by
  rw [← H, ← h₂, ← h₁, ← h₃, ← h₄]
  simp [horner, mul_add, add_mul, @mul_comm α _, mul_left_comm, mul_assoc]

/-- Evaluate `a * b` where `a` and `b` are in normal form. -/
partial def evalMul : HornerExpr → HornerExpr → RingM (HornerExpr × Expr)
| (const e₁ c₁), (const e₂ c₂) => do
  let (e', p) ← NormNum.eval $ ← mkMul e₁ e₂
  return (const e' (c₁ * c₂), p)
| (const e₁ c₁), e₂ =>
  if c₁ = 0 then do
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkNatLit 0, none]
    let p ← mkAppM ``zero_mul #[e₂]
    return (const α0 0, p)
  else if c₁ = 1 then do
    let p ←  mkAppM ``one_mul #[e₂]
    return (e₂, p)
  else evalConstMul (e₁, c₁) e₂
| e₁, he₂@(const e₂ c₂) => do
  let p₁ ← mkAppM ``mul_comm #[e₁, e₂]
  let (e', p₂) ← evalMul he₂ e₁
  let p ← mkEqTrans p₁ p₂
  return (e', p)
| he₁@(xadd e₁ a₁ x₁ n₁ b₁), he₂@(xadd e₂ a₂ x₂ n₂ b₂) => do
  if x₁.2 < x₂.2 then do
    let (a', h₁) ← evalMul a₁ he₂
    let (b', h₂) ← evalMul b₁ he₂
    return (← xadd' a' x₁ n₁ b',
      ← mkAppM ``horner_mul_const #[a₁, x₁.1, n₁.1, b₁, e₂, a', b', h₁, h₂])
  else if x₁.2 ≠ x₂.2 then do
    let (a', h₁) ← evalMul he₁ a₂
    let (b', h₂) ← evalMul he₁ b₂
    return (← xadd' a' x₂ n₂ b',
      ← mkAppM ``horner_const_mul #[e₁, a₂, x₂.1, n₂.1, b₂, a', b', h₁, h₂])
  else do
    let (aa, h₁) ← evalMul he₁ a₂
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkNatLit 0, none]
    let (haa, h₂) ← evalHorner aa x₁ n₂ (const α0 0)
    if b₂.isZero then
      return (haa, ← mkAppM ``horner_mul_horner_zero
        #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, aa, haa, h₁, h₂])
    else do
      let (ab, h₃) ← evalMul a₁ b₂
      let (bb, h₄) ← evalMul b₁ b₂
      let (t, H) ← evalAdd haa (← xadd' ab x₁ n₁ bb)
      return (t, ← mkAppM ``horner_mul_horner
        #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, aa, haa, ab, bb, t, h₁, h₂, h₃, h₄, H])


partial def eval (e : Expr) : RingM (HornerExpr × Expr) :=
  match e.getAppFnAndArgs with
  | some (``HAdd.hAdd, #[_,_,_,_,e₁,e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    let p ← mkAppM ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    (e',p)
  | some (``HMul.hMul, #[_,_,_,_,e₁,e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalMul e₁' e₂'
    let p ← mkAppM ``subst_into_mul #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    return (e', p)
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
-- set_option pp.all true
def test {α} [CommSemiring α] (x y z : α) : x * y * 2 + x + 2 * y = y * (x + 2) + (y +1) * x := by ring; done

#print test
#print test.proof_1
