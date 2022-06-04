/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum

/-!
# `ring`

Evaluate expressions in the language of commutative (semi)rings.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .
-/

open Lean Parser.Tactic Elab Command Elab.Tactic Meta

namespace Tactic
namespace Ring

/-- This cache contains data required by the `ring` tactic during execution. -/
structure Cache :=
  α : Expr
  univ : Level
  cs : Expr

structure State :=
  atoms : Array Expr := #[]
  numAtoms : Nat     := 0

/-- The monad that `ring` works in. This is a reader monad containing a cache and
the list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
abbrev RingM := ReaderT Cache $ StateRefT State MetaM

def RingM.run (ty : Expr) (m : RingM α) : MetaM α := do
  let Level.succ u _ ← getLevel ty | throwError "fail"
  let inst ← synthInstance (mkApp (mkConst ``CommSemiring [u]) ty)
  (m {α := ty, univ := u, cs := inst }).run' {}

def mkAppCS (f : Name) (args : Array Expr) : RingM Expr := do
  let c ← read
  pure $ mkAppN (mkConst f [c.univ]) (#[c.α, c.cs] ++ args)

/-- Get the index corresponding to an atomic expression, if it has already been encountered, or
put it in the list of atoms and return the new index, otherwise. -/
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
contains only one `CommSemiring` instance at the top level. See also `HornerExpr` for a
description of normal form. -/
@[reducible] def horner {α} [CommSemiring α] (a x : α) (n : ℕ) (b : α) := a * (x ^ n) + b

/-- Every expression in the language of commutative semirings can be viewed as a sum of monomials,
where each monomial is a product of powers of atoms. We fix a global order on atoms (up to
definitional equality), and then separate the terms according to their smallest atom. So the top
level expression is `a * x^n + b` where `x` is the smallest atom and `n > 0` is a numeral, and
`n` is maximal (so `a` contains at least one monomial not containing an `x`), and `b` contains no
monomials with an `x` (hence all atoms in `b` are larger than `x`).

If there is no `x` satisfying these constraints, then the expression must be a numeral. Even though
we are working over rings, we allow rational constants when these can be interpreted in the ring,
so we can solve problems like `x / 3 = 1 / 3 * x` even though these are not technically in the
language of rings.

These constraints ensure that there is a unique normal form for each ring expression, and so the
algorithm is simply to calculate the normal form of each side and compare for equality.

To allow us to efficiently pattern match on normal forms, we maintain this inductive type that
holds a normalized expression together with its structure. All the `Expr`s in this type could be
removed without loss of information, and conversely the `horner_expr` structure and the `ℕ` and
`ℚ` values can be recovered from the top level `Expr`, but we keep both in order to keep proof
producing normalization functions efficient. -/
inductive HornerExpr : Type
| const (e : Expr) (coeff : ℕ) : HornerExpr --TODO : coeff in ℚ
| xadd (e : Expr) (a : HornerExpr) (x : Expr × ℕ) (n : Expr × ℕ) (b : HornerExpr) : HornerExpr

instance : Inhabited HornerExpr := ⟨HornerExpr.const (mkRawNatLit 0) 0⟩

namespace HornerExpr

/-- Get the expression corresponding to a `HornerExpr`. This can be calculated recursively from
the structure, but we cache the exprs in all subterms so that this function can be computed in
constant time. -/
def e : HornerExpr → Expr
| (HornerExpr.const e _) => e
| (HornerExpr.xadd e _ _ _ _) => e

instance : Coe HornerExpr Expr := ⟨e⟩

/-- Is this expr the constant `0`? -/
def isZero : HornerExpr → Bool
| (HornerExpr.const _ c) => c = 0
| _ => false

/-- Construct a `xadd` node -/
def xadd' (a : HornerExpr) (x : Expr × ℕ) (n : Expr × ℕ) (b : HornerExpr) : RingM HornerExpr := do
  pure $ xadd (← mkAppCS ``horner #[a, x.1, n.1, b]) a x n b

/-- Reflexivity conversion for a `HornerExpr`. -/
def reflConv (e : HornerExpr) : RingM (HornerExpr × Expr) := do pure (e, ← mkEqRefl e)

/-- Pretty printer for `horner_expr`. -/
def pp : HornerExpr → MetaM Format
| (const e c) => pure $ toString c
| (xadd e a x (_, n) b) => do
  let pa ← a.pp
  let pb ← b.pp
  let px ← PrettyPrinter.ppExpr x.1
  return "(" ++ pa ++ ") * (" ++ px ++ ")^" ++ toString n ++ " + " ++ pb

end HornerExpr

open HornerExpr

theorem zero_horner {α} [CommSemiring α] (x n b) :
  @horner α _ 0 x n b = b :=
by simp [horner]

theorem horner_horner {α} [CommSemiring α] (a₁ x n₁ n₂ b n')
  (h : n₁ + n₂ = n') :
  @horner α _ (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
by simp [h.symm, horner, pow_add, mul_assoc]

/-- Evaluate `horner a n x b` where `a` and `b` are already in normal form. -/
def evalHorner : HornerExpr → Expr × ℕ → Expr × ℕ → HornerExpr → RingM (HornerExpr × Expr)
| ha@(const a coeff), x, n, b => do
  if coeff = 0 then
    return (b, ← mkAppCS ``zero_horner #[x.1, n.1, b])
  else (← xadd' ha x n b).reflConv
| ha@(xadd a a₁ x₁ n₁ b₁), x, n, b => do
  if x₁.2 = x.2 ∧ b₁.e.numeral? = some 0 then do
    let n' := mkRawNatLit (n₁.2 + n.2)
    let h ← mkEqRefl n'
    return (← xadd' a₁ x (n', n₁.2 + n.2) b,
      ← mkAppCS ``horner_horner #[a₁, x.1, n₁.1, n.1, b, n', h])
  else (← xadd' ha x n b).reflConv


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
  simp [horner, add_assoc, add_mul, pow_add, mul_assoc, add_comm n₁ k, add_left_comm b₁]

theorem horner_add_horner_gt {α} [CommSemiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
  (h₁ : n₂ + k = n₁) (h₂ : (horner a₁ x k 0 + a₂ : α) = a') (h₃ : b₁ + b₂ = b') :
  @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₂ b' :=
by
  rw [← h₁, ← h₂, ← h₃]
  simp [horner, add_assoc, mul_assoc, add_mul, add_comm n₂ k, pow_add, add_left_comm b₁]

theorem horner_add_horner_eq {α} [CommSemiring α] (a₁ x n b₁ a₂ b₂ a' b' t)
  (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b') (h₃ : horner a' x n b' = t) :
  @horner α _ a₁ x n b₁ + horner a₂ x n b₂ = t :=
by
  rw [← h₃, ← h₁, ← h₂]
  simp only [horner, add_assoc, mul_assoc, add_mul, zero_mul, zero_add, pow_add, add_left_comm b₁]

partial def evalAdd : HornerExpr → HornerExpr → RingM (HornerExpr × Expr)
| (const e₁ c₁), (const e₂ c₂) => do
  let (e', p) ← NormNum.eval $ ← mkAdd e₁ e₂
  pure (const e' (c₁ + c₂), p)
| he₁@(const e₁ c₁), he₂@(xadd e₂ a x n b) => do

  if c₁ = 0 then
    let p ← mkAppM ``zero_add #[e₂]
    return (he₂, p)
  else
    let (b', h) ← evalAdd he₁ b
    return (← xadd' a x n b',
      ← mkAppCS ``const_add_horner #[e₁, a, x.1, n.1, b, b', h])
| he₁@(xadd e₁ a x n b), he₂@(const e₂ c₂) => do
  if c₂ = 0 then
    let p ← mkAppM ``add_zero #[e₁]
    return (he₁, p)
  else
    let (b', h) ← evalAdd b he₂
    return (← xadd' a x n b',
      ← mkAppCS ``horner_add_const #[a, x.1, n.1, b, e₂, b', h])
| he₁@(xadd e₁ a₁ x₁ n₁ b₁), he₂@(xadd e₂ a₂ x₂ n₂ b₂) => do
  let c ← get
  if x₁.2 < x₂.2 then
    let (b', h) ← evalAdd b₁ he₂
    return (← xadd' a₁ x₁ n₁ b',
      ← mkAppCS ``horner_add_const #[a₁, x₁.1, n₁.1, b₁, e₂, b', h])
  else if x₁.2 ≠ x₂.2 then
    let (b', h) ← evalAdd he₁ b₂
    return (← xadd' a₂ x₂ n₂ b',
      ← mkAppCS ``const_add_horner #[e₁, a₂, x₂.1, n₂.1, b₂, b', h])
  else if n₁.2 < n₂.2 then do
    let k := n₂.2 - n₁.2
    let ek := mkRawNatLit k
    let h₁ ← mkEqRefl n₂.1
    let c ← read
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 0, none]
    let (a', h₂) ← evalAdd a₁ (← xadd' a₂ x₁ (ek, k) (const α0 0))
    let (b', h₃) ← evalAdd b₁ b₂
    return (← xadd' a' x₁ n₁ b',
      ← mkAppCS ``horner_add_horner_lt #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  else if n₁.2 ≠ n₂.2 then do
    let k := n₁.2 - n₂.2
    let ek := mkRawNatLit k
    let h₁ ← mkEqRefl n₁.1
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 0, none]
    let (a', h₂) ← evalAdd (← xadd' a₁ x₁ (ek, k) (const α0 0)) a₂
    let (b', h₃) ← evalAdd b₁ b₂
    return (← xadd' a' x₁ n₂ b',
      ← mkAppCS ``horner_add_horner_gt #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, ek, a', b', h₁, h₂, h₃])
  else do
    let (a', h₁) ← evalAdd a₁ a₂
    let (b', h₂) ← evalAdd b₁ b₂
    let (t, h₃) ← evalHorner a' x₁ n₁ b'
    return (t, ← mkAppCS ``horner_add_horner_eq
      #[a₁, x₁.1, n₁.1, b₁, a₂, b₂, a', b', t, h₁, h₂, h₃])


theorem horner_const_mul {α} [CommSemiring α] (c a x n b a' b')
  (h₁ : c * a = a') (h₂ : c * b = b') :
  c * @horner α _ a x n b = horner a' x n b' :=
by simp [h₂.symm, h₁.symm, horner, mul_add, mul_assoc]

theorem horner_mul_const {α} [CommSemiring α] (a x n b c a' b')
  (h₁ : a * c = a') (h₂ : b * c = b') :
  @horner α _ a x n b * c = horner a' x n b' :=
by simp [horner, ← h₁, ← h₂, add_mul, mul_assoc, mul_comm c]

/-- Evaluate `k * a` where `k` is a rational numeral and `a` is in normal form. -/
def evalConstMul (k : Expr × ℕ) : HornerExpr → RingM (HornerExpr × Expr)
| (const e coeff) => do
  let (e', p) ← NormNum.eval $ ← mkMul k.1 e
  return (const e' (k.2 * coeff), p)
| (xadd e a x n b) => do
  let (a', h₁) ← evalConstMul k a
  let (b', h₂) ← evalConstMul k b
  return (← xadd' a' x n b',
    ← mkAppCS ``horner_const_mul #[k.1, a, x.1, n.1, b, a', b', h₁, h₂])


theorem horner_mul_horner_zero {α} [CommSemiring α] (a₁ x n₁ b₁ a₂ n₂ aa t)
  (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
  (h₂ : horner aa x n₂ 0 = t) :
  horner a₁ x n₁ b₁ * horner a₂ x n₂ 0 = t :=
by
  rw [← h₂, ← h₁]
  simp [horner, add_mul, mul_assoc]

theorem horner_mul_horner {α} [CommSemiring α]
  (a₁ x n₁ b₁ a₂ n₂ b₂ aa haa ab bb t)
  (h₁ : @horner α _ a₁ x n₁ b₁ * a₂ = aa)
  (h₂ : horner aa x n₂ 0 = haa)
  (h₃ : a₁ * b₂ = ab) (h₄ : b₁ * b₂ = bb)
  (H : haa + horner ab x n₁ bb = t) :
  horner a₁ x n₁ b₁ * horner a₂ x n₂ b₂ = t :=
by
  rw [← H, ← h₂, ← h₁, ← h₃, ← h₄]
  simp [horner, add_mul, mul_add, mul_assoc, mul_comm b₂]

/-- Evaluate `a * b` where `a` and `b` are in normal form. -/
partial def evalMul : HornerExpr → HornerExpr → RingM (HornerExpr × Expr)
| (const e₁ c₁), (const e₂ c₂) => do
  let (e', p) ← NormNum.eval $ ← mkMul e₁ e₂
  return (const e' (c₁ * c₂), p)
| (const e₁ c₁), e₂ =>
  if c₁ = 0 then do
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 0, none]
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
      ← mkAppCS ``horner_mul_const #[a₁, x₁.1, n₁.1, b₁, e₂, a', b', h₁, h₂])
  else if x₁.2 ≠ x₂.2 then do
    let (a', h₁) ← evalMul he₁ a₂
    let (b', h₂) ← evalMul he₁ b₂
    return (← xadd' a' x₂ n₂ b',
      ← mkAppCS ``horner_const_mul #[e₁, a₂, x₂.1, n₂.1, b₂, a', b', h₁, h₂])
  else do
    let (aa, h₁) ← evalMul he₁ a₂
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 0, none]
    let (haa, h₂) ← evalHorner aa x₁ n₂ (const α0 0)
    if b₂.isZero then
      return (haa, ← mkAppCS ``horner_mul_horner_zero
        #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, aa, haa, h₁, h₂])
    else do
      let (ab, h₃) ← evalMul a₁ b₂
      let (bb, h₄) ← evalMul b₁ b₂
      let (t, H) ← evalAdd haa (← xadd' ab x₁ n₁ bb)
      return (t, ← mkAppCS ``horner_mul_horner
        #[a₁, x₁.1, n₁.1, b₁, a₂, n₂.1, b₂, aa, haa, ab, bb, t, h₁, h₂, h₃, h₄, H])


theorem horner_pow {α} [CommSemiring α] (a x : α) (n m n' : ℕ) (a') (h₁ : n * m = n') (h₂ : a ^ m = (a' : α)) :
  @horner α _ a x n 0 ^ m = horner a' x n' 0 :=
by
  simp [h₁.symm, h₂.symm, horner,  mul_pow a, pow_mul]

theorem pow_succ_eq {α} [CommSemiring α] (a : α) (n : ℕ) (b c)
  (h₁ : a ^ n = b) (h₂ : b * a = c) : a ^ (n + 1) = c :=
by rw [← h₂, ← h₁, pow_succ]

/-- Evaluate `a ^ n` where `a` is in normal form and `n` is a natural numeral. -/
partial def evalPow : HornerExpr → Expr × ℕ → RingM (HornerExpr × Expr)
| e, (_, 0) => do
  let α1 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 1, none]
  let p ← mkAppM ``pow_zero #[e]
  pure (const α1 1, p)
| e, (_, 1) => do
  let p ← mkAppM ``pow_one #[e]
  pure (e, p)
| const e coeff, (e₂, m) => do
  let (e', p) ← NormNum.eval $ ← mkAppM ``HPow.hPow #[e, e₂]
  pure (const e' (coeff ^ m), p)
| he@(xadd e a x n b), m =>
  match b.e.numeral? with
  | some 0 => do
    let n' := mkRawNatLit (n.2 * m.2)
    let h₁ ← mkEqRefl n'
    let (a', h₂) ← evalPow a m
    let α0 ← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 0, none]
    pure (← xadd' a' x (n', n.2 * m.2) (const α0 0),
      ← mkAppCS ``horner_pow #[a, x.1, n.1, m.1, n', a', h₁, h₂])
  | _ => do
    let e₂ := mkRawNatLit (m.2 - 1)
    let (tl, hl) ← evalPow he (e₂, m.2-1)
    let (t, p₂) ← evalMul tl he
    pure (t, ← mkAppCS ``pow_succ_eq #[e, e₂, tl, t, hl, p₂])


theorem horner_atom {α} [CommSemiring α] (x : α) : x = horner 1 x 1 0 := by
  simp [horner]

/-- Evaluate `a` where `a` is an atom. -/
def evalAtom (e : Expr) : RingM (HornerExpr × Expr) := do
  let i ← addAtom e
  let zero := const (← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 0, none]) 0
  let one := const (← mkAppOptM ``OfNat.ofNat #[(← read).α, mkRawNatLit 1, none]) 1
  pure (← xadd' one (e,i) (mkRawNatLit 1,1) zero, ← mkAppCS ``horner_atom #[e])

theorem subst_into_add {α} [Add α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t :=
by rw [prl, prr, prt]

theorem subst_into_mul {α} [Mul α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl * tr = t) : l * r = t :=
by rw [prl, prr, prt]

theorem subst_into_pow {α} [Monoid α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : (r : ℕ) = tr) (prt : tl ^ tr = t) : l ^ r = t :=
by rw [prl, prr, prt]

partial def eval (e : Expr) : RingM (HornerExpr × Expr) :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_,_,_,_,e₁,e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    let p ← mkAppM ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    pure (e', p)
  | (``HMul.hMul, #[_,_,_,_,e₁,e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalMul e₁' e₂'
    let p ← mkAppM ``subst_into_mul #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    return (e', p)
  | (``HPow.hPow, #[_,_,_,P,e₁,e₂]) => do
    -- let (e₂', p₂) ← lift $ norm_num.derive e₂ <|> refl_conv e₂,
    let (e₂', p₂) := (e₂, ← mkEqRefl e₂)
    match e₂'.numeral?, P.getAppFn with
    | some k, Expr.const ``Monoid.HPow _ _ => do
      let (e₁', p₁) ← eval e₁
      let (e', p') ← evalPow e₁' (e₂, k)
      let p ← mkAppM ``subst_into_pow #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
      return (e', p)
    | _, _ => evalAtom e
  | _ =>
    match e.numeral? with
    | some n => (const e n).reflConv
    | _ => evalAtom e

elab "ring" : tactic => liftMetaMAtMain fun g => do
  match (← instantiateMVars (← getMVarDecl g).type).getAppFnArgs with
  | (`Eq, #[ty, e₁, e₂]) =>
    let ((e₁', p₁), (e₂', p₂)) ← RingM.run ty $ do pure (← eval e₁, ← eval e₂)
    if ← isDefEq e₁' e₂' then
      assignExprMVar g (← mkEqTrans p₁ (← mkEqSymm p₂))
    else
      throwError "ring failed, ring expressions not equal: \n{← e₁'.pp}\n  !=\n{← e₂'.pp}"
  | _ => throwError "ring failed: not an equality"
