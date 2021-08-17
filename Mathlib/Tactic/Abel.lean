/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Aurélien Saue
-/
import Lean.Elab.Tactic.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ToExprInt

/-!
# `ring`

Evaluate expressions in the language of commutative (semi)rings.
Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .
-/

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

namespace Tactic
namespace Abel

/-- This cache contains data required by the `ring` tactic during execution. -/
structure Cache :=
  α : Expr
  univ : Level

structure State :=
  atoms : Array Expr := #[]
  numAtoms : Nat     := 0

/-- The monad that `ring` works in. This is a reader monad containing a cache and
the list of atoms-up-to-defeq encountered thus far, used for atom sorting. -/
abbrev AbelM := ReaderT Cache $ StateRefT State TacticM

def run (e : Expr) {α} (m : AbelM α): TacticM α := do
  let ty ← inferType e
  let u ← getLevel ty
  (m {α := ty, univ := u}).run' {} --TODO: define isGrp properly

/-- Get the index corresponding to an atomic expression, if it has already been encountered, or
put it in the list of atoms and return the new index, otherwise. -/
def addAtom (e : Expr) : AbelM Nat := do
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

@[reducible] def LC {α} [AddCommGroup α] (n : ℤ) (a b : α) := SubNegMonoid.gsmul n a + b

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
inductive GrpExpr : Type
| zero (e : Expr) : GrpExpr --TODO : coeff in ℚ
| xadd (e : Expr) (n : Expr × ℤ) (x : Expr × ℕ) (b : GrpExpr) : GrpExpr -- n • x + b

variable {A : Type}

instance : Inhabited GrpExpr := ⟨GrpExpr.zero (mkRawNatLit 0)⟩

namespace GrpExpr

/-- Get the expression corresponding to a `HornerExpr`. This can be calculated recursively from
the structure, but we cache the exprs in all subterms so that this function can be computed in
constant time. -/
def e : GrpExpr → Expr
| (GrpExpr.zero e) => e
| (GrpExpr.xadd e _ _ _) => e

instance : Coe GrpExpr Expr := ⟨e⟩

/-- Is this expr the constant `0`? -/
def isZero : GrpExpr → Bool
| (GrpExpr.zero _) => true
| _ => false

/-- Construct a `xadd` node -/
def xadd' (n : Expr × ℤ) (x : Expr × ℕ) (b : GrpExpr) : AbelM GrpExpr := do
  xadd (← mkAppM ``LC #[n.1, x.1, b]) n x b

/-- Reflexivity conversion for a `HornerExpr`. -/
def reflConv (e : GrpExpr) : AbelM (GrpExpr × Expr) := do (e, ← mkEqRefl e)

/-- Pretty printer for `horner_expr`. -/
def pp : GrpExpr → TacticM Format
| (zero e) => do
  let pe ← PrettyPrinter.ppExpr Name.anonymous [] e
  return "[" ++ pe ++ "]"
| (xadd e (_, n) x b) => do
  let pb ← b.pp
  let px ← PrettyPrinter.ppExpr Name.anonymous [] x.1
  return "(" ++ toString n ++ "•" ++ px ++ " + " ++ pb


end GrpExpr

open GrpExpr

theorem zero_LC {α} [AddCommGroup α] (x b) :
  @LC α _ 0 x b = b :=
by simp [LC, SubNegMonoid.gsmul_zero']

-- theorem horner_horner {α} [CommSemiring α] (a₁ x n₁ n₂ b n')
--   (h : n₁ + n₂ = n') :
--   @horner α _ (horner a₁ x n₁ 0) x n₂ b = horner a₁ x n' b :=
-- by simp [h.symm, horner, pow_add, mul_assoc]

/-- Evaluate `LC n a b` where `b` is already in normal form. -/
def evalLC : Expr × ℤ → Expr × ℕ → GrpExpr → AbelM (GrpExpr × Expr)
| n, x, b => do (← xadd' n x b).reflConv

theorem const_add_LC {α} [AddCommGroup α] (k n x b b') (h : k + b = b') :
  k + @LC α _ n x b = LC n x b' :=
by simp [LC, h.symm, add_comm k, add_assoc]

theorem LC_add_const {α} [AddCommGroup α] (n x b k b') (h : b + k = b') :
  @LC α _ n x b + k = LC n x b' :=
by simp [LC, h.symm, add_assoc]

/-- Need gsmul_add to prove this -/
theorem LC_add_LC {α} [AddCommGroup α] (n₁ x b₁ n₂ b₂ k b')
  (h₁ : n₁ + n₂ = k) (h₂ : b₁ + b₂ = b') :
  @LC α _ n₁ x b₁ + LC n₂ x b₂ = LC k x b' :=
sorry

/-- Need gsmul_add to prove this -/
theorem LC_add_LC_zero {α} [AddCommGroup α] (x n₁ b₁ n₂ b₂ b')
  (h₁ : (n₁ : ℤ) + n₂ = 0) (h₂ : b₁ + b₂ = b') :
  @LC α _ n₁ x b₁ + LC n₂ x b₂ = b' :=
sorry

-- theorem horner_add_horner_gt {α} [CommSemiring α] (a₁ x n₁ b₁ a₂ n₂ b₂ k a' b')
--   (h₁ : n₂ + k = n₁) (h₂ : (horner a₁ x k 0 + a₂ : α) = a') (h₃ : b₁ + b₂ = b') :
--   @horner α _ a₁ x n₁ b₁ + horner a₂ x n₂ b₂ = horner a' x n₂ b' :=
-- by
--   rw [← h₁, ← h₂, ← h₃]
--   simp [horner, add_mul, mul_assoc, (pow_add x k n₂).symm, add_comm k, @add_comm α _, @add_assoc α _]

-- theorem horner_add_horner_eq {α} [CommSemiring α] (a₁ x n b₁ a₂ b₂ a' b' t)
--   (h₁ : a₁ + a₂ = a') (h₂ : b₁ + b₂ = b') (h₃ : horner a' x n b' = t) :
--   @horner α _ a₁ x n b₁ + horner a₂ x n b₂ = t :=
-- by
--   rw [← h₃, ← h₁, ← h₂]
--   simp [horner, add_mul, @add_comm α _, @add_assoc α _]

partial def evalAdd : GrpExpr → GrpExpr → AbelM (GrpExpr × Expr)
| (zero e₁), (zero e₂) => do (zero e₁, ← mkAppM ``add_zero #[e₁])
| he₁@(zero e₁), he₂@(xadd e₂ n x b) => do
  let p ← mkAppM ``zero_add #[e₂]
  return (he₂, p)
| he₁@(xadd e₁ n x b), he₂@(zero e₂) => do
  let p ← mkAppM ``add_zero #[e₁]
  return (he₁, p)
| he₁@(xadd e₁ n₁ x₁ b₁), he₂@(xadd e₂ n₂ x₂ b₂) => do
  let c ← get
  if x₁.2 < x₂.2 then
    let (b', h) ← evalAdd b₁ he₂
    return (← xadd' n₁ x₁ b',
      ← mkAppM ``LC_add_const #[n₁.1, x₁.1, b₁, e₂, b', h])
  else if x₁.2 ≠ x₂.2 then
    let (b', h) ← evalAdd he₁ b₂
    return (← xadd' n₂ x₂ b',
      ← mkAppM ``const_add_LC #[e₁, n₂.1, x₂.1, b₂, b', h])
  do
    let (b', hb) ← evalAdd b₁ b₂
    let k := n₁.2 + n₂.2
    if k = 0 then
      return (b', ← mkAppM ``LC_add_LC_zero #[x₁.1, n₁.1, b₁, n₂.1, b₂, b',
        ← mkEqRefl (toExpr (0 : ℤ)), hb])
    else
      let ke ← toExpr k
      return (← xadd' (ke, k) x₁ b',
        ← mkAppM ``LC_add_LC #[n₁.1, x₁.1, b₁, n₂.1, b₂, ke, b', ← mkEqRefl ke, hb])

/-- Need gsmul_add to prove this -/
theorem gsmul_LC {α} [AddCommGroup α] (c x n b n' b')
   (h₁ : c * n = n') (h₂ : SubNegMonoid.gsmul c b = b') :
   SubNegMonoid.gsmul c (@LC α _ n x b) = LC n' x b' :=
sorry

-- theorem horner_const_mul {α} [CommSemiring α] (c a x n b a' b')
--   (h₁ : c * a = a') (h₂ : c * b = b') :
--   c * @horner α _ a x n b = horner a' x n b' :=
-- by simp [h₂.symm, h₁.symm, horner, mul_add, mul_assoc]

-- theorem horner_mul_const {α} [CommSemiring α] (a x n b c a' b')
--   (h₁ : a * c = a') (h₂ : b * c = b') :
--   @horner α _ a x n b * c = horner a' x n b' :=
-- by simp [h₂.symm, h₁.symm, horner, add_mul, @mul_right_comm α _]

lemma gsmul_zero {A} [AddCommGroup A] (n : ℤ) :
  SubNegMonoid.gsmul n (0 : A) = 0 := sorry

/-- Evaluate `k * a` where `k` is a rational numeral and `a` is in normal form. -/
def evalGSmul (c : Expr × ℤ) : GrpExpr → AbelM (GrpExpr × Expr)
| (zero e) => do
  return (zero e, ← mkAppOptM ``gsmul_zero #[(← read).α, none, c.1])
| (xadd e n x b) => do
  let (b', hb) ← evalGSmul c b
  let n' := c.2 * n.2
  let n'e := toExpr n'
  return (← xadd' (n'e, n') x b', ← mkAppM ``gsmul_LC #[c.1, x.1, n.1, b, n'e, b', ← mkEqRefl n'e, hb])

lemma neg_zero {A : Type u} [AddGroup A] : - (0 : A) = 0 := sorry

theorem neg_LC {α} [AddCommGroup α] (x n b n' b')
   (h₁ : -n = n') (h₂ : -(b : α) = b') :
   -(@LC α _ n x b) = LC n' x b' := sorry

def evalNeg : GrpExpr → AbelM (GrpExpr × Expr)
| (zero e) => do
  return (zero e, ← mkAppOptM ``neg_zero #[(← read).α, none])
| (xadd e n x b) => do
  let (b', hb) ← evalNeg b
  let n' := - n.2
  let n'e := toExpr n'
  return (← xadd' (n'e, n') x b', ← mkAppM ``neg_LC #[x.1, n.1, b, n'e, b', ← mkEqRefl n'e, hb])

theorem sub_LC {α} [AddCommGroup α] (a b b' c : α)
  (h₁ : -b = b') (h₂ : a + b' = c) :
  a - b = c :=
sorry

def evalSub : GrpExpr → GrpExpr → AbelM (GrpExpr × Expr)
| a, b => do
  let (b', hb) ← evalNeg b
  let (c, hc) ← evalAdd a b'
  (c, ← mkAppM ``sub_LC #[a, b, b', c, hb, hc])

theorem LC_atom {α} [AddCommGroup α] (x : α) : x = LC 1 x 0 := sorry

/-- Evaluate `a` where `a` is an atom. -/
def evalAtom (e : Expr) : AbelM (GrpExpr × Expr) := do
  let i ← addAtom e
  let zero ← zero (toExpr 0)
  let one ← (← mkAppOptM ``OfNat.ofNat #[mkConst `Int, mkRawNatLit 1, none])
  return (← xadd' (one, 1) (e,i) (GrpExpr.zero (← mkAppOptM ``Zero.zero #[(← read).α, none])), ← mkAppM ``LC_atom #[e])

theorem subst_into_add {α} [Add α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t :=
by rw [prl, prr, prt]

theorem subst_into_gsmul {α} [SubNegMonoid α] (r l tr tl t)
  (prr : (r : ℤ) = tr) (prl : (l : α) = tl) (prt : SubNegMonoid.gsmul tr tl = t) :
  SubNegMonoid.gsmul r l = t :=
by rw [prl, prr, prt]

theorem subst_into_neg {α} [Neg α] (l tl t)
  (prl : (l : α) = tl) (prt : - tl = t) :
  -l = t :=
by rw [prl, prt]

theorem subst_into_sub {α} [Sub α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl - tr = t) : l - r = t :=
by rw [prl, prr, prt]

unsafe def eval (e : Expr) : AbelM (GrpExpr × Expr) :=
  match e.getAppFnAndArgs with
  | some (``HAdd.hAdd, #[_,_,_,_,e₁,e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    let p ← mkAppM ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    (e',p)
  | some (``HSub.hSub, #[_,_,_,_,e₁,e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalSub e₁' e₂'
    let p ← mkAppM ``subst_into_sub #[e₁, e₂, e₁', e₂', e', p₁, p₂, p']
    (e',p)
  | some (``SubNegMonoid.gsmul, #[_,_,e₁,e₂]) => do
    let n : Option ℤ ← (return (some (← Lean.Elab.Term.evalExpr ℤ `Int e₁)) <|> return none)
    match n with
    | some k =>
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalGSmul (e₁, k) e₂'
    let p ← mkAppM ``subst_into_gsmul #[e₁, e₂, toExpr k, e₂', e', ← mkEqRefl (toExpr k), p₂, p']
    return (e', p)
    | _ => evalAtom e
  | some (``Neg.neg, #[_,_,e₁]) => do
    let (e₁', p₁) ← eval e₁
    let (e', p') ← evalNeg e₁'
    let p ← mkAppM ``subst_into_neg #[e₁, e₁', e', p₁, p']
    (e', p)
  | some (``Zero.zero, #[_, h]) => do
    (GrpExpr.zero e, ← mkEqRefl e)
  | some (``OfNat.ofNat, #[_, n, _]) =>
    match n.numeral? with
    | some 0 => do (GrpExpr.zero e, ← mkEqRefl e)
    | _ => evalAtom e
  | _ => evalAtom e

end Abel
end Tactic

namespace Lean

open Tactic.Abel

syntax (name := Parser.Tactic.abel) "abel" : tactic

@[tactic abel] unsafe def evalAbel : Tactic := fun stx => do
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
  | _ => throwError "failed: not an equality"

end Lean

variable {α : Type} [AddCommGroup α]

instance : AddGroup α := inferInstance

example (x y : α) : x + y = y + x := by abel

example (x y : α) : SubNegMonoid.gsmul 2 x + y = y + x + x :=
by abel

example (x y : α) : -y + x = x - y := by abel

example (x : α) : x - x = (Zero.zero) := by abel

example (x y : α) : SubNegMonoid.gsmul (-3) x + y - y + x +
  SubNegMonoid.gsmul 2 x = 0 := by abel
