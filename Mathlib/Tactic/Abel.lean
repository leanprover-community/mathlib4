/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.GroupPower.Basic

/-!
# The `abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.

-/

open Lean Elab Meta Tactic
open Qq

/-- Construct the term of type `α` for a given natural number
(doing typeclass search for the `OfNat` instance required). -/
def _root_.Lean.Expr.ofNat (α : Expr) (n : ℕ) : MetaM Expr := do
  mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit n, none]

/-- Construct the term of type `α` for a given integer
(doing typeclass search for the `OfNat` and `Neg` instances required). -/
def _root_.Lean.Expr.ofInt (α : Expr) : ℤ → MetaM Expr
| Int.ofNat n => Expr.ofNat α n
| Int.negSucc n => do mkAppM ``Neg.neg #[← Expr.ofNat α (n+1)]

namespace Tactic
namespace Abel

initialize registerTraceClass `abel
initialize registerTraceClass `abel.detail

/-- The `Context` for a call to `abel`.

Stores a few options for this call, and caches some common subexpressions
such as typeclass instances and `0 : α`.
-/
structure Context where
  /-- TransparencyMode for comparing atoms -/
  red      : TransparencyMode
  /-- The type of the ambient additive commutative group or monoid. -/
  α        : Expr
  /-- The universe level for `α`. -/
  univ     : Level
  /-- The expression representing `0 : α`. -/
  α0       : Expr
  /-- Specify whether we are in an additive commutative group or an additive commutative monoid. -/
  is_group : Bool
  /-- The `AddCommGroup α` or `AddCommMonoid α` expression. -/
  inst     : Expr

/-- Populate a `context` object for evaluating `e`, up to reducibility level `red`. -/
def mkContext (red : TransparencyMode) (e : Expr) : MetaM Context := do
  let α ← inferType e
  let c ← synthInstance (← mkAppM ``AddCommMonoid #[α])
  let cg ← synthInstance? (← mkAppM ``AddCommGroup #[α])
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ u)) (← inferType α)
  let α0 ← Expr.ofNat α 0
  match cg with
  | (some cg) => return ⟨red, α, u, α0, true, cg⟩
  | _ => return ⟨red, α, u, α0, false, c⟩

/-- Apply the function `n : ∀ {α} [inst : AddWhatever α], _` to the
implicit parameters in the context, and the given list of arguments. -/
def Context.app (c : Context) (n : Name) (inst : Expr) : Array Expr → Expr :=
mkAppN (((@Expr.const n [c.univ]).app c.α).app inst)

/-- Apply the function `n : ∀ {α} [inst α], _` to the implicit parameters in the
context, and the given list of arguments.

Compared to `context.app`, this takes the name of the typeclass, rather than an
inferred typeclass instance.
-/
def Context.mkApp (c : Context) (n inst : Name) (l : Array Expr) : MetaM Expr := do
  return c.app n (← synthInstance ((Expr.const inst [c.univ]).app c.α)) l

/-- Add the letter "g" to the end of the name, e.g. turning `term` into `termg`.

This is used to choose between declarations taking `AddCommMonoid` and those
taking `AddCommGroup` instances.
-/
def add_g : Name → Name
| .str p s => .str p (s ++ "g")
| n => n

/-- Apply the function `n : ∀ {α} [add_comm_{monoid,group} α]` to the given
list of arguments.

Will use the `add_comm_{monoid,group}` instance that has been cached in the context.
-/
def Context.iapp (c : Context) (n : Name) : Array Expr → Expr :=
c.app (if c.is_group then add_g n else n) c.inst

/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative monoid. -/
def term {α} [AddCommMonoid α] (n : ℕ) (x a : α) : α := n • x + a
/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative group. -/
def termg {α} [AddCommGroup α] (n : ℤ) (x a : α) : α := n • x + a

/-- Evaluate a term with coefficient `n`, atom `x` and successor terms `a`. -/
def Context.mkTerm (c : Context) (n x a : Expr) : Expr := c.iapp ``term #[n, x, a]

/-- Interpret an integer as a coefficient to a term. -/
def Context.intToExpr (c : Context) (n : ℤ) : MetaM Expr :=
Expr.ofInt (mkConst (if c.is_group then ``Int else ``Nat) []) n

/-- A normal form for `abel`.
Expressions are represented as a list of terms of the form `e = n • x`,
where `n : ℤ` and `x` is an arbitrary element of the additive commutative monoid or group.
We explicitly track the `Expr` forms of `e` and `n`, even though they could be reconstructed,
for efficiency. -/
inductive NormalExpr : Type
| zero (e : Expr) : NormalExpr
| nterm (e : Expr) (n : Expr × ℤ) (x : Expr) (a : NormalExpr) : NormalExpr
deriving Inhabited

/-- Extract the expression from a normal form. -/
def NormalExpr.e : NormalExpr → Expr
| (NormalExpr.zero e) => e
| (NormalExpr.nterm e _ _ _) => e

instance : Coe NormalExpr Expr where coe := NormalExpr.e

/-- Construct the normal form representing a single term. -/
def NormalExpr.term' (c : Context) (n : Expr × ℤ) (x : Expr) (a : NormalExpr) :
  NormalExpr :=
NormalExpr.nterm (c.mkTerm n.1 x a) n x a

/-- Construct the normal form representing zero. -/
def NormalExpr.zero' (c : Context) : NormalExpr := NormalExpr.zero c.α0

open NormalExpr

theorem const_add_term {α} [AddCommMonoid α] (k n x a a') (h : k + a = a') :
    k + @term α _ n x a = term n x a' := by
  simp [h.symm, term, add_comm, add_assoc]

theorem const_add_termg {α} [AddCommGroup α] (k n x a a') (h : k + a = a') :
    k + @termg α _ n x a = termg n x a' := by
  simp [h.symm, termg, add_comm, add_assoc]

theorem term_add_const {α} [AddCommMonoid α] (n x a k a') (h : a + k = a') :
    @term α _ n x a + k = term n x a' := by
  simp [h.symm, term, add_assoc]

theorem term_add_constg {α} [AddCommGroup α] (n x a k a') (h : a + k = a') :
    @termg α _ n x a + k = termg n x a' := by
  simp [h.symm, termg, add_assoc]

theorem term_add_term {α} [AddCommMonoid α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n')
    (h₂ : a₁ + a₂ = a') : @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a' := by
  simp [h₁.symm, h₂.symm, term, add_nsmul]
  sorry -- TODO should be by `ac_refl`, or do it by hand.

theorem term_add_termg {α} [AddCommGroup α] (n₁ x a₁ n₂ a₂ n' a')
    (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a' := by
  -- TODO waiting on port of `Algebra.GroupPower.Lemmas` for `add_zsmul`
  -- simp [h₁.symm, h₂.symm, termg, add_zsmul]
  -- TODO then by `ac_refl`, or by hand
  sorry

theorem zero_term {α} [AddCommMonoid α] (x a) : @term α _ 0 x a = a := by
  simp [term, zero_nsmul, one_nsmul]

theorem zero_termg {α} [AddCommGroup α] (x a) : @termg α _ 0 x a = a := by
  -- TODO waiting on port of `Algebra.GroupPower.Lemmas` for `zero_zsmul`
  -- simp [termg, zero_zsmul]
  sorry

/--
Intepret the sum of two expressions in `abel`'s normal form.
-/
partial def eval_add (c : Context) : NormalExpr → NormalExpr → TacticM (NormalExpr × Expr)
| (zero _), e₂ => do
  let p ← mkAppM ``zero_add #[e₂]
  return (e₂, p)
| e₁, (zero _) => do
  let p ← mkAppM ``add_zero #[e₁]
  return (e₁, p)
| he₁@(nterm e₁ n₁ x₁ a₁), he₂@(nterm e₂ n₂ x₂ a₂) => do
  if (← withTransparency c.red (isDefEq x₁ x₂)) then do
    let ⟨n', h₁, _⟩ ← Mathlib.Meta.NormNum.eval (← mkAppM ``HAdd.hAdd #[n₁.1, n₂.1])
    let (a', h₂) ← eval_add c a₁ a₂
    let k := n₁.2 + n₂.2
    let p₁ := c.iapp ``term_add_term #[n₁.1, x₁, a₁, n₂.1, a₂, n', a', h₁.getD (←mkEqRefl n'), h₂]
    if k = 0 then do
      let p ← mkEqTrans p₁ (c.iapp ``zero_term #[x₁, a'])
      return (a', p)
    else return (term' c (n', k) x₁ a', p₁)
  else
    if Expr.quickLt x₁ x₂ then do -- Since we don't care about the ordering, use `Expr.quickLt`
      let (a', h) ← eval_add c a₁ he₂
      return (term' c n₁ x₁ a', c.iapp ``term_add_const #[n₁.1, x₁, a₁, e₂, a', h])
    else do
      let (a', h) ← eval_add c he₁ a₂
      return (term' c n₂ x₂ a', c.iapp ``const_add_term #[e₁, n₂.1, x₂, a₂, a', h])

theorem term_neg {α} [AddCommGroup α] (n x a n' a')
  (h₁ : -n = n') (h₂ : -a = a') :
  -@termg α _ n x a = termg n' x a' :=
by simp [h₂.symm, h₁.symm, termg]; sorry

/--
Interpret a negated expression in `abel`'s normal form.
-/
def eval_neg (c : Context) : NormalExpr → TacticM (NormalExpr × Expr)
| (zero _) => do
  let p ← c.mkApp ``neg_zero ``NegZeroClass #[]
  return (zero' c, p)
| (nterm _ n x a) => do
  let ⟨n', h₁, _⟩ ← Mathlib.Meta.NormNum.eval (← mkAppM ``Neg.neg #[n.1])
  let (a', h₂) ← eval_neg c a
  return (term' c (n', -n.2) x a',
    c.app ``term_neg c.inst #[n.1, x, a, n', a', h₁.getD (←mkEqRefl n'), h₂])

/-- A synonym for `•`, used internally in `abel`. -/
def smul {α} [AddCommMonoid α] (n : ℕ) (x : α) : α := n • x
/-- A synonym for `•`, used internally in `abel`. -/
def smulg {α} [AddCommGroup α] (n : ℤ) (x : α) : α := n • x

theorem zero_smul {α} [AddCommMonoid α] (c) : smul c (0 : α) = 0 := by
  simp [smul, nsmul_zero]

theorem zero_smulg {α} [AddCommGroup α] (c) : smulg c (0 : α) = 0 := by
  -- TODO waiting for port of Algebra.GroupPower.Basic for `zsmul_zero`
  -- simp [smulg, zsmul_zero]
  sorry

theorem term_smul {α} [AddCommMonoid α] (c n x a n' a')
  (h₁ : c * n = n') (h₂ : smul c a = a') :
  smul c (@term α _ n x a) = term n' x a' := by
  -- TODO waiting for port of Algebra.GroupPower.Basic for `nsmul_add` and `mul_nsmul`
  -- simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul]
  sorry

theorem term_smulg {α} [AddCommGroup α] (c n x a n' a')
  (h₁ : c * n = n') (h₂ : smulg c a = a') :
  smulg c (@termg α _ n x a) = termg n' x a' := by
  -- TODO waiting for port of Algebra.GroupPower.Lemmas for `zsmul_add` and `mul_zsmul`
  -- simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]
  sorry

/--
Auxiliary function for `eval_smul'`.
-/
def eval_smul (c : Context) (k : Expr × ℤ) : NormalExpr → TacticM (NormalExpr × Expr)
| (zero _) => return (zero' c, c.iapp ``zero_smul #[k.1])
| (nterm _ n x a) => do
  let ⟨n', h₁, _⟩ ← Mathlib.Meta.NormNum.eval (← mkAppM ``HMul.hMul #[k.1, n.1])
  let (a', h₂) ← eval_smul c k a
  return (term' c (n', k.2 * n.2) x a',
    c.iapp ``term_smul #[k.1, n.1, x, a, n', a', h₁.getD (← mkEqRefl n'), h₂])

theorem term_atom {α} [AddCommMonoid α] (x : α) : x = term 1 x 0 := by
  simp [term]

theorem term_atomg {α} [AddCommGroup α] (x : α) : x = termg 1 x 0 := by
  -- TODO waiting for port of Algebra.GroupPower.Basic for `one_zsmul`
  simp [termg]
  sorry

/-- Interpret an expression as an atom for `abel`'s normal form. -/
def eval_atom (c : Context) (e : Expr) : TacticM (NormalExpr × Expr) := do
  let n1 ← c.intToExpr 1
  return (term' c (n1, 1) e (zero' c), c.iapp ``term_atom #[e])

theorem unfold_sub {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c) : a - b = c :=
by rw [sub_eq_add_neg, h]

theorem unfold_smul {α} [AddCommMonoid α] (n) (x y : α)
  (h : smul n x = y) : n • x = y := h

theorem unfold_smulg {α} [AddCommGroup α] (n : ℕ) (x y : α)
  (h : smulg (Int.ofNat n) x = y) : (n : ℤ) • x = y := h

theorem unfold_zsmul {α} [AddCommGroup α] (n : ℤ) (x y : α)
  (h : smulg n x = y) : n • x = y := h

lemma subst_into_smul {α} [AddCommMonoid α]
  (l r tl tr t) (prl : l = tl) (prr : r = tr)
  (prt : @smul α _ tl tr = t) : smul l r = t :=
by simp [prl, prr, prt]

lemma subst_into_smulg {α} [AddCommGroup α]
  (l r tl tr t) (prl : l = tl) (prr : r = tr)
  (prt : @smulg α _ tl tr = t) : smulg l r = t :=
by simp [prl, prr, prt]

lemma subst_into_smul_upcast {α} [AddCommGroup α]
  (l r tl zl tr t) (prl₁ : l = tl) (prl₂ : ↑tl = zl) (prr : r = tr)
  (prt : @smulg α _ zl tr = t) : smul l r = t := by
  -- TODO waiting for fixes to Algebra.Group.Defs (supposedly ported!) for `coe_nat_zsmul`
  -- simp [← prt, prl₁, ← prl₂, prr, smul, smulg]
  sorry

lemma subst_into_add {α} [AddCommMonoid α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t :=
by rw [prl, prr, prt]

lemma subst_into_addg {α} [AddCommGroup α] (l r tl tr t)
  (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t :=
by rw [prl, prr, prt]

lemma subst_into_negg {α} [AddCommGroup α] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t :=
by simp [pra, prt]

/-- Normalize a term `orig` of the form `smul e₁ e₂` or `smulg e₁ e₂`.
  Normalized terms use `smul` for monoids and `smulg` for groups,
  so there are actually four cases to handle:
  * Using `smul` in a monoid just simplifies the pieces using `subst_into_smul`
  * Using `smulg` in a group just simplifies the pieces using `subst_into_smulg`
  * Using `smul a b` in a group requires converting `a` from a nat to an int and
    then simplifying `smulg ↑a b` using `subst_into_smul_upcast`
  * Using `smulg` in a monoid is impossible (or at least out of scope),
    because you need a group argument to write a `smulg` term -/
def eval_smul' (c : Context) (eval : Expr → TacticM (NormalExpr × Expr))
    (is_smulg : Bool) (orig e₁ e₂ : Expr) : TacticM (NormalExpr × Expr) := do
  trace[abel] "Calling NormNum on {e₁}"
  let ⟨e₁', p₁, _⟩ ← try Mathlib.Meta.NormNum.eval e₁
    catch _ => pure { expr := e₁ }
  let p₁ := p₁.getD (← mkEqRefl e₁') -- FIXME does this always run??
  match Mathlib.Meta.NormNum.isIntLit e₁' with
  | some n => do
    let (e₂', p₂) ← eval e₂
    if c.is_group = is_smulg then do
      let (e', p) ← eval_smul c (e₁', n) e₂'
      return (e', c.iapp ``subst_into_smul #[e₁, e₂, e₁', e₂', e', p₁, p₂, p])
    else do
      if ¬ c.is_group then throwError "Doesn't make sense to us `smulg` in a monoid. "
      -- We are multiplying by a natural number in an additive group.
      let zl ← Expr.ofInt q(ℤ) n
      let p₁' ← mkEqRefl zl
      let (e', p) ← eval_smul c (zl, n) e₂'
      return (e', c.app ``subst_into_smul_upcast c.inst #[e₁, e₂, e₁', zl, e₂', e', p₁, p₁', p₂, p])
  | none => eval_atom c orig

/-- Evaluate an expression into its `abel` normal form,
by recursing into subexpressions. -/
partial def eval (c : Context) (e : Expr) : TacticM (NormalExpr × Expr) := do
  trace[abel.detail] "running eval on {e}"
  trace[abel.detail] "getAppFnArgs: {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (e₁', p₁) ← eval c e₁
    let (e₂', p₂) ← eval c e₂
    let (e', p') ← eval_add c e₁' e₂'
    return (e', c.iapp ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p'])
  | (``HSub.hSub, #[_, _, _ ,_, e₁, e₂]) => do
    let e₂' ← mkAppM ``Neg.neg #[e₂]
    let e ← mkAppM ``HAdd.hAdd #[e₁, e₂']
    let (e', p) ← eval c e
    let p' ← c.mkApp ``unfold_sub ``SubtractionMonoid #[e₁, e₂, e', p]
    return (e', p')
  | (``Neg.neg, #[_, _, e]) => do
    let (e₁, p₁) ← eval c e
    let (e₂, p₂) ← eval_neg c e₁
    return (e₂, c.iapp `Tactic.Abel.subst_into_neg #[e, e₁, e₂, p₁, p₂])
  | (`AddMonoid.nsmul, #[_, _, e₁, e₂]) => do
    let n ← if c.is_group then mkAppM ``Int.ofNat #[e₁] else pure e₁
    let (e', p) ← eval c $ c.iapp ``smul #[n, e₂]
    return (e', c.iapp ``unfold_smul #[e₁, e₂, e', p])
  | (``SubNegMonoid.zsmul, #[_, _, e₁, e₂]) => do
      if ¬ c.is_group then failure
      let (e', p) ← eval c $ c.iapp ``smul #[e₁, e₂]
      return (e', c.app ``unfold_zsmul c.inst #[e₁, e₂, e', p])
  | (``HasSmul.smul, #[.const ``Int _, _, _, e₁, e₂]) =>
    eval_smul' c (eval c) true e e₁ e₂
  | (``HasSmul.smul, #[.const ``Nat _, _, _, e₁, e₂]) =>
    eval_smul' c (eval c) false e e₁ e₂
  | (``smul, #[_, _, e₁, e₂]) => eval_smul' c (eval c) false e e₁ e₂
  | (``smulg, #[_, _, e₁, e₂]) => eval_smul' c (eval c) true e e₁ e₂
  | (``OfNat.ofNat, #[_, .lit (.natVal 0), _])
  | (``Zero.zero, #[_, _]) =>
     if ← isDefEq e c.α0 then
       pure (zero' c, ← mkEqRefl c.α0)
      else
        eval_atom c e
  | _ => eval_atom c e

end Abel

open Tactic.Abel

/-- Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.
-/
syntax (name := abel1) "abel1" : tactic
@[inherit_doc abel1]
syntax (name := abel1!) "abel1!" : tactic

/-- The `abel1` tactic, which solves equations in the language of commutative additive groups
(or monoids). -/
def abel1Impl (tm : TransparencyMode := .default) : TacticM Unit := do
  match (←getMainTarget).getAppFnArgs with
  | (``Eq, #[_, e₁, e₂]) =>
    trace[abel] "running on an equality `{e₁} = {e₂}`."
    let c ← mkContext tm e₁
    let (e₁', p₁) ← eval c e₁
    trace[abel] "found `{p₁}`, a proof that `{e₁} = {e₁'.e}`"
    let (e₂', p₂) ← eval c e₂
    trace[abel] "found `{p₂}`, a proof that `{e₂} = {e₂'.e}`"
    if ← isDefEq e₁' e₂' then
      trace[abel] "verified that the simplified forms are identical"
      closeMainGoal (← mkEqTrans p₁ (← mkEqSymm p₂))
    else
      throwError "abel1 found that the two sides were not equal"
  | _ => throwError "abel1 requires an equality goal"

elab_rules : tactic | `(tactic| abel1) => abel1Impl .reducible
elab_rules : tactic | `(tactic| abel1!) => abel1Impl .default

-- TODO finish porting `abel`, rather than just `abel1`.
