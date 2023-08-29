/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Scott Morrison
-/
import Mathlib.Tactic.NormNum
import Mathlib.Util.AtomM
import Mathlib.Data.Int.Basic

/-!
# The `abel` tactic

Evaluate expressions in the language of additive, commutative monoids and groups.

-/

set_option autoImplicit true

namespace Mathlib.Tactic.Abel
open Lean Elab Meta Tactic Qq

initialize registerTraceClass `abel
initialize registerTraceClass `abel.detail

/-- The `Context` for a call to `abel`.

Stores a few options for this call, and caches some common subexpressions
such as typeclass instances and `0 : α`.
-/
structure Context where
  /-- The type of the ambient additive commutative group or monoid. -/
  α       : Expr
  /-- The universe level for `α`. -/
  univ    : Level
  /-- The expression representing `0 : α`. -/
  α0      : Expr
  /-- Specify whether we are in an additive commutative group or an additive commutative monoid. -/
  isGroup : Bool
  /-- The `AddCommGroup α` or `AddCommMonoid α` expression. -/
  inst    : Expr

/-- Populate a `context` object for evaluating `e`. -/
def mkContext (e : Expr) : MetaM Context := do
  let α ← inferType e
  let c ← synthInstance (← mkAppM ``AddCommMonoid #[α])
  let cg ← synthInstance? (← mkAppM ``AddCommGroup #[α])
  let u ← mkFreshLevelMVar
  _ ← isDefEq (.sort (.succ u)) (← inferType α)
  let α0 ← Expr.ofNat α 0
  match cg with
  | some cg => return ⟨α, u, α0, true, cg⟩
  | _ => return ⟨α, u, α0, false, c⟩

/-- The monad for `Abel` contains, in addition to the `AtomM` state,
some information about the current type we are working over, so that we can consistently
use group lemmas or monoid lemmas as appropriate. -/
abbrev M := ReaderT Context AtomM

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
def addG : Name → Name
  | .str p s => .str p (s ++ "g")
  | n => n

/-- Apply the function `n : ∀ {α} [AddComm{Monoid,Group} α]` to the given list of arguments.

Will use the `AddComm{Monoid,Group}` instance that has been cached in the context.
-/
def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app (if c.isGroup then addG n else n) c.inst xs

/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative monoid. -/
def term {α} [AddCommMonoid α] (n : ℕ) (x a : α) : α := n • x + a
/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative group. -/
def termg {α} [AddCommGroup α] (n : ℤ) (x a : α) : α := n • x + a

/-- Evaluate a term with coefficient `n`, atom `x` and successor terms `a`. -/
def mkTerm (n x a : Expr) : M Expr := iapp ``term #[n, x, a]

/-- Interpret an integer as a coefficient to a term. -/
def intToExpr (n : ℤ) : M Expr := do
  Expr.ofInt (mkConst (if (← read).isGroup then ``Int else ``Nat) []) n

/-- A normal form for `abel`.
Expressions are represented as a list of terms of the form `e = n • x`,
where `n : ℤ` and `x` is an arbitrary element of the additive commutative monoid or group.
We explicitly track the `Expr` forms of `e` and `n`, even though they could be reconstructed,
for efficiency. -/
inductive NormalExpr : Type
  | zero (e : Expr) : NormalExpr
  | nterm (e : Expr) (n : Expr × ℤ) (x : ℕ × Expr) (a : NormalExpr) : NormalExpr
  deriving Inhabited

/-- Extract the expression from a normal form. -/
def NormalExpr.e : NormalExpr → Expr
  | .zero e => e
  | .nterm e .. => e

instance : Coe NormalExpr Expr where coe := NormalExpr.e

/-- Construct the normal form representing a single term. -/
def NormalExpr.term' (n : Expr × ℤ) (x : ℕ × Expr) (a : NormalExpr) : M NormalExpr :=
  return .nterm (← mkTerm n.1 x.2 a) n x a

/-- Construct the normal form representing zero. -/
def NormalExpr.zero' : M NormalExpr := return NormalExpr.zero (← read).α0

open NormalExpr

theorem const_add_term {α} [AddCommMonoid α] (k n x a a') (h : k + a = a') :
    k + @term α _ n x a = term n x a' := by
  simp [h.symm, term, add_comm, add_assoc]
  -- 🎉 no goals

theorem const_add_termg {α} [AddCommGroup α] (k n x a a') (h : k + a = a') :
    k + @termg α _ n x a = termg n x a' := by
  simp [h.symm, termg, add_comm, add_assoc]
  -- 🎉 no goals

theorem term_add_const {α} [AddCommMonoid α] (n x a k a') (h : a + k = a') :
    @term α _ n x a + k = term n x a' := by
  simp [h.symm, term, add_assoc]
  -- 🎉 no goals

theorem term_add_constg {α} [AddCommGroup α] (n x a k a') (h : a + k = a') :
    @termg α _ n x a + k = termg n x a' := by
  simp [h.symm, termg, add_assoc]
  -- 🎉 no goals

theorem term_add_term {α} [AddCommMonoid α] (n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n')
    (h₂ : a₁ + a₂ = a') : @term α _ n₁ x a₁ + @term α _ n₂ x a₂ = term n' x a' := by
  simp [h₁.symm, h₂.symm, term, add_nsmul, add_assoc, add_left_comm]
  -- 🎉 no goals

theorem term_add_termg {α} [AddCommGroup α] (n₁ x a₁ n₂ a₂ n' a')
    (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') :
    @termg α _ n₁ x a₁ + @termg α _ n₂ x a₂ = termg n' x a' := by
  simp [h₁.symm, h₂.symm, termg, add_zsmul]
  -- ⊢ n₁ • x + a₁ + (n₂ • x + a₂) = n₁ • x + n₂ • x + (a₁ + a₂)
  exact add_add_add_comm (n₁ • x) a₁ (n₂ • x) a₂
  -- 🎉 no goals

theorem zero_term {α} [AddCommMonoid α] (x a) : @term α _ 0 x a = a := by
  simp [term, zero_nsmul, one_nsmul]
  -- 🎉 no goals

theorem zero_termg {α} [AddCommGroup α] (x a) : @termg α _ 0 x a = a := by
  simp [termg, zero_zsmul]
  -- 🎉 no goals

/--
Interpret the sum of two expressions in `abel`'s normal form.
-/
partial def evalAdd : NormalExpr → NormalExpr → M (NormalExpr × Expr)
  | zero _, e₂ => do
    let p ← mkAppM ``zero_add #[e₂]
    return (e₂, p)
  | e₁, zero _ => do
    let p ← mkAppM ``add_zero #[e₁]
    return (e₁, p)
  | he₁@(nterm e₁ n₁ x₁ a₁), he₂@(nterm e₂ n₂ x₂ a₂) => do
    if x₁.1 = x₂.1 then
      let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``HAdd.hAdd #[n₁.1, n₂.1])
      let (a', h₂) ← evalAdd a₁ a₂
      let k := n₁.2 + n₂.2
      let p₁ ← iapp ``term_add_term
        #[n₁.1, x₁.2, a₁, n₂.1, a₂, n'.expr, a', ← n'.getProof, h₂]
      if k = 0 then do
        let p ← mkEqTrans p₁ (← iapp ``zero_term #[x₁.2, a'])
        return (a', p)
      else return (← term' (n'.expr, k) x₁ a', p₁)
    else if x₁.1 < x₂.1 then do
      let (a', h) ← evalAdd a₁ he₂
      return (← term' n₁ x₁ a', ← iapp ``term_add_const #[n₁.1, x₁.2, a₁, e₂, a', h])
    else do
      let (a', h) ← evalAdd he₁ a₂
      return (← term' n₂ x₂ a', ← iapp ``const_add_term #[e₁, n₂.1, x₂.2, a₂, a', h])

theorem term_neg {α} [AddCommGroup α] (n x a n' a')
    (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a' := by
  simp [h₂.symm, h₁.symm, termg]; exact add_comm _ _
  -- ⊢ -a + -(n • x) = -(n • x) + -a
                                  -- 🎉 no goals

/--
Interpret a negated expression in `abel`'s normal form.
-/
def evalNeg : NormalExpr → M (NormalExpr × Expr)
  | (zero _) => do
    let p ← (← read).mkApp ``neg_zero ``NegZeroClass #[]
    return (← zero', p)
  | (nterm _ n x a) => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``Neg.neg #[n.1])
    let (a', h₂) ← evalNeg a
    return (← term' (n'.expr, -n.2) x a',
      (← read).app ``term_neg (← read).inst #[n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])

/-- A synonym for `•`, used internally in `abel`. -/
def smul {α} [AddCommMonoid α] (n : ℕ) (x : α) : α := n • x
/-- A synonym for `•`, used internally in `abel`. -/
def smulg {α} [AddCommGroup α] (n : ℤ) (x : α) : α := n • x

theorem zero_smul {α} [AddCommMonoid α] (c) : smul c (0 : α) = 0 := by
  simp [smul, nsmul_zero]
  -- 🎉 no goals

theorem zero_smulg {α} [AddCommGroup α] (c) : smulg c (0 : α) = 0 := by
  simp [smulg, zsmul_zero]
  -- 🎉 no goals

theorem term_smul {α} [AddCommMonoid α] (c n x a n' a')
  (h₁ : c * n = n') (h₂ : smul c a = a') :
  smul c (@term α _ n x a) = term n' x a' := by
  simp [h₂.symm, h₁.symm, term, smul, nsmul_add, mul_nsmul']
  -- 🎉 no goals

theorem term_smulg {α} [AddCommGroup α] (c n x a n' a')
  (h₁ : c * n = n') (h₂ : smulg c a = a') :
  smulg c (@termg α _ n x a) = termg n' x a' := by
  simp [h₂.symm, h₁.symm, termg, smulg, zsmul_add, mul_zsmul]
  -- 🎉 no goals

/--
Auxiliary function for `evalSMul'`.
-/
def evalSMul (k : Expr × ℤ) : NormalExpr → M (NormalExpr × Expr)
  | zero _ => return (← zero', ← iapp ``zero_smul #[k.1])
  | nterm _ n x a => do
    let n' ← Mathlib.Meta.NormNum.eval (← mkAppM ``HMul.hMul #[k.1, n.1])
    let (a', h₂) ← evalSMul k a
    return (← term' (n'.expr, k.2 * n.2) x a',
      ← iapp ``term_smul #[k.1, n.1, x.2, a, n'.expr, a', ← n'.getProof, h₂])

theorem term_atom {α} [AddCommMonoid α] (x : α) : x = term 1 x 0 := by simp [term]
                                                                       -- 🎉 no goals
theorem term_atomg {α} [AddCommGroup α] (x : α) : x = termg 1 x 0 := by simp [termg]
                                                                        -- 🎉 no goals
theorem term_atom_pf {α} [AddCommMonoid α] (x x' : α) (h : x = x') : x = term 1 x' 0 := by
  simp [term, h]
  -- 🎉 no goals
theorem term_atom_pfg {α} [AddCommGroup α] (x x' : α) (h : x = x') : x = termg 1 x' 0 := by
  simp [termg, h]
  -- 🎉 no goals

/-- Interpret an expression as an atom for `abel`'s normal form. -/
def evalAtom (e : Expr) : M (NormalExpr × Expr) := do
  let { expr := e', proof?, .. } ← (← readThe AtomM.Context).evalAtom e
  let i ← AtomM.addAtom e'
  let p ← match proof? with
  | none => iapp ``term_atom #[e]
  | some p => iapp ``term_atom_pf #[e, e', p]
  return (← term' (← intToExpr 1, 1) (i, e') (← zero'), p)

theorem unfold_sub {α} [SubtractionMonoid α] (a b c : α) (h : a + -b = c) : a - b = c := by
  rw [sub_eq_add_neg, h]
  -- 🎉 no goals

theorem unfold_smul {α} [AddCommMonoid α] (n) (x y : α)
    (h : smul n x = y) : n • x = y := h

theorem unfold_smulg {α} [AddCommGroup α] (n : ℕ) (x y : α)
    (h : smulg (Int.ofNat n) x = y) : (n : ℤ) • x = y := h

theorem unfold_zsmul {α} [AddCommGroup α] (n : ℤ) (x y : α)
    (h : smulg n x = y) : n • x = y := h

lemma subst_into_smul {α} [AddCommMonoid α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smul α _ tl tr = t) : smul l r = t := by simp [prl, prr, prt]
                                                     -- 🎉 no goals

lemma subst_into_smulg {α} [AddCommGroup α]
    (l r tl tr t) (prl : l = tl) (prr : r = tr)
    (prt : @smulg α _ tl tr = t) : smulg l r = t := by simp [prl, prr, prt]
                                                       -- 🎉 no goals

lemma subst_into_smul_upcast {α} [AddCommGroup α]
    (l r tl zl tr t) (prl₁ : l = tl) (prl₂ : ↑tl = zl) (prr : r = tr)
    (prt : @smulg α _ zl tr = t) : smul l r = t := by
  simp [← prt, prl₁, ← prl₂, prr, smul, smulg, coe_nat_zsmul]
  -- 🎉 no goals

lemma subst_into_add {α} [AddCommMonoid α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl, prr, prt]
  -- 🎉 no goals

lemma subst_into_addg {α} [AddCommGroup α] (l r tl tr t)
    (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r = t := by
  rw [prl, prr, prt]
  -- 🎉 no goals

lemma subst_into_negg {α} [AddCommGroup α] (a ta t : α)
    (pra : a = ta) (prt : -ta = t) : -a = t := by
  simp [pra, prt]
  -- 🎉 no goals

/-- Normalize a term `orig` of the form `smul e₁ e₂` or `smulg e₁ e₂`.
  Normalized terms use `smul` for monoids and `smulg` for groups,
  so there are actually four cases to handle:
  * Using `smul` in a monoid just simplifies the pieces using `subst_into_smul`
  * Using `smulg` in a group just simplifies the pieces using `subst_into_smulg`
  * Using `smul a b` in a group requires converting `a` from a nat to an int and
    then simplifying `smulg ↑a b` using `subst_into_smul_upcast`
  * Using `smulg` in a monoid is impossible (or at least out of scope),
    because you need a group argument to write a `smulg` term -/
def evalSMul' (eval : Expr → M (NormalExpr × Expr))
    (is_smulg : Bool) (orig e₁ e₂ : Expr) : M (NormalExpr × Expr) := do
  trace[abel] "Calling NormNum on {e₁}"
  let ⟨e₁', p₁, _⟩ ← try Meta.NormNum.eval e₁ catch _ => pure { expr := e₁ }
  let p₁ ← p₁.getDM (mkEqRefl e₁')
  match Meta.NormNum.isIntLit e₁' with
  | some n => do
    let c ← read
    let (e₂', p₂) ← eval e₂
    if c.isGroup = is_smulg then do
      let (e', p) ← evalSMul (e₁', n) e₂'
      return (e', ← iapp ``subst_into_smul #[e₁, e₂, e₁', e₂', e', p₁, p₂, p])
    else do
      if ¬ c.isGroup then throwError "Doesn't make sense to us `smulg` in a monoid. "
      -- We are multiplying by a natural number in an additive group.
      let zl ← Expr.ofInt q(ℤ) n
      let p₁' ← mkEqRefl zl
      let (e', p) ← evalSMul (zl, n) e₂'
      return (e', c.app ``subst_into_smul_upcast c.inst #[e₁, e₂, e₁', zl, e₂', e', p₁, p₁', p₂, p])
  | none => evalAtom orig

/-- Evaluate an expression into its `abel` normal form, by recursing into subexpressions. -/
partial def eval (e : Expr) : M (NormalExpr × Expr) := do
  trace[abel.detail] "running eval on {e}"
  trace[abel.detail] "getAppFnArgs: {e.getAppFnArgs}"
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, e₁, e₂]) => do
    let (e₁', p₁) ← eval e₁
    let (e₂', p₂) ← eval e₂
    let (e', p') ← evalAdd e₁' e₂'
    return (e', ← iapp ``subst_into_add #[e₁, e₂, e₁', e₂', e', p₁, p₂, p'])
  | (``HSub.hSub, #[_, _, _ ,_, e₁, e₂]) => do
    let e₂' ← mkAppM ``Neg.neg #[e₂]
    let e ← mkAppM ``HAdd.hAdd #[e₁, e₂']
    let (e', p) ← eval e
    let p' ← (← read).mkApp ``unfold_sub ``SubtractionMonoid #[e₁, e₂, e', p]
    return (e', p')
  | (``Neg.neg, #[_, _, e]) => do
    let (e₁, p₁) ← eval e
    let (e₂, p₂) ← evalNeg e₁
    return (e₂, ← iapp `Mathlib.Tactic.Abel.subst_into_neg #[e, e₁, e₂, p₁, p₂])
  | (`AddMonoid.nsmul, #[_, _, e₁, e₂]) => do
    let n ← if (← read).isGroup then mkAppM ``Int.ofNat #[e₁] else pure e₁
    let (e', p) ← eval <| ← iapp ``smul #[n, e₂]
    return (e', ← iapp ``unfold_smul #[e₁, e₂, e', p])
  | (``SubNegMonoid.zsmul, #[_, _, e₁, e₂]) => do
      if ¬ (← read).isGroup then failure
      let (e', p) ← eval <| ← iapp ``smul #[e₁, e₂]
      return (e', (← read).app ``unfold_zsmul (← read).inst #[e₁, e₂, e', p])
  | (``SMul.smul, #[.const ``Int _, _, _, e₁, e₂]) =>
    evalSMul' eval true e e₁ e₂
  | (``SMul.smul, #[.const ``Nat _, _, _, e₁, e₂]) =>
    evalSMul' eval false e e₁ e₂
  | (``HSMul.hSMul, #[.const ``Int _, _, _, _, e₁, e₂]) =>
    evalSMul' eval true e e₁ e₂
  | (``HSMul.hSMul, #[.const ``Nat _, _, _, _, e₁, e₂]) =>
    evalSMul' eval false e e₁ e₂
  | (``smul, #[_, _, e₁, e₂]) => evalSMul' eval false e e₁ e₂
  | (``smulg, #[_, _, e₁, e₂]) => evalSMul' eval true e e₁ e₂
  | (``OfNat.ofNat, #[_, .lit (.natVal 0), _])
  | (``Zero.zero, #[_, _]) =>
    if ← isDefEq e (← read).α0 then
      pure (← zero', ← mkEqRefl (← read).α0)
    else
      evalAtom e
  | _ => evalAtom e

/-- Tactic for solving equations in the language of
*additive*, commutative monoids and groups.
This version of `abel` fails if the target is not an equality
that is provable by the axioms of commutative monoids/groups.

`abel1!` will use a more aggressive reducibility setting to identify atoms.
This can prove goals that `abel` cannot, but is more expensive.
-/
syntax (name := abel1) "abel1" "!"? : tactic

open Lean Elab Meta Tactic

/-- The `abel1` tactic, which solves equations in the language of commutative additive groups
(or monoids). -/
elab_rules : tactic | `(tactic| abel1 $[!%$tk]?) => withMainContext do
  let tm := if tk.isSome then .default else .reducible
  let some (_, e₁, e₂) := (← whnfR <| ← getMainTarget).eq?
    | throwError "abel1 requires an equality goal"
  trace[abel] "running on an equality `{e₁} = {e₂}`."
  let c ← mkContext e₁
  closeMainGoal <| ← AtomM.run tm <| ReaderT.run (r := c) do
    let (e₁', p₁) ← eval e₁
    trace[abel] "found `{p₁}`, a proof that `{e₁} = {e₁'.e}`"
    let (e₂', p₂) ← eval e₂
    trace[abel] "found `{p₂}`, a proof that `{e₂} = {e₂'.e}`"
    unless ← isDefEq e₁' e₂' do
      throwError "abel1 found that the two sides were not equal"
    trace[abel] "verified that the simplified forms are identical"
    mkEqTrans p₁ (← mkEqSymm p₂)

@[inherit_doc abel1] macro (name := abel1!) "abel1!" : tactic => `(tactic| abel1 !)

theorem term_eq [AddCommMonoid α] (n : ℕ) (x a : α) : term n x a = n • x + a := rfl
/-- A type synonym used by `abel` to represent `n • x + a` in an additive commutative group. -/
theorem termg_eq [AddCommGroup α] (n : ℤ) (x a : α) : termg n x a = n • x + a := rfl

/-- True if this represents an atomic expression. -/
def NormalExpr.isAtom : NormalExpr → Bool
  | .nterm _ (_, 1) _ (.zero _) => true
  | _ => false

/-- The normalization style for `abel_nf`. -/
inductive AbelMode where
  /-- The default form -/
  | term
  /-- Raw form: the representation `abel` uses internally. -/
  | raw

/-- Configuration for `abel_nf`. -/
structure AbelNF.Config where
  /-- the reducibility setting to use when comparing atoms for defeq -/
  red := TransparencyMode.reducible
  /-- if true, atoms inside ring expressions will be reduced recursively -/
  recursive := true
  /-- The normalization style. -/
  mode := AbelMode.term

/-- Function elaborating `AbelNF.Config`. -/
declare_config_elab elabAbelNFConfig AbelNF.Config

/--
The core of `abel_nf`, which rewrites the expression `e` into `abel` normal form.

* `s`: a reference to the mutable state of `abel`, for persisting across calls.
  This ensures that atom ordering is used consistently.
* `cfg`: the configuration options
* `e`: the expression to rewrite
-/
partial def abelNFCore
    (s : IO.Ref AtomM.State) (cfg : AbelNF.Config) (e : Expr) : MetaM Simp.Result := do
  let ctx := {
    simpTheorems := #[← Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) {}]
    congrTheorems := ← getSimpCongrTheorems }
  let simp ← match cfg.mode with
  | .raw => pure pure
  | .term =>
    let thms := [``term_eq, ``termg_eq, ``add_zero, ``one_nsmul, ``one_zsmul, ``zsmul_zero]
    let ctx' := { ctx with simpTheorems := #[← thms.foldlM (·.addConst ·) {:_}] }
    pure fun r' : Simp.Result ↦ do
      Simp.mkEqTrans r' (← Simp.main r'.expr ctx' (methods := Simp.DefaultMethods.methods)).1
  let rec
    /-- The recursive case of `abelNF`.
    * `root`: true when the function is called directly from `abelNFCore`
      and false when called by `evalAtom` in recursive mode.
    * `parent`: The input expression to simplify. In `pre` we make use of both `parent` and `e`
      to determine if we are at the top level in order to prevent a loop
      `go -> eval -> evalAtom -> go` which makes no progress.
    -/
    go root parent :=
      let pre e :=
        try
          guard <| root || parent != e -- recursion guard
          let e ← withReducible <| whnf e
          guard e.isApp -- all interesting group expressions are applications
          let (a, pa) ← eval e (← mkContext e) { red := cfg.red, evalAtom } s
          guard !a.isAtom
          let r ← simp { expr := a, proof? := pa }
          if ← withReducible <| isDefEq r.expr e then return .done { expr := r.expr }
          pure (.done r)
        catch _ => pure <| .visit { expr := e }
      let post := (Simp.postDefault · fun _ ↦ none)
      (·.1) <$> Simp.main parent ctx (methods := { pre, post }),
    /-- The `evalAtom` implementation passed to `eval` calls `go` if `cfg.recursive` is true,
    and does nothing otherwise. -/
    evalAtom := if cfg.recursive then go false else fun e ↦ pure { expr := e }
  go true e

open Elab.Tactic Parser.Tactic
/-- Use `abel_nf` to rewrite the main goal. -/
def abelNFTarget (s : IO.Ref AtomM.State) (cfg : AbelNF.Config) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let r ← abelNFCore s cfg tgt
  if r.expr.isConstOf ``True then
    goal.assign (← mkOfEqTrue (← r.getProof))
    replaceMainGoal []
  else
    replaceMainGoal [← applySimpResultToTarget goal tgt r]

/-- Use `abel_nf` to rewrite hypothesis `h`. -/
def abelNFLocalDecl (s : IO.Ref AtomM.State) (cfg : AbelNF.Config) (fvarId : FVarId) :
    TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← fvarId.getType)
  let goal ← getMainGoal
  let myres ← abelNFCore s cfg tgt
  match ← applySimpResultToLocalDecl goal fvarId myres false with
  | none => replaceMainGoal []
  | some (_, newGoal) => replaceMainGoal [newGoal]

/-- Unsupported legacy syntax from mathlib3, which allowed passing additional terms to `abel`. -/
syntax (name := abel_term) "abel" (&" raw" <|> &" term")? (location)? : tactic
/-- Unsupported legacy syntax from mathlib3, which allowed passing additional terms to `abel!`. -/
syntax (name := abel!_term) "abel!" (&" raw" <|> &" term")? (location)? : tactic

/--
Simplification tactic for expressions in the language of abelian groups,
which rewrites all group expressions into a normal form.
* `abel_nf!` will use a more aggressive reducibility setting to identify atoms.
* `abel_nf (config := cfg)` allows for additional configuration:
  * `red`: the reducibility setting (overridden by `!`)
  * `recursive`: if true, `abel_nf` will also recurse into atoms
* `abel_nf` works as both a tactic and a conv tactic.
  In tactic mode, `abel_nf at h` can be used to rewrite in a hypothesis.
-/
elab (name := abelNF) "abel_nf" tk:"!"? cfg:(config ?) loc:(location)? : tactic => do
  let mut cfg ← elabAbelNFConfig cfg
  if tk.isSome then cfg := { cfg with red := .default }
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  let s ← IO.mkRef {}
  withLocation loc (abelNFLocalDecl s cfg) (abelNFTarget s cfg)
    fun _ ↦ throwError "abel_nf failed"

@[inherit_doc abelNF] macro "abel_nf!" cfg:(config)? loc:(location)? : tactic =>
  `(tactic| abel_nf ! $(cfg)? $(loc)?)

@[inherit_doc abelNF] syntax (name := abelNFConv) "abel_nf" "!"? (config)? : conv

/-- Elaborator for the `abel_nf` tactic. -/
@[tactic abelNFConv] def elabAbelNFConv : Tactic := fun stx ↦ match stx with
  | `(conv| abel_nf $[!%$tk]? $(_cfg)?) => withMainContext do
    let mut cfg ← elabAbelNFConfig stx[2]
    if tk.isSome then cfg := { cfg with red := .default }
    Conv.applySimpResult (← abelNFCore (← IO.mkRef {}) cfg (← instantiateMVars (← Conv.getLhs)))
  | _ => Elab.throwUnsupportedSyntax

@[inherit_doc abelNF] macro "abel_nf!" cfg:(config)? : conv => `(conv| abel_nf ! $(cfg)?)

/--
Tactic for evaluating expressions in abelian groups.

* `abel!` will use a more aggressive reducibility setting to determine equality of atoms.
* `abel1` fails if the target is not an equality.

For example:
```
example [AddCommMonoid α] (a b : α) : a + (b + a) = a + a + b := by abel
example [AddCommGroup α] (a : α) : (3 : ℤ) • a = a + (2 : ℤ) • a := by abel
```
-/
macro (name := abel) "abel" : tactic =>
  `(tactic| first | abel1 | abel_nf; trace "Try this: abel_nf")
@[inherit_doc abel] macro "abel!" : tactic =>
  `(tactic| first | abel1! | abel_nf!; trace "Try this: abel_nf!")

/--
The tactic `abel` evaluates expressions in abelian groups.
This is the conv tactic version, which rewrites a target which is an abel equality to `True`.

See also the `abel` tactic.
-/
macro (name := abelConv) "abel" : conv =>
  `(conv| first | discharge => abel1 | abel_nf; tactic => trace "Try this: abel_nf")
@[inherit_doc abelConv] macro "abel!" : conv =>
  `(conv| first | discharge => abel1! | abel_nf!; tactic => trace "Try this: abel_nf!")
