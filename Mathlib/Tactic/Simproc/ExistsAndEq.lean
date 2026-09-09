/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Init
public meta import Qq
public import Qq
public import Qq.MatchImpl
public import Qq.Typ

/-!
# Simproc for `∃ a', ... ∧ a' = a ∧ ...`

This module implements the `existsAndEq` simproc, which triggers on goals of the form `∃ a, P`.
It checks whether `P` allows only one possible value for `a`, and if so, substitutes it, eliminating
the leading quantifier.

The procedure traverses the body, branching at each `∧` and entering existential quantifiers,
searching for a subexpression of the form `a = a'` or `a' = a` for `a'` that is independent of `a`.
If such an expression is found, all occurrences of `a` are replaced with `a'`. If `a'` depends on
variables bound by existential quantifiers, those quantifiers are moved outside.

For example, `∃ a, p a ∧ ∃ b, a = f b ∧ q b` will be rewritten as `∃ b, p (f b) ∧ q b`.
-/

public meta section

open Lean Meta Qq

namespace ExistsAndEq

/-- Type for storing the chosen branch at `And` nodes. -/
inductive GoTo
| andLeft | andRight | existsType | existsBody
deriving BEq, Inhabited

/-- Type for storing the path in the body expression leading to `a = a'`. We store only the chosen
directions at each `And` node because there is no branching at `Exists` nodes, and `Exists` nodes
will be removed from the body. -/
abbrev Path := List GoTo

/-- Qq-fied version of `Expr`. Here, we use it to store free variables introduced when unpacking
existential quantifiers. -/
abbrev VarQ := (u : Level) × (α : Q(Sort u)) × Q($α)

instance : Inhabited VarQ where
  default := ⟨default, default, default⟩

/-- Qq-fied version of `Expr` proving some `P : Prop`. -/
abbrev HypQ := (P : Q(Prop)) × Q($P)

instance : Inhabited HypQ where
  default := ⟨default, default⟩

/-- Checks whether the equation with sides `x` and `y` determines the free variable `a` as `y`:
`x` is `a` itself, and `y` doesn't mention `a` (in `a = f a`, for example, it does). The callers
try both orientations. -/
def eqDetermines (a x y : Expr) : Bool :=
  a == x && !(y.containsFVar a.fvarId!)

/-- Finds a `Path` for `findEq`. It leads to a subexpression `a = a'` or `a' = a`, where
`a'` doesn't contain the free variable `a`.
This is a fast version that quickly returns `none` when the simproc
is not applicable. -/
partial def findEqPath {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) :
    OptionT MetaM Path := do
  match_expr P with
  | Eq _ x y =>
    if eqDetermines a x y then
      return []
    if eqDetermines a y x then
      return []
    failure
  | And L R =>
    ((.andLeft :: ·) <$> findEqPath a L) <|> ((.andRight :: ·) <$> findEqPath a R)
  | Exists tb pb =>
    guard !(tb.containsFVar a.fvarId!)
    let .lam _ _ body _ := pb | failure
    (.existsBody :: ·) <$> findEqPath a body
  | _ => failure

/-- Given `P : Prop` and `a : α`, traverses the expression `P` to find a subexpression of
the form `a = a'` or `a' = a` for some `a'`. It branches at each `And` and walks into
existential quantifiers.

Returns a tuple `(fvars, lctx, P', a')`, where:
* `fvars` is a list of all variables bound by existential quantifiers along the path.
* `lctx` is the local context containing all these free variables.
* `P'` is `P` with all existential quantifiers along the path removed, and corresponding bound
  variables replaced with `fvars`.
* `a'` is the expression found that must be equal to `a`.
  It may contain free variables from `fvars`. -/
partial def findEq {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) (path : Path) :
    MetaM (List VarQ × LocalContext × Q(Prop) × Q($α)) := do
   go a P path
where
  /-- Recursive part of `findEq`. -/
  go {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) (path : Path) :
    MetaM (List VarQ × LocalContext × Q(Prop) × Q($α)) := do
  match path with
  | [] =>
    let ~q(@Eq.{u} $γ $x $y) := P
      | panic! s!"path is empty, but `P` is not an equality: {← ppExpr P}"
    if eqDetermines a x y then
      return ([], ← getLCtx, P, y)
    if eqDetermines a y x then
      return ([], ← getLCtx, P, x)
    panic!
      "some side of equality must be `a`, and the other must not depend on `a`"
  | .andLeft :: tl =>
    let ~q($L ∧ $R) := P | panic! "path starts with andLeft, but `P` is not a conjuction"
    let (fvars, lctx, P', a') ← go a q($L) tl
    return (fvars, lctx, q($P' ∧ $R), a')
  | .andRight :: tl =>
    let ~q($L ∧ $R) := P | panic! "path starts with andLeft, but `P` is not a conjuction"
    let (fvars, lctx, P', a') ← go a q($R) tl
    return (fvars, lctx, q($L ∧ $P'), a')
  | .existsType :: _ =>
    panic! "not implemented"
  | .existsBody :: tl =>
    let ~q(@Exists $β $pb) := P | panic! "path starts with `existsBody`, but `P` is not `Exists`"
    lambdaBoundedTelescope pb 1 fun bs (body : Q(Prop)) => do
      let #[(b : Q($β))] := bs | unreachable!
      let (fvars, lctx, P', a') ← go a q($body) tl
      return (⟨_, _, b⟩ :: fvars, lctx, P', a')

/-- Constructs `∃ f₁ f₂ ... fₙ, body`, where `[f₁, ..., fₙ] = fvars`. -/
def mkNestedExists (fvars : List VarQ) (body : Q(Prop)) : MetaM Q(Prop) := do
  match fvars with
  | [] => pure body
  | ⟨_, β, b⟩ :: tl =>
    let res ← mkNestedExists tl body
    let p : Q($β → Prop) ← mkLambdaFVars #[b] res
    pure q(Exists $p)

/-- The path to the equation in the result formula: the quantifiers entered along `path` are moved
to the front, so their `existsBody` steps come first, followed by the `And` steps in their original
order. -/
def Path.forResult (path : Path) : Path :=
  let (quantifiers, conjunctions) := path.partition (· == .existsBody)
  quantifiers ++ conjunctions

/-- Destructs `h : P` following `path`, as the chain of `refine h.elim fun … ↦ ?_` in the docstring
of `mkBeforeToAfter` does: at an `existsBody` step the quantifier is unpacked with `Exists.elim`,
using the next variable of `exs` as the bound variable; at an `andLeft`/`andRight` step the
conjunction is split with `And.elim`, and the part outside the path becomes a *leaf*. The
continuation `k` receives the leaves (in path order, after those in `acc`) and the hypothesis at
the end of the path, i.e. the equation. All of them are local hypotheses. -/
partial def destruct {P goal : Q(Prop)} (h : Q($P)) (exs : List VarQ) (path : Path)
    (acc : List HypQ) (k : List HypQ → HypQ → MetaM Q($goal)) : MetaM Q($goal) := do
  match path with
  | [] => k acc ⟨P, h⟩
  | .existsBody :: tl =>
    match exs with
    | [] => panic! "path starts with `existsBody`, but `exs` is empty"
    | ⟨v, γ, e⟩ :: exsTl =>
    let ~q(@Exists.{v} $β $pb) := P
      | panic! "path starts with `existsBody`, but `P` is not `Exists`"
    let _ : $γ =Q $β := ⟨⟩
    withLocalDeclQ .anonymous .default q($pb $e) fun h' => do
      let pf ← destruct h' exsTl tl acc k
      let f : Q(∀ e, $pb e → $goal) ← mkLambdaFVars #[e, h'] pf
      return q(Exists.elim $h $f)
  | .andRight :: tl =>
    let ~q($L ∧ $R) := P | panic! "path starts with `andRight`, but `P` is not a conjunction"
    withLocalDeclQ .anonymous .default q($L) fun leaf => do
    withLocalDeclQ .anonymous .default q($R) fun h' => do
      let pf ← destruct h' exs tl (acc ++ [⟨q($L), leaf⟩]) k
      let f : Q($L → $R → $goal) ← mkLambdaFVars #[leaf, h'] pf
      return q(And.elim $f $h)
  | .andLeft :: tl =>
    let ~q($L ∧ $R) := P | panic! "path starts with `andLeft`, but `P` is not a conjunction"
    withLocalDeclQ .anonymous .default q($L) fun h' => do
    withLocalDeclQ .anonymous .default q($R) fun leaf => do
      let pf ← destruct h' exs tl (acc ++ [⟨q($R), leaf⟩]) k
      let f : Q($L → $R → $goal) ← mkLambdaFVars #[h', leaf] pf
      return q(And.elim $f $h)
  | .existsType :: _ => panic! "not implemented"

/-- Constructs a proof of `goal` following `path`, as the chain of `refine Exists.intro … ?_` and
`refine And.intro … ?_` in the docstring of `mkBeforeToAfter` does: at an `existsBody` step the
next variable of `exs` is the witness; at an `andLeft`/`andRight` step the part outside the path
is proved by the next leaf; the equation at the end of the path is closed by `rfl`. -/
partial def construct {goal : Q(Prop)} (exs : List VarQ) (path : Path) (leaves : List HypQ) :
    MetaM Q($goal) := do
  match path with
  | [] =>
    let ~q($x = $y) := goal | panic! "path is empty, but the goal is not an equation"
    let _ : $x =Q $y := ⟨⟩
    return q(rfl)
  | .existsBody :: tl =>
    match exs with
    | [] => panic! "path starts with `existsBody`, but `exs` is empty"
    | ⟨v, γ, e⟩ :: exsTl =>
    let ~q(@Exists.{v} $β $pb) := goal
      | panic! "path starts with `existsBody`, but the goal is not `Exists`"
    let _ : $γ =Q $β := ⟨⟩
    let pf : Q($pb $e) ← construct exsTl tl leaves
    return q(Exists.intro $e $pf)
  | .andRight :: tl =>
    let ~q($L ∧ $R) := goal
      | panic! "path starts with `andRight`, but the goal is not a conjunction"
    match leaves with
    | [] => panic! "path starts with `andRight`, but `leaves` is empty"
    | ⟨T, leaf⟩ :: leavesTl =>
    let _ : $T =Q $L := ⟨⟩
    have leaf : Q($L) := leaf
    let pf : Q($R) ← construct exs tl leavesTl
    return q(And.intro $leaf $pf)
  | .andLeft :: tl =>
    let ~q($L ∧ $R) := goal
      | panic! "path starts with `andLeft`, but the goal is not a conjunction"
    match leaves with
    | [] => panic! "path starts with `andLeft`, but `leaves` is empty"
    | ⟨T, leaf⟩ :: leavesTl =>
    let _ : $T =Q $R := ⟨⟩
    have leaf : Q($R) := leaf
    let pf : Q($L) ← construct exs tl leavesTl
    return q(And.intro $pf $leaf)
  | .existsType :: _ => panic! "not implemented"

/-- Generates a proof of `(∃ a, p a) → P'`. We assume that `fvars = [f₁, ..., fₙ]` are free
variables and `P' = ∃ f₁ ... fₙ, newBody`, and `path` leads to `a = a'` in `∃ a, p a`.

The proof follows the following structure:
```
example (f : β → α) {P Q : β → Prop} :
    (∃ x b, P b ∧ (∃ c, f c = x ∧ Q c) ∧ Q b) → ∃ b c, P b ∧ (f c = f c ∧ Q c) ∧ Q b := by
  -- path : existsBody, andRight, andLeft, existsBody, andLeft
  intro ⟨x, h₁⟩
  -- destruct the input following the path:
  -- obtain ⟨e1, a1, ⟨e2, h_eq, a3⟩, a2⟩ := h₁
  refine
    h₁.elim fun e1 h₂ ↦           -- existsBody
    h₂.elim fun a1 h₃ ↦           -- andRight
    h₃.elim fun h₄ a2 ↦           -- andLeft
    h₄.elim fun e2 h₅ ↦           -- existsBody
    h₅.elim fun h_eq a3 ↦ ?_      -- andLeft
  -- subst the equation (`substCore`)
  subst h_eq
  -- construct the output following the path of the result (with all existsBody moved left):
  -- existsBody, existsBody, andRight, andLeft, andLeft
  -- exact ⟨e1, e2, a1, ⟨rfl, a3⟩, a2⟩
  refine Exists.intro e1 ?_       -- existsBody
  refine Exists.intro e2 ?_       -- existsBody
  refine And.intro a1 ?_          -- andRight
  refine And.intro ?_ a2          -- andLeft
  refine And.intro ?_ a3          -- andLeft
  exact rfl
``` -/
def mkBeforeToAfter {u : Level} {α : Q(Sort u)} {p : Q($α → Prop)}
    {P' : Q(Prop)} (fvars : List VarQ) (path : Path) :
    MetaM <| Q((∃ a, $p a) → $P') := do
  withLocalDeclQ .anonymous .default q(∃ a, $p a) fun h => do
  withLocalDeclQ .anonymous .default q($α) fun a => do
  withLocalDeclQ .anonymous .default q($p $a) fun ha => do
    let pf1 : Q($P') ← destruct ha fvars path [] fun leaves ⟨hEqType, hEq⟩ => do
      let ~q(@Eq.{u} $γ $x $y) := hEqType | panic! "the end of the path is not an equation"
      -- the equation is a local hypothesis, so `substCore` applies to it directly;
      -- for `a' = a` the variable to eliminate is on the right-hand side
      let goal ← mkFreshExprSyntheticOpaqueMVar P'
      let (fvarSubst, goal') ← substCore goal.mvarId! hEq.fvarId! (symm := x != a)
      goal'.withContext do
        let leaves : List HypQ ← leaves.mapM fun ⟨_, leaf⟩ => do
          let e := fvarSubst.apply leaf
          return ⟨← inferType e, e⟩
        goal'.assign (← construct (goal := P') fvars path.forResult leaves)
      instantiateMVars goal
    let pf2 : Q(∀ a : $α, $p a → $P') ← mkLambdaFVars #[a, ha] pf1
    let pf3 : Q($P') := q(Exists.elim $h $pf2)
    mkLambdaFVars #[h] pf3

/-- Generates a proof of `P' → ∃ a, p a`. We assume that `fvars = [f₁, ..., fₙ]` are free variables
and `P' = ∃ f₁ ... fₙ, newBody`, and `path` leads to `a = a'` in `∃ a, p a`.

The proof follows the following structure:
```
example (f : β → α) {P Q : β → Prop} :
    (∃ b c, P b ∧ (f c = f c ∧ Q c) ∧ Q b) → ∃ x b, P b ∧ (∃ c, f c = x ∧ Q c) ∧ Q b := by
  intro h₁
  -- destruct the input following the path of the result (with all existsBody moved left):
  -- existsBody, existsBody, andRight, andLeft, andLeft
  -- obtain ⟨e1, e2, a1, ⟨_, a3⟩, a2⟩ := h₁
  refine
    h₁.elim fun e1 h₂ ↦           -- existsBody
    h₂.elim fun e2 h₃ ↦           -- existsBody
    h₃.elim fun a1 h₄ ↦           -- andRight
    h₄.elim fun h₅ a2 ↦           -- andLeft
    h₅.elim fun _ a3 ↦ ?_         -- andLeft
  -- construct the output following the path: existsBody, andRight, andLeft, existsBody, andLeft
  -- exact ⟨f e2, e1, a1, ⟨e2, rfl, a3⟩, a2⟩
  refine Exists.intro (f e2) ?_   -- `a'`
  refine Exists.intro e1 ?_       -- existsBody
  refine And.intro a1 ?_          -- andRight
  refine And.intro ?_ a2          -- andLeft
  refine Exists.intro e2 ?_       -- existsBody
  refine And.intro ?_ a3          -- andLeft
  exact rfl
``` -/
def mkAfterToBefore {u : Level} {α : Q(Sort u)} {p : Q($α → Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (fvars : List VarQ) (path : Path) :
    MetaM <| Q($P' → (∃ a, $p a)) := do
  withLocalDeclQ .anonymous .default P' fun (h : Q($P')) => do
    let pf : Q(∃ a, $p a) ← destruct h fvars path.forResult [] fun leaves _ => do
      let pf1 : Q($p $a') ← construct fvars path leaves
      return q(Exists.intro $a' $pf1)
    mkLambdaFVars #[h] pf

/-- Runs `k` on `e` with the metavariables occurring in `e` replaced by local variables, and
substitutes the metavariables back into the resulting `Simp.Step`. In some cases (e.g. under
`aesop`) the goal contains metavariables, and this is needed to handle them properly: the proof
built by `substCore` can only be instantiated when the goal contains none.

The abstraction is done by `abstractMVars`, so that metavariables occurring in the types of other
metavariables (as in `?f : α → ?β`) are handled consistently.

TODO: this is a general simproc infrastructure, should we moved somewhere else?
-/
def withAbstractMVars (e : Expr) (k : Expr → MetaM Simp.Step) : MetaM Simp.Step := do
  let e ← instantiateMVars e
  if !e.hasMVar then
    return ← k e
  let r ← abstractMVars e (levels := false)
  lambdaBoundedTelescope r.expr r.numMVars fun xs e' => do
    let restore (t : Expr) : MetaM Expr :=
      instantiateMVars <| t.replaceFVars xs r.mvars
    let subst (res : Simp.Result) : MetaM Simp.Result := do
      return { res with expr := ← restore res.expr, proof? := ← res.proof?.mapM restore }
    match ← k e' with
    | .done res => return .done (← subst res)
    | .visit res => return .visit (← subst res)
    | .continue res? => return .continue (← res?.mapM subst)

/-- The implementation of `existsAndEq`, for an expression without metavariables. -/
def existsAndEqCore (e : Expr) : MetaM Simp.Step := do
  let_expr f@Exists α p := e | return .continue
  lambdaBoundedTelescope p 1 fun xs (body : Q(Prop)) => do
    let some u := f.constLevels![0]? | unreachable!
    have α : Q(Sort $u) := α; have p : Q($α → Prop) := p
    let some (a : Q($α)) := xs[0]? | return .continue
    let some path ← findEqPath a body | return .continue
    let (fvars, lctx, newBody, a') ← findEq a body path
    let newBody := newBody.replaceFVar a a'
    withLCtx' lctx do
      let P' : Q(Prop) ← mkNestedExists fvars newBody
      let pfBeforeAfter : Q((∃ a, $p a) → $P') ← mkBeforeToAfter fvars path
      let pfAfterBefore : Q($P' → (∃ a, $p a)) ← mkAfterToBefore a' fvars path
      let pf := q(propext ⟨$pfBeforeAfter, $pfAfterBefore⟩)
      return .visit <| Simp.ResultQ.mk _ <| some q($pf)

/-- Triggers at goals of the form `∃ a, body` and checks if `body` allows a single value `a'`
for `a`. If so, replaces `a` with `a'` and removes quantifier.

It looks through nested quantifiers and conjunctions searching for a `a = a'`
or `a' = a` subexpression. -/
simproc ↓ existsAndEq (Exists _) := fun e => withAbstractMVars e existsAndEqCore

end ExistsAndEq

export ExistsAndEq (existsAndEq)
