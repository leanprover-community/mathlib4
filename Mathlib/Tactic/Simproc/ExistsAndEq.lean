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

-- /-- Used to indicate the current case should be unreachable, unless an invariant is violated.
-- `context` should be used to indicate which case is asserted to be unreachable.
-- For example, `"findEq: path for a conjunction should be nonempty"`. -/
-- private def panic! {α : Type} (context : String) : MetaM α := do
--   let e := s!"existsAndEq: internal error, unreachable case has occurred:\n{context}."
--   logError e
--   -- the following error will be caught by `simp` so we additionally log it above
--   throwError e

#check mkLambda

/-- Constructs `∃ f₁ f₂ ... fₙ, body`, where `[f₁, ..., fₙ] = fvars`. -/
def mkNestedExists (fvars : List VarQ) (body : Q(Prop)) : MetaM Q(Prop) := do
  match fvars with
  | [] => pure body
  | ⟨_, β, b⟩ :: tl =>
    let res ← mkNestedExists tl body
    let name := (← getLCtx).findFVar? b |>.get!.userName
    let p : Q($β → Prop) ← Impl.mkLambdaQ name b res
    pure q(Exists $p)

/-- Finds a `Path` for `findEq`. It leads to a subexpression `a = a'` or `a' = a`, where
`a'` doesn't contain the free variable `a`.
This is a fast version that quickly returns `none` when the simproc
is not applicable. -/
partial def findEqPath {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) :
    MetaM <| Option Path := do
  match_expr P with
  | Eq _ x y =>
    if a == x && !(y.containsFVar a.fvarId!) then
      return some []
    if a == y && !(x.containsFVar a.fvarId!) then
      return some []
    return none
  | And L R =>
    if let some path ← findEqPath a L then
      return some (.andLeft :: path)
    if let some path ← findEqPath a R then
      return some (.andRight :: path)
    return none
  | Exists tb pb =>
    if (tb.containsFVar a.fvarId!) then
      return none
    let .lam _ _ body _ := pb | return none
    let some path ← findEqPath a body | return none
    return some (.existsBody :: path)
  | _ => return none

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
    let ~q(@Eq.{u} $γ $x $y) := P | panic! "path is empty, but `P` is not an equality: {← ppExpr P}"
    if a == x && !(y.containsFVar a.fvarId!) then
      return ([], ← getLCtx, P, y)
    if a == y && !(x.containsFVar a.fvarId!) then
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
  | .existsType :: tl =>
    panic! "not implemented"
  | .existsBody :: tl =>
    let ~q(@Exists $β $pb) := P | panic! "path starts with `existsBody`, but `P` is not `Exists`"
    lambdaBoundedTelescope pb 1 fun bs (body : Q(Prop)) => do
      let #[(b : Q($β))] := bs | unreachable!
      let (fvars, lctx, P', a') ← go a q($body) tl
      return (⟨_, _, b⟩ :: fvars, lctx, P', a')

/-- The path to the equation in the result formula: the quantifiers entered along `path` are moved
to the front, so their `existsBody` steps come first, followed by the `And` steps in their original
order. -/
def Path.forResult (path : Path) : Path :=
  path.filter (· == .existsBody) ++ path.filter (· != .existsBody)

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
  -- path : EB, AR, AL, EB, AL
  intro ⟨x, h₁⟩
  -- destruct the input following the path
  refine
    h₁.elim fun e1 h₂ ↦        -- EB
    h₂.elim fun a1 h₃ ↦        -- AR
    h₃.elim fun h₄ a2 ↦        -- AL
    h₄.elim fun e2 h₅ ↦        -- EB
    h₅.elim fun h_eq a3 ↦ ?_   -- AL
  -- subst the equation (`substCore`)
  subst h_eq
  -- construct the output following the path of the result: EB, EB, AR, AL, AL
  refine Exists.intro e1 ?_ -- EB
  refine Exists.intro e2 ?_ -- EB
  refine And.intro a1 ?_    -- AR
  refine And.intro ?_ a2    -- AL
  refine And.intro ?_ a3    -- AL
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
      have pf : Q($P') := ← instantiateMVars goal
      return pf
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
  -- destruct the input following the path of the result: EB, EB, AR, AL, AL
  refine
    h₁.elim fun e1 h₂ ↦    -- EB
    h₂.elim fun e2 h₃ ↦    -- EB
    h₃.elim fun a1 h₄ ↦    -- AR
    h₄.elim fun h₅ a2 ↦    -- AL
    h₅.elim fun _ a3 ↦ ?_  -- AL
  -- construct the output following the path: EB, AR, AL, EB, AL
  refine Exists.intro (f e2) ?_  -- `a'`
  refine Exists.intro e1 ?_      -- EB
  refine And.intro a1 ?_         -- AR
  refine And.intro ?_ a2         -- AL
  refine Exists.intro e2 ?_      -- EB
  refine And.intro ?_ a3         -- AL
  exact rfl
``` -/
def mkAfterToBefore {u : Level} {α : Q(Sort u)} {p : Q($α → Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (fvars : List VarQ) (path : Path) :
    MetaM <| Q($P' → (∃ a, $p a)) := do
  withLocalDeclQ .anonymous .default P' fun (h : Q($P')) => do
    let pf : Q(∃ a, $p a) ← destruct h fvars path.forResult [] fun leaves _ => do
      let pf1 : Q($p $a') ← construct (goal := q($p $a')) fvars path leaves
      return q(Exists.intro $a' $pf1)
    mkLambdaFVars #[h] pf


/-- Triggers at goals of the form `∃ a, body` and checks if `body` allows a single value `a'`
for `a`. If so, replaces `a` with `a'` and removes quantifier.

It looks through nested quantifiers and conjunctions searching for a `a = a'`
or `a' = a` subexpression. -/
simproc ↓ existsAndEq (Exists _) := fun e => do
  let_expr f@Exists α p := e | return .continue
  lambdaBoundedTelescope p 1 fun xs (body : Q(Prop)) => withNewMCtxDepth do
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

end ExistsAndEq

export ExistsAndEq (existsAndEq)
