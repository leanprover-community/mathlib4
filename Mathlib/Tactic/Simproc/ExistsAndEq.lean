/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Init
import Qq

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

open Lean Meta Qq

namespace ExistsAndEq

/-- Type for storing the chosen branch at `And` nodes. -/
inductive GoTo
| left | right
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

/-- Used to indicate the current case should be unreachable, unless an invariant is violated.
`context` should be used to indicate which case is asserted to be unreachable.
For example, `"findEq: path for a conjunction should be nonempty"`. -/
private def assertUnreachable {α : Type} (context : String) : MetaM α := do
  let e := s!"existsAndEq: internal error, unreachable case has occurred:\n{context}."
  logError e
  -- the following error will be caught by `simp` so we additionaly log it above
  throwError e

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
      return some (.left :: path)
    if let some path ← findEqPath a R then
      return some (.right :: path)
    return none
  | Exists tb pb =>
    if (tb.containsFVar a.fvarId!) then
      return none
    let .lam _ _ body _ := pb | return none
    findEqPath a body
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
  match P with
  | ~q(@Eq.{u} $γ $x $y) =>
    if a == x && !(y.containsFVar a.fvarId!) then
      return ([], ← getLCtx, P, y)
    if a == y && !(x.containsFVar a.fvarId!) then
      return ([], ← getLCtx, P, x)
    assertUnreachable
      "findEq: some side of equality must be `a`, and the other must not depend on `a`"
  | ~q($L ∧ $R) =>
    match (generalizing := false) path with
    | [] => assertUnreachable "findEq: P is conjuction but path is empty"
    | .left :: tl =>
      let (fvars, lctx, P', a') ← go a q($L) tl
      return (fvars, lctx, q($P' ∧ $R), a')
    | .right :: tl =>
      let (fvars, lctx, P', a') ← go a q($R) tl
      return (fvars, lctx, q($L ∧ $P'), a')
  | ~q(@Exists $β $pb) =>
    lambdaBoundedTelescope pb 1 fun bs (body : Q(Prop)) => do
      let #[(b : Q($β))] := bs | unreachable!
      let (fvars, lctx, P', a') ← go a q($body) path
      return (⟨_, _, b⟩ :: fvars, lctx, P', a')
  | _ => assertUnreachable s!"findEq: unexpected P = {← ppExpr P}"

/-- When `P = ∃ f₁ ... fₙ, body`, where `exs = [f₁, ..., fₙ]`, this function takes
`act : body → goal` and proves `P → goal` using `Exists.elim`.

Example:
```
exs = []: act h
exs = [b]:
  P := ∃ b, body
  Exists.elim h (fun b hb ↦ act hb)
exs = [b, c]:
  P := ∃ b c, body
  Exists.elim h (fun b hb ↦
    Exists.elim hb (fun c hc ↦ act hc)
  )
...
``` -/
def withNestedExistsElim {P body goal : Q(Prop)} (exs : List VarQ) (h : Q($P))
    (act : Q($body) → MetaM Q($goal)) : MetaM Q($goal) := do
  match exs with
  | [] =>
    let _ : $P =Q $body := ⟨⟩
    act q($h)
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
      | assertUnreachable <| "withNestedExistsElim: exs is not empty but P is not `Exists`.\n" ++
          s!"P = {← ppExpr P}"
    let _ : $β =Q $γ := ⟨⟩
    withLocalDeclQ .anonymous .default q($p $b) fun hb => do
      let pf1 ← withNestedExistsElim tl hb act
      let pf2 : Q(∀ b, $p b → $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)

/-- Generates a proof of `P' → ∃ a, p a`. We assume that `fvars = [f₁, ..., fₙ]` are free variables
and `P' = ∃ f₁ ... fₙ, newBody`, and `path` leads to `a = a'` in `∃ a, p a`.

The proof follows the following structure:
```
example {α β : Type} (f : β → α) {p : α → Prop} :
    (∃ b, p (f b) ∧ f b = f b) → (∃ a, p a ∧ ∃ b, a = f b) := by
  -- withLocalDeclQ
  intro h
  -- withNestedExistsElim : we unpack all quantifiers in `P` to get `h : newBody`.
  refine h.elim (fun b h ↦ ?_)
  -- use `a'` in the leading existential quantifier
  refine Exists.intro (f b) ?_
  -- then we traverse `newBody` and goal simultaneously
  refine And.intro ?_ ?_
  -- at branches outside the path `h` must concide with goal
  · replace h := h.left
    exact h
  -- inside path we substitute variables from `fvars` into existential quantifiers.
  · replace h := h.right
    refine Exists.intro b ?_
    -- at the end the goal must be `x' = x'`.
    rfl
``` -/
partial def mkAfterToBefore {u : Level} {α : Q(Sort u)} {p : Q($α → Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (newBody : Q(Prop)) (fvars : List VarQ) (path : Path) :
    MetaM <| Q($P' → (∃ a, $p a)) := do
  withLocalDeclQ .anonymous .default P' fun (h : Q($P')) => do
    let pf : Q(∃ a, $p a) ← withNestedExistsElim fvars h fun (h : Q($newBody)) => do
      let pf1 : Q($p $a') ← go h fvars path
      return q(Exists.intro $a' $pf1)
    mkLambdaFVars #[h] pf
where
  /-- Traverses `P` and `goal` simultaneously, proving `goal`. -/
  go {goal P : Q(Prop)} (h : Q($P)) (exs : List VarQ) (path : Path) :
    MetaM Q($goal) := do
  match goal with
  | ~q(@Exists $β $pb) =>
    match (generalizing := false) exs with
    | [] => assertUnreachable "mkAfterToBefore: goal is `Exists` but `exs` is empty"
    | ⟨v, γ, c⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
    let _ : $γ =Q $β := ⟨⟩
    let pf1 : Q($pb $c) := ← go h exsTail path
    return q(Exists.intro $c $pf1)
  | ~q(And $L $R) =>
    let ~q($L' ∧ $R') := P
      | assertUnreachable "mkAfterToBefore: goal is `And` but `P` is not `And`"
    match (generalizing := false) path with
    | [] => assertUnreachable "mkAfterToBefore: goal is `And` but `exs` is empty"
    | .left :: tl =>
      let _ : $R =Q $R' := ⟨⟩
      let pfRight : Q($R) := q(And.right $h)
      let pfLeft : Q($L) ← go q(And.left $h) exs tl
      return q(And.intro $pfLeft $pfRight)
    | .right :: tl =>
      let _ : $L =Q $L' := ⟨⟩
      let pfLeft : Q($L) := q(And.left $h)
      let pfRight : Q($R) ← go q(And.right $h) exs tl
      return q(And.intro $pfLeft $pfRight)
  | _ =>
    let ~q($x = $y) := goal
      | assertUnreachable "mkAfterToBefore: unexpected goal: {← ppExpr goal}"
    if !path.isEmpty then
      assertUnreachable "mkAfterToBefore: `goal` is equality but `path` is not empty"
    let _ : $x =Q $y := ⟨⟩
    return q(rfl)

/-- Recursive implementation for `withExistsElimAlongPath`. -/
partial def withExistsElimAlongPathImp {u : Level} {α : Q(Sort u)}
    {P goal : Q(Prop)} (h : Q($P)) {a a' : Q($α)} (exs : List VarQ) (path : Path)
    (hs : List HypQ)
    (act : Q($a = $a') → List HypQ → MetaM Q($goal)) :
    MetaM Q($goal) := do
  match P with
  | ~q(@Exists $β $pb) =>
    match (generalizing := false) exs with
    | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `Exists` but `exs` is empty"
    | ⟨v, γ, b⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
    let _ : $γ =Q $β := ⟨⟩
    withLocalDeclQ .anonymous .default q($pb $b) fun hb => do
      let newHs := hs ++ [⟨_, hb⟩]
      let pf1 ← withExistsElimAlongPathImp (P := q($pb $b)) hb exsTail path newHs act
      let pf2 : Q(∀ b, $pb b → $goal) ← mkLambdaFVars #[b, hb] pf1
      return q(Exists.elim $h $pf2)
  | ~q(And $L' $R') =>
      match (generalizing := false) path with
      | [] => assertUnreachable "withExistsElimAlongPathImp: `P` is `And` but `path` is empty"
      | .left :: tl =>
        withExistsElimAlongPathImp q(And.left $h) exs tl hs act
      | .right :: tl =>
        withExistsElimAlongPathImp q(And.right $h) exs tl hs act
  | ~q(@Eq.{u} $γ $x $y) =>
    let _ : $γ =Q $α := ⟨⟩
    if !path.isEmpty then
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but `path` is not empty"
    if a == x then
      let _ : $a =Q $x := ⟨⟩
      let _ : $a' =Q $y := ⟨⟩
      act q($h) hs
    else if a == y then
      let _ : $a =Q $y := ⟨⟩
      let _ : $a' =Q $x := ⟨⟩
      act q(Eq.symm $h) hs
    else
      assertUnreachable "withExistsElimAlongPathImp: `P` is equality but neither of sides is `a`"
  | _ => assertUnreachable s!"withExistsElimAlongPathImp: unexpected P = {← ppExpr P}"

/-- Given `act : (a = a') → hb₁ → hb₂ → ... → hbₙ → goal` where `hb₁, ..., hbₙ` are hypotheses
obtained when unpacking existential quantifiers with variables from `exs`, it proves `goal` using
`Exists.elim`. We use this to prove implication in the forward direction. -/
def withExistsElimAlongPath {u : Level} {α : Q(Sort u)}
    {P goal : Q(Prop)} (h : Q($P)) {a a' : Q($α)} (exs : List VarQ) (path : Path)
    (act : Q($a = $a') → List HypQ → MetaM Q($goal)) :
    MetaM Q($goal) :=
  withExistsElimAlongPathImp h exs path [] act

/-- When `P = ∃ f₁ ... fₙ, body`, where `exs = [f₁, ..., fₙ]`, this function takes
`act : body` and proves `P` using `Exists.intro`.

Example:
```
exs = []: act
exs = [b]:
  P := ∃ b, body
  Exists.intro b act
exs = [b, c]:
  P := ∃ b c, body
  Exists.intro b (Exists.intro c act)
...
``` -/
def withNestedExistsIntro {P body : Q(Prop)} (exs : List VarQ)
    (act : MetaM Q($body)) : MetaM Q($P) := do
  match exs with
  | [] =>
    let _ : $P =Q $body := ⟨⟩
    act
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P
      | assertUnreachable "withNestedExistsIntro: `exs` is not empty but `P` is not `Exists`"
    let _ : $β =Q $γ := ⟨⟩
    let pf ← withNestedExistsIntro tl act
    return q(Exists.intro $b $pf)

/-- Generates a proof of `∃ a, p a → P'`. We assume that `fvars = [f₁, ..., fₙ]` are free variables
and `P' = ∃ f₁ ... fₙ, newBody`, and `path` leads to `a = a'` in `∃ a, p a`.

The proof follows the following structure:
```
example {α β : Type} (f : β → α) {p : α → Prop} :
    (∃ a, p a ∧ ∃ b, a = f b) → (∃ b, p (f b) ∧ f b = f b) := by
  -- withLocalDeclQ
  intro h
  refine h.elim (fun a ha ↦ ?_)
  -- withExistsElimAlongPath: following the path we unpack all existential quantifiers.
  -- at the end `hs = [hb]`.
  have h' := ha
  replace h' := h'.right
  refine Exists.elim h' (fun b hb ↦ ?_)
  replace h' := hb
  have h_eq := h'
  clear h'
  -- go: we traverse `P` and `goal` simultaneously
  have h' := ha
  refine Exists.intro b ?_
  refine And.intro ?_ ?_
  -- outside the path goal must concide with `h_eq ▸ h'`
  · replace h' := h'.left
    exact Eq.mp (congrArg (fun t ↦ p t) h_eq) h'
  -- inside the path:
  · replace h' := h'.right
    -- when `h'` starts with existential quantifier we replace it with next hypothesis from `hs`.
    replace h' := hb
    -- at the end the goal must be `x' = x'`.
    rfl
``` -/
partial def mkBeforeToAfter {u : Level} {α : Q(Sort u)} {p : Q($α → Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (newBody : Q(Prop)) (fvars : List VarQ) (path : Path) :
    MetaM <| Q((∃ a, $p a) → $P') := do
  withLocalDeclQ .anonymous .default q(∃ a, $p a) fun h => do
  withLocalDeclQ .anonymous .default q($α) fun a => do
  withLocalDeclQ .anonymous .default q($p $a) fun ha => do
    let pf1 ← withExistsElimAlongPath ha fvars path fun (h_eq : Q($a = $a')) hs => do
      let pf1 : Q($P') ← withNestedExistsIntro fvars (body := newBody) do
        let pf ← go ha fvars hs path h_eq
        pure pf
      pure pf1
    let pf2 : Q(∀ a : $α, $p a → $P') ← mkLambdaFVars #[a, ha] pf1
    let pf3 : Q($P') := q(Exists.elim $h $pf2)
    mkLambdaFVars #[h] pf3
where
  /-- Traverses `P` and `goal` simultaneously, proving `goal`. -/
  go {goal P : Q(Prop)} (h : Q($P)) (exs : List VarQ) (hs : List HypQ) (path : Path)
    {u : Level} {α : Q(Sort u)} {a a' : Q($α)} (h_eq : Q($a = $a')) :
    MetaM Q($goal) := do
  match P with
  | ~q(@Exists $β $pb) =>
    match (generalizing := false) exs with
    | [] => assertUnreachable "mkBeforeToAfter: `P` is `Exists` but `exs` is empty"
    | ⟨v, γ, b⟩ :: exsTail =>
    let _ : u_1 =QL v := ⟨⟩
    let _ : $γ =Q $β := ⟨⟩
    match (generalizing := false) hs with
    | [] => assertUnreachable "mkBeforeToAfter: `P` is `Exists` but `hs` is empty"
    | ⟨H, hb⟩ :: hsTail =>
    let _ : $H =Q $pb $b := ⟨⟩
    let pf : Q($goal) := ← go hb exsTail hsTail path h_eq
    return pf
  | ~q(And $L $R) =>
    let ~q($L' ∧ $R') := goal
      | assertUnreachable "mkBeforeToAfter: `P` is `And` but `goal` is not `And`"
    match (generalizing := false) path with
    | [] => assertUnreachable "mkBeforeToAfter: `P` is `And` but `path` is empty"
    | .left :: tl =>
      let pa : Q($α → Prop) ← mkLambdaFVars #[a] R
      let _ : $R =Q $pa $a := ⟨⟩
      let _ : $R' =Q $pa $a' := ⟨⟩
      let pfRight : Q($R) := q(And.right $h)
      let pfRight' : Q($R') := q(Eq.mp (congrArg $pa $h_eq) $pfRight)
      let pfLeft' : Q($L') ← go q(And.left $h) exs hs tl h_eq
      return q(And.intro $pfLeft' $pfRight')
    | .right :: tl =>
      let pa : Q($α → Prop) ← mkLambdaFVars #[a] L
      let _ : $L =Q $pa $a := ⟨⟩
      let _ : $L' =Q $pa $a' := ⟨⟩
      let pfLeft : Q($L) := q(And.left $h)
      let pfLeft' : Q($L') := q(Eq.mp (congrArg $pa $h_eq) $pfLeft)
      let pfRight' : Q($R') ← go q(And.right $h) exs hs tl h_eq
      return q(And.intro $pfLeft' $pfRight')
  | _ =>
    let ~q($x = $y) := goal
      | assertUnreachable s!"mkBeforeToAfter: unexpected goal = {← ppExpr goal}"
    if !path.isEmpty then
      assertUnreachable "mkBeforeToAfter: goal is equality but path is not empty"
    let _ : $x =Q $y := ⟨⟩
    return q(rfl)

/-- Triggers at goals of the form `∃ a, body` and checks if `body` allows a single value `a'`
for `a`. If so, replaces `a` with `a'` and removes quantifier.

It looks through nested quantifiers and conjuctions searching for a `a = a'`
or `a' = a` subexpression. -/
simproc ↓ existsAndEq (Exists _) := fun e => do
  let_expr f@Exists α p := e | return .continue
  lambdaBoundedTelescope p 1 fun xs (body : Q(Prop)) => withNewMCtxDepth do
    let some u := f.constLevels![0]? | unreachable!
    have α : Q(Sort $u) := α; have p : Q($α → Prop) := p
    let some (a : Q($α)) := xs[0]? | return .continue
    let some path ← findEqPath a body | return .continue
    let (fvars, lctx, newBody, a') ← findEq a body path
    withLCtx' lctx do
      let newBody := newBody.replaceFVar a a'
      let P' : Q(Prop) ← mkNestedExists fvars newBody
      let pfBeforeAfter : Q((∃ a, $p a) → $P') ← mkBeforeToAfter a' newBody fvars path
      let pfAfterBefore : Q($P' → (∃ a, $p a)) ← mkAfterToBefore a' newBody fvars path
      let pf := q(propext (Iff.intro $pfBeforeAfter $pfAfterBefore))
      return .visit <| Simp.ResultQ.mk _ <| some q($pf)

end ExistsAndEq

export ExistsAndEq (existsAndEq)
