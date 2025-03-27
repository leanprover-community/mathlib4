/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
import Mathlib.Init
import Qq

/-!
# simproc for `∃ a', ... ∧ a' = a ∧ ...`

This module implements the `existsAndEq` simproc that triggers on goals of the form `∃ a, P`,
checks if `P` allows only one value for `a` and if so, substitute it elimination leading quantifier.
It traverses the body branching at each `∧` and enterring existential quantifiers looking for a
subexpression of the form `a = a'` or `a' = a`. If such expression found all occurances of `a`
are replaced with `a'`. If `a'` depends on some variables bounded by enterred existential
quantifiers those quantifiers are moved outside.

For example `∃ a, p a ∧ ∃ b, a = f b ∧ q b` will be rewrited as `∃ b, p (f b) ∧ q b`.
-/

open Lean Meta Qq

namespace existsAndEq

/-- Type for storing chosen branch at `And` nodes. -/
inductive GoTo
| left | right
deriving BEq, Inhabited

/-- Type for storing path in the body expression leading to `a = a'`. We store only chosen
directions at each `And` node, because there is no branching at `Exists` nodes. -/
abbrev Path := List GoTo

/-- TODO: does it already exists? -/
abbrev FvarQ := (u : Level) × (α : Q(Sort u)) × Q($α)

instance : Inhabited FvarQ where
  default := ⟨default, default, default⟩

/-- TODO: does it already exists? -/
abbrev HypQ := (P : Q(Prop)) × Q($P)

instance : Inhabited HypQ where
  default := ⟨default, default⟩

/-- Makes `∃ f₁ f₂ ... fₙ, body` where `[f₁, ..., fₙ] = fvars`. -/
def mkNestedExists (fvars : List FvarQ) (body : Expr) : MetaM Expr := do
  match fvars with
  | [] => pure body
  | ⟨_, β, b⟩ :: tl =>
    let res ← mkNestedExists tl body
    pure <| ← mkAppOptM ``Exists #[.some β, .some <| ← mkLambdaFVars #[b] res]

/-- Finds path for `findEq`. It is a fast version that should quickly return `none` when the simproc
is not applicable. -/
partial def findEqPath {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) :
    MetaM <| Option Path := do
  match_expr P with
  | Eq _ x y =>
    if a == x then
      if !(y.containsFVar a.fvarId!) then
        return .some []
      return .none
    else if a == (y : Q($α)) then
      if !(x.containsFVar a.fvarId!) then
        return .some []
      return .none
    else
      return .none
  | And L R =>
    if let .some path ← findEqPath a L then
      return .some (.left :: path)
    if let .some path ← findEqPath a R then
      return .some (.right :: path)
    return none
  | Exists _ pb =>
    let .lam _ _ body _ := pb | return none
    if let .some path ← findEqPath a body then
      pure <| .some path
    else
      pure .none
  | _ => return none

/-- Given `P : Prop` and `a : α` traverses the expression `P` aiming to find some subexpression of
the form `a = a'` or `a' = a` for some `a'`. It branches at each `And` and walks into existential
quantifiers. It returns tuple `(P', a', lctx, fvars, path)` where
* `path` is a `Path` leading to found subexpression.
* `a'` is found expression that must be equal to `a`.
* `fvars` is a list of all variables binded by existential quantifiers along the path
* `lctx` is a local context containing all these fvars
* `P'` is `P` with all existential quantifiers along the path removed and corresponding bvars
  replaced with `fvars`. -/
partial def findEq {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) :
    MetaM <| Option (Q(Prop) × Q($α) × LocalContext × List FvarQ × Path) := do
  let .some path ← findEqPath a P | return none
  let .some (res, a', lctx, fvars) ← go a P path | failure
  return (res, a', lctx, fvars, path)
where
  /-- Recursive part of `findEq`. -/
  go {u : Level} {α : Q(Sort u)} (a : Q($α)) (P : Q(Prop)) (path : Path) :
    MetaM <| Option (Q(Prop) × Q($α) × LocalContext × List FvarQ) := do
  match P with
  | ~q(@Eq.{u} $γ $x $y) =>
    let .defEq _ := ← isDefEqQ q($α) q($γ) | return none
    if let .defEq _ ← isDefEqQ a x then
      if !(y.containsFVar a.fvarId!) then
        return .some (P, y, ← getLCtx, [])
      return .none
    else if let .defEq _ ← isDefEqQ a (y : Q($α)) then
      if !(x.containsFVar a.fvarId!) then
        return .some (P, x, ← getLCtx, [])
      return .none
    else
      return .none
  | ~q($L ∧ $R) =>
    let goto := path.head!
    let tl := path.tail
    if goto == .left then
      let .some (res, a', lctx, fvars) ← go a q($L) tl | failure
      return .some (q($res ∧ $R), a', lctx, fvars)
    else
      let .some (res, a', lctx, fvars) ← go a q($R) tl | failure
      return .some (q($L ∧ $res), a', lctx, fvars)
  | ~q(@Exists $β $pb) =>
    lambdaBoundedTelescope pb 1 fun bs (body : Q(Prop)) => do
      let #[(b : Q($β))] := bs | failure
      if let .some (res, a', lctx, fvars) ← go a q($body) path then
        pure <| .some (res, a', lctx, ⟨_, _, b⟩ :: fvars)
      else
        pure .none
  | _ => return none

/--
When `P = ∃ f₁ ... fₙ, body` where `exs = [f₁, ..., fₙ]`, it takes `act : body → goal` and
proves `P → goal` using `Exists.elim`.

Example:
```
exs = []: act h
exs = [b]:
  P == ∃ b, body
  Exists.elim h (fun b hb ↦ act hb)
exs = [b, c]:
  P == ∃ c b, body
  Exists.elim h (fun c hc ↦
    Exists.elim hc (fun b hb ↦ act hb)
  )
...
```
-/
def withNestedExistsElim {P body goal : Q(Prop)} (exs : List FvarQ) (h : Q($P))
    (act : Q($body) → MetaM Q($goal)) : MetaM Q($goal) := do
  match exs with
  | [] =>
    let _ : $P =Q $body := ⟨⟩
    return ← act q($h)
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P | failure
    let _ : $β =Q $γ := ⟨⟩
    withLocalDeclQ .anonymous .default q($p $b) fun hb => do
      let pf1 ← withNestedExistsElim tl hb act
      let pf2 : Q(∀ b, $p b → $goal) ← mkLambdaFVars #[b, hb] pf1
      let pf3 := q(Exists.elim $h $pf2)
      return pf3

/--
When `P = ∃ f₁ ... fₙ, body` where `exs = [f₁, ..., fₙ]`, it takes `act : body` and
proves `P` using `Exists.intro`.

Example:
```
exs = []: act
exs = [b]:
  P == ∃ b, body
  Exists.intro b act
exs = [b, c]:
  P == ∃ c b, body
  Exists.intro c (Exists.intro b act)
...
```
-/
def withNestedExistsIntro {P body : Q(Prop)} (exs : List FvarQ)
    (act : MetaM Q($body)) : MetaM Q($P) := do
  match exs with
  | [] =>
    let _ : $P =Q $body := ⟨⟩
    return ← act
  | ⟨u, β, b⟩ :: tl =>
    let ~q(@Exists.{u} $γ $p) := P | failure
    let _ : $β =Q $γ := ⟨⟩
    let pf ← withNestedExistsIntro tl act
    return q(Exists.intro $b $pf)

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
```
-/
partial def mkAfterToBefore {u : Level} {α : Q(Sort u)} {p : Q($α → Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (newBody : Q(Prop)) (fvars : List FvarQ) (path : Path) :
    MetaM <| Q($P' → (∃ a, $p a)) := do
  withLocalDeclQ .anonymous .default P' fun (h : Q($P')) => do
    let pf : Q(∃ a, $p a) ← withNestedExistsElim fvars h fun (h : Q($newBody)) => do
      let pf1 : Q($p $a') ← go h fvars path
      let pf2 : Q(∃ a, $p a) := q(Exists.intro $a' $pf1)
      return pf2
    return ← mkLambdaFVars #[h] pf
where
  /-- Traverses `P` and `goal` simultaneously, proving `goal`. -/
  go {goal P : Q(Prop)} (h : Q($P)) (exs : List FvarQ) (path : Path) :
    MetaM Q($goal) := do
  match goal with
  | ~q(@Exists $β $pb) =>
    let ⟨v, γ, c⟩ := exs.head! -- TODO : why matching fails?
    let _ : u_1 =QL v := ⟨⟩
    let _ : $γ =Q $β := ⟨⟩
    let pf1 : Q($pb $c) := ← go h exs.tail path
    return q(Exists.intro $c $pf1)
  | ~q(And $L $R) =>
      let goto := path.head! -- TODO : why matching fails?
      let tl := path.tail
      if goto == .left then -- TODO : why matching fails?
        let ~q($L' ∧ $R') := P | failure
        let _ : $R =Q $R' := ⟨⟩
        let pfRight : Q($R) := q(And.right $h)
        let pfLeft : Q($L) ← go q(And.left $h) exs tl
        return q(And.intro $pfLeft $pfRight)
      else
        let ~q($L' ∧ $R') := P | failure
        let _ : $L =Q $L' := ⟨⟩
        let pfLeft : Q($L) := q(And.left $h)
        let pfRight : Q($R) ← go q(And.right $h) exs tl
        return q(And.intro $pfLeft $pfRight)
  | _ =>
    if !path.isEmpty then failure
    let ~q($x = $y) := goal | failure
    return ← mkEqRefl x

/-- Recursive implementation for `withExistsElimAlongPath`. -/
partial def withExistsElimAlongPathImp {u : Level} {α : Q(Sort u)}
    {P goal : Q(Prop)} (h : Q($P)) {a a' : Q($α)} (exs : List FvarQ) (path : Path)
    (hs : List HypQ)
    (act : Q($a = $a') → List HypQ → MetaM Q($goal)) :
    MetaM Q($goal) := do
  match P with
  | ~q(@Exists $β $pb) =>
    let ⟨v, γ, b⟩ := exs.head! -- TODO : why matching fails?
    let _ : u_1 =QL v := ⟨⟩
    let _ : $γ =Q $β := ⟨⟩
    withLocalDeclQ .anonymous .default q($pb $b) fun hb => do
      let newHs := hs ++ [⟨_, hb⟩]
      let pf1 ← withExistsElimAlongPathImp (P := q($pb $b)) hb exs.tail path newHs act
      let pf2 : Q(∀ b, $pb b → $goal) ← mkLambdaFVars #[b, hb] pf1
      let pf3 : Q($goal) := q(Exists.elim $h $pf2)
      return pf3
  | ~q(And $L' $R') =>
      let goto := path.head! -- TODO : why matching fails?
      let tl := path.tail
      if goto == .left then -- TODO : why matching fails?
        return ← withExistsElimAlongPathImp q(And.left $h) exs tl hs act
      else
        return ← withExistsElimAlongPathImp q(And.right $h) exs tl hs act
  | ~q(@Eq.{u} $γ $x $y) =>
    let _ : $γ =Q $α := ⟨⟩
    if !path.isEmpty then failure
    if let .defEq _ ← isDefEqQ a x then
      let _ : $a' =Q $y := ⟨⟩
      return ← act q($h) hs
    else if let .defEq _ ← isDefEqQ a y then
      let _ : $a' =Q $x := ⟨⟩
      return ← act q(Eq.symm $h) hs
    else
      failure
  | _ => failure

/-- Given `act : (a = a') → hb₁ → hb₂ → ... → hbₙ → goal` where `hb₁, ..., hbₙ` are hypotheses
obtained when unpacking existential quantifiers with variables from `exs`, it proves `goal` using
`Exists.elim`. We use this to prove implication in the forward direction. -/
def withExistsElimAlongPath {u : Level} {α : Q(Sort u)}
    {P goal : Q(Prop)} (h : Q($P)) {a a' : Q($α)} (exs : List FvarQ) (path : Path)
    (act : Q($a = $a') → List HypQ → MetaM Q($goal)) :
    MetaM Q($goal) :=
  withExistsElimAlongPathImp h exs path [] act

/--
Generates a proof of `∃ a, p a → P'`. We assume that `fvars = [f₁, ..., fₙ]` are free variables
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
```
-/
partial def mkBeforeToAfter {u : Level} {α : Q(Sort u)} {p : Q($α → Prop)}
    {P' : Q(Prop)} (a' : Q($α)) (newBody : Q(Prop)) (fvars : List FvarQ) (path : Path) :
    MetaM <| Q((∃ a, $p a) → $P') := do
  withLocalDeclQ .anonymous .default q(∃ a, $p a) fun h => do
  withLocalDeclQ .anonymous .default q($α) fun a => do
  withLocalDeclQ .anonymous .default q($p $a) fun ha => do
    let pf1 ← withExistsElimAlongPath ha fvars path fun (h_eq : Q($a = $a')) hs =>
    do
      let pf1 : Q($P') ← withNestedExistsIntro fvars (body := newBody) do
        let pf ← go ha fvars hs path h_eq
        pure pf
      pure pf1
    let pf2 : Q(∀ a : $α, $p a → $P') ← mkLambdaFVars #[a, ha] pf1
    let pf3 : Q($P') := q(Exists.elim $h $pf2)
    return ← mkLambdaFVars #[h] pf3
where
  /-- Traverses `P` and `goal` simultaneously, proving `goal`. -/
  go {goal P : Q(Prop)} (h : Q($P)) (exs : List FvarQ) (hs : List HypQ) (path : Path)
    {u : Level} {α : Q(Sort u)} {a a' : Q($α)} (h_eq : Q($a = $a')) :
    MetaM Q($goal) := do
  match P with
  | ~q(@Exists $β $pb) =>
    let ⟨v, γ, b⟩ := exs.head! -- TODO : why matching fails?
    let _ : u_1 =QL v := ⟨⟩
    let _ : $γ =Q $β := ⟨⟩
    let ⟨H, hb⟩ := hs.head!
    let _ : $H =Q $pb $b := ⟨⟩
    let pf : Q($goal) := ← go hb exs.tail hs.tail path h_eq
    return pf
  | ~q(And $L $R) =>
      let goto := path.head! -- TODO : why matching fails?
      let tl := path.tail
      if goto == .left then -- TODO : why matching fails?
        let ~q($L' ∧ $R') := goal | failure
        let pa : Q($α → Prop) ← mkLambdaFVars #[a] R
        let _ : $R =Q $pa $a := ⟨⟩
        let _ : $R' =Q $pa $a' := ⟨⟩
        let pfRight : Q($R) := q(And.right $h)
        let pfRight' : Q($R') := q(Eq.mp (congrArg $pa $h_eq) $pfRight)
        let pfLeft' : Q($L') ← go q(And.left $h) exs hs tl h_eq
        return q(And.intro $pfLeft' $pfRight')
      else
        let ~q($L' ∧ $R') := goal | failure
        let pa : Q($α → Prop) ← mkLambdaFVars #[a] L
        let _ : $L =Q $pa $a := ⟨⟩
        let _ : $L' =Q $pa $a' := ⟨⟩
        let pfLeft : Q($L) := q(And.left $h)
        let pfLeft' : Q($L') := q(Eq.mp (congrArg $pa $h_eq) $pfLeft)
        let pfRight' : Q($R') ← go q(And.right $h) exs hs tl h_eq
        return q(And.intro $pfLeft' $pfRight')
  | _ =>
    if !path.isEmpty then failure
    let ~q($x = $y) := goal | failure
    return ← mkEqRefl x

/-- Implementation of `existsAndEqNested` simproc. -/
def existsAndEqNestedImp {u : Level} {α : Q(Sort u)} (p : Q($α → Prop)) :
    MetaM <| Option <| (P' : Q(Prop)) × Q((∃ a, $p a) = $P') := do
  lambdaBoundedTelescope p 1 fun xs (body : Q(Prop)) => withNewMCtxDepth do
    let #[(a : Q($α))] := xs | return .none
    let .some (newBody, a', lctx, fvars, path) ← findEq a body | return .none
    withLCtx' lctx do
      let newBody := newBody.replaceFVar a a'
      let (P' : Q(Prop)) ← mkNestedExists fvars newBody
      let pfBeforeAfter : Q((∃ a, $p a) → $P') ← mkBeforeToAfter a' newBody fvars path
      let pfAfterBefore : Q($P' → (∃ a, $p a)) ← mkAfterToBefore a' newBody fvars path
      let pf := q(propext (Iff.intro $pfBeforeAfter $pfAfterBefore))
      return .some ⟨P', pf⟩

end existsAndEq

/-- Triggers at goal of the form `∃ a, body` and checks if `body` allows a single value `a'`
for `a`. If so, replaces `a` with `a'` and removes quantifier.

It looks through nested quantifiers and conjuctions searching for a `a = a'`
or `a' = a` subexpression. -/
simproc existsAndEqNested (Exists _) := .ofQ fun u α e => do
  match u, α, e with
  | 1, ~q(Prop), ~q(@Exists $α $p) =>
    let .some ⟨P', pf⟩ ← existsAndEq.existsAndEqNestedImp p | return .continue
    return .visit {expr := P', proof? := pf}
  | _, _, _ => return .continue
