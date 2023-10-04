/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kyle Miller
-/
import Mathlib.Lean.Expr
import Mathlib.Util.Syntax
import Std.Data.Option.Basic

/-!
# The notation3 macro, simulating Lean 3's notation.
-/

-- To fix upstream:
-- * bracketedExplicitBinders doesn't support optional types

namespace Mathlib.Notation3
open Lean Parser Meta Elab Command PrettyPrinter.Delaborator SubExpr
open Std.ExtendedBinder

initialize registerTraceClass `notation3

/-! ### Syntaxes supporting `notation3` -/

set_option autoImplicit true

/--
Expands binders into nested combinators.
For example, the familiar exists is given by:
`expand_binders% (p => Exists p) x y : Nat, x < y`
which expands to the same expression as
`∃ x y : Nat, x < y`
-/
syntax "expand_binders% " "(" ident " => " term ")" extBinders ", " term : term

macro_rules
  | `(expand_binders% ($x => $term) $y:extBinder, $res) =>
    `(expand_binders% ($x => $term) ($y:extBinder), $res)
  | `(expand_binders% ($_ => $_), $res) => pure res
macro_rules
  | `(expand_binders% ($x => $term) ($y:ident $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident : $ty ↦ expand_binders% ($x => $term) $[$binders]*, $res)
  | `(expand_binders% ($x => $term) (_%$ph $[: $ty]?) $binders*, $res) => do
    let ty := ty.getD (← `(_))
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun _%$ph : $ty ↦ expand_binders% ($x => $term) $[$binders]*, $res)
  | `(expand_binders% ($x => $term) ($y:ident $pred:binderPred) $binders*, $res) =>
    term.replaceM fun x' ↦ do
      unless x == x' do return none
      `(fun $y:ident ↦ expand_binders% ($x => $term) (h : satisfies_binder_pred% $y $pred)
        $[$binders]*, $res)

macro (name := expandFoldl) "expand_foldl% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldlM (init := init) fun res arg ↦ do
    term.replaceM fun e ↦
      return if e == x then some res else if e == y then some arg else none
macro (name := expandFoldr) "expand_foldr% "
  "(" x:ident ppSpace y:ident " => " term:term ") " init:term:max " [" args:term,* "]" : term =>
  args.getElems.foldrM (init := init) fun arg res ↦ do
    term.replaceM fun e ↦
      return if e == x then some arg else if e == y then some res else none

/-- Keywording indicating whether to use a left- or right-fold. -/
syntax foldKind := &"foldl" <|> &"foldr"
/-- `notation3` argument matching `extBinders`. -/
syntax bindersItem := atomic("(" "..." ")")
/-- `notation3` argument simulating a Lean 3 fold notation. -/
syntax foldAction := "(" ident ppSpace strLit "*" (precedence)? " => " foldKind
  " (" ident ppSpace ident " => " term ") " term ")"
/-- `notation3` argument binding a name. -/
syntax identOptScoped :=
  ident (notFollowedBy(":" "(" "scoped") precedence)? (":" "(" "scoped " ident " => " term ")")?
/-- `notation3` argument. -/
-- Note: there is deliberately no ppSpace between items
-- so that the space in the literals themselves stands out
syntax notation3Item := strLit <|> bindersItem <|> identOptScoped <|> foldAction

/-! ### Expression matching

A more complicated part of `notation3` is the delaborator generator.
While `notation` relies on generating app unexpanders, we instead generate a
delaborator directly so that we can control how binders are formatted (we want
to be able to know the types of binders, whether a lambda is a constant function,
and whether it is `Prop`-valued, which are not things we can answer once we pass
to app unexpanders).
-/

/-- The dynamic state of a `Matcher`. -/
structure MatchState where
  /-- This stores the assignments of variables to subexpressions (and their contexts)
  that have been found so far during the course of the matching algorithm.
  We store the contexts since we need to delaborate expressions after we leave
  scoping constructs. -/
  vars : HashMap Name (SubExpr × LocalContext × LocalInstances)
  /-- The binders accumulated while matching a `scoped` expression. -/
  scopeState : Option (Array (TSyntax ``extBinderParenthesized))
  /-- The arrays of delaborated `Term`s accumulated while matching
  `foldl` and `foldr` expressions. For `foldl`, the arrays are stored in reverse order. -/
  foldState : HashMap Name (Array Term)

/-- A matcher is a delaboration function that transforms `MatchState`s. -/
def Matcher := MatchState → DelabM MatchState
  deriving Inhabited

/-- The initial state. -/
def MatchState.empty : MatchState where
  vars := {}
  scopeState := none
  foldState := {}

/-- Evaluate `f` with the given variable's value as the `SubExpr` and within that subexpression's
saved context. Fails if the variable has no value. -/
def MatchState.withVar (s : MatchState) (name : Name)
    (m : DelabM α) : DelabM α := do
  let some (se, lctx, linsts) := s.vars.find? name | failure
  withLCtx lctx linsts <| withTheReader SubExpr (fun _ => se) <| m

/-- Delaborate the given variable's value. Fails if the variable has no value.
If `checkNot` is provided, then checks that the expression being delaborated is not
the given one (this is used to prevent infinite loops). -/
def MatchState.delabVar (s : MatchState) (name : Name) (checkNot? : Option Expr := none) :
    DelabM Term :=
  s.withVar name do
    if let some checkNot := checkNot? then
      guard <| checkNot != (← getExpr)
    delab

/-- Assign a variable to the current `SubExpr`, capturing the local context. -/
def MatchState.captureSubexpr (s : MatchState) (name : Name) : DelabM MatchState := do
  return {s with vars := s.vars.insert name (← readThe SubExpr, ← getLCtx, ← getLocalInstances)}

/-- Get the accumulated array of delaborated terms for a given foldr/foldl.
Returns `#[]` if nothing has been pushed yet. -/
def MatchState.getFoldArray (s : MatchState) (name : Name) : Array Term :=
  (s.foldState.find? name).getD #[]

/-- Get the accumulated array of delaborated terms for a given foldr/foldl.
Returns `#[]` if nothing has been pushed yet. -/
def MatchState.getBinders (s : MatchState) : Array (TSyntax ``extBinderParenthesized) :=
  s.scopeState.getD #[]

/-- Push a delaborated term onto a foldr/foldl array. -/
def MatchState.pushFold (s : MatchState) (name : Name) (t : Term) : MatchState :=
  let ts := (s.getFoldArray name).push t
  {s with foldState := s.foldState.insert name ts}

/-- Matcher that assigns the current `SubExpr` into the match state;
if a value already exists, then it checks for equality. -/
def matchVar (c : Name) : Matcher := fun s => do
  if let some (se, _, _) := s.vars.find? c then
    guard <| se.expr == (← getExpr)
    return s
  else
    s.captureSubexpr c

/-- Matcher for `Expr.const`. -/
def matchConst (c : Name) : Matcher := fun s => do
  guard <| (← getExpr).isConstOf c
  return s

/-- Matcher for `Expr.fvar`. This is only used for `local notation3`.
It checks that the user name agrees, which isn't completely accurate, but probably sufficient. -/
def matchFVar (userName : Name) : Matcher := fun s => do
  let .fvar fvarId ← getExpr | failure
  guard <| userName == (← fvarId.getUserName)
  return s

/-- Matches raw nat lits and `OfNat.ofNat` expressions. -/
def natLitMatcher (n : Nat) : Matcher := fun s => do
  let mut e ← getExpr
  if e.isAppOfArity ``OfNat.ofNat 3 then
    e := e.getArg! 1
  guard <| e.natLit? == n
  return s

/-- Given an identifier `f`, returns
(1) the resolved constant (if it's not an fvar)
(2) a Term for a matcher for the function
(3) the arity
(4) the positions at which the function takes an explicit argument -/
def getExplicitArgIndices (f : Syntax) :
    OptionT TermElabM (Option Name × Term × Nat × Array Nat) := do
  let fe? ← try liftM <| Term.resolveId? f catch _ => pure none
  match fe? with
  | some fe@(.const f _) =>
    return (some f, ← ``(matchConst $(quote f)), ← collectIdxs (← inferType fe))
  | some fe@(.fvar fvarId) =>
    let userName ← fvarId.getUserName
    return (none, ← ``(matchFVar $(quote userName)), ← collectIdxs (← inferType fe))
  | _ =>
    trace[notation3] "could not resolve name {f}"
    failure
where
  collectIdxs (ty : Expr) : MetaM (Nat × Array Nat) := do
    let (_, binderInfos, _) ← Meta.forallMetaTelescope ty
    let mut idxs := #[]
    for bi in binderInfos, i in [0:binderInfos.size] do
      if bi.isExplicit then
        idxs := idxs.push i
    return (binderInfos.size, idxs)

/-- A matcher that runs `matchf` for the function and the `matchers` for the associated
argument indices. Fails if the function doesn't have exactly `arity` arguments. -/
def fnArgMatcher (arity : Nat) (matchf : Matcher) (matchers : Array (Nat × Matcher)) :
    Matcher := fun s => do
  let mut s := s
  let nargs := (← getExpr).getAppNumArgs
  guard <| nargs == arity
  s ← withNaryFn <| matchf s
  for (i, matcher) in matchers do
    s ← withNaryArg i <| matcher s
  return s

/-- Returns a `Term` that represents a `Matcher` for the given pattern `stx`.
The `boundNames` set determines which identifiers are variables in the pattern.
Fails in the `OptionT` sense if it comes across something it's unable to handle.

Also returns constant names that could serve as a key for a delaborator.
For example, if it's for a function `f`, then `app.f`. -/
partial def mkExprMatcher (stx : Term) (boundNames : HashSet Name) :
    OptionT TermElabM (List Name × Term) := do
  let stx'? ← liftM <| (liftMacroM <| expandMacro? stx : TermElabM (Option Syntax))
  match stx'? with
  | some stx' => mkExprMatcher ⟨stx'⟩ boundNames
  | none =>
    match stx with
    | `(_) => return ([], ← `(pure))
    | `($n:ident) =>
      if boundNames.contains n.getId then
        return ([], ← ``(matchVar $(quote n.getId)))
      else
        processFn n #[]
    | `($f:ident $args*) => processFn f args
    | `(term| $n:num) => return ([], ← ``(natLitMatcher $n))
    | `(($stx)) =>
      if Term.hasCDot stx then
        failure
      else
        mkExprMatcher stx boundNames
    | _ =>
      trace[notation3] "mkExprMatcher can't handle {stx}"
      failure
where
  processFn (f : Term) (args : TSyntaxArray `term) : OptionT TermElabM (List Name × Term) := do
    let (name?, matchf, arity, idxs) ← getExplicitArgIndices f
    unless args.size ≤ idxs.size do
      trace[notation3] "Function {f} has been given more explicit arguments than expected"
      failure
    let mut matchers := #[]
    for i in idxs, arg in args do
      let (_, matcher) ← mkExprMatcher arg boundNames
      matchers := matchers.push <| ← `(($(quote i), $matcher))
    -- `arity'` is the number of arguments (including trailing implicits) given these
    -- explicit arguments. This reflects how the function would be elaborated.
    let arity' := if _ : args.size < idxs.size then idxs[args.size] else arity
    let key? := name?.map (`app ++ ·)
    return (key?.toList, ← ``(fnArgMatcher $(quote arity') $matchf #[$matchers,*]))

/-- Matcher for processing `scoped` syntax. Assumes the expression to be matched
against is in the `lit` variable.

Runs `smatcher`, extracts the resulting `scopeId` variable, processes this value
(which must be a lambda) to produce a binder, and loops. -/
partial def matchScoped (lit scopeId : Name) (smatcher : Matcher) : Matcher := go #[] where
  /-- Variant of `matchScoped` after some number of `binders` have already been captured. -/
  go (binders : Array (TSyntax ``extBinderParenthesized)) : Matcher := fun s => do
    -- `lit` is bound to the SubExpr that the `scoped` syntax produced
    s.withVar lit do
    try
      -- Run `smatcher` at `lit`, clearing the `scopeId` variable so that it can get a fresh value
      let s ← smatcher {s with vars := s.vars.erase scopeId}
      s.withVar scopeId do
        guard (← getExpr).isLambda
        let prop ← try Meta.isProp (← getExpr).bindingDomain! catch _ => pure false
        let isDep := (← getExpr).bindingBody!.hasLooseBVar 0
        let ppTypes ← getPPOption getPPPiBinderTypes -- the same option controlling ∀
        let dom ← withBindingDomain delab
        withBindingBodyUnusedName <| fun x => do
          let x : Ident := ⟨x⟩
          let binder ←
            if prop && !isDep then
              -- this underscore is used to support binder predicates, since it indicates
              -- the variable is unused and this binder is safe to merge into another
              `(extBinderParenthesized|(_ : $dom))
            else if prop || ppTypes then
              `(extBinderParenthesized|($x:ident : $dom))
            else
              `(extBinderParenthesized|($x:ident))
          -- Now use the body of the lambda for `lit` for the next iteration
          let s ← s.captureSubexpr lit
          -- TODO merge binders as an inverse to `satisfies_binder_pred%`
          let binders := binders.push binder
          go binders s
    catch _ =>
      guard <| !binders.isEmpty
      if let some binders₂ := s.scopeState then
        guard <| binders == binders₂ -- TODO: this might be a bit too strict, but it seems to work
        return s
      else
        return {s with scopeState := binders}

/- Create a `Term` that represents a matcher for `scoped` notation.
Fails in the `OptionT` sense if a matcher couldn't be constructed.
Also returns a delaborator key like in `mkExprMatcher`.
Reminder: `$lit:ident : (scoped $scopedId:ident => $scopedTerm:Term)` -/
partial def mkScopedMatcher (lit scopeId : Name) (scopedTerm : Term) (boundNames : HashSet Name) :
    OptionT TermElabM (List Name × Term) := do
  -- Build the matcher for `scopedTerm` with `scopeId` as an additional variable
  let (keys, smatcher) ← mkExprMatcher scopedTerm (boundNames.insert scopeId)
  return (keys, ← ``(matchScoped $(quote lit) $(quote scopeId) $smatcher))

/-- Matcher for expressions produced by `foldl`. -/
partial def matchFoldl (lit x y : Name) (smatcher : Matcher) (sinit : Matcher) :
    Matcher := fun s => do
  s.withVar lit do
    let expr ← getExpr
    -- Clear x and y state before running smatcher so it can store new values
    let s := {s with vars := s.vars |>.erase x |>.erase y}
    let some s ← try some <$> smatcher s catch _ => pure none
      | -- We put this here rather than using a big try block to prevent backtracking.
        -- We have `smatcher` match greedily, and then require that `sinit` *must* succeed
        sinit s
    -- y gives the next element of the list
    let s := s.pushFold lit (← s.delabVar y expr)
    -- x gives the next lit
    let some newLit := s.vars.find? x | failure
    -- If progress was not made, fail
    if newLit.1.expr == expr then failure
    -- Progress was made, so recurse
    let s := {s with vars := s.vars.insert lit newLit}
    matchFoldl lit x y smatcher sinit s

/-- Create a `Term` that represents a matcher for `foldl` notation.
Reminder: `( lit ","* => foldl (x y => scopedTerm) init)` -/
partial def mkFoldlMatcher (lit x y : Name) (scopedTerm init : Term) (boundNames : HashSet Name) :
    OptionT TermElabM (List Name × Term) := do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
  let boundNames' := boundNames |>.insert x |>.insert y
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quote x) $(quote y) $smatcher $sinit))

/-- Create a `Term` that represents a matcher for `foldr` notation.
Reminder: `( lit ","* => foldr (x y => scopedTerm) init)` -/
partial def mkFoldrMatcher (lit x y : Name) (scopedTerm init : Term) (boundNames : HashSet Name) :
    OptionT TermElabM (List Name × Term) := do
  -- Build the `scopedTerm` matcher with `x` and `y` as additional variables
  let boundNames' := boundNames |>.insert x |>.insert y
  let (keys, smatcher) ← mkExprMatcher scopedTerm boundNames'
  let (keys', sinit) ← mkExprMatcher init boundNames
  -- N.B. by swapping `x` and `y` we can just use the foldl matcher
  return (keys ++ keys', ← ``(matchFoldl $(quote lit) $(quote y) $(quote x) $smatcher $sinit))

/-! ### The `notation3` command -/

/-- Create a name that we can use for the `syntax` definition, using the
algorithm from `notation`. -/
def mkNameFromSyntax (name? : Option (TSyntax ``namedName))
    (syntaxArgs : Array (TSyntax `stx)) (attrKind : TSyntax ``Term.attrKind) :
    CommandElabM Name := do
  if let some name := name? then
    match name with
    | `(namedName| (name := $n)) => return n.getId
    | _ => pure ()
  let name ← liftMacroM <| mkNameFromParserSyntax `term (mkNullNode syntaxArgs)
  addMacroScopeIfLocal name attrKind

/-- Used when processing different kinds of variables when building the
final delaborator. -/
inductive BoundValueType
  /-- A normal variable, delaborate its expression. -/
  | normal
  /-- A fold variable, use the fold state (but reverse the array). -/
  | foldl
  /-- A fold variable, use the fold state (do not reverse the array). -/
  | foldr

syntax prettyPrintOpt := "(" &"prettyPrint" " := " (&"true" <|> &"false") ")"

/-- Interpret a `prettyPrintOpt`. The default value is `true`. -/
def getPrettyPrintOpt (opt? : Option (TSyntax ``prettyPrintOpt)) : Bool :=
  if let some opt := opt? then
    match opt with
    | `(prettyPrintOpt| (prettyPrint := false)) => false
    | _ => true
  else
    true

/--
`notation3` declares notation using Lean-3-style syntax.

Examples:
```
notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r
notation3 "MyList[" (x", "* => foldr (a b => MyList.cons a b) MyList.nil) "]" => x
```
By default notation is unable to mention any variables defined using `variable`, but
`local notation3` is able to use such local variables.

Use `notation3 (prettyPrint := false)` to keep the command from generating a pretty printer
for the notation.

This command can be used in mathlib4 but it has an uncertain future and was created primarily
for backward compatibility.
-/
elab (name := notation3) doc:(docComment)? attrs?:(Parser.Term.attributes)? attrKind:Term.attrKind
    "notation3" prec?:(precedence)? name?:(namedName)? prio?:(namedPrio)? pp?:(prettyPrintOpt)?
    ppSpace items:(notation3Item)+ " => " val:term : command => do
  -- We use raw `Name`s for variables. This maps variable names back to the
  -- identifiers that appear in `items`
  let mut boundIdents : HashMap Name Ident := {}
  -- Replacements to use for the `macro`
  let mut boundValues : HashMap Name Syntax := {}
  -- The normal/foldl/foldr type of each variable (for delaborator)
  let mut boundType : HashMap Name BoundValueType := {}
  -- Function to get the keys of `boundValues`. This set is used when constructing
  -- patterns for delaboration.
  let getBoundNames (boundValues : HashMap Name Syntax) : HashSet Name :=
    HashSet.empty.insertMany <| boundValues.toArray.map Prod.fst
  -- Function to update `syntaxArgs` and `pattArgs` using `macroArg` syntax
  let pushMacro (syntaxArgs : Array (TSyntax `stx)) (pattArgs : Array Syntax)
      (mac : TSyntax ``macroArg) := do
    let (syntaxArg, pattArg) ← expandMacroArg mac
    return (syntaxArgs.push syntaxArg, pattArgs.push pattArg)
  -- Arguments for the `syntax` command
  let mut syntaxArgs := #[]
  -- Arguments for the LHS pattern in the `macro`. Also used to construct the syntax
  -- when delaborating
  let mut pattArgs := #[]
  -- The matchers to assemble into a delaborator
  let mut matchers := #[]
  -- Whether we've seen a `(...)` item
  let mut hasBindersItem := false
  -- Whether we've seen a `scoped` item
  let mut hasScoped := false
  for item in items do
    match item with
    | `(notation3Item| $lit:str) =>
      -- Can't use `pushMacro` since it inserts an extra variable into the pattern for `str`, which
      -- breaks our delaborator
      syntaxArgs := syntaxArgs.push (← `(stx| $lit:str))
      pattArgs := pattArgs.push <| mkAtomFrom lit lit.1.isStrLit?.get!
    | `(notation3Item| $_:bindersItem) =>
      if hasBindersItem then
        throwErrorAt item "Cannot have more than one `(...)` item."
      hasBindersItem := true
      -- HACK: Lean 3 traditionally puts a space after the main binder atom, resulting in
      -- notation3 "∑ "(...)", "r:(scoped f => sum f) => r
      -- but extBinders already has a space before it so we strip the trailing space of "∑ "
      if let `(stx| $lit:str) := syntaxArgs.back then
        syntaxArgs := syntaxArgs.pop.push (← `(stx| $(quote lit.getString.trimRight):str))
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs (← `(macroArg| binders:extBinders))
    | `(notation3Item| ($id:ident $sep:str* $(prec?)? => $kind ($x $y => $scopedTerm) $init)) =>
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs <| ←
        `(macroArg| $id:ident:sepBy(term $(prec?)?, $sep:str))
      -- N.B. `Syntax.getId` returns `.anonymous` for non-idents
      let scopedTerm' ← scopedTerm.replaceM fun s => pure (boundValues.find? s.getId)
      let init' ← init.replaceM fun s => pure (boundValues.find? s.getId)
      boundIdents := boundIdents.insert id.getId id
      match kind with
        | `(foldKind| foldl) =>
          boundValues := boundValues.insert id.getId <| ←
            `(expand_foldl% ($x $y => $scopedTerm') $init' [$$(.ofElems $id),*])
          boundType := boundType.insert id.getId .foldl
          matchers := matchers.push <|
            mkFoldlMatcher id.getId x.getId y.getId scopedTerm init (getBoundNames boundValues)
        | `(foldKind| foldr) =>
          boundValues := boundValues.insert id.getId <| ←
            `(expand_foldr% ($x $y => $scopedTerm') $init' [$$(.ofElems $id),*])
          boundType := boundType.insert id.getId .foldr
          matchers := matchers.push <|
            mkFoldrMatcher id.getId x.getId y.getId scopedTerm init (getBoundNames boundValues)
        | _ => throwUnsupportedSyntax
    | `(notation3Item| $lit:ident $(prec?)? : (scoped $scopedId:ident => $scopedTerm)) =>
      hasScoped := true
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs <|←
        `(macroArg| $lit:ident:term $(prec?)?)
      matchers := matchers.push <|
        mkScopedMatcher lit.getId scopedId.getId scopedTerm (getBoundNames boundValues)
      let scopedTerm' ← scopedTerm.replaceM fun s => pure (boundValues.find? s.getId)
      boundIdents := boundIdents.insert lit.getId lit
      boundValues := boundValues.insert lit.getId <| ←
        `(expand_binders% ($scopedId => $scopedTerm') $$binders:extBinders,
          $(⟨lit.1.mkAntiquotNode `term⟩):term)
    | `(notation3Item| $lit:ident $(prec?)?) =>
      (syntaxArgs, pattArgs) ← pushMacro syntaxArgs pattArgs <|←
        `(macroArg| $lit:ident:term $(prec?)?)
      boundIdents := boundIdents.insert lit.getId lit
      boundValues := boundValues.insert lit.getId <| lit.1.mkAntiquotNode `term
    | stx => throwUnsupportedSyntax
  if hasScoped && !hasBindersItem then
    throwError "If there is a `scoped` item then there must be a `(...)` item for binders."

  -- 1. The `syntax` command
  let name ← mkNameFromSyntax name? syntaxArgs attrKind
  elabCommand <| ← `(command|
    $[$doc]? $(attrs?)? $attrKind
    syntax $(prec?)? (name := $(Lean.mkIdent name)) $(prio?)? $[$syntaxArgs]* : term)

  -- 2. The `macro_rules`
  let currNamespace : Name ← getCurrNamespace
  -- The `syntax` command puts definitions into the current namespace; we need this
  -- to make the syntax `pat`.
  let fullName := currNamespace ++ name
  trace[notation3] "syntax declaration has name {fullName}"
  let pat : Term := ⟨mkNode fullName pattArgs⟩
  let val' ← val.replaceM fun s => pure (boundValues.find? s.getId)
  let mut macroDecl ← `(macro_rules | `($pat) => `($val'))
  if isLocalAttrKind attrKind then
    -- For local notation, take section variables into account
    macroDecl ← `(section set_option quotPrecheck.allowSectionVars true $macroDecl end)
  elabCommand macroDecl

  -- 3. Create a delaborator
  if getPrettyPrintOpt pp? then
    matchers := matchers.push <| Mathlib.Notation3.mkExprMatcher val (getBoundNames boundValues)
    -- The matchers need to run in reverse order, so may as well reverse them here.
    let matchersM? := (matchers.reverse.mapM id).run
    -- We let local notations have access to `variable` declarations
    let matchers? ← if isLocalAttrKind attrKind then
      runTermElabM fun _ => matchersM?
    else
      liftTermElabM matchersM?
    if let some ms := matchers? then
      trace[notation3] "Matcher creation succeeded; assembling delaborator"
      let delabName := name ++ `delab
      let matcher ← ms.foldrM (fun m t => `($(m.2) >=> $t)) (← `(pure))
      trace[notation3] "matcher: {indentD matcher}"
      let mut result ← `(`($pat))
      for (name, id) in boundIdents.toArray do
        match boundType.findD name .normal with
        | .normal => result ← `(MatchState.delabVar s $(quote name) (some e) >>= fun $id => $result)
        | .foldl => result ←
          `(let $id := (MatchState.getFoldArray s $(quote name)).reverse; $result)
        | .foldr => result ←
          `(let $id := MatchState.getFoldArray s $(quote name); $result)
      if hasBindersItem then
        result ← `(`(extBinders| $$(MatchState.getBinders s)*) >>= fun binders => $result)
      elabCommand <| ← `(command|
        def $(Lean.mkIdent delabName) : Delab := whenPPOption getPPNotation <|
          getExpr >>= fun e => $matcher MatchState.empty >>= fun s => $result)
      trace[notation3] "Defined delaborator {currNamespace ++ delabName}"
      let delabKeys := ms.foldr (·.1 ++ ·) []
      trace[notation3] "Adding `delab` attribute for keys {delabKeys}"
      for key in delabKeys do
        elabCommand <| ← `(command| attribute [delab $(mkIdent key)] $(Lean.mkIdent delabName))
    else
      logWarning s!"Could not generate matchers for a delaborator, so notation will not be pretty{
        ""} printed. Consider either adjusting the expansions or use{
        ""} `notation3 (prettyPrint := false)`."

initialize Std.Linter.UnreachableTactic.addIgnoreTacticKind ``«notation3»
