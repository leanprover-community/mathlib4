/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jacob von Raumer
-/
import Lean

/-!

# Recursive cases (`rcases`) tactic and related tactics

`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alternation pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

The patterns are fairly liberal about the exact shape of the constructors, and will insert
additional alternation branches and tuple arguments if there are not enough arguments provided, and
reuse the tail for further matches if there are too many arguments provided to alternation and
tuple patterns.

This file also contains the `obtain` and `rintro` tactics, which use the same syntax of `rcases`
patterns but with a slightly different use case:

* `rintro` (or `rintros`) is used like `rintro x ⟨y, z⟩` and is the same as `intros` followed by
  `rcases` on the newly introduced arguments.
* `obtain` is the same as `rcases` but with a syntax styled after `have` rather than `cases`.
  `obtain ⟨hx, hy⟩ | hz := foo` is equivalent to `rcases foo with ⟨hx, hy⟩ | hz`. Unlike `rcases`,
  `obtain` also allows one to omit `:= foo`, although a type must be provided in this case,
  as in `obtain ⟨hx, hy⟩ | hz : a ∧ b ∨ c`, in which case it produces a subgoal for proving
  `a ∧ b ∨ c` in addition to the subgoals `hx : a, hy : b |- goal` and `hz : c |- goal`.

## Tags

rcases, rintro, obtain, destructuring, cases, pattern matching, match
-/

namespace Lean.Parser.Tactic

/-- The syntax category of `rcases` patterns. -/
declare_syntax_cat rcasesPat
syntax rcasesPatMed := sepBy1(rcasesPat, " | ")
syntax rcasesPatLo := rcasesPatMed (" : " term)?
syntax (name := rcasesPat.one) ident : rcasesPat
syntax (name := rcasesPat.ignore) "_" : rcasesPat
syntax (name := rcasesPat.clear) "-" : rcasesPat
syntax (name := rcasesPat.tuple) "⟨" rcasesPatLo,* "⟩" : rcasesPat
syntax (name := rcasesPat.paren) "(" rcasesPatLo ")" : rcasesPat

/-- The syntax category of `rintro` patterns. -/
declare_syntax_cat rintroPat
syntax (name := rintroPat.one) rcasesPat : rintroPat
syntax (name := rintroPat.binder) "(" rintroPat+ (" : " term)? ")" : rintroPat

end Lean.Parser.Tactic

/- A list, with a disjunctive meaning (like a list of inductive constructors, or subgoals) -/
local notation "ListΣ" => List

/- A list, with a conjunctive meaning (like a list of constructor arguments, or hypotheses) -/
local notation "ListΠ" => List

namespace Lean.Meta

/-- Constructs a substitution consisting of `s` followed by `t`.
  This satisfies `(s.append t).apply e = t.apply (s.apply e)` -/
def FVarSubst.append (s t : FVarSubst) : FVarSubst :=
  s.1.foldl (fun s' k v => s'.insert k (t.apply v)) t

namespace RCases

/--
An `rcases` pattern can be one of the following, in a nested combination:

* A name like `foo`
* The special keyword `rfl` (for pattern matching on equality using `subst`)
* A hyphen `-`, which clears the active hypothesis and any dependents.
* A type ascription like `pat : ty` (parentheses are optional)
* A tuple constructor like `⟨p1, p2, p3⟩`
* An alternation / variant pattern `p1 | p2 | p3`

Parentheses can be used for grouping; alternation is higher precedence than type ascription, so
`p1 | p2 | p3 : ty` means `(p1 | p2 | p3) : ty`.

N-ary alternations are treated as a group, so `p1 | p2 | p3` is not the same as `p1 | (p2 | p3)`,
and similarly for tuples. However, note that an n-ary alternation or tuple can match an n-ary
conjunction or disjunction, because if the number of patterns exceeds the number of constructors in
the type being destructed, the extra patterns will match on the last element, meaning that
`p1 | p2 | p3` will act like `p1 | (p2 | p3)` when matching `a1 ∨ a2 ∨ a3`. If matching against a
type with 3 constructors,  `p1 | (p2 | p3)` will act like `p1 | (p2 | p3) | _` instead.
-/
inductive RCasesPatt : Type
| one : Syntax → Name → RCasesPatt
| clear : Syntax → RCasesPatt
| typed : Syntax → RCasesPatt → Syntax → RCasesPatt
| tuple : Syntax → ListΠ RCasesPatt → RCasesPatt
| alts : Syntax → ListΣ RCasesPatt → RCasesPatt
deriving Repr

namespace RCasesPatt

instance : Inhabited RCasesPatt := ⟨RCasesPatt.one Syntax.missing `_⟩

/-- Get the name from a pattern, if provided -/
partial def name? : RCasesPatt → Option Name
| one _ `_    => none
| one _ `rfl  => none
| one _ n     => n
| typed _ p _ => p.name?
| alts _ [p]  => p.name?
| _           => none

/-- Get the syntax node from which this pattern was parsed. Used for error messages -/
def ref : RCasesPatt → Syntax
| one ref _ => ref
| clear ref => ref
| typed ref _ _ => ref
| tuple ref _ => ref
| alts ref _ => ref

/-- Interpret an rcases pattern as a tuple, where `p` becomes `⟨p⟩`
if `p` is not already a tuple. -/
def asTuple : RCasesPatt → ListΠ RCasesPatt
| tuple _ ps => ps
| p          => [p]

/-- Interpret an rcases pattern as an alternation, where non-alternations are treated as one
alternative. -/
def asAlts : RCasesPatt → ListΣ RCasesPatt
| alts _ ps => ps
| p         => [p]

/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
def typed? (ref : Syntax) : RCasesPatt → Option Syntax → RCasesPatt
| p, none => p
| p, some ty => typed ref p ty

/-- Convert a list of patterns to a tuple pattern, but mapping `[p]` to `p` instead of `⟨p⟩`. -/
def tuple' : ListΠ RCasesPatt → RCasesPatt
| [p] => p
| ps  => tuple (ps.head?.map (·.ref) |>.getD Syntax.missing) ps

/-- Convert a list of patterns to an alternation pattern, but mapping `[p]` to `p` instead of
a unary alternation `|p`. -/
def alts' (ref : Syntax) : ListΣ RCasesPatt → RCasesPatt
| [p] => p
| ps  => alts ref ps

/-- This function is used for producing rcases patterns based on a case tree. Suppose that we have
a list of patterns `ps` that will match correctly against the branches of the case tree for one
constructor. This function will merge tuples at the end of the list, so that `[a, b, ⟨c, d⟩]`
becomes `⟨a, b, c, d⟩` instead of `⟨a, b, ⟨c, d⟩⟩`.

We must be careful to turn `[a, ⟨⟩]` into `⟨a, ⟨⟩⟩` instead of `⟨a⟩` (which will not perform the
nested match). -/
def tuple₁Core : ListΠ RCasesPatt → ListΠ RCasesPatt
| []         => []
| [tuple ref []] => [tuple ref []]
| [tuple _ ps] => ps
| p :: ps    => p :: tuple₁Core ps

/-- This function is used for producing rcases patterns based on a case tree. This is like
`tuple₁Core` but it produces a pattern instead of a tuple pattern list, converting `[n]` to `n`
instead of `⟨n⟩` and `[]` to `_`, and otherwise just converting `[a, b, c]` to `⟨a, b, c⟩`. -/
def tuple₁ : ListΠ RCasesPatt → RCasesPatt
| []      => default
| [one ref n] => one ref n
| ps      => tuple ps.head!.ref $ tuple₁Core ps

/-- This function is used for producing rcases patterns based on a case tree. Here we are given
the list of patterns to apply to each argument of each constructor after the main case, and must
produce a list of alternatives with the same effect. This function calls `tuple₁` to make the
individual alternatives, and handles merging `[a, b, c | d]` to `a | b | c | d` instead of
`a | b | (c | d)`. -/
def alts₁Core : ListΣ (ListΠ RCasesPatt) → ListΣ RCasesPatt
| []          => []
| [[alts _ ps]] => ps
| p :: ps     => tuple₁ p :: alts₁Core ps

/-- This function is used for producing rcases patterns based on a case tree. This is like
`alts₁Core`, but it produces a cases pattern directly instead of a list of alternatives. We
specially translate the empty alternation to `⟨⟩`, and translate `|(a | b)` to `⟨a | b⟩` (because we
don't have any syntax for unary alternation). Otherwise we can use the regular merging of
alternations at the last argument so that `a | b | (c | d)` becomes `a | b | c | d`. -/
def alts₁ (ref : Syntax) : ListΣ (ListΠ RCasesPatt) → RCasesPatt
| [[]]        => tuple Syntax.missing []
| [[alts ref ps]] => tuple ref ps
| ps          => alts' ref $ alts₁Core ps

open MessageData in
partial instance : ToMessageData RCasesPatt := ⟨fmt 0⟩ where
  parenAbove (tgt p : Nat) (m : MessageData) : MessageData :=
    if tgt < p then m.paren else m
  fmt : Nat → RCasesPatt → MessageData
  | _, one _ n => n
  | _, clear _ => "-"
  | p, typed _ pat ty => parenAbove 0 p m!"{fmt 1 pat}: {ty}"
  | _, tuple _ pats => bracket "⟨" (joinSep (pats.map (fmt 0)) ("," ++ Format.line)) "⟩"
  | p, alts _ pats => parenAbove 1 p (joinSep (pats.map (fmt 2)) " | ")

end RCasesPatt

/-- Takes the number of fields of a single constructor and patterns to match its fields against
(not necessarily the same number). The returned lists each contain one element per field of the
constructor. The `name` is the name which will be used in the top-level `cases` tactic, and the
`rcases_patt` is the pattern which the field will be matched against by subsequent `cases`
tactics. -/
def processConstructor (ref : Syntax) : Nat → ListΠ RCasesPatt → ListΠ Name × ListΠ RCasesPatt
| 0,     _       => ([], [])
| 1,     []      => ([`_], [default])
| 1,     [p]     => ([p.name?.getD `_], [p])
| 1,     ps      => ([`_], [RCasesPatt.tuple ref ps])
| n + 1, p :: ps => let (ns, tl) := processConstructor ref n ps
                    (p.name?.getD `_ :: ns, p :: tl)
| _,     _       => ([], [])

/-- Takes a list of constructor names, and an (alternation) list of patterns, and matches each
pattern against its constructor. It returns the list of names that will be passed to `cases`,
and the list of `(constructor name, patterns)` for each constructor, where `patterns` is the
(conjunctive) list of patterns to apply to each constructor argument. -/
def processConstructors (ref : Syntax) (params : Nat) (altVarNames : Array AltVarNames := #[]) :
  ListΣ Name → ListΣ RCasesPatt → MetaM (Array AltVarNames × ListΣ (Name × ListΠ RCasesPatt))
| [], _ => pure (altVarNames, [])
| c :: cs, ps => do
  let n := FunInfo.getArity $ ← getFunInfo (← mkConstWithLevelParams c)
  let p := ps.headD default
  let t := ps.tailD []
  let (h, t) := match cs, t with
  | [], _ :: _ => ([RCasesPatt.alts ref ps], [])
  | _,  _      => (p.asTuple, t)
  let (ns, ps) := processConstructor p.ref (n - params) h
  let (altVarNames, r)  ← processConstructors ref params (altVarNames.push ⟨true, ns⟩) cs t
  pure (altVarNames, (c, ps) :: r)

open Elab Tactic

-- this belongs in core; it is a variation on subst that passes fvarSubst through
def subst' (mvarId : MVarId) (hFVarId : FVarId)
  (fvarSubst : FVarSubst := {}) : MetaM (FVarSubst × MVarId) := do
  let hLocalDecl ← hFVarId.getDecl
  let error {α} _ : MetaM α := throwTacticEx `subst mvarId
    m!"invalid equality proof, it is not of the form (x = t) or (t = x){indentExpr hLocalDecl.type}"
  let some (_, lhs, rhs) ← matchEq? hLocalDecl.type | error ()
  let substReduced (newType : Expr) (symm : Bool) : MetaM (FVarSubst × MVarId) := do
    let mvarId ← mvarId.assert hLocalDecl.userName newType (mkFVar hFVarId)
    let (hFVarId', mvarId) ← mvarId.intro1P
    let mvarId ← mvarId.clear hFVarId
    substCore mvarId hFVarId' (symm := symm) (tryToSkip := true) (fvarSubst := fvarSubst)
  let rhs' ← whnf rhs
  if rhs'.isFVar then
    if rhs != rhs' then
      substReduced (← mkEq lhs rhs') true
    else
      substCore mvarId hFVarId (symm := true) (tryToSkip := true) (fvarSubst := fvarSubst)
  else
    let lhs' ← whnf lhs
    if lhs'.isFVar then
      if lhs != lhs' then
        substReduced (← mkEq lhs' rhs) false
      else
        substCore mvarId hFVarId (symm := false) (tryToSkip := true) (fvarSubst := fvarSubst)
    else error ()

mutual

/-- This will match a pattern `pat` against a local hypothesis `e`.
  * `g`: The initial subgoal
  * `fs`: A running variable substitution, the result of `cases` operations upstream.
    The variable `e` must be run through this map before locating it in the context of `g`,
    and the output variable substitutions will be end extensions of this one.
  * `clears`: The list of variables to clear in all subgoals generated from this point on.
    We defer clear operations because clearing too early can cause `cases` to fail.
    The actual clearing happens in `RCases.finish`.
  * `e`: a local hypothesis, the scrutinee to match against.
  * `a`: opaque "user data" which is passed through all the goal calls at the end.
  * `pat`: the pattern to match against
  * `cont`: A continuation. This is called on every goal generated by the result of the pattern
    match, with updated values for `g` , `fs`, `clears`, and `a`. -/
partial def rcasesCore (g : MVarId) (fs : FVarSubst) (clears : Array FVarId) (e : FVarId) (a : α)
  (pat : RCasesPatt) (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) : TermElabM α :=
  let translate e : MetaM _ := do
    let e := fs.get e
    unless e.isFVar do
      throwError "rcases tactic failed: {e} is not a fvar"
    pure e
  withRef pat.ref <| g.withContext <| match pat with
  | RCasesPatt.one _ `rfl => do
    let (fs, g) ← subst' g (← translate e).fvarId! fs
    cont g fs clears a
  | RCasesPatt.one _ _ => cont g fs clears a
  | RCasesPatt.clear _ => cont g fs (clears.push e) a
  | RCasesPatt.typed _ pat ty => do
    let expected ← Term.elabType ty
    let e ← translate e
    let etype ← inferType e
    unless ← isDefEq etype expected do
      Term.throwTypeMismatchError "rcases: scrutinee" expected etype e
    let g ← g.replaceLocalDeclDefEq e.fvarId! expected
    rcasesCore g fs clears e.fvarId! a pat cont
  | RCasesPatt.alts _ [p] => rcasesCore g fs clears e a p cont
  | _ => do
    let e ← translate e
    let type ← whnfD (← inferType e)
    let failK {α} _ : TermElabM α :=
      throwError "rcases tactic failed: {e} : {type} is not an inductive datatype"
    let (r, subgoals) ← matchConst type.getAppFn failK fun
      | ConstantInfo.quotInfo info, _ => do
        unless info.kind matches QuotKind.type do failK ()
        let pat := pat.asAlts.headD default
        let ([x], ps) := processConstructor pat.ref 1 pat.asTuple | panic! "rcases"
        let (vars, g) ← g.revert (← getFVarsToGeneralize #[e])
        g.withContext do
          let elimInfo ← getElimInfo `Quot.ind
          let res ← ElimApp.mkElimApp elimInfo #[e] (← g.getTag)
          let elimArgs := res.elimApp.getAppArgs
          ElimApp.setMotiveArg g elimArgs[elimInfo.motivePos]!.mvarId! #[e.fvarId!]
          g.assign res.elimApp
          let #[(n, g)] := res.alts | panic! "rcases"
          let (v, g) ← g.intro x
          let (varsOut, g) ← g.introNP vars.size
          let fs' := (vars.zip varsOut).foldl (init := fs) fun fs (v, w) => fs.insert v (mkFVar w)
          pure ([(n, ps)], #[⟨⟨g, #[mkFVar v], fs'⟩, n⟩])
      | ConstantInfo.inductInfo info, _ => do
        let (altVarNames, r) ← processConstructors pat.ref info.numParams #[] info.ctors pat.asAlts
        (r, ·) <$> cases g e.fvarId! altVarNames
      | _, _ => failK ()
    (·.2) <$> subgoals.foldlM (init := (r, a)) fun (r, a) ⟨goal, ctorName⟩ => do
      let rec align
      | [] => pure ([], a)
      | (tgt, ps) :: as => do
        if tgt == ctorName then
          let fs := fs.append goal.subst
          (as, ·) <$> rcasesContinue goal.mvarId fs clears a (ps.zip goal.fields.toList) cont
        else
          align as
      align r

/-- This will match a list of patterns against a list of hypotheses `e`. The arguments are similar
to `rcasesCore`, but the patterns and local variables are in `pats`. Because the calls are all
nested in continuations, later arguments can be matched many times, once per goal produced by
earlier arguments. For example `⟨a | b, ⟨c, d⟩⟩` performs the `⟨c, d⟩` match twice, once on the
`a` branch and once on `b`. -/
partial def rcasesContinue (g : MVarId) (fs : FVarSubst) (clears : Array FVarId) (a : α)
  (pats : ListΠ (RCasesPatt × Expr)) (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) :
  TermElabM α :=
  match pats with
  | []  => cont g fs clears a
  | ((pat, e) :: ps) => do
    unless e.isFVar do
      throwError "rcases tactic failed: {e} is not a fvar"
    rcasesCore g fs clears e.fvarId! a pat fun g fs clears a =>
      rcasesContinue g fs clears a ps cont

end

/-- Like `tryClearMany`, but also clears dependent hypotheses if possible -/
def tryClearMany' (mvarId : MVarId) (fvarIds : Array FVarId) : MetaM MVarId := do
  let mut toErase := fvarIds
  for localDecl in (← mvarId.getDecl).lctx do
    if ← findLocalDeclDependsOn localDecl toErase.contains then
      toErase := toErase.push localDecl.fvarId
  mvarId.tryClearMany toErase

/-- The terminating continuation used in `rcasesCore` and `rcasesContinue`. We specialize the type
`α` to `Array MVarId` to collect the list of goals, and given the list of `clears`, it attempts to
clear them from the goal and adds the goal to the list. -/
def finish (g : MVarId) (fs : FVarSubst) (clears : Array FVarId)
  (gs : Array MVarId) : TermElabM (Array MVarId) := do
  let cs : Array Expr := (clears.map fs.get).filter Expr.isFVar
  gs.push <$> tryClearMany' g (cs.map Expr.fvarId!)

open Elab

/-- Parses a `Syntax` into the `RCasesPatt` type used by the `RCases` tactic. -/
partial def RCasesPatt.parse (stx : Syntax) : MetaM RCasesPatt :=
  match stx with
  | `(Lean.Parser.Tactic.rcasesPatMed| $ps:rcasesPat|*) => do
    pure $ RCasesPatt.alts' stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(Lean.Parser.Tactic.rcasesPatLo| $pat:rcasesPatMed : $t:term) => do
    pure $ RCasesPatt.typed stx (← parse pat) t
  | `(Lean.Parser.Tactic.rcasesPatLo| $pat:rcasesPatMed) => parse pat
  | `(rcasesPat| _) => pure $ RCasesPatt.one stx `_
  | `(rcasesPat| $h:ident) => pure $ RCasesPatt.one stx h.getId
  | `(rcasesPat| -) => pure $ RCasesPatt.clear stx
  | `(rcasesPat| ⟨$ps,*⟩) => do
    pure $ RCasesPatt.tuple stx (← ps.getElems.toList.mapM (parse ·.raw))
  | `(rcasesPat| ($pat)) => parse pat
  | _ => throwUnsupportedSyntax

-- extracted from elabCasesTargets
def generalizeExceptFVar (mvarId : MVarId) (args : Array GeneralizeArg) : MetaM (Array Expr × MVarId) := do
  let argsToGeneralize := args.filter fun arg => !(arg.expr.isFVar && arg.hName?.isNone)
  let (fvarIdsNew, mvarId) ← generalize mvarId argsToGeneralize
  let mut result := #[]
  let mut j := 0
  for arg in args do
    if arg.expr.isFVar && arg.hName?.isNone then
      result := result.push arg.expr
    else
      result := result.push (mkFVar fvarIdsNew[j]!)
      j := j+1
  pure (result, mvarId)

/-- Given a list of targets of the form `e` or `h : e`, and a pattern, match all the targets
against the pattern. Returns the list of produced subgoals. -/
def rcases (tgts : Array (Option Name × Syntax))
  (pat : RCasesPatt) (g : MVarId) : TermElabM (List MVarId) := do
  let pats ← match tgts.size with
  | 0 => return [g]
  | 1 => pure [pat]
  | _ => pure (processConstructor pat.ref tgts.size pat.asTuple).2
  let (pats, args) := Array.unzip <|← (tgts.zip pats.toArray).mapM fun ((hName?, tgt), pat) => do
    let (pat, ty) ← match pat with
    | RCasesPatt.typed ref pat ty => pure (pat, some (← withRef ref <| Term.elabType ty))
    | _ => pure (pat, none)
    let expr ← Term.ensureHasType ty (← Term.elabTerm tgt ty)
    pure (pat, { expr, xName? := pat.name?, hName? : GeneralizeArg })
  let (vs, g) ← generalizeExceptFVar g args
  let gs ← rcasesContinue g {} #[] #[] (pats.zip vs).toList finish
  pure gs.toList

/-- The `obtain` tactic in the no-target case. Given a type `T`, create a goal `|- T` and
and pattern match `T` against the given pattern. Returns the list of goals, with the assumed goal
first followed by the goals produced by the pattern match. -/
def obtainNone (pat : RCasesPatt) (ty : Syntax) (g : MVarId) : TermElabM (List MVarId) := do
  let ty ← Term.elabType ty
  let g₁ ← mkFreshExprMVar (some ty)
  let (v, g₂) ← (← g.assert (pat.name?.getD default) ty g₁).intro1
  let gs ← rcasesCore g₂ {} #[] v #[] pat finish
  pure (g₁.mvarId! :: gs.toList)

mutual

partial def rintroCore (g : MVarId) (fs : FVarSubst) (clears : Array FVarId) (a : α)
  (ref pat : Syntax) (ty? : Option Syntax)
  (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) : TermElabM α := do
  match pat with
  | `(rintroPat| $pat:rcasesPat) =>
    let pat := (← RCasesPatt.parse pat).typed? ref ty?
    let (v, g) ← g.intro (pat.name?.getD `_)
    rcasesCore g fs clears v a pat cont
  | `(rintroPat| ($(pats)* $[: $ty?]?)) =>
    rintroContinue g fs clears pat pats ty? a cont
  | _ => throwUnsupportedSyntax

partial def rintroContinue (g : MVarId) (fs : FVarSubst) (clears : Array FVarId)
  (ref : Syntax) (pats : Array Syntax) (ty? : Option Syntax) (a : α)
  (cont : MVarId → FVarSubst → Array FVarId → α → TermElabM α) : TermElabM α := do
  g.withContext do
    let rec loop i g fs clears a := do
      if h : i < pats.size then
        rintroCore g fs clears a ref (pats.get ⟨i, h⟩) ty? (loop (i+1))
      else cont g fs clears a
    loop 0 g fs clears a

end

def rintro (ref : Syntax) (pats : Array Syntax) (ty? : Option Syntax)
  (g : MVarId) : TermElabM (List MVarId) :=
  (·.toList) <$> rintroContinue g {} #[] ref pats ty? #[] finish

end Lean.Meta.RCases

namespace Mathlib.Tactic
open Lean Elab Elab.Tactic Meta RCases Parser.Tactic

/--
`rcases? e` will perform case splits on `e` in the same way as `rcases e`,
but rather than accepting a pattern, it does a maximal cases and prints the
pattern that would produce this case splitting. The default maximum depth is 5,
but this can be modified with `rcases? e : n`.
-/
elab (name := rcases?) "rcases?" _tgts:casesTarget,* _num:(" : " num)? : tactic =>
  throwError "unimplemented"

/--
`rcases` is a tactic that will perform `cases` recursively, according to a pattern. It is used to
destructure hypotheses or expressions composed of inductive types like `h1 : a ∧ b ∧ c ∨ d` or
`h2 : ∃ x y, trans_rel R x y`. Usual usage might be `rcases h1 with ⟨ha, hb, hc⟩ | hd` or
`rcases h2 with ⟨x, y, _ | ⟨z, hxz, hzy⟩⟩` for these examples.

Each element of an `rcases` pattern is matched against a particular local hypothesis (most of which
are generated during the execution of `rcases` and represent individual elements destructured from
the input expression). An `rcases` pattern has the following grammar:

* A name like `x`, which names the active hypothesis as `x`.
* A blank `_`, which does nothing (letting the automatic naming system used by `cases` name the
  hypothesis).
* A hyphen `-`, which clears the active hypothesis and any dependents.
* The keyword `rfl`, which expects the hypothesis to be `h : a = b`, and calls `subst` on the
  hypothesis (which has the effect of replacing `b` with `a` everywhere or vice versa).
* A type ascription `p : ty`, which sets the type of the hypothesis to `ty` and then matches it
  against `p`. (Of course, `ty` must unify with the actual type of `h` for this to work.)
* A tuple pattern `⟨p1, p2, p3⟩`, which matches a constructor with many arguments, or a series
  of nested conjunctions or existentials. For example if the active hypothesis is `a ∧ b ∧ c`,
  then the conjunction will be destructured, and `p1` will be matched against `a`, `p2` against `b`
  and so on.
* An alteration pattern `p1 | p2 | p3`, which matches an inductive type with multiple constructors,
  or a nested disjunction like `a ∨ b ∨ c`.

A pattern like `⟨a, b, c⟩ | ⟨d, e⟩` will do a split over the inductive datatype,
naming the first three parameters of the first constructor as `a,b,c` and the
first two of the second constructor `d,e`. If the list is not as long as the
number of arguments to the constructor or the number of constructors, the
remaining variables will be automatically named. If there are nested brackets
such as `⟨⟨a⟩, b | c⟩ | d` then these will cause more case splits as necessary.
If there are too many arguments, such as `⟨a, b, c⟩` for splitting on
`∃ x, ∃ y, p x`, then it will be treated as `⟨a, ⟨b, c⟩⟩`, splitting the last
parameter as necessary.

`rcases` also has special support for quotient types: quotient induction into Prop works like
matching on the constructor `quot.mk`.

`rcases h : e with PAT` will do the same as `rcases e with PAT` with the exception that an
assumption `h : e = PAT` will be added to the context.
-/
elab (name := rcases) tk:"rcases" tgts:casesTarget,* pat:((" with " rcasesPatLo)?) : tactic => do
  let pat ← match pat.raw.getArgs with
  | #[_, pat] => RCasesPatt.parse pat
  | #[] => pure $ RCasesPatt.tuple tk []
  | _ => throwUnsupportedSyntax
  let tgts := tgts.getElems.map fun tgt =>
    (if tgt.raw[0].isNone then none else some tgt.raw[0][0].getId, tgt.raw[1])
  withMainContext do
    replaceMainGoal (← RCases.rcases tgts pat (← getMainGoal))

/--
The `obtain` tactic is a combination of `have` and `rcases`. See `rcases` for
a description of supported patterns.

```lean
obtain ⟨patt⟩ : type := proof
```
is equivalent to
```lean
have h : type := proof
rcases h with ⟨patt⟩
```

If `⟨patt⟩` is omitted, `rcases` will try to infer the pattern.

If `type` is omitted, `:= proof` is required.
-/
elab (name := obtain) tk:"obtain"
    pat:(ppSpace rcasesPatMed)? ty:((" : " term)?) val:((" := " term,+)?) : tactic => do
  let pat ← liftM $ pat.mapM RCasesPatt.parse
  if val.raw.isNone then
    if ty.raw.isNone then throwError
        ("`obtain` requires either an expected type or a value.\n" ++
        "usage: `obtain ⟨patt⟩? : type (:= val)?` or `obtain ⟨patt⟩? (: type)? := val`")
    let pat := pat.getD (RCasesPatt.one tk `this)
    withMainContext do
      replaceMainGoal (← RCases.obtainNone pat ty.raw[1] (← getMainGoal))
  else
    let pat := pat.getD (RCasesPatt.one tk `_)
    let pat := pat.typed? tk $ if ty.raw.isNone then none else some ty.raw[1]
    let tgts := val.raw[1].getSepArgs.map fun val => (none, val)
    withMainContext do
      replaceMainGoal (← RCases.rcases tgts pat (← getMainGoal))

/--
`rintro?` will introduce and case split on variables in the same way as
`rintro`, but will also print the `rintro` invocation that would have the same
result. Like `rcases?`, `rintro? : n` allows for modifying the
depth of splitting; the default is 5.
-/
elab (name := rintro?) "rintro?" (" : " num)? : tactic =>
  throwError "unimplemented"

/--
The `rintro` tactic is a combination of the `intros` tactic with `rcases` to
allow for destructuring patterns while introducing variables. See `rcases` for
a description of supported patterns. For example, `rintro (a | ⟨b, c⟩) ⟨d, e⟩`
will introduce two variables, and then do case splits on both of them producing
two subgoals, one with variables `a d e` and the other with `b c d e`.

`rintro`, unlike `rcases`, also supports the form `(x y : ty)` for introducing
and type-ascripting multiple variables at once, similar to binders.
-/
elab (name := rintro) "rintro" pats:(ppSpace colGt rintroPat)+ ty:((" : " term)?) : tactic => do
  let ty? := if ty.raw.isNone then none else some ty.raw[1]
  withMainContext do
    replaceMainGoal (← RCases.rintro ty pats ty? (← getMainGoal))
