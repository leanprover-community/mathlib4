/-
Copyright (c) 2024 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import Std.Data.String.Basic
import Std.Lean.Expr
import Std.Lean.PersistentHashMap
import Std.Lean.Syntax
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Set

/-!
#  A testing linter

In a file with `import Mathlib.Tactic.MPTests`, you can run the tests in a single command
writing `#test cmd`.

If you want to run the tests on all the files, you write `set_option linter.linterTest true`.

By default, `set_option linter.linterTest true` skips any declaration that contains
`SyntaxNodeKind`s in `nonTesters` (typically, something involved in flow-control, such as
`guard_hyp` or `guard_target`), since the tests may not be too reliable on them.

If you want to skip a declaration, there is a convenience `untest` macro:
`untext cmd` expands to `set_option linter.linterTest false in cmd`.

TODO:
* Automatically ignore `#guard_cmd`s?
* Pretty printing of types in `have`s, `let`s, `set`s?
* Deal with `let`s already present in the signature: `unfold_let` will destructure them.
-/

open Lean Parser Elab Command Meta Tactic

section low_level_syntax

namespace Lean

namespace Syntax

/-- assumes that `t1` is a tactic sequence and that `t2` is a single tactic.
Inserts `t2` as the `n`-th tactic of the sequence, defaulting to the last position
if `n` is larger than the number of tactics in the sequence `t1`. -/
def insertAt (t1 : Syntax) (n : Nat) (t2 : Syntax) : Syntax :=
  -- we check if `t1` is a `tacticSeq` and further split on whether it ends in `;` or not
  match t1 with
    | .node n1 ``tacticSeq #[.node n2 ``tacticSeq1Indented #[.node n3 `null args]] =>
      let (noOfTacs, trail?) := ((args.size + 1) / 2, args.size % 2 == 0)
      let nargs := match compare n noOfTacs, trail? with
        | .lt, _     => (args.insertAt! (2 * n - 1) mkNullNode).insertAt! (2 * n) t2
        | _,   true  => args.push t2
        | _,   false => (args.push mkNullNode).push t2
      .node n1 ``tacticSeq #[.node n2 ``tacticSeq1Indented #[.node n3 `null nargs]]
    | _ => t1

/-- assumes that `t1` is a tactic sequence and that `t2` is a single tactic.
Inserts `t2` as the `n`-th tactic of the sequence from the bottom, defaulting to the first position
if `n` is larger than the number of tactics in the sequence `t1`. -/
def insertRight (t1 : Syntax) (n : Nat) (t2 : Syntax) : Syntax :=
  match t1 with
    | .node _ ``tacticSeq #[.node _ ``tacticSeq1Indented #[.node _ `null args]] =>
      t1.insertAt (((args.size + 1)/ 2) - n) t2
    | _ => t1

/-- inserts all the tactics in the array `ts` at the beginning of the tactic sequence `tac`. -/
def insertMany (tac : Syntax) (ts : Array Syntax) : Syntax :=
  (Array.range ts.size).foldl (fun l r => l.insertAt r ts[r]!) tac

end Syntax

/-- inserts all the tactics in the array `ts` at the beginning of the tactic sequence `tac`. -/
def TSyntax.insertMany (tac : TSyntax ``tacticSeq) (ts : Array (TSyntax `tactic)) :
    TSyntax ``tacticSeq :=
  ⟨tac.raw.insertMany ts⟩

/-- inserts the tactic `ts` at the end of the tactic sequence `tac`. -/
def TSyntax.insertBack (tac : TSyntax ``tacticSeq) (ts : TSyntax `tactic) :
    TSyntax ``tacticSeq :=
  ⟨tac.raw.insertRight 0 ts⟩

end Lean

end low_level_syntax

section tactic_modifications
variable {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m]

/-- adds `done` at the end of the given tactic sequence. -/
def addDone (tac : TSyntax ``tacticSeq) : m (TSyntax ``tacticSeq) :=
  return tac.insertBack (← `(tactic| done))
  --return ⟨tac.raw.insertRight 0 (← `(tactic| done))⟩

/-- adds `have := 0` at the beginning and `done` at the end of the input tactic sequence.
When evaluating the resulting tactic, the goal acquires `mdata`
as a consequence of the `have := 0`. -/
def addHaveDone (tac : TSyntax ``tacticSeq) : m (TSyntax ``tacticSeq) := do
  addDone (tac.insertMany #[(← `(tactic| have := 0))])

/-- adds `show id _` at the beginning and `done` at the end of the input tactic sequence.
When evaluating the resulting tactic, the goal has the same `whnf` as the original one, but is
not the same. -/
def addShowIdDone (tac : TSyntax ``tacticSeq) : m (TSyntax ``tacticSeq) := do
  addDone (tac.insertMany #[(← `(tactic| show id _))])

/-- adds at the beginning of the tactic sequence `tac` lines like `set x := x`,
where `x` is the username of each local declaration in `toSet`.
These `set`s introduce a layer of separation between the original names of the declarations
and the current ones.  This may help detect missing `withContext`s. -/
def addLetsOrSets (lets? unLet? : Bool) (tac : TSyntax ``tacticSeq) (toSet : Array LocalDecl) :
    TermElabM (TSyntax ``tacticSeq × Array (TSyntax `tactic)) := do
  let mut repls := #[]
  for d in toSet do
    let nid := mkIdent d.userName
    let dtyp := ⟨← d.type.toSyntax⟩
    let next ← if lets?
               then `(tactic| let $nid : $dtyp := $nid)
               else `(tactic| set $nid : $dtyp := $nid)
    repls := repls.push next
  if unLet? then
    let unf ← `(tactic| unfold_let at *)
    -- we use `unfold_let` twice, since each time it "reverses" the variables
    -- revert this, once #12077 gets merged: thanks Kyle!
    repls := (repls.push unf).push unf
  return (← addDone (tac.insertMany repls), repls)

/-- adds at the beginning of the tactic sequence `tac` lines like `have new := old`,
where `old` is the username of each local declaration in `toHave`.
It also replaces all `old` names with the `new` ones in `tac`.
These `have`s introduce the "same" local declarations, but inside a metavariable,
creating a layer of separation between the original names of the declarations
and the current ones.  This may help detect missing `instantiateMVars`. -/
def addPropHaves (tac : TSyntax ``tacticSeq) (toHave : Array LocalDecl) :
    TermElabM (TSyntax ``tacticSeq × Array (TSyntax `tactic)) := do
  let mut (t1, repls) := (tac, #[])
  for i in [:toHave.size] do
    let decl := toHave[i]!
    let oldId := mkIdent decl.userName
    let str := decl.userName.toString ++ "__"++ decl.userName.toString ++ "__" ++ (toString i)
    -- prefer to `let newId := mkIdent (← mkFreshId)` that also requires `[MonadNameGenerator m]`
    -- just for easier copy/pasting
    let newId : Ident := ⟨.ident .none str str []⟩
--    let dtyp := ⟨← decl.type.toSyntax⟩
    t1 ← t1.replaceM fun s => return if s == oldId then some newId else none
    repls := repls.push (← `(tactic| have $newId := $oldId ))
  t1 ← addDone (t1.insertMany repls)
  return (t1, repls)

end tactic_modifications

section tactic_tests

/-- A generic testing of a tactic sequence.
It returns a message informing about errors and successes. -/
def testTactic (tac : TSyntax ``tacticSeq) (test : MessageData)
    (fail success : Option MessageData := none) :
    TacticM (Option MessageData) := withoutModifyingState do
  let str ← (do evalTactic tac
                trace[Tactic.tests] (checkEmoji ++ m!" {test}")
                return success) <|>
            (do trace[Tactic.tests] (crossEmoji ++ m!" {test}")
                return fail)
  return str

/-- The standard test for not handling `mdata`: adds `have := 0`, which introduces
some metadata in the goal.  This may produce an error. -/
def testMData (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) := do
  let fin ← addHaveDone tac
  testTactic fin "'have := 0'" m!"is mdata correctly handled? {fin}"

/-- The standard test for not handling `whnf`: adds `show id _`, which changes the goal
to a `whnf` equivalent one.  This may produce an error. -/
def testWhnf (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) := do
  let fin ← addShowIdDone tac
  testTactic fin "'show id _'" m!"is `whnf` correctly handled? {fin}"

/-- The standard test for missing `withContext`: adds `let x := x`, for every variable
`x` in context.  Since the new `x` was not present in the original metavariable context,
if `x` is used by the tactic, it might produce an error. -/
def testFVs (lets? unLet? : Bool) (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) :=
withoutModifyingState do withMainContext do
  let ctx ← getLCtx
  let carr := ctx.fvarIdToDecl.toArray.qsort (·.1.name.toString < ·.1.name.toString)
  let Typ ← inferType (.const ``Nat [])
  let mut typs : HashSet Expr := HashSet.empty.insert Typ
  for (_, d) in carr do
    typs := typs.insert (d.type)
  let nonSort ← carr.filterM fun (_, d) => do
    let d' := (ctx.findFromUserName? d.userName).get!
    -- we only duplicate variables that are not shadowed to begin with
    return d.binderInfo != .instImplicit && (← isDefEq d'.type d.type) &&
      d.kind == .default && d.type.ctorName != "sort" && !(← inferType d.type).isProp
  let toSet := nonSort.map Prod.snd
  let (ntac, repls) ← addLetsOrSets lets? unLet? tac toSet
  testTactic ntac m!"{if lets? then "'let's" else "'set's"} {repls}" m!"missing withContext? {ntac}"

/-- The standard test for `instantiateMVars`: adds `have h' := h`, for every `Prop`-valued
`h` in context.  Since the new `h'` does not have an explicit Type annotation, it is introduced
as a metavariable and if it is used by the tactic with un-instantiated mvars, it might
produce an error. -/
def testInstMVs (tac : TSyntax ``tacticSeq) : TacticM (Option MessageData) :=
withoutModifyingState do withMainContext do
  let ctx ← getLCtx
  let carr := ctx.fvarIdToDecl.toArray.qsort (·.1.name.toString < ·.1.name.toString)
  let props ← carr.filterM fun d => return d.2.kind == .default && ((← inferType d.2.type).isProp)
  let (t1, _repls) ← addPropHaves tac (props.map Prod.snd)
  testTactic ⟨t1⟩ m!"'have's{indentD t1}" m!"missing instantiateMVars? {t1}"

/-- `test tacSeq` runs the standard meta-programming tests on the tactic sequence `tacSeq`.
If the `!`-flag is not present, then it reverts the state, otherwise it leaves the state as
it is after the tactic sequence.
 -/
elab (name := testTac) "test " tk:"!"? tac:tacticSeq : tactic => do
  let _ ← for test in [testMData, testFVs false false, testFVs true false, testInstMVs,
                                  testFVs false true,  testFVs true true
                                  ] do
    if let some str := ← test tac then
      logWarningAt (← getRef) str
  match tk with
    | none => evalTactic tac
    | some _ => return

@[inherit_doc testTac]
macro "test! " tac:tacticSeq : tactic => `(tactic| test ! $tac)

end tactic_tests

/-- if a declaration contains one of these `SyntaxNodeKind`s, then likely the automated testing
will fail, but would not be an indication of a bug. -/
abbrev nonTesters : HashSet SyntaxNodeKind := HashSet.empty
--  |>.insert ``Lean.guardMsgsCmd  -- <--- does not actually work
--  |>.insert ``Lean.Parser.Tactic.guardTarget
--  |>.insert ``Lean.Parser.Tactic.guardHyp

/-- checks whether the input `Syntax` contains a `SyntaxNodeKind` in `nonTesters` and, if so,
returns its `atomVal`. -/
partial
def test? : Syntax → (c : HashSet SyntaxNodeKind := nonTesters) → Option String
  | stx@(.node _ k args), c =>
    if c.contains k then some stx[0].getAtomVal else
      (args.map (test? · c)).findSome? id
  | _, _ => none

/-- converts
* `theorem x ...` to  `some (example ... , x)`,
* `lemma x ...`   to  `some (example ... , x)`,
* `example ...`   to ``some (example ... , `example)``,
*  everything else goes to `none`.
-/
def toExample {m : Type → Type} [Monad m] [MonadRef m] [MonadQuotation m] :
    Syntax → m (Option (Syntax × Syntax))
  | `($dm:declModifiers theorem $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers lemma $did:declId $ds* : $t $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds* : $t $dv:declVal), did.raw[0])
  | `($dm:declModifiers example $ds:optDeclSig $dv:declVal) => do
    return some (← `($dm:declModifiers example $ds $dv:declVal), mkIdent `example)
  | _ => return none

/-- `#test cmd` runs the standard meta-programming tests on the declaration `cmd`. -/
elab "#test " cmd:command : command => do
  if let some (_, id) ← toExample cmd then
    trace[Tactic.tests] m!"testing '{id}'"
  let ncmd ← cmd.replaceM fun x => do
    if x.getKind == ``tacticSeq then
      let xs := ⟨x⟩
      return some (x.insertAt 0 (← `(tactic| test! $xs))) else return none
  elabCommand ncmd

/-- The meta-programming test linter modifies tests for tactics, trying to highlight common
pitfalls: missing `instantiateMVars`, `withContext` or `consumeMData` could be isolated. -/
register_option linter.linterTest : Bool := {
  defValue := false
  descr := "enable the meta-programming test linter"
}

/-- Gets the value of the `linter.linterTest` option. -/
def getLinterTest (o : Options) : Bool := Linter.getLinterValue linter.linterTest o

@[inherit_doc linter.linterTest]
def linterTest : Linter where run := withSetOptionIn fun cmd => do
  if getLinterTest (← getOptions) && ! cmd.getKind == ``«command#test_» then
    match test? cmd with
      | none => if let some (cmd, _) ← toExample cmd then
                  let cmd := ⟨cmd⟩
                  elabCommand (← `(command| #test $cmd))
      | some gd => logInfo m!"Skipped since it contains '{gd}'\n\n\
                              Use '#test cmd' if you really want to run the test on 'cmd'"

initialize addLinter linterTest

/-- a convenience macro expanding to `set_option linter.linterTest false in`. -/
macro "untest " cmd:command : command => `(command| set_option linter.linterTest false in $cmd)

initialize registerTraceClass `Tactic.tests
