/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Joachim Breitner
-/
import Lean
import Std.Lean.Delaborator
import Mathlib.Tactic.Cache
import Mathlib.Lean.Data.NameRel
import Mathlib.Lean.Data.RBTree

/-!
# The `#find` command and tactic.
-/

open Lean Meta Elab

/-- Returns `true` if `needle` is a substring of `hey` -/
def String.isInfixOf (needle : String) (hey : String) := Id.run do
  -- until https://github.com/leanprover/std4/pull/178 lands
  let mut i := hey.mkIterator
  while not i.atEnd do
    if needle.isPrefixOf i.remainingToString
    then return true
    else i := i.next
  return false


/-!
## Formattnig utilities
-/

/-- Puts `MessageData` into a bulleted list -/
def MessageData.bulletList (xs : List MessageData) : MessageData :=
  MessageData.joinSep (xs.map (m!"• " ++ ·)) Format.line

/-- Puts `MessageData` into a comma-separated list with `"and"` at the back (no Oxford comma).
Best used on non-empty arrays; returns `"– none –"` for an empty array.  -/
def MessageData.andList (xs : Array MessageData) : MessageData :=
  match xs with
  | #[] => m!"– none –"
  | #[x] => x
  | _ => MessageData.joinSep xs.pop.toList m!", " ++ m!" and " ++ xs.back

/-- Formats a list of names, as you would expect from a lemma-searching command.  -/
def MessageData.bulletListOfConsts {m} [Monad m] [MonadEnv m] [MonadError m]
  (names : List Name) : m MessageData := do
    let es ← names.mapM mkConstWithLevelParams
    pure (MessageData.bulletList (es.map ppConst))


/-!
## Matching term patterns against conclusions or any subexpression
-/

namespace Mathlib.Tactic.Find

/-- A predicate on `ConstantInfo` -/
def ConstMatcher := ConstantInfo → MetaM Bool

/-- A quick comparison of expressions, to avoid setting up the machinery for isDefEq
when it will surely fail -/
def _root_.Lean.Expr.headIndexWithArgs (e : Expr) := (e.toHeadIndex, e.headNumArgs)

/-- Takes a pattern (of type `Expr`), and returns a matcher that succeeds if _any_ subexpression
matches that patttern.  -/
def matchAnywhere (t : Expr) : MetaM ConstMatcher := withReducible do
  let head := t.headIndexWithArgs
  let pat ← abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let found  ← IO.mkRef false
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    Lean.Meta.forEachExpr' cTy fun sub_e => do
      if head == sub_e.headIndexWithArgs then do
        withNewMCtxDepth $ do
          let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
            (← mkFreshLevelMVars pat.numMVars).toArray
          let (_, _, pat) ← lambdaMetaTelescope pat
          -- dbg_trace (pat, sub_e)
          if ← isDefEq pat sub_e
          then found.set true
      -- keep searching if we haven't found it yet
      not <$> found.get
    found.get


private partial def matchHyps : List Expr → List Expr → List Expr → MetaM Bool
  | p::ps, oldHyps, h::newHyps => do
    let pt ← inferType p
    let t ← inferType h
    if (← isDefEq pt t) then
      matchHyps ps [] (oldHyps ++ newHyps)
    else
      matchHyps (p::ps) (h::oldHyps) newHyps
  | [], _, _    => pure true
  | _::_, _, [] => pure false

/-- Takes a pattern (of type `Expr`), and returns a matcher that succeeds if the conclusion of the
lemma matches the conclusion of the pattern, and all hypotheses of the pattern are found among the
hypotheses of the lemma.  -/
def matchConclusion (t : Expr) : MetaM ConstMatcher := withReducible do
  let head := (← forallMetaTelescopeReducing t).2.2.headIndexWithArgs
  let pat ← abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    forallTelescopeReducing cTy fun cParams cTy' ↦ do
      if head == cTy'.headIndexWithArgs then
        let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
          (← mkFreshLevelMVars pat.numMVars).toArray
        let (_, _, pat) ← lambdaMetaTelescope pat
        let (patParams, _, pat) ← forallMetaTelescopeReducing pat
        isDefEq cTy' pat <&&> matchHyps patParams.toList [] cParams.toList
      else
        pure false


/-!
## The find tactic engine: Cache and matching
-/

/-- The declaration cache used by `#find`, stores `NameRel` mapping names to the name
of constants they are mentinend in.

The first `NameRel` is for library declaration (and doesn't change once populated),
the second is for local declarations and is rebuilt upon every invocation of `#find`.  -/
initialize findDeclsByConsts : DeclCache (NameRel × NameRel) ←
  DeclCache.mk
    (profilingName := "#find: init cache")
    (empty := ({}, {}))
    (addLibraryDecl := fun _ c (m₁, m₂) ↦ return (← NameRel.addDecl c m₁, m₂))
    (addDecl := fun _ c (m₁, m₂) ↦ return (m₁, ← NameRel.addDecl c m₂))

-- NB: In large files it may be slightly wasteful to calculate a full NameSet for the local
-- definition upon every invocation of `#find`, and a linear scan might work better. For now,
-- this keeps the code below more uniform.

/-- The parsed and elaborated arguments to `#find`  -/
structure Arguments where
  /-- Identifiers to search for -/
  idents : Array Name
  /-- Lemma name substrings to search for -/
  namePats : Array String
  /-- Term patterns to search for. The boolean indicates conclusion patterns. -/
  terms : Array (Bool × Expr)

/-- The core of the `#find` tactic with all parsing/printing factored out, for
programmatic use.  -/
def find (args : Arguments) (maxShown := 200) :
  MetaM (Except MessageData (MessageData × List Name)) := do
  profileitM Exception "#find" (← getOptions) do
    -- Collect set of names to query the index by
    let needles : NameSet :=
          {} |> args.idents.foldl NameSet.insert
             |> args.terms.foldl (fun s (_,t) => t.foldConsts s (flip NameSet.insert))
    if needles.isEmpty then do
      return .error m!"Cannot search: No constants in search pattern."

    -- Prepare term patterns
    let pats ← liftM <| args.terms.mapM fun (isConclusionPattern, t) =>
      if isConclusionPattern
      then matchConclusion t
      else matchAnywhere t

    -- Query the declaration cache
    let (m₁, m₂) ← findDeclsByConsts.get
    let hits := RBTree.intersects <| needles.toArray.map <| fun needle =>
      (m₁.find needle).union (m₂.find needle)

    -- Filter by name patterns
    let hits2 := hits.toArray.filter fun n => args.namePats.all fun p =>
      p.isInfixOf n.toString

    -- Filter by term patterns
    let hits3 ← hits2.filterM fun n => do
      let env ← getEnv
      if let some ci := env.find? n then do pats.allM (· ci)
      else return false

    -- Sort to bring lemmas with small names to the top, and keep related lemmas together
    let hits4 := hits3.qsort Name.lt

    let summary ← IO.mkRef MessageData.nil
    let addLine line := do summary.set <| (← summary.get) ++ line ++ Format.line

    let needlesList := MessageData.andList (needles.toArray.map .ofName)
    addLine m!"Found {hits.size} definitions mentioning {needlesList}."
    unless (args.namePats.isEmpty) do
      let nameList := MessageData.andList <| args.namePats.map fun s => m!"\"{s}\""
      addLine $ m!"Of these, {hits2.size} have a name containing {nameList}."
    unless (pats.isEmpty) do
      addLine $ m!"Of these, {hits3.size} match your patterns."
    unless (hits4.size ≤ maxShown) do
      addLine $ m!"Of these, only the first {maxShown} are shown."
    return .ok (← summary.get, hits4.toList.take maxShown)

/-!
## The #find command, syntax and parsing
-/

open Parser

/-- `#find` name pattern: `"substring"` -/
syntax name_pattern := strLit
/-- `#find` identifier pattern: `Real.sqrt`, `sqrt` -/
syntax ident_pattern := ident
/-- The turnstyle for `conclusion_pattern` -/
syntax turnstyle := "⊢ " <|> "|- "
/-- `#find` conclusion pattern: `⊢ (tsum _ = _)` -/
syntax conclusion_pattern := turnstyle term:max
/-- `#find` subexpression pattern: `(_ * (_ + _))` -/
syntax term_pattern := term:max
/-- a single `#find` pattern -/
syntax find_pattern := name_pattern <|> ident_pattern <|> conclusion_pattern <|> term_pattern

/-- A syntax category for the argument to `#find`, so that it can be used by external tools. -/
declare_syntax_cat find_patterns
/-- `#find` patterns -/
syntax find_pattern* : find_patterns

/-- Parses a list of `find_pattern` syntax into `Arguments` -/
def parseFindPatterns (args : TSyntax `find_patterns) : TermElabM Arguments :=
  withReader (fun ctx => { ctx with errToSorry := false }) do
    let mut idents := #[]
    let mut namePats := #[]
    let mut terms := #[]
    match args with
    | `(find_patterns| $args':find_pattern*) =>
      for arg in args' do
        match arg with
        | `(find_pattern| $ss:str) => do
          let str := Lean.TSyntax.getString ss
          namePats := namePats.push str
        | `(find_pattern| $i:ident) => do
          let n := Lean.TSyntax.getId i
          unless (← getEnv).contains n do
            throwErrorAt i "unknown identifier '{n}'"
          idents := idents.push n
        | `(find_pattern| _) => do
            throwErrorAt arg ("Cannot search for _. " ++
              "Did you forget to put a term pattern in parentheses?")
        | `(find_pattern| $_:turnstyle $s:term) => do
          let t ← Lean.Elab.Term.elabTerm s none
          terms := terms.push (true, t)
        | `(find_pattern| $s:term) => do
          let t ← Lean.Elab.Term.elabTerm s none
          terms := terms.push (false, t)
        | _ => throwErrorAt arg "unexpected argument to #find"
    | _ => throwErrorAt args "unexpected argument to #find"
    pure {idents, namePats, terms}


open Command

/--
The `#find` command finds definitions and lemmas in various ways. One can search by: the constants
involved in the type; a substring of the name; a subexpression of the type; or a subexpression
located in the return type or a hypothesis specifically. All of these search methods can be
combined in a single query.

1. By constant:
   ```lean
   #find Real.sin
   ```
   finds all lemmas whose statement somehow mentions the sine function.

2. By lemma name substring:
   ```lean
   #find Real.sin "two"
   ```
   restricts the search above to those lemmas that have `"two"` as part of the lemma _name_.

   (Currently, substring searches _must_ be combined with other kind of queries.)

3. By subexpression:
   ```lean
   #find (_ * (_ ^ _))
   ```
   finds all lemmas whose statements somewhere include a product where the second argument is
   raised to some power. The pattern can also be non-linear, as in
   ```lean
   #find (Real.sqrt ?a * Real.sqrt ?a)
   ```

4. By conclusion and/or hypothesis:
   ```lean
   #find ⊢ (tsum _ = _ * tsum _)
   ```
   finds all lemmas where the conclusion (the subexpression to the right of all `→` and `∀`) has the
   given shape. If the pattern has hypotheses, they are matched against the hypotheses of
   the lemma in any order; for example,
   ```lean
   #find ⊢ (_ < _ → tsum _ < tsum _)
   ```
   will find `tsum_lt_tsum` even though the hypothesis `f i < g i` is not the last.

5. In combination:
   ```lean
   #find Real.sin "two" tsum  (_ * _) (_ ^ _) ⊢ (_ < _ → _)
   ```
   will find all lemmas which mention the constants `Real.sin` and `tsum`, have `"two"` as a
   substring of the lemma name, include a product and a power somewhere in the type, *and* have a
   hypothesis of the form `_ < _`.

If you pass more than one such search filter, `#find` will only return lemmas which match _all_ of
them simultaneously. At least some filter must mention a concrete name, because `#find` maintains
an index of which lemmas mention which other constants. This is also why the _first_ use of `#find`
will be somewhat slow (typically less than half a minute with all of `Mathlib` imported), but
subsequent uses are faster.

It may be useful to open a scratch file, `import Mathlib`, and use `#find` there, this way you will
find lemmas that you have not yet imported, and the cache will stay up-to-date.

Inside tactic proofs, the `#find` tactic can be used instead.
-/
elab s:"#find " args:find_patterns : command => liftTermElabM do
  profileitM Exception "find" (← getOptions) do
    match ← find (← parseFindPatterns args) with
    | .error warn =>
      Lean.logWarningAt s warn
    | .ok (summary, hits) =>
      Lean.logInfo $ summary ++ (← MessageData.bulletListOfConsts hits)

/--
Tactic version of the `#find` command.
See also the `apply?` tactic to search for theorems matching the current goal.
-/
elab s:"#find " args:find_patterns : tactic => do
  profileitM Exception "find" (← getOptions) do
    match ← find (← parseFindPatterns args) with
    | .error warn =>
      Lean.logWarningAt s warn
    | .ok (summary, hits) =>
      Lean.logInfo $ summary ++ (← MessageData.bulletListOfConsts hits)
