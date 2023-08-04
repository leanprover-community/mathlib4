/-
Copyright (c) 2023 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Joachim Breitner
-/
import Lean
import Mathlib.Tactic.Cache

/-!
# The `#find` command and tactic.
-/

set_option autoImplicit false

open Lean
open Lean.Meta
open Lean.Elab

/-!
## Utilities, to be moved somewhere else before merging
-/

/-- The intersection of a (non-empy) array of `NameSet`s -/
def Lean.NameSet.intersects (ss : Array NameSet) : NameSet :=
  -- sort smallest set to the back, and iterate over that one
  -- TODO: Does `RBTree` admit faster intersection algorithms?
  let ss := ss.qsort (·.size > ·.size)
  ss.back.fold (init := {}) fun s m =>
    if ss.pop.all (·.contains m) then s.insert m else s

/-- The union of two `NameSet`s -/
def Lean.NameSet.union (s₁ : NameSet) (s₂ : NameSet) : NameSet :=
  -- TODO: Does `RBTree` admit faster union?
  s₂.fold (init := s₁) .insert

/-- Returns `true` if `needle` is a substring of `hey` -/
def String.isInfixOf (needle : String) (hey : String) := Id.run do
  -- until https://github.com/leanprover/std4/pull/178 lands
  let mut i := hey.mkIterator
  while not i.atEnd do
    if needle.isPrefixOf i.remainingToString
    then return true
    else i := i.next
  return false

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
    let es <- names.mapM mkConstWithLevelParams
    pure (MessageData.bulletList (es.map ppConst))


/-!
## Matching term patterns against conclusions or any subexpression
-/

namespace Mathlib.Tactic.Find

/-- A predicate on `ConstantInfo` -/
def ConstMatcher := ConstantInfo → MetaM Bool

/-- Takes a pattern (of type `Expr`), and returns a matcher that succeeds if _any_ subexpression
matches that patttern.  -/
def matchAnywhere (t : Expr) : MetaM ConstMatcher := withReducible do
  let head := t.toHeadIndex
  let pat <- abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let found  ← IO.mkRef false
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    Lean.Meta.forEachExpr' cTy fun sub_e => do
      if head == sub_e.toHeadIndex then do
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
  let head := (← forallMetaTelescopeReducing t).2.2.toHeadIndex
  let pat <- abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    forallTelescopeReducing cTy fun cParams cTy' ↦ do
      if head == cTy'.toHeadIndex then
        let pat := pat.expr.instantiateLevelParamsArray pat.paramNames
          (← mkFreshLevelMVars pat.numMVars).toArray
        let (_, _, pat) ← lambdaMetaTelescope pat
        let (patParams, _, pat) ← forallMetaTelescopeReducing pat
        isDefEq cTy' pat <&&> matchHyps patParams.toList [] cParams.toList
      else
        pure false

end Mathlib.Tactic.Find


/-!
## A data structure for a relation on names
-/

namespace Lean

/-- A `NameRel` maps names to sets of names -/
def NameRel := NameMap NameSet

instance : EmptyCollection NameRel :=
  inferInstanceAs $ EmptyCollection (NameMap NameSet)

instance : Nonempty NameRel :=
  inferInstanceAs $ Nonempty (NameMap NameSet)

/-- For all names `n` mentioned in the type of the constant `c`, add `c.name` to the set associated
with `n`. -/
def NameRel.addDecl (c : ConstantInfo) (m : NameRel) := do
  if ← c.name.isBlackListed then
    return m
  let consts := c.type.foldConsts {} (flip NameSet.insert)
  return consts.fold (init := m) fun m n =>
    m.insert n (
      m.findD n {} |> flip .insert c.name
    )

end Lean


/-!
## The find tactic engine: Cache and matching
-/

namespace Mathlib.Tactic.Find

/-- The declaration cache used by `#find`, stores  `NameRel` mapping names to the
name of constants they are mentinend in.

The first `NameRel` is for library declaration (and doesn't change once populated),
the second is for local declarations and is rebuilt upon every invocation of `#find`.  -/
initialize findDeclsByConsts : DeclCache (NameRel × NameRel) ←
  DeclCache.mk
    (profilingName := "#find_theorems: init cache")
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
  name_pats : Array String
  /-- Term patterns to search for. The boolean indicates conclusion patterns. -/
  terms : Array (Bool × Expr)

/-- The core of the `#find` tactic with all parsing/printing factored out, for
programmatic use.  -/
def find (args : Arguments) (maxShown := 200) :
  MetaM (MessageData ⊕ (MessageData × List Name)) := do
  profileitM Exception "find_theorems" (← getOptions) do
    -- Collect set of names to query the index by
    let needles : NameSet :=
          {} |> args.idents.foldl NameSet.insert
             |> args.terms.foldl (fun s (_,t) => t.foldConsts s (flip NameSet.insert))
    if needles.isEmpty then do
      return .inl m!"Cannot search: No constants in search pattern."

    -- Prepare term patterns
    let pats <- liftM $ args.terms.mapM fun (is_conclusion_pattern, t) =>
      if is_conclusion_pattern
      then matchConclusion t
      else matchAnywhere t

    -- Query the declaration cache
    let (m₁, m₂) <- findDeclsByConsts.get
    let hits := NameSet.intersects $ needles.toArray.map $ fun needle =>
      NameSet.union (m₁.findD needle {}) (m₂.findD needle {})

    -- Filter by name patterns
    let hits2 := hits.toArray.filter fun n => args.name_pats.all fun p =>
      p.isInfixOf n.toString

    -- Filter by term patterns
    let hits3 <- hits2.filterM fun n => do
      let env <- getEnv
      if let some ci := env.find? n then do pats.allM (· ci)
      else return false

    -- Sort to bring lemmas with small names to the top, and keep related lemmas together
    let hits4 := hits3.qsort Name.lt

    let summary ← IO.mkRef MessageData.nil
    let add_line line := do summary.set $ (← summary.get) ++ line ++ Format.line

    let needles_list := MessageData.andList (needles.toArray.map .ofName)
    add_line $ m!"Found {hits.size} definitions mentioning {needles_list}."
    unless (args.name_pats.isEmpty) do
      let name_list := MessageData.andList <| args.name_pats.map fun s => m!"\"{s}\""
      add_line $ m!"Of these, {hits2.size} have a name containing {name_list}."
    unless (pats.isEmpty) do
      add_line $ m!"Of these, {hits3.size} match your patterns."
    unless (hits4.size ≤ maxShown) do
      add_line $ m!"Of these, the first {maxShown} are shown."
    return .inr (← summary.get, hits4.toList.take maxShown)

/-!
## The #find command, syntax and parsing
-/

open Lean.Parser

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
/-- `#find` patterns -/
syntax find_pattern := name_pattern <|> ident_pattern <|> conclusion_pattern <|> term_pattern


/-- Parses a list of `find_pattern` syntax into `Arguments` -/
def parseFindPatterns (args : TSyntaxArray ``find_pattern) : TermElabM Arguments := do
  let mut idents := #[]
  let mut name_pats := #[]
  let mut terms := #[]
  for arg in args do
    match arg with
    | `(find_pattern| $ss:str) => do
      let str := Lean.TSyntax.getString ss
      name_pats := name_pats.push str
    | `(find_pattern| $i:ident) => do
      let n := Lean.TSyntax.getId i
      unless (← getEnv).contains n do
        throwErrorAt i "unknown identifier '{n}'"
      idents := idents.push n
    | `(find_pattern| $_:turnstyle $s:term) => do
      let t ← Lean.Elab.Term.elabTerm s none
      terms := terms.push (true, t)
    | `(find_pattern| $s:term) => do
      let t ← Lean.Elab.Term.elabTerm s none
      terms := terms.push (false, t)
    | _ => throwErrorAt arg "unexpected argument to #find"
  pure {idents, name_pats, terms}

open Lean.Elab.Command

/--
The `#find` command finds definitions and lemmas by various ways, which can be combined:

1. By constant:
   ```lean
   #find Real.sin tsum
   ```
   finds all lemmas that somehow mention the square root and the infinite series sum.

2. By lemma name substring:
   ```lean
   #find tsum "two"
   ```
   finds all lemmas about `tsum` that have `"two"` as part of the lemma _name_.

3. By subexpression:
   ```lean
   #find tsum (_ * _ ^ _)
   ```
   finds all lemmas that mention `tsum` and where somewhere in the lemma statement there is a
   product with a power as the second argument. The pattern can also be non-linear, as in
   ```lean
   #find (Real.sqrt ?a * Real.sqrt ?a)
   ```

4. By conclusion:
   ```lean
   #find_theorems ⊢ (tsum _ = _ * tsum _)
   ```
   finds all lemmas where the conclusion (the subexpression to the right of all `→` and `∀`) has the
   given shape. If the pattern has hypothesis, then they are matched agains the hypotheses of
   the lemma in any order:
   ```lean
   #find_theorems ⊢ (_ < _ → tsum _ < tsum _)
   ```
   will find `tsum_lt_tsum` even though the hypotheses `f i < g i` is not the last.

The command will show the list of results in the info view, where you can cover to see theirs types
or click to go to their definition.

If you pass more than one such search filter, it will list lemmas matching _all_ of them. At least
some filter must mention a concrete name, because `#find` maintains an index of which lemmas
mention which other constants. This is also why the _first_ use of `#find` will be somewhat slow
(typically less than half a minute with all of `Mathlib` imported), but subsequent uses are faster.

It may be useful to open a scratch file, `import Mathlib`, and use `#find` there, this way you will
find lemmas that you have not yet imported, and the cache will stay up-to-date.

Inside tactic proofs, the `#find` tactic can be used instead.
-/
elab s:"#find_theorems " args:find_pattern* : command => liftTermElabM do
  profileitM Exception "find_theorems" (← getOptions) do
    match ← find (← parseFindPatterns args) with
    | .inl warn =>
      Lean.logWarningAt s warn
    | .inr (summary, hits) =>
      Lean.logInfo $ summary ++ (← MessageData.bulletListOfConsts hits)

/--
Tactic version of the `#find` command.
See also the `apply?` tactic to search for theorems matching the current goal.
-/
elab s:"#find_theorms " args:find_pattern+ : tactic => do
  profileitM Exception "find_theorems" (← getOptions) do
    match ← find (← parseFindPatterns args) with
    | .inl warn =>
      Lean.logWarningAt s warn
    | .inr (summary, hits) =>
      Lean.logInfo $ summary ++ (← MessageData.bulletListOfConsts hits)
