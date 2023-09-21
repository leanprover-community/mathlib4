/-
Copyright (c) 2021 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Joachim Breitner
-/
import Lean
import Std.Lean.Delaborator
import Std.Data.String.Basic
import Std.Util.Pickle
import Mathlib.Tactic.Cache
import Mathlib.Lean.Data.NameRel
import Mathlib.Lean.Data.RBTree

/-!
# The `#find` command and tactic.
-/

open Lean Meta Elab

/-!
## Formatting utilities
-/

/-- Puts `MessageData` into a bulleted list -/
def MessageData.bulletList (xs : Array MessageData) : MessageData :=
  MessageData.joinSep (xs.toList.map (m!"• " ++ ·)) Format.line

/-- Puts `MessageData` into a comma-separated list with `"and"` at the back (no Oxford comma).
Best used on non-empty arrays; returns `"– none –"` for an empty array.  -/
def MessageData.andList (xs : Array MessageData) : MessageData :=
  match xs with
  | #[] => m!"– none –"
  | #[x] => x
  | _ => MessageData.joinSep xs.pop.toList m!", " ++ m!" and " ++ xs.back

/-- Formats a list of names, as you would expect from a lemma-searching command.  -/
def MessageData.bulletListOfConsts {m} [Monad m] [MonadEnv m] [MonadError m]
  (names : Array Name) : m MessageData := do
    let es ← names.mapM mkConstWithLevelParams
    pure (MessageData.bulletList (es.map ppConst))


/-!
## Matching term patterns against conclusions or any subexpression
-/

namespace Mathlib.Tactic.Find

/-- A predicate on `ConstantInfo` -/
def ConstMatcher := ConstantInfo → MetaM Bool

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

/-- Like defEq, but the pattern is a function type, matches parameters up to reordering -/
def matchUpToHyps (pat: AbstractMVarsResult) (head : HeadIndex) (e : Expr) : MetaM Bool := do
  forallTelescopeReducing e fun e_params e_concl ↦ do
    if head == e_concl.toHeadIndex then
      let (_, _, pat_e) ← openAbstractMVarsResult pat
      let (pat_params, _, pat_concl) ← forallMetaTelescopeReducing pat_e
      isDefEq e_concl pat_concl <&&> matchHyps pat_params.toList [] e_params.toList
    else
      pure false

/-- Takes a pattern (of type `Expr`), and returns a matcher that succeeds if the conclusion of the
lemma matches the pattern.  If the pattern is a function type, it matches up to parameter
reordering. -/
def matchConclusion (t : Expr) : MetaM ConstMatcher := withReducible do
  let head := (← forallMetaTelescopeReducing t).2.2.toHeadIndex
  let pat ← abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    matchUpToHyps pat head cTy

/-- A wrapper around `Lean.Meta.forEachExpr'` that checks if any subexpression matches the
predicate.  -/
def Lean.Meta.anyExpr (input : Expr) (pred : Expr → MetaM Bool) : MetaM Bool := do
  let found  ← IO.mkRef false
  Lean.Meta.forEachExpr' input fun sub_e => do
    if ← pred sub_e then found.set true
    -- keep searching if we haven't found it yet
    not <$> found.get
  found.get

/-- Takes a pattern (of type `Expr`), and returns a matcher that succeeds if _any_ subexpression
matches that patttern. If the pattern is a function type, it matches up to parameter reordering. -/
def matchAnywhere (t : Expr) : MetaM ConstMatcher := withReducible do
  let head := (← forallMetaTelescopeReducing t).2.2.toHeadIndex
  let pat ← abstractMVars (← instantiateMVars t)
  pure fun (c : ConstantInfo) => withReducible do
    let cTy := c.instantiateTypeLevelParams (← mkFreshLevelMVars c.numLevelParams)
    -- NB: Lean.Meta.forEachExpr`' handles nested foralls in one go, so
    -- in `(a → b → c)`, it will never vist `b → c`.
    -- But since we use `matchUpToHyps` instead of `isDefEq` directly, this is ok.
    Lean.Meta.anyExpr cTy $ matchUpToHyps pat head

/-!
## The find tactic engine: Index and matching
-/

/-- For all names `n` mentioned in the type of the constant `c`, add a mapping from
`n` to `c.name` to the relation. -/
private def addDecl (c : ConstantInfo) (m : NameRel) : CoreM NameRel := do
  if ← c.name.isBlackListed then
    return m
  let consts := c.type.foldConsts {} (flip NameSet.insert)
  return consts.fold (init := m) fun m n => m.insert n c.name

private def addLibraryDecl (c : ConstantInfo) : NameRel × NameRel → CoreM (NameRel × NameRel)
  | (m₁, m₂) => do return (← addDecl c m₁, m₂)

private def addLocalDecl (c : ConstantInfo) : NameRel × NameRel → CoreM (NameRel × NameRel)
  | (m₁, m₂) => do return (m₁, ← addDecl c m₂)

/-- The declaration cache used by `#find`, stores `NameRel` mapping names to the name
of constants they are mentinend in.

The first `NameRel` is for library declaration (and doesn't change once populated),
the second is for local declarations and is rebuilt upon every invocation of `#find`.  -/
def Index := DeclCache (NameRel × NameRel)

-- NB: In large files it may be slightly wasteful to calculate a full NameSet for the local
-- definition upon every invocation of `#find`, and a linear scan might work better. For now,
-- this keeps the code below more uniform.

/-- Create a fresh index.  -/
def Index.mk : IO Index :=
  DeclCache.mk
    (profilingName := "#find: init cache")
    (empty := ({}, {}))
    (addLibraryDecl := fun _ c m => addLibraryDecl c m)
    (addDecl := fun _ c m => addLocalDecl c m)

/-- Create an index from a cached value -/
def Index.mkFromCache (init : NameRel × NameRel) : IO Index :=
  DeclCache.mkFromCache init
    (addDecl := fun _ c m => addLocalDecl c m)


/-- The parsed and elaborated arguments to `#find`  -/
structure Arguments where
  /-- Identifiers to search for -/
  idents : Array Name
  /-- Lemma name substrings to search for -/
  namePats : Array String
  /-- Term patterns to search for. The boolean indicates conclusion patterns. -/
  terms : Array (Bool × Expr)

/-- Result of `find` -/
structure Result where
  /-- Statistical summary -/
  header : MessageData
  /-- Total number of matches -/
  count : Nat
  /-- Matching definition (with defining module, if imported)  -/
  hits : Array (ConstantInfo × Option Name)

/-- The core of the `#find` tactic with all parsing/printing factored out, for
programmatic use (e.g. the loogle CLI).
It also does not use the implicit global Index, but rather expects one as an argument. -/
def find (index : Index) (args : Arguments) (maxShown := 200) :
    MetaM (Except MessageData Result) := do
  profileitM Exception "#find" (← getOptions) do
    -- Collect set of names to query the index by
    let needles : NameSet :=
          {} |> args.idents.foldl NameSet.insert
             |> args.terms.foldl (fun s (_,t) => t.foldConsts s (flip NameSet.insert))
    if needles.isEmpty then do
      return .error m!"Cannot search: No constants in search pattern."

    -- Prepare term patterns
    let pats ← liftM <| args.terms.mapM fun (isConclusionPattern, t) =>
      if isConclusionPattern then
        matchConclusion t
      else
        matchAnywhere t

    -- Query the declaration cache
    let (m₁, m₂) ← index.get
    let hits := RBTree.intersects <| needles.toArray.map <| fun needle =>
      (m₁.find needle).union (m₂.find needle)

    -- Filter by name patterns
    let nameMatchers := args.namePats.map String.Matcher.ofString
    let hits2 := hits.toArray.filter fun n => nameMatchers.all fun m =>
      m.find? n.toString |>.isSome

    -- Obtain ConstantInfos
    let env ← getEnv
    let hits3 := hits2.filterMap env.find?

    -- Filter by term patterns
    let hits4 ← hits3.filterM fun ci => pats.allM (· ci)

    -- Add defining module index
    let hits5 := hits4.map fun ci => (ci, env.getModuleIdxFor? ci.name)

    -- Sort by modindex and then by name.
    -- A ModIdx of none means locally defined, we put them first.
    -- The modindex corresponds to a topological sort of the modules, so basic lemmas come earlier.
    let hits6 := hits5.qsort fun (ci1, mi1) (ci2, mi2) =>
      match mi1, mi2 with
      | none, none => Name.lt ci1.name ci2.name
      | none, some _ => true
      | some _, none => false
      | some mi1, some mi2 =>
        Nat.blt mi1 mi2 || Nat.beq mi1 mi2 && Name.lt ci1.name ci2.name

    -- Apply maxShown limit
    let hits7 := hits6.extract 0 maxShown

    -- Resolve ModIndex to module name
    let hits8 := hits7.map fun (ci, mi) =>
      let modName : Option Name := do env.header.moduleNames[(← mi).toNat]!
      (ci, modName)

    let summary ← IO.mkRef MessageData.nil
    let addLine line := do summary.set <| (← summary.get) ++ line ++ Format.line

    let needlesList := MessageData.andList (needles.toArray.map .ofName)
    addLine m!"Found {hits.size} definitions mentioning {needlesList}."
    unless (args.namePats.isEmpty) do
      let nameList := MessageData.andList <| args.namePats.map fun s => m!"\"{s}\""
      addLine $ m!"Of these, {hits2.size} have a name containing {nameList}."
    unless (pats.isEmpty) do
      addLine $ m!"Of these, {hits4.size} match your patterns."
    unless (hits7.size ≤ maxShown) do
      addLine $ m!"Of these, only the first {maxShown} are shown."
    return .ok ⟨← summary.get, hits4.size, hits8⟩

/-!
## The #find command, syntax and parsing
-/

open Parser

/-- The turnstyle uesd bin `#find`, unicode or ascii allowed -/
syntax turnstyle := patternIgnore("⊢ " <|> "|- ")
/-- a single `#find` filter. The `term` can also be an ident or a strlit,
these are distinguished in `parseFindFilters` -/
syntax find_filter := (turnstyle term) <|> term

/-- The argument to `#find`, a list of filters -/
syntax find_filters := find_filter,*

/-- A variant of `Lean.Elab.Term.elabTerm` that does not complain for example
when a type class constraint has no instances.  -/
def elabTerm' (t : Term) (expectedType? : Option Expr) : TermElabM Expr := do
  withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) do
    let t ← Term.elabTerm t expectedType?
    Term.synthesizeSyntheticMVars (mayPostpone := false) (ignoreStuckTC := true)
    return t

/-- Parses `find_filters` syntax into `Arguments` -/
def parseFindFilters (args : TSyntax ``find_filters) : TermElabM Arguments :=
  withReader (fun ctx => { ctx with errToSorry := false }) do
    let mut idents := #[]
    let mut namePats := #[]
    let mut terms := #[]
    match args with
    | `(find_filters| $args':find_filter,*) =>
      for arg in args'.getElems do
        match arg with
        | `(find_filter| $_:turnstyle $s:term) => do
          let t ← elabTerm' s none
          terms := terms.push (true, t)
        | `(find_filter| $ss:str) => do
          let str := Lean.TSyntax.getString ss
          namePats := namePats.push str
        | `(find_filter| $i:ident) => do
          let n := Lean.TSyntax.getId i
          unless (← getEnv).contains n do
            throwErrorAt i "unknown identifier '{n}'"
          idents := idents.push n
        | `(find_filter| _) => do
            throwErrorAt arg ("Cannot search for _. " ++
              "Did you forget to put a term pattern in parentheses?")
        | `(find_filter| $s:term) => do
          let t ← elabTerm' s none
          terms := terms.push (false, t)
        | _ => throwErrorAt args "unexpected argument to #find"
    | _ => throwErrorAt args "unexpected argument to #find"
    pure {idents, namePats, terms}


/-
###  The per-module cache used by the `#find` command
-/

open System (FilePath)

/-- Where to search for the cached index -/
def cachePath : IO FilePath :=
  try
    return (← findOLean `MathlibExtras.Find).withExtension "extra"
  catch _ =>
    return "build" / "lib" / "MathlibExtras" / "Find.extra"

/-- The `DeclCache` used by `#find`, together with the `CompactedRegion`, if present -/
initialize cachedData : WithCompactedRegion (DeclCache (NameRel × NameRel)) ← unsafe do
  let path ← cachePath
  if (← path.pathExists) then
    let (d, r) ← unpickle (NameRel × NameRel) path
    return ⟨r, ← Index.mkFromCache d⟩
  else
    return ⟨none, ← Index.mk⟩

open Command

/--
The `#find` command finds definitions and lemmas in various ways. One can search by: the constants
involved in the type; a substring of the name; a subexpression of the type; or a subexpression
located in the return type or a hypothesis specifically. All of these search methods can be
combined in a single query, comma-separated.

1. By constant:
   ```lean
   #find Real.sin
   ```
   finds all lemmas whose statement somehow mentions the sine function.

2. By lemma name substring:
   ```lean
   #find Real.sin, "two"
   ```
   restricts the search above to those lemmas that have `"two"` as part of the lemma _name_.

   (Currently, substring searches _must_ be combined with other kind of queries.)

3. By subexpression:
   ```lean
   #find _ * (_ ^ _)
   ```
   finds all lemmas whose statements somewhere include a product where the second argument is
   raised to some power.

   The pattern can also be non-linear, as in
   ```lean
   #find Real.sqrt ?a * Real.sqrt ?a
   ```

   If the pattern has parameters, they are matched in any order. Both of these will find `List.map`:
   ```
   #find (?a -> ?b) -> List ?a -> List ?b
   #find List ?a -> (?a -> ?b) -> List ?b
   ```

4. By main conclusion:
   ```lean
   #find ⊢ tsum _ = _ * tsum _
   ```
   finds all lemmas where the conclusion (the subexpression to the right of all `→` and `∀`) has the
   given shape.

   As before, if the pattern has parameters, they are matched against the hypotheses of
   the lemma in any order; for example,
   ```lean
   #find ⊢ _ < _ → tsum _ < tsum _
   ```
   will find `tsum_lt_tsum` even though the hypothesis `f i < g i` is not the last.


If you pass more than one such search filter, `#find` will return lemmas which match _all_ of them.
The search
```lean
#find Real.sin, "two", tsum,  _ * _, _ ^ _, ⊢ _ < _ → _
```
will find all lemmas which mention the constants `Real.sin` and `tsum`, have `"two"` as a
substring of the lemma name, include a product and a power somewhere in the type, *and* have a
hypothesis of the form `_ < _`.

At least some filter must mention a concrete name, because `#find` maintains an index of which
lemmas mention which other constants. This is also why the _first_ use of `#find` will be somewhat
slow (typically less than half a minute with all of `Mathlib` imported), but subsequent uses are
faster.

It may be useful to open a scratch file, `import Mathlib`, and use `#find` there, this way you will
find lemmas that you have not yet imported, and the cache will stay up-to-date.
-/
elab s:"#find " args:find_filters : command => liftTermElabM do
  profileitM Exception "find" (← getOptions) do
    match ← find cachedData.val (← parseFindFilters args) with
    | .error warn =>
      Lean.logWarningAt s warn
    | .ok result =>
      let names := result.hits.map (·.1.name)
      Lean.logInfo $ result.header ++ (← MessageData.bulletListOfConsts names)
