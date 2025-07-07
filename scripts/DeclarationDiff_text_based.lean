import Aesop
import Batteries.Data.String.Matcher
import Mathlib.Tactic.Lemma
import Mathlib.Util.ParseCommand

/-! # Declaration diff

This file defines the main script used by the declaration diff bot that posts the PR summary.

From the output of `git diff --unified=0 origin/master...HEAD`, we extract the information of which
declarations have been added/removed in the current commit.
This is achieved by parsing the `git diff` lines, following the "regular" parsers, up until we find
the declaration ids.
From then and until the rest of the line, we simply lump everything into a single new syntax node.

Once this has been performed, we tally the results on all the diff-lines.
-/
namespace DeclDiff

open Lean Parser Elab Command

/--
The declaration diff script reacts to these `keywords`: the presence of one of
these string in a `git diff` line triggers the script.
-/
abbrev keywords :=
  #["abbrev", "alias", "axiom", "class", "class inductive", "def", "example", "inductive",
    "instance", "lemma", "opaque", "structure", "theorem"]

/--
`DiffData` is the main structure carrying around the information about added/removed
declarations
* `file` is the file containing the declaration;
* `keyword` is what kind of declaration it is (e.g. `theorem`, `structure`,...);
* `id` is the name of the declaration;
* `rest` is the content of the line containing the name of the declaration, after the name itself;
* `new` is whether the declaration is in the new version or in the old one.
-/
structure DiffData where
  /-- `file` is the file containing the declaration. -/
  file : String
  /-- `keyword` is what kind of declaration it is (e.g. `theorem`, `structure`,...). -/
  keyword : String
  /-- `id` is the name of the declaration. -/
  id : Name
  /-- `rest` is the content of the line containing the name of the declaration,
  after the name itself. -/
  rest : String
  /-- `new` is whether the declaration is in the new version or in the old one. -/
  new : Bool

/-- A utility instance, to see what a `DiffData` contains. -/
instance : ToString DiffData where
  toString d := s!"file: {d.file}\nkeyword: {d.keyword}\nid: {d.id}\nrest: {d.rest}\nnew: {d.new}"

section Starts
/-!
# Parsing isolated lines

This section copies over the starts of the parsers of the various declaration commands.
We are only interested in converting a single diff line containing one of the declaration keywords
into a syntax object.
For this, we parse a command up to its declaration ID and continue with a "parse everything up to
the following line break" (`restOfDeclParser`).
From this "stumped" syntax object, we later extract all that we need.

`alias ⟨f, r⟩ := y_iff` is the main exception here, since it does not have a single id.
-/

/-- The `SyntaxNodeKind` of everything on the line that contains the declaration name, starting
from after the declaration name (or after `instance`, in the case of nameless `instances`). -/
abbrev restOfDeclKind : SyntaxNodeKind := `DeclDiff.restOfDecl

/--
Parses everything up until the first line break, creating a node with kind `restOfDeclKind`
containing a single atom with value the parsed text.

This is used to absorb what is left of a diff-line after a `declId`.
-/
def restOfDeclFn : ParserFn := fun c s =>
  let i := s.pos
  let s := takeWhileFn (· != '\n') c s
  mkNodeToken restOfDeclKind i c s

@[inherit_doc restOfDeclFn]
def restOfDeclNoAntiquot : Parser := {
  fn   := restOfDeclFn
  info := mkAtomicInfo "restOfDecl"
}

@[inherit_doc restOfDeclFn]
def restOfDeclParser : Parser :=
  withAntiquot (mkAntiquot "restOfDecl" restOfDeclKind) restOfDeclNoAntiquot

/-- The tokens appearing in `alias ⟨f, r⟩`: this is not strictly necessary, but simplifies
the retrieval of the keyword `alias`. -/
def anon := ("⟨", ",", "⟩")

/-- Stump parser for `abbrev` -/
def abbrevTk := leading_parser "abbrev " >> declId
/-- Stump parser for `alias` -/
def aliasFRTk := leading_parser "alias " >> optional anon.1 >>
  Term.binderIdent >> optional (anon.2.1 >> Term.binderIdent >> anon.2.2)
/-- Stump parser for `def` -/
def definitionTk := leading_parser "def " >> declId
/-- Stump parser for `lemma` -/
def lemmaTk := leading_parser "lemma " >> declId
/-- Stump parser for `theorem` -/
def theoremTk := leading_parser "theorem " >> declId
/-- Stump parser for `opaque` -/
def opaqueTk := leading_parser "opaque " >> declId
/- As `declSig` starts with a space, "instance" does not need a trailing space
  if we put `ppSpace` in the optional fragments. -/
/-- Stump parser for `instance` -/
def instanceTk := leading_parser Term.attrKind >> "instance" >> optNamedPrio >> optional (ppSpace >> declId)
/-- Stump parser for `axiom` -/
def axiomTk := leading_parser "axiom " >> declId
/- As `declSig` starts with a space, "example" does not need a trailing space. -/
/-- Stump parser for `example` -/
def exampleTk := leading_parser "example"
/-- Stump parser for `inductive` -/
def inductiveTk := leading_parser "inductive " >> declId
/-- Stump parser for `class inductive` -/
def classInductiveTk := leading_parser atomic (group (symbol "class " >> "inductive ")) >> declId
/-- Stump parser for `structure`/`class` -/
def structureTk := leading_parser ("structure " <|> "class ") >> declId

/--
Extract the strings embedded in `Lean.Parser.symbol` by scanning the input `Expr`.
We only enter `app` and `lam`, since these constructors are sufficient to extract the correct
data from the parsers above.
-/
def getSymbols : Expr → Array String
  | .app (.const ``Lean.Parser.withAntiquot ..) _ => #[]
  | .app (.const ``Lean.Name.mkStr2 ..) _ => #[]
  | .app (.const ``Lean.Parser.symbol ..) (.lit (.strVal g)) => #[g.trim]
  | .app f g => getSymbols f ++ getSymbols g
  | .lam _ _ e _ => getSymbols e
  | _ => #[]

-- Check that `DeclDiff.keywords` and the parsers above coincide.
-- This is a consistency check, so that we keep `keywords` and the parsers in sync.
#eval show TermElabM _ from do
  let csts := (← getEnv).constants.map₂
  let mut parserSymbols := #[]
  for (nm, cinfo) in csts do
    if nm.toString.endsWith "Tk" then
      let symbolParts := getSymbols cinfo.value!
      let symbols :=
        -- Special-casing `structure`/`class`, probably due to the existence of `class inductive`
        if symbolParts == #["structure", "class"] then
          symbolParts
        else #[" ".intercalate symbolParts.toList]
      for symbol in symbols do
        parserSymbols := parserSymbols.binInsert (· < ·) symbol
  if (parserSymbols != DeclDiff.keywords) then
    logWarning <| .joinSep (parserSymbols.map (m!"{·}")).toList "\n"

end Starts

/--
The `declaration` parser parses
* the declaration modifiers (as a regular command would);
* the keyword of the declaration commands (as a regular command would);
* the `declID` of the command (as a regular command would);
* whatever is left on the line into a single syntax node (unlike what a regular command would).
-/
def declaration := leading_parser
  declModifiers false >>
    (abbrevTk <|> aliasFRTk <|> definitionTk <|> lemmaTk <|> theoremTk <|> opaqueTk <|>
     instanceTk <|> axiomTk <|> exampleTk <|> inductiveTk <|> classInductiveTk <|> structureTk)
    >> restOfDeclParser

/--
Extract the parsers appearing in `declaration` by scanning the input `Expr`.
We expect to find all the "stump" parsers above and the scanning is sufficient for finding them.
-/
partial
def getSymbols' (e : Expr) : Array Name :=
  match e.getAppFnArgs with
  | (``HOrElse.hOrElse, #[_, _, _, _, .const nm _, fn]) => (getSymbols' fn).push nm
  | _ => match e with
          | .app f g => getSymbols' f ++ getSymbols' g
          | .lam _ e (.const nm _) _ => (getSymbols' e).push nm
          | .lam _ _ e _ => getSymbols' e
          | _ => #[]

-- Check that the parsers appearing in `declaration` are all the parsers defined in this file
-- whose name ends in `Tk`.  The `restOfDeclParser` is special-cased.
-- This is a consistency check, so that we keep `keywords` and the parsers in sync.
#eval show TermElabM _ from do
  let cinfo := (← getEnv).find? ``declaration |>.get!
  let parsers := getSymbols' cinfo.value! |>.qsort Name.lt
  let csts := (← getEnv).constants.map₂
  let mut parserSymbols := #[]
  for (nm, _) in csts do
    if nm.toString.endsWith "Tk" then
      parserSymbols := parserSymbols.binInsert Name.lt nm

  if parserSymbols != parsers.erase ``restOfDeclParser then
    logWarning m!"DIFFERENT!!"
    for e in (parserSymbols ++ #[`dummy, `dummy]).zip (parsers ++ #[`dummy, `dummy]) do
      dbg_trace e

/-- From the syntax generated by the `declaration` parser in this file, extract the `keyword`. -/
def getKeyword (s : Syntax) : String :=
  -- First, we deal with `class inductive`, which is inside a `group`
  match s.find? (·.isOfKind `group) with
  | some gp => gp.getSubstring?.get!.trim.toString
  | _ =>
    -- Once `class inductive` is out of the way, every other keyword is the first atom after the
    -- `declModifiers`
    match s[1].find? (·.isAtom) with
    | some atomKey => atomKey.getAtomVal
    | none => "[keyword not found]"

/--
From the syntax generated by the `declaration` parser in this file, extract the ids of the
declarations.

All declarations contain exactly one id, with the exception of
* `alias ⟨f, r⟩`, that contains 2;
* nameless `instance`s, that contain none.
-/
def getDeclIds (s : Syntax) : Array Name :=
  -- `alias` has a "double" version `alias X := Y` and `alias ⟨F, R⟩ := Y_iff`, so we deal with it
  -- separately.
  match s[1] with
  | `(aliasFRTk| alias ⟨$i1, $i2⟩) => #[i1.raw.getId, i2.raw.getId].filter (!·.isAnonymous)
  | `(aliasFRTk| alias $i1) => #[i1.raw.getId]
  | _ =>
    match s[1].find? (·.isOfKind ``declId) with
    | some id => #[id[0].getId]
    | none => #[.anonymous]

/--
From the syntax generated by the `declaration` parser in this file, extract the rest of the
line, after the id.
-/
def getRest (s : Syntax) : String :=
  match s.find? (·.isOfKind restOfDeclKind) with
  | some inst => inst[0].getAtomVal
  | none => "getRest: declaration signature not found"

/-- From
* the syntax `s` generated by the `declaration` parser in this file,
* the path `file` of a file,
* the `Bool`ean `new` representing whether the declaration is added (`true`) or removed (`false`),
construct the corresponding array `DiffData`, one for each id extracted from `s`. -/
def getDiffDatas (s : Syntax) (file : String) (new : Bool) : Array DiffData :=
  let template : DiffData := {
    file := file
    keyword := getKeyword s
    id := .anonymous
    rest := getRest s
    new := new
    }
  (getDeclIds s).map ({template with id := ·})

/--
`parseLine` takes as input
* an `Environment` `env`,
* a string `input` representing a line in the `git diff` containing a declaration keyword,
* a path `file` for the corresponding file,
* a `Bool`ean representing whether the diff line `input` is added or removed.

It parses the `input` string and then converts it to an array of `DiffData`, producing an
"error" `DiffData`, in case the parsing is unsuccessful.

*Note*. Unsuccessful parsing is not necessarily a sign of a bug: if a line in the `git diff`
contains one of the keywords, but is not line of actual code (e.g., it is part of a doc-string),
it is expected that parsing will fail.
-/
def parseLine (env : Environment) (input : String) (file : String) (new : Bool) : Array DiffData :=
  match Mathlib.GuardExceptions.captureException env DeclDiff.declaration.fn input with
  | .ok s => getDiffDatas s file new
  | .error _ => #[{
      file := file
      new := new
      id := .anonymous
      keyword := "error"
      rest := s!"parseLine: Something went wrong on input '{input}'"
    }]

/--
info: (lemma, lemmaX, : True := trivial)
(alias, aliasNat, := Nat)
(alias, aliasRevOnly, := Nat)
(alias, aliasFwdOnly, := Nat)
(alias, aliasFwd, := Nat)
(alias, aliasRev, := Nat)
(theorem, theoremX, : True := trivial)
(instance, instX, : True := trivial)
(instance, [anonymous], : True := trivial)
(example, [anonymous], : True := trivial)
(structure, structureDecl, : Prop where)
(class, classDecl, : Prop where)
(class inductive, classInductive, : True := trivial)
(instance, instWithPriority, )
-/
#guard_msgs in
run_cmd
  let env ← getEnv
  let tests := #[
    "lemma lemmaX.{u, v} : True := trivial",
    "alias aliasNat := Nat",
    "alias ⟨_, aliasRevOnly⟩ := Nat",
    "alias ⟨aliasFwdOnly, _⟩ := Nat",
    "alias ⟨aliasFwd, aliasRev⟩ := Nat",
    "@[simp, aesop 10% (rule_sets := [Restrict])] nonrec theorem theoremX.{u, v} : True := trivial",
    "noncomputable partial instance instX.{u, v} : True := trivial",
    "private partial instance : True := trivial",
    "example : True := trivial",
    "structure structureDecl : Prop where",
    "class classDecl : Prop where",
    "class inductive classInductive : True := trivial",
    "instance (priority := 100) instWithPriority",
  ]
  for t in tests do
    let diffDatas := parseLine env t "path" true
    for diffData in diffDatas do
      IO.println <| s!"({diffData.keyword}, {diffData.id}, {diffData.rest})"

/-- Converts a `DiffData` into the actual string that the PR summary uses:
* just the declaration name, in case the declaration has a name
  (i.e., it is not a nameless `instance`);
* the full `instance ...` line, if the data corresponds to a nameless `instance`.
-/
def formatDiffData (d : DiffData) : Option String :=
  if d.keyword != "error" then
    if d.keyword != "instance" then
      d.id.toString
    else
      let desc := d.rest.splitOn " :="
      let desc := desc[0]!.splitOn " where"
      s!"instance {desc[0]!}"
  else none

/-- For an array of `DiffData`, we tally how many times each `formatDiffData` appears in the
array, adding the ones for which `new = true` and subtracting the ones for which `new = false`. -/
def tally (ds : Array DiffData) : Std.HashMap String Int :=
  ds.foldl (init := ∅) fun tally d =>
    match formatDiffData d with
    | none => tally
    | some desc =>
        tally.alter desc (some <| ·.getD 0 + if d.new then 1 else -1)

end DeclDiff

open Lean in
/--
`#declaration_diff` computes the declaration diff between `upstream/master` and the current `HEAD`,
by parsing the output of `git diff --unified=0 upstream/master...HEAD`.

The command takes two optional inputs.
* `#declaration_diff <compare>` uses the output of `git diff --unified=0 <compare>` instead.
* `#declaration_diff verbose` produces more information about the computation, ultimately
  printing the same message, but preceded by some useful/debugging data.
* `#declaration_diff <compare> verbose` does the merging of the two versions above: it uses
  `<compare>` to produce the diff and emits a verbose output.
-/
elab "#declaration_diff" commits:(ppSpace str)? verbose:(ppSpace "verbose")? : command => do
  let commits := if let some str := commits then str.getString else "upstream/master...HEAD"
  let env ← getEnv
  let mut plusFile := ""
  let mut minusFile := ""
  let mut diffDatas := #[]
  if verbose.isSome then
    logInfo m!"Computing 'git diff --unified=0 {commits}'\n"
  let gitDiff ← IO.Process.run {
    cmd := "git"
    args := #["diff", "--unified=0", commits]
  }
  -- Loop over the lines in the diff
  for l in gitDiff.splitOn "\n" do
    if l.startsWith "--- " then
      -- From a line such as `--- a/Mathlib/...` we extract `Mathlib/...` to `minusFile`.
      minusFile := l.dropWhile (· != 'M')
    if l.startsWith "+++ " then
      -- From a line such as `+++ a/Mathlib/...` we extract `Mathlib/...` to `plusFile`.
      plusFile := l.dropWhile (· != 'M')
    let pm := l.take 1 -- This is either `+` or `-`.
    unless #["+", "-"].contains pm do
      continue
    let new := pm == "+"
    let file := if new then plusFile else minusFile
    if DeclDiff.keywords.any (l.containsSubstr <| ·.push ' ') then
      diffDatas := diffDatas ++ DeclDiff.parseLine env (l.drop 1) file new
  let total := diffDatas.size
  let parsed := diffDatas.filter (·.keyword != "error") |>.size
  if verbose.isSome then
    logInfo m!"Parsing attempts:  {total}\nSuccessful parses: {parsed}\n"
  if verbose.isSome then
    let errors := diffDatas.filterMap fun d => if d.keyword == "error" then some m!"{d}" else none
    logInfo <| .joinSep (m!"ERRORS\n"::errors.toList) m!"\n"

  let tally := DeclDiff.tally diffDatas
  let report := tally.toArray.qsort (·.1 < ·.1) |>.foldl (init := #[]) fun tot (decl, count) =>
    -- We skip diffs where as many declarations have been added as removed.
    if count == 0 then tot
    else tot.push m!"{if 0 < count then m!"+{count}" else m!"{count}"} `{decl}`"
  logInfo <| .joinSep report.toList "\n"

#declaration_diff "upstream/master...jriou-types-multicoequalizer-set" --verbose

open Lean
/--
info: Computing 'git diff --unified=0 upstream/master...jriou-types-multicoequalizer-set'
---
info: Parsing attempts:  146
Successful parses: 145
---
info: ERRORS

file: Mathlib/CategoryTheory/Limits/Types/Multicoequalizer.lean
keyword: error
id: [anonymous]
rest: parseLine: Something went wrong on input '`c : d.multispan.CoconeTypes`, we obtain a lemma `isMulticoequalizer_iff`'
new: true
---
info: +1 `BicartSq`
+1 `CoconeTypes.isColimit_iff`
+1 `IsColimit.precompose`
+1 `Lattice.BicartSq.multicoequalizerDiagram`
+1 `M.map_mk`
+1 `M.mk_map`
+2 `M.mk_surjective`
+1 `MulticoequalizerDiagram`
-1 `Quot.desc_colimitCocone`
-1 `Quot.desc_quotQuotUliftEquiv`
-1 `Quot.desc_toCocone_desc`
+1 `coconeTypesEquiv`
+1 `colimitEquivColimitType`
+1 `colimitEquivColimitType_apply`
+1 `colimitEquivColimitType_symm_apply`
-1 `colimitModule.add_smul`
-1 `colimitModule.one_smul`
+1 `colimitTypeRelEquivOrbitRelQuotient`
+1 `colimitTypeRel_iff_orbitRel`
+1 `colimit_add_mk_eq`
+1 `colimit_add_mk_eq'`
+1 `colimit_mul_mk_eq`
+2 `colimit_mul_mk_eq'`
+1 `colimit_one_eq`
+1 `colimit_zero_eq`
+1 `commSq`
+1 `descAddMonoidHom`
+1 `descAddMonoidHom_quotMk`
+1 `descMonoidHom`
+1 `descMonoidHom_apply_eq`
+1 `descMonoidHom_quotMk`
+1 `eqvGen_colimitTypeRel_of_rel`
+1 `finite_of_isColimit`
+1 `fullyFaithfulForgetToMonCat`
+1 `fullyFaithfulForget₂ToGrp`
+1 `fullyFaithfulForget₂ToMonCat`
+1 `fullyFaithfulForget₂ToRingCat`
+2 `fullyFaithfulForget₂ToSemiRingCat`
+2 `hasColimit_iff_small_colimitType`
+1 `instance : (forget₂ CommGrp.{u} Grp).Full`
+1 `instance : (forget₂ CommRingCat RingCat).Full`
+1 `instance : (forget₂ CommSemiRingCat SemiRingCat).Full`
+1 `instance : (forget₂ Grp.{u} MonCat).Full`
+1 `instance : (forget₂ RingCat SemiRingCat).Full`
+1 `instance [Small.{u} J] (F : J ⥤ Type u) : Small.{u} (F.ColimitType)`
-1 `instance [Small.{u} J] (F : J ⥤ Type u) : Small.{u} (Quot F)`
+1 `instance {J : Type} [SmallCategory J] [FinCategory J]`
+1 `isColimitOfMulticoequalizerDiagram`
+1 `isColimit_iff_coconeTypesIsColimit`
+1 `isColimit_precompose_iff`
+1 `isMulticoequalizer_iff`
+1 `le₁₂`
+1 `le₁₃`
+1 `le₂₄`
+1 `le₃₄`
+1 `multicofork`
+1 `multispanIndex`
+1 `naturality_symm`
+2 `precompose`
-1 `quotQuotUliftEquiv`
-1 `quotToQuotUlift`
-1 `quotToQuotUlift_ι`
-1 `quotUliftToQuot`
-1 `quotUliftToQuot_ι`
+1 `rel_eq_eqvGen_colimitTypeRel`
+1 `rel_of_colimitTypeRel`
+1 `small_colimitType_of_hasColimit`
-1 `toCocone`
+2 `zigzag_of_eqvGen_colimitTypeRel`
+1 `ιColimitType_eq_iff`
+1 `ι_colimitDesc`
-/
#guard_msgs in
#declaration_diff "upstream/master...jriou-types-multicoequalizer-set" verbose
