/-
Copyright (c) 2023 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Util.FoldConsts
import Lean

/-! # `lake exe shake` command

This command will check mathlib (or the specified modules) and all their dependency for unused
imports. This works by looking at generated `.olean` files to deduce required imports and ensuring
that every import is used to contribute some constant. Because recompilation is not needed this
is quite fast (about 8 seconds to check `Mathlib` and all dependencies), but it has some known
limitations:

* Tactics that are used during elaboration generally leave no trace in the proof term, so
  they will be incorrectly marked as unused.
* Similarly, files that contribute only notations will not be detected.
* Conversely, files that define tactics and notations are also likely to have false positives
  because the notation itself does not depend on the referenced constant (it elaborates to a
  name literal rather than an actual reference to the target constant).

To mitigate this, the `scripts/noshake.json` file is used to suppress known false positives. See
`ShakeCfg` for information regarding the file format.

-/

def help : String := "Mathlib4 tree shaking tool
Usage: lake exe shake [OPTIONS] <MODULE>..

Arguments:
  <MODULE>
    A module path like `Mathlib`. All files transitively reachable from the
    provided module(s) will be checked.

Options:
  --fix
    Apply the suggested fixes directly. Make sure you have a clean checkout
    before running this, so you can review the changes.

  --cfg <FILE>   (default: scripts/noshake.json)
    Use FILE to specify which imports we should ignore.

  --update
    Assume that all issues we find are false positives and update the config
    file to include them.

  --no-downstream
    Unless disabled, shake will check downstream files that were transitively
    depending on the import we want to remove and re-add the import to these
    downstream files.

# The noshake.json file

The file passed in the --cfg argument is a JSON file with the following
structure:

  {
    \"ignoreAll\": [NAME],
    \"ignoreImport\": [NAME],
    \"ignore\": {NAME: [NAME]}
  }

The fields can be omitted if empty. They have the following interpretation:

* ignoreAll:
  All imports in these files should be treated as necessary
* ignore[X]:
  All imports in the list should be treated as necessary when processing X
* ignoreImport:
  These files should be treated as necessary when imported into any other file.
"

open Lean

/-- We use `Nat` as a bitset for doing efficient set operations.
The bit indexes will usually be a module index. -/
abbrev Bitset := Nat

/-- The main state of the checker, containing information on all loaded modules. -/
structure State where
  /-- Maps a module name to its index in the module list. -/
  toIdx : HashMap Name USize := {}
  /-- Maps a module index to the module name. -/
  modNames : Array Name := #[]
  /-- Maps a module index to the module data. -/
  mods : Array ModuleData := #[]
  /-- `j ∈ deps[i]` if module `j` is a direct dependency of module `i` -/
  deps : Array (Array USize) := #[]
  /-- `j ∈ transDeps[i]` is the reflexive transitive closure of `deps` -/
  transDeps : Array Bitset := #[]
  /-- `j ∈ needs[i]` if module `i` uses a constant declared in module `j`.
  Note: this is left empty if `args.downstream` is false, we calculate `needs` on demand -/
  needs : Array Bitset := #[]
  /-- Maps a constant name to the module index containing it. -/
  constToIdx : HashMap Name USize := {}

/-- Returns `true` if this is a constant whose body should not be considered for dependency
tracking purposes. -/
def isBlacklisted (name : Name) : Bool :=
  -- Compiler-produced definitions are skipped, because they can sometimes pick up spurious
  -- dependencies due to specializations in unrelated files. Even if we remove these modules
  -- from the import path, the compiler will still just find another way to compile the definition.
  if let .str _ "_cstage2" := name then true else
  if let .str _ "_cstage1" := name then true else
  false

/-- Calculates the value of the `needs[i]` bitset for a given module `mod`.
Bit `j` is set in the result if some constant from module `j` is used in this module. -/
def calcNeeds (constToIdx : HashMap Name USize) (mod : ModuleData) : Bitset :=
  mod.constants.foldl (init := 0) fun deps ci =>
    if isBlacklisted ci.name then deps else
    let deps := visitExpr ci.type deps
    match ci.value? with
    | some e => visitExpr e deps
    | none => deps
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr e deps :=
    Lean.Expr.foldConsts e deps fun c deps => match constToIdx.find? c with
      | some i => deps ||| (1 <<< i.toNat)
      | none => deps

/-- Calculates the same as `calcNeeds` but tracing each module to a specific constant. -/
def getExplanations (constToIdx : HashMap Name USize) (mod : ModuleData) :
    HashMap USize (Name × Name) :=
  mod.constants.foldl (init := {}) fun deps ci =>
    if isBlacklisted ci.name then deps else
    let deps := visitExpr ci.name ci.type deps
    match ci.value? with
    | some e => visitExpr ci.name e deps
    | none => deps
where
  /-- Accumulate the results from expression `e` into `deps`. -/
  visitExpr name e deps :=
    Lean.Expr.foldConsts e deps fun c deps => match constToIdx.find? c with
      | some i =>
        if
          if let some (name', _) := deps.find? i then
            decide (name.toString.length < name'.toString.length)
          else true
        then
          deps.insert i (name, c)
        else
          deps
      | none => deps

/-- Load all the modules in `imports` into the `State`, as well as their transitive dependencies.
Returns a pair `(imps, transImps)` where:

* `j ∈ imps` if `j` is one of the module indexes in `imports`
* `j ∈ transImps` if module `j` is transitively reachable from `imports`
 -/
partial def loadModules (imports : Array Import) : StateT State IO (Array USize × Bitset) := do
  let mut imps := #[]
  let mut transImps := 0
  for imp in imports do
    let s ← get
    if let some i := s.toIdx.find? imp.module then
      imps := imps.push i
      transImps := transImps ||| s.transDeps[i]!
    else
      let mFile ← findOLean imp.module
      unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
      let (mod, _) ← readModuleData mFile
      let (deps, transDeps) ← loadModules mod.imports
      let s ← get
      let n := s.mods.size.toUSize
      let transDeps := transDeps ||| (1 <<< n.toNat)
      imps := imps.push n
      transImps := transImps ||| transDeps
      set (σ := State) {
        toIdx := s.toIdx.insert imp.module n
        modNames := s.modNames.push imp.module
        mods := s.mods.push mod
        deps := s.deps.push deps
        transDeps := s.transDeps.push transDeps
        needs := s.needs
        constToIdx := mod.constNames.foldl (·.insert · n) s.constToIdx
      }
  return (imps, transImps)

/-- The list of edits that will be applied in `--fix`. `edits[i] = (removed, added)` where:

* If `j ∈ removed` then we want to delete module named `j` from the imports of `i`
* If `j ∈ added` then we want to add module index `j` to the imports of `i`.
  We keep this as a bitset because we will do transitive reduction before applying it
-/
def Edits := HashMap Name (NameSet × Bitset)

/-- Register that we want to remove `tgt` from the imports of `src`. -/
def Edits.remove (ed : Edits) (src tgt : Name) : Edits :=
  match ed.find? src with
  | none => ed.insert src (RBTree.insert ∅ tgt, 0)
  | some (a, b) => ed.insert src (a.insert tgt, b)

/-- Register that we want to add `tgt` to the imports of `src`. -/
def Edits.add (ed : Edits) (src : Name) (tgt : Nat) : Edits :=
  match ed.find? src with
  | none => ed.insert src (∅, 1 <<< tgt)
  | some (a, b) => ed.insert src (a, b ||| (1 <<< tgt))

/-- Parse a source file to extract the location of the import lines, for edits and error messages.

Returns `(path, inputCtx, headerStx, endPos)` where `headerStx` is the `Lean.Parser.Module.header`
and `endPos` is the position of the end of the header.
-/
def parseHeader (srcSearchPath : SearchPath) (mod : Name) :
    IO (System.FilePath × Parser.InputContext × Syntax × String.Pos) := do
  -- Parse the input file
  let some path ← srcSearchPath.findModuleWithExt "lean" mod
    | throw <| .userError "error: failed to find source file for {mod}"
  let text ← IO.FS.readFile path
  let inputCtx := Parser.mkInputContext text path.toString
  let (header, parserState, msgs) ← Parser.parseHeader inputCtx
  if !msgs.isEmpty then -- skip this file if there are parse errors
    msgs.forM fun msg => msg.toString >>= IO.println
    throw <| .userError "parse errors in file"
  -- the insertion point for `add` is the first newline after the imports
  let insertion := header.getTailPos?.getD parserState.pos
  let insertion := text.findAux (· == '\n') text.endPos insertion + ⟨1⟩
  pure (path, inputCtx, header, insertion)

/-- Analyze and report issues from module `i`. Arguments:

* `s`: The main state (contains all the modules and dependency information)
* `srcSearchPath`: Used to find the path for error reporting purposes
* `ignoreImps`: if `j ∈ ignoreImps` then it will be treated as used
* `i`: the module index
* `needs`: this is the same as `s.needs[i]`, except that this array may not
  be initialized if `downstream` mode is disabled so we pass it in here
* `edits`: accumulates the list of edits to apply if `--fix` is true
* `downstream`: if true, then we report downstream files that need to be fixed too
 -/
def visitModule (s : State) (srcSearchPath : SearchPath) (ignoreImps : Bitset)
    (i : Nat) (needs : Bitset) (edits : Edits)
    (downstream := true) (githubStyle := false) (explain := false) : IO Edits := do
  -- Do transitive reduction of `needs` in `deps` and transitive closure in `transDeps`.
  -- Include the `ignoreImps` in `transDeps`
  let mut deps := needs
  let mut transDeps := needs ||| ignoreImps
  for j in [0:s.mods.size] do
    if deps &&& (1 <<< j) != 0 then
      let deps2 := s.transDeps[j]!
      deps := deps ^^^ (deps &&& deps2) ^^^ (1 <<< j)
      transDeps := transDeps ||| deps2

  -- Any import which is not in `transDeps` was unused.
  -- Also accumulate `newDeps` which is the transitive closure of the remaining imports
  let mut toRemove := #[]
  let mut newDeps := 0
  for imp in s.mods[i]!.imports do
    let j := s.toIdx.find! imp.module
    if transDeps &&& (1 <<< j.toNat) == 0 then
      toRemove := toRemove.push j
    else
      newDeps := newDeps ||| s.transDeps[j]!

  if toRemove.isEmpty then return edits -- nothing to do

  -- If `newDeps` does not cover `needs`, then we have to add back some imports until it does.
  -- To minimize new imports we pick only new imports which are not transitively implied by
  -- another new import
  let mut toAdd := #[]
  for j in [0:s.mods.size] do
    if deps &&& (1 <<< j) != 0 && newDeps &&& (1 <<< j) == 0 then
      toAdd := toAdd.push j
      newDeps := newDeps ||| s.transDeps[j]!

  -- mark and report the removals
  let mut edits := toRemove.foldl (init := edits) fun edits n =>
    edits.remove s.modNames[i]! s.modNames[n]!
  if githubStyle then
    try
      let (path, inputCtx, header, endHeader) ← parseHeader srcSearchPath s.modNames[i]!
      for stx in header[1].getArgs do
        if toRemove.any fun i => s.modNames[i]! == stx[2].getId then
          let pos := inputCtx.fileMap.toPosition stx.getPos?.get!
          println! "{path}:{pos.line}:{pos.column+1}: warning: unused import \
            (use `lake exe shake --fix` to fix this, or `lake exe shake --update` to ignore)"
      if !toAdd.isEmpty then
        -- we put the insert message on the beginning of the last import line
        let pos := inputCtx.fileMap.toPosition endHeader
        println! "{path}:{pos.line-1}:1: warning: \
          import {toAdd.map (s.modNames[·]!)} instead"
    catch _ => pure ()
  if let some path ← srcSearchPath.findModuleWithExt "lean" s.modNames[i]! then
    println! "{path}:"
  else
    println! "{s.modNames[i]!}:"
  println! "  remove {toRemove.map (s.modNames[·]!)}"

  -- mark and report the additions
  if !toAdd.isEmpty then
    edits := toAdd.foldl (init := edits) fun edits n =>
      edits.add s.modNames[i]! n
    println! "  add {toAdd.map (s.modNames[·]!)}"

  if downstream && !toRemove.isEmpty then
    -- In `downstream` mode, we should also check all the other modules to find out if
    -- we have a situation like `A -> B -/> C -> D`, where we are removing the `B -> C` import
    -- but `D` depends on `A` and only directly imports `C`.
    -- This situation occurs when `A ∈ needs[D]`, `C ∈ transDeps[D]`, and `A ∉ newTransDeps[D]`,
    -- where `newTransDeps` is the result of recalculating `transDeps` after breaking the `B -> C`
    -- link.

    -- calculate `newTransDeps[C]`, removing all `B -> C` links from `toRemove` and adding `toAdd`
    let mut newTransDepsI := 1 <<< i
    for j in s.deps[i]! do
      if !toRemove.contains j then
        newTransDepsI := newTransDepsI ||| s.transDeps[j]!
    for j in toAdd do
      newTransDepsI := newTransDepsI ||| s.transDeps[j]!

    let mut newTransDeps := s.transDeps.set! i newTransDepsI -- deep copy
    let mut reAdded := #[]
    for j in [i+1:s.mods.size] do -- for each module `D`
      if s.transDeps[j]! &&& (1 <<< i) != 0 then -- which imports `C`
        -- calculate `newTransDeps[D]` assuming no change to the imports of `D`
        let mut newTransDepsJ := s.deps[j]!.foldl (init := 1 <<< j) fun d k =>
          d ||| newTransDeps[k]!
        let diff := s.transDeps[j]! ^^^ newTransDepsJ
        if diff != 0 then -- if the dependency closure of `D` changed
          let mut reAdd := diff &&& s.needs[j]!
          if reAdd != 0 then -- and there are things from `needs[D]` which were lost:
            -- Add them back.
            -- `reAdd` is the set of all files `A` which have to be added back
            -- to the closure of `D`, but some of them might be importing others,
            -- so we take the transitive reduction of `reAdd`.
            let mut reAddArr := []
            let mut k := j
            while reAdd != 0 do -- note: this loop terminates because `reAdd ⊆ [0:k]`
              k := k - 1
              if reAdd &&& (1 <<< k) != 0 then
                reAddArr := k :: reAddArr
                reAdd := reAdd ^^^ (reAdd &&& newTransDeps[k]!)
                -- add these to `newTransDeps[D]` so that files downstream of `D`
                -- (later in the `for j` loop) will take this into account
                newTransDepsJ := newTransDepsJ ||| newTransDeps[k]!
            edits := reAddArr.foldl (init := edits) (·.add s.modNames[j]! ·)
            reAdded := reAdded.push (j, reAddArr)
          newTransDeps := newTransDeps.set! j newTransDepsJ
    if !reAdded.isEmpty then
      println! "  instead"
      for (j, reAddArr) in reAdded do
        println! "    import {reAddArr.map (s.modNames[·]!)} in {s.modNames[j]!}"

  if explain then
    let explanation := getExplanations s.constToIdx s.mods[i]!
    let sanitize n := if n.hasMacroScopes then (sanitizeName n).run' { options := {} } else n
    let run j := do
      if let some (n, c) := explanation.find? j then
        println! "  note: {s.modNames[i]!} requires {s.modNames[j]!}\
          \n    because {sanitize n} refers to {sanitize c}"
    for imp in s.mods[i]!.imports do run <| s.toIdx.find! imp.module
    for i in toAdd do run i.toUSize

  return edits

/-- Convert a list of module names to a bitset of module indexes -/
def toBitset (s : State) (ns : List Name) : Bitset :=
  ns.foldl (init := 0) fun c name =>
    match s.toIdx.find? name with
    | some i => c ||| (1 <<< i.toNat)
    | none => c

/-- The parsed CLI arguments. See `help` for more information -/
structure Args where
  /-- `--help`: shows the help -/
  help : Bool := false
  /-- `--no-downstream`: disables downstream mode -/
  downstream : Bool := true
  /-- `--gh-style`: output messages that can be parsed by `gh-problem-matcher-wrap` -/
  githubStyle : Bool := false
  /-- `--explain`: give constants explaining why each module is needed -/
  explain : Bool := false
  /-- `--fix`: apply the fixes directly -/
  fix : Bool := false
  /-- `--update`: update the config file -/
  update : Bool := false
  /-- `--global`: with `--update`, add imports to `ignoreImport` instead of `ignore` -/
  global : Bool := false
  /-- `--cfg FILE`: choose a custom location for the config file -/
  cfg : Option String := none
  /-- `<MODULE>..`: the list of root modules to check -/
  mods : Array Name := #[]

instance {α} [FromJson α] : FromJson (NameMap α) where
  fromJson? j := do
    (← j.getObj?).foldM (init := mkNameMap _) fun m a b => do
      m.insert a.toName <$> fromJson? b
instance {α} [ToJson α] : ToJson (NameMap α) where
  toJson m := Json.obj <| m.fold (init := ∅) fun m a b =>
      m.insert compare (toString a) (toJson b)

/-- The config file format, which we both read and write. -/
structure ShakeCfg where
  /-- All imports from modules in this list will be ignored -/
  ignoreAll? : Option (List Name) := none
  /-- The modules in this list will be ignored as imports of any other file -/
  ignoreImport? : Option (List Name) := [`Init, `Lean]
  /-- If `X` maps to `Y` then an import of `Y` in module `X` will be ignored -/
  ignore? : Option (NameMap (Array Name)) := none
  deriving FromJson, ToJson

/-- The main entry point. See `help` for more information on arguments. -/
def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- Parse the arguments
  let rec parseArgs (args : Args) : List String → Args
    | [] => args
    | "--help" :: rest => parseArgs { args with help := true } rest
    | "--no-downstream" :: rest => parseArgs { args with downstream := false } rest
    | "--fix" :: rest => parseArgs { args with fix := true } rest
    | "--explain" :: rest => parseArgs { args with explain := true } rest
    | "--gh-style" :: rest => parseArgs { args with githubStyle := true } rest
    | "--update" :: rest => parseArgs { args with update := true } rest
    | "--global" :: rest => parseArgs { args with global := true } rest
    | "--cfg" :: cfg :: rest => parseArgs { args with cfg := cfg } rest
    | "--" :: rest => { args with mods := args.mods ++ rest.map (·.toName) }
    | other :: rest => parseArgs { args with mods := args.mods.push other.toName } rest
  let args := parseArgs {} args

  -- Bail if `--help` is passed
  if args.help then
    IO.println help
    IO.Process.exit 0

  if (← IO.Process.output { cmd := "lake", args := #["build", "--no-build"] }).exitCode != 0 then
    IO.println "There are out of date oleans. Run `lake build` or `lake exe cache get` first"
    IO.Process.exit 1

  -- Parse the `--cfg` argument
  let srcSearchPath ← initSrcSearchPath
  let cfgFile ← if let some cfg := args.cfg then
    pure (some ⟨cfg⟩)
  else if let some path ← srcSearchPath.findModuleWithExt "lean" `Mathlib then
    pure (some (path.parent.get! / "scripts" / "noshake.json"))
  else pure none

  -- Read the config file
  let cfg ← if let some file := cfgFile then
    try
      IO.ofExcept (Json.parse (← IO.FS.readFile file) >>= fromJson? (α := ShakeCfg))
    catch e =>
      println! "{e.toString}"
      pure {}
  else pure {}

  -- the list of root modules
  let mods := if args.mods.isEmpty then #[`Mathlib] else args.mods
  -- Only submodules of `pkg` will be edited or have info reported on them
  let pkg := mods[0]!.components.head!

  -- Load all the modules
  let mut (_, s) ← (loadModules (mods.map ({module := ·}))).run {}

  -- Parse the config file
  let ignoreMods := toBitset s (cfg.ignoreAll?.getD [])
  let ignoreImps := toBitset s (cfg.ignoreImport?.getD [])
  let ignore := (cfg.ignore?.getD {}).fold (init := mkHashMap) fun m a v =>
    m.insert a (toBitset s v.toList)

  let noIgnore (i : Nat) :=
    !s.mods[i]!.constNames.isEmpty && -- skip import-only mods
    ignoreMods &&& (1 <<< i) == 0 &&
    pkg.isPrefixOf s.modNames[i]!

  -- Run the calculation of the `needs` array in parallel
  let needs := s.mods.mapIdx fun i mod =>
    if args.downstream || noIgnore i then
      some <| Task.spawn fun _ =>
        -- remove the module from its own `needs`
        (calcNeeds s.constToIdx mod ||| (1 <<< i.1)) ^^^ (1 <<< i.1)
    else
      none
  if args.downstream then
    s := { s with needs := needs.map (·.get!.get) }

  if args.fix then
    println! "The following changes will be made automatically:"

  -- Check all selected modules
  let mut edits : Edits := mkHashMap
  for i in [0:s.mods.size], t in needs do
    if let some t := t then
      if noIgnore i then
        let ignoreImps := ignoreImps ||| ignore.findD s.modNames[i]! 0
        edits ← visitModule s srcSearchPath ignoreImps i t.get edits
          args.downstream args.githubStyle args.explain

  -- Write the config file
  if args.update then
    if let some cfgFile := cfgFile then
      let mut ignore := cfg.ignore?.getD {}
      let ignoreImport := cfg.ignoreImport?.getD {}
      let mut ignoreImportSet : NameSet := ignoreImport.foldl .insert {}
      -- if `args.fix` is true then we assume the errors will be fixed after,
      -- so it's just reformatting the existing file
      if !args.fix then
        if args.global then
          -- in global mode all the edits are added to `ignoreImport`
          ignoreImportSet := edits.fold (init := ignoreImportSet)
            (fun ignore _ (remove, _) => ignore.union remove)
        else
          -- in local mode all the edits are added to `ignore`
          ignore := edits.fold (init := ignore) fun ignore mod (remove, _) =>
            let ns := (ignore.findD mod #[]).foldl (init := remove) (·.insert ·)
            if ns.isEmpty then ignore.erase mod else
              ignore.insert mod ns.toArray
      -- If an entry is in `ignoreAll`, the `ignore` key is redundant
      for i in cfg.ignoreAll?.getD {} do
        if ignore.contains i then
          ignore := ignore.erase i
      -- If an entry is in `ignoreImport`, the `ignore` value is redundant
      ignore := ignore.fold (init := {}) fun ignore mod ns =>
        let ns := ns.filter (!ignoreImportSet.contains ·)
        if ns.isEmpty then ignore else ignore.insert mod (ns.qsort (·.toString < ·.toString))
      -- Sort the lists alphabetically
      let ignoreImport := (ignoreImportSet.toArray.qsort (·.toString < ·.toString)).toList
      let cfg : ShakeCfg := {
        ignoreAll? := cfg.ignoreAll?.filter (!·.isEmpty)
        ignoreImport? := (some ignoreImport).filter (!·.isEmpty)
        ignore? := (some ignore).filter (!·.isEmpty)
      }
      IO.FS.writeFile cfgFile <| toJson cfg |>.pretty.push '\n'

  if !args.fix then
    -- return error if any issues were found
    return if edits.isEmpty then 0 else 1

  -- Apply the edits to existing files
  let count ← edits.foldM (init := 0) fun count mod (remove, add) => do
    -- Only edit files in the current package
    if !pkg.isPrefixOf mod then
      return count
    -- Compute the transitive reduction of `add` and convert to a list of names
    let add := if add == 0 then #[] else Id.run do
      let mut val := add
      for i in [0:s.mods.size] do
        if val &&& (1 <<< i) != 0 then
          val := val ^^^ (val &&& s.transDeps[i]!) ^^^ (1 <<< i)
      let mut out := #[]
      for i in [0:s.mods.size] do
        if val &&& (1 <<< i) != 0 then
          out := out.push s.modNames[i]!
      out.qsort Name.lt

    -- Parse the input file
    let (path, inputCtx, header, insertion) ←
      try parseHeader srcSearchPath mod
      catch e => println! e.toString; return count
    let text := inputCtx.input

    -- Calculate the edit result
    let mut pos : String.Pos := 0
    let mut out : String := ""
    let mut seen : NameSet := {}
    for stx in header[1].getArgs do
      let mod := stx[2].getId
      if remove.contains mod || seen.contains mod then
        out := out ++ text.extract pos stx.getPos?.get!
        -- We use the end position of the syntax, but include whitespace up to the first newline
        pos := text.findAux (· == '\n') text.endPos stx.getTailPos?.get! + ⟨1⟩
      seen := seen.insert mod
    out := out ++ text.extract pos insertion
    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        out := out ++ s!"import {mod}\n"
    out := out ++ text.extract insertion text.endPos

    IO.FS.writeFile path out
    return count + 1

  -- Since we throw an error upon encountering issues, we can be sure that everything worked
  -- if we reach this point of the script.
  if count > 0 then
    println! "Successfully applied {count} suggestions."
  else
    println! "No edits required."
  return 0
