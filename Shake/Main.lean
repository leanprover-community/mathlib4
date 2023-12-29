import Lean.Util.FoldConsts
import Lean

open Lean

abbrev Bitset := Nat

structure State where
  toIdx : HashMap Name USize := {}
  modNames : Array Name := #[]
  mods : Array ModuleData := #[]
  deps : Array Bitset := #[]
  transDeps : Array Bitset := #[]
  needs : Array Bitset := #[]
  constToIdx : HashMap Name USize := {}

def calcNeeds (constToIdx : HashMap Name USize) (mod : ModuleData) : Bitset :=
  mod.constants.foldl (init := 0) fun deps ci =>
    let deps := visitExpr ci.type deps
    match ci.value? with
    | some e => visitExpr e deps
    | none => deps
where
  visitExpr e arr :=
    Lean.Expr.foldConsts e arr fun c arr => match constToIdx.find? c with
      | some i => arr ||| (1 <<< i.toNat)
      | none => arr

unsafe def loadModules (imports : Array Import) : StateT State IO (Bitset × Bitset) := do
  let mut imps := 0
  let mut transImps := 0
  for imp in imports do
    let s ← get
    if let some i := s.toIdx.find? imp.module then
      imps := imps ||| (1 <<< i.toNat)
      transImps := transImps ||| s.transDeps.uget i lcProof
    else
      let mFile ← findOLean imp.module
      unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
      let (mod, _) ← readModuleData mFile
      let (deps, transDeps) ← loadModules mod.imports
      let s ← get
      let n := s.mods.size.toUSize
      let transDeps := transDeps ||| (1 <<< n.toNat)
      imps := imps ||| (1 <<< n.toNat)
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

def Edits := HashMap Name (NameSet × Bitset)

def Edits.remove (ed : Edits) (src tgt : Name) : Edits :=
  match ed.find? src with
  | none => ed.insert src (RBTree.insert ∅ tgt, 0)
  | some (a, b) => ed.insert src (a.insert tgt, b)

def Edits.add (ed : Edits) (src : Name) (tgt : Nat) : Edits :=
  match ed.find? src with
  | none => ed.insert src (∅, 1 <<< tgt)
  | some (a, b) => ed.insert src (a, b ||| (1 <<< tgt))

unsafe def visitModule (s : State) (srcSearchPath : SearchPath) (ignoreImps : Bitset)
    (i : Nat) (needs : Bitset) (edits : Edits) (downstream := true) : IO Edits := do
  -- remove transitive dependencies
  let mut deps := needs
  let mut transDeps := needs
  for i in [0:s.mods.size] do
    if deps &&& (1 <<< i) != 0 then
      let deps2 := s.transDeps[i]!
      deps := deps ^^^ (deps &&& deps2) ^^^ (1 <<< i)
      transDeps := transDeps ||| deps2
  let mut toRemove := #[]
  let mut newDeps := 0
  for imp in s.mods[i]!.imports do
    let i := s.toIdx.find! imp.module
    if transDeps &&& (1 <<< i.toNat) == 0 && ignoreImps &&& (1 <<< i.toNat) == 0 then
      toRemove := toRemove.push i
    else
      newDeps := newDeps ||| s.transDeps.uget i lcProof
  if toRemove.isEmpty then return edits
  let mut toAdd := #[]
  for i in [0:s.mods.size] do
    if deps &&& (1 <<< i) != 0 && newDeps &&& (1 <<< i) == 0 then
      toAdd := toAdd.push i
      newDeps := newDeps ||| s.transDeps.get ⟨i, lcProof⟩
  let mut edits := toRemove.foldl (init := edits) fun edits n =>
    edits.remove s.modNames[i]! s.modNames[n]!
  if let some path ← srcSearchPath.findModuleWithExt "lean" s.modNames[i]! then
    println! "{path}:"
  else
    println! "{s.modNames[i]!}:"
  println! "  remove {toRemove.map (s.modNames[·]!)}"
  if !toAdd.isEmpty then
    edits := toAdd.foldl (init := edits) fun edits n =>
      edits.add s.modNames[i]! n
    println! "  add {toAdd.map (s.modNames[·]!)}"
  if downstream then
    for r in toRemove do
      let mut toFix := 0
      for j in [0:s.mods.size] do
        if j != i && s.needs[j]! &&& (1 <<< r.toNat) != 0 && s.transDeps[j]! &&& (1 <<< i) != 0 then
          toFix := toFix ||| (1 <<< j)
      if toFix != 0 then
        let mut toFixArr := #[]
        for j in [0:s.mods.size] do
          if toFix &&& s.transDeps[j]! == 1 <<< j then
            toFixArr := toFixArr.push j
        edits := toFixArr.foldl (init := edits) fun edits n =>
          edits.add s.modNames[n]! r.toNat
        println! "  fix {s.modNames[r]!}: {toFixArr.map (s.modNames[·]!)}"
  return edits

def toBitset (s : State) (ns : List Name) : Bitset :=
  ns.foldl (init := 0) fun c name =>
    match s.toIdx.find? name with
    | some i => c ||| (1 <<< i.toNat)
    | none => c

structure Args where
  downstream : Bool := true
  fix : Bool := false
  update : Bool := false
  cfg : Option String := none
  mods : Array Name := #[]

instance {α} [FromJson α] : FromJson (NameMap α) where
  fromJson? j := do
    (← j.getObj?).foldM (init := mkNameMap _) fun m a b => do
      m.insert a.toName <$> fromJson? b
instance {α} [ToJson α] : ToJson (NameMap α) where
  toJson m := Json.obj <| m.fold (init := ∅) fun m a b =>
      m.insert compare (toString a) (toJson b)

structure ShakeCfg where
  ignoreAll? : Option (List Name) := none
  ignoreImport? : Option (List Name) := [`Init, `Lean]
  ignore? : Option (NameMap (Array Name)) := none
  deriving FromJson, ToJson

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let rec parseArgs (args : Args) : List String → Args
    | [] => args
    | "--no-downstream" :: rest => parseArgs { args with downstream := false } rest
    | "--fix" :: rest => parseArgs { args with fix := true } rest
    | "--update" :: rest => parseArgs { args with update := true } rest
    | "--cfg" :: cfg :: rest => parseArgs { args with cfg := cfg } rest
    | "--" :: rest => { args with mods := args.mods ++ rest.map (·.toName) }
    | other :: rest => parseArgs { args with mods := args.mods.push other.toName } rest
  let args := parseArgs {} args
  let srcSearchPath ← initSrcSearchPath
  let cfgFile ← if let some cfg := args.cfg then
    pure (some ⟨cfg⟩)
  else if let some path ← srcSearchPath.findModuleWithExt "lean" `Mathlib then
    pure (some (path.parent.get! / "scripts" / "noshake.json"))
  else pure none
  let cfg ← if let some file := cfgFile then
    try
      IO.ofExcept (Json.parse (← IO.FS.readFile file) >>= fromJson? (α := ShakeCfg))
    catch e =>
      println! "{e.toString}"
      pure {}
  else pure {}
  let mods := if args.mods.isEmpty then #[`Mathlib] else args.mods
  let pkg := mods[0]!.components.head!
  let mut (_, s) ← (loadModules (mods.map ({module := ·}))).run {}
  let ignoreMods := toBitset s (cfg.ignoreAll?.getD [])
  let ignoreImps := toBitset s (cfg.ignoreImport?.getD [])
  let ignore := (cfg.ignore?.getD {}).fold (init := mkHashMap) fun m a v =>
    m.insert a (toBitset s v.toList)
  let noIgnore (i : Nat) :=
    !s.mods[i]!.constNames.isEmpty && -- skip import-only mods
    ignoreMods &&& (1 <<< i) == 0 &&
    pkg.isPrefixOf s.modNames[i]!
  let needs := s.mods.mapIdx fun i mod =>
    if args.downstream || noIgnore i then
      some <| Task.spawn fun _ => calcNeeds s.constToIdx mod
    else
      none
  if args.downstream then
    s := { s with needs := needs.map (·.get!.get) }
  let mut edits : Edits := mkHashMap
  for i in [0:s.mods.size], t in needs do
    if let some t := t then
      if noIgnore i then
        let ignoreImps := ignoreImps ||| ignore.findD s.modNames[i]! 0
        edits ← visitModule s srcSearchPath ignoreImps i t.get edits args.downstream
  if args.update then
    if let some cfgFile := cfgFile then
      let mut map := cfg.ignore?.getD {}
      if !args.fix then
        map := edits.fold (init := map) fun ignore mod (remove, _) =>
          let ns := (ignore.findD mod #[]).foldl (init := remove) (·.insert ·)
          if ns.isEmpty then ignore.erase mod else ignore.insert mod (ns.toArray.qsort Name.lt)
      let cfg : ShakeCfg := {
        ignoreAll? := cfg.ignoreAll?.filter (!·.isEmpty)
        ignoreImport? := cfg.ignoreImport?.filter (!·.isEmpty)
        ignore? := (some map).filter (!·.isEmpty)
      }
      IO.FS.writeFile cfgFile <| toJson cfg |>.pretty
  if !args.fix then return
  edits.forM fun mod (remove, add) => do
    if pkg.isPrefixOf mod then
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
      let some path ← srcSearchPath.findModuleWithExt "lean" mod
        | println! "error: failed to find source file for {mod}"
      let text ← IO.FS.readFile path
      let inputCtx := Parser.mkInputContext text path.toString
      let (header, parserState, msgs) ← Parser.parseHeader inputCtx
      if !msgs.isEmpty then
        msgs.forM fun msg => msg.toString >>= IO.println
        return
      let mut pos : String.Pos := 0
      let mut out : String := ""
      for stx in header[1].getArgs do
        if remove.contains stx[2].getId then
          out := out ++ text.extract pos stx.getPos?.get!
          pos := text.findAux (· == '\n') text.endPos stx.getTailPos?.get! + ⟨1⟩
      let insertion := header.getTailPos?.getD parserState.pos
      let insertion := text.findAux (· == '\n') text.endPos insertion + ⟨1⟩
      out := out ++ text.extract pos insertion
      for mod in add do
        out := out ++ s!"import {mod}\n"
      out := out ++ text.extract insertion text.endPos
      IO.FS.writeFile path out
