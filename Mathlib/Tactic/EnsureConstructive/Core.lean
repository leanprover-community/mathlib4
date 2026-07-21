/-
Copyright (c) 2026 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
module

public import Lean.Meta.Basic
public import Lean.Elab.Term.TermElabM
import Mathlib.Init

/-!
# Core functionality of `ensure_constructive`
-/
namespace Mathlib.Tactic.EnsureConstructive

open Lean Meta

public def constructiveAxioms := #[``propext, ``Quot.sound]

structure Path where
  /-- Most recent/deeply-nested `decl` is outermost. -/
  nesting : List Name

def Path.currentConst (p : Path) := p.nesting.headD .anonymous

def Path.pop (p : Path) : Path where
  nesting := p.nesting.drop 1

def Path.push (p : Path) (const : Name) : Path where
  nesting := const :: p.nesting

structure ViolationKind where
  isAxiom : Bool := false
  isOpaque : Bool := false
deriving Ord, Repr, Inhabited

deriving instance Repr for Lean.NameSet

structure Violation extends ViolationKind where
  prev : NameSet := ∅
  next : NameSet := ∅
deriving Repr, Inhabited

structure Violations where
  map : NameMap Violation := {}

@[inline] def Violations.isEmpty (vs : Violations) : Bool := vs.map.isEmpty

partial def Violations.erase (vs : Violations) (toErase : NameSet) : Violations := Id.run do
  let mut toErase := toErase
  let mut newErase := false
  for (c, v) in vs.map do
    unless toErase.contains c do
      if
        (!v.prev.isEmpty && v.prev.all toErase.contains)
        || (!v.isAxiom && !v.isOpaque && !v.next.isEmpty && v.next.all toErase.contains)
     then
        toErase  := toErase.insert c
        newErase := true
  if newErase then erase vs toErase else
    letI map := vs.map.eraseMany toErase
    letI map := map.map fun _ v => { v with
      prev := v.prev.eraseMany toErase
      next := v.next.eraseMany toErase }
    return { vs with map := map }

def Violation.insertRawNext (v : Violation) (nextName : Name) : Violation :=
  { v with next := v.next.insert nextName }

def Violation.insertRawPrev (v : Violation) (nextName : Name) : Violation :=
  { v with prev := v.prev.insert nextName }

/-- Insert an axiom if not yet present. -/
def Violations.insertRawAxiom (vs : Violations) (ax : Name) : Violations :=
  { vs with map := vs.map.alter ax fun a? => a?.getD { isAxiom := true }}

def Violations.insertRawOpaque (vs : Violations) (ax : Name) : Violations :=
  { vs with map := vs.map.alter ax fun a? => a?.getD { isOpaque := true }}

inductive PrettyTree where
| node (n : Name) (children : Array PrettyTree)
| opaque (n : Name)
| axiom (n : Name)
| repeatedNode (n : Name)
deriving Inhabited

def _root_.Lean.MessageData.join (msgs : Array MessageData) : MessageData :=
  msgs.foldl (init := .nil) (m!"{·}{·}")

partial def PrettyTree.prettyAux (bars : String) : PrettyTree → MessageData
  | .node n ch => Id.run do
    let some last := ch.back? | m!"{.ofConstName n} {Lean.bombEmoji}"
    let ch := ch.pop
    m!"{.ofConstName n}\
    {.join <| ch.map (m!"\n{bars}├{prettyAux s!"{bars}│" ·}")}\n\
    {bars}└{prettyAux s!"{bars} " last}"
  | .opaque n => m!"{.ofConstName n} {Lean.crossEmoji} (opaque)"
  | .axiom n  => m!"{.ofConstName n} {Lean.crossEmoji} (axiom)"
  | .repeatedNode n => m!"{.ofConstName n}\n{bars}└(⋯)"

instance : ToMessageData PrettyTree where
  toMessageData t := t.prettyAux ""

partial def Violations.toPrettyTreeAux (vs : Violations) (current : Name) :
    StateM NameSet PrettyTree := do
  let { next, isAxiom, isOpaque, .. } := vs.map.get! current
  if isAxiom  then return .axiom current
  if isOpaque then return .opaque current
  if (← get).contains current then return .repeatedNode current
  modify fun s => s.insert current
  let mut ch := #[]
  for n in next do
    ch := ch.push (← vs.toPrettyTreeAux n)
  return .node current ch

def Violations.toPrettyTree (vs : Violations) (root : Name) : PrettyTree :=
  vs.toPrettyTreeAux root |>.run' {}

def Violations.prettyPaths (vs : Violations) (root : Name) : MessageData :=
  m!"{vs.toPrettyTree root}"

/-- Assumes `next` is already in `vs` if specified. -/
def Violations.addPath (vs : Violations) (nesting : List Name) (next? : Option Name := none) :
    Violations :=
  match nesting with
  | [] => vs
  | current :: nesting =>
    -- TODO: seems linear, but is it?
    let (hasCurrent, map) := vs.map.containsThenInsertIfNew current {}
    let vs :=
      letI map :=
        if let some next := next? then
          letI map := map.modify current (·.insertRawNext next)
          map.modify next (·.insertRawPrev current)
        else
          map
      { vs with map }
    if hasCurrent then vs else addPath vs nesting current

structure State extends Path, Violations where
  -- TODO: might be more performant to record violations per expr.
  --  visited : ExprMap (Option NameSet) := ∅
  visitedConsts : NameHashSet := {}
  allowedAxioms : Array Name := constructiveAxioms

abbrev VisitM := StateT State MetaM

namespace Perf

structure PerfState where
  -- TODO: unsafe
  visited : ExprSet := ∅
  visitedConsts : NameHashSet := {}

abbrev VisitM := ReaderT (Array Name) <| StateT PerfState MetaM

partial def visit (e : Expr) : Perf.VisitM Bool := do
  if (← get).visited.contains e then
    return true
  -- Don't visit proofs or types
  if ← (isProof e <||> Meta.isType e) then
    return true
  match e with
  | .forallE n d b bi  =>
    withLocalDecl n bi d fun x =>
      visit (b.instantiate1 x)
  | .lam n d b bi      =>
    withLocalDecl n bi d fun x =>
      visit (b.instantiate1 x)
  | .mdata _ b         => visit b
  | .letE n t v b nondep =>
    visit v <&&> withLetDecl n t v (nondep := nondep) fun x =>
      visit (b.instantiate1 x)
  | .app f a           => visit f <&&> visit a
  | .proj _ _ b        => visit b
  | .const next _      =>
    if (← get).visitedConsts.contains next then
      return true
    else
      modify fun s => { s with visitedConsts := s.visitedConsts.insert next }
      if (← read).contains next then
        return true
      onConst next
  | .sort _
  | .lit _  => return true
  | .fvar _ => return true -- Allow free variables from `withLocalDecl` and `variable`
  | b@(.bvar _) => throwError "Unexpected bound variable {b}"
  | m@(.mvar _) => throwError "Unexpected metavariable {m}"
where
  onConst n := do
    match ← getConstInfo n with
    | .axiomInfo _
    | .opaqueInfo _ => return false
    | .defnInfo d => visit d.value
    | .thmInfo _
    | .quotInfo _
    | .inductInfo _
    | .ctorInfo _
    | .recInfo _ => return true

end Perf

public def isConstructiveExpr (e : Expr) (allowedConstants := constructiveAxioms) : MetaM Bool := do
  unless !(← getEnv).header.isModule do
    throwError "Constructivity can only be determined in a non-module file."
  Perf.visit e allowedConstants |>.run' {}

public def isConstructive (n : Name) (allowedConstants := constructiveAxioms) : MetaM Bool := do
  unless !(← getEnv).header.isModule do
    throwError "Constructivity can only be determined in a non-module file."
  Perf.visit.onConst n allowedConstants |>.run' {}

-- TODO: change to fold over all violations in arbitrary monad, record violations there?
partial def visit (e : Expr) : VisitM Unit := do
  -- TODO: need to keep track of each *expr's* violations-with-paths...or else give up the
  -- performance boost.
  -- if (← get).visited.contains e then
  --   return
  -- Don't visit proofs or types
  if ← (isProof e <||> Meta.isType e) then
    return
  match e with
  | .forallE n d b bi  =>
    -- let r ← visit d acc -- Don't visit the type
    withLocalDecl n bi d fun x =>
      visit (b.instantiate1 x)
  | .lam n d b bi      =>
    -- let r ← visit d acc -- Don't visit the type
    withLocalDecl n bi d fun x =>
      visit (b.instantiate1 x)
  | .mdata _ b         => visit b
  | .letE n t v b nondep    =>
    -- let r₁ ← visit t acc -- Don't visit the type
    visit v
    withLetDecl n t v (nondep := nondep) fun x =>
      visit (b.instantiate1 x)
  | .app f a           =>
    visit f
    visit a
  | .proj _ _ b        => visit b
  | .const next _      =>
    if (← get).visitedConsts.contains next then
      trace[EnsureConstructive] "{.ofConstName next} [re-encountered]"
      -- if this constant has led to a violation before, but not from the ambient constant, record
      if let some v := (← get).map.get? next then
        let current := (← get).currentConst
        unless v.prev.contains current do
          modify fun s => { s with toViolations := s.toViolations.addPath s.nesting next }
      return
    else
      trace[EnsureConstructive] "{.ofConstName next}"
      modify fun s => { s with visitedConsts := s.visitedConsts.insert next }
      match ← getConstInfo next with
      | .thmInfo _ =>
        trace[EnsureConstructive] "Allowed theorem"
        return
      | info@(.axiomInfo _)
      | info@(.opaqueInfo _) =>
        if info.isAxiom then
          if (← get).allowedAxioms.contains next then
            trace[EnsureConstructive] "Allowed axiom"
            return
          else
            trace[EnsureConstructive] "Violation (axiom)"
            modify fun s => { s with toViolations := s.toViolations.insertRawAxiom next }
        else
          trace[EnsureConstructive] "Violation (opaque)"
          modify fun s => { s with toViolations := s.toViolations.insertRawOpaque next }
        let current := (← get).currentConst
        let some violation := (← get).map.get? next
          | unreachable!
        unless violation.prev.contains current do
          modify fun s => { s with toViolations := s.toViolations.addPath s.nesting next }
      | .defnInfo d =>
        trace[EnsureConstructive] "Inspecting... ({d.value})"
        modify fun s => { s with toPath := s.toPath.push next }
        visit d.value
        modify fun s => { s with toPath := s.toPath.pop }
        trace[EnsureConstructive] "{.ofConstName next} finished"
      | .quotInfo _
      | .inductInfo _
      | .ctorInfo _
      | .recInfo _ => return
  | .sort _
  | .lit _  => return
  | .fvar _ => return -- Allow free variables from `variable`
  | b@(.bvar _) => throwError "Unexpected bound variable {b}"
  | m@(.mvar _) => throwError "Unexpected metavariable {m}"
  -- modify fun s => { s with visited := s.visited.insert e }

open Elab Term in
public def ensureConstructiveVerbose (id : Ident) (ignoring : Array Ident) (verbose := true) :
    TermElabM Bool := do
  unless !(← getEnv).header.isModule do
    throwError "Constructivity can only be determined in a non-module file."
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let ignoring ← ignoring.mapM fun id => return (id, ← realizeGlobalConstNoOverloadWithInfo id)
  if let some (self, _) := ignoring.find? (·.2 = n) then
    if verbose then
      logWarningAt self m!"The challenged `{.ofConstName n}` is explicitly allowed to be
        nonconstructive, so is trivially constructive"
    return true
  match ← getConstInfo n with
  | .defnInfo { value .. } => do
    let (_, { toViolations := vs, .. }) ← (visit (← instantiateMVars value)).run { nesting := [n] }
    for (id, ignored) in ignoring do
      unless vs.map.contains ignored do
        logWarningAt id m!"`{.ofConstName ignored}` does not produce a violation in \
          `{.ofConstName n}`, and may be removed."
    let remaining := vs.erase (.ofArray <| ignoring.map (·.2))
    unless remaining.isEmpty do
      let terminal := remaining.map.filterMap fun _ v => do
        guard v.next.isEmpty
        return v.toViolationKind
      let terminal := terminal.toArray.qsort (compare ·.2 ·.2 |>.isLT) |>.map fun (a, b) =>
        if b.isAxiom then
          m!"• `{MessageData.ofConstName a}` (axiom)"
        else if b.isOpaque then
          m!"• `{MessageData.ofConstName a}` (opaque)"
        else m!"• `{MessageData.ofConstName a}` (?)"
      logErrorAt id m!"`{.ofConstName n}` is not constructive. It depends on\n\n\
        {m!"\n".joinSep terminal.toList}\n\n\
        via the following paths:\n\
        {remaining.prettyPaths n}"
    return remaining.isEmpty
  | .thmInfo _ =>
    if verbose then
      logWarning m!"`{.ofConstName n}` is a theorem, and thus automatically constructive in Lean."
    return true
  | .axiomInfo { type .. } => do
    if constructiveAxioms.contains n || ignoring.any (·.2 = n) then
      return true
    else if ← Meta.isProp type then
      if verbose then
        logWarning m!"`{.ofConstName n}` is a proof, and thus automatically constructive in Lean."
      return true
    else
      if verbose then
        logError m!"`{.ofConstName n}` is an axiom, and so not constructive."
      return false
  | .opaqueInfo { type .. } => do
    if ← Meta.isProp type then
      if verbose then
        logWarning m!"`{.ofConstName n}` is a proof, and thus automatically constructive in Lean."
      return true
    else
      if verbose then
        logError m!"`{.ofConstName n}` is opaque, and so not constructive."
      return false
  | _ => return true

initialize registerTraceClass `EnsureConstructive

end Mathlib.Tactic.EnsureConstructive
