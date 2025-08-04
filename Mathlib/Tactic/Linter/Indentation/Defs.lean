import Lean.Elab.Command
-- Import this linter explicitly to ensure that
-- this file has a valid copyright header and module docstring.
import Mathlib.Tactic.Linter.Header

open Lean Parser Elab Command Meta Linter

namespace Mathlib.Linter

/-- docstring TODO -/
register_option linter.indentation : Bool := {
  defValue := false
  descr := "enable the indentation linter"
}

/-- docstring TODO -/
register_option linter.indentation.debug : Bool := {
  defValue := false
}

namespace Indentation

section SyntaxTreeInfo

mutual
  /-- docstring TODO -/
  structure ChildrenInfo where
    children : Array SyntaxTreeInfo
    headTailIdxInChildren : Option (Nat × Nat)
    outIdx : Nat

  /-- docstring TODO -/
  structure ParentInfo where
    parentIdx : Nat
    idxInChildren : Nat
  deriving Inhabited

  /-- docstring TODO -/
  structure SyntaxTreeInfo where
    stx : Syntax
    idx : Nat
    childrenInfo? : Option ChildrenInfo
    parentInfo? : Option ParentInfo
  deriving Repr, Inhabited
end

/-- docstring TODO -/
inductive FlattenSyntaxTreeInfoElement
  | leaf (info : SyntaxTreeInfo) : FlattenSyntaxTreeInfoElement
  | into (info : SyntaxTreeInfo) : FlattenSyntaxTreeInfoElement
  | out (info : SyntaxTreeInfo) : FlattenSyntaxTreeInfoElement

/-- docstring TODO -/
abbrev FlattenSyntaxTreeInfo := Array FlattenSyntaxTreeInfoElement

/-- docstring TODO -/
def FlattenSyntaxTreeInfoElement.info : FlattenSyntaxTreeInfoElement → SyntaxTreeInfo
  | leaf info
  | into info
  | out info => info

/-- docstring TODO -/
def SyntaxTreeInfo.children? (treeInfo : SyntaxTreeInfo) : Option (Array SyntaxTreeInfo) :=
  treeInfo.childrenInfo?.map (·.children)

/-- docstring TODO -/
def SyntaxTreeInfo.getInfo? (treeInfo : SyntaxTreeInfo) : Option SourceInfo :=
  treeInfo.stx.getInfo?

/-- docstring TODO -/
def SyntaxTreeInfo.getPos? (treeInfo : SyntaxTreeInfo) : Option String.Pos :=
  treeInfo.getInfo?.map (·.getPos?) |>.getD .none

/-- docstring TODO -/
def SyntaxTreeInfo.getTailPos? (treeInfo : SyntaxTreeInfo) : Option String.Pos :=
  treeInfo.getInfo?.map (·.getTailPos?) |>.getD .none

def SyntaxTreeInfo.getSubstring? (src : String) (treeInfo : SyntaxTreeInfo) : Option Substring :=
  treeInfo.getPos?.map (⟨src, ·, treeInfo.getTailPos?.get!⟩)

/-- docstringTODO -/
def SyntaxTreeInfo.headTailOfChildren (children : Array SyntaxTreeInfo) :
    Option (Nat × Nat) :=
  children.findIdx? (·.getPos?.isSome) |>.map
    fun headIdx ↦
      (headIdx,
        -- a workaround for not-yet-existing `Array.findRevIdx?`.
        children.findRev? (·.getPos?.isSome) |>.map (·.parentInfo?.get!.idxInChildren) |>.get!)

/-- docstring TODO -/
def SyntaxTreeInfo.ofSyntaxAux (stx : Syntax) (flatten : FlattenSyntaxTreeInfo) (nextLinterIdx : Nat)
    (parentInfo : Option ParentInfo) :
    SyntaxTreeInfo × FlattenSyntaxTreeInfo × Nat :=
  match stx with
  | .atom s ..
  | .ident s .. =>
    assert! match s with | .original .. => true | _ => false
    let leaf : SyntaxTreeInfo :=
      { stx := stx, idx := nextLinterIdx, childrenInfo? := .none, parentInfo? := parentInfo}
    (leaf, flatten.push (.leaf leaf), nextLinterIdx + 1)
  | .node _ kind args =>
    let intoIdx := nextLinterIdx
    let flatten := flatten.push (.into default)
    let ⟨children, flatten, outIdx, _⟩ : _ × _ × _ × ParentInfo :=
      args.foldl
        (fun (arr, flatten, idx, parentInfo) stx ↦
          let ⟨treeInfo, flatten, idx⟩ := SyntaxTreeInfo.ofSyntaxAux stx flatten idx parentInfo
          ⟨arr.push treeInfo, flatten, idx,
            { parentInfo with idxInChildren := parentInfo.idxInChildren + 1}⟩)
        (#[], flatten, intoIdx + 1, { parentIdx := intoIdx, idxInChildren := 0})
    let headTail := SyntaxTreeInfo.headTailOfChildren children
    let info := (headTail.map · |>.getD SourceInfo.none) <| fun ⟨h, t⟩ ↦
      SourceInfo.synthetic (children[h]!.getPos?.get!) (children[t]!.getTailPos?.get!)
    let stx : Syntax := .node info kind <| children.map (·.stx)
    let childrenInfo : ChildrenInfo :=
      { children := children, outIdx := outIdx, headTailIdxInChildren := headTail}
    let node : SyntaxTreeInfo :=
      { stx := stx, idx := intoIdx, childrenInfo? := childrenInfo, parentInfo? := parentInfo }
    let flatten := (flatten.set! intoIdx <| .into node).push <| .out node
    (node, flatten, outIdx + 1)
  | .missing => -- It should not happen?
    let childrenInfo : ChildrenInfo:=
      { children := #[], outIdx := nextLinterIdx + 1, headTailIdxInChildren := .none }
    let node :=
      { stx := stx, idx := nextLinterIdx, childrenInfo? := childrenInfo, parentInfo? := parentInfo }
    (node, flatten.push (.into node) |>.push (.out node), nextLinterIdx + 2)

/-- docstring TODO -/
def SyntaxTreeInfo.ofSyntax (stx : Syntax) : SyntaxTreeInfo × FlattenSyntaxTreeInfo :=
  let ⟨treeInfo, flatten, _⟩ := SyntaxTreeInfo.ofSyntaxAux stx.updateLeading #[] 0 .none
  ⟨treeInfo, flatten⟩

/-- docstring TODO -/
def indentationOfPos (str : String) (pos : String.Pos) : Option Nat :=
  let beforePos : Substring := ⟨str, str.findLineStart pos, pos⟩
  if beforePos.all (· == ' ') then .some beforePos.bsize else .none

/-- docstring TODO -/
def indentationBeforePos (str : String) (pos : String.Pos) : Nat :=
  let beforePos : Substring := ⟨str, str.findLineStart pos, pos⟩
  beforePos.takeWhile (· == ' ') |>.bsize

def SyntaxTreeInfo.getIndentation? (treeInfo : SyntaxTreeInfo) (src : String) : Option Nat := do
  treeInfo.getPos?.map (indentationOfPos src ·) |>.getD .none

def isInCategories {m} [Monad m] [MonadEnv m] (stx : Syntax) : m Bool := do
  for ⟨_, cat⟩ in (parserExtension.getState (← getEnv)).categories do
    if cat.kinds.contains stx.getKind then
      return true
  return false

def SyntaxTreeInfo.needUpdatingIndentation {m} [Monad m] [MonadEnv m]
    (treeInfo : SyntaxTreeInfo) : m Bool :=
  isInCategories treeInfo.stx

#eval do assert! (← SyntaxTreeInfo.needUpdatingIndentation
  { (default : SyntaxTreeInfo) with stx := .node .none ``declaration #[]})

end SyntaxTreeInfo

section IndentationLinter

/-- docstring TODO -/
structure Limitation where
  src : String
  indentation : Nat := 0
  additionalIndentation : Nat := 0
  oneAdditionalIndentation := 2
  isExactIndentation : Bool
  atMost : Option Nat := .none
  flatten : FlattenSyntaxTreeInfo

structure IndentationError where
  msg : MessageData
  stx : Syntax

inductive Result
  | nextLinter (limit : Limitation)
  | finished
deriving Inhabited

abbrev LinterM := ExceptT IndentationError CommandElabM

/-- docstring TODO -/
def throwIndentationError (stx : Syntax) (msg : MessageData) (limit : Limitation)
    (range : Option String.Range := stx.getPos?.map fun p => ⟨limit.src.findLineStart p, p⟩) :
    LinterM Unit :=
  let stx :=
    match range with
    | .some range => stx.setInfo <| .synthetic range.start range.stop
    | _ => stx
  throwThe IndentationError { msg := msg, stx := stx }

/-- docstring TODO -/
abbrev IndentationLinter :=
  (treeInfo : SyntaxTreeInfo) → (limit : Limitation) → LinterM Result

instance : AndThen IndentationLinter where
  andThen (a b info limit) := do
    match (← a info limit) with
      | .finished => pure .finished
      | .nextLinter newLimit => b ⟨⟩ info newLimit

def finishedLinter : IndentationLinter := fun _ _ ↦ pure .finished

end IndentationLinter

section Meta

structure IndentationLinters where
  nodeLinters : NameMap IndentationLinter := ∅
  identLinters : NameMap IndentationLinter := ∅
  atomLinters : Std.HashMap String IndentationLinter := ∅
  linters : Array (Nat × IndentationLinter) := ∅
deriving Inhabited

instance : EmptyCollection IndentationLinters := ⟨{}⟩

/--
`O(|xs| + |ys|)`. Merge arrays `xs` and `ys`. If the arrays are sorted according to `lt`, then the
result is sorted as well. If two (or more) elements are equal according to `lt`, they are preserved.

From module `Batteries.Data.Array.Merge`.
-/
def Array.merge {α} (lt : α → α → Bool) (xs ys : Array α) : Array α :=
  go (Array.mkEmpty (xs.size + ys.size)) 0 0
where
  /-- Auxiliary definition for `merge`. -/
  go (acc : Array α) (i j : Nat) : Array α :=
    if hi : i ≥ xs.size then
      acc ++ ys[j:]
    else if hj : j ≥ ys.size then
      acc ++ xs[i:]
    else
      let x := xs[i]
      let y := ys[j]
      if lt x y then go (acc.push x) (i + 1) j else go (acc.push y) i (j + 1)
  termination_by xs.size + ys.size - (i + j)

def IndentationLinters.add (linters : IndentationLinters) (addedLinters : IndentationLinters) :
    IndentationLinters where
  nodeLinters := linters.nodeLinters.mergeBy (fun _ _ added => added) addedLinters.nodeLinters
  identLinters := linters.identLinters.mergeBy (fun _ _ added => added) addedLinters.identLinters
  atomLinters := linters.atomLinters.insertMany addedLinters.atomLinters
  linters := Array.merge (·.1 > ·.1) linters.linters <| addedLinters.linters.qsort (·.1 > ·.1)

-- use `finishedLinter` as bottom to avoid panic when trying to check in the file where the first
-- actual linter in `linters` hasn't been added
initialize indentationLinterRef : IO.Ref IndentationLinters ←
  IO.mkRef { linters := #[(0, finishedLinter)] }

def addIndentationLinters (linter : IndentationLinters) (ref := indentationLinterRef) : IO Unit :=
  ref.modify (·.add linter)

def runLinterOn (ref := indentationLinterRef) : IndentationLinter :=
  fun info limit ↦ do
    let linters ← ref.get
    let result ← match info.stx with
      | .node (kind := kind) .. => linters.nodeLinters.find? kind |>.mapM (· info limit)
      | .atom (val := val) .. => linters.atomLinters.get? val |>.mapM (· info limit)
      | .ident (val := val) .. => linters.identLinters.find? val |>.mapM (· info limit)
      | _ => pure .none
    let mut result := result.getD <| .nextLinter limit
    for (_, i) in linters.linters do
      match result with
      | .finished => return result
      | .nextLinter newLimit =>
        result ← i info newLimit
    pure result

abbrev ensure (treeInfo : SyntaxTreeInfo) (limit : Limitation)
    (linter : IndentationLinter := runLinterOn) : LinterM Unit := do
  match ← linter treeInfo limit with
  | .finished => pure ()
  | .nextLinter .. => panic! "Next linter is missing here! Please report this."

end Meta

@[inherit_doc Mathlib.Linter.linter.indentation]
partial def indentationLinter : Linter where run := withSetOptionIn fun stx => do
  unless getLinterValue Mathlib.Linter.linter.indentation (← getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  let debug := getLinterValue Mathlib.Linter.linter.indentation.debug (← getLinterOptions)
  if debug then
    IO.println (repr stx)
  let ⟨treeInfo, flatten⟩ := SyntaxTreeInfo.ofSyntax stx
  let .some initialPos := treeInfo.getPos? | return
  let src := (← getFileMap).source
  let result ← ensure treeInfo {
      src := src,
      indentation := 0,
      additionalIndentation := 0,
      isExactIndentation := false,
      atMost := .some 0,
      flatten := flatten }
  if let .error e := result then
    logLint Mathlib.Linter.linter.indentation e.stx e.msg

initialize addLinter indentationLinter

end Indentation

end Mathlib.Linter
