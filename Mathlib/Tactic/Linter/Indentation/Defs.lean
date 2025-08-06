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
initialize registerTraceClass `Indentation
initialize registerTraceClass `Indentation.run

namespace Indentation

section SyntaxTreeInfo

mutual
  structure ChildrenHeadTail where
    head : SyntaxTreeInfo
    headToken : SyntaxTreeInfo
    tail : SyntaxTreeInfo
    tailToken : SyntaxTreeInfo

  /-- docstring TODO -/
  structure ChildrenInfo where
    children : Array SyntaxTreeInfo
    headTail? : Option ChildrenHeadTail
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
    prevTokenIdx? : Option Nat
    nextTokenIdx? : Option Nat
  deriving Inhabited
end

/-- docstring TODO -/
inductive FlattenSyntaxTreeInfoElement
  | leaf (info : SyntaxTreeInfo) : FlattenSyntaxTreeInfoElement
  | into (info : SyntaxTreeInfo) : FlattenSyntaxTreeInfoElement
  | out (info : SyntaxTreeInfo) : FlattenSyntaxTreeInfoElement
deriving Inhabited

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

def SyntaxTreeInfo.isToken (treeInfo : SyntaxTreeInfo) : Bool := treeInfo.childrenInfo?.isNone

def SyntaxTreeInfo.headToken? (treeInfo : SyntaxTreeInfo) : Option SyntaxTreeInfo :=
  match treeInfo.childrenInfo? with
  | .none => treeInfo
  | .some { headTail? := .some { headToken := headToken, .. }, .. } => headToken
  | _ => .none

def SyntaxTreeInfo.headTokenIdx? (treeInfo : SyntaxTreeInfo) : Option Nat :=
  treeInfo.headToken?.map (·.idx)

def SyntaxTreeInfo.tailToken? (treeInfo : SyntaxTreeInfo) : Option SyntaxTreeInfo :=
  match treeInfo.childrenInfo? with
  | .none => treeInfo
  | .some { headTail? := .some { tailToken := tailToken, .. }, .. } => tailToken
  | _ => .none

def SyntaxTreeInfo.tailTokenIdx? (treeInfo : SyntaxTreeInfo) : Option Nat :=
  treeInfo.tailToken?.map (·.idx)

def FlattenSyntaxTreeInfoElement.nextTokenIdx? : FlattenSyntaxTreeInfoElement → Option Nat
  | .out i
  | .leaf i => i.nextTokenIdx?
  | .into i => i.headTokenIdx? <|> i.nextTokenIdx?

class ForInTokens where
  subarray : Subarray FlattenSyntaxTreeInfoElement

def forInTokens (subarray : Subarray FlattenSyntaxTreeInfoElement) : ForInTokens := ⟨subarray⟩

def FlattenSyntaxTreeInfo.forInTokens (array : FlattenSyntaxTreeInfo) : ForInTokens :=
  ⟨array.toSubarray⟩

partial instance {m} : ForIn m ForInTokens FlattenSyntaxTreeInfoElement where
  forIn {β} [Monad m] subarray (init : β) f : m β := do
    let subarray := subarray.subarray
    let start := subarray.start
    let stop := subarray.stop
    let array := subarray.array
    let .some start_ := array[start]? | return init
    let .some start := if start_.info.isToken then .some start else start_.nextTokenIdx? |
      return init
    let rec @[specialize] loop (i : Nat) (state : β) : m β := do
      if i >= stop then return state
      let i := array[i]!
      match (← f i state) with
      | ForInStep.yield state =>
        match i.nextTokenIdx? with
        | .some next => loop next state
        | .none => pure state
      | ForInStep.done state => pure state
    loop start init

def ChildrenHeadTail.getInfo (headTail : ChildrenHeadTail) : SourceInfo :=
  .synthetic headTail.head.stx.getPos?.get! headTail.tail.stx.getTailPos?.get!

def ChildrenHeadTail.getHeadIdxInChildren (headTail : ChildrenHeadTail) : Nat :=
  headTail.head.parentInfo?.get!.idxInChildren

def ChildrenHeadTail.getTailIdxInChildren (headTail : ChildrenHeadTail) : Nat :=
  headTail.tail.parentInfo?.get!.idxInChildren

def SyntaxTreeInfo.hasToken (treeInfo : SyntaxTreeInfo) : Bool :=
  treeInfo.isToken || treeInfo.childrenInfo?.elim false (·.headTail?.isSome)

/-- docstring TODO -/
def SyntaxTreeInfo.getInfo? (treeInfo : SyntaxTreeInfo) : Option SourceInfo :=
  if treeInfo.isToken then
    treeInfo.stx.getInfo?
  else
    (·.getInfo) <$> (treeInfo.childrenInfo? >>= (·.headTail?))

/-- docstring TODO -/
def SyntaxTreeInfo.getPos? (treeInfo : SyntaxTreeInfo) : Option String.Pos :=
  treeInfo.getInfo?.map (·.getPos?.get!)

/-- docstring TODO -/
def SyntaxTreeInfo.getTailPos? (treeInfo : SyntaxTreeInfo) : Option String.Pos :=
  treeInfo.getInfo?.map (·.getTailPos?.get!)

def SyntaxTreeInfo.getSrc? (treeInfo : SyntaxTreeInfo) : Option String :=
  treeInfo.headToken?.map (·.stx.getInfo?.get!.getTrailing?.get!.str)

def SyntaxTreeInfo.getSubstring? (treeInfo : SyntaxTreeInfo) : Option Substring :=
  treeInfo.getPos?.map (⟨treeInfo.getSrc?.get!, ·, treeInfo.getTailPos?.get!⟩)

/-- docstringTODO -/
def SyntaxTreeInfo.headTailOfChildren (children : Array SyntaxTreeInfo) :
    Option (Nat × Nat) :=
  children.findIdx? (·.getPos?.isSome) |>.map
    fun headIdx ↦
      (headIdx,
        -- a workaround for not-yet-existing `Array.findRevIdx?`.
        children.findRev? (·.getPos?.isSome) |>.map (·.parentInfo?.get!.idxInChildren) |>.get!)

/-- docstring TODO -/
partial def SyntaxTreeInfo.ofSyntaxAux (stx : Syntax) (parentInfo : Option ParentInfo) :
    StateM (FlattenSyntaxTreeInfo × Option Nat) SyntaxTreeInfo := do
  let idx := (← get).fst.size
  let newTreeInfo : SyntaxTreeInfo :=
    { stx := stx, idx := idx, nextTokenIdx? := .none, prevTokenIdx? := (← get).snd,
      parentInfo? := parentInfo,
      childrenInfo? := .none /- to be updated in node -/ }
  match stx with
  | .atom s ..
  | .ident s .. =>
    assert! match s with | .original .. => true | _ => false
    modify <| (·.fst.push (.leaf newTreeInfo), Option.some idx)
    pure newTreeInfo
  | .node _ _ args =>
    modify <| Prod.map (·.push (.into default)) id
    let children ←
      args.mapIdxM
        (Option.some { parentIdx := idx, idxInChildren := · } |> SyntaxTreeInfo.ofSyntaxAux ·)
    let headTail? : Option ChildrenHeadTail :=
      match children.find? (·.hasToken) |>.map (·, children.findRev? (·.hasToken) |>.get!) with
      | .some (head, tail) => .some <|
        { head := head, headToken := head.headToken?.get!,
          tail := tail, tailToken := tail.tailToken?.get! }
      | .none => .none
    let childrenInfo : ChildrenInfo :=
      { children := children, outIdx := (← get).fst.size, headTail? := headTail? }
    let node : SyntaxTreeInfo := { newTreeInfo with childrenInfo? := childrenInfo }
    modify <| Prod.map (·.set! idx (.into node) |>.push (.out node)) id
    pure node
  | .missing => -- It should not happen?
    let idx := (← get).fst.size
    let childrenInfo : ChildrenInfo := { children := #[], outIdx := idx + 1, headTail? := .none }
    let pseudoNode : SyntaxTreeInfo := { newTreeInfo with childrenInfo? := childrenInfo }
    modify <| Prod.map (·.push (.into pseudoNode) |>.push (.out pseudoNode)) id
    pure pseudoNode

/-- docstring TODO -/
partial def SyntaxTreeInfo.updateNextTokenIdx (treeInfo : SyntaxTreeInfo) :
    StateM (FlattenSyntaxTreeInfo × Option Nat) SyntaxTreeInfo := do
  let treeInfo := { treeInfo with nextTokenIdx? := (← get).snd }
  match treeInfo with
  | { childrenInfo? := .none, .. } =>
    modify <| Prod.map (·.set! treeInfo.idx (.leaf treeInfo)) id
    pure treeInfo
  | { childrenInfo? := .some childrenInfo@{ outIdx := outIdx, ..}, idx := idx, .. } =>
    -- it could be more directly and effectly if there were `Array.mapRevM`
    let children :=
      (← childrenInfo.children.reverse.mapM (SyntaxTreeInfo.updateNextTokenIdx ·)).reverse
    let flatten := (← get).fst
    let headTail? : Option ChildrenHeadTail := childrenInfo.headTail?.map fun x => {
      head := flatten[x.head.idx]!.info,
      headToken := flatten[x.headToken.idx]!.info,
      tail := flatten[x.tail.idx]!.info,
      tailToken := flatten[x.tailToken.idx]!.info
    }
    let childrenInfo : ChildrenInfo :=
      { childrenInfo with children := children, headTail? := headTail? }
    let treeInfo := { treeInfo with childrenInfo? := .some childrenInfo }
    modify <| Prod.map (·.set! idx (.into treeInfo) |>.set! outIdx (.out treeInfo)) id
    pure treeInfo

/-- docstring TODO -/
def SyntaxTreeInfo.ofSyntax (stx : Syntax) : SyntaxTreeInfo × FlattenSyntaxTreeInfo :=
  let go := SyntaxTreeInfo.ofSyntaxAux stx.updateLeading none >>= SyntaxTreeInfo.updateNextTokenIdx
  let ⟨info, flatten, _⟩ := go.run (#[], .none)
  (info, flatten)

/-- docstring TODO -/
def indentationOfPos (str : String) (pos : String.Pos) : Option Nat :=
  let beforePos : Substring := ⟨str, str.findLineStart pos, pos⟩
  if beforePos.all (· == ' ') then .some beforePos.bsize else .none

/-- docstring TODO -/
def indentationBeforePos (str : String) (pos : String.Pos) : Nat :=
  let beforePos : Substring := ⟨str, str.findLineStart pos, pos⟩
  beforePos.takeWhile (· == ' ') |>.bsize

def SyntaxTreeInfo.getIndentation? (treeInfo : SyntaxTreeInfo) : Option Nat :=
  treeInfo.getPos?.bind (indentationOfPos treeInfo.getSrc?.get! ·)

def categoriesContain {m} [Monad m] [MonadEnv m] (stx : Syntax) : m Bool := do
  for ⟨_, cat⟩ in (parserExtension.getState (← getEnv)).categories do
    if cat.kinds.contains stx.getKind then
      return true
  return false

def SyntaxTreeInfo.needUpdatingIndentation {m} [Monad m] [MonadEnv m]
    (treeInfo : SyntaxTreeInfo) : m Bool :=
  categoriesContain treeInfo.stx

instance : ToString ChildrenHeadTail where
  toString x := s!"({x.head.idx} → {x.headToken.idx}) : ({x.tail.idx} → {x.tailToken.idx}))"

instance : ToString ParentInfo where
  toString x := s!"({x.parentIdx}.{x.idxInChildren})"

open MessageData in
partial instance : ToMessageData SyntaxTreeInfo where
  toMessageData i := go i 0
where
  go (i : SyntaxTreeInfo) (n : Nat) : Id MessageData := do
    let indentation := toMessageData <| "".pushn ' ' (2 * n)
    let name := match i.stx with
      | .node _ kind _ => MessageData.ofConstName kind
      | .ident _ _ v _ => m!"{i.stx.getKind} {ofConstName v}"
      | .atom _ v => m!"{i.stx.getKind} {repr v}"
      | .missing => m!"{i.stx.getKind}"
    let parent := i.parentInfo?.elim "" fun p => s!"({p})"
    let mut msg := m!"{indentation}\{{i.idx}: {name} {parent}"
    if let .some childrenInfo := i.childrenInfo? then
      msg := msg ++ m!"\n{indentation} ["
      if let some headTail := childrenInfo.headTail? then
        msg := msg ++ m!" {headTail}"
      for c in childrenInfo.children do
        msg := msg ++ m!"\n{← go c (n+1)}"
      msg := msg ++ m!"]"
    msg := msg ++ m!"}"
    pure msg

end SyntaxTreeInfo

section IndentationLinter

/-- docstring TODO -/
structure Limitation where
  indentation : Nat := 0
  additionalIndentation : Nat := 0
  oneAdditionalIndentation := 2
  isExactIndentation : Bool := false
  atMost : Option Nat := .none
deriving Repr

structure IndentationError where
  msg : MessageData
  stx : Syntax

inductive Result
  | nextLinter (limit : Limitation)
  | finished
deriving Inhabited

abbrev LinterM := ReaderT (FlattenSyntaxTreeInfo × String) <| ExceptT IndentationError CommandElabM

def getFlatten : LinterM FlattenSyntaxTreeInfo := Prod.fst <$> read

def getSrc : LinterM String := Prod.snd <$> read

/-- docstring TODO -/
def throwIndentationError (info : SyntaxTreeInfo) (msg : MessageData)
    (range : Option String.Range :=
      info.getPos?.map fun p => ⟨info.getSrc?.get!.findLineStart p, p⟩) :
    LinterM Unit :=
  let stx :=
    match range with
    | .some range => info.stx.setInfo <| .synthetic range.start range.stop
    | _ => info.stx
  throwThe IndentationError { msg := msg, stx := stx }

/-- docstring TODO -/
def IndentationLinter :=
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

open MessageData in
def runLinterOn (ref := indentationLinterRef) : IndentationLinter := fun info limit ↦ do
  trace[Indentation.run]
  m!"runLintersOn {info.idx} with {repr limit}"
  let linters ← ref.get
  let result ← match info.stx with
    | .node (kind := kind) .. =>
      linters.nodeLinters.find? kind |>.mapM (do
        trace[Indentation.run] m!"on {info.idx} with linter for node kind {.ofConstName kind}"
        · info limit)
    | .atom (val := val) .. =>
      linters.atomLinters.get? val |>.mapM (do
        trace[Indentation.run] m!"on {info.idx}  with linter for node atom {val}"
        · info limit)
    | .ident (val := val) .. =>
      linters.identLinters.find? val |>.mapM (do
        trace[Indentation.run] m!"on {info.idx} with linter for node ident {.ofConstName val}"
        · info limit)
    | _ => pure .none
  let mut result := result.getD <| .nextLinter limit
  for (priority, i) in linters.linters do
    match result with
    | .finished =>
      trace[Indentation.run] m!"finished on {info.idx}"
      return result
    | .nextLinter newLimit =>
      trace[Indentation.run] m!"on {info.idx} with linter with priority {priority}"
      result ← i info newLimit
  trace[Indentation.run] m!"finished on {info.idx}"
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
  trace[Indentation] stx
  let ⟨treeInfo, flatten⟩ := SyntaxTreeInfo.ofSyntax stx
  trace[Indentation] m!"syntax tree: {treeInfo}"
  let .some initialPos := treeInfo.getPos? | return
  let src := (← getFileMap).source
  trace[Indentation] s!"initial indentation : {treeInfo.getIndentation?}"
  let result ← ensure treeInfo {
      indentation := 0,
      additionalIndentation := 0,
      isExactIndentation := false,
      atMost := .some 0 } |>.run (flatten, src)
  if let .error e := result then
    logLint Mathlib.Linter.linter.indentation e.stx e.msg

initialize addLinter indentationLinter

end Indentation

end Mathlib.Linter
