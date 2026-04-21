/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
module

public import Mathlib.Init

/-!
# Basic Definitions for `RefinedDiscrTree`

We define
* `Key`, the discrimination tree key
* `LazyEntry`, the partial, lazy computation of a sequence of `Key`s
* `Trie`, a node of the discrimination tree, which is indexed with `Key`s
  and stores an array of pending `LazyEntry`s
* `RefinedDiscrTree`, the discrimination tree itself.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace Lean.Meta.RefinedDiscrTree


/-- Discrimination tree key. -/
inductive Key where
  /-- A metavariable. This key matches with anything. -/
  | star
  /-- A metavariable. This key matches with anything. It stores an identifier. -/
  | labelledStar (id : Nat)
  /-- An opaque variable. This key only matches with `Key.star`. -/
  | opaque
  /-- A constant. It stores the name and the arity. -/
  | const (declName : Name) (nargs : Nat)
  /-- A free variable. It stores the `FVarId` and the arity. -/
  | fvar (fvarId : FVarId) (nargs : Nat)
  /-- A bound variable, from a lambda or forall binder.
  It stores the De Bruijn index and the arity. -/
  | bvar (deBruijnIndex nargs : Nat)
  /-- A literal. -/
  | lit (v : Literal)
  /-- A sort. Universe levels are ignored. -/
  | sort
  /-- A lambda function. -/
  | lam
  /-- A dependent arrow. -/
  | forall
  /-- A projection. It stores the structure name, the projection index and the arity. -/
  | proj (typeName : Name) (idx nargs : Nat)
  deriving Inhabited, BEq

/-- Compute the hash of a `RefinedDiscrTree.Key`.

Note: at the root, `.const` is the most common key, and it is very uncommon
to get the same constant name with a different arity.
So for performance, we just use `hash name` to hash `.const name _`.
-/
protected def Key.hash : Key → UInt64
  | .star                => 0
  | .labelledStar id     => mixHash 5 <| hash id
  | .opaque              => 1
  | .const name _        => hash name
  | .fvar fvarId nargs   => mixHash 6 <| mixHash (hash fvarId) (hash nargs)
  | .bvar idx nargs      => mixHash 7 <| mixHash (hash idx) (hash nargs)
  | .lit v               => mixHash 8 <| hash v
  | .sort                => 2
  | .lam                 => 3
  | .«forall»            => 4
  | .proj name idx nargs => mixHash (hash nargs) <| mixHash (hash name) (hash idx)

instance : Hashable Key := ⟨Key.hash⟩

/-- Format a `RefinedDiscrTree.Key`. -/
def Key.format : Key → Format
  | .star                   => f!"*"
  | .labelledStar id        => f!"*{id}"
  | .opaque                 => "◾"
  | .const name nargs       => f!"⟨{name}, {nargs}⟩"
  | .fvar fvarId nargs      => f!"⟨{fvarId.name}, {nargs}⟩"
  | .lit (Literal.natVal n) => f!"{n}"
  | .lit (Literal.strVal s) => f!"{s.quote}"
  | .sort                   => "Sort"
  | .bvar i nargs           => f!"⟨#{i}, {nargs}⟩"
  | .lam                    => "λ"
  | .forall                 => "∀"
  | .proj name idx nargs    => f!"⟨{name}.{idx}, {nargs}⟩"

instance : ToFormat Key := ⟨Key.format⟩

/--
Converts an entry (i.e., `List Key`) to the discrimination tree into
`MessageData` that is more user-friendly.

This is a copy of `Lean.Meta.DiscrTree.keysAsPattern`
-/
partial def keysAsPattern (keys : Array Key) : CoreM MessageData := do
  let (msg, keys) ← go (paren := false) |>.run keys.toList
  if !keys.isEmpty then
    throwError "illegal discrimination tree entry: {keys.map Key.format}"
  return msg
where
  /-- Get the next key. -/
  next : StateRefT (List Key) CoreM Key := do
    let key :: keys ← get | throwError "illegal discrimination tree entry: {keys.map Key.format}"
    set keys
    return key
  /-- Format the application `f args`. -/
  mkApp (f : MessageData) (nargs : Nat) (paren : Bool) : StateRefT (List Key) CoreM MessageData :=
    if nargs == 0 then
      return f
    else do
      let mut r := m!""
      for _ in [:nargs] do
        r := r ++ Format.line ++ (← go)
      r := f ++ .nest 2 r
      if paren then
        return .paren r
      else
        return .group r

  /-- Format the next expression. -/
  go (paren := true) : StateRefT (List Key) CoreM MessageData := do
    let key ← next
    match key with
    | .const declName nargs =>
      mkApp m!"{← mkConstWithLevelParams declName}" nargs paren
    | .fvar fvarId nargs =>
      mkApp m!"{mkFVar fvarId}" nargs paren
    | .proj _ i nargs =>
      mkApp m!"{← go}.{i+1}" nargs paren
    | .bvar i nargs =>
      mkApp m!"#{i}" nargs paren
    | .lam =>
      return parenthesize m!"λ, {← go (paren := false)}" paren
    | .forall =>
      return parenthesize m!"{← go} → {← go (paren := false)}" paren
    | _ => return key.format
  /-- Add parentheses if `paren == true`. -/
  parenthesize (msg : MessageData) (paren : Bool) : MessageData :=
    if paren then msg.paren else msg.group

/-- Return the number of arguments that the `Key` takes. -/
def Key.arity : Key → Nat
  | .const _ nargs  => nargs
  | .fvar _ nargs   => nargs
  | .bvar _ nargs   => nargs
  | .lam            => 1
  | .forall         => 2
  | .proj _ _ nargs => nargs + 1
  | _               => 0

/-- The information for computing the keys of a subexpression. -/
structure ExprInfo where
  /-- The expression -/
  expr : Expr
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId := []
  /-- The local context, which contains the introduced bound variables. -/
  lctx : LocalContext
  /-- The local instances, which may contain the introduced bound variables. -/
  localInsts : LocalInstances
  /-- The `Meta.Config` used by this entry. -/
  cfg : Config

/-- Creates an `ExprInfo` using the current context. -/
def mkExprInfo (expr : Expr) (bvars : List FVarId) : MetaM ExprInfo :=
  return {
    expr, bvars,
    lctx := ← getLCtx
    localInsts := ← getLocalInstances
    cfg := ← getConfig
  }

/-- The possible values that can appear in the stack -/
inductive StackEntry where
  /-- `.star` is an expression that will not be explicitly indexed. -/
  | star
  /-- `.expr` is an expression that will be indexed. -/
  | expr (info : ExprInfo)

/-- Format a `RefinedDiscrTree.StackEntry`. -/
def StackEntry.format : StackEntry → Format
  | .star => f!".star"
  | .expr info => f!".expr {info.expr}"

instance : ToFormat StackEntry := ⟨StackEntry.format⟩

/-- A `LazyEntry` represents a snapshot of the computation of encoding an `Expr` as `Array Key`.
This is used for computing the keys one by one. -/
structure LazyEntry where
  /--
  If an expression creates more entries in the stack, for example because it is an application,
  then instead of pushing to the stack greedily, we only extend the stack once we need to.
  So, the field `previous` is used to extend the `stack` before looking in the `stack`.

  For example in `10.add (20.add 30)`, after computing the key `⟨Nat.add, 2⟩`, the stack is still
  empty, and `previous` will be `10.add (20.add 30)`.
  -/
  previous : Option ExprInfo := none
  /--
  The stack, used to emulate recursion. It contains the list of all expressions for which the
  keys still need to be computed, in that order.

  For example in `10.add (20.add 30)`, after computing the keys `⟨Nat.add, 2⟩` and `10`, the stack
  will be a list of length 1 containing the expression `20.add 30`.
  -/
  stack    : List StackEntry := []
  /-- The metavariable context, which may contain variables appearing in this entry. -/
  mctx     : MetavarContext
  /--
  `MVarId`s corresponding to the `.labelledStar` labels. The index in the array is the label.
  It is `none` if we use `.star` instead of `labelledStar`,
  for example when encoding the lookup expression.
  -/
  labelledStars?   : Option (Array MVarId)
  /--
  The `Key`s that have already been computed.

  Sometimes, more than one `Key` ends up being computed in one go. This happens when
  there are lambda binders (because it depends on the body whether the lambda key
  should be indexed or not). In that case the remaining `Key`s are stored in `results`.
  -/
  computedKeys  : List Key := []
deriving Inhabited

/-- Creates a `LazyEntry` using the current metavariable context. -/
def mkInitLazyEntry (labelledStars : Bool) : MetaM LazyEntry :=
  return {
    mctx := ← getMCtx
    labelledStars? := if labelledStars then some #[] else none
  }

/-- Format a `RefinedDiscrTree.LazyEntry`. -/
def LazyEntry.format (entry : LazyEntry) : Format := Id.run do
  let mut parts := #[f!"stack: {entry.stack}"]
  unless entry.computedKeys == [] do
    parts := parts.push f!"results: {entry.computedKeys}"
  if let some info := entry.previous then
    parts := parts.push f!"todo: {info.expr}"
  return Format.joinSep parts.toList ", "

instance : ToFormat LazyEntry := ⟨LazyEntry.format⟩

/-- Array index of a `Trie α` in the `tries` of a `RefinedDiscrTree`. -/
abbrev TrieIndex := Nat

/--
Discrimination tree trie. See `RefinedDiscrTree`.

A `Trie` will normally have exactly one of the following
- nonempty `values`
- nonempty `stars`, `labelledStars` and/or `children`
- nonempty `pending`
But defining it as a structure that can have all at the same time turns out to be easier.
-/
structure Trie (α : Type) where
  node ::
    /-- Return values, at a leaf -/
    values : Array α
    /-- Following `Trie`s based on a `Key.star`. -/
    star : Option TrieIndex
    /-- Following `Trie`s based on a `Key.labelledStar`. -/
    labelledStars : Std.HashMap Nat TrieIndex
    /-- Following `Trie`s based on the `Key`. -/
    children : Std.HashMap Key TrieIndex
    /-- Lazy entries that still have to be evaluated. -/
    pending : Array (LazyEntry × α)

instance {α : Type} : Inhabited (Trie α) := ⟨.node #[] none {} {} #[]⟩

end RefinedDiscrTree

open RefinedDiscrTree in

/--
Lazy refined discrimination tree. It is an index from expressions to values of type `α`.

We store all of the nodes in one `Array`, `tries`, instead of using a 'normal' inductive type.
This is so that we can modify the tree globally, which is very useful when evaluating lazy
entries and saving the result globally.
-/
structure RefinedDiscrTree (α : Type) where
  /-- `Trie`s at the root based of the `Key`. -/
  root : Std.HashMap Key TrieIndex := {}
  /-- Array of trie entries. Should be owned by this trie. -/
  tries : Array (Trie α) := #[]
deriving Inhabited

namespace RefinedDiscrTree

variable {α : Type}

/-- Format a `RefinedDiscrTree` as a flowchart.
- Non-terminal nodes are of the form `{key} =>`, followed by all of the following nodes,
  indented with 2 more spaces.
- Terminal nodes have either "entries", containing the return values,
  or "pending entries", for nodes that have not been evaluated/expanded.

For example:
```
Discrimination tree flowchart:
⟨HMul.hMul, 6⟩ =>
  ⟨Int, 0⟩ =>
    ⟨Int, 0⟩ =>
      * =>
        * =>
          *0 =>
            *0 =>
              pending entries: #[mul_self]
            *1 =>
              entries: #[mul_comm]
            ⟨Neg.neg, 3⟩ =>
              ⟨Int, 0⟩ =>
                * =>
                  *1 =>
                    entries: #[mul_neg]
            1 =>
              pending entries: #[mul_one]
          ⟨Neg.neg, 3⟩ =>
            pending entries: #[neg_mul]
          1 =>
            *0 =>
              entries: #[one_mul]
```
-/
partial def format [ToFormat α] (tree : RefinedDiscrTree α) : Format :=
  let lines := tree.root.fold (init := #[]) fun lines key trie =>
    lines.push (Format.nest 2 f!"{key} =>{Format.line}{go trie}")
  if lines.size = 0 then
    f!"<empty discrimination tree>"
  else
    "Discrimination tree flowchart:\n" ++ Format.joinSep lines.toList "\n"
where
  /-- Auxiliary function for `RefinedDiscrTree.format`. -/
  go (trie : TrieIndex) : Format := Id.run do
    let { values, star, labelledStars, children, pending } := tree.tries[trie]!
    let mut lines := #[]
    unless pending.isEmpty do
      lines := lines.push f!"pending entries: {pending.map (·.2)}"
    unless values.isEmpty do
      lines := lines.push f!"entries: {values}"
    if let some trie := star then
      lines := lines.push (Format.nest 2 f!"* =>{Format.line}{go trie}")
    lines := labelledStars.fold (init := lines) fun lines key trie =>
      lines.push (Format.nest 2 f!"*{key} =>{Format.line}{go trie}")
    lines := children.fold (init := lines) fun lines key trie =>
      lines.push (Format.nest 2 f!"{key} =>{Format.line}{go trie}")
    if lines.isEmpty then
      f!"<empty node>"
    else
      Format.joinSep lines.toList "\n"

instance [ToFormat α] : ToFormat (RefinedDiscrTree α) := ⟨format⟩

end Lean.Meta.RefinedDiscrTree
