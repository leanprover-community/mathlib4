import Lean.Meta.WHNF

/-!
# Basic Definitions for the RefinedDiscrTree

We define `Key`, `LazyEntry`, `Trie`, `RefinedDiscrTree`, and some basic functions for them.
-/
open Lean Meta

namespace Lean.Meta.RefinedDiscrTree


/-- Discrimination tree key. -/
inductive Key where
  /-- A metavariable. This key matches with anything. It stores an identifier. -/
  | star : (id : Nat) → Key
  /-- An opaque variable. This key only matches with itself or `Key.star`. -/
  | opaque : Key
  /-- A constant. It stores the name and the arity. -/
  | const : (declName : Name) → (nargs : Nat) → Key
  /-- A free variable. It stores the `FVarId` and the arity. -/
  | fvar : (fvarId : FVarId) → (nargs : Nat) → Key
  /-- A bound variable, from a lambda or forall binder.
  It stores the De Bruijn index and the arity. -/
  | bvar : (deBruijnIndex nargs : Nat) → Key
  /-- A literal. -/
  | lit : Literal → Key
  /-- A sort. Universe levels are ignored. -/
  | sort : Key
  /-- A lambda function. -/
  | lam : Key
  /-- A dependent arrow. -/
  | forall : Key
  /-- A projection. It stores the structure name, the projection index and the arity. -/
  | proj : (typeName : Name) → (idx nargs : Nat) → Key
  deriving Inhabited, BEq, Repr

private nonrec def Key.hash : Key → UInt64
  | .star id             => mixHash 7883 $ hash id
  | .opaque              => 342
  | .const name nargs    => mixHash 5237 $ mixHash (hash name) (hash nargs)
  | .fvar fvarId nargs   => mixHash 8765 $ mixHash (hash fvarId) (hash nargs)
  | .bvar idx nargs      => mixHash 4323 $ mixHash (hash idx) (hash nargs)
  | .lit v               => mixHash 1879 $ hash v
  | .sort                => 2411
  | .lam                 => 4742
  | .«forall»            => 9752
  | .proj name idx nargs => mixHash (hash nargs) $ mixHash (hash name) (hash idx)

instance : Hashable Key := ⟨Key.hash⟩

/-- Constructor index used for ordering `Key`.
Note that the index of the star pattern is 0, so that when looking up in a `Trie`,
we can look at the start of the sorted array for all `.star` patterns. -/
def Key.ctorIdx : Key → Nat
  | .star ..   => 0
  | .opaque .. => 1
  | .const ..  => 2
  | .fvar ..   => 3
  | .bvar ..   => 4
  | .lit ..    => 5
  | .sort      => 6
  | .lam       => 7
  | .forall    => 8
  | .proj ..   => 9

/-- The order on `Key` used in the `RefinedDiscrTree`. -/
private def Key.lt : Key → Key → Bool
  | .star id₁,               .star id₂               => id₁ < id₂
  | .const name₁ nargs₁,     .const name₂ nargs₂     => Name.quickLt name₁ name₂ ||
                                                          name₁ == name₂ && nargs₁ < nargs₂
  | .fvar f₁ nargs₁,         .fvar f₂ nargs₂         => Name.quickLt f₁.name f₂.name ||
                                                          f₁ == f₂ && nargs₁ < nargs₂
  | .bvar i₁ nargs₁,         .bvar i₂ nargs₂         => i₁ < i₂ || (i₁ == i₂ && nargs₁ < nargs₂)
  | .lit v₁,                 .lit v₂                 => v₁ < v₂
  | .proj name₁ idx₁ nargs₁, .proj name₂ idx₂ nargs₂ => Name.quickLt name₁ name₂ ||
    name₁ == name₂ && (idx₁ < idx₂ || idx₁ == idx₂ && nargs₁ < nargs₂)
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

private def Key.format : Key → Format
  | .star id                => f!"_{id}"
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
Helper function for converting an entry (i.e., `Array Key`) to the discrimination tree into
`MessageData` that is more user-friendly. We use this function to implement diagnostic information.
-/
partial def keysAsPattern (keys : List Key) : CoreM MessageData := do
  go (paren := false) |>.run' keys
where
  /-- Get the next key. -/
  next : StateRefT (List Key) CoreM Key := do
    let key :: keys ← get | throwError m! "bad keys: {keys.map Key.format}"
    set keys
    return key
  /-- Format the application `f args`. -/
  mkApp (f : MessageData) (args : Array MessageData) (paren : Bool) : CoreM MessageData := do
    if args.isEmpty then
      return f
    else
      let mut r := f
      for arg in args do
        r := r ++ m!" {arg}"
      if paren then
        return m!"({r})"
      else
        return r
  /-- Format the next expression. -/
  go (paren := true) : StateRefT (List Key) CoreM MessageData := do
    let key ← next
    match key with
    | .const declName nargs =>
      mkApp m!"{← mkConstWithLevelParams declName}" (← goN nargs) paren
    | .fvar fvarId nargs =>
      mkApp m!"{mkFVar fvarId}" (← goN nargs) paren
    | .proj _ i nargs =>
      mkApp m!"{← go}.{i+1}" (← goN nargs) paren
    | .bvar i nargs =>
      mkApp m!"#{i}" (← goN nargs) paren
    | .lam =>
      let r := m!"λ, {← go (paren := false)}"
      if paren then return m!"({r})" else return r
    | .forall =>
      let r := m!"{← go} → {← go (paren := false)}";
      if paren then return m!"({r})" else return r
    | _ => return key.format
  /-- Format the next `n` expressions. -/
  goN (num : Nat) : StateRefT (List Key) CoreM (Array MessageData) := do
    let mut r := #[]
    for _ in [: num] do
      r := r.push (← go)
    return r

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
  /-- Variables that come from a lambda that has been removed via η-reduction. -/
  forbiddenVars : List FVarId := []
  /-- The local context, which contains the introduced bound variables. -/
  lctx : LocalContext
  /-- The local instances, which may contain the introduced bound variables. -/
  localInsts : LocalInstances

/-- The possible values that can appear in the stack:
- `.star` is an expression that will not be explicitly indexed
- `.expr` is an expression that will be indexed
- `.cache` is a cache entry, used for computations that can have multiple outcomes,
  so that they always give the same outcome. -/
inductive StackEntry where
  | star
  | expr (info : ExprInfo)
  | cache (key : Expr) (value : List Key)

private def StackEntry.format : StackEntry → Format
  | .star => f!".star"
  | .expr info => f!".expr {info.expr}"
  | .cache key value => f!".cache {key} {value}"

instance : ToFormat StackEntry := ⟨StackEntry.format⟩

/-- A `LazyEntry` represents a snapshot of the computation of encoding an `Expr` as `Array Key`.
This is used for computing the keys one by one. -/
structure LazyEntry (α : Type) where
  /-- The stack, used to emulate recursion. -/
  stack         : List StackEntry := []
  /-- The `MVarId` assignments for converting into `.star` keys. -/
  stars         : RBMap MVarId Nat (·.name.quickCmp ·.name) := {}
  /-- The number to be used for the next new `.star` key. -/
  nStars        : Nat := 0
  /-- The `Key`s that have already been computed. -/
  results       : List Key := []
  /-- The cache of past computations that have multiple possible outcomes. -/
  cache         : AssocList Expr (List Key) := .nil
  /-- The return value. -/
  val           : α

variable {α : Type}

instance [Inhabited α] : Inhabited (LazyEntry α) where
  default := { val := default }

private def LazyEntry.format [ToFormat α] (entry : LazyEntry α) : Format :=
  let results := if entry.results matches [] then f!"" else f!"results: {entry.results}, "
  f!"stack: {entry.stack}, {results}value: {entry.val}"

instance [ToFormat α] : ToFormat (LazyEntry α) := ⟨LazyEntry.format⟩

abbrev TrieIndex := Nat

/-- Discrimination tree trie. See `RefinedDiscrTree`. -/
structure Trie (α : Type) where
  node ::
    /-- Leaf values of the Trie. `values` is an `Array` of size at least 1. -/
    values : Array α
    /-- Following `Trie`s based on a `Key.star`. -/
    stars : HashMap Nat TrieIndex
    /-- Following `Trie`s based on the `Key`. -/
    children : HashMap Key TrieIndex
    /-- Lazy entries that still have to be evaluated. -/
    pending : Array (LazyEntry α)


instance : Inhabited (Trie α) := ⟨.node #[] {} {} #[]⟩

-- private partial def Trie.format [ToFormat α] : Trie α → Format
--   | .node cs => Format.group $ Format.paren $
--     "node " ++ Format.join (cs.toList.map fun (k, c) =>
--       Format.line ++ Format.paren (format (prepend k c)))
--   | .values vs => if vs.isEmpty then Format.nil else Std.format vs
--   | .path ks c => Format.sbracket (Format.joinSep ks.toList (", "))
--       ++ " => " ++ Format.line ++ format c
-- where
--   prepend (k : Key) (t : Trie α) : Trie α := match t with
--     | .path ks c => .path (#[k] ++ ks) c
--     | t => .path #[k] t
-- instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩

end RefinedDiscrTree

open RefinedDiscrTree in

/-- Discrimination tree. It is an index from expressions to values of type `α`. -/
structure RefinedDiscrTree (α : Type) where
  /-- `Trie`s at the root based of the `Key`. -/
  root : HashMap Key TrieIndex := {}
  /-- Array of trie entries. Should be owned by this trie. -/
  tries : Array (Trie α) := #[]
  /-- Configuration for normalization. -/
  config : Lean.Meta.WhnfCoreConfig := {}

namespace RefinedDiscrTree

variable {α : Type}

instance : Inhabited (RefinedDiscrTree α) := ⟨{}⟩

-- private partial def format [ToFormat α] (d : RefinedDiscrTree α) : Format :=
--   let (_, r) := d.root.foldl
--     (fun (p : Bool × Format) k c =>
--       (false,
--         p.2 ++ (if p.1 then Format.nil else Format.line) ++
--           Format.paren (Std.format k ++ " => " ++ Std.format c)))
--     (true, Format.nil)
--   Format.group r

-- instance [ToFormat α] : ToFormat (RefinedDiscrTree α) := ⟨format⟩
