/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Lean.Meta.DiscrTree
import Batteries.Data.List.Basic
import Mathlib.Lean.Meta.RefinedDiscrTree.StateList
import Mathlib.Lean.Meta.RefinedDiscrTree.Pi

/-!
We define discrimination trees for the purpose of unifying local expressions with library results.

This data structure is based on `Lean.Meta.DiscrTree`, and includes many more features.
Comparing performance with `Lean.Meta.DiscrTree`, this version is a bit slower.
However in practice this does not matter, because a lookup in a discrimination tree is always
combined with `isDefEq` unification and these unifications are significantly more expensive,
so the extra lookup cost is neglegible, while better discrimination tree indexing, and thus
less potential matches can save a significant amount of computation.

## New features

- The keys `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for
  matching under lambda and forall binders. `Key.lam` has arity 1 and indexes the body.
  `Key.forall` has arity 2 and indexes the domain and the body. The reason for not indexing the
  domain of a lambda expression is that it is usually already determined, for example in
  `∃ a : α, p`, which is `@Exists α fun a : α => p`, we don't want to index the domain `α` twice.
  In a forall expression it is necessary to index the domain, because in an implication `p → q`
  we need to index both `p` and `q`. `Key.bvar` works the same as `Key.fvar`, but stores the
  De Bruijn index to identify it.

  For example, this allows for more specific matching with the left hand side of
  `∑ i in range n, i = n * (n - 1) / 2`, which is indexed by
  `[⟨Finset.sum, 5⟩, ⟨Nat, 0⟩, ⟨Nat, 0⟩, *0, ⟨Finset.Range, 1⟩, *1, λ, ⟨#0, 0⟩]`.

- The key `Key.star` takes a `Nat` identifier as an argument. For example,
  the library pattern `?a + ?a` is encoded as `[⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *2]`.
  `*0` corresponds to the type of `a`, `*1` to the `HAdd` instance, and `*2` to `a`.
  This means that it will only match an expression `x + y` if `x` is definitionally equal to `y`.
  The matching algorithm requires that the same stars from the discrimination tree match with
  the same patterns in the lookup expression, and similarly requires that the same metavariables
  form the lookup expression match with the same pattern in the discrimination tree.

- The key `Key.opaque` has been introduced in order to index existential variables
  in lemmas like `Nat.exists_prime_and_dvd {n : ℕ} (hn : n ≠ 1) : ∃ p, Prime p ∧ p ∣ n`,
  where the part `Prime p` gets the pattern `[⟨Nat.Prime, 1⟩, ◾]`. (◾ represents `Key.opaque`)
  When matching, `Key.opaque` can only be matched by `Key.star`.

  Using the `WhnfCoreConfig` argument, it is possible to disable β-reduction and ζ-reduction.
  As a result, we may get a lambda expression applied to an argument or a let-expression.
  Since there is no support for indexing these, they will be indexed by `Key.opaque`.

- We evaluate the matching score of a unification.
  This score represents the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 2,
  since the pattern of commutativity is [⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *3],
  so matching `⟨HAdd.hAdd, 6⟩` gives 1 point,
  and matching `*0` after its first appearence gives another point, but the third argument is an
  outParam, so this gets ignored. Similarly, matching it with `add_assoc` gives a score of 5.

- Patterns that have the potential to be η-reduced are put into the `RefinedDiscrTree` under all
  possible reduced key sequences. This is for terms of the form `fun x => f (?m x₁ .. xₙ)`, where
  `?m` is a metavariable, and one of `x₁, .., xₙ` is `x`.
  For example, the pattern `Continuous fun y => Real.exp (f y)])` is indexed by
  both `[⟨Continuous, 5⟩, *0, ⟨Real, 0⟩, *1, *2, λ, ⟨Real.exp⟩, *3]`
  and  `[⟨Continuous, 5⟩, *0, ⟨Real, 0⟩, *1, *2, ⟨Real.exp⟩]`
  so that it also comes up if you search with `Continuous Real.exp`.
  Similarly, `Continuous fun x => f x + g x` is indexed by
  both `[⟨Continuous, 1⟩, λ, ⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *3]`
  and  `[⟨Continuous, 1⟩, ⟨HAdd.hAdd, 5⟩, *0, *0, *0, *1, *2]`.

- For sub-expressions not at the root of the original expression we have some additional reductions:
  - Any combination of `ofNat`, `Nat.zero`, `Nat.succ` and number literals
    is stored as just a number literal.
  - The expression `fun a : α => a` is stored as `@id α`.
    - This makes lemmas such as `continuous_id'` redundant, which is the same as `continuous_id`,
      with `id` replaced by `fun x => x`.
  - Lambdas in front of number literals are removed. This is because usually `n : α → β` is
    defined to be `fun _ : α => n` for a number literal `n`. So instead of `[λ, n]` we store `[n]`.
  - Any expression with head constant `+`, `*`, `-`, `/`, `⁻¹`, `+ᵥ`, `•` or `^` is normalized to
    not have a lambda in front and to always have the default amount of arguments.
    e.g. `(f + g) a` is stored as `f a + g a` and `fun x => f x + g x` is stored as `f + g`.
    - This makes lemmas such as `MeasureTheory.integral_integral_add'` redundant, which is the
      same as `MeasureTheory.integral_integral_add`, with `f a + g a` replaced by `(f + g) a`
    - it also means that a lemma like `Continuous.mul` can be stated as talking about `f * g`
      instead of `fun x => f x * g x`.
    - When trying to find `Continuous.add` with the expression `Continuous fun x => 1 + x`,
      this is possible, because we first revert the eta-reduction that happens by default,
      and then distribute the lambda. Thus this is indexed as `Continuous (1 + id)`,
      which matches with `Continuous (f + g)` from `Continuous.add`.

## Lazt computation

We encode an `Expr` as an `Array Key`. This is implemented with a lazy computation:
we start with a `LazyEntry α`, which comes with a step function of type
`LazyEntry α → Array (Key × LazyEntry α) ⊕ α`.


## TODO

- The unification algorithm could be made more elaborate.
  For example, when looking up the expression `?a + ?a` (for rewriting), there will be
  results like `n + n = 2 * n` or `a + b = b + a`, but not `n + 1 = n.succ`,
  even though this would still unify.

- The reason why implicit arguments are not ignored by the discrimination tree is that they provide
  important type information. Because of this it seems more natural to index the types of
  expressions instead of indexing the implicit type arguments. Then each key would additionally
  index the type of that expression. So instead of indexing `?a + ?b` as
  `[⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *3]`, it would be indexed by something like
  `[(*0, ⟨HAdd.hAdd, 6⟩), _, _, _, _, (*0, *1), (*0, *2)]`.
  The advantage of this would be that there will be less duplicate indexing of types,
  because many functions index the types of their arguments and their return type
  with implicit arguments, meaning that types unnecessarily get indexed multiple times.
  This modification can be explored, but it could very well not be an improvement.

-/

open Lean Meta

namespace Lean.Meta.RefinedDiscrTree

/-!
### Definitions

We define `Key`, `Trie`, `RefinedDiscrTree` and `DTExpr`, and some basic functions for them.
-/

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
partial def keysAsPattern (keys : Array Key) : CoreM MessageData := do
  go (parenIfNonAtomic := false) |>.run' keys.toList
where
  next? : StateRefT (List Key) CoreM (Option Key) := do
    let key :: keys ← get | return none
    set keys
    return some key

  mkApp (f : MessageData) (args : Array MessageData) (parenIfNonAtomic : Bool) : CoreM MessageData := do
    if args.isEmpty then
      return f
    else
      let mut r := f
      for arg in args do
        r := r ++ m!" {arg}"
      if parenIfNonAtomic then
        return m!"({r})"
      else
        return r

  go (parenIfNonAtomic := true) : StateRefT (List Key) CoreM MessageData := do
    let some key ← next? | return .nil
    match key with
    | .const declName nargs =>
      mkApp m!"{← mkConstWithLevelParams declName}" (← goN nargs) parenIfNonAtomic
    | .fvar fvarId nargs =>
      mkApp m!"{mkFVar fvarId}" (← goN nargs) parenIfNonAtomic
    | .proj _ i nargs =>
      mkApp m!"{← go}.{i+1}" (← goN nargs) parenIfNonAtomic
    | .bvar i nargs =>
      mkApp m!"#{i}" (← goN nargs) parenIfNonAtomic
    | .lam =>
      let r := m!"λ, {← go false}"
      if parenIfNonAtomic then return m!"({r})" else return r
    | .forall =>
      let r := m!"{← go} → {← go false}";
      if parenIfNonAtomic then return m!"({r})" else return r
    | _ => return key.format

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



/-- Discrimination tree trie. See `RefinedDiscrTree`. -/
inductive Trie (α : Type) where
  /-- Map from `Key` to `Trie`. Children is an `Array` of size at least 2,
  sorted in increasing order using `Key.lt`. -/
  | node (children : Array (Key × Trie α))
  /-- Sequence of nodes with only one child. `keys` is an `Array` of size at least 1.
  `.path` is used instead of `.node` to reduce the storage size of the discrimination tree. -/
  | path (keys : Array Key) (child : Trie α)
  /-- Leaf of the Trie. `values` is an `Array` of size at least 1. -/
  | values (vs : Array α)

variable {α : Type}

instance : Inhabited (Trie α) := ⟨.node #[]⟩

/-- `Trie.path` constructor that only inserts the path if it is non-empty. -/
def Trie.mkPath (keys : Array Key) (child : Trie α) :=
  if keys.isEmpty then child else Trie.path keys child

/-- `Trie` constructor for a single value. -/
def Trie.singleton (keys : Array Key) (value : α) : Trie α :=
  mkPath keys (values #[value])

/-- `Trie.node` constructor for combining two `Key`, `Trie α` pairs. -/
def Trie.mkNode2 (k1 : Key) (t1 : Trie α) (k2 : Key) (t2 : Trie α) : Trie α :=
  if k1 < k2 then
    .node #[(k1, t1), (k2, t2)]
  else
    .node #[(k2, t2), (k1, t1)]

/-- Return the values from a `Trie α`, assuming that it is a leaf -/
def Trie.values! : Trie α → Array α
  | .values vs => vs
  | _ => panic! "expected .values constructor"

/-- Return the children of a `Trie α`, assuming that it is not a leaf.
The result is sorted by the `Key`'s -/
def Trie.children! : Trie α → Array (Key × Trie α)
  | .node cs => cs
  | .path ks c => #[(ks[0]!, mkPath ks[1:] c)]
  | .values _ => panic! "did not expect .values constructor"

private partial def Trie.format [ToFormat α] : Trie α → Format
  | .node cs => Format.group $ Format.paren $
    "node " ++ Format.join (cs.toList.map fun (k, c) =>
      Format.line ++ Format.paren (format (prepend k c)))
  | .values vs => if vs.isEmpty then Format.nil else Std.format vs
  | .path ks c => Format.sbracket (Format.joinSep ks.toList (", "))
      ++ " => " ++ Format.line ++ format c
where
  prepend (k : Key) (t : Trie α) : Trie α := match t with
    | .path ks c => .path (#[k] ++ ks) c
    | t => .path #[k] t
instance [ToFormat α] : ToFormat (Trie α) := ⟨Trie.format⟩

end RefinedDiscrTree

open RefinedDiscrTree

/-- Discrimination tree. It is an index from expressions to values of type `α`. -/
structure RefinedDiscrTree (α : Type) where
  /-- The underlying `PersistentHashMap` of a `RefinedDiscrTree`. -/
  root : PersistentHashMap Key (Trie α) := {}

namespace RefinedDiscrTree

variable {α : Type}

instance : Inhabited (RefinedDiscrTree α) := ⟨{}⟩

private partial def format [ToFormat α] (d : RefinedDiscrTree α) : Format :=
  let (_, r) := d.root.foldl
    (fun (p : Bool × Format) k c =>
      (false,
        p.2 ++ (if p.1 then Format.nil else Format.line) ++
          Format.paren (Std.format k ++ " => " ++ Std.format c)))
    (true, Format.nil)
  Format.group r

instance [ToFormat α] : ToFormat (RefinedDiscrTree α) := ⟨format⟩



/-! ### Encoding an `Expr` -/


/-- Return `true` if `e` is one of the following
- A nat literal (numeral)
- `Nat.zero`
- `Nat.succ x` where `isNumeral x`
- `OfNat.ofNat _ x _` where `isNumeral x` -/
private partial def isNumeral (e : Expr) : Bool :=
  if e.isRawNatLit then true
  else
    let f := e.getAppFn
    if !f.isConst then false
    else
      let fName := f.constName!
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then isNumeral e.appArg!
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then isNumeral (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then true
      else false

/-- Return `some n` if `e` is definitionally equal to the natural number `n`. -/
private partial def toNatLit? (e : Expr) : Option Literal :=
  if isNumeral e then
    if let some n := loop e then
      some (.natVal n)
    else
      none
  else
    none
where
  loop (e : Expr) : Option Nat := do
    let f := e.getAppFn
    match f with
    | .lit (.natVal n) => return n
    | .const fName .. =>
      if fName == ``Nat.succ && e.getAppNumArgs == 1 then
        let r ← loop e.appArg!
        return r+1
      else if fName == ``OfNat.ofNat && e.getAppNumArgs == 3 then
        loop (e.getArg! 1)
      else if fName == ``Nat.zero && e.getAppNumArgs == 0 then
        return 0
      else
        failure
    | _ => failure

/-- Check whether the expression is represented by `Key.star`. -/
def isStar : Expr → Bool
  | .mvar .. => true
  | .app f _ => isStar f
  | _ => false

/-- Check whether the expression is represented by `Key.star` and has `arg` as an argument. -/
def isStarWithArg (arg : Expr) : Expr → Bool
  | .app f a => if a == arg then isStar f else isStarWithArg arg f
  | _ => false

/-- If there is a loose `.bvar` returns `none`. Otherwise returns the index
of the next branch of the expression. -/
private partial def hasLooseBVarsAux (keys : Array Key) (depth index : Nat) : Option Nat :=
  match keys[index]! with
  | .const _ nargs
  | .fvar _ nargs   => recurse nargs
  | .bvar i nargs   => if i ≥ depth then none else recurse nargs
  | .lam            => hasLooseBVarsAux keys (depth + 1) (index + 1)
  | .forall         => hasLooseBVarsAux keys depth (index + 1) >>= hasLooseBVarsAux keys (depth + 1)
  | .proj _ _ nargs => recurse (nargs + 1)
  | _               => some (index + 1)
where
  recurse (nargs : Nat) : Option Nat :=
    nargs.foldM (init := index + 1) (fun _ => hasLooseBVarsAux keys depth)

/-- Determine whether `keys` contains a loose bound variable. -/
def hasLooseBVars (keys : Array Key) : Bool :=
  hasLooseBVarsAux keys 0 0 |>.isNone


namespace MkKeys

private structure Context where
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId := []
  /-- Variables that come from a lambda that has been removed via η-reduction. -/
  forbiddenVars : List FVarId := []
  config : WhnfCoreConfig
  fvarInContext : FVarId → Bool

private def getStar {m : Type → Type} [MonadState (Array MVarId) m] (mvarId? : Option MVarId) :
    m Key :=
  modifyGet fun s =>
    match mvarId? with
    | some mvarId => match s.getIdx? mvarId with
      | some idx => (.star idx, s)
      | none => (.star s.size, s.push mvarId)
    | none => (.star s.size, s.push ⟨.anonymous⟩)

/-- Determine for each argument whether it should be ignored. -/
def getIgnores (fn : Expr) (args : Array Expr) : MetaM (Array Bool) := do
  let mut fnType ← inferType fn
  let mut result := Array.mkEmpty args.size
  let mut j := 0
  for i in [:args.size] do
    unless fnType.isForall do
      fnType ← whnfD (fnType.instantiateRevRange j i args)
      j := i
    let .forallE _ d b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
    fnType := b
    result := result.push (← isIgnoredArg args[i]! d bi)
  return result
where
  /-- Determine whether the argument should be ignored. -/
  isIgnoredArg (arg domain : Expr) (binderInfo : BinderInfo) : MetaM Bool := do
    if domain.isOutParam then
      return true
    match binderInfo with
    | .instImplicit => return true
    | .implicit
    | .strictImplicit => return !(← isType arg)
    | .default => isProof arg

@[specialize]
private def withLams {m} [Monad m] [MonadWithReader Context m]
    (lambdas : List FVarId) (k : m (Array Key)) : m (Array Key) :=
  if lambdas.isEmpty then
    k
  else do
    let e ← withReader (fun c => { c with bvars := lambdas ++ c.bvars }) k
    return lambdas.foldl (fun d _ => #[.lam] ++ d) e

/-- Reduction procedure for the `RefinedDiscrTree` indexing. -/
partial def reduce (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← whnfCore e config
  match (← unfoldDefinition? e) with
  | some e => reduce e config
  | none => match e.etaExpandedStrict? with
    | some e => reduce e config
    | none   => return e

/-- Repeatedly reduce while stripping lambda binders and introducing their variables -/
@[specialize]
partial def lambdaTelescopeReduce {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    [MonadWithReader Context m] [MonadState (Array MVarId) m]
    (e : Expr) (lambdas : List FVarId) (config : WhnfCoreConfig)
    (k : Expr → List FVarId → m (Array Key)) : m (Array Key) := do
  -- expressions marked with `no_index` are indexed with a star
  if DiscrTree.hasNoindexAnnotation e then
    withLams lambdas do return #[← getStar none]
  else
  match ← reduce e config with
  | .lam n d b bi =>
    withLocalDecl n bi d fun fvar =>
      lambdaTelescopeReduce (b.instantiate1 fvar) (fvar.fvarId! :: lambdas) config k
  | e => k e lambdas


/-- Return the encoding of `e` as a `DTExpr`.
If `root = false`, then `e` is a strict sub expression of the original expression. -/
partial def mkKeyAux (e : Expr) (root : Bool) : ReaderT Context (StateT (Array MVarId) MetaM) (Array Key) := do
  lambdaTelescopeReduce e [] (← read).config fun e lambdas => do
  unless root do
    if let some (n, as) ← reducePi e lambdas then
      let (args, lambdas) := as.back
      return ← withLams lambdas do
        return #[.const n args.size] ++ (← args.concatMapM fun
          | none => return #[← getStar none]
          | some arg => mkKeyAux arg false)
  e.withApp fun fn args => do

  let argDTExpr (arg : Expr) (ignore : Bool) : ReaderT Context (StateT (Array MVarId) MetaM) (Array Key) :=
    if ignore then return #[← getStar none] else mkKeyAux arg false

  let argDTExprs : ReaderT Context (StateT (Array MVarId) MetaM) (Array (Array Key)) := do
    let ignores ← getIgnores fn args
    args.mapIdxM fun i arg =>
      argDTExpr arg ignores[i]!

  match fn with
  | .const n _ =>
    unless root do
      /- since `(fun _ => 0) = 0` and `(fun _ => 1) = 1`,
      we don't index lambdas before literals -/
      if let some v := toNatLit? e then
        return #[.lit v]
    withLams lambdas do
      return #[.const n args.size] ++ (← argDTExprs).concatMap id
  | .proj n i a =>
    withLams lambdas do
      let a ← argDTExpr a (isClass (← getEnv) n)
      return #[.proj n i args.size] ++ a ++ (← argDTExprs).concatMap id
  | .fvar fvarId =>
    /- we index `fun x => x` as `id` when not at the root -/
    if let fvarId' :: lambdas' := lambdas then
      if fvarId' == fvarId && args.isEmpty && !root then
        return ← withLams lambdas' do
          let type ← mkKeyAux (← fvarId.getType) false
          return #[.const ``id 1] ++ type
    withLams lambdas do
      if let some idx := (← read).bvars.indexOf? fvarId then
        return #[.bvar idx args.size] ++ (← argDTExprs).concatMap id
      if (← read).fvarInContext fvarId then
        return #[.fvar fvarId args.size] ++ (← argDTExprs).concatMap id
      else
        return #[.opaque]
  | .mvar mvarId =>
    /- If there are arguments, don't index the lambdas, as `e` might contain the bound variables
    When not at the root, don't index the lambdas, as it should be able to match with
    `fun _ => x + y`, which is indexed as `(fun _ => x) + (fun _ => y)`. -/
    if args.isEmpty && (root || lambdas.isEmpty) then
      withLams lambdas do return #[← getStar (some mvarId)]
    else
      return #[← getStar none]

  | .forallE n d b bi =>
    withLams lambdas do
      let d' ← mkKeyAux d false
      let b' ← withLocalDecl n bi d fun fvar =>
        withReader (fun c => { c with bvars := fvar.fvarId! :: c.bvars }) do
          mkKeyAux (b.instantiate1 fvar) false
      return #[.forall] ++ d' ++ b'
  | .lit v      => withLams lambdas do return #[.lit v]
  | .sort _     => withLams lambdas do return #[.sort]
  | .letE ..    => withLams lambdas do return #[.opaque]
  | .lam ..     => withLams lambdas do return #[.opaque]
  | _           => unreachable!


private abbrev M := ReaderT Context $ StateListT (Array MVarId × AssocList Expr (Array Key)) $ MetaM

/-
Caching values is a bit dangerous, because when two expressions are be equal and they live under
a different number of binders, then the resulting De Bruijn indices are offset.
In practice, getting a `.bvar` in a `DTExpr` is very rare, so we exclude such values from the cache.
-/
instance : MonadCache Expr (Array Key) M where
  findCached? e := do
    let s ← get
    return s.2.find? e
  cache e e' :=
    if hasLooseBVars e' then
      return
    else
      modify (fun (s,t) => (s,t.insert e e'))

local instance : MonadState (Array MVarId) M where
  get := return (← get).1
  set s := modify ({ · with fst := s })
  modifyGet f := modifyGet fun s => let (a,s1) := f s.1; (a, {s with fst := s1})


/-- Return all pairs of body, bound variables that could possibly appear due to η-reduction -/
@[specialize]
def etaPossibilities (e : Expr) (lambdas : List FVarId) (k : Expr → List FVarId → M α) : M α :=
  k e lambdas
  <|> do
  match e, lambdas with
  | .app f a, fvarId :: lambdas =>
    if isStarWithArg (.fvar fvarId) a then
      withReader (fun c => { c with forbiddenVars := fvarId :: c.forbiddenVars }) do
        etaPossibilities f lambdas k
    else
      failure
  | _, _ => failure

/-- run `etaPossibilities`, and cache the result if there are multiple possibilities. -/
@[specialize]
def cacheEtaPossibilities (e original : Expr) (lambdas : List FVarId)
    (k : Expr → List FVarId → M (Array Key)) : M (Array Key) :=
  match e, lambdas with
  | .app _ a, fvarId :: _ =>
    if isStarWithArg (.fvar fvarId) a then
      checkCache original fun _ =>
        etaPossibilities e lambdas k
    else
      k e lambdas
  | _, _ => k e lambdas


/-- Return all encodings of `e` as a `DTExpr`, taking possible η-reductions into account.
If `root = false`, then `e` is a strict sub expression of the original expression. -/
partial def mkKeysAux (original : Expr) (root : Bool) : M (Array Key) := do
  lambdaTelescopeReduce original [] (← read).config fun e lambdas => do
  unless root do
    if let some (n, as) ← reducePi e lambdas then
      let (args, lambdas) ← fun _ => StateListT.ofArray as
      return ← withLams lambdas do
        return #[.const n args.size] ++ (← args.concatMapM fun
          | none => return #[← getStar none]
          | some arg => mkKeysAux arg false)
  cacheEtaPossibilities e original lambdas fun e lambdas =>
  e.withApp fun fn args => do

  let argDTExpr (arg : Expr) (ignore : Bool) : M (Array Key) :=
    if ignore then return #[← getStar none] else mkKeysAux arg false

  let argDTExprs : M (Array (Array Key)) := do
    let ignores ← getIgnores fn args
    args.mapIdxM fun i arg =>
      argDTExpr arg ignores[i]!

  match fn with
  | .const n _ =>
      unless root do
        /- since `(fun _ => 0) = 0` and `(fun _ => 1) = 1`,
        we don't index lambdas before nat literals -/
        if let some v := toNatLit? e then
          return #[.lit v]
      withLams lambdas do
        return #[.const n args.size] ++ (← argDTExprs).concatMap id
  | .proj n i a =>
    withLams lambdas do
    let a ← argDTExpr a (isClass (← getEnv) n)
    return #[.proj n i args.size] ++ a ++ (← argDTExprs).concatMap id
  | .fvar fvarId =>
    /- we index `fun x => x` as `id` when not at the root -/
    if let fvarId' :: lambdas' := lambdas then
      if fvarId' == fvarId && args.isEmpty && !root then
        return ← withLams lambdas' do
          let type ← mkKeysAux (← fvarId.getType) false
          return #[.const ``id 1] ++ type
    withLams lambdas do
      let c ← read
      if let some idx := c.bvars.indexOf? fvarId then
        return #[.bvar idx args.size] ++ (← argDTExprs).concatMap id
      guard !(c.forbiddenVars.contains fvarId)
      if c.fvarInContext fvarId then
        return #[.fvar fvarId args.size] ++ (← argDTExprs).concatMap id
      else
        return #[.opaque]
  | .mvar mvarId =>
    /- If there are arguments, don't index the lambdas, as `e` might contain the bound variables
    When not at the root, don't index the lambdas, as it should be able to match with
    `fun _ => x + y`, which is indexed as `(fun _ => x) + (fun _ => y)`. -/
    if args.isEmpty && (root || lambdas.isEmpty) then
      withLams lambdas do return #[← getStar (some mvarId)]
    else
      return #[← getStar none]

  | .forallE n d b bi =>
    withLams lambdas do
    let d' ← mkKeysAux d false
    let b' ← withLocalDecl n bi d fun fvar =>
      withReader (fun c => { c with bvars := fvar.fvarId! :: c.bvars }) do
        mkKeysAux (b.instantiate1 fvar) false
    return #[.forall] ++ d' ++ b'
  | .lit v      => withLams lambdas do return #[.lit v]
  | .sort _     => withLams lambdas do return #[.sort]
  | .letE ..    => withLams lambdas do return #[.opaque]
  | .lam ..     => withLams lambdas do return #[.opaque]
  | _           => unreachable!

end MkKeys

/-- Return `false` if the `Key`s have pattern `*` or `Eq(*, *, *)`. -/
def isSpecific : Array Key → Bool
  | #[.star _]
  | #[.const ``Eq 3, .star _, .star _, .star _] => false
  | _ => true

/-- Return the encoding of `e` as a `DTExpr`.

Warning: to account for potential η-reductions of `e`, use `mkDTExprs` instead.

The argument `fvarInContext` allows you to specify which free variables in `e` will still be
in the context when the `RefinedDiscrTree` is being used for lookup.
It should return true only if the `RefinedDiscrTree` is built and used locally. -/
def mkKey (e : Expr) (config : WhnfCoreConfig)
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (Array Key) :=
  withReducible do (MkKeys.mkKeyAux e true |>.run {config, fvarInContext} |>.run' #[])

/-- Similar to `mkKey`.
Return all encodings of `e` as a `DTExpr`, taking potential further η-reductions into account.
If onlySpecific is `true`, then filter the encodings by whether they are specific. -/
def mkKeys (e : Expr) (config : WhnfCoreConfig) (onlySpecific : Bool)
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (List (Array Key)) :=
  withReducible do
    let es ← (MkKeys.mkKeysAux e true).run {config, fvarInContext} |>.run' (#[],{})
    return if onlySpecific then es.filter isSpecific else es



/-! ### Inserting intro a RefinedDiscrTree -/

/-- If `vs` contains an element `v'` such that `v == v'`, then replace `v'` with `v`.
Otherwise, push `v`.
See issue #2155
Recall that `BEq α` may not be Lawful.
-/
private def insertInArray [BEq α] (vs : Array α) (v : α) : Array α :=
  loop 0
where
  loop (i : Nat) : Array α :=
    if h : i < vs.size then
      if v == vs[i] then
        vs.set ⟨i,h⟩ v
      else
        loop (i+1)
    else
      vs.push v
termination_by vs.size - i

/-- Insert the value `v` at index `keys[i:] : Array Key` in a `Trie`.
For efficiency, we don't compute `keys[i:]`. -/
partial def insertInTrie [BEq α] (keys : Array Key) (i : Nat) (v : α) : Trie α → Trie α
  | .node cs =>
      let k := keys[i]!
      let c := Id.run $ cs.binInsertM
        (·.1 < ·.1)
        (fun (k', s) => (k', insertInTrie keys (i+1) v s))
        (fun _ => (k, Trie.singleton keys[i+1:] v))
        (k, default)
      .node c
  | .values vs =>
      .values (insertInArray vs v)
  | .path ks c => Id.run do
    for n in [:ks.size] do
      let k1 := keys[i+n]!
      let k2 := ks[n]!
      if k1 != k2 then
        let shared := ks[:n]
        let rest := ks[n+1:]
        return .mkPath shared (.mkNode2 k1 (.singleton keys[i+n+1:] v) k2 (.mkPath rest c))
    return .path ks (insertInTrie keys (i + ks.size) v c)

/-- Insert the value `v` at index `keys : Array Key` in a `RefinedDiscrTree`.

Warning: to account for η-reduction, an entry may need to be added at multiple indexes,
so it is recommended to use `RefinedDiscrTree.insert` for insertion. -/
def insertInRefinedDiscrTree [BEq α] (d : RefinedDiscrTree α) (keys : Array Key) (v : α) :
    RefinedDiscrTree α :=
  let k := keys[0]!
  match d.root.find? k with
  | none =>
    let c := .singleton keys[1:] v
    { root := d.root.insert k c }
  | some c =>
    let c := insertInTrie keys 1 v c
    { root := d.root.insert k c }

/-- Insert the value `v` at index `e : DTExpr` in a `RefinedDiscrTree`.

Warning: to account for η-reduction, an entry may need to be added at multiple indexes,
so it is recommended to use `RefinedDiscrTree.insert` for insertion. -/
def insertKeys [BEq α] (d : RefinedDiscrTree α) (keys : Array Key) (v : α) : RefinedDiscrTree α :=
  insertInRefinedDiscrTree d keys v

/-- Insert the value `v` at index `e : Expr` in a `RefinedDiscrTree`.
The argument `fvarInContext` allows you to specify which free variables in `e` will still be
in the context when the `RefinedDiscrTree` is being used for lookup.
It should return true only if the `RefinedDiscrTree` is built and used locally.

if `onlySpecific := true`, then we filter out the patterns `*` and `Eq * * *`. -/
def insert [BEq α] (d : RefinedDiscrTree α) (e : Expr) (v : α)
    (onlySpecific : Bool := true) (config : WhnfCoreConfig := {})
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (RefinedDiscrTree α) := do
  let keys ← mkKeys e config onlySpecific fvarInContext
  return keys.foldl (insertKeys · · v) d

def isPerm (t s : Expr) : Bool := match t, s with
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _   => isPerm d₁ d₂ && isPerm b₁ b₂
    | .lam _ d₁ b₁ _    , .lam _ d₂ b₂ _       => isPerm d₁ d₂ && isPerm b₁ b₂
    | .mdata d₁ e₁      , .mdata d₂ e₂         => d₁ == d₂ && isPerm e₁ e₂
    | .letE _ t₁ v₁ b₁ _, .letE _ t₂ v₂ b₂ _   => isPerm t₁ t₂ && isPerm v₁ v₂ && isPerm b₁ b₂
    | .app f₁ a₁        , .app f₂ a₂           => isPerm f₁ f₂ && isPerm a₁ a₂
    | .proj n₁ i₁ e₁    , .proj n₂ i₂ e₂       => n₁ == n₂ && i₁ == i₂ && isPerm e₁ e₂
    | .mvar _           , .mvar _              => true
    | t                 , s                    => t == s


/-- Insert the value `vlhs` at index `lhs`, and if `rhs` is indexed differently, then also
insert the value `vrhs` at index `rhs`. -/
def insertEqn [BEq α] (d : RefinedDiscrTree α) (lhs rhs : Expr) (vlhs vrhs : α)
    (onlySpecific : Bool := true) (config : WhnfCoreConfig := {})
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (RefinedDiscrTree α) := do
  let keysLhs ← mkKeys lhs config onlySpecific fvarInContext
  let d := keysLhs.foldl (insertKeys · · vlhs) d
  if isPerm lhs rhs then
    return d
  else
    let keysRhs ← mkKeys rhs config onlySpecific fvarInContext
    return keysRhs.foldl (insertKeys · · vrhs) d



/-!
### Matching with a RefinedDiscrTree

We use a very simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` and in the target, we store the assignment, and when it is assigned again,
we check that it is the same assignment.
-/

namespace GetUnify

/-- If `k` is a key in `children`, return the corresponding `Trie α`. Otherwise return `none`. -/
def findKey (children : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  (·.2) <$> children.binSearch (k, default) (·.1 < ·.1)

private structure Context where
  unify  : Bool
  config : WhnfCoreConfig

private structure State where
  /-- Score representing how good the match is. -/
  score : Nat := 0
  /-- Metavariable assignments for the `Key.star` patterns in the `RefinedDiscrTree`. -/
  treeAssignments : HashMap Nat (Array Key) := {}
  /-- Metavariable assignments for the `Expr.mvar` in the expression. -/
  queryAssignments : HashMap Nat (Array Key) := {}


private abbrev M := ReaderT Context $ StateListM State

/-- Return all values from `x` in an array, together with their scores. -/
private def M.run (unify : Bool) (config : WhnfCoreConfig) (x : M (Trie α)) :
    Array (Array α × Nat) :=
  ((x.run { unify, config }).run {}).toArray.map (fun (t, s) => (t.values!, s.score))

/-- Increment the score by `n`. -/
private def incrementScore (n : Nat) : M Unit :=
  modify fun s => { s with score := s.score + n }

/-- Log a metavariable assignment in the `State`, assuming it isn't assigned yet -/
private def assignTreeStar (n : Nat) (keys : Array Key) : M Unit :=
  modify fun s => { s with treeAssignments := s.treeAssignments.insert n keys }

/-- Log a metavariable assignment in the `State`. -/
private def assignQueryStar (id : Nat) (keys : Array Key) : M Unit := do
  let { queryAssignments, .. } ← get
  match queryAssignments.find? id with
  | some keys' => guard (keys == keys')
  | none =>
    modify fun s => { s with queryAssignments := s.queryAssignments.insert id keys }

/-- Return the possible `Trie α` that match with `n` metavariables. -/
partial def skipEntries (t : Trie α) (skipped : Array Key) : Nat → M (Array Key × Trie α)
  | 0      => pure (skipped, t)
  | skip+1 =>
    t.children!.foldr (init := failure) fun (k, c) x =>
      (skipEntries c (skipped.push k) (skip + k.arity)) <|> x

/-- Return the possible `Trie α` that match with anything.
We add 1 to the matching score when the key is `.opaque`,
since this pattern is "harder" to match with. -/
def matchTargetStar (id : Nat) (t : Trie α) : M (Trie α) := do
  let (dropped, t) ← t.children!.foldr (init := failure) fun (k, c) x => (do
    if k == .opaque then
      incrementScore 1
    skipEntries c #[k] k.arity
    ) <|> x
  assignQueryStar id dropped
  return t

private partial def getKeysPrefix (keys : List Key) : List Key × Array Key := Id.run do
  let key :: keys := keys | panic! "too few keys"
  key.arity.fold (init := (keys, #[key])) fun _ (keys, pre) =>
    let (keys, pre') := getKeysPrefix keys;
    (keys, pre ++ pre')

/-- Return the possible `Trie α` that come from a `Key.star`,
while keeping track of the `Key.star` assignments. -/
def matchTreeStars (keys : List Key) (t : Trie α) : M (List Key × Trie α) := do
  let { treeAssignments, .. } ← get
  Id.run do
  let mut result := failure
  let mut getPrefixResult := none
  /- The `Key.star` are at the start of the `t.children!`,
  so this loops through all of them. -/
  for (k, c) in t.children! do
    let .star i := k | break
    let (keys', pre) := getPrefixResult.getD <| getKeysPrefix keys
    getPrefixResult := (keys', pre)
    if let some assignment := treeAssignments.find? i then
      if pre == assignment then
        result := (incrementScore pre.size *> pure (keys', c)) <|> result
    else
      result := (assignTreeStar i pre *> pure (keys', c)) <|> result
  result

mutual
  /-- Return the possible `Trie α` that match with `keys`. -/
  partial def matchExpr (keys : List Key) (t : Trie α) : M (List Key × Trie α) := do
    let key :: keys' := keys | panic! "too few keys"
    if let .star id := key then
      if (← read).unify then
        (keys', ·) <$> matchTargetStar id t
      else
        matchTreeStars keys t
    else
      matchTreeStars keys t <|> exactMatch keys (findKey t.children!)

  /-- Assuming that `keys` is not a metavariable, return the possible `Trie α` that
    exactly match with `keys`. -/
  @[specialize]
  partial def exactMatch (keys : List Key) (find? : Key → Option (Trie α)) : M (List Key × Trie α) := do
    let key :: keys := keys | panic! "too few keys"
    let some trie := find? key | failure
    match key with
      | .opaque => failure
      | .lam => pure ()
      | _ => incrementScore 1
    key.arity.foldM (init := (keys, trie)) fun _ (keys, trie) => matchExpr keys trie
end

private partial def getMatchWithScoreAux (d : RefinedDiscrTree α) (keys : Array Key) (unify : Bool)
    (config : WhnfCoreConfig) (allowRootStar : Bool := false) : Array (Array α × Nat) := (do
  if keys == #[Key.star 0] then
    guard allowRootStar
    d.root.foldl (init := failure) fun x k c => (do
      if k == Key.opaque then
        GetUnify.incrementScore 1
      let (_, t) ← GetUnify.skipEntries c #[k] k.arity
      return t) <|> x
  else
    (Prod.snd <$> GetUnify.exactMatch keys.toList d.root.find?)
    <|> do
    guard allowRootStar
    let some c := d.root.find? (.star 0) | failure
    return c
  ).run unify config

end GetUnify

/--
Return the results from the `RefinedDiscrTree` that match the given expression,
together with their matching scores, in decreasing order of score.

Each entry of type `Array α × Nat` corresponds to one pattern.

If `unify := false`, then unassigned metavariables in `e` are treated as opaque variables.
This is for when you don't want to instantiate metavariables in `e`.

If `allowRootStar := false`, then we don't allow `e` or the matched key in `d`
to be a star pattern. -/
def getMatchWithScore (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig := {}) (allowRootStar := false) : MetaM (Array (Array α × Nat)) := do
  let e ← mkKey e config
  let result := GetUnify.getMatchWithScoreAux d e unify config allowRootStar
  return result.qsort (·.2 > ·.2)

/-- Same as `getMatchWithScore`, but doesn't return the score. -/
def getMatch (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig := {}) (allowRootStar := false) : MetaM (Array (Array α)) :=
  Array.map (·.1) <$> getMatchWithScore d e unify config allowRootStar

/-- Similar to `getMatchWithScore`, but also returns matches with prefixes of `e`.
We store the score, followed by the number of ignored arguments. -/
partial def getMatchWithScoreWithExtra (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig := {}) (allowRootStar := false) :
    MetaM (Array (Array α × Nat × Nat)) := do
  let result ← go e 0
  return result.qsort (·.2.1 > ·.2.1)
where
  /-- Auxiliary function for `getMatchWithScoreWithExtra` -/
  go (e : Expr) (numIgnored : Nat) : MetaM (Array (Array α × Nat × Nat)) := do
  let result ← getMatchWithScore d e unify config allowRootStar
  let result := result.map fun (a, b) => (a, b, numIgnored)
  match e with
  | .app e _ => return (← go e (numIgnored + 1)) ++ result
  | _ => return result


variable {β : Type} {m : Type → Type} [Monad m]

/-- Apply a monadic function to the array of values at each node in a `RefinedDiscrTree`. -/
partial def Trie.mapArraysM (t : RefinedDiscrTree.Trie α) (f : Array α → m (Array β)) :
    m (Trie β) := do
  match t with
  | .node children =>
    return .node (← children.mapM fun (k, t') => do pure (k, ← t'.mapArraysM f))
  | .values vs =>
    return .values (← f vs)
  | .path ks c =>
    return .path ks (← c.mapArraysM f)

/-- Apply a monadic function to the array of values at each node in a `RefinedDiscrTree`. -/
def mapArraysM (d : RefinedDiscrTree α) (f : Array α → m (Array β)) : m (RefinedDiscrTree β) :=
  return { root := ← d.root.mapM (·.mapArraysM f) }

/-- Apply a function to the array of values at each node in a `RefinedDiscrTree`. -/
def mapArrays (d : RefinedDiscrTree α) (f : Array α → Array β) : RefinedDiscrTree β :=
  d.mapArraysM (m := Id) f
