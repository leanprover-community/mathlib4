/-
Copyright (c) 2023 J. W. Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: J. W. Gerbscheid
-/
import Mathlib.Tactic.FunProp.StateList
import Mathlib.Algebra.Group.Pi.Basic

/-!
We define discrimination trees for the purpose of unifying local expressions with library results.

This structure is based on `Lean.Meta.DiscrTree`.
I document here what features are not in the original:

- The keys `Key.lam`, `Key.forall` and `Key.bvar` have been introduced in order to allow for
  matching under lambda and forall binders. `Key.lam` has arity 1 and indexes the body.
  `Key.forall` has arity 2 and indexes the domain and the body. The reason for not indexing the
  domain of a lambda expression is that it is usually already determined, for example in
  `∃ a : α, p`, which is `@Exists α fun a : α => p`, we don't want to index the domain `α` twice.
  In a forall expression it is necessary to index the domain, because in an implication `p → q`
  we need to index both `p` and `q`. `Key.bvar` works the same as `Key.fvar`, but stores the
  De Bruijn index to identify it.

  For example, this allows for more specific matching with the left hand side of
  `∑ i ∈ range n, i = n * (n - 1) / 2`, which is indexed by
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

- We keep track of the matching score of a unification.
  This score represents the number of keys that had to be the same for the unification to succeed.
  For example, matching `(1 + 2) + 3` with `add_comm` gives a score of 2,
  since the pattern of commutativity is [⟨HAdd.hAdd, 6⟩, *0, *0, *0, *1, *2, *3],
  so matching `⟨HAdd.hAdd, 6⟩` gives 1 point,
  and matching `*0` after its first appearence gives another point, but the third argument is an
  outParam, so this gets ignored. Similarly, matching it with `add_assoc` gives a score of 5.

- Patterns that have the potential to be η-reduced are put into the `RefinedDiscrTree` under all
  possible reduced key sequences. This is for terms of the form `fun x => f (?m x₁ .. xₙ)`, where
  `?m` is a metavariable, and one of `x₁, .., xₙ` in `x`.
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
    - This makes lemmata such as `continuous_id'` redundant, which is the same as `continuous_id`,
      with `id` replaced by `fun x => x`.
  - Any expressions involving `+`, `*`, `-`, `/` or `⁻¹` is normalized to not have a lambda
    in front and to always have the default amount of arguments.
    e.g. `(f + g) a` is stored as `f a + g a` and `fun x => f x + g x` is stored as `f + g`.
    - This makes lemmata such as `MeasureTheory.integral_integral_add'` redundant, which is the
      same as `MeasureTheory.integral_integral_add`, with `f a + g a` replaced by `(f + g) a`
    - it also means that a lemma like `Continuous.mul` can be stated as talking about `f * g`
      instead of `fun x => f x + g x`.

I have also made some changes in the implementation:

- Instead of directly converting from `Expr` to `Array Key` during insertion, and directly
  looking up from an `Expr` during lookup, I defined the intermediate structure `DTExpr`,
  which is a form of `Expr` that only contains information relevant for the discrimination tree.
  Each `Expr` is transformed into a `DTExpr` before insertion or lookup. For insertion there
  could be multiple `DTExpr` representations due to potential η-reductions as mentioned above.

TODO:

- More thought could be put into the matching algorithm for non-trivial unifications.
  For example, when looking up the expression `?a + ?a` (for rewriting), there will only be
  results like `n + n = 2 * n` or `a + b = b + a`, but not like `n + 1 = n.succ`,
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

namespace Mathlib.Meta.FunProp.RefinedDiscrTree

/-! ## Definitions -/

/-- Discrimination tree key. -/
inductive Key where
  /-- A metavariable. This key matches with anything. It stores an index. -/
  | star : Nat → Key
  /-- An opaque variable. This key only matches with itself or `Key.star`. -/
  | opaque : Key
  /-- A constant. It stores the name and the arity. -/
  | const : Name → Nat → Key
  /-- A free variable. It stores the `FVarId` and the arity. -/
  | fvar : FVarId → Nat → Key
  /-- A bound variable, from a lambda or forall binder.
  It stores the De Bruijn index and the arity. -/
  | bvar : Nat → Nat → Key
  /-- A literal. -/
  | lit : Literal → Key
  /-- A sort. Universe levels are ignored. -/
  | sort : Key
  /-- A lambda function. -/
  | lam : Key
  /-- A dependent arrow. -/
  | forall : Key
  /-- A projection. It stores the structure name, the projection index and the arity. -/
  | proj : Name → Nat → Nat → Key
  deriving Inhabited, BEq, Repr

private nonrec def Key.hash : Key → UInt64
  | .star i     => mixHash 7883 $ hash i
  | .opaque     => 342
  | .const n a  => mixHash 5237 $ mixHash (hash n) (hash a)
  | .fvar  n a  => mixHash 8765 $ mixHash (hash n) (hash a)
  | .bvar i a   => mixHash 4323 $ mixHash (hash i) (hash a)
  | .lit v      => mixHash 1879 $ hash v
  | .sort       => 2411
  | .lam        => 4742
  | .«forall»   => 9752
  | .proj s i a => mixHash (hash a) $ mixHash (hash s) (hash i)

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
  | .star i₁,       .star i₂       => i₁ < i₂
  | .const n₁ a₁,   .const n₂ a₂   => Name.quickLt n₁ n₂ || (n₁ == n₂ && a₁ < a₂)
  | .fvar f₁ a₁,    .fvar f₂ a₂    => Name.quickLt f₁.name f₂.name || (f₁ == f₂ && a₁ < a₂)
  | .bvar i₁ a₁,    .bvar i₂ a₂    => i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)
  | .lit v₁,        .lit v₂        => v₁ < v₂
  | .proj s₁ i₁ a₁, .proj s₂ i₂ a₂ => Name.quickLt s₁ s₂ ||
    (s₁ == s₂ && (i₁ < i₂ || (i₁ == i₂ && a₁ < a₂)))
  | k₁,             k₂             => k₁.ctorIdx < k₂.ctorIdx

instance : LT Key := ⟨fun a b => Key.lt a b⟩
instance (a b : Key) : Decidable (a < b) := inferInstanceAs (Decidable (Key.lt a b))

private def Key.format : Key → Format
  | .star i                 => "*" ++ Std.format i
  | .opaque                 => "◾"
  | .const k a              => "⟨" ++ Std.format k ++ ", " ++ Std.format a ++ "⟩"
  | .fvar k a               => "⟨" ++ Std.format k.name ++ ", " ++ Std.format a ++ "⟩"
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .sort                   => "sort"
  | .bvar i a               => "⟨" ++ "#" ++ Std.format i ++ ", " ++ Std.format a ++ "⟩"
  | .lam                    => "λ"
  | .forall                 => "∀"
  | .proj s i a             => "⟨" ++ Std.format s ++"."++ Std.format i ++", "++ Std.format a ++ "⟩"

instance : ToFormat Key := ⟨Key.format⟩

/-- Return the number of arguments that the `Key` takes. -/
def Key.arity : Key → Nat
  | .const _ a  => a
  | .fvar _ a   => a
  | .bvar _ a   => a
  | .lam        => 1
  | .forall     => 2
  | .proj _ _ a => 1 + a
  | _           => 0

variable {α : Type}
/-- Discrimination tree trie. See `RefinedDiscrTree`. -/
inductive Trie (α : Type) where
  /-- Map from `Key` to `Trie`. Children is an `Array` of size at least 2,
  sorted in increasing order using `Key.lt`. -/
  | node (children : Array (Key × Trie α))
  /-- Sequence of nodes with only one child. `keys` is an `Array` of size at least 1. -/
  | path (keys : Array Key) (child : Trie α)
  /-- Leaf of the Trie. `values` is an `Array` of size at least 1. -/
  | values (vs : Array α)
instance : Inhabited (Trie α) := ⟨.node #[]⟩

/-- `Trie.path` constructor that only inserts the path if it is non-empty. -/
def Trie.mkPath (keys : Array Key) (child : Trie α) :=
  if keys.isEmpty then child else Trie.path keys child

/-- `Trie` constructor for a single value, taking the keys starting at index `i`. -/
def Trie.singleton (keys : Array Key) (value : α) (i : Nat) : Trie α :=
  mkPath keys[i:] (values #[value])

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


/-- Discrimination tree. It is an index from expressions to values of type `α`. -/
structure _root_.Mathlib.Meta.FunProp.RefinedDiscrTree (α : Type) where
  /-- The underlying `PersistentHashMap` of a `RefinedDiscrTree`. -/
  root : PersistentHashMap Key (Trie α) := {}
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


/-- `DTExpr` is a simplified form of `Expr`.
It is the intermediate step for converting from `Expr` to `Array Key`. -/
inductive DTExpr where
  /-- A metavariable. It optionally stores an `MVarId`. -/
  | star : Option MVarId → DTExpr
  /-- An opaque variable or a let-expression in the case `WhnfCoreConfig.zeta := false`. -/
  | opaque : DTExpr
  /-- A constant. It stores the name and the arguments. -/
  | const : Name → Array DTExpr → DTExpr
  /-- A free variable. It stores the `FVarId` and the argumenst -/
  | fvar : FVarId → Array DTExpr → DTExpr
  /-- A bound variable. It stores the De Bruijn index and the arguments -/
  | bvar : Nat → Array DTExpr → DTExpr
  /-- A literal. -/
  | lit : Literal → DTExpr
  /-- A sort. -/
  | sort : DTExpr
  /-- A lambda function. It stores the body. -/
  | lam : DTExpr → DTExpr
  /-- A dependent arrow. It stores the domain and body. -/
  | forall : DTExpr → DTExpr → DTExpr
  /-- A projection. It stores the structure name, projection index, struct body and arguments. -/
  | proj : Name → Nat → DTExpr → Array DTExpr → DTExpr
deriving Inhabited, BEq, Repr

private partial def DTExpr.format : DTExpr → Format
  | .star _                 => "*"
  | .opaque                 => "◾"
  | .const n as             => Std.format n ++ formatArgs as
  | .fvar n as              => Std.format n.name ++ formatArgs as
  | .bvar i as              => "#" ++ Std.format i  ++ formatArgs as
  | .lit (Literal.natVal v) => Std.format v
  | .lit (Literal.strVal v) => repr v
  | .sort                   => "Sort"
  | .lam b                  => "λ " ++ DTExpr.format b
  | .forall d b             => DTExpr.format d ++ " → " ++ DTExpr.format b
  | .proj _ i a as          => DTExpr.format a ++ "." ++ Std.format i ++ formatArgs as
where
  formatArgs (as : Array DTExpr) :=
    if as.isEmpty
      then .nil
      else " " ++ Format.paren (@Format.joinSep _ ⟨DTExpr.format⟩ as.toList ", ")

instance : ToFormat DTExpr := ⟨DTExpr.format⟩

/-- Return the size of the `DTExpr`. This is used for calculating the matching score when two
expressions are equal.
The score is not incremented at a lambda, which is so that the expressions
`∀ x, p[x]` and `∃ x, p[x]` get the same size. -/
partial def DTExpr.size : DTExpr → Nat
| .const _ args
| .fvar _ args
| .bvar _ args => args.foldl (init := 1) (· + ·.size)
| .lam b => b.size
| .forall d b => 1 + d.size + b.size
| _ => 1

private def DTExpr.eqv (a b : DTExpr) : Bool :=
  (go a b).run' {}
where
  go (a b : DTExpr) : StateM (HashMap MVarId MVarId) Bool :=
    match a, b with
    | .opaque           , .opaque            => pure true
    | .const n₁ as₁     , .const n₂ as₂      => pure (n₁ == n₂) <&&> goArray as₁ as₂
    | .fvar n₁ as₁      , .fvar n₂ as₂       => pure (n₁ == n₂) <&&> goArray as₁ as₂
    | .bvar i₁ as₁      , .bvar i₂ as₂       => pure (i₁ == i₂) <&&> goArray as₁ as₂
    | .lit li₁          , .lit li₂           => pure (li₁ == li₂)
    | .sort             , .sort              => pure true
    | .lam b₁           , .lam b₂            => go b₁ b₂
    | .forall d₁ b₁     , .forall d₂ b₂      => go d₁ d₂ <&&> go b₁ b₂
    | .proj n₁ i₁ a₁ as₁, .proj n₂ i₂ a₂ as₂ => pure (n₁ == n₂ && i₁ == i₂)
                                            <&&> go a₁ a₂ <&&> goArray as₁ as₂
    | .star none        , .star none         => pure true
    | .star (some id₁)  , .star (some id₂)   => modifyGet fun map => match map.find? id₁ with
      | some id => (id == id₂, map)
      | none => (true, map.insert id₁ id₂)
    | _ , _ => return false

  goArray (as bs : Array DTExpr) : StateM (HashMap MVarId MVarId) Bool := do
    if h : as.size = bs.size then
      for g : i in [:as.size] do
        unless ← go as[i] (bs[i]'(h ▸ g.2)) do
          return false
      return true
    else
      return false

/-! ## Encoding an Expr -/

/-- This state is used to turn the indexing by `MVarId` and `FVarId` in `DTExpr` into
indexing by `Nat` in `Key`. -/
private structure Flatten.State where
  stars : Array MVarId := #[]

private def getStar (mvarId? : Option MVarId) : StateM Flatten.State Nat :=
  modifyGet fun s =>
    match mvarId? with
    | some mvarId => match s.stars.findIdx? (· == mvarId) with
      | some idx => (idx, s)
      | none => (s.stars.size, { s with stars := s.stars.push mvarId })
    | none => (s.stars.size, { s with stars := s.stars.push ⟨.anonymous⟩ })

private partial def DTExpr.flattenAux (todo : Array Key) : DTExpr → StateM Flatten.State (Array Key)
  | .star i => return todo.push (.star (← getStar i))
  | .opaque => return todo.push .opaque
  | .const n as => as.foldlM flattenAux (todo.push (.const n as.size))
  | .fvar  f as => as.foldlM flattenAux (todo.push (.fvar f as.size))
  | .bvar  i as => as.foldlM flattenAux (todo.push (.bvar i as.size))
  | .lit l => return todo.push (.lit l)
  | .sort  => return todo.push .sort
  | .lam b => flattenAux (todo.push .lam) b
  | .«forall» d b => do flattenAux (← flattenAux (todo.push .forall) d) b
  | .proj n i e as => do as.foldlM flattenAux (← flattenAux (todo.push (.proj n i as.size)) e)

/-- Given a `DTExpr`, return the linearized encoding in terms of `Key`,
which is used for `RefinedDiscrTree` indexing. -/
def DTExpr.flatten (e : DTExpr) (initCapacity := 16) : Array Key :=
  (DTExpr.flattenAux (.mkEmpty initCapacity) e).run' {}



/-- Return true if `e` is one of the following
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

/-- Reduction procedure for the `RefinedDiscrTree` indexing. -/
partial def reduce (e : Expr) (config : WhnfCoreConfig) : MetaM Expr := do
  let e ← whnfCore e config
  match (← unfoldDefinition? e) with
  | some e => reduce e config
  | none => match e.etaExpandedStrict? with
    | some e => reduce e config
    | none   => return e

/-- Repeatedly apply reduce while stripping lambda binders and introducing their variables -/
@[specialize]
partial def lambdaTelescopeReduce {m} [Monad m] [MonadLiftT MetaM m] [MonadControlT MetaM m]
    [Inhabited α] (e : Expr) (fvars : List FVarId) (config : WhnfCoreConfig)
    (k : Expr → List FVarId → m α) : m α := do
  match ← reduce e config with
  | .lam n d b bi =>
    withLocalDecl n bi d fun fvar =>
      lambdaTelescopeReduce (b.instantiate1 fvar) (fvar.fvarId! :: fvars) config k
  | e => k e fvars



/-- Check whether the expression is represented by `Key.star`. -/
def isStar : Expr → Bool
  | .mvar .. => true
  | .app f _ => isStar f
  | _ => false

/-- Check whether the expression is represented by `Key.star` and has `arg` as an argument. -/
def isStarWithArg (arg : Expr) : Expr → Bool
  | .app f a => if a == arg then isStar f else isStarWithArg arg f
  | _ => false

private partial def DTExpr.hasLooseBVarsAux (i : Nat) : DTExpr → Bool
  | .const  _ as   => as.any (hasLooseBVarsAux i)
  | .fvar   _ as   => as.any (hasLooseBVarsAux i)
  | .bvar j as     => j ≥ i || as.any (hasLooseBVarsAux i)
  | .proj _ _ a as => a.hasLooseBVarsAux i || as.any (hasLooseBVarsAux i)
  | .forall d b    => d.hasLooseBVarsAux i || b.hasLooseBVarsAux (i+1)
  | .lam b         => b.hasLooseBVarsAux (i+1)
  | _              => false

/-- Return `true` if `e` contains a loose bound variable. -/
def DTExpr.hasLooseBVars (e : DTExpr) : Bool :=
  e.hasLooseBVarsAux 0


namespace MkDTExpr

private structure Context where
  /-- Variables that come from a lambda or forall binder.
  The list index gives the De Bruijn index. -/
  bvars : List FVarId := []
  /-- Variables that come from a lambda that has been removed via η-reduction. -/
  forbiddenVars : List FVarId := []
  config : WhnfCoreConfig
  fvarInContext : FVarId → Bool

/-- Return for each argument whether it should be ignored. -/
def getIgnores (fn : Expr) (args : Array Expr) : MetaM (Array Bool) := do
  let mut fnType ← inferType fn
  let mut result := Array.mkEmpty args.size
  let mut j := 0
  for i in [:args.size] do
    unless fnType matches .forallE .. do
      fnType ← whnfD (fnType.instantiateRevRange j i args)
      j := i
    let .forallE _ d b bi := fnType | throwError m! "expected function type {indentExpr fnType}"
    fnType := b
    result := result.push (← isIgnoredArg args[i]! d bi)
  return result
where
  /-- Return whether the argument should be ignored. -/
  isIgnoredArg (arg domain : Expr) (binderInfo : BinderInfo) : MetaM Bool := do
    if domain.isOutParam then
      return true
    match binderInfo with
    | .instImplicit => return true
    | .implicit
    | .strictImplicit => return !(← isType arg)
    | .default => isProof arg



/-- Introduce new lambdas by η-expansion. -/
@[specialize]
def etaExpand (args : Array Expr) (type : Expr) (lambdas : List FVarId) (goalArity : Nat)
    (k : Array Expr → List FVarId → MetaM α) : MetaM α  := do
  if args.size < goalArity then
    withLocalDeclD `_η type fun fvar =>
      etaExpand (args.push fvar) type (fvar.fvarId! :: lambdas) goalArity k
  else
    k args lambdas
termination_by goalArity - args.size


/-- Normalize an application of a heterogenous binary operator like `HAdd.hAdd`, using:
- `f = fun x => f x` to increase the arity to 6
- `(f + g) a = f a + g a` to decrease the arity to 6
- `(fun x => f x + g x) = f + g` to get rid of any lambdas in front -/
def reduceHBinOpAux (args : Array Expr) (lambdas : List FVarId) (instH instPi : Name) :
    OptionT MetaM (Expr × Expr × Expr × List FVarId) := do
  let some (mkApp2 (.const instH' _) type inst) := args[3]? | failure
  guard (instH == instH')
  if args.size ≤ 6 then
    etaExpand args type lambdas 6 fun args lambdas =>
      distributeLambdas lambdas type args[4]! args[5]!
  else
  /- use that `(f + g) a = f a + g a` -/
  let mut type := type
  let mut inst := inst
  let mut lhs := args[4]!
  let mut rhs := args[5]!
  for arg in args[6:] do
    let mkApp3 (.const i _) _ f inst' := inst | return (type, lhs, rhs, lambdas)
    unless i == instPi do return (type, lhs, rhs, lambdas)
    type := .app f arg
    inst := inst'
    lhs := .app lhs arg
    rhs := .app rhs arg
  distributeLambdas lambdas type lhs rhs
where
  /-- use that `(fun x => f x + g x) = f + g` -/
  distributeLambdas (lambdas : List FVarId) (type lhs rhs : Expr) :
    MetaM (Expr × Expr × Expr × List FVarId) := match lambdas with
    | fvarId :: lambdas => do
      let decl ← fvarId.getDecl
      let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
      let lhs  := .lam     decl.userName decl.type (lhs.abstract  #[.fvar fvarId]) decl.binderInfo
      let rhs  := .lam     decl.userName decl.type (rhs.abstract  #[.fvar fvarId]) decl.binderInfo
      distributeLambdas lambdas type lhs rhs
    | [] => return (type, lhs, rhs, [])

/-- Normalize an application if the head is  `+`, `*`, `-` or `/`.
Optionally return the `(type, lhs, rhs, lambdas)`. -/
@[inline] def reduceHBinOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × Expr × Expr × List FVarId)) :=
  match n with
  | ``HAdd.hAdd => reduceHBinOpAux args lambdas ``instHAdd ``Pi.instAdd
  | ``HMul.hMul => reduceHBinOpAux args lambdas ``instHMul ``Pi.instMul
  | ``HSub.hSub => reduceHBinOpAux args lambdas ``instHSub ``Pi.instSub
  | ``HDiv.hDiv => reduceHBinOpAux args lambdas ``instHDiv ``Pi.instDiv
  | _ => return none

/-- Normalize an application of a unary operator like `Inv.inv`, using:
- `f⁻¹ a = (f a)⁻¹` to decrease the arity to 3
- `(fun x => (f a)⁻¹) = f⁻¹` to get rid of any lambdas in front -/
def reduceUnOpAux (args : Array Expr) (lambdas : List FVarId) (instPi : Name) :
    OptionT MetaM (Expr × Expr × List FVarId) := do
  guard (args.size ≥ 3)
  let mut type := args[0]!
  let mut inst := args[1]!
  let mut arg := args[2]!
  if args.size == 3 then
    distributeLambdas lambdas type arg
  else
  /- use that `f⁻¹ a = (f a)⁻¹` -/
  for arg' in args[3:] do
    let mkApp3 (.const i _) _ f inst' := inst | return (type, arg, lambdas)
    unless i == instPi do return (type, arg, lambdas)
    type := .app f arg'
    inst := inst'
    arg := .app arg arg'
  distributeLambdas lambdas type arg
where
  /-- use that `(fun x => (f x)⁻¹) = f⁻¹` -/
  distributeLambdas (lambdas : List FVarId) (type arg : Expr) :
    MetaM (Expr × Expr × List FVarId) := match lambdas with
    | fvarId :: lambdas => do
      let decl ← fvarId.getDecl
      let type := .forallE decl.userName decl.type (type.abstract #[.fvar fvarId]) decl.binderInfo
      let arg  := .lam     decl.userName decl.type (arg.abstract  #[.fvar fvarId]) decl.binderInfo
      distributeLambdas lambdas type arg
    | [] => return (type, arg, [])

/-- Normalize an application if the head is `⁻¹` or `-`.
Optionally return the `(type, arg, lambdas)`. -/
@[inline] def reduceUnOp (n : Name) (args : Array Expr) (lambdas : List FVarId) :
    MetaM (Option (Expr × Expr × List FVarId)) :=
  match n with
  | ``Neg.neg => reduceUnOpAux args lambdas ``Pi.instNeg
  | ``Inv.inv => reduceUnOpAux args lambdas ``Pi.instInv
  | _ => return none

@[specialize]
private def withLams {m} [Monad m] [MonadWithReader Context m]
    (lambdas : List FVarId) (k : m DTExpr) : m DTExpr :=
  if lambdas.isEmpty then
    k
  else do
    let e ← withReader (fun c => { c with bvars := lambdas ++ c.bvars }) k
    return lambdas.foldl (fun _ => ·.lam) e


/-- Return the encoding of `e` as a `DTExpr`.
If `root = false`, then `e` is a strict sub expression of the original expression. -/
partial def mkDTExprAux (e : Expr) (root : Bool) : ReaderT Context MetaM DTExpr := do
  lambdaTelescopeReduce e [] (← read).config fun e lambdas =>
  e.withApp fun fn args => do

  let argDTExpr (arg : Expr) (ignore : Bool) : ReaderT Context MetaM DTExpr :=
    if ignore then pure (.star none) else mkDTExprAux arg false

  let argDTExprs : ReaderT Context MetaM (Array DTExpr) := do
    let ignores ← getIgnores fn args
    args.mapIdxM fun i arg =>
      argDTExpr arg ignores[i]!

  match fn with
  | .const n _ =>
    unless root do
      if let some (type, lhs, rhs, lambdas') ← reduceHBinOp n args lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprAux type false
          let lhs ← mkDTExprAux lhs false
          let rhs ← mkDTExprAux rhs false
          return .const n #[type, type, .star none, .star none, lhs, rhs]

      if let some (type, arg, lambdas') ← reduceUnOp n e.getAppArgs lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprAux type false
          let arg ← mkDTExprAux arg false
          return .const n #[type, .star none, arg]

      /- since `(fun _ => 0) = 0` and `(fun _ => 1) = 1`,
      we don't index lambdas before literals -/
      if let some v := toNatLit? e then
        return .lit v
    withLams lambdas do
      return .const n (← argDTExprs)
  | .proj s i a =>
    withLams lambdas do
      let a ← argDTExpr a (isClass (← getEnv) s)
      return .proj s i a (← argDTExprs)
  | .fvar fvarId =>
    /- we index `fun x => x` as `id` when not at the root -/
    if let fvarId' :: lambdas' := lambdas then
      if fvarId' == fvarId && args.isEmpty && !root then
        return ← withLams lambdas' do
          let type ← mkDTExprAux (← fvarId.getType) false
          return .const ``id #[type]
    withLams lambdas do
      if let some idx := (← read).bvars.findIdx? (· == fvarId) then
        return .bvar idx (← argDTExprs)
      if (← read).fvarInContext fvarId then
        return .fvar fvarId (← argDTExprs)
      else
        return .opaque
  | .mvar mvarId =>
    /- When the mvarId has arguments, index it with `[*]` instead of `[λ,*]`,
    because the star could depend on the bound variables. As a result,
    something indexed `[λ,*]` has that the `*` cannot depend on the λ-bound variables -/
    if args.isEmpty then
      withLams lambdas do return .star (some mvarId)
    else
      return .star none

  | .forallE n d b bi =>
    withLams lambdas do
      let d' ← mkDTExprAux d false
      let b' ← withLocalDecl n bi d fun fvar =>
        withReader (fun c => { c with bvars := fvar.fvarId! :: c.bvars }) do
          mkDTExprAux (b.instantiate1 fvar) false
      return .forall d' b'
  | .lit v      => withLams lambdas do return .lit v
  | .sort _     => withLams lambdas do return .sort
  | .letE ..    => withLams lambdas do return .opaque
  | .lam ..     => withLams lambdas do return .opaque
  | _           => unreachable!


private abbrev M := StateListT (AssocList Expr DTExpr) $ ReaderT Context MetaM

/-
Caching values is a bit dangerous, because when two expressions are be equal and they live under
a different number of binders, then the resulting De Bruijn indices are offset.
In practice, getting a `.bvar` in a `DTExpr` is very rare, so we exclude such values from the cache.
-/
instance : MonadCache Expr DTExpr M where
  findCached? e := do
    let s ← get
    return s.find? e
  cache e e' :=
    if e'.hasLooseBVars then
      return
    else
      modify (·.insert e e')

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
    (k : Expr → List FVarId → M DTExpr) : M DTExpr :=
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
partial def mkDTExprsAux (original : Expr) (root : Bool) : M DTExpr := do
  lambdaTelescopeReduce original [] (← read).config fun e lambdas => do

  if !root then
    if let .const n _ := e.getAppFn then
      if let some (type, lhs, rhs, lambdas') ← reduceHBinOp n e.getAppArgs lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprsAux type false
          let lhs ← mkDTExprsAux lhs false
          let rhs ← mkDTExprsAux rhs false
          return .const n #[type, type, .star none, .star none, lhs, rhs]

      if let some (type, arg, lambdas') ← reduceUnOp n e.getAppArgs lambdas then
        return ← withLams lambdas' do
          let type ← mkDTExprsAux type false
          let arg ← mkDTExprsAux arg false
          return .const n #[type, .star none, arg]

  cacheEtaPossibilities e original lambdas fun e lambdas =>
  e.withApp fun fn args => do

  let argDTExpr (arg : Expr) (ignore : Bool) : M DTExpr :=
    if ignore then pure (.star none) else mkDTExprsAux arg false

  let argDTExprs : M (Array DTExpr) := do
    let ignores ← getIgnores fn args
    args.mapIdxM fun i arg =>
      argDTExpr arg ignores[i]!

  match fn with
  | .const n _ =>
      unless root do
        /- since `(fun _ => 0) = 0` and `(fun _ => 1) = 1`,
        we don't index lambdas before nat literals -/
        if let some v := toNatLit? e then
          return .lit v
      withLams lambdas do
        return .const n (← argDTExprs)
  | .proj s i a =>
    withLams lambdas do
    let a ← argDTExpr a (isClass (← getEnv) s)
    return .proj s i a (← argDTExprs)
  | .fvar fvarId =>
    /- we index `fun x => x` as `id` when not at the root -/
    if let fvarId' :: lambdas' := lambdas then
      if fvarId' == fvarId && args.isEmpty && !root then
        return ← withLams lambdas' do
          let type ← mkDTExprAux (← fvarId.getType) false
          return .const ``id #[type]
    withLams lambdas do
      let c ← read
      if let some idx := c.bvars.findIdx? (· == fvarId) then
        return .bvar idx (← argDTExprs)
      guard !(c.forbiddenVars.contains fvarId)
      if c.fvarInContext fvarId then
        return .fvar fvarId (← argDTExprs)
      else
        return .opaque
  | .mvar mvarId =>
    /- When the mvarId has arguments, index it with `[*]` instead of `[λ,*]`,
    because the star could depend on the bound variables. As a result,
    something indexed `[λ,*]` has that the `*` cannot depend on the λ-bound variables -/
    if args.isEmpty then
      withLams lambdas do return .star (some mvarId)
    else
      return .star none

  | .forallE n d b bi =>
    withLams lambdas do
    let d' ← mkDTExprsAux d false
    let b' ← withLocalDecl n bi d fun fvar =>
      withReader (fun c => { c with bvars := fvar.fvarId! :: c.bvars }) do
        mkDTExprsAux (b.instantiate1 fvar) false
    return .forall d' b'
  | .lit v      => withLams lambdas do return .lit v
  | .sort _     => withLams lambdas do return .sort
  | .letE ..    => withLams lambdas do return .opaque
  | .lam ..     => withLams lambdas do return .opaque
  | _           => unreachable!

end MkDTExpr

/--  -/
def DTExpr.isSpecific : DTExpr → Bool
  | .star _
  | .const ``Eq #[.star _, .star _, .star _] => false
  | _ => true

/-- Return the encoding of `e` as a `DTExpr`.

Warning: to account for potential η-reductions of `e`, use `mkDTExprs` instead.

The argument `fvarInContext` allows you to specify which free variables in `e` will still be
in the context when the `RefinedDiscrTree` is being used for lookup.
It should return true only if the `RefinedDiscrTree` is built and used locally. -/
def mkDTExpr (e : Expr) (config : WhnfCoreConfig)
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM DTExpr :=
  withReducible do (MkDTExpr.mkDTExprAux e true |>.run {config, fvarInContext})

/-- Similar to `mkDTExpr`.
Return all encodings of `e` as a `DTExpr`, taking potential further η-reductions into account. -/
def mkDTExprs (e : Expr) (config : WhnfCoreConfig) (onlySpecific : Bool)
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (List DTExpr) :=
  withReducible do
    let es ← (MkDTExpr.mkDTExprsAux e true).run' {} |>.run {config, fvarInContext}
    return if onlySpecific then es.filter (·.isSpecific) else es


/-! ## Inserting intro a RefinedDiscrTree -/

variable {α : Type}

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

/-- Insert the value `v` at index `keys : Array Key` in a `Trie`. -/
partial def insertInTrie [BEq α] (keys : Array Key) (v : α) (i : Nat) : Trie α → Trie α
  | .node cs =>
      let k := keys[i]!
      let c := Id.run $ cs.binInsertM
        (fun a b => a.1 < b.1)
        (fun (k', s) => (k', insertInTrie keys v (i+1) s))
        (fun _ => (k, Trie.singleton keys v (i+1)))
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
        return .mkPath shared (.mkNode2 k1 (.singleton keys v (i+n+1)) k2 (.mkPath rest c))
    return .path ks (insertInTrie keys v (i + ks.size) c)

/-- Insert the value `v` at index `keys : Array Key` in a `RefinedDiscrTree`.

Warning: to accound for η-reduction, an entry may need to be added at multiple indexes,
so it is recommended to use `RefinedDiscrTree.insert` for insertion. -/
def insertInRefinedDiscrTree [BEq α] (d : RefinedDiscrTree α) (keys : Array Key) (v : α) :
    RefinedDiscrTree α :=
  let k := keys[0]!
  match d.root.find? k with
  | none =>
    let c := .singleton keys v 1
    { root := d.root.insert k c }
  | some c =>
    let c := insertInTrie keys v 1 c
    { root := d.root.insert k c }

/-- Insert the value `v` at index `e : DTExpr` in a `RefinedDiscrTree`.

Warning: to accound for η-reduction, an entry may need to be added at multiple indexes,
so it is recommended to use `RefinedDiscrTree.insert` for insertion. -/
def insertDTExpr [BEq α] (d : RefinedDiscrTree α) (e : DTExpr) (v : α) : RefinedDiscrTree α :=
  insertInRefinedDiscrTree d e.flatten v

/-- Insert the value `v` at index `e : Expr` in a `RefinedDiscrTree`.
The argument `fvarInContext` allows you to specify which free variables in `e` will still be
in the context when the `RefinedDiscrTree` is being used for lookup.
It should return true only if the `RefinedDiscrTree` is built and used locally.

if `onlySpecific := true`, then we filter out the patterns `*` and `Eq * * *`. -/
def insert [BEq α] (d : RefinedDiscrTree α) (e : Expr) (v : α)
    (onlySpecific : Bool := true) (config : WhnfCoreConfig := {})
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (RefinedDiscrTree α) := do
  let keys ← mkDTExprs e config onlySpecific fvarInContext
  return keys.foldl (insertDTExpr · · v) d

/-- Insert the value `vLhs` at index `lhs`, and if `rhs` is indexed differently, then also
insert the value `vRhs` at index `rhs`. -/
def insertEqn [BEq α] (d : RefinedDiscrTree α) (lhs rhs : Expr) (vLhs vRhs : α)
    (onlySpecific : Bool := true) (config : WhnfCoreConfig := {})
    (fvarInContext : FVarId → Bool := fun _ => false) : MetaM (RefinedDiscrTree α) := do
  let keysLhs ← mkDTExprs lhs config onlySpecific fvarInContext
  let keysRhs ← mkDTExprs rhs config onlySpecific fvarInContext
  let d := keysLhs.foldl (insertDTExpr · · vLhs) d
  if @List.beq _ ⟨DTExpr.eqv⟩ keysLhs keysRhs then
    return d
  else
    return keysRhs.foldl (insertDTExpr · · vRhs) d



/-! ## Matching with a RefinedDiscrTree

We use a very simple unification algorithm. For all star/metavariable patterns in the
`RefinedDiscrTree` and in the target, we store the assignment, and when it is assigned again,
we check that it is the same assignment.
-/

namespace GetUnify

/-- If `k` is a key in `children`, return the corresponding `Trie α`. Otherwise return `none`. -/
def findKey (children : Array (Key × Trie α)) (k : Key) : Option (Trie α) :=
  (·.2) <$> children.binSearch (k, default) (fun a b => a.1 < b.1)

private structure Context where
  unify : Bool
  config : WhnfCoreConfig

private structure State where
  /-- Score representing how good the match is. -/
  score : Nat := 0
  /-- Metavariable assignments for the `Key.star` patterns in the `RefinedDiscrTree`. -/
  starAssignments : HashMap Nat DTExpr := {}
  /-- Metavariable assignments for the `Expr.mvar` in the expression. -/
  mvarAssignments : HashMap MVarId (Array Key) := {}


private abbrev M := ReaderT Context $ StateListM State

/-- Return all values from `x` in an array, together with their scores. -/
private def M.run (unify : Bool) (config : WhnfCoreConfig) (x : M (Trie α)) :
    Array (Array α × Nat) :=
  ((x.run { unify, config }).run {}).toArray.map (fun (t, s) => (t.values!, s.score))

/-- Increment the score by `n`. -/
private def incrementScore (n : Nat) : M Unit :=
  modify fun s => { s with score := s.score + n }

/-- Log a metavariable assignment in the `State`. -/
private def insertStarAssignment (n : Nat) (e : DTExpr) : M Unit :=
  modify fun s => { s with starAssignments := s.starAssignments.insert n e }

/-- Log a metavariable assignment in the `State`. -/
private def assignMVar (mvarId : MVarId) (e : Array Key) : M Unit := do
  let { mvarAssignments, .. } ← get
  match mvarAssignments.find? mvarId with
  | some e' => guard (e == e')
  | none =>
    modify fun s => { s with mvarAssignments := s.mvarAssignments.insert mvarId e }

/-- Return the possible `Trie α` that match with `n` metavariable. -/
partial def skipEntries (t : Trie α) (skipped : Array Key) : Nat → M (Array Key × Trie α)
  | 0      => pure (skipped, t)
  | skip+1 =>
    t.children!.foldr (init := failure) fun (k, c) x =>
      (skipEntries c (skipped.push k) (skip + k.arity)) <|> x
/-- Return the possible `Trie α` that match with anything.
We add 1 to the matching score when the key is `.opaque`,
since this pattern is "harder" to match with. -/
def matchTargetStar (mvarId? : Option MVarId) (t : Trie α) : M (Trie α) := do
  let (keys, t) ← t.children!.foldr (init := failure) fun (k, c) x => (do
    if k == .opaque then
      incrementScore 1
    skipEntries c #[k] k.arity
    ) <|> x
  if let some mvarId := mvarId? then
    assignMVar mvarId keys
  return t

/-- Return the possible `Trie α` that come from a `Key.star`,
while keeping track of the `Key.star` assignments. -/
def matchTreeStars (e : DTExpr) (t : Trie α) : M (Trie α) := do
  let {starAssignments, ..} ← get
  let mut result := failure
  /- The `Key.star` are at the start of the `t.children!`,
  so this loops through all of them. -/
  for (k, c) in t.children! do
    let .star i := k | break
    if let some assignment := starAssignments.find? i then
      if e == assignment then
        result := (incrementScore e.size *> pure c) <|> result
    else
      result := (insertStarAssignment i e *> pure c) <|> result
  result

mutual
  /-- Return the possible `Trie α` that match with `e`. -/
  partial def matchExpr (e : DTExpr) (t : Trie α) : M (Trie α) := do
    if let .star mvarId? := e then
      if (← read).unify then
        matchTargetStar mvarId? t
      else
        matchTreeStars e t
    else
      matchTreeStars e t <|> exactMatch e (findKey t.children!)

  /-- If `e` is not a metavariable, return the possible `Trie α` that exactly match with `e`. -/
  @[specialize]
  partial def exactMatch (e : DTExpr) (find? : Key → Option (Trie α)) : M (Trie α) := do

    let findKey (k : Key) (x : Trie α → M (Trie α) := pure) (score := 1) : M (Trie α) :=
      match find? k with
        | none => failure
        | some trie => do
          incrementScore score
          x trie

    let matchArgs (args : Array DTExpr) : Trie α → M (Trie α) :=
      args.foldlM (fun t e => matchExpr e t)

    match e with
    | .opaque           => failure
    | .const c args     => findKey (.const c args.size) (matchArgs args)
    | .fvar fvarId args => findKey (.fvar fvarId args.size) (matchArgs args)
    | .bvar i args      => findKey (.bvar i args.size) (matchArgs args)
    | .lit v            => findKey (.lit v)
    | .sort             => findKey .sort
    | .lam b            => findKey .lam (matchExpr b) 0
    | .forall d b       => findKey .forall (matchExpr d >=> matchExpr b)
    | .proj n i a args  => findKey (.proj n i args.size) (matchExpr a >=> matchArgs args)
    | _                 => unreachable!

end

private partial def getMatchWithScoreAux (d : RefinedDiscrTree α) (e : DTExpr) (unify : Bool)
    (config : WhnfCoreConfig) (allowRootStar : Bool := false) : Array (Array α × Nat) := (do
  if e matches .star _ then
    guard allowRootStar
    d.root.foldl (init := failure) fun x k c => (do
      if k == Key.opaque then
        GetUnify.incrementScore 1
      let (_, t) ← GetUnify.skipEntries c #[k] k.arity
      return t) <|> x
  else
    GetUnify.exactMatch e d.root.find?
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

If `unify := false`, then metavariables in `e` are treated as opaque variables.
This is for when you don't want to instantiate metavariables in `e`.

If `allowRootStar := false`, then we don't allow `e` or the matched key in `d`
to be a star pattern. -/
def getMatchWithScore (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig) (allowRootStar : Bool := false) : MetaM (Array (Array α × Nat)) := do
  let e ← mkDTExpr e config
  let result := GetUnify.getMatchWithScoreAux d e unify config allowRootStar
  return result.qsort (·.2 > ·.2)

/-- Similar to `getMatchWithScore`, but also returns matches with prefixes of `e`.
We store the score, followed by the number of ignored arguments. -/
partial def getMatchWithScoreWithExtra (d : RefinedDiscrTree α) (e : Expr) (unify : Bool)
    (config : WhnfCoreConfig) (allowRootStar : Bool := false) :
    MetaM (Array (Array α × Nat × Nat)) := do
  let result ← go e 0
  return result.qsort (·.2.1 > ·.2.1)
where
  /-- go -/
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
