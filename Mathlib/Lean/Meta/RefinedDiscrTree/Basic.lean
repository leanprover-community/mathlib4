/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid
-/
import Mathlib.Init

/-!
# Basic Definitions for `RefinedDiscrTree`
-/

namespace Lean.Meta.RefinedDiscrTree

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
  | .star i     => mixHash 7883 <| hash i
  | .opaque     => 342
  | .const n a  => mixHash 5237 <| mixHash (hash n) (hash a)
  | .fvar  n a  => mixHash 8765 <| mixHash (hash n) (hash a)
  | .bvar i a   => mixHash 4323 <| mixHash (hash i) (hash a)
  | .lit v      => mixHash 1879 <| hash v
  | .sort       => 2411
  | .lam        => 4742
  | .«forall»   => 9752
  | .proj s i a => mixHash (hash a) <| mixHash (hash s) (hash i)

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
  | .node cs => Format.group <| Format.paren <|
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
structure _root_.Lean.Meta.RefinedDiscrTree (α : Type) where
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

end Lean.Meta.RefinedDiscrTree
