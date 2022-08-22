import Mathlib.Init.ExtendedBinder

/-- Notation type class for the subset relation `⊆`. -/
class Subset (α : Type u) where
  /-- Subset relation: `a ⊆ b`  -/
  subset : α → α → Prop

/-- Subset relation: `a ⊆ b`  -/
infix:50 " ⊆ " => Subset.subset

/-- Notation type class for the strict subset relation `⊂`. -/
class SSubset (α : Type u) where
  /-- Strict subset relation: `a ⊂ b`  -/
  ssubset : α → α → Prop

/-- Strict subset relation: `a ⊂ b`  -/
infix:50 " ⊂ " => SSubset.ssubset

/-- Superset relation: `a ⊇ b`  -/
abbrev superset [Subset α] (a b : α) := b ⊆ a
/-- Superset relation: `a ⊇ b`  -/
infix:50 " ⊇ " => superset

/-- Strict superset relation: `a ⊃ b`  -/
abbrev ssuperset [SSubset α] (a b : α) := b ⊂ a
/-- Strict superset relation: `a ⊃ b`  -/
infix:50 " ⊃ " => ssuperset

/-- Notation type class for the union operation `∪`. -/
class Union (α : Type u) where
  /-- `a ∪ b` is the union of`a` and `b`. -/
  union : α → α → α
/-- `a ∪ b` is the union of`a` and `b`. -/
infixl:65 " ∪ " => Union.union

/-- Notation type class for the intersection operation `∩`. -/
class Inter (α : Type u) where
  /-- `a ∩ b` is the intersection of`a` and `b`. -/
  inter : α → α → α
/-- `a ∩ b` is the intersection of`a` and `b`. -/
infixl:70 " ∩ " => Inter.inter

/-- Notation type class for the set difference `\`. -/
class Sdiff (α : Type u) where
  /--
  `a \ b` is the set difference of `a` and `b`,
  consisting of all elements in `a` that are not in `b`.
  -/
  sdiff : α → α → α
/--
`a \ b` is the set difference of `a` and `b`,
consisting of all elements in `a` that are not in `b`.
-/
infix:70 " \\ " => Sdiff.sdiff

/--
Type class for the `insert` operation.
Used to implement the `{ a, b, c }` syntax.
-/
class Insert (α : outParam <| Type u) (γ : Type v) where
  /-- `insert x xs` inserts the element `x` into the collection `xs`. -/
  insert : α → γ → γ
export Insert (insert)

/--
Type class for the `singleton` operation.
Used to implement the `{ a, b, c }` syntax.
-/
class Singleton (α : outParam <| Type u) (β : Type v) where
  /-- `singleton x` is a collection with the single element `x` (notation: `{x}`). -/
  singleton : α → β
export Singleton (singleton)

/-- Type class used to implement the notation `{ a ∈ c | p a }` -/
class Sep (α : outParam <| Type u) (γ : Type v) where
  /-- Computes `{ a ∈ c | p a }`. -/
  sep : (α → Prop) → γ → γ

binder_predicate x " ∈ " y:term => `($x ∈ $y)

/--
`{ a, b, c }` is a set with elements `a`, `b`, and `c`.

This notation works for all types that implement `Insert` and `Singleton`.
-/
syntax "{" term,+ "}" : term

macro_rules
  | `({$x:term}) => `(singleton $x)
  | `({$x:term, $xs:term,*}) => `(insert $x {$xs:term,*})

/-- Unexpander for the `{ x }` notation. -/
@[appUnexpander singleton]
def singletonUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a) => `({ $a:term })
  | _ => throw ()

/-- Unexpander for the `{ x, y, ... }` notation. -/
@[appUnexpander insert]
def insertUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $a { $ts,* }) => `({$a:term, $ts,*})
  | _ => throw ()

/-- `insert x ∅ = {x}` -/
class IsLawfulSingleton (α : Type u) (β : Type v) [EmptyCollection β] [Insert α β] [Singleton α β] : Prop where
  /-- `insert x ∅ = {x}` -/
  insert_emptyc_eq (x : α) : (insert x ∅ : β) = {x}
export IsLawfulSingleton (insert_emptyc_eq)
