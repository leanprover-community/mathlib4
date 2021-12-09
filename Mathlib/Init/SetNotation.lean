import Mathlib.Init.ExtendedBinder

class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem

notation:50 x " ∉ " s => ¬ x ∈ s

class Subset (α : Type u) where
  subset : α → α → Prop

infix:50 " ⊆ " => Subset.subset

class Union (α : Type u) where
  union : α → α → α

infixl:65 " ∪ " => Union.union

class Inter (α : Type u) where
  inter : α → α → α

infixl:70 " ∩ " => Inter.inter

class Sdiff (α : Type u) where
  sdiff : α → α → α

infix:70 " \\ " => Sdiff.sdiff

binder_predicate x " ∈ " y:term => `($x ∈ $y)
