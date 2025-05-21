/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.List

/-!
# Equivalences involving `Array`
-/


namespace Equiv

/-- The natural equivalence between arrays and lists. -/
@[simps! apply symm_apply]
def arrayEquivList (α : Type*) : Array α ≃ List α :=
  ⟨Array.toList, List.toArray, fun _ => rfl, fun _ => rfl⟩

/-- `toVector` and `ofVector` together form an equivalence. -/
@[simps! apply symm_apply]
def vectorEquivListVector (α : Type*) (n : ℕ) : Vector α n ≃ List.Vector α n :=
  ⟨List.Vector.ofVector, List.Vector.toVector, fun _ => rfl, fun _ => rfl⟩

end Equiv

/- Porting note: removed instances for what would be ported as `Traversable (Array α)` and
`LawfulTraversable (Array α)`. These would

1. be implemented directly in terms of `Array` functionality for efficiency, rather than being the
traversal of some other type transported along an equivalence to `Array α` (as the traversable
instance for `array` was)

2. belong in `Mathlib.Control.Traversable.Instances` instead of this file. -/

-- namespace Array'

-- open Function

-- variable {n : ℕ}

-- instance : Traversable (Array' n) :=
--   @Equiv.traversable (flip Vector n) _ (fun α => Equiv.vectorEquivArray α n) _

-- instance : LawfulTraversable (Array' n) :=
--   @Equiv.isLawfulTraversable (flip Vector n) _ (fun α => Equiv.vectorEquivArray α n) _ _

-- end Array'

/-- If `α` is encodable, then so is `Array α`. -/
instance Array.encodable {α} [Encodable α] : Encodable (Array α) :=
  Encodable.ofEquiv _ (Equiv.arrayEquivList _)

/-- If `α` is countable, then so is `Array α`. -/
instance Array.countable {α} [Countable α] : Countable (Array α) :=
  Countable.of_equiv _ (Equiv.arrayEquivList α).symm
