/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Equiv.List

#align_import logic.equiv.array from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Equivalences involving `Array`
-/

/-

Porting note:

The following commented-out definitions only made sense for the mathlib3 datatypes `d_array` and
`array`. `d_array` (a dependent array) does not yet (as of Jun 27 2023) have a corresponding
datatype in lean4/std4/mathlib4; `array` was length-indexed and therefore more similar to `Vector`,
which may be reimplemented in terms of `Array` internally anyway in the future.

However, we have tried to align `array` with `Array` where possible nonetheless, and therefore we
introduce the "right" equivalence for `Array` (`arrayEquivList`) and align the instances
`array.encodable`, `array.countable` with `Array.encodable`, `Array.countable` respectively.

-/

namespace Equiv

-- /-- The natural equivalence between length-`n` heterogeneous arrays
-- and dependent functions from `fin n`. -/
-- def darrayEquivFin {n : ℕ} (α : Fin n → Type*) : DArray n α ≃ ∀ i, α i :=
--   ⟨DArray.read, DArray.mk, fun ⟨f⟩ => rfl, fun f => rfl⟩
#noalign equiv.d_array_equiv_fin

-- /-- The natural equivalence between length-`n` arrays and functions from `fin n`. -/
-- def array'EquivFin (n : ℕ) (α : Type*) : Array' n α ≃ (Fin n → α) :=
--   darrayEquivFin _
#noalign equiv.array_equiv_fin

-- /-- The natural equivalence between length-`n` vectors and length-`n` arrays. -/
-- def vectorEquivArray' (α : Type*) (n : ℕ) : Vector α n ≃ Array' n α :=
--   (vectorEquivFin _ _).trans (array'EquivFin _ _).symm
#noalign equiv.vector_equiv_array

/-- The natural equivalence between arrays and lists. -/
def arrayEquivList (α : Type*) : Array α ≃ List α :=
  ⟨Array.data, Array.mk, fun _ => rfl, fun _ => rfl⟩

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
#noalign array.encodable

/-- If `α` is countable, then so is `Array α`. -/
instance Array.countable {α} [Countable α] : Countable (Array α) :=
  Countable.of_equiv _ (Equiv.arrayEquivList α).symm
#noalign array.countable
