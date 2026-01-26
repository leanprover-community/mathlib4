import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Free abelian groups have unique sums
-/

@[expose] public section

assert_not_exists Cardinal StarModule

instance {σ : Type*} : TwoUniqueSums (FreeAbelianGroup σ) :=
  (FreeAbelianGroup.equivFinsupp σ).twoUniqueSums_iff.mpr inferInstance
