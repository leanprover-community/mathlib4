import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Ring.Rat

/-!
# A `ℚ`-vector space has `TwoUniqueSums`.
-/

@[expose] public section

variable {G : Type*}

/-- Any `ℚ`-vector space has `TwoUniqueSums`, because it is isomorphic to some
  `(Basis.ofVectorSpaceIndex ℚ G) →₀ ℚ` by choosing a basis, and `ℚ` already has
  `TwoUniqueSums` because it's ordered. -/
instance [AddCommGroup G] [Module ℚ G] : TwoUniqueSums G :=
  TwoUniqueSums.of_injective_addHom _ (Module.Basis.ofVectorSpace ℚ G).repr.injective inferInstance
