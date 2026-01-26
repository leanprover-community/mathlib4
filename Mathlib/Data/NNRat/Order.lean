import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

/-!
# Bundled ordered algebra structures on `ℚ≥0`

-/

@[expose] public section

instance : IsStrictOrderedRing ℚ≥0 := Nonneg.isStrictOrderedRing

-- TODO: `deriving instance OrderedSub for NNRat` doesn't work yet, so we add the instance manually
instance NNRat.instOrderedSub : OrderedSub ℚ≥0 := Nonneg.orderedSub
instance NNRat.instCanonicallyOrderedAdd : CanonicallyOrderedAdd ℚ≥0 := Nonneg.canonicallyOrderedAdd
