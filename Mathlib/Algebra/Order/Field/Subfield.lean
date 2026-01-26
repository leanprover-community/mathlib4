import Mathlib.Algebra.Order.Ring.Defs

/-!
# Ordered instances on subfields
-/

@[expose] public section

namespace Subfield
variable {K : Type*}

/-- A subfield of an ordered field is an ordered field. -/
instance toIsStrictOrderedRing [Field K] [LinearOrder K] [IsStrictOrderedRing K] (s : Subfield K) :
    IsStrictOrderedRing s :=
  Function.Injective.isStrictOrderedRing
    Subtype.val rfl rfl (fun _ _ => rfl) (fun _ _ => rfl) .rfl .rfl

end Subfield
