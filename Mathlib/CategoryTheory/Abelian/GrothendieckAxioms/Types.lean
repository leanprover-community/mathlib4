
/-!
# The category of types satisfies Grothendieck's AB5 axiom

This is of course just the well-known fact that filtered colimits commute with finite limits in
the category of types.
-/

@[expose] public section

universe v

namespace CategoryTheory.Limits

instance : AB5 (Type v) where
  ofShape _ _ _ := ⟨inferInstance⟩

end CategoryTheory.Limits
