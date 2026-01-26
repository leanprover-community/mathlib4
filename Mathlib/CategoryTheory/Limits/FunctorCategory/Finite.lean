
/-!

# Functor categories have finite limits when the target category does

These declarations cannot be in `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean` because
that file shouldn't import `Mathlib/CategoryTheory/Limits/Shapes/FiniteProducts.lean`.
-/

@[expose] public section

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] {K : Type*} [Category* K]

instance [HasFiniteLimits C] : HasFiniteLimits (K ⥤ C) := ⟨fun _ ↦ inferInstance⟩

instance [HasFiniteProducts C] : HasFiniteProducts (K ⥤ C) := ⟨inferInstance⟩

instance [HasFiniteColimits C] : HasFiniteColimits (K ⥤ C) := ⟨fun _ ↦ inferInstance⟩

instance [HasFiniteCoproducts C] : HasFiniteCoproducts (K ⥤ C) := ⟨inferInstance⟩

instance [HasFiniteLimits C] (k : K) : PreservesFiniteLimits ((evaluation K C).obj k) where
  preservesFiniteLimits _ _ _ := inferInstance

instance [HasFiniteColimits C] (k : K) : PreservesFiniteColimits ((evaluation K C).obj k) where
  preservesFiniteColimits _ _ _ := inferInstance

end CategoryTheory.Limits
