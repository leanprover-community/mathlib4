
/-!
# Functor categories have filtered colimits when the target category does

These declarations cannot be in `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean` because
that file shouldn't import `Mathlib/CategoryTheory/Limits/Filtered.lean`.
-/

@[expose] public section

universe w' w v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {K : Type u₂} [Category.{v₂} K]

instance [HasFilteredColimitsOfSize.{w', w} C] : HasFilteredColimitsOfSize.{w', w} (K ⥤ C) :=
  ⟨fun _ => inferInstance⟩

instance [HasCofilteredLimitsOfSize.{w', w} C] : HasCofilteredLimitsOfSize.{w', w} (K ⥤ C) :=
  ⟨fun _ => inferInstance⟩

end CategoryTheory.Limits
