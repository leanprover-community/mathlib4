import Mathlib.CategoryTheory.Filtered.CostructuredArrow
import Mathlib.CategoryTheory.Functor.Flat

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

instance {C : Type u₁} [Category.{v₁} C] [IsFilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun c₁ c₂ =>
    .trans (.of_hom (IsFiltered.leftToMax c₁ c₂)) (.of_inv (IsFiltered.rightToMax c₁ c₂))

instance {C : Type u₁} [Category.{v₁} C] [IsCofilteredOrEmpty C] : IsPreconnected C :=
  zigzag_isPreconnected fun c₁ c₂ =>
    .trans (.of_inv (IsCofiltered.minToLeft c₁ c₂)) (.of_hom (IsCofiltered.minToRight c₁ c₂))

instance {C : Type u₁} [Category.{v₁} C] [IsFiltered C] : IsConnected C where
  is_nonempty := IsFiltered.nonempty

instance {C : Type u₁} [Category.{v₁} C] [IsCofiltered C] : IsConnected C where
  is_nonempty := IsCofiltered.nonempty

variable {C : Type u₁} [SmallCategory C]
variable {D : Type u₁} [SmallCategory D]
variable (F : C ⥤ D)

instance [h : RepresentablyFlat F] : F.Final := ⟨inferInstance⟩

lemma isFiltered_of_preservesFiniteLimits [IsFiltered C] [RepresentablyFlat F] : IsFiltered D :=
  haveI : PreservesFiniteLimits F := preservesFiniteLimits_of_flat F
  isFiltered_of_isFiltered_costructuredArrow (𝟭 _) F

end CategoryTheory
