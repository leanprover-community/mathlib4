import Mathlib.CategoryTheory.Category.Pointed.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact

open CategoryTheory

universe u

namespace Pointed

instance : Limits.HasZeroMorphisms Pointed.{u} where
  zero _ Y := ⟨⟨fun _ ↦ Y.point, rfl⟩⟩
  comp_zero _ _ := ConcreteCategory.ext (Subtype.ext (funext fun _ ↦ rfl))
  zero_comp _ _ _ f  := ConcreteCategory.ext (Subtype.ext (funext fun _ ↦ f.map_point))

section exact

theorem mono_iff_injective {X Y : Pointed.{u}} (f : X ⟶ Y) : Mono f ↔ Function.Injective f := sorry

theorem epi_iff_surjective {X Y : Pointed.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f := sorry

theorem exact_iff (S : ShortComplex Pointed.{u}) :
    S.Exact ↔ ∀ (x : S.X₂), S.g x = S.X₃.point → x ∈ Set.range S.f := sorry

end exact

end Pointed
