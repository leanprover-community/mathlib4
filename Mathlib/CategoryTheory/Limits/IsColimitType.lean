import Mathlib.CategoryTheory.Limits.Types
import Mathlib.CategoryTheory.Limits.HasLimits

universe v u w

namespace CategoryTheory

variable {J : Type u} [Category.{v} J] {F : J ⥤ Type w}

lemma Functor.sections_ext_iff {x y : F.sections} : x = y ↔ ∀ j, x.1 j = y.1 j := by
  constructor
  · rintro rfl _
    rfl
  · intro h
    ext j
    exact h j

namespace Limits

namespace Types

variable (c : Cone F)

lemma nonempty_isLimit_iff_bijective_sectionOfCone :
    Nonempty (IsLimit c) ↔ Function.Bijective (Types.sectionOfCone c) := by
  simp only [Function.bijective_iff_existsUnique, isLimit_iff,
    Functor.sections_ext_iff, sectionOfCone]
  constructor
  · intro h x
    exact h x.1 x.2
  · intro h x hx
    exact h ⟨x, hx⟩

variable {c}

lemma sectionOfCone_bijective_of_isLimit (hc : IsLimit c) :
    Function.Bijective (Types.sectionOfCone c) :=
  (nonempty_isLimit_iff_bijective_sectionOfCone c).1 ⟨hc⟩

variable (F)

section

variable [Small.{w} F.sections]

@[simps!]
noncomputable def coneOfSmall : Cone F where
  pt := Shrink F.sections
  π :=
    { app := fun j x => ((equivShrink F.sections).symm x).1 j
      naturality := fun j j' φ => by
        ext t
        obtain ⟨z, rfl⟩ := (equivShrink F.sections).surjective t
        simp }

@[simp]
lemma coneOfSmall_toSections :
    (Types.sectionOfCone (Types.coneOfSmall F)) = (equivShrink F.sections).invFun := by
  ext t
  obtain ⟨z, rfl⟩ := (equivShrink F.sections).surjective t
  simp [sectionOfCone]

noncomputable def isLimitConeOfSmall :
    IsLimit (Types.coneOfSmall F) :=
  Nonempty.some (by simpa only [nonempty_isLimit_iff_bijective_sectionOfCone,
    Types.coneOfSmall_toSections] using (equivShrink F.sections).symm.bijective)

end

lemma hasLimit_iff_small_sections : HasLimit F ↔ Small.{w} F.sections :=
  ⟨fun _ => Small.mk ⟨_, ⟨(Equiv.ofBijective _
      (sectionOfCone_bijective_of_isLimit (limit.isLimit F))).symm⟩⟩,
    fun _ => ⟨_, Types.isLimitConeOfSmall F⟩⟩

end Types

end Limits

end CategoryTheory
