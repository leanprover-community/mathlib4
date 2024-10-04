import Mathlib

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism with affine target is an isomorphism if and only if the source is affine and
the induced map on global sections is bijective. -/
lemma isIso_iff_of_isAffine [IsAffine Y] :
    IsIso f ↔ IsAffine X ∧ Function.Bijective (f.app ⊤) := by
  refine ⟨fun h ↦ ⟨isAffine_of_isIso f, ?_⟩, fun ⟨_, hf⟩ ↦ ?_⟩
  · apply (ConcreteCategory.isIso_iff_bijective (f := (Scheme.Γ.map f.op))).mp
    exact Functor.map_isIso Scheme.Γ f.op
  · let e : Arrow.mk f ≅ Arrow.mk (Spec.map (f.app ⊤)) := arrowIsoSpecΓOfIsAffine f
    apply ((MorphismProperty.isomorphisms Scheme.{u}).arrow_mk_iso_iff e).mpr
    have : IsIso (f.app ⊤) := (ConcreteCategory.isIso_iff_bijective (Scheme.Hom.app f ⊤)).mpr hf
    apply Functor.map_isIso Scheme.Spec (f.app ⊤).op

-- scheme map preserves specialization
lemma schemePreservesSpec (X Y : Scheme) (f : X ⟶ Y) (x x' : X.carrier) (h : x' ⤳ x) :
    (f.val.base x') ⤳ (f.val.base x) :=
  Specializes.map_of_continuousAt h (map_continuousAt f.val.base x)

end AlgebraicGeometry
