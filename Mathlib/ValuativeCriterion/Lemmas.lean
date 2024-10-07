import Mathlib

open CategoryTheory CategoryTheory.Limits

section

lemma _root_.RingHom.injective_stableUnderComposition :
    RingHom.StableUnderComposition (fun f ↦ Function.Injective f) := by
  intro R S T _ _ _ f g hf hg
  simp only [RingHom.coe_comp]
  exact Function.Injective.comp hg hf

lemma _root_.RingHom.injective_respectsIso :
    RingHom.RespectsIso (fun f ↦ Function.Injective f) := by
  apply RingHom.injective_stableUnderComposition.respectsIso
  intro R S _ _ e
  exact e.bijective.injective

end

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

-- from #15033
/-- If `f : A ⟶ B` is a ring homomorphism, the corresponding arrow is isomorphic
to the arrow of the morphism induced on global sections by the map on prime spectra. -/
noncomputable
def Scheme.arrowIsoΓSpecOfIsAffine {A B : CommRingCat} (f : A ⟶ B) :
    Arrow.mk f ≅ Arrow.mk ((Spec.map f).app ⊤) :=
  Arrow.isoMk (Scheme.ΓSpecIso _).symm (Scheme.ΓSpecIso _).symm
    (Scheme.ΓSpecIso_inv_naturality f).symm

end AlgebraicGeometry
