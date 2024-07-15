-- `Mathlib/AlgebraicGeometry/Stalk
import Mathlib.AlgebraicGeometry.Stalk

open CategoryTheory CategoryTheory.Limits TopologicalSpace LocalRing

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

-- by def
@[reassoc]
lemma Scheme.stalkSpecializes_fromSpecStalk {X : Scheme} {x y : X.carrier} (h : x ⤳ y) :
  Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk y = X.fromSpecStalk x := sorry

-- not sure if `hU` is necessary. More or less by def of `fromSpecStalk`.
lemma IsAffineOpen.fromSpecStalk_app {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
  (X.fromSpecStalk x).app U =
    X.presheaf.germ ⟨x, hxU⟩ ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := sorry

-- by def
@[reassoc]
lemma Scheme.map_app_fromSpec {V : Opens X} (hV : IsAffineOpen V) {U} (hU : IsAffineOpen U)
    (i : V ⟶ f ⁻¹ᵁ U) :
    Spec.map (X.presheaf.map i.op) ≫ Spec.map (f.app U) ≫ hU.fromSpec = hV.fromSpec ≫ f := sorry

lemma Scheme.stalkMap_fromSpecStalk {x} :
    Spec.map (PresheafedSpace.stalkMap f.1 x) ≫ Y.fromSpecStalk _ = X.fromSpecStalk x ≫ f := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := (isBasis_affine_open Y).exists_subset_of_mem_open
    (Set.mem_univ (f.1.base x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := (isBasis_affine_open X).exists_subset_of_mem_open
    hxU (f ⁻¹ᵁ U).2
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, ← hV.fromSpecStalk_eq_fromSpecStalk hxV,
    IsAffineOpen.fromSpecStalk, ← Spec.map_comp_assoc, PresheafedSpace.stalkMap_germ f.1 _ ⟨x, hxU⟩,
    IsAffineOpen.fromSpecStalk, Spec.map_comp_assoc, ← X.presheaf.germ_res (homOfLE hVU) ⟨x, hxV⟩,
    Spec.map_comp_assoc, Category.assoc, Scheme.map_app_fromSpec]

/-- by unfolding `fromSpecStalk`. -/
lemma IsAffineOpen.fromSpecStalk_closedPoint {U : Opens X} (hU : IsAffineOpen U)
    {x : X} (hxU : x ∈ U) :
    (hU.fromSpecStalk hxU).1.base (closedPoint (X.presheaf.stalk x)) = x := sorry

/-- IsAffineOpen.fromSpecStalk_closedPoint -/
lemma Scheme.fromSpecStalk_closedPoint {x : X} :
    (X.fromSpecStalk x).1.base (closedPoint (X.presheaf.stalk x)) = x := sorry

/-- https://stacks.math.columbia.edu/tag/01J7 -/
lemma Scheme.range_fromSpecStalk {x : X} :
    Set.range (X.fromSpecStalk x).1.base = { y | y ⤳ x } := sorry

noncomputable
def stalkClosedPointIso (R : CommRingCat) [LocalRing R] :
    (Spec R).presheaf.stalk (closedPoint R) ≅ R :=
  StructureSheaf.stalkIso _ _ ≪≫ (IsLocalization.atUnits R
      (closedPoint R).asIdeal.primeCompl fun _ ↦ not_not.mp).toRingEquiv.toCommRingCatIso.symm

noncomputable
def Scheme.stalkClosedPointTo (R : CommRingCat) [LocalRing R] (f : Spec R ⟶ X) :
    X.presheaf.stalk (f.1.base (closedPoint R)) ⟶ R :=
  PresheafedSpace.stalkMap f.1 (closedPoint R) ≫ (stalkClosedPointIso R).hom

instance isLocalRingHom_stalkClosedPointTo (R : CommRingCat) [LocalRing R] (f : Spec R ⟶ X) :
    IsLocalRingHom (Scheme.stalkClosedPointTo R f) := sorry

-- move me
lemma LocalRing.closed_point_mem_iff {R : Type*} [CommRing R] [LocalRing R]
    {U : Opens (PrimeSpectrum R)} : closedPoint R ∈ U ↔ U = ⊤ := sorry

lemma preimage_eq_top_of_closedPoint_mem {R : CommRingCat} [LocalRing R] {f : Spec R ⟶ X}
    {U : Opens X} (hU : f.1.base (closedPoint R) ∈ U) : f ⁻¹ᵁ U = ⊤ :=
  LocalRing.closed_point_mem_iff.mp hU

-- by def
@[reassoc]
lemma Scheme.germ_stalkClosedPointTo_toOpen (R : CommRingCat) [LocalRing R] (f : Spec R ⟶ X)
    (U : Opens X) (hU : f.1.base (closedPoint R) ∈ U) :
    X.presheaf.germ ⟨_, hU⟩ ≫ stalkClosedPointTo R f = f.app U ≫
      ((Spec R).presheaf.mapIso (eqToIso (preimage_eq_top_of_closedPoint_mem hU).symm).op ≪≫
        Scheme.ΓSpecIso R).hom := sorry

-- by def & `germ_stalkClosedPointTo_toOpen`
@[reassoc]
lemma Scheme.Spec_stalkClosedPointTo_fromSpecStalk
    (R : CommRingCat) [LocalRing R] (f : Spec R ⟶ X) :
    Spec.map (stalkClosedPointTo R f) ≫ X.fromSpecStalk _ = f := sorry

-- useful lemma for applications of `SpecToEquivOfLocalRing`
lemma SpecToEquivOfLocalRing_eq_iff (R : CommRingCat) [LocalRing R] (X : Scheme)
    {f₁ f₂ : Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalRingHom f }} :
    f₁ = f₂ ↔ ∃ h₁ : f₁.1 = f₂.1, f₁.2.1 =
      (X.presheaf.stalkCongr (by rw [h₁]; rfl)).hom ≫ f₂.2.1 := by sorry

noncomputable
def SpecToEquivOfLocalRing (R : CommRingCat) [LocalRing R] (X : Scheme) :
    (Spec R ⟶ X) ≃ Σ x, { f : X.presheaf.stalk x ⟶ R // IsLocalRingHom f } where
  toFun f := ⟨f.1.base (closedPoint R), Scheme.stalkClosedPointTo R f, inferInstance⟩
  invFun xf := Spec.map xf.2.1 ≫ X.fromSpecStalk xf.1
  left_inv := Scheme.Spec_stalkClosedPointTo_fromSpecStalk R
  right_inv xf := sorry -- by `SpecToEquivOfLocalRing_eq_iff`, faithful-ness of `Spec` and `Spec_stalkClosedPointTo_fromSpecStalk`

-- by `SpecToEquivOfLocalRing`
lemma Scheme.stalkClosedPointTo_fromSpecStalk {X : Scheme} (x : X.carrier) :
    stalkClosedPointTo (X.presheaf.stalk x) (X.fromSpecStalk x) =
      (X.presheaf.stalkCongr (by erw [fromSpecStalk_closedPoint]; rfl)).hom := sorry

end AlgebraicGeometry
