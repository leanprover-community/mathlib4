-- `Mathlib/AlgebraicGeometry/ResidueField
import Mathlib.ValuativeCriterion.Stalk
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.SurjectiveOnStalks

open CategoryTheory CategoryTheory.Limits TopologicalSpace LocalRing

/-

THIS IS PRed in #17768

-/

noncomputable section

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

section TOBEMOVED

lemma IsPreimmersion.mk_spec_map {R S : CommRingCat.{u}} {f : R ⟶ S}
    (h₁ : Embedding (PrimeSpectrum.comap f)) (h₂ : f.SurjectiveOnStalks) :
    IsPreimmersion (Spec.map f) where
  base_embedding := h₁
  surj_on_stalks (x : PrimeSpectrum S) := by
    let e := Scheme.arrowStalkMapSpecIso f x
    haveI : (RingHom.toMorphismProperty <| fun f ↦ Function.Surjective f).RespectsIso := by
      rw [← RingHom.toMorphismProperty_respectsIso_iff]
      exact surjective_respectsIso
    apply ((RingHom.toMorphismProperty <| fun f ↦ Function.Surjective f).arrow_mk_iso_iff e).mpr
    exact h₂ x.asIdeal x.isPrime

lemma isPreimmersion_of_isLocalization {R S : Type u} [CommRing R] (M : Submonoid R) [CommRing S]
    [Algebra R S] [IsLocalization M S] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom <| algebraMap R S)) :=
  IsPreimmersion.mk_spec_map
    (PrimeSpectrum.localization_comap_embedding (R := R) S M)
    (RingHom.surjectiveOnStalks_of_isLocalization (M := M) S)

instance IsAffineOpen.fromSpecStalk_isPreimmersion {U : Opens X} (hU : IsAffineOpen U) (x : X)
    (hx : x ∈ U) : IsPreimmersion (hU.fromSpecStalk hx) := by
  dsimp [fromSpecStalk]
  haveI : IsPreimmersion (Spec.map (X.presheaf.germ ⟨x, hx⟩)) :=
    letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ ⟨x, hx⟩).toAlgebra
    haveI := hU.isLocalization_stalk ⟨x, hx⟩
    isPreimmersion_of_isLocalization (R := Γ(X, U)) (S := X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  apply IsPreimmersion.comp

instance (x) : AlgebraicGeometry.IsPreimmersion (X.fromSpecStalk x) :=
  IsAffineOpen.fromSpecStalk_isPreimmersion _ _ _

end TOBEMOVED

def Scheme.residueField (x : X) : CommRingCat := X.toLocallyRingedSpace.residueField x

instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (LocalRing.ResidueField (X.presheaf.stalk x))

def Scheme.toResidueField (X : Scheme) (x) : X.presheaf.stalk x ⟶ X.residueField x :=
  LocalRing.residue _

instance (x) : IsClosedImmersion (Spec.map (X.toResidueField x)) :=
  IsClosedImmersion.spec_of_surjective (X.toResidueField x)
    Ideal.Quotient.mk_surjective

def Scheme.descResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalRingHom f] : X.residueField x ⟶ .of K :=
  LocalRing.ResidueField.lift (S := K) f

@[reassoc (attr := simp)]
lemma Scheme.toResidueField_descResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalRingHom f] :
    X.toResidueField x ≫ X.descResidueField f = f :=
  RingHom.ext fun _ ↦ rfl

instance (x) : Epi (X.toResidueField x) :=
  ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective

def evaluation {U : Opens X} (x : U) : Γ(X, U) ⟶ X.residueField x :=
  X.toLocallyRingedSpace.evaluation x

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
def Γevaluation (x : X) : Γ(X, ⊤) ⟶ X.residueField x :=
  X.toLocallyRingedSpace.Γevaluation x

-- replace this def if hard to work wit
def Scheme.residueFieldCongr (X : Scheme) {x y : X} (h : x = y) :
    X.residueField x ≅ X.residueField y :=
  eqToIso (by subst h; rfl)

@[simp]
lemma Scheme.residueFieldCongr_refl (X : Scheme) {x : X} :
    X.residueFieldCongr (refl x) = Iso.refl _ := rfl

@[simp]
lemma Scheme.residueFieldCongr_symm (X : Scheme) {x y : X} (e : x = y) :
    (X.residueFieldCongr e).symm = X.residueFieldCongr e.symm := rfl

@[simp]
lemma Scheme.residueFieldCongr_inv (X : Scheme) {x y : X} (e : x = y) :
    (X.residueFieldCongr e).inv = (X.residueFieldCongr e.symm).hom := rfl

@[simp]
lemma Scheme.residueFieldCongr_trans (X : Scheme) {x y z : X} (e : x = y) (e' : y = z) :
    X.residueFieldCongr e ≪≫ X.residueFieldCongr e' = X.residueFieldCongr (e.trans e') := by
  subst e e'
  rfl

@[reassoc (attr := simp)]
lemma Scheme.residueFieldCongr_trans' (X : Scheme) {x y z : X} (e : x = y) (e' : y = z) :
    (X.residueFieldCongr e).hom ≫ (X.residueFieldCongr e').hom =
      (X.residueFieldCongr (e.trans e')).hom := by
  subst e e'
  rfl

@[reassoc]
lemma Scheme.toResidueField_residueFieldCongr (X : Scheme) {x y : X} (h : x = y) :
    X.toResidueField x ≫ (X.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.toResidueField y := by
  subst h
  simp

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
def Scheme.Hom.residueFieldMap (f : X.Hom Y) (x : X) :
    Y.residueField (f.val.base x) ⟶ X.residueField x :=
  LocallyRingedSpace.residueFieldMap f x

@[reassoc]
lemma residue_residueFieldMap (x : X) :
    Y.toResidueField (f.1.base x) ≫ f.residueFieldMap x =
      f.stalkMap x ≫ X.toResidueField x :=
  LocallyRingedSpace.residue_comp_residueFieldMap_eq_stalkMap_comp_residue _ _

lemma residueFieldMap_id (x : X) :
    Scheme.Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) :=
  LocallyRingedSpace.residueFieldMap_id _

@[simp]
lemma residueFieldMap_comp (x):
    (f ≫ g).residueFieldMap x = g.residueFieldMap (f.val.base x) ≫ f.residueFieldMap x :=
  LocallyRingedSpace.residueFieldMap_comp _ _ _

lemma Scheme.Hom.residueFieldMap_congr {f g : X ⟶ Y} (e : f = g) (x : X) :
    f.residueFieldMap x = (Y.residueFieldCongr (by subst e; rfl)).hom ≫ g.residueFieldMap x := by
  subst e; simp

@[reassoc]
lemma evaluation_naturality {V : Opens Y} (x : f ⁻¹ᵁ V) :
    Y.evaluation ⟨f.1.base x, x.2⟩ ≫ f.residueFieldMap x.val = f.app V ≫ X.evaluation x :=
  LocallyRingedSpace.evaluation_naturality _ _

@[reassoc]
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f.val.base x) ≫ f.residueFieldMap x = f.app ⊤ ≫ X.Γevaluation x :=
  LocallyRingedSpace.Γevaluation_naturality _ _

def Scheme.fromSpecResidueField (X : Scheme) (x : X) :
    Spec (X.residueField x) ⟶ X :=
  Spec.map (X.toResidueField x) ≫ X.fromSpecStalk x

lemma Scheme.Hom.residueFieldMap_fromSpecResidueField (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  dsimp only [fromSpecResidueField]
  rw [Category.assoc, ← Scheme.stalkMap_fromSpecStalk, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  rfl

@[reassoc (attr := simp)]
lemma Scheme.residueFieldCongr_fromSpecResidueField {x y : X} (h : x = y) :
    Spec.map (X.residueFieldCongr h).hom ≫ X.fromSpecResidueField _ =
      X.fromSpecResidueField _ := by
  subst h; simp

lemma _root_.Function.Bijective.residueFieldMap {R S : Type*} [CommRing R] [CommRing S]
    [LocalRing R] [LocalRing S] (f : R →+* S) [IsLocalRingHom f] (hf : Function.Bijective f) :
    Function.Bijective (LocalRing.ResidueField.map f) :=
  (ResidueField.mapEquiv (RingEquiv.ofBijective f hf)).bijective

instance (x) : AlgebraicGeometry.IsPreimmersion (X.fromSpecResidueField x) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [IsPreimmersion.comp_iff]
  infer_instance

instance [IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x) := by
  dsimp [Scheme.Hom.residueFieldMap, LocallyRingedSpace.residueFieldMap]
  rw [ConcreteCategory.isIso_iff_bijective]
  have : Function.Bijective (LocallyRingedSpace.Hom.stalkMap f x) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  exact this.residueFieldMap

/-- by `Scheme.fromSpecStalk_closedPoint` -/
@[simp]
lemma Scheme.fromSpecResidueField_apply (x : X.carrier) (s) :
    (X.fromSpecResidueField x).1.base s = x := by
  dsimp [fromSpecResidueField]
  have : (Spec.map (X.toResidueField x)).val.base s =
      closedPoint (X.presheaf.stalk x) :=
    LocalRing.PrimeSpectrum.comap_residue _ s
  rw [this]
  apply Scheme.fromSpecStalk_closedPoint

-- by the previous lemma
lemma Scheme.range_fromSpecResidueField  (x : X.carrier) :
    Set.range (X.fromSpecResidueField x).1.base = {x} := by
  ext s
  simp only [Set.mem_range, fromSpecResidueField_apply, Set.mem_singleton_iff, eq_comm (a := s)]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro rfl
    exact ⟨closedPoint (residueField x), rfl⟩

attribute [instance] isLocalRingHom_stalkClosedPointTo

lemma Scheme.descResidueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalRingHom f] :
    Spec.map (X.descResidueField f) ≫
      X.fromSpecResidueField x = Spec.map f ≫ X.fromSpecStalk x := by
  dsimp only [descResidueField, fromSpecResidueField]
  rw [← Spec.map_comp_assoc]
  erw [Scheme.toResidueField_descResidueField]

lemma Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) :
    Spec.map (X.descResidueField (Scheme.stalkClosedPointTo f)) ≫
      X.fromSpecResidueField (f.1.base (closedPoint K)) = f := by
  erw [Scheme.descResidueField_fromSpecResidueField]
  apply Scheme.Spec_stalkClosedPointTo_fromSpecStalk

lemma SpecToEquivOfField_eq_iff {K : Type*} [Field K] {X : Scheme}
    {f₁ f₂ : Σ x : X.carrier, X.residueField x ⟶ .of K} :
    f₁ = f₂ ↔ ∃ e : f₁.1 = f₂.1, f₁.2 = (X.residueFieldCongr e).hom ≫ f₂.2 := by
  constructor
  · rintro rfl
    simp
  · intro ⟨e, h⟩
    ext
    exact e
    exact (Functor.conj_eqToHom_iff_heq f₁.snd f₂.snd (congrArg Scheme.residueField e) rfl).mp h

def SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where
  toFun f :=
    letI : IsLocalRingHom (Scheme.stalkClosedPointTo f) := inferInstance -- why??
    ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv := by
    intro f
    rw [SpecToEquivOfField_eq_iff]
    simp only [CommRingCat.coe_of, Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply,
      Scheme.fromSpecResidueField_apply, exists_true_left]
    rw [← Spec.map_inj, Spec.map_comp]
    rw [← cancel_mono (X.fromSpecResidueField _)]
    erw [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField]
    simp

end AlgebraicGeometry
