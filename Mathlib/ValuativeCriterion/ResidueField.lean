-- `Mathlib/AlgebraicGeometry/ResidueField
import Mathlib.ValuativeCriterion.Stalk
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

open CategoryTheory CategoryTheory.Limits TopologicalSpace LocalRing

noncomputable section

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

def Scheme.residueField (x : X) : CommRingCat := X.toLocallyRingedSpace.residueField x

instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs <| Field (LocalRing.ResidueField (X.stalk x))

def Scheme.toResidueField (X : Scheme) (x) : X.stalk x ⟶ X.residueField x :=
  LocalRing.residue _

def Scheme.descResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalRingHom f] : X.residueField x ⟶ .of K :=
  LocalRing.ResidueField.lift (S := K) f

@[reassoc (attr := simp)]
lemma Scheme.toResidueField_descResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.stalk x ⟶ .of K) [IsLocalRingHom f] :
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
      PresheafedSpace.stalkMap f.1 x ≫ X.toResidueField x :=
  LocallyRingedSpace.residue_comp_residueFieldMap_eq_stalkMap_comp_residue _ _

lemma residueFieldMap_id (x : X) :
    Scheme.Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) :=
  LocallyRingedSpace.residueFieldMap_id _

@[simp]
lemma residueFieldMap_comp (x):
    (f ≫ g).residueFieldMap x = g.residueFieldMap (f.val.base x) ≫ f.residueFieldMap x :=
  LocallyRingedSpace.residueFieldMap_comp _ _ _

lemma Scheme.hom.residueFieldMap_congr {f g : X ⟶ Y} (e : f = g) (x : X) :
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
  Spec.map (CommRingCat.ofHom (LocalRing.residue _)) ≫ X.fromSpecStalk x

/--
by `Epi (X.toResidueField x)` and `Scheme.stalkMap_fromSpecStalk` and `residue_residueFieldMap`
-/
lemma Scheme.hom.residueFieldMap_fromSpecResidueField (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  have : Epi (X.toResidueField x) := inferInstance
  have h1 := Scheme.stalkMap_fromSpecStalk f (x := x)
  have h2 := residue_residueFieldMap f x
  dsimp only [fromSpecResidueField]
  sorry

@[reassoc (attr := simp)]
lemma Scheme.residueFieldCongr_fromSpecResidueField {x y : X} (h : x = y) :
    Spec.map (X.residueFieldCongr h).hom ≫ X.fromSpecResidueField _ =
      X.fromSpecResidueField _ := by
  subst h; simp

instance [IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x) := sorry

/-- by `Scheme.fromSpecStalk_closedPoint` -/
lemma Scheme.fromSpecResidueField_apply (x : X.carrier) (s) :
    (X.fromSpecResidueField x).1.base s = x := by sorry

-- by the previous lemma
lemma Scheme.range_fromSpecResidueField  (x : X.carrier) :
    Set.range (X.fromSpecResidueField x).1.base = {x} := by
  ext s
  simp only [Set.mem_range, fromSpecResidueField_apply, Set.mem_singleton_iff, eq_comm (a := s)]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro rfl
    refine ⟨?_, rfl⟩
    sorry

attribute [instance] isLocalRingHom_stalkClosedPointTo

lemma Scheme.descResidueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.stalk x ⟶ .of K) [IsLocalRingHom f] :
    Spec.map (X.descResidueField f)
      ≫ X.fromSpecResidueField x = Spec.map f ≫ X.fromSpecStalk x := sorry -- by def

lemma Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) :
  Spec.map (X.descResidueField (Scheme.stalkClosedPointTo _ f))
    ≫ X.fromSpecResidueField (f.1.base (closedPoint K)) = f := sorry -- by def

lemma SpecToEquivOfField_eq_iff {K : Type*} [Field K] {X : Scheme}
    {f₁ f₂ : Σ x : X.carrier, X.residueField x ⟶ .of K} :
  f₁ = f₂ ↔ ∃ e : f₁.1 = f₂.1, f₁.2 = (X.residueFieldCongr e).hom ≫ f₂.2 := sorry -- by def

def SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where
  toFun f :=
    letI : IsLocalRingHom (Scheme.stalkClosedPointTo (.of K) f) := inferInstance -- why??
    ⟨_, X.descResidueField (Scheme.stalkClosedPointTo (.of K) f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv := sorry

end AlgebraicGeometry
