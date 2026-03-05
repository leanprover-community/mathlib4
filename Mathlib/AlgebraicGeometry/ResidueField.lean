/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.ResidueField

/-!

# Residue fields of points

## Main definitions

The following are in the `AlgebraicGeometry.Scheme` namespace:

- `AlgebraicGeometry.Scheme.residueField`: The residue field of the stalk at `x`.
- `AlgebraicGeometry.Scheme.evaluation`: For open subsets `U` of `X` containing `x`,
  the evaluation map from sections over `U` to the residue field at `x`.
- `AlgebraicGeometry.Scheme.Hom.residueFieldMap`: A morphism of schemes induce a homomorphism of
  residue fields.
- `AlgebraicGeometry.Scheme.fromSpecResidueField`: The canonical map `Spec κ(x) ⟶ X`.
- `AlgebraicGeometry.Scheme.SpecToEquivOfField`: morphisms `Spec K ⟶ X` for a field `K` correspond
  to pairs of `x : X` with embedding `κ(x) ⟶ K`.


-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite IsLocalRing

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) {U : X.Opens}

/-- The residue field of `X` at a point `x` is the residue field of the stalk of `X`
at `x`. -/
def residueField (x : X) : CommRingCat :=
  CommRingCat.of <| IsLocalRing.ResidueField (X.presheaf.stalk x)

instance (x : X) : Field (X.residueField x) :=
  inferInstanceAs% (Field (IsLocalRing.ResidueField (X.presheaf.stalk x)))

instance (x : X) : Unique (Spec (X.residueField x)) := inferInstanceAs% (Unique (Spec <| .of _))

/-- The residue map from the stalk to the residue field. -/
def residue (X : Scheme.{u}) (x) : X.presheaf.stalk x ⟶ X.residueField x :=
  CommRingCat.ofHom (IsLocalRing.residue (X.presheaf.stalk x))

/-- See `AlgebraicGeometry.IsClosedImmersion.SpecMap_residue` for the stronger result that
`Spec.map (X.residue x)` is a closed immersion. -/
instance {X : Scheme.{u}} (x) : IsPreimmersion (Spec.map (X.residue x)) :=
  IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
      Ideal.Quotient.mk_surjective).isEmbedding
    (RingHom.surjectiveOnStalks_of_surjective (Ideal.Quotient.mk_surjective))

@[simp]
lemma SpecMap_residue_apply {X : Scheme.{u}} (x : X) (s : Spec (X.residueField x)) :
    Spec.map (X.residue x) s = closedPoint (X.presheaf.stalk x) :=
  IsLocalRing.PrimeSpectrum.comap_residue _ s

@[deprecated (since := "2025-10-07")] alias Spec_map_residue_apply := SpecMap_residue_apply

lemma residue_surjective (X : Scheme.{u}) (x) : Function.Surjective (X.residue x) :=
  Ideal.Quotient.mk_surjective

instance (X : Scheme.{u}) (x) : Epi (X.residue x) :=
  ConcreteCategory.epi_of_surjective _ (X.residue_surjective x)

/-- If `K` is a field and `f : 𝒪_{X, x} ⟶ K` is a ring map, then this is the induced
map `κ(x) ⟶ K`. -/
def descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x : X}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residueField x ⟶ .of K :=
  CommRingCat.ofHom (IsLocalRing.ResidueField.lift (S := K) f.hom)

@[reassoc (attr := simp)]
lemma residue_descResidueField {K : Type u} [Field K] {X : Scheme.{u}} {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    X.residue x ≫ X.descResidueField f = f :=
  CommRingCat.hom_ext <| RingHom.ext fun _ ↦ rfl

/--
If `U` is an open of `X` containing `x`, we have a canonical ring map from the sections
over `U` to the residue field of `x`.

If we interpret sections over `U` as functions of `X` defined on `U`, then this ring map
corresponds to evaluation at `x`.
-/
def evaluation (U : X.Opens) (x : X) (hx : x ∈ U) : Γ(X, U) ⟶ X.residueField x :=
  X.presheaf.germ U x hx ≫ X.residue _

@[reassoc]
lemma germ_residue (x hx) : X.presheaf.germ U x hx ≫ X.residue x = X.evaluation U x hx := rfl

/-- The global evaluation map from `Γ(X, ⊤)` to the residue field at `x`. -/
abbrev Γevaluation (x : X) : Γ(X, ⊤) ⟶ X.residueField x :=
  X.evaluation ⊤ x trivial

@[simp]
lemma evaluation_eq_zero_iff_notMem_basicOpen (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f = 0 ↔ x ∉ X.basicOpen f :=
  X.toLocallyRingedSpace.evaluation_eq_zero_iff_notMem_basicOpen ⟨x, hx⟩ f

lemma evaluation_ne_zero_iff_mem_basicOpen (x : X) (hx : x ∈ U) (f : Γ(X, U)) :
    X.evaluation U x hx f ≠ 0 ↔ x ∈ X.basicOpen f := by
  simp

lemma basicOpen_eq_bot_iff_forall_evaluation_eq_zero (f : X.presheaf.obj (op U)) :
    X.basicOpen f = ⊥ ↔ ∀ (x : U), X.evaluation U x x.property f = 0 :=
  X.toLocallyRingedSpace.basicOpen_eq_bot_iff_forall_evaluation_eq_zero f

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- If `X ⟶ Y` is a morphism of locally ringed spaces and `x` a point of `X`, we obtain
a morphism of residue fields in the other direction. -/
def Hom.residueFieldMap (f : X ⟶ Y) (x : X) :
    Y.residueField (f x) ⟶ X.residueField x :=
  CommRingCat.ofHom <| IsLocalRing.ResidueField.map (f.stalkMap x).hom

@[reassoc]
lemma residue_residueFieldMap (x : X) :
    Y.residue (f x) ≫ f.residueFieldMap x = f.stalkMap x ≫ X.residue x := by
  simp [Hom.residueFieldMap]
  rfl

@[simp]
lemma residueFieldMap_id (x : X) :
    Hom.residueFieldMap (𝟙 X) x = 𝟙 (X.residueField x) :=
  LocallyRingedSpace.residueFieldMap_id _

@[simp]
lemma residueFieldMap_comp {Z : Scheme.{u}} (g : Y ⟶ Z) (x : X) :
    (f ≫ g).residueFieldMap x = g.residueFieldMap (f x) ≫ f.residueFieldMap x :=
  LocallyRingedSpace.residueFieldMap_comp _ _ _

@[reassoc]
lemma evaluation_naturality {V : Opens Y} (x : X) (hx : f x ∈ V) :
    Y.evaluation V (f x) hx ≫ f.residueFieldMap x =
      f.app V ≫ X.evaluation (f ⁻¹ᵁ V) x hx :=
  LocallyRingedSpace.evaluation_naturality f.1 ⟨x, hx⟩

lemma evaluation_naturality_apply {V : Opens Y} (x : X) (hx : f x ∈ V) (s) :
    f.residueFieldMap x (Y.evaluation V (f x) hx s) =
      X.evaluation (f ⁻¹ᵁ V) x hx (f.app V s) :=
  LocallyRingedSpace.evaluation_naturality_apply f.1 ⟨x, hx⟩ s

@[reassoc]
lemma Γevaluation_naturality (x : X) :
    Y.Γevaluation (f x) ≫ f.residueFieldMap x = f.appTop ≫ X.Γevaluation x :=
  LocallyRingedSpace.Γevaluation_naturality f.toLRSHom x

lemma Γevaluation_naturality_apply (x : X) (a : Y.presheaf.obj (op ⊤)) :
    f.residueFieldMap x (Y.Γevaluation (f x) a) = X.Γevaluation x (f.appTop a) :=
  LocallyRingedSpace.Γevaluation_naturality_apply f.toLRSHom x a

instance [IsOpenImmersion f] (x) : IsIso (f.residueFieldMap x) :=
  (IsLocalRing.ResidueField.mapEquiv
    (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom

section congr

-- replace this def if hard to work with
/-- The isomorphism between residue fields of equal points. -/
def residueFieldCongr {x y : X} (h : x = y) :
    X.residueField x ≅ X.residueField y :=
  eqToIso (by subst h; rfl)

@[simp]
lemma residueFieldCongr_refl {x : X} :
    X.residueFieldCongr (refl x) = Iso.refl _ := rfl

@[simp]
lemma residueFieldCongr_symm {x y : X} (e : x = y) :
    (X.residueFieldCongr e).symm = X.residueFieldCongr e.symm := rfl

@[simp]
lemma residueFieldCongr_inv {x y : X} (e : x = y) :
    (X.residueFieldCongr e).inv = (X.residueFieldCongr e.symm).hom := rfl

@[simp]
lemma residueFieldCongr_trans {x y z : X} (e : x = y) (e' : y = z) :
    X.residueFieldCongr e ≪≫ X.residueFieldCongr e' = X.residueFieldCongr (e.trans e') := by
  subst e e'
  rfl

@[reassoc (attr := simp)]
lemma residueFieldCongr_trans_hom (X : Scheme) {x y z : X} (e : x = y) (e' : y = z) :
    (X.residueFieldCongr e).hom ≫ (X.residueFieldCongr e').hom =
      (X.residueFieldCongr (e.trans e')).hom := by
  subst e e'
  rfl

@[reassoc]
lemma residue_residueFieldCongr (X : Scheme) {x y : X} (h : x = y) :
    X.residue x ≫ (X.residueFieldCongr h).hom =
      (X.presheaf.stalkCongr (.of_eq h)).hom ≫ X.residue y := by
  subst h
  simp

lemma Hom.residueFieldMap_congr {f g : X ⟶ Y} (e : f = g) (x : X) :
    f.residueFieldMap x = (Y.residueFieldCongr (by subst e; rfl)).hom ≫ g.residueFieldMap x := by
  subst e; simp

end congr

section fromResidueField

/-- The canonical map `Spec κ(x) ⟶ X`. -/
def fromSpecResidueField (X : Scheme) (x : X) :
    Spec (X.residueField x) ⟶ X :=
  Spec.map (X.residue x) ≫ X.fromSpecStalk x

instance {X : Scheme.{u}} (x : X) : IsPreimmersion (X.fromSpecResidueField x) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [IsPreimmersion.comp_iff]
  infer_instance

@[simps] noncomputable
instance (x : X) : (Spec (X.residueField x)).Over X := ⟨X.fromSpecResidueField x⟩

noncomputable
instance (x : X) : (Spec (X.residueField x)).CanonicallyOver X where

@[reassoc (attr := simp)]
lemma residueFieldCongr_fromSpecResidueField {x y : X} (h : x = y) :
    Spec.map (X.residueFieldCongr h).hom ≫ X.fromSpecResidueField _ =
      X.fromSpecResidueField _ := by
  subst h; simp

instance {x y : X} (h : x = y) : (Spec.map (X.residueFieldCongr h).hom).IsOver X where

@[reassoc (attr := simp)]
lemma Hom.SpecMap_residueFieldMap_fromSpecResidueField (x : X) :
    Spec.map (f.residueFieldMap x) ≫ Y.fromSpecResidueField _ =
      X.fromSpecResidueField x ≫ f := by
  dsimp only [fromSpecResidueField]
  rw [Category.assoc, ← SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc]
  rfl

@[deprecated (since := "2025-10-07")]
alias Hom.Spec_map_residueFieldMap_fromSpecResidueField :=
  Hom.SpecMap_residueFieldMap_fromSpecResidueField
@[deprecated (since := "2025-10-07")]
alias Hom.Spec_map_residueFieldMap_fromSpecResidueField_assoc :=
  Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc

instance [X.Over Y] (x : X) : Spec.map ((X ↘ Y).residueFieldMap x) |>.IsOver Y where

@[simp]
lemma fromSpecResidueField_apply (x : X.carrier) (s : Spec (X.residueField x)) :
    X.fromSpecResidueField x s = x := by
  simp [fromSpecResidueField]

lemma range_fromSpecResidueField (x : X.carrier) :
    Set.range (X.fromSpecResidueField x) = {x} := by
  simp

lemma descResidueField_fromSpecResidueField {K : Type*} [Field K] (X : Scheme) {x}
    (f : X.presheaf.stalk x ⟶ .of K) [IsLocalHom f.hom] :
    Spec.map (X.descResidueField f) ≫
      X.fromSpecResidueField x = Spec.map f ≫ X.fromSpecStalk x := by
  simp [fromSpecResidueField, ← Spec.map_comp_assoc]

lemma descResidueField_stalkClosedPointTo_fromSpecResidueField
    (K : Type u) [Field K] (X : Scheme.{u}) (f : Spec (.of K) ⟶ X) :
    Spec.map (descResidueField (Scheme.stalkClosedPointTo f)) ≫
      X.fromSpecResidueField (f (closedPoint K)) = f := by
  rw [X.descResidueField_fromSpecResidueField, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

end fromResidueField

section Spec

variable (R : CommRingCat) (x : Spec R)

/-- The residue fields of `Spec R` are isomorphic to `Ideal.ResidueField`. -/
noncomputable
def Spec.residueFieldIso :
    (Spec R).residueField x ≅ .of x.asIdeal.ResidueField :=
  (IsLocalRing.ResidueField.mapEquiv
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv).toCommRingCatIso

@[reassoc (attr := simp)]
lemma Spec.algebraMap_residueFieldIso_inv :
    CommRingCat.ofHom (algebraMap R _) ≫ (residueFieldIso R x).inv =
      (Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.germ ⊤ x trivial ≫ (Spec R).residue x := by
  rw [← Spec.algebraMap_stalkIso_inv_assoc]; rfl

@[reassoc (attr := simp)]
lemma Spec.residue_residueFieldIso_hom :
    (Spec R).residue x ≫ (residueFieldIso R x).hom =
      (Spec.stalkIso R x).hom ≫ CommRingCat.ofHom (algebraMap _ _) := rfl

@[reassoc (attr := simp)]
lemma Spec.map_residueFieldIso_inv_eq_fromSpecResidueField :
    Spec.map (residueFieldIso _ _).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap R x.asIdeal.ResidueField)) =
    (Spec R).fromSpecResidueField x := by
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  rw [Spec.map_inj]
  simp [← Scheme.Spec.algebraMap_residueFieldIso_inv]

end Spec

/-- A helper lemma to work with `AlgebraicGeometry.Scheme.SpecToEquivOfField`. -/
lemma SpecToEquivOfField_eq_iff {K : Type*} [Field K] {X : Scheme}
    {f₁ f₂ : Σ x : X.carrier, X.residueField x ⟶ .of K} :
    f₁ = f₂ ↔ ∃ e : f₁.1 = f₂.1, f₁.2 = (X.residueFieldCongr e).hom ≫ f₂.2 := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨f, _⟩ := f₁
    obtain ⟨g, _⟩ := f₂
    rintro ⟨(rfl : f = g), h⟩
    simpa

/-- For a field `K` and a scheme `X`, the morphisms `Spec K ⟶ X` bijectively correspond
to pairs of points `x` of `X` and embeddings `κ(x) ⟶ K`. -/
def SpecToEquivOfField (K : Type u) [Field K] (X : Scheme.{u}) :
    (Spec (.of K) ⟶ X) ≃ Σ x, X.residueField x ⟶ .of K where
  toFun f :=
    ⟨_, X.descResidueField (Scheme.stalkClosedPointTo f)⟩
  invFun xf := Spec.map xf.2 ≫ X.fromSpecResidueField xf.1
  left_inv := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X
  right_inv f := by
    rw [SpecToEquivOfField_eq_iff]
    simp only [CommRingCat.coe_of, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply,
      Scheme.fromSpecResidueField_apply, exists_true_left]
    rw [← Spec.map_inj, Spec.map_comp, ← cancel_mono (X.fromSpecResidueField _)]
    grind [Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField,
      Scheme.fromSpecResidueField_apply,
      Scheme.residueFieldCongr_fromSpecResidueField]

end Scheme

end AlgebraicGeometry
