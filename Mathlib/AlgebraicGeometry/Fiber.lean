/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Sheaves.Init

/-!
# Scheme-theoretic fiber

## Main result
- `AlgebraicGeometry.Scheme.Hom.fiber`: `f.fiber y` is the scheme-theoretic fiber of `f` at `y`.
- `AlgebraicGeometry.Scheme.Hom.fiberHomeo`: `f.fiber y` is homeomorphic to `f ⁻¹' {y}`.
- `AlgebraicGeometry.Scheme.Hom.finite_preimage`: Finite morphisms have finite fibers.
- `AlgebraicGeometry.Scheme.Hom.discrete_fiber`: Finite morphisms have discrete fibers.

-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- `f.fiber y` is the scheme-theoretic fiber of `f` at `y`. -/
def Scheme.Hom.fiber (f : X ⟶ Y) (y : Y) : Scheme := pullback f (Y.fromSpecResidueField y)

/-- `f.fiberι y : f.fiber y ⟶ X` is the embedding of the scheme-theoretic fiber into `X`. -/
def Scheme.Hom.fiberι (f : X ⟶ Y) (y : Y) : f.fiber y ⟶ X := pullback.fst _ _

instance (f : X ⟶ Y) (y : Y) : (f.fiber y).CanonicallyOver X where hom := f.fiberι y

/-- The canonical map from the scheme-theoretic fiber to the residue field. -/
def Scheme.Hom.fiberToSpecResidueField (f : X ⟶ Y) (y : Y) :
    f.fiber y ⟶ Spec (Y.residueField y) :=
  pullback.snd _ _

/-- The fiber of `f` at `y` is naturally a `κ(y)`-scheme. -/
@[reducible] def Scheme.Hom.fiberOverSpecResidueField
    (f : X ⟶ Y) (y : Y) : (f.fiber y).Over (Spec (Y.residueField y)) where
  hom := f.fiberToSpecResidueField y

lemma Scheme.Hom.fiberToSpecResidueField_apply (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    f.fiberToSpecResidueField y x = IsLocalRing.closedPoint (Y.residueField y) :=
  Subsingleton.elim (α := PrimeSpectrum _) _ _

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_fiberToSpecResidueField_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) :
    IsPullback (pullback.map _ _ _ _ fst (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp))
      (snd.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y))
      (Spec.map (g.residueFieldMap y)) := by
  refine .of_right (h₁₂ := pullback.fst _ _) ?_ ?_
      (IsPullback.of_hasPullback f (Z.fromSpecResidueField (g y)))
  · simpa using (IsPullback.of_hasPullback _ _).paste_horiz h
  · simp [Scheme.Hom.fiberToSpecResidueField]

set_option backward.isDefEq.respectTransparency false in
/-- The morphism from the fiber of `Spec S ⟶ Spec R` at some prime `p` to `Spec κ(p)`
is isomorphic to the map induced by `κ(p) ⟶ κ(p) ⊗[R] S`. -/
noncomputable def Spec.fiberToSpecResidueFieldIso (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (p : PrimeSpectrum R) :
    Arrow.mk ((Spec.map (CommRingCat.ofHom <| algebraMap R S)).fiberToSpecResidueField p) ≅
      Arrow.mk (Spec.map <| CommRingCat.ofHom <|
        algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber S)) := by
  refine Arrow.isoMk' _ _
    (pullbackSymmetry _ _ ≪≫ ?_ ≪≫ pullbackSpecIso R p.asIdeal.ResidueField S) ?_ ?_
  · refine pullback.congrHom
      (Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) p).symm rfl ≪≫ ?_
    refine asIso <| pullback.map _ _ _ _ (Spec.map <| (Scheme.Spec.residueFieldIso (.of R) _).inv)
      (𝟙 _) (𝟙 _) (by simp) (by simp)
  · exact Scheme.Spec.mapIso (Scheme.Spec.residueFieldIso (.of R) _).symm.op
  · cat_disch

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Hom.range_fiberι (f : X ⟶ Y) (y : Y) :
    Set.range (f.fiberι y) = f ⁻¹' {y} := by
  simp [fiber, fiberι, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]

instance (f : X ⟶ Y) (y : Y) : IsPreimmersion (f.fiberι y) :=
  MorphismProperty.pullback_fst _ _ inferInstance

/-- The scheme-theoretic fiber of `f` at `y` is homeomorphic to `f ⁻¹' {y}`. -/
def Scheme.Hom.fiberHomeo (f : X ⟶ Y) (y : Y) : f.fiber y ≃ₜ f ⁻¹' {y} :=
  .trans (f.fiberι y).isEmbedding.toHomeomorph (.setCongr (f.range_fiberι y))

@[simp]
lemma Scheme.Hom.fiberHomeo_apply (f : X ⟶ Y) (y : Y) (x : f.fiber y) :
    (f.fiberHomeo y x).1 = f.fiberι y x := rfl

@[simp]
lemma Scheme.Hom.fiberι_fiberHomeo_symm (f : X ⟶ Y) (y : Y) (x : f ⁻¹' {y}) :
    f.fiberι y ((f.fiberHomeo y).symm x) = x :=
  congr($((f.fiberHomeo y).apply_symm_apply x).1)

/-- A point `x` as a point in the fiber of `f` at `f x`. -/
def Scheme.Hom.asFiber (f : X ⟶ Y) (x : X) : f.fiber (f x) :=
    (f.fiberHomeo (f x)).symm ⟨x, rfl⟩

@[simp]
lemma Scheme.Hom.fiberι_asFiber (f : X ⟶ Y) (x : X) : f.fiberι _ (f.asFiber x) = x :=
  f.fiberι_fiberHomeo_symm _ _

instance (f : X ⟶ Y) [QuasiCompact f] (y : Y) : CompactSpace (f.fiber y) :=
  haveI : QuasiCompact (f.fiberToSpecResidueField y) :=
      MorphismProperty.pullback_snd _ _ inferInstance
  HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)
    (f := f.fiberToSpecResidueField y).mp inferInstance

lemma Scheme.Hom.isCompact_preimage_singleton (f : X ⟶ Y) [QuasiCompact f] (y : Y) :
    IsCompact (f ⁻¹' {y}) :=
  f.range_fiberι y ▸ isCompact_range (f.fiberι y).continuous

@[deprecated (since := "2026-02-05")]
alias QuasiCompact.isCompact_preimage_singleton := Scheme.Hom.isCompact_preimage_singleton

instance (f : X ⟶ Y) [IsAffineHom f] (y : Y) : IsAffine (f.fiber y) :=
  haveI : IsAffineHom (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  isAffine_of_isAffineHom (f.fiberToSpecResidueField y)

instance (f : X ⟶ Y) (y : Y) [LocallyOfFiniteType f] : JacobsonSpace (f.fiber y) :=
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  LocallyOfFiniteType.jacobsonSpace (f.fiberToSpecResidueField y)

/-- The `κ(x)`-point of `f ⁻¹' {f x}` corresponding to `x`. -/
def Scheme.Hom.asFiberHom (f : X ⟶ Y) (x : X) : Spec (X.residueField x) ⟶ f.fiber (f x) :=
  pullback.lift (X.fromSpecResidueField x) (Spec.map (f.residueFieldMap _)) (by simp)

@[reassoc (attr := simp)]
lemma Scheme.Hom.asFiberHom_fiberι (f : X ⟶ Y) (x : X) :
    f.asFiberHom x ≫ f.fiberι _ = X.fromSpecResidueField x := pullback.lift_fst ..

@[reassoc (attr := simp)]
lemma Scheme.Hom.asFiberHom_fiberToSpecResidueField (f : X ⟶ Y) (x : X) :
    f.asFiberHom x ≫ f.fiberToSpecResidueField _ = Spec.map (f.residueFieldMap _) :=
  pullback.lift_snd ..

@[simp]
lemma Scheme.Hom.asFiberHom_apply (f : X ⟶ Y) (x : X) (y) :
    f.asFiberHom x y = f.asFiber x :=
  (f.fiberι _).isEmbedding.injective (by simp [← Scheme.Hom.comp_apply])

@[simp]
lemma Scheme.Hom.range_asFiberHom (f : X ⟶ Y) (x : X) :
    Set.range (f.asFiberHom x) = {f.asFiber x} := by aesop

instance (f : X ⟶ Y) (x : X) : IsPreimmersion (f.asFiberHom x) :=
  have : IsPreimmersion (f.asFiberHom x ≫ f.fiberι _) := f.asFiberHom_fiberι x ▸ inferInstance
  .of_comp _ (f.fiberι _)

end AlgebraicGeometry
