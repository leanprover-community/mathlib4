/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Data.List.TFAE

#align_import algebraic_geometry.morphisms.basic from "leanprover-community/mathlib"@"434e2fd21c1900747afc6d13d8be7f4eedba7218"

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `MorphismProperty Scheme` is a predicate on morphisms between schemes, and an
`AffineTargetMorphismProperty` is a predicate on morphisms into affine schemes. Given a
`P : AffineTargetMorphismProperty`, we may construct a `MorphismProperty` called
`targetAffineLocally P` that holds for `f : X ⟶ Y` whenever `P` holds for the
restriction of `f` on every affine open subset of `Y`.

## Main definitions

- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal`: We say that `P.IsLocal` if `P`
satisfies the assumptions of the affine communication lemma
(`AlgebraicGeometry.of_affine_open_cover`). That is,
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.

- `AlgebraicGeometry.IsLocalAtTarget`: We say that `IsLocalAtTarget P` for
`P : MorphismProperty Scheme` if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.

## Main results

- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_TFAE`:
  If `P.IsLocal`, then `targetAffineLocally P f` iff there exists an affine cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.
- `AlgebraicGeometry.AffineTargetMorphismProperty.isLocalOfOpenCoverImply`:
  If the existence of an affine cover `{ Uᵢ }` of `Y` such that `P` holds for `f ∣_ Uᵢ` implies
  `targetAffineLocally P f`, then `P.IsLocal`.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_target_iff`:
  If `Y` is affine and `f : X ⟶ Y`, then `targetAffineLocally P f ↔ P f` provided `P.IsLocal`.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocally_isLocal` :
  If `P.IsLocal`, then `IsLocalAtTarget (targetAffineLocally P)`.
- `AlgebraicGeometry.IsLocalAtTarget.openCover_TFAE`:
  If `IsLocalAtTarget P`, then `P f` iff there exists an open cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.

These results should not be used directly, and should be ported to each property that is local.

-/

set_option linter.uppercaseLean3 false

universe u

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

section IsLocalAtTarget

/--
We say that `P : MorphismProperty Scheme` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.
-/
class IsLocalAtTarget (P : MorphismProperty Scheme) : Prop where
  /-- `P` respects isomorphisms. -/
  RespectsIso : P.RespectsIso
  /-- If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`. -/
  restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y), P f → P (f ∣_ U)
  /-- If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.  -/
  of_sSup_eq_top :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (Us : Set (Opens Y)), sSup Us = ⊤ →
      (∀ U ∈ Us, P (f ∣_ U)) → P f
#align algebraic_geometry.property_is_local_at_target AlgebraicGeometry.IsLocalAtTarget

variable {P} [hP : IsLocalAtTarget P]
variable {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] (𝒰 : Y.OpenCover)

lemma IsLocalAtTarget.baseChange (H : P f) :
    P (pullback.snd : pullback f g ⟶ U) :=
  (hP.RespectsIso.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)).mp (restrict f g.opensRange H)

lemma IsLocalAtTarget.of_iSup_eq_top {ι} (U : ι → Opens Y) (hU : iSup U = ⊤)
    (H : ∀ i, P (f ∣_ U i)) : P f :=
  of_sSup_eq_top f (Set.range U) hU (fun _ ⟨j, e⟩ ↦ e ▸ H j)

theorem IsLocalAtTarget.iff_of_iSup_eq_top {ι} (U : ι → Opens Y) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict _ _ H, of_iSup_eq_top _ U hU⟩

lemma IsLocalAtTarget.of_openCover (H : ∀ i, P (𝒰.pullbackHom f i)) : P f := by
  apply of_iSup_eq_top f (fun i ↦ (𝒰.map i).opensRange) 𝒰.iSup_opensRange
  exact fun i ↦ (hP.RespectsIso.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

theorem IsLocalAtTarget.iff_of_openCover (𝒰 : Y.OpenCover) :
    P f ↔ ∀ i, P (𝒰.pullbackHom f i) :=
  ⟨fun H _ ↦ baseChange _ _ H, of_openCover _ _⟩

end IsLocalAtTarget

section AffineTargetMorphismProperty

/-- An `AffineTargetMorphismProperty` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def AffineTargetMorphismProperty :=
  ∀ ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop
#align algebraic_geometry.affine_target_morphism_property AlgebraicGeometry.AffineTargetMorphismProperty

/-- An `AffineTargetMorphismProperty` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def AffineTargetMorphismProperty.of (P : MorphismProperty Scheme) : AffineTargetMorphismProperty :=
  fun _ _ f _ ↦ P f

/-- `IsIso` as a `MorphismProperty`. -/
protected def Scheme.isIso : MorphismProperty Scheme :=
  @IsIso Scheme _
#align algebraic_geometry.Scheme.is_iso AlgebraicGeometry.Scheme.isIso

/-- `IsIso` as an `AffineTargetMorphismProperty`. -/
protected def Scheme.affineTargetIsIso : AffineTargetMorphismProperty := fun _ _ f _ => IsIso f
#align algebraic_geometry.Scheme.affine_target_is_iso AlgebraicGeometry.Scheme.affineTargetIsIso

instance : Inhabited AffineTargetMorphismProperty := ⟨Scheme.affineTargetIsIso⟩

/-- An `AffineTargetMorphismProperty` can be extended to a `MorphismProperty` such that it
*never* holds when the target is not affine -/
def AffineTargetMorphismProperty.toProperty (P : AffineTargetMorphismProperty) :
    MorphismProperty Scheme := fun _ _ f => ∃ h, @P _ _ f h
#align algebraic_geometry.affine_target_morphism_property.to_property AlgebraicGeometry.AffineTargetMorphismProperty.toProperty

theorem AffineTargetMorphismProperty.toProperty_apply (P : AffineTargetMorphismProperty)
    {X Y : Scheme} (f : X ⟶ Y) [i : IsAffine Y] : P.toProperty f ↔ P f := by
  delta AffineTargetMorphismProperty.toProperty; simp [*]
#align algebraic_geometry.affine_target_morphism_property.to_property_apply AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply

theorem AffineTargetMorphismProperty.cancel_left_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.cancel_left_of_respectsIso]
#align algebraic_geometry.affine_cancel_left_is_iso AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIso

theorem AffineTargetMorphismProperty.cancel_right_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]
#align algebraic_geometry.affine_cancel_right_is_iso AlgebraicGeometry.AffineTargetMorphismProperty.cancel_right_of_respectsIso

@[deprecated (since := "2024-07-02")] alias affine_cancel_left_isIso :=
  AffineTargetMorphismProperty.cancel_left_of_respectsIso
@[deprecated (since := "2024-07-02")] alias affine_cancel_right_isIso :=
  AffineTargetMorphismProperty.cancel_right_of_respectsIso

theorem affine_arrow_mk_iso_iff {P : AffineTargetMorphismProperty} (hP : P.toProperty.RespectsIso)
    {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk f') {h : IsAffine Y} :
    letI : IsAffine Y' := isAffine_of_isIso (Y := Y) e.inv.right
    P f ↔ P f' := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, hP.arrow_mk_iso_iff e]

theorem AffineTargetMorphismProperty.respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f → P (e.hom ≫ f))
    (h₂ : ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [h : IsAffine Y],
      P f → @P _ _ (f ≫ e.hom) (isAffine_of_isIso e.inv)) :
    P.toProperty.RespectsIso := by
  constructor
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨isAffine_of_isIso e.inv, h₂ e f h⟩
#align algebraic_geometry.affine_target_morphism_property.respects_iso_mk AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk

lemma AffineTargetMorphismProperty.respectsIso_of
    (P : MorphismProperty Scheme) (hP : P.RespectsIso) :
    (of P).toProperty.RespectsIso := by
  apply respectsIso_mk
  · intro _ _ _ _ _ _; apply hP.1
  · intro _ _ _ _ _ _; apply hP.2

/-- We say that `P : AffineTargetMorphismProperty` is a local property if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.
-/
class AffineTargetMorphismProperty.IsLocal (P : AffineTargetMorphismProperty) : Prop where
  /-- `P` as a morphism property respects isomorphisms -/
  respectsIso : P.toProperty.RespectsIso
  /-- `P` is stable under restriction to basic open set of global sections. -/
  to_basicOpen :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)),
      P f → @P _ _ (f ∣_ Y.basicOpen r) ((isAffineOpen_top Y).basicOpen _)
  /-- `P` for `f` if `P` holds for `f` restricted to basic sets of a spanning set of the global
    sections -/
  of_basicOpenCover :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤))
      (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤),
      (∀ r : s, @P _ _ (f ∣_ Y.basicOpen r.1) ((isAffineOpen_top Y).basicOpen _)) → P f
#align algebraic_geometry.affine_target_morphism_property.is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal

open AffineTargetMorphismProperty in
instance (P : MorphismProperty Scheme) [IsLocalAtTarget P] :
    (of P).IsLocal where
  respectsIso := respectsIso_of P IsLocalAtTarget.RespectsIso
  to_basicOpen _ _ := IsLocalAtTarget.restrict _ _
  of_basicOpenCover {_ Y} _ _ _ hs := IsLocalAtTarget.of_iSup_eq_top _ _
    (((isAffineOpen_top Y).basicOpen_union_eq_self_iff _).mpr hs)

/-- A `P : AffineTargetMorphismProperty` is stable under base change if `P` holds for `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes. -/
def AffineTargetMorphismProperty.StableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  ∀ ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
    P g → P (pullback.fst : pullback f g ⟶ X)
#align algebraic_geometry.affine_target_morphism_property.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.StableUnderBaseChange

end AffineTargetMorphismProperty

section targetAffineLocally

/-- For a `P : AffineTargetMorphismProperty`, `targetAffineLocally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => ∀ U : Y.affineOpens, P (f ∣_ U)
#align algebraic_geometry.target_affine_locally AlgebraicGeometry.targetAffineLocally

class HasAffineProperty (P : MorphismProperty Scheme) where
  protected affineProperty : AffineTargetMorphismProperty
  isLocal_affineProperty : affineProperty.IsLocal
  protected eq_targetAffineLocally' : P = targetAffineLocally affineProperty

alias _root_.CategoryTheory.MorphismProperty.affineProperty := HasAffineProperty.affineProperty

variable (P : MorphismProperty Scheme) [HasAffineProperty P]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance : P.affineProperty.IsLocal := HasAffineProperty.isLocal_affineProperty

instance (P : AffineTargetMorphismProperty) [P.IsLocal] :
    HasAffineProperty (targetAffineLocally P) :=
  ⟨P, inferInstance, rfl⟩

lemma eq_targetAffineLocally : P = targetAffineLocally P.affineProperty :=
    HasAffineProperty.eq_targetAffineLocally'

lemma iff_targetAffineLocally : P f ↔ targetAffineLocally P.affineProperty f :=
    eq_targetAffineLocally P ▸ Iff.rfl

-- move me
theorem IsAffineOpen.preimage_of_isIso {X Y : Scheme} {U : Opens Y.carrier} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsIso f] : IsAffineOpen (f ⁻¹ᵁ U) :=
  haveI : IsAffine _ := hU
  isAffine_of_isIso (f ∣_ U)
#align algebraic_geometry.is_affine_open.map_is_iso AlgebraicGeometry.IsAffineOpen.preimage_of_isIso

theorem HasAffineProperty.restrict (hf : P f) (U : Y.affineOpens) :
    P.affineProperty (f ∣_ U) :=
  (iff_targetAffineLocally P f).mp hf U

theorem HasAffineProperty.respectsIso_mk :
    P.RespectsIso := by
  rw [eq_targetAffineLocally P]
  constructor
  · introv H U
    rw [morphismRestrict_comp, affine_cancel_left_isIso
      (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty))]
    exact H U
  · introv H
    rintro ⟨U, hU : IsAffineOpen U⟩; dsimp
    haveI : IsAffine _ := hU.preimage_of_isIso e.hom
    rw [morphismRestrict_comp, affine_cancel_right_isIso
      (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty))]
    exact H ⟨(Opens.map e.hom.val.base).obj U, hU.preimage_of_isIso e.hom⟩
#align algebraic_geometry.target_affine_locally_respects_iso AlgebraicGeometry.HasAffineProperty.respectsIso_mk

-- move me
/-- Specialization of `ConcreteCategory.id_apply` because `simp` can't see through the defeq. -/
@[local simp] lemma CommRingCat.id_apply (R : CommRingCat) (x : R) : 𝟙 R x = x := rfl

-- move me
attribute [-simp] eqToHom_op in
@[simps!]
def Scheme.resTop (X : Scheme.{u}) (U : Opens X) : Γ(X ∣_ᵤ U, ⊤) ≅ Γ(X, U) :=
  X.presheaf.mapIso (eqToIso U.openEmbedding_obj_top.symm).op

theorem HasAffineProperty.of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Opens Y) = ⊤)
    (hU' : ∀ i, P.affineProperty (f ∣_ U i)) :
    P f := by
  rw [eq_targetAffineLocally P]
  classical
  intro V
  induction V using of_affine_open_cover U hU  with
  | basicOpen U r h =>
    haveI : IsAffine _ := U.2
    have := AffineTargetMorphismProperty.IsLocal.to_basicOpen (f ∣_ U.1) ((Y.resTop U).inv r) h
    exact (affine_arrow_mk_iso_iff (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty))
      (morphismRestrictRestrictBasicOpen f _ r)).mp this
  | openCover U s hs H =>
    apply AffineTargetMorphismProperty.IsLocal.of_basicOpenCover _
      (s.image (Y.resTop _).inv) (by simp [← Ideal.map_span, hs, Ideal.map_top])
    intro ⟨r, hr⟩
    obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hr
    exact (affine_arrow_mk_iso_iff
      (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty))
      (morphismRestrictRestrictBasicOpen f _ r).symm).mp (H ⟨r, hr'⟩)
  | hU i => exact hU' i

theorem HasAffineProperty.iff_of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Opens Y) = ⊤) :
    P f ↔ ∀ i, P.affineProperty (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict P f H _, fun H ↦ HasAffineProperty.of_iSup_eq_top P f U hU H⟩

theorem HasAffineProperty.of_openCover
    (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.obj i)] (h𝒰 : ∀ i, P.affineProperty (𝒰.pullbackHom f i)) :
    P f := by
  apply of_iSup_eq_top P f
    (fun i ↦ ⟨_, isAffineOpen_opensRange (𝒰.map i)⟩) 𝒰.iSup_opensRange
    (fun i ↦ (affine_arrow_mk_iso_iff (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty)) (morphismRestrictOpensRange f _)).mpr (h𝒰 i))
#align algebraic_geometry.target_affine_locally_of_open_cover AlgebraicGeometry.HasAffineProperty.of_openCover

theorem HasAffineProperty.iff_of_openCover
    (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.obj i)] :
    P f ↔ ∀ i, P.affineProperty (𝒰.pullbackHom f i) := by
  rw [iff_of_iSup_eq_top P f
    (fun i ↦ ⟨_, isAffineOpen_opensRange _⟩) 𝒰.iSup_opensRange]
  exact forall_congr' fun i ↦ affine_arrow_mk_iso_iff (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty)) (morphismRestrictOpensRange f _)

theorem HasAffineProperty.morphsimRestrict
    (U : Opens Y) (H : P f) : P (f ∣_ U) := by
  rw [eq_targetAffineLocally P] at H ⊢
  intros V
  rw [affine_arrow_mk_iso_iff (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty)) (morphismRestrictRestrict _ _ _)]
  exact H ⟨_, V.2.image_of_isOpenImmersion _⟩

protected
theorem HasAffineProperty.pullback {U} (g : U ⟶ Y) [IsOpenImmersion g] (h : P f) :
    P (pullback.snd : pullback f g ⟶ _) := by
  rw [← (respectsIso_mk P).arrow_mk_iso_iff (morphismRestrictOpensRange _ _)]
  exact morphsimRestrict P f _ h

theorem HasAffineProperty.iff_of_isAffine [IsAffine Y] :
    P f ↔ P.affineProperty f := by
  haveI : ∀ i, IsAffine (Scheme.OpenCover.obj (Scheme.openCoverOfIsIso (𝟙 Y)) i) := fun i => by
    dsimp; infer_instance
  rw [iff_of_openCover P f (Scheme.openCoverOfIsIso.{0} (𝟙 Y))]
  trans P.affineProperty (pullback.snd : pullback f (𝟙 _) ⟶ _)
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_isIso (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty))]
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_target_iff AlgebraicGeometry.HasAffineProperty.iff_of_isAffine

theorem HasAffineProperty.pullback_of_isAffine {U} (g : U ⟶ Y) [IsOpenImmersion g] [IsAffine U]
    (h : P f) : P.affineProperty (pullback.snd : pullback f g ⟶ _) := by
  rw [← iff_of_isAffine P]
  exact HasAffineProperty.pullback P f _ h

def Scheme.OpenCover.pullbackCoverAffineRefinementObj (𝒰 : Y.OpenCover) (i) :
    (𝒰.affineRefinement.openCover.pullbackCover f).obj i ≅
      pullback (𝒰.pullbackHom f i.1) ((𝒰.obj i.1).affineCover.map i.2) := by
  refine pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
    pullbackSymmetry _ _ ≪≫
      asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_)
  · simp [pullbackHom]
  · simp

@[reassoc (attr := simp)]
lemma Scheme.OpenCover.pullbackCoverAffineRefinementObj_inv_map (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObj f i).inv ≫
      (𝒰.affineRefinement.openCover.pullbackCover f).map i =
      pullback.fst ≫ (𝒰.pullbackCover f).map i.1 := by
  simp only [pullbackCover_obj, AffineOpenCover.openCover_obj, AffineOpenCover.openCover_map,
    pullbackCoverAffineRefinementObj, Iso.trans_inv, asIso_inv, Iso.symm_inv, Category.assoc,
    pullbackCover_map, pullbackSymmetry_inv_comp_fst, IsIso.inv_comp_eq, limit.lift_π_assoc, id_eq,
    PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app, pullbackSymmetry_hom_comp_fst]
  convert pullbackSymmetry_inv_comp_snd_assoc
    ((𝒰.obj i.1).affineCover.map i.2) pullback.fst _ using 2
  exact pullbackRightPullbackFstIso_hom_snd _ _ _

@[reassoc (attr := simp)]
lemma Scheme.OpenCover.pullbackCoverAffineRefinementObj_inv_pullbackHom (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObj f i).inv ≫
      𝒰.affineRefinement.openCover.pullbackHom f i =
      pullback.snd := by
  simp only [pullbackCover_obj, pullbackHom, AffineOpenCover.openCover_obj,
    AffineOpenCover.openCover_map, pullbackCoverAffineRefinementObj, Iso.trans_inv, asIso_inv,
    Iso.symm_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, IsIso.inv_comp_eq, limit.lift_π,
    id_eq, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id]
  convert pullbackSymmetry_inv_comp_fst ((𝒰.obj i.1).affineCover.map i.2) pullback.fst
  exact pullbackRightPullbackFstIso_hom_fst _ _ _

instance (𝒰 : X.AffineOpenCover) (i) : IsAffine (𝒰.openCover.obj i) :=
  inferInstanceAs (IsAffine (Spec (𝒰.obj i)))

instance HasAffineProperty.isLocalAtTarget_mk :
    IsLocalAtTarget P := by
  constructor
  · exact respectsIso_mk P
  · rw [eq_targetAffineLocally P]
    intro X Y f U H V
    rw [affine_arrow_mk_iso_iff (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty)) (morphismRestrictRestrict f _ _)]
    exact H ⟨_, V.2.image_of_isOpenImmersion (Y.ofRestrict _)⟩
  · rintro X Y f Us hU H
    let 𝒰 := Y.openCoverOfSuprEqTop (fun i : Us ↦ i) (by rwa [iSup_subtype, ← sSup_eq_iSup])
    apply of_openCover P _ 𝒰.affineRefinement.openCover
    rintro ⟨i, j⟩
    have : P (𝒰.pullbackHom f i) := by
      refine ((respectsIso_mk P).arrow_mk_iso_iff
        (morphismRestrictEq _ ?_ ≪≫ morphismRestrictOpensRange f (𝒰.map i))).mp (H _ i.2)
      exact (opensRange_ιOpens _).symm
    rw [← affine_cancel_left_isIso (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty)) (𝒰.pullbackCoverAffineRefinementObj f _).inv,
      𝒰.pullbackCoverAffineRefinementObj_inv_pullbackHom]
    exact pullback_of_isAffine P _ ((𝒰.obj i).affineCover.map j) this
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_is_local AlgebraicGeometry.HasAffineProperty.isLocalAtTarget_mk

theorem HasAffineProperty.pullback_fst_of_right (hP' : P.affineProperty.StableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : P.affineProperty g) :
    P (pullback.fst : pullback f g ⟶ X) := by
  rw [iff_of_openCover P _ X.affineCover]
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.map i)
  have : e.hom ≫ pullback.fst = X.affineCover.pullbackHom pullback.fst i := by
    simp [e, Scheme.OpenCover.pullbackHom]
  rw [← this, affine_cancel_left_isIso (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty))]
  apply hP' _ _
  exact H
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_pullback_fst_of_right_of_stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocally_pullback_fst_of_right_of_stableUnderBaseChange

theorem HasAffineProperty.stableUnderBaseChange_mk (hP' : P.affineProperty.StableUnderBaseChange) :
    P.StableUnderBaseChange :=
  MorphismProperty.StableUnderBaseChange.mk (respectsIso_mk P)
    (fun X Y S f g H => by
      rw [IsLocalAtTarget.iff_of_openCover (P := P) _ (S.affineCover.pullbackCover f)]
      intro i
      let e : pullback (pullback.fst : pullback f g ⟶ _) ((S.affineCover.pullbackCover f).map i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g _ ≪≫ ?_ ≪≫
          (pullbackRightPullbackFstIso (S.affineCover.map i) g
            (pullback.snd : pullback f (S.affineCover.map i) ⟶ _)).symm
        exact asIso
          (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst =
          (S.affineCover.pullbackCover f).pullbackHom pullback.fst i := by
        simp [e, Scheme.OpenCover.pullbackHom]
      rw [← this, (respectsIso_mk P).cancel_left_isIso]
      apply HasAffineProperty.pullback_fst_of_right P hP'
      rw [← pullbackSymmetry_hom_comp_snd, affine_cancel_left_isIso (AffineTargetMorphismProperty.IsLocal.respectsIso (P := P.affineProperty))]
      apply pullback_of_isAffine P _ _ H)
#align algebraic_geometry.affine_target_morphism_property.is_local.stable_under_base_change AlgebraicGeometry.HasAffineProperty.stableUnderBaseChange_mk

end targetAffineLocally

end AlgebraicGeometry
