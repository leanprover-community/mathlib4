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

A `MorphismProperty Scheme` is a predicate on morphisms between schemes. For properties local at
the target, its behaviour is entirely determined by its definition on morphisms into affine schemes,
which we call an `AffineTargetMorphismProperty`. In this file, we provide API lemmas for properties
local at the target, and special support for those properties whose `AffineTargetMorphismProperty`
takes on a more simple form. The main interfaces of the API are the typeclasses
`IsLocalAtTarget` and `HasAffineProperty`, which we describle in detail below.

## `IsLocalAtTarget`

- `AlgebraicGeometry.IsLocalAtTarget`: We say that `IsLocalAtTarget P` for
`P : MorphismProperty Scheme` if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any open `U` of `Y`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.

For a morphism property `P` local at the target and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsLocalAtTarget.of_isPullback`:
    `P` is preserved under pullback along open immersions.
- `AlgebraicGeometry.IsLocalAtTarget.restrict`:
    `P f → P (f ∣_ U)` for an open `U` of `Y`.
- `AlgebraicGeometry.IsLocalAtTarget.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P (f ∣_ U i)` for a family `U i` of open sets covering `Y`.
- `AlgebraicGeometry.IsLocalAtTarget.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.pullbackHom f i)` for `𝒰 : Y.openCover`.

## `AffineTargetMorphismProperty`

- `AlgebraicGeometry.AffineTargetMorphismProperty`:
    The type of predicates on `f : X ⟶ Y` with `Y` affine.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal`: We say that `P.IsLocal` if `P`
    satisfies the assumptions of the affine communication lemma
    (`AlgebraicGeometry.of_affine_open_cover`). That is,
    1. `P` respects isomorphisms.
    2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
      global section `r`.
    3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
      then `P` holds for `f`.

## `HasAffineProperty`

- `AlgebraicGeometry.HasAffineProperty`:
  `HasAffineProperty P Q` is a type class asserting that `P` is local at the target,
  and over affine schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.

For `HasAffineProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.HasAffineProperty.of_isPullback`:
    `P` is preserved under pullback along open immersions from affine schemes.
- `AlgebraicGeometry.HasAffineProperty.restrict`:
    `P f → Q (f ∣_ U)` for affine `U` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, Q (f ∣_ U i)` for a family `U i` of affine open sets covering `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.pullbackHom f i)` for affine open covers `𝒰` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.stableUnderBaseChange_mk`:
    If `Q` is stable under affine base change, then `P` is stable under arbitrary base change.
-/

set_option linter.uppercaseLean3 false

universe u

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/--
We say that `P : MorphismProperty Scheme` is local at the target if
1. `P` respects isomorphisms.
2. `P` holds for `f ∣_ U` for an open cover `U` of `Y` if and only if `P` holds for `f`.
Also see `IsLocalAtTarget.mk'` for a convenient constructor.
-/
class IsLocalAtTarget (P : MorphismProperty Scheme) : Prop where
  /-- `P` respects isomorphisms. -/
  respectsIso : P.RespectsIso := by infer_instance
  /-- `P` holds for `f ∣_ U` for an open cover `U` of `Y` if and only if `P` holds for `f`.  -/
  iff_of_openCover' :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y),
      P f ↔ ∀ i, P (𝒰.pullbackHom f i)
#align algebraic_geometry.property_is_local_at_target AlgebraicGeometry.IsLocalAtTarget

namespace IsLocalAtTarget

attribute [instance] respectsIso

/--
`P` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.
-/
protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y), P f → P (f ∣_ U))
    (of_sSup_eq_top :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y), iSup U = ⊤ →
        (∀ i, P (f ∣_ U i)) → P f) :
    IsLocalAtTarget P := by
  refine ⟨inferInstance, fun {X Y} f 𝒰 ↦ ⟨?_, fun H ↦ of_sSup_eq_top f _ 𝒰.iSup_opensRange ?_⟩⟩
  · exact fun H i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp (restrict _ _ H)
  · exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

/-- The intersection of two morphism properties that are local at the target is again local at
the target. -/
instance inf (P Q : MorphismProperty Scheme) [IsLocalAtTarget P] [IsLocalAtTarget Q] :
    IsLocalAtTarget (P ⊓ Q) where
  iff_of_openCover' {X Y} f 𝒰 :=
    ⟨fun h i ↦ ⟨(iff_of_openCover' f 𝒰).mp h.left i, (iff_of_openCover' f 𝒰).mp h.right i⟩,
     fun h ↦ ⟨(iff_of_openCover' f 𝒰).mpr (fun i ↦ (h i).left),
      (iff_of_openCover' f 𝒰).mpr (fun i ↦ (h i).right)⟩⟩

variable {P} [hP : IsLocalAtTarget P]
variable {X Y U V : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y} [IsOpenImmersion g] (𝒰 : Y.OpenCover)

lemma of_isPullback {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (H : P f) : P f' := by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact (iff_of_openCover' f (Y.affineCover.add iY)).mp H .none

theorem restrict (hf : P f) (U : Opens Y) : P (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf

lemma of_iSup_eq_top {ι} (U : ι → Opens Y) (hU : iSup U = ⊤)
    (H : ∀ i, P (f ∣_ U i)) : P f := by
  refine (IsLocalAtTarget.iff_of_openCover' f
    (Y.openCoverOfSuprEqTop (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i ↦ ?_
  obtain ⟨_, i, rfl⟩ := i
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp ?_
  show P (f ∣_ (Scheme.ιOpens (U i)).opensRange)
  rw [opensRange_ιOpens]
  exact H i

theorem iff_of_iSup_eq_top {ι} (U : ι → Opens Y) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict H _, of_iSup_eq_top U hU⟩

lemma of_openCover (H : ∀ i, P (𝒰.pullbackHom f i)) : P f := by
  apply of_iSup_eq_top (fun i ↦ (𝒰.map i).opensRange) 𝒰.iSup_opensRange
  exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

theorem iff_of_openCover (𝒰 : Y.OpenCover) :
    P f ↔ ∀ i, P (𝒰.pullbackHom f i) :=
  ⟨fun H _ ↦ of_isPullback (.of_hasPullback _ _) H, of_openCover _⟩

end IsLocalAtTarget

/-- An `AffineTargetMorphismProperty` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def AffineTargetMorphismProperty :=
  ∀ ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop
#align algebraic_geometry.affine_target_morphism_property AlgebraicGeometry.AffineTargetMorphismProperty

namespace AffineTargetMorphismProperty

@[ext]
lemma ext {P Q : AffineTargetMorphismProperty}
    (H : ∀ ⦃X Y : Scheme⦄ (f : X ⟶ Y) [IsAffine Y], P f ↔ Q f) : P = Q := by
  delta AffineTargetMorphismProperty; ext; exact H _

/-- The restriction of a `MorphismProperty Scheme` to morphisms with affine target. -/
def of (P : MorphismProperty Scheme) : AffineTargetMorphismProperty :=
  fun _ _ f _ ↦ P f

/-- An `AffineTargetMorphismProperty` can be extended to a `MorphismProperty` such that it
*never* holds when the target is not affine -/
def toProperty (P : AffineTargetMorphismProperty) :
    MorphismProperty Scheme := fun _ _ f => ∃ h, @P _ _ f h
#align algebraic_geometry.affine_target_morphism_property.to_property AlgebraicGeometry.AffineTargetMorphismProperty.toProperty

theorem toProperty_apply (P : AffineTargetMorphismProperty)
    {X Y : Scheme} (f : X ⟶ Y) [i : IsAffine Y] : P.toProperty f ↔ P f := by
  delta AffineTargetMorphismProperty.toProperty; simp [*]
#align algebraic_geometry.affine_target_morphism_property.to_property_apply AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply

theorem cancel_left_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.cancel_left_of_respectsIso]
#align algebraic_geometry.affine_cancel_left_is_iso AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIso

theorem cancel_right_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]
#align algebraic_geometry.affine_cancel_right_is_iso AlgebraicGeometry.AffineTargetMorphismProperty.cancel_right_of_respectsIso

@[deprecated (since := "2024-07-02")] alias affine_cancel_left_isIso :=
  AffineTargetMorphismProperty.cancel_left_of_respectsIso
@[deprecated (since := "2024-07-02")] alias affine_cancel_right_isIso :=
  AffineTargetMorphismProperty.cancel_right_of_respectsIso

theorem arrow_mk_iso_iff
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk f') {h : IsAffine Y} :
    letI : IsAffine Y' := isAffine_of_isIso (Y := Y) e.inv.right
    P f ↔ P f' := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.arrow_mk_iso_iff e]

theorem respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f → P (e.hom ≫ f))
    (h₂ : ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [h : IsAffine Y],
      P f → @P _ _ (f ≫ e.hom) (isAffine_of_isIso e.inv)) :
    P.toProperty.RespectsIso := by
  constructor
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨isAffine_of_isIso e.inv, h₂ e f h⟩
#align algebraic_geometry.affine_target_morphism_property.respects_iso_mk AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk

instance respectsIso_of
    (P : MorphismProperty Scheme) [P.RespectsIso] :
    (of P).toProperty.RespectsIso := by
  apply respectsIso_mk
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.precomp
  · intro _ _ _ _ _ _; apply MorphismProperty.RespectsIso.postcomp

/-- We say that `P : AffineTargetMorphismProperty` is a local property if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.
-/
class IsLocal (P : AffineTargetMorphismProperty) : Prop where
  /-- `P` as a morphism property respects isomorphisms -/
  respectsIso : P.toProperty.RespectsIso
  /-- `P` is stable under restriction to basic open set of global sections. -/
  to_basicOpen :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)), P f → P (f ∣_ Y.basicOpen r)
  /-- `P` for `f` if `P` holds for `f` restricted to basic sets of a spanning set of the global
    sections -/
  of_basicOpenCover :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤))
      (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤), (∀ r : s, P (f ∣_ Y.basicOpen r.1)) → P f
#align algebraic_geometry.affine_target_morphism_property.is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal

attribute [instance] AffineTargetMorphismProperty.IsLocal.respectsIso

open AffineTargetMorphismProperty in
instance (P : MorphismProperty Scheme) [IsLocalAtTarget P] : (of P).IsLocal where
  respectsIso := inferInstance
  to_basicOpen _ _ H := IsLocalAtTarget.restrict H _
  of_basicOpenCover {_ Y} _ _ _ hs := IsLocalAtTarget.of_iSup_eq_top _
    (((isAffineOpen_top Y).basicOpen_union_eq_self_iff _).mpr hs)

/-- A `P : AffineTargetMorphismProperty` is stable under base change if `P` holds for `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes. -/
def StableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  ∀ ⦃Z X Y S : Scheme⦄ [IsAffine S] [IsAffine X] {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Z ⟶ Y} {g' : Z ⟶ X}, IsPullback g' f' f g → P g → P g'
#align algebraic_geometry.affine_target_morphism_property.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.StableUnderBaseChange

lemma StableUnderBaseChange.mk (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    (H : ∀ ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
      P g → P (pullback.fst f g)) : P.StableUnderBaseChange := by
  intros Z X Y S _ _ f g f' g' h hg
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_fst]
  exact H f g hg

end AffineTargetMorphismProperty

section targetAffineLocally

/-- For a `P : AffineTargetMorphismProperty`, `targetAffineLocally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => ∀ U : Y.affineOpens, P (f ∣_ U)
#align algebraic_geometry.target_affine_locally AlgebraicGeometry.targetAffineLocally

theorem of_targetAffineLocally_of_isPullback
    {P : AffineTargetMorphismProperty} [P.IsLocal]
    {X Y UX UY : Scheme.{u}} [IsAffine UY] {f : X ⟶ Y} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (hf : targetAffineLocally P f) :
    P f' := by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact (P.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)).mp (hf ⟨_, isAffineOpen_opensRange iY⟩)

instance (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] :
    (targetAffineLocally P).RespectsIso := by
  constructor
  · introv H U
    rw [morphismRestrict_comp, P.cancel_left_of_respectsIso]
    exact H U
  · introv H
    rintro ⟨U, hU : IsAffineOpen U⟩; dsimp
    haveI : IsAffine _ := hU.preimage_of_isIso e.hom
    rw [morphismRestrict_comp, P.cancel_right_of_respectsIso]
    exact H ⟨(Opens.map e.hom.val.base).obj U, hU.preimage_of_isIso e.hom⟩

/--
`HasAffineProperty P Q` is a type class asserting that `P` is local at the target, and over affine
schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.
To make the proofs easier, we state it instead as
1. `Q` is local at the target
2. `P f` if and only if `∀ U, Q (f ∣_ U)` ranging over all affine opens of `U`.
See `HasAffineProperty.iff`.
-/
class HasAffineProperty (P : MorphismProperty Scheme)
    (Q : outParam AffineTargetMorphismProperty) : Prop where
  isLocal_affineProperty : Q.IsLocal
  eq_targetAffineLocally' : P = targetAffineLocally Q

namespace HasAffineProperty

variable (P : MorphismProperty Scheme) {Q} [HasAffineProperty P Q]
variable {X Y : Scheme.{u}} {f : X ⟶ Y}

instance (Q : AffineTargetMorphismProperty) [Q.IsLocal] :
    HasAffineProperty (targetAffineLocally Q) Q :=
  ⟨inferInstance, rfl⟩

lemma eq_targetAffineLocally : P = targetAffineLocally Q := eq_targetAffineLocally'

/-- Every property local at the target can be associated with an affine target property.
This is not an instance as the associated property can often take on simpler forms. -/
lemma of_isLocalAtTarget (P) [IsLocalAtTarget P] :
    HasAffineProperty P (AffineTargetMorphismProperty.of P) where
  isLocal_affineProperty := inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    constructor
    · intro hf ⟨U, hU⟩
      exact IsLocalAtTarget.restrict hf _
    · intro hf
      exact IsLocalAtTarget.of_openCover (P := P) Y.affineCover
        fun i ↦ of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) hf

lemma copy {P P'} {Q Q'} [HasAffineProperty P Q]
    (e : P = P') (e' : Q = Q') : HasAffineProperty P' Q' where
  isLocal_affineProperty := e' ▸ isLocal_affineProperty P
  eq_targetAffineLocally' := e' ▸ e.symm ▸ eq_targetAffineLocally P

variable {P}

theorem of_isPullback {UX UY : Scheme.{u}} [IsAffine UY] {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (hf : P f) :
    Q f' :=
  letI := isLocal_affineProperty P
  of_targetAffineLocally_of_isPullback h (eq_targetAffineLocally (P := P) ▸ hf)

theorem restrict (hf : P f) (U : Y.affineOpens) :
    Q (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf

instance (priority := 900) : P.RespectsIso := by
  letI := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  infer_instance
#align algebraic_geometry.target_affine_locally_respects_iso AlgebraicGeometry.HasAffineProperty.instRespectsIsoScheme

theorem of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Opens Y) = ⊤)
    (hU' : ∀ i, Q (f ∣_ U i)) :
    P f := by
  letI := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  classical
  intro V
  induction V using of_affine_open_cover U hU  with
  | basicOpen U r h =>
    haveI : IsAffine _ := U.2
    have := AffineTargetMorphismProperty.IsLocal.to_basicOpen (f ∣_ U.1) ((Y.resTop U).inv r) h
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r)).mp this
  | openCover U s hs H =>
    apply AffineTargetMorphismProperty.IsLocal.of_basicOpenCover _
      (s.image (Y.resTop _).inv) (by simp [← Ideal.map_span, hs, Ideal.map_top])
    intro ⟨r, hr⟩
    obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hr
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r).symm).mp (H ⟨r, hr'⟩)
  | hU i => exact hU' i

theorem iff_of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Opens Y) = ⊤) :
    P f ↔ ∀ i, Q (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict H _, fun H ↦ HasAffineProperty.of_iSup_eq_top U hU H⟩

theorem of_openCover
    (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.obj i)] (h𝒰 : ∀ i, Q (𝒰.pullbackHom f i)) :
    P f :=
  letI := isLocal_affineProperty P
  of_iSup_eq_top
    (fun i ↦ ⟨_, isAffineOpen_opensRange (𝒰.map i)⟩) 𝒰.iSup_opensRange
    (fun i ↦ (Q.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h𝒰 i))
#align algebraic_geometry.target_affine_locally_of_open_cover AlgebraicGeometry.HasAffineProperty.of_openCover

theorem iff_of_openCover (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.obj i)] :
    P f ↔ ∀ i, Q (𝒰.pullbackHom f i) := by
  letI := isLocal_affineProperty P
  rw [iff_of_iSup_eq_top (P := P)
    (fun i ↦ ⟨_, isAffineOpen_opensRange _⟩) 𝒰.iSup_opensRange]
  exact forall_congr' fun i ↦ Q.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)

theorem iff_of_isAffine [IsAffine Y] : P f ↔ Q f := by
  letI := isLocal_affineProperty P
  haveI : ∀ i, IsAffine (Scheme.OpenCover.obj (Scheme.openCoverOfIsIso (𝟙 Y)) i) := fun i => by
    dsimp; infer_instance
  rw [iff_of_openCover (P := P) (Scheme.openCoverOfIsIso.{0} (𝟙 Y))]
  trans Q (pullback.snd f (𝟙 _))
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id (pullback.snd _ _), ← pullback.condition,
    Q.cancel_left_of_respectsIso]
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_target_iff AlgebraicGeometry.HasAffineProperty.iff_of_isAffine

instance (priority := 900) : IsLocalAtTarget P := by
  letI := isLocal_affineProperty P
  apply IsLocalAtTarget.mk'
  · rw [eq_targetAffineLocally P]
    intro X Y f U H V
    rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict f _ _)]
    exact H ⟨_, V.2.image_of_isOpenImmersion (Y.ofRestrict _)⟩
  · rintro X Y f ι U hU H
    let 𝒰 := Y.openCoverOfSuprEqTop U hU
    apply of_openCover 𝒰.affineRefinement.openCover
    rintro ⟨i, j⟩
    have : P (𝒰.pullbackHom f i) := by
      refine (P.arrow_mk_iso_iff
        (morphismRestrictEq _ ?_ ≪≫ morphismRestrictOpensRange f (𝒰.map i))).mp (H i)
      exact (opensRange_ιOpens _).symm
    rw [← Q.cancel_left_of_respectsIso (𝒰.pullbackCoverAffineRefinementObjIso f _).inv,
      𝒰.pullbackCoverAffineRefinementObjIso_inv_pullbackHom]
    exact of_isPullback (.of_hasPullback _ _) this
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_is_local AlgebraicGeometry.HasAffineProperty.instIsLocalAtTarget

open AffineTargetMorphismProperty in
protected theorem iff :
    HasAffineProperty P Q ↔ IsLocalAtTarget P ∧ Q = of P :=
  ⟨fun _ ↦ ⟨inferInstance, ext fun _ _ _ ↦ iff_of_isAffine.symm⟩,
    fun ⟨_, e⟩ ↦ e ▸ of_isLocalAtTarget P⟩

private theorem pullback_fst_of_right (hP' : Q.StableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : Q g) :
    P (pullback.fst f g) := by
  letI := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) X.affineCover]
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.map i)
  have : e.hom ≫ pullback.fst _ _ = X.affineCover.pullbackHom (pullback.fst _ _) i := by
    simp [e, Scheme.OpenCover.pullbackHom]
  rw [← this, Q.cancel_left_of_respectsIso]
  apply hP' (.of_hasPullback _ _)
  exact H

theorem stableUnderBaseChange (hP' : Q.StableUnderBaseChange) :
    P.StableUnderBaseChange :=
  MorphismProperty.StableUnderBaseChange.mk
    (fun X Y S f g H => by
      rw [IsLocalAtTarget.iff_of_openCover (P := P) (S.affineCover.pullbackCover f)]
      intro i
      let e : pullback (pullback.fst f g) ((S.affineCover.pullbackCover f).map i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g _ ≪≫ ?_ ≪≫
          (pullbackRightPullbackFstIso (S.affineCover.map i) g
            (pullback.snd f (S.affineCover.map i))).symm
        exact asIso
          (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst _ _ =
          (S.affineCover.pullbackCover f).pullbackHom (pullback.fst _ _) i := by
        simp [e, Scheme.OpenCover.pullbackHom]
      rw [← this, P.cancel_left_of_respectsIso]
      apply HasAffineProperty.pullback_fst_of_right hP'
      letI := isLocal_affineProperty P
      rw [← pullbackSymmetry_hom_comp_snd, Q.cancel_left_of_respectsIso]
      apply of_isPullback (.of_hasPullback _ _) H)
#align algebraic_geometry.affine_target_morphism_property.is_local.stable_under_base_change AlgebraicGeometry.HasAffineProperty.stableUnderBaseChange

end HasAffineProperty

end targetAffineLocally

end AlgebraicGeometry
