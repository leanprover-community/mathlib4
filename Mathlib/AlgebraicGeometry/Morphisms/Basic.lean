/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import Mathlib.Data.List.TFAE

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `MorphismProperty Scheme` is a predicate on morphisms between schemes. For properties local at
the target, its behaviour is entirely determined by its definition on morphisms into affine schemes,
which we call an `AffineTargetMorphismProperty`. In this file, we provide API lemmas for properties
local at the target, and special support for those properties whose `AffineTargetMorphismProperty`
takes on a simpler form. We also provide API lemmas for properties local at the source.
The main interfaces of the API are the typeclasses `IsZariskiLocalAtTarget`,
`IsZariskiLocalAtSource` and `HasAffineProperty`, which we describe in detail below.

## `IsZariskiLocalAtTarget`

- `AlgebraicGeometry.IsZariskiLocalAtTarget`: We say that `IsZariskiLocalAtTarget P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `f ∣_ U` for an open cover `U` of `Y` if and only if `P` holds for `f`.

For a morphism property `P` local at the target and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtTarget.of_isPullback`:
    `P` is preserved under pullback along open immersions.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`:
    `P f → P (f ∣_ U)` for an open `U` of `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P (f ∣_ U i)` for a family `U` of open sets covering `Y`.
- `AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.pullbackHom f i)` for `𝒰 : Y.OpenCover`.

## `IsZariskiLocalAtSource`

- `AlgebraicGeometry.IsZariskiLocalAtSource`: We say that `IsZariskiLocalAtSource P` for
  `P : MorphismProperty Scheme` if
  1. `P` respects isomorphisms.
  2. `P` holds for `𝒰.f i ≫ f` for an open cover `𝒰` of `X` iff `P` holds for `f : X ⟶ Y`.

For a morphism property `P` local at the source and `f : X ⟶ Y`, we provide these API lemmas:

- `AlgebraicGeometry.IsZariskiLocalAtSource.comp`:
    `P` is preserved under composition with open immersions at the source.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_iSup_eq_top`:
    `P f ↔ ∀ i, P ((U i).ι ≫ f)` for a family `U` of open sets covering `X`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.iff_of_openCover`:
    `P f ↔ ∀ i, P (𝒰.f i ≫ f)` for `𝒰 : X.OpenCover`.
- `AlgebraicGeometry.IsZariskiLocalAtSource.of_isOpenImmersion`: If `P` contains identities then `P`
    holds for open immersions.

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
    `P f ↔ ∀ i, Q (f ∣_ U i)` for a family `U` of affine open sets covering `Y`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_openCover`:
    `P f ↔ ∀ i, Q (𝒰.pullbackHom f i)` for affine open covers `𝒰` of `Y`.
- `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`:
    If `Q` is stable under affine base change, then `P` is stable under arbitrary base change.

## Implementation details

The properties `IsZariskiLocalAtTarget` and `IsZariskiLocalAtSource` are defined as abbreviations
for the respective local property of morphism properties defined generally for categories equipped
with a `Precoverage`.
-/

@[expose] public section


universe u v

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/-- A property is Zariski-local at target if it is local at target in the Zariski topology. -/
abbrev IsZariskiLocalAtTarget (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtTarget Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtTarget

/--
`P` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.
-/
protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Y.Opens), P f → P (f ∣_ U))
    (of_sSup_eq_top :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens), iSup U = ⊤ →
        (∀ i, P (f ∣_ U i)) → P f) :
    IsZariskiLocalAtTarget P where
  pullbackSnd 𝒰 i hf := (P.arrow_mk_iso_iff (morphismRestrictOpensRange _ _)).mp (restrict _ _ hf)
  of_zeroHypercover {X Y f} 𝒰 h := by
    refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange 𝒰) ?_
    exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h i)

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : Y.OpenCover)

lemma of_isPullback {UX UY : Scheme.{u}} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (H : P f) : P f' :=
  MorphismProperty.IsLocalAtTarget.of_isPullback (Y.affineCover.add iY) .none h H

theorem restrict (hf : P f) (U : Y.Opens) : P (f ∣_ U) :=
  of_isPullback (isPullback_morphismRestrict f U).flip hf

lemma of_iSup_eq_top {ι} (U : ι → Y.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, P (f ∣_ U i)) : P f := by
  refine (P.iff_of_zeroHypercover_target
    (Y.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i ↦ ?_
  obtain ⟨_, i, rfl⟩ := i
  refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mp ?_
  change P (f ∣_ (U i).ι.opensRange)
  rw [Scheme.Opens.opensRange_ι]
  exact H i

theorem iff_of_iSup_eq_top {ι} (U : ι → Y.Opens) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict H _, of_iSup_eq_top U hU⟩

lemma of_openCover (H : ∀ i, P (𝒰.pullbackHom f i)) : P f := by
  apply of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  exact fun i ↦ (P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (H i)

theorem iff_of_openCover (𝒰 : Y.OpenCover) :
    P f ↔ ∀ i, P (𝒰.pullbackHom f i) :=
  ⟨fun H _ ↦ of_isPullback (.of_hasPullback _ _) H, of_openCover _⟩

lemma of_range_subset_iSup [P.RespectsRight @IsOpenImmersion] {ι : Type*} (U : ι → Y.Opens)
    (H : Set.range f ⊆ (⨆ i, U i : Y.Opens)) (hf : ∀ i, P (f ∣_ U i)) : P f := by
  let g : X ⟶ (⨆ i, U i : Y.Opens) := IsOpenImmersion.lift (Scheme.Opens.ι _) f (by simpa using H)
  rw [← IsOpenImmersion.lift_fac (⨆ i, U i).ι f (by simpa using H)]
  apply MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance
  rw [iff_of_iSup_eq_top (P := P) (U := fun i : ι ↦ (⨆ i, U i).ι ⁻¹ᵁ U i)]
  · intro i
    have heq : g ⁻¹ᵁ (⨆ i, U i).ι ⁻¹ᵁ U i = f ⁻¹ᵁ U i := by
      change (g ≫ (⨆ i, U i).ι) ⁻¹ᵁ U i = _
      simp [g]
    let e : Arrow.mk (g ∣_ (⨆ i, U i).ι ⁻¹ᵁ U i) ≅ Arrow.mk (f ∣_ U i) :=
        Arrow.isoMk (X.isoOfEq heq) (Scheme.Opens.isoOfLE (le_iSup U i)) <| by
      simp [← CategoryTheory.cancel_mono (U i).ι, g]
    rw [P.arrow_mk_iso_iff e]
    exact hf i
  apply (⨆ i, U i).ι.image_injective
  dsimp
  rw [Scheme.Hom.image_iSup, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  simp [Scheme.Hom.image_preimage_eq_opensRange_inf, le_iSup U]

set_option backward.isDefEq.respectTransparency false in
lemma of_forall_exists_morphismRestrict (H : ∀ x, ∃ U : Y.Opens, x ∈ U ∧ P (f ∣_ U)) : P f := by
  choose U hxU hU using H
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U (top_le_iff.mp fun x _ ↦ ?_) hU
  simpa using ⟨x, hxU x⟩

lemma of_forall_source_exists_preimage
    [P.RespectsRight IsOpenImmersion] [P.HasOfPostcompProperty IsOpenImmersion]
    (f : X ⟶ Y) (hX : ∀ x, ∃ (U : Y.Opens), f x ∈ U ∧ P ((f ⁻¹ᵁ U).ι ≫ f)) :
    P f := by
  choose U h₁ h₂ using hX
  apply IsZariskiLocalAtTarget.of_range_subset_iSup U
  · rintro y ⟨x, rfl⟩
    simp only [Opens.coe_iSup, Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨x, h₁ x⟩
  · intro x
    exact P.of_postcomp (f ∣_ U x) (U x).ι (inferInstance : IsOpenImmersion _) (by simp [h₂])

set_option backward.isDefEq.respectTransparency false in
lemma coprodMap {X Y X' Y' : Scheme.{u}} (f : X ⟶ X') (g : Y ⟶ Y') (hf : P f) (hg : P g) :
    P (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{_, 0} _ _) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inl_inl_coprodMap f g).flip.isoPullback.hom]
    convert hf
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]
  · rw [← MorphismProperty.cancel_left_of_respectsIso P
      (isPullback_inr_inr_coprodMap f g).flip.isoPullback.hom]
    convert hg
    simp [Scheme.Cover.pullbackHom, coprodOpenCover]

end IsZariskiLocalAtTarget

/-- A property is Zariski-local at source if it is local at source in the Zariski topology. -/
abbrev IsZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) :=
  P.IsLocalAtSource Scheme.zariskiPrecoverage

namespace IsZariskiLocalAtSource

/--
`P` is local at the source if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `U.ι ≫ f` for any `U`.
3. If `P` holds for `U.ι ≫ f` for an open cover `U` of `X`, then `P` holds for `f`.
-/
protected lemma mk' {P : MorphismProperty Scheme} [P.RespectsIso]
    (restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens), P f → P (U.ι ≫ f))
    (of_sSup_eq_top :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → X.Opens), iSup U = ⊤ →
        (∀ i, P ((U i).ι ≫ f)) → P f) :
    IsZariskiLocalAtSource P where
  comp 𝒰 i H := by
    rw [← IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact restrict _ _ H
  of_zeroHypercover {X Y} f 𝒰 h := by
    refine of_sSup_eq_top f _ (Scheme.OpenCover.iSup_opensRange 𝒰) fun i ↦ ?_
    rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
      (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
      P.cancel_left_of_respectsIso]
    exact h _

variable {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} (𝒰 : X.OpenCover)

lemma comp {UX : Scheme.{u}} (H : P f) (i : UX ⟶ X) [IsOpenImmersion i] :
    P (i ≫ f) :=
  (P.iff_of_zeroHypercover_source (X.affineCover.add i)).mp H .none

/-- If `P` is local at the source, then it respects composition on the left with open immersions. -/
instance respectsLeft_isOpenImmersion {P : MorphismProperty Scheme}
    [IsZariskiLocalAtSource P] : P.RespectsLeft @IsOpenImmersion where
  precomp i _ _ hf := IsZariskiLocalAtSource.comp hf i

lemma of_iSup_eq_top {ι} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (H : ∀ i, P ((U i).ι ≫ f)) : P f := by
  refine (P.iff_of_zeroHypercover_source
    (X.openCoverOfIsOpenCover (s := Set.range U) Subtype.val (by ext; simp [← hU]))).mpr fun i ↦ ?_
  obtain ⟨_, i, rfl⟩ := i
  exact H i

theorem iff_of_iSup_eq_top {ι} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    P f ↔ ∀ i, P ((U i).ι ≫ f) :=
  ⟨fun H _ ↦ comp H _, of_iSup_eq_top U hU⟩

lemma of_openCover (H : ∀ i, P (𝒰.f i ≫ f)) : P f := by
  refine of_iSup_eq_top (fun i ↦ (𝒰.f i).opensRange) 𝒰.iSup_opensRange fun i ↦ ?_
  rw [← IsOpenImmersion.isoOfRangeEq_inv_fac (𝒰.f i) (Scheme.Opens.ι _)
    (congr_arg Opens.carrier (𝒰.f i).opensRange.opensRange_ι.symm), Category.assoc,
    P.cancel_left_of_respectsIso]
  exact H i

theorem iff_of_openCover :
    P f ↔ ∀ i, P (𝒰.f i ≫ f) :=
  ⟨fun H _ ↦ comp H _, of_openCover _⟩

variable (f) in
lemma of_isOpenImmersion [P.ContainsIdentities] [IsOpenImmersion f] : P f :=
  Category.comp_id f ▸ comp (P.id_mem Y) f

lemma isZariskiLocalAtTarget [P.IsMultiplicative]
    (hP : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion g], P (f ≫ g) → P f) :
    IsZariskiLocalAtTarget P where
  pullbackSnd {X Y} f 𝒰 i hf := by
    apply hP _ (𝒰.f i)
    rw [← pullback.condition]
    exact IsZariskiLocalAtSource.comp hf _
  of_zeroHypercover {X Y} f 𝒰 h := by
    rw [P.iff_of_zeroHypercover_source (𝒰.pullback₁ f)]
    intro i
    rw [← Scheme.Cover.pullbackHom_map]
    exact P.comp_mem _ _ (h i) (of_isOpenImmersion _)

set_option backward.isDefEq.respectTransparency false in
lemma sigmaDesc {X : Scheme.{u}} {ι : Type v} [Small.{u} ι] {Y : ι → Scheme.{u}}
    {f : ∀ i, Y i ⟶ X} (hf : ∀ i, P (f i)) : P (Sigma.desc f) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (Scheme.IsLocallyDirected.openCover _)]
  exact fun i ↦ by simp [hf]

section IsZariskiLocalAtSourceAndTarget

/-- If `P` is local at the source and the target, then restriction on both source and target
preserves `P`. -/
lemma resLE [IsZariskiLocalAtTarget P] {U : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U)
    (hf : P f) : P (f.resLE U V e) :=
  IsZariskiLocalAtSource.comp (IsZariskiLocalAtTarget.restrict hf U) _

set_option backward.isDefEq.respectTransparency false in
/-- If `P` is local at the source, local at the target and is stable under post-composition with
open immersions, then `P` can be checked locally around points. -/
lemma iff_exists_resLE [IsZariskiLocalAtTarget P]
    [P.RespectsRight @IsOpenImmersion] :
    P f ↔ ∀ x : X, ∃ (U : Y.Opens) (V : X.Opens) (_ : x ∈ V.1) (e : V ≤ f ⁻¹ᵁ U),
      P (f.resLE U V e) := by
  refine ⟨fun hf x ↦ ⟨⊤, ⊤, trivial, by simp, resLE _ hf⟩, fun hf ↦ ?_⟩
  choose U V hxU e hf using hf
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (fun x : X ↦ V x) (P := P)]
  · intro x
    rw [← Scheme.Hom.resLE_comp_ι _ (e x)]
    exact MorphismProperty.RespectsRight.postcomp (Q := @IsOpenImmersion) _ inferInstance _ (hf x)
  · rw [eq_top_iff]
    rintro x -
    simp only [Opens.mem_iSup]
    use x, hxU x

end IsZariskiLocalAtSourceAndTarget

end IsZariskiLocalAtSource

/-- An `AffineTargetMorphismProperty` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def AffineTargetMorphismProperty :=
  ∀ ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop

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

theorem toProperty_apply (P : AffineTargetMorphismProperty)
    {X Y : Scheme} (f : X ⟶ Y) [i : IsAffine Y] : P.toProperty f ↔ P f := by
  delta AffineTargetMorphismProperty.toProperty; simp [*]

theorem cancel_left_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.cancel_left_of_respectsIso]

theorem cancel_right_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]

set_option backward.isDefEq.respectTransparency false in
theorem arrow_mk_iso_iff
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk f') {h : IsAffine Y} :
    letI : IsAffine Y' := .of_isIso (Y := Y) e.inv.right
    P f ↔ P f' := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.arrow_mk_iso_iff e]

theorem respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f → P (e.hom ≫ f))
    (h₂ : ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [IsAffine Y],
      P f → @P _ _ (f ≫ e.hom) (.of_isIso e.inv)) :
    P.toProperty.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨.of_isIso e.inv, h₂ e f h⟩

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
  /-- `P` is stable under restriction to a basic open set of global sections. -/
  to_basicOpen :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)), P f → P (f ∣_ Y.basicOpen r)
  /-- `P` for `f` if `P` holds for `f` restricted to basic sets of a spanning set of the global
  sections -/
  of_basicOpenCover :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤))
      (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤), (∀ r : s, P (f ∣_ Y.basicOpen r.1)) → P f

attribute [instance] AffineTargetMorphismProperty.IsLocal.respectsIso

open AffineTargetMorphismProperty in
instance (P : MorphismProperty Scheme) [IsZariskiLocalAtTarget P] :
    (of P).IsLocal where
  respectsIso := inferInstance
  to_basicOpen _ _ H := IsZariskiLocalAtTarget.restrict H _
  of_basicOpenCover {_ Y} _ _ _ hs := IsZariskiLocalAtTarget.of_iSup_eq_top _
    ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)

/-- A `P : AffineTargetMorphismProperty` is stable under base change if `P` holds for `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes. -/
def IsStableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  ∀ ⦃Z X Y S : Scheme⦄ [IsAffine S] [IsAffine X] {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Z ⟶ Y} {g' : Z ⟶ X}, IsPullback g' f' f g → P g → P g'

lemma IsStableUnderBaseChange.mk (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    (H : ∀ ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
      P g → P (pullback.fst f g)) : P.IsStableUnderBaseChange := by
  intro Z X Y S _ _ f g f' g' h hg
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_fst]
  exact H f g hg

end AffineTargetMorphismProperty

section targetAffineLocally

/-- For a `P : AffineTargetMorphismProperty`, `targetAffineLocally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => ∀ U : Y.affineOpens, P (f ∣_ U)

theorem of_targetAffineLocally_of_isPullback
    {P : AffineTargetMorphismProperty} [P.IsLocal]
    {X Y UX UY : Scheme.{u}} [IsAffine UY] {f : X ⟶ Y} {iY : UY ⟶ Y} [IsOpenImmersion iY]
    {iX : UX ⟶ X} {f' : UX ⟶ UY} (h : IsPullback iX f' f iY) (hf : targetAffineLocally P f) :
    P f' := by
  rw [← P.cancel_left_of_respectsIso h.isoPullback.inv, h.isoPullback_inv_snd]
  exact (P.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)).mp (hf ⟨_, isAffineOpen_opensRange iY⟩)

set_option backward.isDefEq.respectTransparency false in
instance (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso] :
    (targetAffineLocally P).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · introv H U
    rw [morphismRestrict_comp, P.cancel_left_of_respectsIso]
    exact H U
  · introv H
    rintro ⟨U, hU : IsAffineOpen U⟩; dsimp
    haveI : IsAffine _ := hU.preimage_of_isIso e.hom
    rw [morphismRestrict_comp, P.cancel_right_of_respectsIso]
    exact H ⟨(Opens.map e.hom.base).obj U, hU.preimage_of_isIso e.hom⟩

/--
`HasAffineProperty P Q` is a type class asserting that `P` is local at the target, and over affine
schemes, it is equivalent to `Q : AffineTargetMorphismProperty`.
To make the proofs easier, we state it instead as
1. `Q` is local at the target
2. `P f` if and only if `∀ U, Q (f ∣_ U)` ranging over all affine opens of the target of `f`.
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
lemma of_isZariskiLocalAtTarget (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] :
    HasAffineProperty P (AffineTargetMorphismProperty.of P) where
  isLocal_affineProperty := inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    constructor
    · intro hf ⟨U, hU⟩
      exact IsZariskiLocalAtTarget.restrict hf _
    · intro hf
      exact P.of_zeroHypercover_target Y.affineCover
        fun i ↦ of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) hf

@[deprecated (since := "2025-10-07")] alias of_isLocalAtTarget := of_isZariskiLocalAtTarget

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

theorem of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Y.Opens) = ⊤)
    (hU' : ∀ i, Q (f ∣_ U i)) :
    P f := by
  letI := isLocal_affineProperty P
  rw [eq_targetAffineLocally P]
  classical
  intro V
  induction V using of_affine_open_cover U hU with
  | basicOpen U r h =>
    have := AffineTargetMorphismProperty.IsLocal.to_basicOpen (f ∣_ U.1) (U.1.topIso.inv r) h
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r)).mp this
  | openCover U s hs H =>
    apply AffineTargetMorphismProperty.IsLocal.of_basicOpenCover _
      (s.image (Scheme.Opens.topIso _).inv) (by simp [← Ideal.map_span, hs, Ideal.map_top])
    intro ⟨r, hr⟩
    obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hr
    exact (Q.arrow_mk_iso_iff
      (morphismRestrictRestrictBasicOpen f _ r).symm).mp (H ⟨r, hr'⟩)
  | hU i => exact hU' i

theorem iff_of_iSup_eq_top
    {ι} (U : ι → Y.affineOpens) (hU : ⨆ i, (U i : Y.Opens) = ⊤) :
    P f ↔ ∀ i, Q (f ∣_ U i) :=
  ⟨fun H _ ↦ restrict H _, fun H ↦ HasAffineProperty.of_iSup_eq_top U hU H⟩

theorem of_openCover
    (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.X i)] (h𝒰 : ∀ i, Q (𝒰.pullbackHom f i)) :
    P f :=
  letI := isLocal_affineProperty P
  of_iSup_eq_top
    (fun i ↦ ⟨_, isAffineOpen_opensRange (𝒰.f i)⟩) 𝒰.iSup_opensRange
    (fun i ↦ (Q.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr (h𝒰 i))

theorem iff_of_openCover (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.X i)] :
    P f ↔ ∀ i, Q (𝒰.pullbackHom f i) := by
  letI := isLocal_affineProperty P
  rw [iff_of_iSup_eq_top (P := P)
    (fun i ↦ ⟨_, isAffineOpen_opensRange _⟩) 𝒰.iSup_opensRange]
  exact forall_congr' fun i ↦ Q.arrow_mk_iso_iff
    (morphismRestrictOpensRange f _)

theorem iff_of_isAffine [IsAffine Y] : P f ↔ Q f := by
  letI := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) (Scheme.coverOfIsIso.{0} (𝟙 Y))]
  trans Q (pullback.snd f (𝟙 _))
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id (pullback.snd _ _), ← pullback.condition,
    Q.cancel_left_of_respectsIso]

set_option backward.isDefEq.respectTransparency false in
instance (priority := 900) : IsZariskiLocalAtTarget P := by
  letI := isLocal_affineProperty P
  apply IsZariskiLocalAtTarget.mk'
  · rw [eq_targetAffineLocally P]
    intro X Y f U H V
    rw [Q.arrow_mk_iso_iff (morphismRestrictRestrict f _ _)]
    exact H ⟨_, V.2.image_of_isOpenImmersion (Y.ofRestrict _)⟩
  · rintro X Y f ι U hU H
    let 𝒰 := Y.openCoverOfIsOpenCover U hU
    apply of_openCover 𝒰.affineRefinement.openCover
    rintro ⟨i, j⟩
    have : P (𝒰.pullbackHom f i) := by
      refine (P.arrow_mk_iso_iff
        (morphismRestrictEq _ ?_ ≪≫ morphismRestrictOpensRange f (𝒰.f i))).mp (H i)
      exact (Scheme.Opens.opensRange_ι _).symm
    rw [← Q.cancel_left_of_respectsIso (𝒰.pullbackCoverAffineRefinementObjIso f _).inv,
      𝒰.pullbackCoverAffineRefinementObjIso_inv_pullbackHom]
    exact of_isPullback (.of_hasPullback _ _) this

open AffineTargetMorphismProperty in
protected theorem iff {P : MorphismProperty Scheme} {Q : AffineTargetMorphismProperty} :
    HasAffineProperty P Q ↔ IsZariskiLocalAtTarget P ∧ Q = of P :=
  ⟨fun _ ↦ ⟨inferInstance, ext fun _ _ _ ↦ iff_of_isAffine.symm⟩,
    fun ⟨_, e⟩ ↦ e ▸ of_isZariskiLocalAtTarget P⟩

set_option backward.isDefEq.respectTransparency false in
private theorem pullback_fst_of_right (hP' : Q.IsStableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : Q g) :
    P (pullback.fst f g) := by
  letI := isLocal_affineProperty P
  rw [iff_of_openCover (P := P) X.affineCover]
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.f i)
  have : e.hom ≫ pullback.fst _ _ = X.affineCover.pullbackHom (pullback.fst _ _) i := by
    simp [e, Scheme.Cover.pullbackHom]
  rw [← this, Q.cancel_left_of_respectsIso]
  apply hP' (.of_hasPullback _ _)
  exact H

set_option backward.isDefEq.respectTransparency false in
theorem isStableUnderBaseChange (hP' : Q.IsStableUnderBaseChange) :
    P.IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.mk'
    (fun X Y S f g _ H => by
      rw [P.iff_of_zeroHypercover_target (S.affineCover.pullback₁ f)]
      intro i
      let e : pullback (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g _ ≪≫ ?_ ≪≫
          (pullbackRightPullbackFstIso (S.affineCover.f i) g
            (pullback.snd f (S.affineCover.f i))).symm
        exact asIso
          (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst _ _ =
          pullback.snd (pullback.fst f g) ((S.affineCover.pullback₁ f).f i) := by
        simp [e]
      rw [← this, P.cancel_left_of_respectsIso]
      apply HasAffineProperty.pullback_fst_of_right hP'
      letI := isLocal_affineProperty P
      rw [← pullbackSymmetry_hom_comp_snd, Q.cancel_left_of_respectsIso]
      apply of_isPullback (.of_hasPullback _ _) H)

lemma isZariskiLocalAtSource
    (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (𝒰 : Scheme.OpenCover.{u} X),
        Q f ↔ ∀ i, Q (𝒰.f i ≫ f)) : IsZariskiLocalAtSource P := by
  refine .mk_of_iff ?_
  intro X Y f 𝒰
  simp_rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top _ (iSup_affineOpens_eq_top Y)]
  rw [forall_comm]
  refine forall_congr' fun U ↦ ?_
  simp_rw [HasAffineProperty.iff_of_isAffine, morphismRestrict_comp]
  exact @H _ _ (f ∣_ U.1) U.2 (Scheme.OpenCover.restrict 𝒰 (f ⁻¹ᵁ U.1))

end HasAffineProperty

end targetAffineLocally

open MorphismProperty

set_option backward.isDefEq.respectTransparency false in
lemma hasOfPostcompProperty_isOpenImmersion_of_morphismRestrict (P : MorphismProperty Scheme)
    [P.RespectsIso] (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens), P f → P (f ∣_ U)) :
    P.HasOfPostcompProperty @IsOpenImmersion where
  of_postcomp {X Y Z} f g hg hfg := by
    have : (f ≫ g) ⁻¹ᵁ g.opensRange = ⊤ := by simp
    have : f = X.topIso.inv ≫ (X.isoOfEq this).inv ≫ (f ≫ g) ∣_ g.opensRange ≫
        (IsOpenImmersion.isoOfRangeEq g.opensRange.ι g (by simp)).hom := by
      simp [← cancel_mono g]
    simp_rw [this, cancel_left_of_respectsIso (P := P), cancel_right_of_respectsIso (P := P)]
    exact H _ _ hfg

instance (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange] :
    P.HasOfPostcompProperty @IsOpenImmersion :=
  HasOfPostcompProperty.of_le P (.monomorphisms Scheme) (fun _ _ f _ ↦ inferInstanceAs (Mono f))

section Deprecations

@[deprecated (since := "2025-10-07")] alias IsLocalAtTarget := IsZariskiLocalAtTarget

namespace IsLocalAtTarget

@[deprecated (since := "2025-10-07")]
alias mk' := IsZariskiLocalAtTarget.mk'

@[deprecated (since := "2025-10-07")]
alias of_iSup_eq_top := IsZariskiLocalAtTarget.of_iSup_eq_top

@[deprecated (since := "2025-10-07")]
alias iff_of_iSup_eq_top := IsZariskiLocalAtTarget.iff_of_iSup_eq_top

@[deprecated (since := "2025-10-07")]
alias of_openCover := IsZariskiLocalAtTarget.of_openCover

@[deprecated (since := "2025-10-07")]
alias iff_of_openCover := IsZariskiLocalAtTarget.iff_of_openCover

@[deprecated (since := "2025-10-07")]
alias of_isPullback := IsZariskiLocalAtTarget.of_isPullback

@[deprecated (since := "2025-10-07")]
alias restrict := IsZariskiLocalAtTarget.restrict

@[deprecated (since := "2025-10-07")]
alias of_range_subset_iSup := IsZariskiLocalAtTarget.of_range_subset_iSup

end IsLocalAtTarget

@[deprecated (since := "2025-10-07")] alias IsLocalAtSource := IsZariskiLocalAtSource

namespace IsLocalAtSource

@[deprecated (since := "2025-10-07")]
alias mk' := IsZariskiLocalAtSource.mk'

@[deprecated (since := "2025-10-07")]
alias comp := IsZariskiLocalAtSource.comp

@[deprecated (since := "2025-10-07")]
alias respectsLeft_isOpenImmersion := IsZariskiLocalAtSource.respectsLeft_isOpenImmersion

@[deprecated (since := "2025-10-07")]
alias of_iSup_eq_top := IsZariskiLocalAtSource.of_iSup_eq_top

@[deprecated (since := "2025-10-07")]
alias iff_of_iSup_eq_top := IsZariskiLocalAtSource.iff_of_iSup_eq_top

@[deprecated (since := "2025-10-07")]
alias of_openCover := IsZariskiLocalAtSource.of_openCover

@[deprecated (since := "2025-10-07")]
alias iff_of_openCover := IsZariskiLocalAtSource.iff_of_openCover

@[deprecated (since := "2025-10-07")]
alias of_isOpenImmersion := IsZariskiLocalAtSource.of_isOpenImmersion

@[deprecated (since := "2025-10-07")]
alias isLocalAtTarget := IsZariskiLocalAtSource.isZariskiLocalAtTarget

@[deprecated (since := "2025-10-07")]
alias sigmaDesc := IsZariskiLocalAtSource.sigmaDesc

@[deprecated (since := "2025-10-07")]
alias resLE := IsZariskiLocalAtSource.resLE

@[deprecated (since := "2025-10-07")]
alias iff_exists_resLE := IsZariskiLocalAtSource.iff_exists_resLE

end IsLocalAtSource

end Deprecations

end AlgebraicGeometry
