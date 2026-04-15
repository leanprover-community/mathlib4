/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Flat.Rank

/-!
# Rank of a finite flat morphism of schemes

In this file we define the rank function `AlgebraicGeometry.finrank` of a morphism of schemes
`f : X ⟶ Y`. It assigns to each point `y : Y` the rank of the fiber of `f` at `y`.

## Main definitions

- `AlgebraicGeometry.finrank`: For a morphism `f : X ⟶ Y` of schemes, the function `Y → ℕ` sending
  `y` to the rank of the fiber of `f` at `y`.

## Main results

- `AlgebraicGeometry.isLocallyConstant_finrank`: The rank function of a finite flat locally
  finitely presented morphism is locally constant.
- `AlgebraicGeometry.one_le_finrank_iff_surjective`: The rank function is at least `1` everywhere
  if and only if the morphism is surjective.
- `AlgebraicGeometry.isIso_iff_rank_eq`: A finite flat locally finitely presented morphism is an
  isomorphism if and only if its rank function is constant equal to `1`.
-/

public section

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

/-! ## Declarations that should be moved

The declarations in this section are not specific to the rank of flat morphisms and should
eventually be moved to more appropriate locations.
-/

/-!
### Category theory

The following should be moved to
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting`.
-/

namespace CategoryTheory

open Limits

set_option backward.isDefEq.respectTransparency false in
lemma Limits.isPullback_map_fst_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S) (h : U ⟶ pullback i g) :
    IsPullback
      (pullback.map (pullback.snd f g) (h ≫ pullback.snd i g) f i
        (pullback.fst f g) (h ≫ pullback.fst i g) g
        pullback.condition.symm (by simp [pullback.condition]))
      (pullback.snd (pullback.snd f g) (h ≫ pullback.snd i g))
      (pullback.snd f i)
      (h ≫ pullback.fst i g) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    exact pullback.lift (pullback.lift (c.fst ≫ pullback.fst _ _) (c.snd ≫ h ≫ pullback.snd _ _)
          (by simp [pullback.condition, c.condition_assoc])) c.snd (by simp)
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    simp
  · intro c m hfst hsnd
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [← hfst]
      · simp [← hsnd, pullback.condition]
    · simpa

end CategoryTheory

/-!
### Affine pullback lemmas

The following should be moved to `Mathlib.AlgebraicGeometry.Morphisms.Affine`.
-/

namespace AlgebraicGeometry

noncomputable section

section

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

lemma IsAffine.of_isPullback [IsAffine X] [IsAffine Y] [IsAffine Z]
    (h : IsPullback fst snd f g) : IsAffine P :=
  .of_isIso h.isoPullback.hom

lemma isPushout_appTop_of_isPullback [IsAffine X] [IsAffine Y] [IsAffine Z]
    (h : IsPullback fst snd f g) :
    IsPushout f.appTop g.appTop fst.appTop snd.appTop := by
  have : IsAffine P := .of_isPullback h
  have : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd) (AffineScheme.ofHom f)
      (AffineScheme.ofHom g) :=
    IsPullback.of_map_of_faithful AffineScheme.forgetToScheme.{u} h
  exact (IsPullback.map AffineScheme.Γ.rightOp this).unop.flip

end

/-!
### Scheme existence lemma

The following should be moved to `Mathlib.AlgebraicGeometry.AffineScheme`.
-/

/-- Every point of a scheme is in the image of some affine open immersion. -/
lemma Scheme.exists_Spec_base_eq {X : Scheme.{u}} (x : X) :
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ X) (_ : IsOpenImmersion f) (y : Spec R),
    f.base y = x :=
  ⟨X.affineOpenCover.X _, X.affineOpenCover.f _, inferInstance, X.affineOpenCover.covers x⟩

/-! ## Rank of a morphism of schemes -/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`, when `S` is affine.
This is used as an auxiliary definition to define `AlgebraicGeometry.finrank`. -/
private def IsAffine.finrank [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  (f.appTop).hom.finrank (S.isoSpec.hom.base s)

private lemma IsAffine.finrank_of_isPullback {Y T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (f' : Y ⟶ T) (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [Flat f] [IsFinite f]
    (s : S) (t : T) (hs : g.base t = s) :
    IsAffine.finrank f' t = IsAffine.finrank f s := by
  subst hs
  dsimp [finrank]
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  convert CommRingCat.finrank_eq_of_isPushout this
    (HasRingHomProperty.appTop (P := @Flat) _ inferInstance)
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite).mp inferInstance).2) (T.isoSpec.hom.base t)
  rw [← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality]
  rfl

private lemma IsAffine.finrank_snd {T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (g : T ⟶ S) [Flat f] [IsFinite f] (x : T) :
    IsAffine.finrank (pullback.snd f g) x = IsAffine.finrank f (g.base x) := by
  dsimp [finrank]
  apply finrank_of_isPullback f
  · apply IsPullback.of_hasPullback
  · rfl

private lemma IsAffine.finrank_comp_left_of_isIso {X Y Z : Scheme.{u}} [IsAffine Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsFinite g] [Flat g] :
    IsAffine.finrank (f ≫ g) = IsAffine.finrank g := by
  ext z
  apply finrank_of_isPullback g (f ≫ g) f (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)

/-- The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`. When `f` is finite,
flat and locally of finite presentation, this is a locally constant function (see
`AlgebraicGeometry.isLocallyConstant_finrank`). -/
def finrank {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : ℕ :=
  IsAffine.finrank (pullback.snd f (S.affineOpenCover.f <| S.affineOpenCover.idx s))
    (S.affineOpenCover.covers s).choose

set_option backward.isDefEq.respectTransparency false in
private lemma finrank_eq_finrank_snd_of_isAffine {T : Scheme.{u}} (g : T ⟶ S) [IsAffine T] (t : T)
    [Flat f] [IsFinite f] :
    finrank f (g.base t) = IsAffine.finrank (pullback.snd f g) t := by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g.base t))
  dsimp only [finrank]
  let Y := pullback i g
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g.base t).choose t
    ((S.affineOpenCover.covers <| g.base t).choose_spec)
  let U := Spec (Y.affineOpenCover.X (Y.affineOpenCover.idx y))
  let z : U := (Y.affineOpenCover.covers y).choose
  have : IsFinite (pullback.snd f g) := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsFinite (pullback.snd f (S.affineOpenCover.f ((ConcreteCategory.hom g.base) t))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  trans IsAffine.finrank
      (pullback.snd (pullback.snd f g) (Y.affineOpenCover.f _ ≫ pullback.snd _ _)) z
  · symm
    refine IsAffine.finrank_of_isPullback _ _ ?_ ?_ ?_ _ _ ?_
    · exact pullback.map _ _ _ _ (pullback.fst f g) (Y.affineOpenCover.f _ ≫ pullback.fst _ _) g
        pullback.condition.symm (by simp [← pullback.condition]; rfl)
    · exact Y.affineOpenCover.f _ ≫ pullback.fst _ _
    · apply isPullback_map_fst_fst
    · rw [← hyl]
      simp only [Scheme.affineOpenCover_X, Spec.toLocallyRingedSpace_obj,
        Scheme.affineOpenCover_f, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
        Scheme.affineOpenCover_f]
      congr
      exact (Y.affineOpenCover.covers y).choose_spec
  · convert IsAffine.finrank_snd (pullback.snd f g) (Y.affineOpenCover.f _ ≫ pullback.snd _ _) z
    simp only [← hyr, Scheme.affineOpenCover_f, Scheme.affineOpenCover_X, TopCat.hom_comp,
      Spec.toLocallyRingedSpace_obj, Scheme.affineOpenCover_f, Scheme.Hom.comp_base,
      ContinuousMap.comp_apply]
    congr
    exact (Y.affineOpenCover.covers y).choose_spec.symm

private lemma finrank_eq_of_isAffine [IsAffine S] [Flat f] [IsFinite f] (s : S) :
    finrank f s = IsAffine.finrank f s := by
  rw [show s = (𝟙 S : S ⟶ S).base s from rfl, finrank_eq_finrank_snd_of_isAffine,
    IsAffine.finrank_snd]

@[simp]
lemma finrank_SpecMap_eq_finrank {R S : CommRingCat.{u}} {f : R ⟶ S} (hf₁ : f.hom.Finite)
    (hf₂ : f.hom.Flat) :
    finrank (Spec.map f) = f.hom.finrank := by
  have : IsFinite (Spec.map f) := by
    rwa [HasAffineProperty.SpecMap_iff_of_affineAnd (hQi := RingHom.finite_respectsIso)
      (P := @IsFinite)]
    infer_instance
  have : Flat (Spec.map f) := by
    rwa [HasRingHomProperty.Spec_iff (P := @Flat)]
  have hf : (Spec.map f).appTop.hom.Finite :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mp ‹_›).2
  have hf2 := HasRingHomProperty.appTop (P := @Flat) _ ‹_›
  ext x
  rw [finrank_eq_of_isAffine]
  dsimp only [IsAffine.finrank]
  have : f = (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom := by simp
  conv_rhs => rw [this]
  rw [← Category.assoc]
  have : Function.Bijective (Scheme.ΓSpecIso S).hom :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom
  rw [← RingHom.finrank_comp_right_of_bijective (Scheme.ΓSpecIso R).inv.hom _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv) hf hf2]
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp,
    RingHom.finrank_comp_left_of_bijective _ _ this (hf.comp _) (.comp _ hf2)]
  · congr
    simp only [Scheme.isoSpec_Spec_hom]
    change (Spec.map _).base _ = _
    rw [← Scheme.Hom.comp_apply, ← Spec.map_comp]
    simp
  · apply (HasAffineProperty.SpecMap_iff_of_affineAnd
      (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp
      inferInstance
  apply (HasRingHomProperty.Spec_iff (P := @Flat)).mp inferInstance

lemma rank_SpecMap_algebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (x : PrimeSpectrum R) :
    finrank (Spec.map (CommRingCat.ofHom <| algebraMap R S)) x =
      Module.rankAtStalk S x := by
  rw [finrank_SpecMap_eq_finrank]
  · simp
  · simpa [RingHom.finite_algebraMap]
  · simpa [RingHom.flat_algebraMap_iff]

/-! ## Properties of the rank function -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f]

@[simp]
lemma finrank_comp_left_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [Flat g]
    [IsFinite g] [LocallyOfFinitePresentation g] : finrank (f ≫ g) = finrank g := by
  ext z
  rw [finrank, finrank]
  let e : pullback (f ≫ g) (Z.affineOpenCover.f (Z.affineOpenCover.idx z)) ≅
      pullback g (Z.affineOpenCover.f (Z.affineOpenCover.idx z)) :=
    (pullbackRightPullbackFstIso g (Z.affineOpenCover.f (Z.affineOpenCover.idx z)) f).symm ≪≫
      asIso (pullback.snd f (pullback.fst g (Z.affineOpenCover.f _)))
  have : e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [e]
  rw [← this, IsAffine.finrank_comp_left_of_isIso]

lemma finrank_pullback_snd {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (y : Y) :
    finrank (pullback.snd f g) y = finrank f (g.base y) := by
  let R := Y.affineOpenCover.X (Y.affineOpenCover.idx y)
  let i : Spec R ⟶ Y := Y.affineOpenCover.f (Y.affineOpenCover.idx y)
  let y' : Spec R := Y.affineOpenCover.covers y |>.choose
  have h1 : i.base y' = y := Y.affineOpenCover.covers y |>.choose_spec
  have h2 : (i ≫ g).base y' = g.base y := by simp [h1]
  rw [← h2, ← h1, finrank_eq_finrank_snd_of_isAffine, finrank_eq_finrank_snd_of_isAffine,
    ← pullbackLeftPullbackSndIso_hom_snd f g i, ← finrank_eq_of_isAffine,
    ← finrank_eq_of_isAffine, finrank_comp_left_of_isIso]

nonrec lemma finrank_of_isPullback {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsPullback fst snd f g)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (y : Y) :
    finrank snd y = finrank f (g.base y) := by
  rw [← h.isoPullback_hom_snd, finrank_comp_left_of_isIso, finrank_pullback_snd]

nonrec lemma one_le_finrank_map [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (x : X) :
    1 ≤ finrank f (f.base x) := by
  wlog hY : ∃ R, Y = Spec R
  · let g : Spec (Y.affineOpenCover.X _) ⟶ Y :=
      Y.affineOpenCover.f (Y.affineOpenCover.idx <| f.base x)
    let y' := Y.affineOpenCover.covers (f.base x) |>.choose
    have heq : g.base y' = f.base x :=
      Y.affineOpenCover.covers (f.base x) |>.choose_spec
    rw [← heq, ← finrank_pullback_snd]
    obtain ⟨z, hzl, hzr⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y' heq.symm
    have heq : y' = (pullback.snd f g).base z := hzr.symm
    rw [heq]
    refine this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    have heq : f.base x = (X.isoSpec.inv ≫ f).base (X.isoSpec.hom.base x) := by simp
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv, heq]
    exact this _ _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have h₁ : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
  have h₂ : φ.hom.Finite := (HasAffineProperty.SpecMap_iff_of_affineAnd
      (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
  rw [finrank_SpecMap_eq_finrank h₂ h₁]
  algebraize [φ.hom]
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]
  change 0 < _
  rw [PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap]
  use x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A finite flat locally finitely presented morphism is surjective if and only if its rank
function is at least `1` everywhere. -/
nonrec lemma one_le_finrank_iff_surjective [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] :
    1 ≤ finrank f ↔ Surjective f := by
  refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
  · wlog hY : ∃ R, Y = Spec R
    · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Surjective) Y.affineCover]
      intro i
      dsimp only [Scheme.Cover.pullbackHom]
      refine this _ (fun y ↦ ?_) ⟨_, rfl⟩
      rw [finrank_pullback_snd]
      exact h _
    obtain ⟨R, rfl⟩ := hY
    wlog hX : ∃ S, X = Spec S
    · have _ : IsAffine X := isAffine_of_isAffineHom f
      rw [← MorphismProperty.cancel_left_of_respectsIso @Surjective X.isoSpec.inv]
      refine this _ _ (fun x ↦ ?_) ⟨_, rfl⟩
      rw [finrank_comp_left_of_isIso]
      exact h x
    obtain ⟨S, rfl⟩ := hX
    obtain ⟨φ, rfl⟩ := Spec.map_surjective f
    constructor
    intro x
    specialize h x
    have h₁ : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
    have h₂ : φ.hom.Finite := (HasAffineProperty.SpecMap_iff_of_affineAnd
      (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
    rw [finrank_SpecMap_eq_finrank h₂ h₁] at h
    algebraize [φ.hom]
    exact (PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap _).mp h
  · intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact one_le_finrank_map f x

set_option backward.isDefEq.respectTransparency false in
/-- The rank function of a finite flat locally finitely presented morphism is locally constant. -/
nonrec lemma isLocallyConstant_finrank : IsLocallyConstant (finrank f) := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨R, g, _, x, rfl⟩ := Y.exists_Spec_base_eq y
    have := this (pullback.snd f g) ⟨_, rfl⟩
    rw [IsLocallyConstant.iff_exists_open] at this
    obtain ⟨U, hU, hxU, H⟩ := this x
    refine ⟨g ''ᵁ ⟨U, hU⟩, (g ''ᵁ ⟨U, hU⟩).2, ⟨x, hxU, rfl⟩, fun y ↦ ?_⟩
    rintro ⟨y, (hyU : y ∈ U), rfl⟩
    have := H y hyU
    rwa [finrank_pullback_snd, finrank_pullback_snd] at this
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv]
    exact this _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have h₁ : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
  have h₂ : φ.hom.Finite := (HasAffineProperty.SpecMap_iff_of_affineAnd
    (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
  rw [finrank_SpecMap_eq_finrank h₂ h₁]
  algebraize [φ.hom]
  have : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mp ‹_›
  have := Module.FinitePresentation.of_finite_of_finitePresentation
  exact Module.isLocallyConstant_rankAtStalk

lemma continuous_finrank : Continuous (finrank f) :=
  (isLocallyConstant_finrank f).continuous

set_option backward.isDefEq.respectTransparency false in
/-- The rank of an isomorphism is `1`. -/
lemma finrank_eq_one_of_isIso [IsIso f] : finrank f = 1 := by
  ext y
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_base_eq y
  have : Nontrivial R := y.nontrivial
  rw [← finrank_pullback_snd, ← Category.comp_id (pullback.snd f g), finrank_comp_left_of_isIso,
    ← Spec.map_id, finrank_SpecMap_eq_finrank, CommRingCat.hom_id, Pi.one_apply,
    ← Algebra.algebraMap_self, RingHom.finrank_algebraMap]
  · simp
  · exact RingHom.Finite.id R
  · exact RingHom.Flat.id ↑R

/-- A finite flat locally finitely presented morphism is an isomorphism if and only if
its rank function is constant equal to `1`. -/
nonrec lemma isIso_iff_rank_eq : IsIso f ↔ finrank f = 1 := by
  refine ⟨fun h ↦ finrank_eq_one_of_isIso f, fun h ↦ ?_⟩
  wlog hY : ∃ R, Y = Spec R
  · change MorphismProperty.isomorphisms _ _
    rw [IsZariskiLocalAtTarget.iff_of_openCover
      (P := MorphismProperty.isomorphisms Scheme) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    ext y
    rw [finrank_pullback_snd, h, Pi.one_apply, Pi.one_apply]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    change MorphismProperty.isomorphisms _ _
    rw [← MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme)
      X.isoSpec.inv]
    refine this _ _ ?_ ⟨_, rfl⟩
    rw [finrank_comp_left_of_isIso, h]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  have h₁ : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp ‹_›
  have h₂ : φ.hom.Finite := (HasAffineProperty.SpecMap_iff_of_affineAnd
    (P := @IsFinite) (Q := RingHom.Finite) inferInstance RingHom.finite_respectsIso _).mp ‹_›
  algebraize [φ.hom]
  have : IsIso φ := by
    apply (ConcreteCategory.isIso_iff_bijective φ).mpr
    apply Module.algebraMap_bijective_of_rankAtStalk
    rwa [finrank_SpecMap_eq_finrank h₂ h₁] at h
  infer_instance

lemma finrank_eq_const_of_preconnectedSpace [PreconnectedSpace Y] (y y' : Y) :
    finrank f y = finrank f y' := by
  apply IsLocallyConstant.apply_eq_of_preconnectedSpace
  rw [IsLocallyConstant.iff_continuous]
  exact continuous_finrank f

end

end AlgebraicGeometry
