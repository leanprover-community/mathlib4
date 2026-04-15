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

In this file we define the rank `AlgebraicGeometry.Scheme.Hom.finrank` of a finite flat morphism of
schemes `f : X ⟶ Y`. It is locally constant and is characterized by the condition that the rank of
`Spec S ⟶ Spec R` at some prime `p` of `R` is the rank of `S` as an `R`-algebra at `p`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.finrank`: For a morphism `f : X ⟶ Y` of schemes, the function
  `Y → ℕ` sending `y` to the rank of `f_* 𝒪_X` over `𝒪_Y` at `y`. Instead of talking about
  sheaves, we define it by choosing an open neighbourhood of `y`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.isLocallyConstant_finrank`: The rank function of a finite flat
  locally finitely presented morphism is locally constant.
- `AlgebraicGeometry.Scheme.Hom.one_le_finrank_iff_surjective`: The rank function is at least `1`
  everywhere if and only if the morphism is surjective.
- `AlgebraicGeometry.Scheme.Hom.isIso_iff_rank_eq`: A finite flat locally finitely presented
  morphism is an isomorphism if and only if its rank is constant equal to `1`.
-/

public section

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

namespace CategoryTheory

open Limits

-- move me
set_option backward.isDefEq.respectTransparency false in
lemma Limits.isPullback_map_fst_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z U S : C} (f : X ⟶ S) (g : Y ⟶ S) (i : Z ⟶ S) (h : U ⟶ pullback i g) :
    IsPullback
      (pullback.map _ _ f i (pullback.fst f g) (h ≫ pullback.fst i g) g
        pullback.condition.symm (by simp [pullback.condition]))
      (pullback.snd (pullback.snd f g) (h ≫ pullback.snd i g))
      (pullback.snd f i)
      (h ≫ pullback.fst i g) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    exact pullback.lift (pullback.lift (c.fst ≫ pullback.fst _ _) (c.snd ≫ h ≫ pullback.snd _ _)
      (by simp [pullback.condition, c.condition_assoc])) c.snd (by simp)
  · intro c
    apply pullback.hom_ext <;> simp [c.condition]
  · intro c
    simp
  · intro c m hfst hsnd
    apply pullback.hom_ext
    · apply pullback.hom_ext <;> simp [← hfst, ← hsnd, pullback.condition]
    · simpa

end CategoryTheory

namespace AlgebraicGeometry

noncomputable section

variable {X S Y T : Scheme.{u}} (f : X ⟶ S)

/-- The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`, when `S` is affine.
This is used as an auxiliary definition to define `AlgebraicGeometry.finrank`. -/
private def IsAffine.finrank [IsAffine S] (f : X ⟶ S) (s : S) : ℕ :=
  f.appTop.hom.finrank (S.isoSpec.hom s)

private lemma IsAffine.finrank_of_isPullback [IsAffine S] [IsAffine T]
    (f' : Y ⟶ T) (g' : Y ⟶ X) (g : T ⟶ S) (h : IsPullback g' f' f g) [Flat f] [IsFinite f]
    (s : S) (t : T) (hs : g t = s) :
    IsAffine.finrank f' t = IsAffine.finrank f s := by
  subst hs
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsPushout f.appTop g.appTop g'.appTop f'.appTop := isPushout_appTop_of_isPullback h
  dsimp [finrank]
  rw [CommRingCat.finrank_eq_of_isPushout this f.flat_appTop f.finite_appTop (T.isoSpec.hom t),
    ← Scheme.Hom.comp_apply, ← Scheme.isoSpec_hom_naturality]
  rfl

private lemma IsAffine.finrank_snd [IsAffine S] [IsAffine T]
    (g : T ⟶ S) [Flat f] [IsFinite f] (x : T) :
    IsAffine.finrank (pullback.snd f g) x = IsAffine.finrank f (g x) :=
  finrank_of_isPullback f _ _ _ (.of_hasPullback _ _) _ _ rfl

private lemma IsAffine.finrank_comp_left_of_isIso [IsAffine S]
    (f : X ⟶ Y) (g : Y ⟶ S) [IsIso f] [IsFinite g] [Flat g] :
    IsAffine.finrank (f ≫ g) = IsAffine.finrank g := by
  ext z
  apply finrank_of_isPullback g (f ≫ g) f (𝟙 _) _ _ _ rfl
  exact IsPullback.of_horiz_isIso (by simp)

/-- The rank of a morphism `f : X ⟶ S` of schemes at a point `s : S`. When `f` is finite,
flat and locally of finite presentation, this is a locally constant function (see
`AlgebraicGeometry.isLocallyConstant_finrank`). -/
def Scheme.Hom.finrank {X S : Scheme.{u}} (f : X ⟶ S) (s : S) : ℕ :=
  IsAffine.finrank (pullback.snd f (S.affineOpenCover.f <| S.affineOpenCover.idx s))
    (S.affineOpenCover.covers s).choose

set_option backward.isDefEq.respectTransparency false in
private lemma Scheme.Hom.finrank_eq_finrank_snd_of_isAffine (g : T ⟶ S) [IsAffine T] (t : T)
    [Flat f] [IsFinite f] :
    f.finrank (g t) = IsAffine.finrank (pullback.snd f g) t := by
  let i := S.affineOpenCover.f (S.affineOpenCover.idx (g t))
  obtain ⟨y, hyl, hyr⟩ := Scheme.Pullback.exists_preimage_pullback
    (S.affineOpenCover.covers <| g t).choose t (S.affineOpenCover.covers <| g t).choose_spec
  obtain ⟨R, u, hu, z, rfl⟩ := (pullback i g).exists_Spec_apply_eq y
  have : IsFinite (pullback.snd f g) := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsFinite (pullback.snd f (S.affineOpenCover.f (g t))) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  trans IsAffine.finrank (pullback.snd (pullback.snd f g) (u ≫ pullback.snd _ _)) z
  · refine (IsAffine.finrank_of_isPullback _ _ ?_ ?_ ?_ _ _ ?_).symm
    · exact pullback.map _ _ _ _ (pullback.fst f g) (u ≫ pullback.fst _ _) g
        pullback.condition.symm (by simp [← pullback.condition]; rfl)
    · exact u ≫ pullback.fst _ _
    · apply isPullback_map_fst_fst
    · exact hyl
  · simp_rw [← hyr]
    exact IsAffine.finrank_snd (pullback.snd f g) (u ≫ pullback.snd _ _) z

private lemma Scheme.Hom.finrank_eq_of_isAffine [IsAffine S] [Flat f] [IsFinite f] (s : S) :
    f.finrank s = IsAffine.finrank f s := by
  rw [show s = (𝟙 S : S ⟶ S) s from rfl, finrank_eq_finrank_snd_of_isAffine,
    IsAffine.finrank_snd]

@[simp]
lemma Scheme.Hom.finrank_SpecMap_eq_finrank {R S : CommRingCat.{u}} {f : R ⟶ S} (hf₁ : f.hom.Finite)
    (hf₂ : f.hom.Flat) :
    finrank (Spec.map f) = f.hom.finrank := by
  simp only [← IsFinite.SpecMap_iff, ← Flat.SpecMap_iff] at hf₁ hf₂
  have hf₁ : (Spec.map f).appTop.hom.Finite := (Spec.map f).finite_appTop
  have hf₂ : (Spec.map f).appTop.hom.Flat := (Spec.map f).flat_appTop
  ext
  rw [finrank_eq_of_isAffine, IsAffine.finrank]
  have : f = (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop ≫ (Scheme.ΓSpecIso S).hom := by simp
  conv_rhs => rw [this]
  dsimp
  rw [RingHom.finrank_comp_right_of_bijective _ _ (ConcreteCategory.bijective_of_isIso _)]
  · rw [RingHom.finrank_comp_left_of_bijective _ _ (ConcreteCategory.bijective_of_isIso _) hf₁ hf₂]
  · exact .comp (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective) hf₁
  · exact .comp hf₂ (.of_bijective (ConcreteCategory.bijective_of_isIso _))
  · simp [isoSpec_Spec_hom, SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_apply,
      ← Scheme.Hom.comp_apply, toSpecΓ_SpecMap_ΓSpecIso_inv]

lemma Scheme.Hom.rank_SpecMap_algebraMap (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Flat R S] (x : PrimeSpectrum R) :
    finrank (Spec.map (CommRingCat.ofHom <| algebraMap R S)) x = Module.rankAtStalk S x := by
  rw [finrank_SpecMap_eq_finrank]
  · simp
  · simpa [RingHom.finite_algebraMap, ]
  · simpa [RingHom.flat_algebraMap_iff]

variable (f : X ⟶ Y) [Flat f] [IsFinite f] [LocallyOfFinitePresentation f]

@[simp]
lemma Scheme.Hom.finrank_comp_left_of_isIso (f : X ⟶ Y) (g : Y ⟶ S)
    [IsIso f] [Flat g] [IsFinite g] [LocallyOfFinitePresentation g] :
    finrank (f ≫ g) = finrank g := by
  ext z
  let e : pullback (f ≫ g) (S.affineOpenCover.f (S.affineOpenCover.idx z)) ≅
      pullback g (S.affineOpenCover.f (S.affineOpenCover.idx z)) :=
    (pullbackRightPullbackFstIso g (S.affineOpenCover.f (S.affineOpenCover.idx z)) f).symm ≪≫
      asIso (pullback.snd f (pullback.fst g (S.affineOpenCover.f _)))
  have : e.hom ≫ pullback.snd _ _ = pullback.snd _ _ := by simp [e]
  rw [finrank, finrank, ← this, IsAffine.finrank_comp_left_of_isIso]

lemma Scheme.Hom.finrank_pullback_snd {Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (y : Y) :
    finrank (pullback.snd f g) y = finrank f (g y) := by
  obtain ⟨R, i, _, y', rfl⟩ := Y.exists_Spec_apply_eq y
  rw [← Scheme.Hom.comp_apply, finrank_eq_finrank_snd_of_isAffine,
    finrank_eq_finrank_snd_of_isAffine, ← pullbackLeftPullbackSndIso_hom_snd f g i,
    ← finrank_eq_of_isAffine, ← finrank_eq_of_isAffine, finrank_comp_left_of_isIso]

lemma Scheme.Hom.finrank_of_isPullback {P X Y Z : Scheme.{u}} (fst : P ⟶ X) (snd : P ⟶ Y)
    (f : X ⟶ Z) (g : Y ⟶ Z) (h : IsPullback fst snd f g)
    [Flat f] [IsFinite f] [LocallyOfFinitePresentation f] (y : Y) :
    finrank snd y = finrank f (g y) := by
  rw [← h.isoPullback_hom_snd, finrank_comp_left_of_isIso, finrank_pullback_snd]

nonrec lemma Scheme.Hom.one_le_finrank_map (x : X) : 1 ≤ finrank f (f x) := by
  wlog hY : ∃ R, Y = Spec R
  · obtain ⟨R, g, hg, y, hy⟩ := Y.exists_Spec_apply_eq (f x)
    rw [← hy, ← finrank_pullback_snd]
    obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hy.symm
    rw [hzr.symm]
    refine this _ _ ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    have heq : f x = (X.isoSpec.inv ≫ f) (X.isoSpec.hom x) := by simp
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv, heq]
    exact this _ _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  rw [finrank_SpecMap_eq_finrank ‹_› ‹_›]
  algebraize [φ.hom]
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap, Nat.add_one_le_iff,
    PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap]
  use x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A finite flat locally finitely presented morphism is surjective if and only if its rank
function is at least `1` everywhere. -/
nonrec lemma Scheme.Hom.one_le_finrank_iff_surjective : 1 ≤ finrank f ↔ Surjective f := by
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
    simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
    rw [finrank_SpecMap_eq_finrank ‹_› ‹_›] at h
    algebraize [φ.hom]
    exact (PrimeSpectrum.rankAtStalk_pos_iff_mem_range_comap _).mp h
  · intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    exact one_le_finrank_map f x

set_option backward.isDefEq.respectTransparency false in
/-- The rank of a finite flat locally finitely presented morphism is locally constant. -/
nonrec lemma Scheme.Hom.isLocallyConstant_finrank : IsLocallyConstant (finrank f) := by
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    obtain ⟨R, g, _, x, rfl⟩ := Y.exists_Spec_apply_eq y
    simp_rw [IsLocallyConstant.iff_exists_open] at this
    obtain ⟨U, hU, hxU, H⟩ := this (pullback.snd f g) ⟨_, rfl⟩ x
    refine ⟨g ''ᵁ ⟨U, hU⟩, (g ''ᵁ ⟨U, hU⟩).2, ⟨x, hxU, rfl⟩, fun y ↦ ?_⟩
    rintro ⟨y', (hyU : y' ∈ U), (rfl : g y' = y)⟩
    rw [← finrank_pullback_snd _ g, ← finrank_pullback_snd _ g]
    exact H y' hyU
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← finrank_comp_left_of_isIso X.isoSpec.inv]
    exact this _ _ ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [Flat.SpecMap_iff, IsFinite.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  rw [finrank_SpecMap_eq_finrank ‹_› ‹_›]
  algebraize [φ.hom]
  have := Module.FinitePresentation.of_finite_of_finitePresentation
  exact Module.isLocallyConstant_rankAtStalk

set_option backward.isDefEq.respectTransparency false in
/-- The rank of an isomorphism is `1`. -/
lemma Scheme.Hom.finrank_eq_one_of_isIso (f : X ⟶ Y) [IsIso f] : finrank f = 1 := by
  ext y
  obtain ⟨R, g, _, y, rfl⟩ := Y.exists_Spec_apply_eq y
  have : Nontrivial R := y.nontrivial
  rw [← finrank_pullback_snd, ← Category.comp_id (pullback.snd f g), finrank_comp_left_of_isIso,
    ← Spec.map_id, finrank_SpecMap_eq_finrank, CommRingCat.hom_id, Pi.one_apply,
    ← Algebra.algebraMap_self, RingHom.finrank_algebraMap]
  · simp
  · exact RingHom.Finite.id R
  · exact RingHom.Flat.id ↑R

/-- A finite flat locally finitely presented morphism is an isomorphism if and only if
its rank is constant equal to `1`. -/
nonrec lemma Scheme.Hom.isIso_iff_rank_eq : IsIso f ↔ finrank f = 1 := by
  refine ⟨fun h ↦ finrank_eq_one_of_isIso f, fun h ↦ ?_⟩
  wlog hY : ∃ R, Y = Spec R
  · rw [← MorphismProperty.isomorphisms.iff,
      IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms Scheme) Y.affineCover]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    refine this _ ?_ ⟨_, rfl⟩
    ext y
    rw [finrank_pullback_snd, h, Pi.one_apply, Pi.one_apply]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have _ : IsAffine X := isAffine_of_isAffineHom f
    rw [← isIso_comp_left_iff X.isoSpec.inv]
    refine this _ _ ?_ ⟨_, rfl⟩
    rw [finrank_comp_left_of_isIso, h]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  simp only [IsFinite.SpecMap_iff, Flat.SpecMap_iff, LocallyOfFinitePresentation.SpecMap_iff] at *
  algebraize [φ.hom]
  have : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    apply Module.algebraMap_bijective_of_rankAtStalk
    rwa [finrank_SpecMap_eq_finrank ‹_› ‹_›] at h
  infer_instance

end

end AlgebraicGeometry
