/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.CategoryTheory.Sites.Preserves

/-!
# The quasi-compact topology of a scheme

The `qc`-pretopology of a scheme wrt. to a morphism property `P` is the pretopology
given by quasi compact covers satisfying `P`.

We show that a presheaf is a sheaf in this topology if and only if it is a sheaf
in the Zariski topology and a sheaf on single object `P`-coverings of affine schemes.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback
    (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S : Presieve X) (T : Sieve X) [S.HasPairwisePullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := HasPairwisePullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F (T.pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X), S f → Presieve.IsSheafFor F (T.pullback f).arrows) :
    Presieve.IsSheafFor F T.arrows := by
  intro t ht
  have ⦃Y : C⦄ (f : Y ⟶ X) (hf : S f) := H f hf (t.pullback f) (ht.pullback f)
  choose s hs huniq using this
  have hr : FamilyOfElements.Compatible s := by
    rw [pullbackCompatible_iff]
    intro Y Z f g hf hg
    haveI := HasPairwisePullbacks.has_pullbacks hf hg
    obtain ⟨R, hR, h⟩ := H' f g hf hg
    refine hR.ext fun W w hw ↦ (h w hw).ext fun U u hu ↦ ?_
    simp only [← FunctorToTypes.map_comp_apply, ← op_comp]
    dsimp only [FamilyOfElements.IsAmalgamation, FamilyOfElements.pullback] at hs
    rw [hs f hf (u ≫ w ≫ pullback.fst f g) (by simpa),
      hs g hg (u ≫ w ≫ pullback.snd f g) (by simpa [← pullback.condition])]
    congr 1
    simp [pullback.condition]
  obtain ⟨t', ht', hunique⟩ := hF s hr
  refine ⟨t', fun Y f hf ↦ (hF' f).ext fun Z g hg ↦ ?_, fun y hy ↦ ?_⟩
  · rw [← FunctorToTypes.map_comp_apply, ← op_comp]
    simp only [Sieve.pullback_apply, Sieve.generate_apply] at hg
    obtain ⟨W, w, u, hu, heq⟩ := hg
    simp only [← heq, op_comp, FunctorToTypes.map_comp_apply, ht' u hu]
    have : t (g ≫ f) (by simp [hf]) = t (w ≫ u) (by simp [heq, hf]) := by
      congr 1
      rw [heq]
    rw [← t.comp_of_compatible _ ht, this]
    apply hs
  · refine hunique _ fun Y f hf ↦ huniq _ _ _ fun Z g hg ↦ ?_
    simp [Presieve.FamilyOfElements.pullback, ← hy _ hg]

lemma Presieve.IsSheafFor.of_isSheafFor_pullback' (F : Cᵒᵖ ⥤ Type*) {X : C}
    (S T : Presieve X) [S.HasPairwisePullbacks]
    (hF : Presieve.IsSheafFor F S)
    (hF' : ∀ {Y : C} (f : Y ⟶ X), Presieve.IsSeparatedFor F ((Sieve.generate S).pullback f).arrows)
    (H' : ∀ {Y Z : C} (f : Y ⟶ X) (g : Z ⟶ X) (hf : S f) (hg : S g),
      haveI := HasPairwisePullbacks.has_pullbacks hf hg
      ∃ (R : Presieve (pullback f g)), Presieve.IsSeparatedFor F R ∧
        ∀ {W : C} (w : W ⟶ pullback f g),
          R w → Presieve.IsSeparatedFor F
            ((Sieve.generate T).pullback (w ≫ pullback.fst f g ≫ f)).arrows)
    (H : ∀ {Y : C} (f : Y ⟶ X),
      S f → Presieve.IsSheafFor F ((Sieve.generate T).pullback f).arrows) :
    Presieve.IsSheafFor F T := by
  rw [isSheafFor_iff_generate]
  apply Presieve.IsSheafFor.of_isSheafFor_pullback F S _ _ hF'
  · assumption
  · assumption
  · assumption

variable {C : Type*} [Category C] {X : C}

/--
If
- `F` contravariantly maps (suitable) coproducts to products,
- (suitable) coproducts exist in `C`, and
- (suitable) coproducts distribute over pullbacks, then:

`F` is a sheaf for the single object covering `{ ∐ᵢ Yᵢ ⟶ X }`
if and only if it is a presieve for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.

Note: The second two conditions are satisfied if `C` is (finitary) extensive.
-/
lemma Presieve.isSheafFor_sigmaDesc_iff {F : Cᵒᵖ ⥤ Type v} {X : C} {ι : Type*} [Small.{v} ι]
    {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) [(ofArrows Y f).HasPairwisePullbacks]
    [HasCoproduct Y] [HasCoproduct fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)]
    [HasPullback (Limits.Sigma.desc f) (Limits.Sigma.desc f)]
    [PreservesLimit (Discrete.functor <| fun i ↦ op (Y i)) F]
    [PreservesLimit (Discrete.functor fun (ij : ι × ι) ↦ op (pullback (f ij.1) (f ij.2))) F]
    [IsIso (Limits.Sigma.desc fun (ij : ι × ι) ↦ Limits.pullback.map (f ij.fst) (f ij.snd)
      (Limits.Sigma.desc f) (Limits.Sigma.desc f) (Limits.Sigma.ι _ _) (Limits.Sigma.ι _ _) (𝟙 X)
      (by simp) (by simp))] :
    Presieve.IsSheafFor F (.singleton <| Limits.Sigma.desc f) ↔
      Presieve.IsSheafFor F (.ofArrows Y f) := by
  let e : (∐ fun (ij : ι × ι) ↦ pullback (f ij.1) (f ij.2)) ⟶
      pullback (Limits.Sigma.desc f) (Limits.Sigma.desc f) :=
    Limits.Sigma.desc fun ij ↦
    pullback.map _ _ _ _ (Limits.Sigma.ι _ _) (Limits.Sigma.ι _ _) (𝟙 X) (by simp) (by simp)
  rw [Equalizer.Presieve.isSheafFor_singleton_iff (pullback.cone _ _) (pullback.isLimit _ _),
    Equalizer.Presieve.Arrows.sheaf_condition]
  refine (Fork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).nonempty_congr
  · exact F.mapIso (opCoproductIsoProduct Y) ≪≫ PreservesProduct.iso F _
  · exact F.mapIso (.op <| asIso e) ≪≫ F.mapIso (opCoproductIsoProduct _) ≪≫
      PreservesProduct.iso F _
  · exact Iso.refl _
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.fst_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.firstMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_fst, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun ij ↦ ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom, Category.assoc,
      limit.cone_x, PullbackCone.snd_limit_cone, Iso.op_hom, asIso_hom, e, piComparison_comp_π,
      Equalizer.Presieve.Arrows.secondMap]
    rw [← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← F.map_comp, ← op_comp, Sigma.ι_desc,
      ← F.map_comp, ← op_comp, pullback.lift_snd, Pi.lift_π, piComparison_comp_π_assoc,
      ← F.map_comp, ← F.map_comp]
    simp
  · refine Pi.hom_ext _ _ fun i ↦ ?_
    simp only [Fork.ofι_pt, Fork.ι_ofι, Iso.trans_hom, Functor.mapIso_hom, PreservesProduct.iso_hom,
      Category.assoc, piComparison_comp_π]
    rw [← F.map_comp, ← F.map_comp, opCoproductIsoProduct_hom_comp_π, ← op_comp, Sigma.ι_desc]
    simp [Equalizer.Presieve.Arrows.forkMap]

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {P : MorphismProperty Scheme.{u}}

attribute [grind .] Scheme.Hom.surjective

-- This holds more generally if `𝒰.J` is `u`-small, but we don't need that for now.
lemma Scheme.Cover.isSheafFor_sigma_iff {F : Scheme.{u}ᵒᵖ ⥤ Type w} [IsZariskiLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [Finite 𝒰.I₀] :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.X 𝒰.sigma.f) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.X 𝒰.f) := by
  have : PreservesLimitsOfShape (Discrete (𝒰.I₀ × 𝒰.I₀)) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  have : PreservesLimitsOfShape (Discrete 𝒰.I₀) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  conv_rhs => rw [← Presieve.isSheafFor_sigmaDesc_iff]
  congr!
  rw [← PreZeroHypercover.presieve₀, 𝒰.presieve₀_sigma]

variable (P : MorphismProperty Scheme.{u})

lemma zariskiTopology_le_propqcTopology [P.IsMultiplicative] [IsZariskiLocalAtSource P] :
    zariskiTopology ≤ propqcTopology P := by
  apply Precoverage.toGrothendieck_mono
  rw [le_inf_iff]
  refine ⟨?_, ?_⟩
  · apply zariskiPrecoverage_le_qcPrecoverage
  · rw [precoverage, precoverage]
    gcongr
    apply MorphismProperty.precoverage_monotone
    intro X Y f hf
    apply IsZariskiLocalAtSource.of_isOpenImmersion

open Opposite

variable {P} [P.IsStableUnderBaseChange]

lemma Scheme.Cover.Hom.isSheafFor {F : Scheme.{u}ᵒᵖ ⥤ Type*} {S : Scheme.{u}}
    {𝒰 𝒱 : S.Cover (precoverage P)}
    (f : 𝒰 ⟶ 𝒱)
    (H₁ : Presieve.IsSheafFor F (.ofArrows _ 𝒰.f))
    (H₂ : ∀ {X : Scheme.{u}} (f : X ⟶ S),
      Presieve.IsSeparatedFor F (.ofArrows (𝒰.pullback₂ f).X (𝒰.pullback₂ f).f)) :
    Presieve.IsSheafFor F (.ofArrows 𝒱.X 𝒱.f) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.X 𝒰.f))
  · change Sieve.generate _ ≤ Sieve.generate _
    rw [Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    rw [← f.w₀]
    exact ⟨_, f.h₀ i, 𝒱.f _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
    rw [← Presieve.ofArrows_pullback]
    apply H₂

instance {S : Scheme.{u}} (𝒰 : S.AffineCover P) (i : 𝒰.I₀) : IsAffine (𝒰.cover.X i) :=
  inferInstanceAs <| IsAffine (Spec _)

instance {S : Scheme.{u}} [IsAffine S] (𝒰 : S.AffineCover P) [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover :=
  haveI : Finite 𝒰.cover.I₀ := ‹_›
  .of_finite

/-- A pre-sheaf is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisifies `P`. -/
@[stacks 022H]
nonrec lemma isSheaf_propqcTopology_iff [P.IsMultiplicative] (F : Scheme.{u}ᵒᵖ ⥤ Type*)
    [IsZariskiLocalAtSource P] :
    Presieve.IsSheaf (propqcTopology P) F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨?_, fun {R S} f hf hs ↦ ?_⟩, fun ⟨hzar, hff⟩ ↦ ?_⟩
  · exact Presieve.isSheaf_of_le _ (zariskiTopology_le_propqcTopology P) hF
  · apply hF.isSheafFor
    rw [← Hom.presieve₀_cover _ hf]
    exact Cover.mem_propqcTopology _
  · rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
    intro T (𝒰 : Scheme.Cover _ _)
    wlog hT : ∃ (R : CommRingCat.{u}), T = Spec R generalizing T
    · let 𝒱 : T.OpenCover := T.affineCover
      have h (j : T.affineCover.I₀) : Presieve.IsSheafFor F
          (.ofArrows (𝒰.pullback₂ (𝒱.f j)).X (𝒰.pullback₂ (𝒱.f j)).f) :=
        this _ ⟨_, rfl⟩
      refine .of_isSheafFor_pullback' F (.ofArrows 𝒱.X 𝒱.f) _ ?_ ?_ ?_ ?_
      · exact hzar.isSheafFor _ _ 𝒱.mem_grothendieckTopology
      · intro Y f
        refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
        rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm,
          ← PreZeroHypercover.presieve₀_pullback₁]
        exact Scheme.Cover.mem_grothendieckTopology (𝒱.pullback₂ f)
      · rintro - - - - ⟨i⟩ ⟨j⟩
        use .ofArrows (pullback (𝒱.f i) (𝒱.f j)).affineCover.X
          (pullback (𝒱.f i) (𝒱.f j)).affineCover.f
        refine ⟨(hzar.isSheafFor _ _ <| Cover.mem_grothendieckTopology _).isSeparatedFor, ?_⟩
        · rintro - - ⟨k⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
          apply Presieve.IsSheafFor.isSeparatedFor
          rw [← Presieve.ofArrows_pullback]
          exact this (𝒰.pullback₂ _) ⟨_, rfl⟩
      · rintro - - ⟨i⟩
        rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
          ← Presieve.isSheafFor_iff_generate]
        exact this (𝒰.pullback₂ (𝒱.f i)) ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hT
    wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
    · obtain ⟨𝒱, f, hfin, ho⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
      have H (V : Scheme.{u}) (f : V ⟶ Spec R) : Presieve.IsSheafFor F
          (.ofArrows (𝒱.cover.pullback₂ f).X (𝒱.cover.pullback₂ f).f) := by
        let 𝒰V := V.affineCover
        refine .of_isSheafFor_pullback' F (.ofArrows 𝒰V.X 𝒰V.f) _ ?_ ?_ ?_ ?_
        · exact hzar.isSheafFor _ _ 𝒰V.mem_grothendieckTopology
        · intro Y f
          refine (hzar.isSheafFor _ _ ?_).isSeparatedFor
          rw [Sieve.generate_sieve, ← Sieve.pullbackArrows_comm,
            ← PreZeroHypercover.presieve₀_pullback₁]
          exact Scheme.Cover.mem_grothendieckTopology (𝒰V.pullback₂ f)
        · rintro - - - - ⟨i⟩ ⟨j⟩
          refine ⟨.ofArrows _ (pullback (𝒰V.f i) (𝒰V.f j)).affineCover.f, ?_, ?_⟩
          · exact hzar.isSheafFor _ _ (Cover.mem_grothendieckTopology _) |>.isSeparatedFor
          · rintro - - ⟨k⟩
            rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
              ← Presieve.isSeparatedFor_iff_generate]
            refine (this _ (.ofQuasiCompactCover ((𝒱.cover.pullback₂ f).pullback₂ _)
                (qc := by dsimp; infer_instance))
              ⟨fun l ↦ ?_, hfin⟩).isSeparatedFor
            exact .of_isIso (pullbackLeftPullbackSndIso (𝒱.f l) f _).hom
        · rintro - - ⟨i⟩
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSheafFor_iff_generate]
          let 𝒰' := (𝒱.cover.pullback₂ f).pullback₂ (𝒰V.f i)
          refine this _ (.ofQuasiCompactCover 𝒰' (qc := by dsimp [𝒰']; infer_instance))
            ⟨fun j ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.f j) f (𝒰V.f i)).hom, hfin⟩
      refine Scheme.Cover.Hom.isSheafFor f ?_ fun f ↦ (H _ f).isSeparatedFor
      exact this _ (.ofQuasiCompactCover 𝒱.cover)
        ⟨fun i ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    obtain ⟨_, _⟩ := h𝒰
    let 𝒰' := 𝒰.forgetQc.sigma
    rw [← Scheme.Cover.forgetQc_toPreZeroHypercover,
      ← Scheme.Cover.isSheafFor_sigma_iff hzar, Presieve.ofArrows_of_unique]
    have : IsAffine (𝒰.forgetQc.sigma.X default) := by dsimp; infer_instance
    let f : Spec _ ⟶ Spec R := (𝒰.forgetQc.sigma.X default).isoSpec.inv ≫ 𝒰.forgetQc.sigma.f default
    obtain ⟨φ, hφ⟩ := Spec.map_surjective f
    rw [Presieve.isSheafFor_singleton_iff_of_iso _ (Spec.map φ)
      (𝒰.forgetQc.sigma.X default).isoSpec (by simp [hφ, f])]
    refine hff _ ?_ ?_
    · simpa only [hφ, f] using IsZariskiLocalAtSource.comp (𝒰.forgetQc.sigma.map_prop _) _
    · simp only [hφ, f, Cover.sigma_I₀, PUnit.default_eq_unit, Cover.sigma_X, Cover.sigma_f, f]
      have : Surjective (Sigma.desc 𝒰.f) := inferInstanceAs <| Surjective (Sigma.desc 𝒰.forgetQc.f)
      infer_instance

end AlgebraicGeometry
