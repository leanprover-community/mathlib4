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
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes

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
    zariskiTopology ≤ propQCTopology P := by
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

@[simps!]
noncomputable
def Scheme.affineOneHypercover (X : Scheme.{u}) : zariskiTopology.OneHypercover X :=
  .mk'
    (X.affineCover.refineOneHypercover fun i j ↦
      (pullback (X.affineCover.f i) (X.affineCover.f j)).affineCover.toPreZeroHypercover)
    X.affineCover.mem_grothendieckTopology
    fun i j ↦ by simpa using Cover.mem_grothendieckTopology _

/-- A pre-sheaf is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisifies `P`. -/
@[stacks 022H]
nonrec lemma isSheaf_propqcTopology_iff [P.IsMultiplicative] (F : Scheme.{u}ᵒᵖ ⥤ Type*)
    [IsZariskiLocalAtSource P] :
    Presieve.IsSheaf (propQCTopology P) F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨?_, fun {R S} f hf hs ↦ ?_⟩, fun ⟨hzar, hff⟩ ↦ ?_⟩
  · exact Presieve.isSheaf_of_le _ (zariskiTopology_le_propqcTopology P) hF
  · apply hF.isSheafFor
    rw [← Hom.presieve₀_cover _ hf]
    exact Cover.mem_propQCTopology _
  · rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
    intro T (𝒰 : Scheme.Cover _ _)
    wlog hT : ∃ (R : CommRingCat.{u}), T = Spec R generalizing T
    · let 𝒱 : T.OpenCover := T.affineCover
      refine T.affineOneHypercover.isSheafFor_of_pullback hzar ?_ ?_
      · intro i
        rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
          ← Presieve.isSheafFor_iff_generate]
        exact this (𝒰.pullback₂ (𝒱.f i)) ⟨_, rfl⟩
      · intro i j k
        rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
        apply Presieve.IsSheafFor.isSeparatedFor
        rw [← Presieve.ofArrows_pullback]
        exact this (𝒰.pullback₂ _) ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hT
    wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
    · obtain ⟨𝒱, f, hfin, ho⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
      have H (V : Scheme.{u}) (f : V ⟶ Spec R) : Presieve.IsSheafFor F
          (.ofArrows (𝒱.cover.pullback₂ f).X (𝒱.cover.pullback₂ f).f) := by
        let 𝒰V := V.affineCover
        refine V.affineOneHypercover.isSheafFor_of_pullback hzar ?_ ?_
        · intro i
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSheafFor_iff_generate]
          let 𝒰' := (𝒱.cover.pullback₂ f).pullback₂ (𝒰V.f i)
          refine this _ (.ofQuasiCompactCover 𝒰' (qc := by dsimp [𝒰']; infer_instance))
            ⟨fun j ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.f j) f (𝒰V.f i)).hom, hfin⟩
        · intro i j k
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSeparatedFor_iff_generate]
          refine (this _ (.ofQuasiCompactCover ((𝒱.cover.pullback₂ f).pullback₂ _)
              (qc := by dsimp; infer_instance))
            ⟨fun l ↦ ?_, hfin⟩).isSeparatedFor
          exact .of_isIso (pullbackLeftPullbackSndIso (𝒱.f l) f _).hom
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
