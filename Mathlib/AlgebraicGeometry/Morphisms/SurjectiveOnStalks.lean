/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.PrimeSpectrum.TensorProduct
import Mathlib.Topology.LocalAtTarget

/-!
# Morphisms surjective on stalks

We define the classe of morphisms between schemes that are surjective on stalks.
We show that this class is stable under composition and base change.

We also show that (`AlgebraicGeometry.SurjectiveOnStalks.isEmbedding_pullback`)
if `Y ⟶ S` is surjective on stalks, then for every `X ⟶ S`, `X ×ₛ Y` is a subset of
`X × Y` (cartesian product as topological spaces) with the induced topology.
-/

open CategoryTheory CategoryTheory.Limits Topology

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The class of morphisms `f : X ⟶ Y` between schemes such that
`𝒪_{Y, f x} ⟶ 𝒪_{X, x}` is surjective for all `x : X`. -/
@[mk_iff]
class SurjectiveOnStalks : Prop where
  surj_on_stalks : ∀ x, Function.Surjective (f.stalkMap x)

theorem Scheme.Hom.stalkMap_surjective (f : X.Hom Y) [SurjectiveOnStalks f] (x) :
    Function.Surjective (f.stalkMap x) :=
  SurjectiveOnStalks.surj_on_stalks x

namespace SurjectiveOnStalks

instance (priority := 900) [IsOpenImmersion f] : SurjectiveOnStalks f :=
  ⟨fun _ ↦ (ConcreteCategory.bijective_of_isIso _).2⟩

instance : MorphismProperty.IsMultiplicative @SurjectiveOnStalks where
  id_mem _ := inferInstance
  comp_mem {X Y Z} f g hf hg := by
    refine ⟨fun x ↦ ?_⟩
    rw [Scheme.stalkMap_comp]
    exact (hf.surj_on_stalks x).comp (hg.surj_on_stalks (f.base x))

instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SurjectiveOnStalks f]
    [SurjectiveOnStalks g] : SurjectiveOnStalks (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

lemma eq_stalkwise :
    @SurjectiveOnStalks = stalkwise (Function.Surjective ·) := by
  ext; exact surjectiveOnStalks_iff _

instance : IsLocalAtTarget @SurjectiveOnStalks :=
  eq_stalkwise ▸ stalkwiseIsLocalAtTarget_of_respectsIso RingHom.surjective_respectsIso

instance : IsLocalAtSource @SurjectiveOnStalks :=
  eq_stalkwise ▸ stalkwise_isLocalAtSource_of_respectsIso RingHom.surjective_respectsIso

lemma Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    SurjectiveOnStalks (Spec.map φ) ↔ RingHom.SurjectiveOnStalks φ := by
  rw [eq_stalkwise, stalkwise_Spec_map_iff RingHom.surjective_respectsIso,
    RingHom.SurjectiveOnStalks]

instance : HasRingHomProperty @SurjectiveOnStalks RingHom.SurjectiveOnStalks :=
  eq_stalkwise ▸ .stalkwise RingHom.surjective_respectsIso

variable {f} in
lemma iff_of_isAffine [IsAffine X] [IsAffine Y] :
    SurjectiveOnStalks f ↔ RingHom.SurjectiveOnStalks (f.app ⊤) := by
  rw [← Spec_iff, MorphismProperty.arrow_mk_iso_iff @SurjectiveOnStalks (arrowIsoSpecΓOfIsAffine f)]

theorem of_comp [SurjectiveOnStalks (f ≫ g)] : SurjectiveOnStalks f := by
  refine ⟨fun x ↦ ?_⟩
  have := (f ≫ g).stalkMap_surjective x
  rw [Scheme.stalkMap_comp] at this
  exact Function.Surjective.of_comp this

instance stableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @SurjectiveOnStalks := by
  apply HasRingHomProperty.isStableUnderBaseChange
  apply RingHom.IsStableUnderBaseChange.mk
  · exact (HasRingHomProperty.isLocal_ringHomProperty @SurjectiveOnStalks).respectsIso
  intros R S T _ _ _ _ _ H
  exact H.baseChange

/-- If `Y ⟶ S` is surjective on stalks, then for every `X ⟶ S`, `X ×ₛ Y` is a subset of
`X × Y` (cartesian product as topological spaces) with the induced topology. -/
lemma isEmbedding_pullback {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks g] :
    IsEmbedding (fun x ↦ ((pullback.fst f g).base x, (pullback.snd f g).base x)) := by
  let L := (fun x ↦ ((pullback.fst f g).base x, (pullback.snd f g).base x))
  have H : ∀ R A B (f' : Spec A ⟶ Spec R) (g' : Spec B ⟶ Spec R) (iX : Spec A ⟶ X)
      (iY : Spec B ⟶ Y) (iS : Spec R ⟶ S) (e₁ e₂), IsOpenImmersion iX → IsOpenImmersion iY →
      IsOpenImmersion iS → IsEmbedding (L ∘ (pullback.map f' g' f g iX iY iS e₁ e₂).base) := by
    intro R A B f' g' iX iY iS e₁ e₂ _ _ _
    have H : SurjectiveOnStalks g' :=
      have : SurjectiveOnStalks (g' ≫ iS) := e₂ ▸ inferInstance
      .of_comp _ iS
    obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f' := ⟨_, Spec.map_preimage _⟩
    obtain ⟨ψ, rfl⟩ : ∃ ψ, Spec.map ψ = g' := ⟨_, Spec.map_preimage _⟩
    letI := φ.toAlgebra
    letI := ψ.toAlgebra
    rw [HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks)] at H
    convert ((iX.isOpenEmbedding.prodMap iY.isOpenEmbedding).isEmbedding.comp
      (PrimeSpectrum.isEmbedding_tensorProductTo_of_surjectiveOnStalks R A B H)).comp
      (Scheme.homeoOfIso (pullbackSpecIso R A B)).isEmbedding
    ext1 x
    obtain ⟨x, rfl⟩ := (Scheme.homeoOfIso (pullbackSpecIso R A B).symm).surjective x
    simp only [Scheme.homeoOfIso_apply, Function.comp_apply]
    ext
    · simp only [L, ← Scheme.comp_base_apply, pullback.lift_fst, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.comp_base_apply, pullbackSpecIso_inv_fst_assoc]
      rfl
    · simp only [L, ← Scheme.comp_base_apply, pullback.lift_snd, Iso.symm_hom,
        Iso.inv_hom_id]
      erw [← Scheme.comp_base_apply, pullbackSpecIso_inv_snd_assoc]
      rfl
  let 𝒰 := S.affineOpenCover.openCover
  let 𝒱 (i) := ((𝒰.pullbackCover f).obj i).affineOpenCover.openCover
  let 𝒲 (i) := ((𝒰.pullbackCover g).obj i).affineOpenCover.openCover
  let U (ijk : Σ i, (𝒱 i).J × (𝒲 i).J) : TopologicalSpace.Opens (X.carrier × Y) :=
    ⟨{ P | P.1 ∈ ((𝒱 ijk.1).map ijk.2.1 ≫ (𝒰.pullbackCover f).map ijk.1).opensRange ∧
          P.2 ∈ ((𝒲 ijk.1).map ijk.2.2 ≫ (𝒰.pullbackCover g).map ijk.1).opensRange },
      (continuous_fst.1 _ ((𝒱 ijk.1).map ijk.2.1 ≫
      (𝒰.pullbackCover f).map ijk.1).opensRange.2).inter (continuous_snd.1 _
      ((𝒲 ijk.1).map ijk.2.2 ≫ (𝒰.pullbackCover g).map ijk.1).opensRange.2)⟩
  have : Set.range L ⊆ (iSup U : _) := by
    simp only [Scheme.Cover.pullbackCover_J, Scheme.Cover.pullbackCover_obj, Set.range_subset_iff]
    intro z
    simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup, Sigma.exists, Prod.exists]
    obtain ⟨is, s, hsx⟩ := 𝒰.exists_eq (f.base ((pullback.fst f g).base z))
    have hsy : (𝒰.map is).base s = g.base ((pullback.snd f g).base z) := by
      rwa [← Scheme.comp_base_apply, ← pullback.condition, Scheme.comp_base_apply]
    obtain ⟨x : (𝒰.pullbackCover f).obj is, hx⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsx.symm
    obtain ⟨y : (𝒰.pullbackCover g).obj is, hy⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hsy.symm
    obtain ⟨ix, x, rfl⟩ := (𝒱 is).exists_eq x
    obtain ⟨iy, y, rfl⟩ := (𝒲 is).exists_eq y
    refine ⟨is, ix, iy, ⟨x, hx⟩, ⟨y, hy⟩⟩
  let 𝓤 := (Scheme.Pullback.openCoverOfBase 𝒰 f g).bind
    (fun i ↦ Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒲 i) _ _)
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range _ ?_ U this _ (fun i ↦ (𝓤.map i).base)
    (fun i ↦ (𝓤.map i).continuous) ?_ ?_
  · fun_prop
  · rintro i x ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
    obtain ⟨x₁', hx₁'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₁.symm
    obtain ⟨x₂', hx₂'⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ hx₂.symm
    obtain ⟨z, hz⟩ :=
      Scheme.IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop
        (P := @IsOpenImmersion) inferInstance _ _ (hx₁'.trans hx₂'.symm)
    refine ⟨(pullbackFstFstIso _ _ _ _ _ _ (𝒰.map i.1) ?_ ?_).hom.base z, ?_⟩
    · simp [pullback.condition]
    · simp [pullback.condition]
    · dsimp only
      rw [← hx₁', ← hz, ← Scheme.comp_base_apply]
      erw [← Scheme.comp_base_apply]
      congr 4
      apply pullback.hom_ext <;> simp [𝓤, ← pullback.condition, ← pullback.condition_assoc]
  · intro i
    have := H (S.affineOpenCover.obj i.1) (((𝒰.pullbackCover f).obj i.1).affineOpenCover.obj i.2.1)
        (((𝒰.pullbackCover g).obj i.1).affineOpenCover.obj i.2.2)
        ((𝒱 i.1).map i.2.1 ≫ 𝒰.pullbackHom f i.1)
        ((𝒲 i.1).map i.2.2 ≫ 𝒰.pullbackHom g i.1)
        ((𝒱 i.1).map i.2.1 ≫ (𝒰.pullbackCover f).map i.1)
        ((𝒲 i.1).map i.2.2 ≫ (𝒰.pullbackCover g).map i.1)
        (𝒰.map i.1)
        (by simp +zetaDelta [pullback.condition]) (by simp +zetaDelta [pullback.condition])
        inferInstance inferInstance inferInstance
    convert this using 6
    apply pullback.hom_ext <;>
      simp +zetaDelta [𝓤, ← pullback.condition, ← pullback.condition_assoc,
        Scheme.Cover.pullbackHom]

end SurjectiveOnStalks

end AlgebraicGeometry
