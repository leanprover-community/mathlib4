-- `Mathlib/AlgebraicGeometry/Morphisms/Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-
This is a stub. I(@erdOne) am working towards a better def via #14748 and #14377.
Feel free to tackle these sorries though. They will be useful regardless.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

-- Some of these belongs in `AlgebraicGeometry/Pullbacks`
namespace Scheme.Pullback

variable (𝒰 : Y.OpenCover) (𝒱 : ∀ i, (pullback f (𝒰.map i)).OpenCover)

/-
Given `𝒰 i` covering `Y` and `𝒱 i j` covering `𝒰 i`, this is the open cover
`𝒱 i j₁ ×_{𝒰 i} 𝒱 i j₂` ranging over all `i`, `j₁`, `j₂`.
-/
noncomputable
def diagonalCover : (pullback.diagonalObj f).OpenCover :=
(Scheme.Pullback.openCoverOfBase 𝒰 f f).bind
  (fun i ↦ Scheme.Pullback.openCoverOfLeftRight (𝒱 i) (𝒱 i) (pullback.snd _ _) (pullback.snd _ _))

/-- The image of `𝒱 i j₁ ×_{𝒰 i} 𝒱 i j₂` in `diagonalCover` with `j₁ = j₂`  -/
noncomputable
def diagonalCoverDiagonal : (pullback.diagonalObj f).Opens :=
⨆ i : Σ i, (𝒱 i).J, ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange

lemma diagonalCover_map (I) : (diagonalCover f 𝒰 𝒱).map I =
    pullback.map _ _ _ _
    ((𝒱 I.fst).map _ ≫ pullback.fst _ _) ((𝒱 I.fst).map _ ≫ pullback.fst _ _) (𝒰.map _)
    (by simp only [Category.assoc, pullback.condition])
    (by simp only [Category.assoc, pullback.condition]) := by
  ext1 <;> simp [diagonalCover]

lemma diagonalCoverDiagonal_eq_top_of_injective (hf : Function.Injective f.1.base) :
    diagonalCoverDiagonal f 𝒰 𝒱 = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  simp only [diagonalCoverDiagonal, openCoverOfBase_J, openCoverOfBase_obj, openCoverOfLeftRight_J,
    Opens.iSup_mk, Opens.carrier_eq_coe, Hom.opensRange_coe, Opens.coe_mk, Set.mem_iUnion,
    Set.mem_range, Sigma.exists]
  have H : (pullback.fst f f).base x = (pullback.snd f f).base x :=
    hf (by rw [← Scheme.comp_base_apply, ← Scheme.comp_base_apply, pullback.condition])
  let i := 𝒰.f (f.base ((pullback.fst f f).base x))
  obtain ⟨y : 𝒰.obj i, hy : (𝒰.map i).base y = f.base _⟩ :=
    𝒰.covers (f.base ((pullback.fst f f).base x))
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).f z
  obtain ⟨w : (𝒱 i).obj j, hy : ((𝒱 i).map j).base w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, ?_⟩
  simp_rw [diagonalCover_map]
  show x ∈ Set.range _
  erw [range_map]
  simp only [comp_coeBase, TopCat.coe_comp, Set.mem_inter_iff, Set.mem_preimage, Set.mem_range,
    Function.comp_apply, ← H, and_self, ← hz₁, ← hy]
  exact ⟨w, rfl⟩

lemma range_diagonal_subset_diagonalCoverDiagonal :
    Set.range (pullback.diagonal f).base ⊆ diagonalCoverDiagonal f 𝒰 𝒱 := by
  rintro _ ⟨x, rfl⟩
  simp only [diagonalCoverDiagonal, openCoverOfBase_J, openCoverOfBase_obj, openCoverOfLeftRight_J,
    Opens.iSup_mk, Opens.carrier_eq_coe, Hom.opensRange_coe, Opens.coe_mk, Set.mem_iUnion,
    Set.mem_range, Sigma.exists]
  let i := 𝒰.f (f.base x)
  obtain ⟨y : 𝒰.obj i, hy : (𝒰.map i).base y = f.base x⟩ := 𝒰.covers (f.base x)
  obtain ⟨z, hz₁, hz₂⟩ := exists_preimage_pullback _ _ hy.symm
  let j := (𝒱 i).f z
  obtain ⟨w : (𝒱 i).obj j, hy : ((𝒱 i).map j).base w = z⟩ := (𝒱 i).covers z
  refine ⟨i, j, (pullback.diagonal ((𝒱 i).map j ≫ pullback.snd f (𝒰.map i))).base w, ?_⟩
  rw [← hz₁, ← hy, ← Scheme.comp_base_apply, ← Scheme.comp_base_apply]
  erw [← Scheme.comp_base_apply]
  congr 4
  apply pullback.hom_ext <;> simp [diagonalCover_map]

/-- The restriction of the diagonal `X ⟶ X ×ₛ X` to `𝒱 i j ×[𝒰 i] 𝒱 i j` is the diagonal
`𝒱 i j ⟶ 𝒱 i j ×[𝒰 i] 𝒱 i j`. -/
noncomputable
def diagonalRestrictIsoDiagonal (i j) :
    Arrow.mk (pullback.diagonal f ∣_ ((diagonalCover f 𝒰 𝒱).map ⟨i, j, j⟩).opensRange) ≅
    Arrow.mk (pullback.diagonal ((𝒱 i).map j ≫ pullback.snd _ _)) := by
  refine (morphismRestrictOpensRange _ _).trans ?_
  refine Arrow.isoMk ?_ (Iso.refl _) ?_
  · exact pullback.congrHom rfl (diagonalCover_map _ _ _ _) ≪≫
      pullbackDiagonalMapIso _ _ _ _ ≪≫ (asIso (pullback.diagonal _)).symm
  have H : pullback.snd (pullback.diagonal f) ((diagonalCover f 𝒰 𝒱).map ⟨i, (j, j)⟩) ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ := by
    rw [← cancel_mono ((𝒱 i).map _)]
    apply pullback.hom_ext
    · trans pullback.snd (pullback.diagonal f) ((diagonalCover f 𝒰 𝒱).map ⟨i, (j, j)⟩) ≫
        (diagonalCover f 𝒰 𝒱).map _ ≫ pullback.snd _ _
      · simp [diagonalCover_map]
      symm
      trans pullback.snd (pullback.diagonal f) ((diagonalCover f 𝒰 𝒱).map ⟨i, (j, j)⟩) ≫
        (diagonalCover f 𝒰 𝒱).map _ ≫ pullback.fst _ _
      · simp [diagonalCover_map]
      · rw [← pullback.condition_assoc, ← pullback.condition_assoc]
        simp
    · simp [pullback.condition]
  apply pullback.hom_ext
  · dsimp
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    simp only [← Category.assoc, IsIso.comp_inv_eq]
    apply pullback.hom_ext <;> simp [H]
  · dsimp
    simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
    simp only [← Category.assoc, IsIso.comp_inv_eq]
    apply pullback.hom_ext <;> simp [H]

lemma isClosedImmersion_diagonal_restrict
    [∀ i, IsAffine (𝒰.obj i)] [∀ i j, IsAffine ((𝒱 i).obj j)] :
    IsClosedImmersion (pullback.diagonal f ∣_ diagonalCoverDiagonal f 𝒰 𝒱) := by
  let U : (Σ i, (𝒱 i).J) → (diagonalCoverDiagonal f 𝒰 𝒱).toScheme.Opens := fun i ↦
    (diagonalCoverDiagonal f 𝒰 𝒱).ι ⁻¹ᵁ ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange
  have hU (i) : (diagonalCoverDiagonal f 𝒰 𝒱).ι ''ᵁ U i =
      ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange := by
    rw [TopologicalSpace.Opens.functor_obj_map_obj, inf_eq_right, Hom.image_top_eq_opensRange,
      Opens.opensRange_ι]
    exact le_iSup (fun i : Σ i, (𝒱 i).J ↦ ((diagonalCover f 𝒰 𝒱).map ⟨i.1, i.2, i.2⟩).opensRange) i
  have hf : iSup U = ⊤ :=
    (TopologicalSpace.Opens.map_iSup _ _).symm.trans (diagonalCoverDiagonal f 𝒰 𝒱).ι_preimage_self
  rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hf]
  intro i
  rw [MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictRestrict _ _ _),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (morphismRestrictEq _ (hU i)),
    MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) (diagonalRestrictIsoDiagonal ..)]
  infer_instance

end Scheme.Pullback

open Scheme.Pullback

@[stacks 01KJ]
instance : IsImmersion (pullback.diagonal f) := by
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.map i)).affineCover
  have H : pullback.diagonal f ⁻¹ᵁ diagonalCoverDiagonal f 𝒰 𝒱 = ⊤ :=
    top_le_iff.mp fun _ _ ↦ range_diagonal_subset_diagonalCoverDiagonal _ _ _ ⟨_, rfl⟩
  have := isClosedImmersion_diagonal_restrict f 𝒰 𝒱
  have : IsImmersion ((pullback.diagonal f ∣_ diagonalCoverDiagonal f 𝒰 𝒱) ≫ Scheme.Opens.ι _) :=
    inferInstance
  rwa [morphismRestrict_ι, H, ← Scheme.topIso_hom,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsImmersion)] at this

@[stacks 0DVA]
lemma isSeparated_of_injective (hf : Function.Injective f.base) :
    IsSeparated f := by
  constructor
  let 𝒰 := Y.affineCover
  let 𝒱 (i) := (pullback f (𝒰.map i)).affineCover
  refine IsLocalAtTarget.of_iSup_eq_top (fun i : PUnit.{0} ↦ ⊤) (by simp) fun _ ↦ ?_
  rw [← diagonalCoverDiagonal_eq_top_of_injective f 𝒰 𝒱 hf]
  exact isClosedImmersion_diagonal_restrict f 𝒰 𝒱

end AlgebraicGeometry
