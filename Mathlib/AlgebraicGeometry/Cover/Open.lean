/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-!
# Open covers of schemes

This file provides the basic API for open covers of schemes.

## Main definition
- `AlgebraicGeometry.Scheme.OpenCover`: The type of open covers of a scheme `X`,
  consisting of a family of open immersions into `X`,
  and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.
- `AlgebraicGeometry.Scheme.affineCover`: `X.affineCover` is a choice of an affine cover of `X`.
- `AlgebraicGeometry.Scheme.AffineOpenCover`: The type of affine open covers of a scheme `X`.
-/


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

universe v v₁ v₂ u

namespace AlgebraicGeometry

namespace Scheme

instance : MorphismProperty.HasPullbacks IsOpenImmersion where
  hasPullback _ _ := inferInstance

/-- An open cover of a scheme `X` is a cover where all component maps are open immersions. -/
abbrev OpenCover (X : Scheme.{u}) : Type _ := Cover.{v} (precoverage @IsOpenImmersion) X

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ x, HasPullback (𝒰.f x ≫ f) g]

instance (i : 𝒰.I₀) : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i

/-- The affine cover of a scheme. -/
def affineCover (X : Scheme.{u}) : OpenCover X where
  I₀ := X
  X x := Spec (X.local_affine x).choose_spec.choose
  f x :=
    ⟨(X.local_affine x).choose_spec.choose_spec.some.inv ≫ X.toLocallyRingedSpace.ofRestrict _⟩
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    use x
    simp only [LocallyRingedSpace.comp_toShHom, SheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp]
    rw [Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
    · erw [Subtype.range_coe_subtype]
      exact (X.local_affine x).choose.2
    rw [← TopCat.epi_iff_surjective]
    change Epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forgetToSheafedSpace.map _))
    infer_instance

instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

theorem OpenCover.iSup_opensRange {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    ⨆ i, (𝒰.f i).opensRange = ⊤ :=
  Opens.ext <| by rw [Opens.coe_iSup]; exact 𝒰.iUnion_range

/-- The ranges of the maps in a scheme-theoretic open cover are a topological open cover. -/
lemma OpenCover.isOpenCover_opensRange {X : Scheme.{u}} (𝒰 : X.OpenCover) :
    IsOpenCover fun i ↦ (𝒰.f i).opensRange :=
  .mk 𝒰.iSup_opensRange

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps! X f]
def OpenCover.finiteSubcover {X : Scheme.{u}} (𝒰 : OpenCover X) [H : CompactSpace X] :
    OpenCover X := by
  have :=
    @CompactSpace.elim_nhds_subcover _ _ H (fun x : X => Set.range (𝒰.f (𝒰.idx x)).base)
      fun x => (IsOpenImmersion.isOpen_range (𝒰.f (𝒰.idx x))).mem_nhds (𝒰.covers x)
  let t := this.choose
  have h : ∀ x : X, ∃ y : t, x ∈ Set.range (𝒰.f (𝒰.idx y)).base := by
    intro x
    have h' : x ∈ (⊤ : Set X) := trivial
    rw [← Classical.choose_spec this, Set.mem_iUnion] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { I₀ := t
      X := fun x => 𝒰.X (𝒰.idx x.1)
      f := fun x => 𝒰.f (𝒰.idx x.1)
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        exact ⟨h, inferInstance⟩ }

instance [H : CompactSpace X] : Fintype 𝒰.finiteSubcover.I₀ := by
  delta OpenCover.finiteSubcover; infer_instance

theorem OpenCover.compactSpace {X : Scheme.{u}} (𝒰 : X.OpenCover) [Finite 𝒰.I₀]
    [H : ∀ i, CompactSpace (𝒰.X i)] : CompactSpace X := by
  cases nonempty_fintype 𝒰.I₀
  rw [← isCompact_univ_iff, ← 𝒰.iUnion_range]
  apply isCompact_iUnion
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @Homeomorph.compactSpace _ _ _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.f i)
            (X.ofRestrict (Opens.isOpenEmbedding ⟨_, (𝒰.map_prop i).base_open.isOpen_range⟩))
            Subtype.range_coe.symm).hom.base))
/--
An affine open cover of `X` consists of a family of open immersions into `X` from
spectra of rings.
-/
abbrev AffineOpenCover (X : Scheme.{u}) : Type _ :=
  AffineCover.{v} @IsOpenImmersion X

namespace AffineOpenCover

instance {X : Scheme.{u}} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀) : IsOpenImmersion (𝒰.f j) :=
  𝒰.map_prop j

/-- The open cover associated to an affine open cover. -/
@[simps! I₀ X f]
def openCover {X : Scheme.{u}} (𝒰 : X.AffineOpenCover) : X.OpenCover :=
  AffineCover.cover 𝒰

end AffineOpenCover

/-- A choice of an affine open cover of a scheme. -/
@[simps]
def affineOpenCover (X : Scheme.{u}) : X.AffineOpenCover where
  X := _
  I₀ := X.affineCover.I₀
  f := X.affineCover.f
  idx x := (X.affineCover.exists_eq x).choose
  covers x := (X.affineCover.exists_eq x).choose_spec

@[simp]
lemma openCover_affineOpenCover (X : Scheme.{u}) : X.affineOpenCover.openCover = X.affineCover :=
  rfl

/-- Given any open cover `𝓤`, this is an affine open cover which refines it.
The morphism in the category of open covers which proves that this is indeed a refinement, see
`AlgebraicGeometry.Scheme.OpenCover.fromAffineRefinement`.
-/
def OpenCover.affineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) : X.AffineOpenCover where
  X := _
  I₀ := (𝓤.bind fun j => (𝓤.X j).affineCover).I₀
  f := (𝓤.bind fun j => (𝓤.X j).affineCover).f
  idx := Cover.idx (𝓤.bind fun j => (𝓤.X j).affineCover)
  covers := Cover.covers (𝓤.bind fun j => (𝓤.X j).affineCover)

/-- The pullback of the affine refinement is the pullback of the affine cover. -/
def OpenCover.pullbackCoverAffineRefinementObjIso (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.affineRefinement.openCover.pullback₁ f).X i ≅
      ((𝒰.X i.1).affineCover.pullback₁ (𝒰.pullbackHom f i.1)).X i.2 :=
  pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso _ _ _).symm ≪≫
    pullbackSymmetry _ _ ≪≫ asIso (pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _)
      (by simp [Cover.pullbackHom]) (by simp))

@[reassoc]
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_map (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      (𝒰.affineRefinement.openCover.pullback₁ f).f i =
      ((𝒰.X i.1).affineCover.pullback₁ (𝒰.pullbackHom f i.1)).f i.2 ≫
        (𝒰.pullback₁ f).f i.1 := by
  simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, AffineOpenCover.openCover_X, AffineOpenCover.openCover_f,
    pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv, Iso.symm_inv, Category.assoc,
    PreZeroHypercover.pullback₁_f, pullbackSymmetry_inv_comp_fst, IsIso.inv_comp_eq,
    limit.lift_π_assoc, PullbackCone.mk_pt, cospan_left, PullbackCone.mk_π_app,
    pullbackSymmetry_hom_comp_fst]
  convert pullbackSymmetry_inv_comp_snd_assoc
    ((𝒰.X i.1).affineCover.f i.2) (pullback.fst _ _) _ using 2
  exact pullbackRightPullbackFstIso_hom_snd _ _ _

@[reassoc]
lemma OpenCover.pullbackCoverAffineRefinementObjIso_inv_pullbackHom
    (f : X ⟶ Y) (𝒰 : Y.OpenCover) (i) :
    (𝒰.pullbackCoverAffineRefinementObjIso f i).inv ≫
      𝒰.affineRefinement.openCover.pullbackHom f i =
      (𝒰.X i.1).affineCover.pullbackHom (𝒰.pullbackHom f i.1) i.2 := by
  simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
    PreZeroHypercover.pullback₁_X, Cover.pullbackHom, AffineOpenCover.openCover_X,
    AffineOpenCover.openCover_f, pullbackCoverAffineRefinementObjIso, Iso.trans_inv, asIso_inv,
    Iso.symm_inv, Category.assoc, pullbackSymmetry_inv_comp_snd, IsIso.inv_comp_eq, limit.lift_π,
    PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id]
  convert pullbackSymmetry_inv_comp_fst ((𝒰.X i.1).affineCover.f i.2) (pullback.fst _ _)
  exact pullbackRightPullbackFstIso_hom_fst _ _ _

/-- A family of elements spanning the unit ideal of `R` gives a affine open cover of `Spec R`. -/
@[simps]
noncomputable
def affineOpenCoverOfSpanRangeEqTop {R : CommRingCat} {ι : Type*} (s : ι → R)
    (hs : Ideal.span (Set.range s) = ⊤) : (Spec R).AffineOpenCover where
  I₀ := ι
  X i := .of (Localization.Away (s i))
  f i := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s i))))
  idx x := by
    have : ∃ i, s i ∉ x.asIdeal := by
      by_contra! h; apply x.2.ne_top; rwa [← top_le_iff, ← hs, Ideal.span_le, Set.range_subset_iff]
    exact this.choose
  covers x := by
    generalize_proofs H
    let i := H.choose
    have := PrimeSpectrum.localization_away_comap_range (Localization.Away (s i)) (s i)
    exact (eq_iff_iff.mp congr(x ∈ $this)).mpr H.choose_spec

/-- Given any open cover `𝓤`, this is an affine open cover which refines it. -/
def OpenCover.fromAffineRefinement {X : Scheme.{u}} (𝓤 : X.OpenCover) :
    𝓤.affineRefinement.openCover ⟶ 𝓤 where
  idx j := j.fst
  app j := (𝓤.X j.fst).affineCover.f _

/-- If two global sections agree after restriction to each member of an open cover, then
they agree globally. -/
lemma OpenCover.ext_elem {X : Scheme.{u}} {U : X.Opens} (f g : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.I₀, (𝒰.f i).app U f = (𝒰.f i).app U g) : f = g := by
  fapply TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun i ↦ (𝒰.f (𝒰.idx i)).opensRange ⊓ U) _ (fun _ ↦ homOfLE inf_le_right)
  · intro x hx
    simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_inf, Hom.coe_opensRange, Opens.coe_mk,
      Set.mem_iUnion, Set.mem_inter_iff, Set.mem_range, SetLike.mem_coe, exists_and_right]
    refine ⟨?_, hx⟩
    simpa using ⟨_, 𝒰.covers x⟩
  · intro x
    replace h := h (𝒰.idx x)
    rw [← IsOpenImmersion.map_ΓIso_inv] at h
    exact (IsOpenImmersion.ΓIso (𝒰.f (𝒰.idx x)) U).commRingCatIsoToRingEquiv.symm.injective h

/-- If the restriction of a global section to each member of an open cover is zero, then it is
globally zero. -/
lemma zero_of_zero_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U)) (𝒰 : X.OpenCover)
    (h : ∀ i : 𝒰.I₀, (𝒰.f i).app U s = 0) : s = 0 :=
  𝒰.ext_elem s 0 (fun i ↦ by rw [map_zero]; exact h i)

/-- If a global section is nilpotent on each member of a finite open cover, then `f` is
nilpotent. -/
lemma isNilpotent_of_isNilpotent_cover {X : Scheme.{u}} {U : X.Opens} (s : Γ(X, U))
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (h : ∀ i : 𝒰.I₀, IsNilpotent ((𝒰.f i).app U s)) :
    IsNilpotent s := by
  choose fn hfn using h
  have : Fintype 𝒰.I₀ := Fintype.ofFinite 𝒰.I₀
  /- the maximum of all `fn i` (exists, because `𝒰.I₀` is finite) -/
  let N : ℕ := Finset.sup Finset.univ fn
  have hfnleN (i : 𝒰.I₀) : fn i ≤ N := Finset.le_sup (Finset.mem_univ i)
  use N
  apply zero_of_zero_cover (𝒰 := 𝒰)
  on_goal 1 => intro i; simp only [map_pow]
  -- This closes both remaining goals at once.
  exact pow_eq_zero_of_le (hfnleN i) (hfn i)

section deprecated

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingCat.{u}) : OpenCover (Spec R) where
  I₀ := R
  X r := Spec <| .of <| Localization.Away r
  f r := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ⟨1, ?_⟩, AlgebraicGeometry.Scheme.basic_open_isOpenImmersion⟩
    rw [Set.range_eq_univ.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · infer_instance

/-- We may bind the basic open sets of an open affine cover to form an affine cover that is also
a basis. -/
def affineBasisCover (X : Scheme.{u}) : OpenCover X :=
  X.affineCover.bind fun _ => affineBasisCoverOfAffine _

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : Scheme.{u}) (i : X.affineBasisCover.I₀) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2

theorem affineBasisCover_obj (X : Scheme.{u}) (i : X.affineBasisCover.I₀) :
    X.affineBasisCover.X i = Spec (X.affineBasisCoverRing i) :=
  rfl

theorem affineBasisCover_map_range (X : Scheme.{u}) (x : X)
    (r : (X.local_affine x).choose_spec.choose) :
    Set.range (X.affineBasisCover.f ⟨x, r⟩).base =
      (X.affineCover.f x).base '' (PrimeSpectrum.basicOpen r).1 := by
  simp only [affineBasisCover, Precoverage.ZeroHypercover.bind_toPreZeroHypercover,
    PreZeroHypercover.bind_f, comp_coeBase, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r :)

theorem affineBasisCover_is_basis (X : Scheme.{u}) :
    TopologicalSpace.IsTopologicalBasis
      {x : Set X |
        ∃ a : X.affineBasisCover.I₀, x = Set.range (X.affineBasisCover.f a).base} := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.isOpen_range (X.affineBasisCover.f a)
  · rintro a U haU hU
    rcases X.affineCover.covers a with ⟨x, e⟩
    let U' := (X.affineCover.f (X.affineCover.idx a)).base ⁻¹' U
    have hxU' : x ∈ U' := by rw [← e] at haU; exact haU
    rcases PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affineCover.f (X.affineCover.idx a)).base.hom.continuous_toFun.isOpen_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine ⟨_, ⟨⟨_, s⟩, rfl⟩, ?_, ?_⟩ <;> rw [affineBasisCover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]; exact hVU

end deprecated

end Scheme

end AlgebraicGeometry
