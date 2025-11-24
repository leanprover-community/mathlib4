/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Sets.CompactOpenCovered

/-!
# Quasi-compact covers

A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

This is used to define the fpqc (faithfully flat, quasi-compact) topology, where covers are given by
flat covers that are quasi-compact.
-/

@[expose] public section

universe w' w u v

open CategoryTheory Limits MorphismProperty TopologicalSpace.Opens AlgebraicGeometry

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/--
A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

Note: This is available with dot notation after `open AlgebraicGeometry`.
-/
@[stacks 022B, mk_iff]
class CategoryTheory.PreZeroHypercover.QuasiCompact (𝒰 : PreZeroHypercover.{v} S) : Prop where
  isCompactOpenCovered_of_isAffineOpen {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (fun i ↦ (𝒰.f i).base) U.1

variable (𝒰 : PreZeroHypercover.{v} S)

lemma IsAffineOpen.isCompactOpenCovered [𝒰.QuasiCompact] {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (fun i ↦ (𝒰.f i).base) U.1 :=
  CategoryTheory.PreZeroHypercover.QuasiCompact.isCompactOpenCovered_of_isAffineOpen hU

lemma CategoryTheory.PreZeroHypercover.isCompactOpenCovered_of_isCompact [𝒰.QuasiCompact]
    {U : S.Opens} (hU : IsCompact U.1) :
    IsCompactOpenCovered (fun i ↦ (𝒰.f i).base) U.1 := by
  obtain ⟨Us, hUs, hUf, hUc⟩ := S.isBasis_affineOpens.exists_finite_of_isCompact hU
  refine .of_iUnion_eq_of_finite (SetLike.coe '' Us) (by aesop) (hUf.image _) ?_
  simpa using fun t ht ↦ IsAffineOpen.isCompactOpenCovered 𝒰 (hUs ht)

namespace CategoryTheory.PreZeroHypercover.QuasiCompact

variable {𝒰 : PreZeroHypercover.{v} S} {K : Precoverage Scheme.{u}}

variable (𝒰) in
lemma exists_isAffineOpen_of_isCompact [𝒰.QuasiCompact] {U : S.Opens} (hU : IsCompact U.1) :
    ∃ (n : ℕ) (f : Fin n → 𝒰.I₀) (V : ∀ i, (𝒰.X (f i)).Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      ⋃ i, (𝒰.f (f i)).base '' (V i) = U := by
  obtain ⟨n, a, V, ha, heq⟩ := (𝒰.isCompactOpenCovered_of_isCompact hU).exists_mem_of_isBasis
    (fun i ↦ (𝒰.X i).isBasis_affineOpens) (fun _ _ h ↦ h.isCompact)
  exact ⟨n, a, V, ha, heq⟩

/-- If the component maps of `𝒰` are open, `𝒰` is quasi-compact. This in particular
applies if `K` is the is the fppf topology (i.e., flat and of finite presentation) and hence in
particular for étale and Zariski covers. -/
@[stacks 022C]
lemma of_isOpenMap {𝒰 : S.Cover K} [Scheme.JointlySurjective K] (h : ∀ i, IsOpenMap (𝒰.f i).base) :
    𝒰.QuasiCompact where
  isCompactOpenCovered_of_isAffineOpen {U} hU := .of_isOpenMap
    (fun i ↦ (𝒰.f i).continuous) h (fun x _ ↦ ⟨𝒰.idx x, 𝒰.covers x⟩) U.2 hU.isCompact

/-- Any open cover is quasi-compact. -/
instance (𝒰 : S.OpenCover) : 𝒰.QuasiCompact :=
  of_isOpenMap fun i ↦ (𝒰.f i).isOpenEmbedding.isOpenMap

/-- If `𝒱` is a refinement of `𝒰` such that `𝒱` is quasicompact, also `𝒰` is quasicompact. -/
@[stacks 03L8]
lemma of_hom {𝒱 : PreZeroHypercover.{w'} S} (f : 𝒱.Hom 𝒰) [𝒱.QuasiCompact] : 𝒰.QuasiCompact := by
  refine ⟨fun {U} hU ↦ ?_⟩
  exact .of_comp (a := f.s₀) (fun i ↦ (𝒱.f i).base) (fun i ↦ (f.h₀ i).base)
    (fun _ ↦ Scheme.Hom.continuous _) (fun i ↦ funext <| by simp [← Scheme.Hom.comp_apply])
    (fun _ ↦ Scheme.Hom.continuous _) U.2 (hU.isCompactOpenCovered 𝒱)

variable (𝒰) in
@[stacks 022D "(3)"]
instance [𝒰.QuasiCompact] {T : Scheme.{u}} (f : T ⟶ S) : (𝒰.pullback₁ f).QuasiCompact := by
  refine ⟨fun {U'} hU' ↦ ?_⟩
  wlog h : ∃ (U : S.Opens), IsAffineOpen U ∧ f.base '' U' ⊆ U generalizing U'
  · refine .of_isCompact_of_forall_exists hU'.isCompact fun x hxU ↦ ?_
    obtain ⟨W, hW, hx, _⟩ := isBasis_iff_nbhd.mp S.isBasis_affineOpens (mem_top (f.base x))
    obtain ⟨W', hW', hx', hle⟩ := isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ W ⊓ U' from ⟨hx, hxU⟩)
    exact ⟨W', le_trans hle inf_le_right, by simpa [hx], W'.2,
      this hW' ⟨W, hW, by simpa using le_trans hle inf_le_left⟩⟩
  obtain ⟨U, hU, hsub⟩ := h
  obtain ⟨s, hf, V, hc, (heq : _ = (U : Set S))⟩ := hU.isCompactOpenCovered 𝒰
  refine ⟨s, hf, fun i hi ↦ pullback.fst f (𝒰.f i) ⁻¹ᵁ U' ⊓ pullback.snd f (𝒰.f i) ⁻¹ᵁ (V i hi),
      fun i hi ↦ ?_, ?_⟩
  · exact hU'.isCompact_pullback_inf (hc _ _) hU (by simpa using hsub) <| show _ ⊆ _ by
      simpa [← heq, Set.range_comp] using Set.subset_iUnion_of_subset i
        (Set.subset_iUnion_of_subset hi (Set.subset_preimage_image _ _))
  · refine subset_antisymm (by simp) (fun x hx ↦ ?_)
    have : f.base x ∈ (U : Set S) := hsub ⟨x, hx, rfl⟩
    simp_rw [← heq, Set.mem_iUnion] at this
    obtain ⟨i, hi, y, hy, heq⟩ := this
    simp_rw [Set.mem_iUnion]
    obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback x y heq.symm
    exact ⟨i, hi, z, ⟨by simpa [hzl], by simpa [hzr]⟩, hzl⟩

variable (𝒰) in
instance [𝒰.QuasiCompact] {T : Scheme.{u}} (f : T ⟶ S) : (𝒰.pullback₂ f).QuasiCompact :=
  .of_hom (PreZeroHypercover.pullbackIso f 𝒰).hom

@[stacks 022D "(2)"]
instance {X : Scheme.{u}} (𝒰 : PreZeroHypercover.{w} X) [𝒰.QuasiCompact]
    (f : ∀ (x : 𝒰.I₀), PreZeroHypercover.{w} (𝒰.X x)) [∀ x, (f x).QuasiCompact] :
    QuasiCompact (𝒰.bind f) where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    obtain ⟨s, hs, V, hcV, hU⟩ := hU.isCompactOpenCovered 𝒰
    have (i) (hi) : IsCompactOpenCovered (fun k ↦ ((f i).f k).base) (V i hi) :=
      (f i).isCompactOpenCovered_of_isCompact (hcV i hi)
    choose t ht W hcW hV using this
    have : Finite s := hs
    have (i) (hi) : Finite (t i hi) := ht i hi
    refine .of_finite (κ := Σ (i : s), t i.1 i.2) (fun p ↦ ⟨p.1, p.2⟩) (fun p ↦ W _ p.1.2 _ p.2.2)
      (fun p ↦ hcW ..) ?_
    simpa [← hV, Set.iUnion_sigma, Set.iUnion_subtype, Set.image_iUnion, Set.image_image] using hU

instance of_finite {𝒰 : S.Cover K} [Scheme.JointlySurjective K]
    [∀ i, AlgebraicGeometry.QuasiCompact (𝒰.f i)] [Finite 𝒰.I₀] : 𝒰.QuasiCompact where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    refine .of_finite_of_isSpectralMap (fun i ↦ (𝒰.f i).isSpectralMap) ?_ U.2 hU.isCompact
    exact (fun x _ ↦ ⟨𝒰.idx x, 𝒰.covers x⟩)

variable {P : MorphismProperty Scheme.{u}}

instance homCover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f]
    [AlgebraicGeometry.QuasiCompact f] : (f.cover hf).QuasiCompact :=
  have _ (i) : AlgebraicGeometry.QuasiCompact ((f.cover hf).f i) := ‹_›
  .of_finite

instance singleton {X : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    [AlgebraicGeometry.QuasiCompact f] : (PreZeroHypercover.singleton f).QuasiCompact :=
  homCover (P := ⊤) f trivial

@[stacks 022D "(1)"]
instance {P : MorphismProperty Scheme.{u}} [P.ContainsIdentities] [P.RespectsIso]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] :
    (Scheme.coverOfIsIso (P := P) f).QuasiCompact :=
  of_isOpenMap (fun _ ↦ f.homeomorph.isOpenMap)

end CategoryTheory.PreZeroHypercover.QuasiCompact

namespace Scheme

/-- The object property on the category of pre-`0`-hypercovers of a scheme given
by quasi-compact covers. -/
def quasiCompactCover (S : Scheme.{u}) : ObjectProperty (PreZeroHypercover.{v} S) :=
  fun 𝒰 ↦ 𝒰.QuasiCompact

@[simp]
lemma quasiCompactCover_iff (S : Scheme.{u}) (𝒰 : PreZeroHypercover.{v} S) :
    S.quasiCompactCover 𝒰 ↔ 𝒰.QuasiCompact := .rfl

instance isClosedUnderIsomorphisms_quasiCompactCover (S : Scheme.{u}) :
    S.quasiCompactCover.IsClosedUnderIsomorphisms where
  of_iso {𝒰 _} e (_ : 𝒰.QuasiCompact) := .of_hom e.hom

end Scheme

end AlgebraicGeometry
