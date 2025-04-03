/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.Topology.Spectral.Hom
import Mathlib.AlgebraicGeometry.Limits

#align_import algebraic_geometry.morphisms.quasi_compact from "leanprover-community/mathlib"@"5dc6092d09e5e489106865241986f7f2ad28d4c8"

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasiCompact_iff_forall_affine`).

-/


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is "quasi-compact" if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
class QuasiCompact (f : X ⟶ Y) : Prop where
  /-- Preimage of compact open set under a quasi-compact morphism between schemes is compact. -/
  isCompact_preimage : ∀ U : Set Y.carrier, IsOpen U → IsCompact U → IsCompact (f.1.base ⁻¹' U)
#align algebraic_geometry.quasi_compact AlgebraicGeometry.QuasiCompact

theorem quasiCompact_iff_spectral : QuasiCompact f ↔ IsSpectralMap f.1.base :=
  ⟨fun ⟨h⟩ => ⟨by continuity, h⟩, fun h => ⟨h.2⟩⟩
#align algebraic_geometry.quasi_compact_iff_spectral AlgebraicGeometry.quasiCompact_iff_spectral

/-- The `AffineTargetMorphismProperty` corresponding to `QuasiCompact`, asserting that the
domain is a quasi-compact scheme. -/
def QuasiCompact.affineProperty : AffineTargetMorphismProperty := fun X _ _ _ =>
  CompactSpace X.carrier
#align algebraic_geometry.quasi_compact.affine_property AlgebraicGeometry.QuasiCompact.affineProperty

instance (priority := 900) quasiCompactOfIsIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := by
  constructor
  intro U _ hU'
  convert hU'.image (inv f.1.base).continuous_toFun using 1
  rw [Set.image_eq_preimage_of_inverse]
  · delta Function.LeftInverse
    exact IsIso.inv_hom_id_apply f.1.base
  · exact IsIso.hom_inv_id_apply f.1.base
#align algebraic_geometry.quasi_compact_of_is_iso AlgebraicGeometry.quasiCompactOfIsIso

instance quasiCompactComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    [QuasiCompact g] : QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.comp_val_base, TopCat.coe_comp, Set.preimage_comp]
  apply QuasiCompact.isCompact_preimage
  · exact Continuous.isOpen_preimage (by
    -- Porting note: `continuity` failed
    -- see https://github.com/leanprover-community/mathlib4/issues/5030
      exact Scheme.Hom.continuous g) _ hU
  apply QuasiCompact.isCompact_preimage <;> assumption
#align algebraic_geometry.quasi_compact_comp AlgebraicGeometry.quasiCompactComp

theorem isCompact_open_iff_eq_finset_affine_union {X : Scheme} (U : Set X.carrier) :
    IsCompact U ∧ IsOpen U ↔
      ∃ s : Set X.affineOpens, s.Finite ∧ U = ⋃ (i : X.affineOpens) (_ : i ∈ s), i := by
  apply Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    (fun (U : X.affineOpens) => (U : Opens X.carrier))
  · rw [Subtype.range_coe]; exact isBasis_affine_open X
  · exact fun i => i.2.isCompact
#align algebraic_geometry.is_compact_open_iff_eq_finset_affine_union AlgebraicGeometry.isCompact_open_iff_eq_finset_affine_union

theorem isCompact_open_iff_eq_basicOpen_union {X : Scheme} [IsAffine X] (U : Set X.carrier) :
    IsCompact U ∧ IsOpen U ↔
      ∃ s : Set (X.presheaf.obj (op ⊤)),
        s.Finite ∧ U = ⋃ (i : X.presheaf.obj (op ⊤)) (_ : i ∈ s), X.basicOpen i :=
  (isBasis_basicOpen X).isCompact_open_iff_eq_finite_iUnion _
    (fun _ => ((topIsAffineOpen _).basicOpenIsAffine _).isCompact) _
#align algebraic_geometry.is_compact_open_iff_eq_basic_open_union AlgebraicGeometry.isCompact_open_iff_eq_basicOpen_union

theorem quasiCompact_iff_forall_affine :
    QuasiCompact f ↔
      ∀ U : Opens Y.carrier, IsAffineOpen U → IsCompact (f.1.base ⁻¹' (U : Set Y.carrier)) := by
  rw [quasiCompact_iff]
  refine ⟨fun H U hU => H U U.isOpen hU.isCompact, ?_⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := (isCompact_open_iff_eq_finset_affine_union U).mp ⟨hU', hU⟩
  simp only [Set.preimage_iUnion]
  exact Set.Finite.isCompact_biUnion hS (fun i _ => H i i.prop)
#align algebraic_geometry.quasi_compact_iff_forall_affine AlgebraicGeometry.quasiCompact_iff_forall_affine

@[simp]
theorem QuasiCompact.affineProperty_toProperty {X Y : Scheme} (f : X ⟶ Y) :
    (QuasiCompact.affineProperty : _).toProperty f ↔ IsAffine Y ∧ CompactSpace X.carrier := by
  delta AffineTargetMorphismProperty.toProperty QuasiCompact.affineProperty; simp
#align algebraic_geometry.quasi_compact.affine_property_to_property AlgebraicGeometry.QuasiCompact.affineProperty_toProperty

theorem quasiCompact_iff_affineProperty :
    QuasiCompact f ↔ targetAffineLocally QuasiCompact.affineProperty f := by
  rw [quasiCompact_iff_forall_affine]
  trans ∀ U : Y.affineOpens, IsCompact (f.1.base ⁻¹' (U : Set Y.carrier))
  · exact ⟨fun h U => h U U.prop, fun h U hU => h ⟨U, hU⟩⟩
  apply forall_congr'
  exact fun _ => isCompact_iff_compactSpace
#align algebraic_geometry.quasi_compact_iff_affine_property AlgebraicGeometry.quasiCompact_iff_affineProperty

theorem quasiCompact_eq_affineProperty :
    @QuasiCompact = targetAffineLocally QuasiCompact.affineProperty := by
  ext
  exact quasiCompact_iff_affineProperty _
#align algebraic_geometry.quasi_compact_eq_affine_property AlgebraicGeometry.quasiCompact_eq_affineProperty

theorem isCompact_basicOpen (X : Scheme) {U : Opens X.carrier} (hU : IsCompact (U : Set X.carrier))
    (f : X.presheaf.obj (op U)) : IsCompact (X.basicOpen f : Set X.carrier) := by
  classical
  refine ((isCompact_open_iff_eq_finset_affine_union _).mpr ?_).1
  obtain ⟨s, hs, e⟩ := (isCompact_open_iff_eq_finset_affine_union _).mp ⟨hU, U.isOpen⟩
  let g : s → X.affineOpens := by
    intro V
    use V.1 ⊓ X.basicOpen f
    have : V.1.1 ⟶ U := by
      apply homOfLE; change _ ⊆ (U : Set X.carrier); rw [e]
      convert Set.subset_iUnion₂ (s := fun (U : X.affineOpens) (_ : U ∈ s) => (U : Set X.carrier))
        V V.prop using 1
    erw [← X.toLocallyRingedSpace.toRingedSpace.basicOpen_res this.op]
    exact IsAffineOpen.basicOpenIsAffine V.1.prop _
  haveI : Finite s := hs.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  refine (Set.inter_eq_right.mpr
            (SetLike.coe_subset_coe.2 <| RingedSpace.basicOpen_le _ _)).symm.trans ?_
  rw [e, Set.iUnion₂_inter]
  apply le_antisymm <;> apply Set.iUnion₂_subset
  · intro i hi
    -- Porting note: had to make explicit the first given parameter to `Set.subset_iUnion₂`
    exact Set.Subset.trans (Set.Subset.rfl : _ ≤ g ⟨i, hi⟩)
      (@Set.subset_iUnion₂ _ _ _
        (fun (i : Scheme.affineOpens X) (_ : i ∈ Set.range g) => (i : Set X.toPresheafedSpace)) _
        (Set.mem_range_self ⟨i, hi⟩))
  · rintro ⟨i, hi⟩ ⟨⟨j, hj⟩, hj'⟩
    rw [← hj']
    refine Set.Subset.trans ?_ (Set.subset_iUnion₂ j hj)
    exact Set.Subset.rfl
#align algebraic_geometry.is_compact_basic_open AlgebraicGeometry.isCompact_basicOpen

theorem QuasiCompact.affineProperty_isLocal : (QuasiCompact.affineProperty : _).IsLocal := by
  constructor
  · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
    exacts [@Homeomorph.compactSpace _ _ _ _ H (TopCat.homeoOfIso (asIso e.inv.1.base)), H]
  · introv H
    dsimp [affineProperty] at H ⊢
    change CompactSpace ((Opens.map f.val.base).obj (Y.basicOpen r))
    rw [Scheme.preimage_basicOpen f r]
    erw [← isCompact_iff_compactSpace]
    rw [← isCompact_univ_iff] at H
    apply isCompact_basicOpen
    exact H
  · rintro X Y H f S hS hS'
    rw [← IsAffineOpen.basicOpen_union_eq_self_iff] at hS
    · delta QuasiCompact.affineProperty
      rw [← isCompact_univ_iff]
      change IsCompact ((Opens.map f.val.base).obj ⊤).1
      rw [← hS]
      dsimp [Opens.map]
      simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk, Set.preimage_iUnion]
      exact isCompact_iUnion fun i => isCompact_iff_compactSpace.mpr (hS' i)
    · exact topIsAffineOpen _
#align algebraic_geometry.quasi_compact.affine_property_is_local AlgebraicGeometry.QuasiCompact.affineProperty_isLocal

theorem QuasiCompact.affine_openCover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE
      [QuasiCompact f,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, CompactSpace (pullback f (𝒰.map i)).carrier,
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          CompactSpace (pullback f (𝒰.map i)).carrier,
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g],
          CompactSpace (pullback f g).carrier,
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (_ : iSup U = ⊤) (_ : ∀ i, IsAffineOpen (U i)),
          ∀ i, CompactSpace (f.1.base ⁻¹' (U i).1)] :=
  quasiCompact_eq_affineProperty.symm ▸ QuasiCompact.affineProperty_isLocal.affine_openCover_TFAE f
#align algebraic_geometry.quasi_compact.affine_open_cover_tfae AlgebraicGeometry.QuasiCompact.affine_openCover_tfae

theorem QuasiCompact.is_local_at_target : PropertyIsLocalAtTarget @QuasiCompact :=
  quasiCompact_eq_affineProperty.symm ▸
    QuasiCompact.affineProperty_isLocal.targetAffineLocallyIsLocal
#align algebraic_geometry.quasi_compact.is_local_at_target AlgebraicGeometry.QuasiCompact.is_local_at_target

theorem QuasiCompact.openCover_tfae {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE
      [QuasiCompact f,
        ∃ 𝒰 : Scheme.OpenCover.{u} Y,
          ∀ i : 𝒰.J, QuasiCompact (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) (i : 𝒰.J),
          QuasiCompact (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.carrier, QuasiCompact (f ∣_ U),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsOpenImmersion g],
          QuasiCompact (pullback.snd : pullback f g ⟶ _),
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (_ : iSup U = ⊤), ∀ i, QuasiCompact (f ∣_ U i)] :=
  quasiCompact_eq_affineProperty.symm ▸
    QuasiCompact.affineProperty_isLocal.targetAffineLocallyIsLocal.openCover_TFAE f
#align algebraic_geometry.quasi_compact.open_cover_tfae AlgebraicGeometry.QuasiCompact.openCover_tfae

theorem quasiCompact_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    QuasiCompact f ↔ CompactSpace X.carrier :=
  quasiCompact_eq_affineProperty.symm ▸ QuasiCompact.affineProperty_isLocal.affine_target_iff f
#align algebraic_geometry.quasi_compact_over_affine_iff AlgebraicGeometry.quasiCompact_over_affine_iff

theorem compactSpace_iff_quasiCompact (X : Scheme) :
    CompactSpace X.carrier ↔ QuasiCompact (terminal.from X) :=
  (quasiCompact_over_affine_iff _).symm
#align algebraic_geometry.compact_space_iff_quasi_compact AlgebraicGeometry.compactSpace_iff_quasiCompact

theorem QuasiCompact.affine_openCover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (f : X ⟶ Y) :
    QuasiCompact f ↔ ∀ i, CompactSpace (pullback f (𝒰.map i)).carrier :=
  quasiCompact_eq_affineProperty.symm ▸ QuasiCompact.affineProperty_isLocal.affine_openCover_iff f 𝒰
#align algebraic_geometry.quasi_compact.affine_open_cover_iff AlgebraicGeometry.QuasiCompact.affine_openCover_iff

theorem QuasiCompact.openCover_iff {X Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y) (f : X ⟶ Y) :
    QuasiCompact f ↔ ∀ i, QuasiCompact (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  quasiCompact_eq_affineProperty.symm ▸
    QuasiCompact.affineProperty_isLocal.targetAffineLocallyIsLocal.openCover_iff f 𝒰
#align algebraic_geometry.quasi_compact.open_cover_iff AlgebraicGeometry.QuasiCompact.openCover_iff

theorem quasiCompact_respectsIso : MorphismProperty.RespectsIso @QuasiCompact :=
  quasiCompact_eq_affineProperty.symm ▸
    targetAffineLocally_respectsIso QuasiCompact.affineProperty_isLocal.1
#align algebraic_geometry.quasi_compact_respects_iso AlgebraicGeometry.quasiCompact_respectsIso

instance quasiCompact_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiCompact where
  comp_mem _ _ _ _ := inferInstance
#align algebraic_geometry.quasi_compact_stable_under_composition AlgebraicGeometry.quasiCompact_isStableUnderComposition

theorem QuasiCompact.affineProperty_stableUnderBaseChange :
    QuasiCompact.affineProperty.StableUnderBaseChange := by
  intro X Y S _ _ f g h
  rw [QuasiCompact.affineProperty] at h ⊢
  let 𝒰 := Scheme.Pullback.openCoverOfRight Y.affineCover.finiteSubcover f g
  have : Finite 𝒰.J := by dsimp [𝒰]; infer_instance
  have : ∀ i, CompactSpace (𝒰.obj i).carrier := by intro i; dsimp [𝒰]; infer_instance
  exact 𝒰.compactSpace
#align algebraic_geometry.quasi_compact.affine_property_stable_under_base_change AlgebraicGeometry.QuasiCompact.affineProperty_stableUnderBaseChange

theorem quasiCompact_stableUnderBaseChange : MorphismProperty.StableUnderBaseChange @QuasiCompact :=
  quasiCompact_eq_affineProperty.symm ▸
    QuasiCompact.affineProperty_isLocal.stableUnderBaseChange
      QuasiCompact.affineProperty_stableUnderBaseChange
#align algebraic_geometry.quasi_compact_stable_under_base_change AlgebraicGeometry.quasiCompact_stableUnderBaseChange

variable {Z : Scheme.{u}}

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] :
    QuasiCompact (pullback.fst : pullback f g ⟶ X) :=
  quasiCompact_stableUnderBaseChange.fst f g inferInstance

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] :
    QuasiCompact (pullback.snd : pullback f g ⟶ Y) :=
  quasiCompact_stableUnderBaseChange.snd f g inferInstance

@[elab_as_elim]
theorem compact_open_induction_on {P : Opens X.carrier → Prop} (S : Opens X.carrier)
    (hS : IsCompact S.1) (h₁ : P ⊥)
    (h₂ : ∀ (S : Opens X.carrier) (_ : IsCompact S.1) (U : X.affineOpens), P S → P (S ⊔ U)) :
    P S := by
  classical
  obtain ⟨s, hs, hs'⟩ := (isCompact_open_iff_eq_finset_affine_union S.1).mp ⟨hS, S.2⟩
  replace hs' : S = iSup fun i : s => (i : Opens X.carrier) := by ext1; simpa using hs'
  subst hs'
  apply @Set.Finite.induction_on _ _ _ hs
  · convert h₁; rw [iSup_eq_bot]; rintro ⟨_, h⟩; exact h.elim
  · intro x s _ hs h₄
    have : IsCompact (⨆ i : s, (i : Opens X.carrier)).1 := by
      refine ((isCompact_open_iff_eq_finset_affine_union _).mpr ?_).1; exact ⟨s, hs, by simp⟩
    convert h₂ _ this x h₄
    rw [iSup_subtype, sup_comm]
    conv_rhs => rw [iSup_subtype]
    exact iSup_insert
#align algebraic_geometry.compact_open_induction_on AlgebraicGeometry.compact_open_induction_on

theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen (X : Scheme)
    {U : Opens X} (hU : IsAffineOpen U) (x f : X.presheaf.obj (op U))
    (H : x |_ X.basicOpen f = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  rw [← map_zero (X.presheaf.map (homOfLE <| X.basicOpen_le f : X.basicOpen f ⟶ U).op)] at H
  obtain ⟨⟨_, n, rfl⟩, e⟩ := (hU.isLocalization_basicOpen f).exists_of_eq H
  exact ⟨n, by simpa [mul_comm x] using e⟩
#align algebraic_geometry.exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_affine_open AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen

/-- If `x : Γ(X, U)` is zero on `D(f)` for some `f : Γ(X, U)`, and `U` is quasi-compact, then
`f ^ n * x = 0` for some `n`. -/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme.{u})
    {U : Opens X.carrier} (hU : IsCompact U.1) (x f : X.presheaf.obj (op U))
    (H : x |_ X.basicOpen f = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  obtain ⟨s, hs, e⟩ := (isCompact_open_iff_eq_finset_affine_union U.1).mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : Opens X.carrier) := by
    ext1; simpa using e
  have h₁ : ∀ i : s, i.1.1 ≤ U := by
    intro i
    change (i : Opens X.carrier) ≤ U
    rw [e]
    -- Porting note: `exact le_iSup _ _` no longer works
    exact le_iSup (fun (i : s) => (i : Opens (X.toPresheafedSpace))) _
  have H' := fun i : s =>
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X i.1.2
      (X.presheaf.map (homOfLE (h₁ i)).op x) (X.presheaf.map (homOfLE (h₁ i)).op f) ?_
  swap
  · delta TopCat.Presheaf.restrictOpen TopCat.Presheaf.restrict at H ⊢
    convert congr_arg (X.presheaf.map (homOfLE _).op) H
    -- Note: the below was `simp only [← comp_apply]`
    · rw [← comp_apply, ← comp_apply]
      · simp only [← Functor.map_comp]
        rfl
      · simp only [Scheme.basicOpen_res, ge_iff_le, inf_le_right]
    · rw [map_zero]
  choose n hn using H'
  haveI := hs.to_subtype
  cases nonempty_fintype s
  use Finset.univ.sup n
  suffices ∀ i : s, X.presheaf.map (homOfLE (h₁ i)).op (f ^ Finset.univ.sup n * x) = 0 by
    subst e
    apply TopCat.Sheaf.eq_of_locally_eq X.sheaf fun i : s => (i : Opens X.carrier)
    intro i
    rw [map_zero]
    apply this
  intro i
  replace hn :=
    congr_arg (fun x => X.presheaf.map (homOfLE (h₁ i)).op (f ^ (Finset.univ.sup n - n i)) * x)
      (hn i)
  dsimp at hn
  simp only [← map_mul, ← map_pow] at hn
  rwa [mul_zero, ← mul_assoc, ← pow_add, tsub_add_cancel_of_le] at hn
  apply Finset.le_sup (Finset.mem_univ i)
#align algebraic_geometry.exists_pow_mul_eq_zero_of_res_basic_open_eq_zero_of_is_compact AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact

end AlgebraicGeometry
