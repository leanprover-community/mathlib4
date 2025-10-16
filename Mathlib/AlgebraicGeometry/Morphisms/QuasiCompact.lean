/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.Topology.Spectral.Hom
import Mathlib.AlgebraicGeometry.Limits

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasiCompact_iff_forall_isAffineOpen`).

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
  isCompact_preimage : ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U)

variable {f} in
theorem quasiCompact_iff_isSpectralMap : QuasiCompact f ↔ IsSpectralMap f :=
  ⟨fun ⟨h⟩ => ⟨by fun_prop, h⟩, fun h => ⟨h.2⟩⟩

theorem Scheme.Hom.isSpectralMap [QuasiCompact f] : IsSpectralMap f := by
  rwa [← quasiCompact_iff_isSpectralMap]

@[deprecated (since := "2025-10-07")]
alias quasiCompact_iff_spectral := quasiCompact_iff_isSpectralMap

instance (priority := 900) quasiCompact_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := by
  constructor
  intro U _ hU'
  convert hU'.image (inv f.base).hom.continuous_toFun using 1
  rw [Set.image_eq_preimage_of_inverse]
  · delta Function.LeftInverse
    exact IsIso.inv_hom_id_apply f.base
  · exact IsIso.hom_inv_id_apply f.base

instance quasiCompact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    [QuasiCompact g] : QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  apply QuasiCompact.isCompact_preimage
  · exact Continuous.isOpen_preimage (by fun_prop) _ hU
  apply QuasiCompact.isCompact_preimage <;> assumption

theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set X.affineOpens, s.Finite ∧ U = ⋃ i ∈ s, i := by
  apply Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    (fun (U : X.affineOpens) => (U : X.Opens))
  · rw [Subtype.range_coe]; exact X.isBasis_affineOpens
  · exact fun i => i.2.isCompact

@[deprecated (since := "2025-10-14")]
alias isCompactOpen_iff_eq_finset_affine_union :=
  isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens

theorem isCompact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} :
    IsCompact (X := X) U ↔ ∃ s : Set X.affineOpens, s.Finite ∧ U = ⨆ i ∈ s, (i : X.Opens) := by
  convert isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (U := U.1) using 4 with s
  · simp [U.isOpen]
  · convert SetLike.coe_injective.eq_iff.symm; simp

theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen [IsAffine X] {U : Set X} :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set Γ(X, ⊤), s.Finite ∧ U = ⋃ i ∈ s, X.basicOpen i :=
  (isBasis_basicOpen X).isCompact_open_iff_eq_finite_iUnion _
    (fun _ => ((isAffineOpen_top _).basicOpen _).isCompact) _

@[deprecated (since := "2025-10-14")]
alias isCompactOpen_iff_eq_basicOpen_union :=
  isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen

variable {f} in
theorem quasiCompact_iff_forall_isAffineOpen :
    QuasiCompact f ↔ ∀ U : Y.Opens, IsAffineOpen U → IsCompact (f ⁻¹ᵁ U : Set X) := by
  rw [quasiCompact_iff]
  refine ⟨fun H U hU => H U U.isOpen hU.isCompact, ?_⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU', hU⟩
  simp only [Set.preimage_iUnion]
  exact Set.Finite.isCompact_biUnion hS (fun i _ => H i i.prop)

@[deprecated (since := "2025-10-14")]
alias quasiCompact_iff_forall_affine := quasiCompact_iff_forall_isAffineOpen

theorem isCompact_basicOpen (X : Scheme) {U : X.Opens} (hU : IsCompact (U : Set X))
    (f : Γ(X, U)) : IsCompact (X.basicOpen f : Set X) := by
  classical
  refine isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ?_
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  let g : s → X.affineOpens := fun V ↦ ⟨V.1 ⊓ X.basicOpen f, by
    rw [← X.basicOpen_res _ (homOfLE ((le_iSup₂ V.1 V.2).trans_eq e.symm)).op]
    exact V.1.2.basicOpen _⟩
  haveI : Finite s := hs.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  rw [iSup_range, ← iSup_inf_eq, iSup_subtype, ← e, inf_eq_right.mpr (X.basicOpen_le f)]

instance : HasAffineProperty @QuasiCompact (fun X _ _ _ ↦ CompactSpace X) where
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [quasiCompact_iff_forall_isAffineOpen, isCompact_iff_compactSpace,
      targetAffineLocally, Subtype.forall]
    rfl
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
      exacts [@Homeomorph.compactSpace _ _ _ _ H (TopCat.homeoOfIso (asIso e.inv.base)), H]
    · introv _ H
      rw [Scheme.preimage_basicOpen f r]
      exact (isCompact_iff_compactSpace.mp (isCompact_basicOpen _ isCompact_univ _))
    · rintro X Y H f S hS hS'
      rw [← (isAffineOpen_top _).iSup_basicOpen_eq_self_iff] at hS
      rw [← isCompact_univ_iff, ← Opens.coe_top, ← f.preimage_top, ← hS, Scheme.Hom.preimage_iSup,
        Opens.iSup_mk, Opens.coe_mk]
      exact isCompact_iUnion fun i => isCompact_iff_compactSpace.mpr (hS' i)

theorem quasiCompact_over_affine_iff {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] :
    QuasiCompact f ↔ CompactSpace X := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

theorem compactSpace_iff_quasiCompact (X : Scheme) :
    CompactSpace X ↔ QuasiCompact (terminal.from X) := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

lemma QuasiCompact.compactSpace_of_compactSpace {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [CompactSpace Y] : CompactSpace X := by
  constructor
  rw [← Set.preimage_univ (f := f)]
  exact QuasiCompact.isCompact_preimage _ isOpen_univ CompactSpace.isCompact_univ

instance quasiCompact_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiCompact where
  comp_mem _ _ _ _ := inferInstance

instance quasiCompact_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiCompact := by
  letI := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  apply HasAffineProperty.isStableUnderBaseChange
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g h
  let 𝒰 := Scheme.Pullback.openCoverOfRight Y.affineCover.finiteSubcover f g
  have : Finite 𝒰.I₀ := by dsimp [𝒰]; infer_instance
  have : ∀ i, CompactSpace (𝒰.X i) := by intro i; dsimp [𝒰]; infer_instance
  exact 𝒰.compactSpace

variable {Z : Scheme.{u}}

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] : QuasiCompact (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] : QuasiCompact (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

lemma compactSpace_iff_exists :
    CompactSpace X ↔ ∃ R, ∃ f : Spec R ⟶ X, Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun ⟨R, f, hf⟩ ↦ ⟨hf.range_eq ▸ isCompact_range f.continuous⟩⟩
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  refine ⟨Γ(∐ 𝒰.X, ⊤), (∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f, ?_⟩
  refine Function.Surjective.comp (g := Sigma.desc 𝒰.f)
    (fun x ↦ ?_) (∐ 𝒰.X).isoSpec.inv.surjective
  obtain ⟨y, hy⟩ := 𝒰.covers x
  exact ⟨Sigma.ι 𝒰.X (𝒰.idx x) y, by rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, hy]⟩

lemma isCompact_iff_exists {U : X.Opens} :
    IsCompact (U : Set X) ↔ ∃ R, ∃ f : Spec R ⟶ X, Set.range f = U := by
  refine isCompact_iff_compactSpace.trans ((compactSpace_iff_exists (X := U)).trans ?_)
  refine ⟨fun ⟨R, f, hf⟩ ↦ ⟨R, f ≫ U.ι, by simp [hf.range_comp]⟩, fun ⟨R, f, hf⟩ ↦ ?_⟩
  refine ⟨R, IsOpenImmersion.lift U.ι f (by simp [hf]), ?_⟩
  rw [← Set.range_eq_univ]
  apply show Function.Injective (U.ι '' ·) from Set.image_val_injective
  simp only [Set.image_univ, Scheme.Opens.range_ι]
  rwa [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsOpenImmersion.lift_fac]

@[stacks 01K9]
lemma isClosedMap_iff_specializingMap (f : X ⟶ Y) [QuasiCompact f] :
    IsClosedMap f ↔ SpecializingMap f := by
  refine ⟨fun h ↦ h.specializingMap, fun H ↦ ?_⟩
  wlog hY : ∃ R, Y = Spec R
  · change topologically @IsClosedMap f
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically @IsClosedMap) Y.affineCover]
    intro i
    have _ : QuasiCompact (Y.affineCover.pullbackHom f i) := MorphismProperty.pullback_snd _ _ ‹_›
    refine this (Y.affineCover.pullbackHom f i) ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback
      (P := topologically @SpecializingMap) (.of_hasPullback _ _) H
  obtain ⟨S, rfl⟩ := hY
  clear * - H
  intro Z hZ
  replace H := hZ.stableUnderSpecialization.image H
  wlog hX : ∃ R, X = Spec R
  · obtain ⟨R, g, hg⟩ :=
      compactSpace_iff_exists.mp ((quasiCompact_over_affine_iff f).mp inferInstance)
    have inst : QuasiCompact (g ≫ f) := HasAffineProperty.iff_of_isAffine.mpr (by infer_instance)
    have := this _ (g ≫ f) (g ⁻¹' Z) (hZ.preimage g.continuous)
    simp_rw [Scheme.Hom.comp_base, TopCat.comp_app, ← Set.image_image,
      Set.image_preimage_eq _ hg] at this
    exact this H ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.homEquiv.symm.surjective f
  exact PrimeSpectrum.isClosed_image_of_stableUnderSpecialization φ.hom Z hZ H

@[elab_as_elim]
theorem compact_open_induction_on {P : X.Opens → Prop} (S : X.Opens)
    (hS : IsCompact (S : Set X)) (h₁ : P ⊥)
    (h₂ : ∀ (S : X.Opens) (_ : IsCompact S.1) (U : X.affineOpens), P S → P (S ⊔ U)) :
    P S := by
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hS
  refine hs.induction_on _ (by simpa using h₁) fun {x s} _ hs h₄ ↦ ?_
  rw [iSup_insert, sup_comm]
  exact h₂ _ (isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨s, hs, by simp⟩) x h₄

theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen (X : Scheme)
    {U : X.Opens} (hU : IsAffineOpen U) (x f : Γ(X, U))
    (H : x |_ (X.basicOpen f) = 0) :
    ∃ n : ℕ, f ^ n * x = 0 := by
  rw [← map_zero (X.presheaf.map (homOfLE <| X.basicOpen_le f : X.basicOpen f ⟶ U).op).hom] at H
  obtain ⟨n, e⟩ := (hU.isLocalization_basicOpen f).exists_of_eq _ H
  exact ⟨n, by simpa [mul_comm x] using e⟩

/-- If `x : Γ(X, U)` is zero on `D(f)` for some `f : Γ(X, U)`, and `U` is quasi-compact, then
`f ^ n * x = 0` for some `n`. -/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme.{u})
    {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U))
    (H : x |_ (X.basicOpen f) = 0) :
    ∃ n : ℕ, f ^ n * x = 0 := by
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1; simpa using e
  have h₁ (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun (i : s) => (i : Opens (X.toPresheafedSpace))) _
  have H' := fun i : s =>
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X i.1.2
      (X.presheaf.map (homOfLE (h₁ i)).op x) (X.presheaf.map (homOfLE (h₁ i)).op f) ?_
  swap
  · change (X.presheaf.map (homOfLE _).op) ((X.presheaf.map (homOfLE _).op).hom x) = 0
    have H : (X.presheaf.map (homOfLE _).op) x = 0 := H
    convert congr_arg (X.presheaf.map (homOfLE _).op).hom H
    · simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
      · rfl
    · rw [map_zero]
    · simp only [Scheme.basicOpen_res, inf_le_right]
  choose n hn using H'
  haveI := hs.to_subtype
  cases nonempty_fintype s
  use Finset.univ.sup n
  suffices ∀ i : s, X.presheaf.map (homOfLE (h₁ i)).op (f ^ Finset.univ.sup n * x) = 0 by
    subst e
    apply TopCat.Sheaf.eq_of_locally_eq X.sheaf fun i : s => (i : X.Opens)
    intro i
    change _ = (X.sheaf.val.map _) 0
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

/-- A section over a compact open of a scheme is nilpotent if and only if its associated
basic open is empty. -/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact {X : Scheme.{u}}
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ := by
  refine ⟨X.basicOpen_eq_bot_of_isNilpotent U f, fun hf ↦ ?_⟩
  have h : (1 : Γ(X, U)) |_ (X.basicOpen f) = 0 := by
    have e : X.basicOpen f ≤ ⊥ := by rw [hf]
    rw [← TopCat.Presheaf.restrict_restrict e bot_le]
    rw [Subsingleton.eq_zero (1 |_ ⊥)]
    change X.presheaf.map _ 0 = 0
    rw [map_zero]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU 1 f h
  rw [mul_one] at hn
  use n

/-- A global section of a quasi-compact scheme is nilpotent if and only if its associated
basic open is empty. -/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot {X : Scheme.{u}}
    [CompactSpace X] (f : Γ(X, ⊤)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ :=
  isNilpotent_iff_basicOpen_eq_bot_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) f

/-- The zero locus of a set of sections over a compact open of a scheme is `X` if and only if
`s` is contained in the nilradical of `Γ(X, U)`. -/
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact {X : Scheme.{u}} {U : X.Opens}
    (hU : IsCompact (U : Set X)) (s : Set Γ(X, U)) :
    X.zeroLocus s = Set.univ ↔ s ⊆ nilradical Γ(X, U) := by
  simp [Scheme.zeroLocus_def, ← Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU,
    ← mem_nilradical, Set.subset_def]

/-- The zero locus of a set of sections over a compact open of a scheme is `X` if and only if
`s` is contained in the nilradical of `Γ(X, U)`. -/
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical {X : Scheme.{u}}
    [CompactSpace X] (s : Set Γ(X, ⊤)) :
    X.zeroLocus s = Set.univ ↔ s ⊆ nilradical Γ(X, ⊤) :=
  zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) s

@[deprecated (since := "2025-04-05")]
alias Scheme.zeroLocus_eq_top_iff_subset_nilradical_of_isCompact :=
  Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact

@[deprecated (since := "2025-04-05")]
alias Scheme.zeroLocus_eq_top_iff_subset_nilradical :=
  Scheme.zeroLocus_eq_univ_iff_subset_nilradical

end AlgebraicGeometry
