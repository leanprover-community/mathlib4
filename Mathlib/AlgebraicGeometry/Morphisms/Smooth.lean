/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Smooth.Field

/-!

# Smooth morphisms

In this file we define smooth morphisms. The main definitions are:

- `AlgebraicGeometry.Smooth`: A morphism of schemes `f : X ⟶ Y` is smooth if for each affine `U ⊆ Y`
  and `V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is smooth.

- `AlgebraicGeometry.SmoothOfRelativeDimension`: A morphism of schemes `f : X ⟶ Y` is smooth of
  relative dimension `n` if for each `x : X` there exists an affine open neighborhood `V` of `x`
  and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced
  map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth (of relative dimension `n`).

## Main results

- `AlgebraicGeometry.Smooth.iff_forall_exists_isStandardSmooth`: A morphism of schemes is smooth
  if and only if for each `x : X` there exists an affine open neighborhood `V` of `x`
  and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced
  map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry" in
June 2024.

-/

@[expose] public section

noncomputable section

open CategoryTheory Limits

universe t w v u

namespace AlgebraicGeometry

open RingHom

variable (n m : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is smooth if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is smooth. -/
@[mk_iff]
class Smooth (f : X ⟶ Y) : Prop where
  smooth_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Smooth

alias Scheme.Hom.smooth_appLE := Smooth.smooth_appLE

@[deprecated (since := "2026-02-09")] alias IsSmooth := Smooth

/-- The property of scheme morphisms `Smooth` is associated with the ring
homomorphism property `Smooth`. -/
instance : HasRingHomProperty @Smooth RingHom.Smooth where
  isLocal_ringHomProperty := RingHom.Smooth.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [smooth_iff, affineLocally_iff_forall_isAffineOpen]

/--
A morphism of schemes is smooth if and only if for each `x : X` there exists an affine open
neighborhood `V` of `x` and an affine open neighborhood `U` of `f.base x` with `V ≤ f ⁻¹ᵁ U`
such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is standard smooth.
-/
lemma Smooth.iff_forall_exists_isStandardSmooth (f : X ⟶ Y) :
    Smooth f ↔
      ∀ (x : X), ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
        (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmooth := by
  have : HasRingHomProperty @Smooth.{u} (Locally IsStandardSmooth) := by
    convert (inferInstanceAs <| HasRingHomProperty @Smooth.{u} RingHom.Smooth)
    ext f
    rw [RingHom.smooth_iff_locally_isStandardSmooth]
  rw [HasRingHomProperty.iff_exists_appLE_locally (P := @Smooth)]
  · congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]
  · exact isStandardSmooth_stableUnderCompositionWithLocalizationAway.left
  · exact isStandardSmooth_respectsIso

lemma Smooth.exists_isStandardSmooth (f : X ⟶ Y) [Smooth f] (x : X) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V)
        (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.IsStandardSmooth :=
  (iff_forall_exists_isStandardSmooth f).mp ‹_› x

/-- Being smooth is stable under composition. -/
instance : MorphismProperty.IsStableUnderComposition @Smooth :=
  HasRingHomProperty.stableUnderComposition Smooth.stableUnderComposition

/-- The composition of smooth morphisms is smooth. -/
instance smooth_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Smooth f] [Smooth g] :
    Smooth (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Smooth f› ‹Smooth g›

instance (priority := low) [Smooth f] : Flat f where
  flat_appLE {_} hU {_} hV e := (f.smooth_appLE hU hV e).flat

/-- Smooth is stable under base change. -/
instance smooth_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Smooth :=
  HasRingHomProperty.isStableUnderBaseChange Smooth.isStableUnderBaseChange

instance : MorphismProperty.Respects @Smooth @IsOpenImmersion :=
  HasRingHomProperty.respects_isOpenImmersion
    (RingHom.Smooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.Smooth.holdsForLocalizationAway).1

@[deprecated (since := "2026-02-09")]
alias isSmooth_isStableUnderBaseChange := smooth_isStableUnderBaseChange

/--
A morphism of schemes `f : X ⟶ Y` is smooth of relative dimension `n` if for each `x : X` there
exists an affine open neighborhood `V` of `x` and an affine open neighborhood `U` of
`f.base x` with `V ≤ f ⁻¹ᵁ U` such that the induced map `Γ(Y, U) ⟶ Γ(X, V)` is
standard smooth of relative dimension `n`.
-/
@[mk_iff]
class SmoothOfRelativeDimension : Prop where
  exists_isStandardSmoothOfRelativeDimension : ∀ (x : X), ∃ (U : Y.Opens) (_ : IsAffineOpen U)
    (V : X.Opens) (_ : IsAffineOpen V) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
    IsStandardSmoothOfRelativeDimension n (f.appLE U V e).hom

@[deprecated (since := "2026-02-09")] alias IsSmoothOfRelativeDimension := SmoothOfRelativeDimension

/-- If `f` is smooth of any relative dimension, it is smooth. -/
lemma SmoothOfRelativeDimension.smooth [SmoothOfRelativeDimension n f] : Smooth f := by
  rw [Smooth.iff_forall_exists_isStandardSmooth]
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  exact ⟨U, hU, V, hV, hx, e, hf.isStandardSmooth⟩

@[deprecated (since := "2026-02-09")]
alias IsSmoothOfRelativeDimension.isSmooth := SmoothOfRelativeDimension.smooth

/-- The property of scheme morphisms `SmoothOfRelativeDimension n` is associated with the ring
homomorphism property `Locally (IsStandardSmoothOfRelativeDimension n)`. -/
instance : HasRingHomProperty (@SmoothOfRelativeDimension n)
    (Locally (IsStandardSmoothOfRelativeDimension n)) := by
  apply HasRingHomProperty.locally_of_iff
  · exact (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
  · exact isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n
  · intro X Y f
    rw [smoothOfRelativeDimension_iff]
    congr!
    simp [Subtype.exists]
    grind [Scheme.affineOpens]

/-- Smooth of relative dimension `n` is stable under base change. -/
lemma smoothOfRelativeDimension_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension n) :=
  HasRingHomProperty.isStableUnderBaseChange <| locally_isStableUnderBaseChange
    isStandardSmoothOfRelativeDimension_respectsIso
    (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n)

@[deprecated (since := "2026-02-09")]
alias isSmoothOfRelativeDimension_isStableUnderBaseChange :=
  smoothOfRelativeDimension_isStableUnderBaseChange

/-- Open immersions are smooth of relative dimension `0`. -/
instance (priority := 900) [IsOpenImmersion f] : SmoothOfRelativeDimension 0 f :=
  HasRingHomProperty.of_isOpenImmersion
    (locally_holdsForLocalizationAway <|
      isStandardSmoothOfRelativeDimension_holdsForLocalizationAway).containsIdentities

/-- Open immersions are smooth. -/
instance (priority := 900) [IsOpenImmersion f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 0 f

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth g] :
    Smooth (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Smooth f] :
    Smooth (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [Smooth f] : Smooth (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Smooth f] :
    Smooth (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

/-- If `f` is smooth of relative dimension `n` and `g` is smooth of relative dimension
`m`, then `f ≫ g` is smooth of relative dimension `n + m`. -/
instance smoothOfRelativeDimension_comp {Z : Scheme.{u}} (g : Y ⟶ Z)
    [hf : SmoothOfRelativeDimension n f] [hg : SmoothOfRelativeDimension m g] :
    SmoothOfRelativeDimension (n + m) (f ≫ g) where
  exists_isStandardSmoothOfRelativeDimension x := by
    obtain ⟨U₂, hU₂, V₂, hV₂, hfx₂, e₂, hf₂⟩ := hg.exists_isStandardSmoothOfRelativeDimension (f x)
    obtain ⟨U₁', hU₁', V₁', hV₁', hx₁', e₁', hf₁'⟩ :=
      hf.exists_isStandardSmoothOfRelativeDimension x
    obtain ⟨r, s, hx₁, e₁, hf₁⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine
      (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).right
      (isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      x ⟨V₂, hV₂⟩ ⟨U₁', hU₁'⟩ ⟨V₁', hV₁'⟩ ⟨V₁', hV₁'⟩ hx₁' hx₁' e₁' hf₁' hfx₂
    have e : X.basicOpen s ≤ (f ≫ g) ⁻¹ᵁ U₂ :=
      le_trans e₁ <| f.preimage_mono <| le_trans (Y.basicOpen_le r) e₂
    have heq : (f ≫ g).appLE U₂ (X.basicOpen s) e = g.appLE U₂ V₂ e₂ ≫
        CommRingCat.ofHom (algebraMap Γ(Y, V₂) Γ(Y, Y.basicOpen r)) ≫
          f.appLE (Y.basicOpen r) (X.basicOpen s) e₁ := by
      rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom,
        g.appLE_map_assoc, Scheme.Hom.appLE_comp_appLE]
    refine ⟨U₂, hU₂, X.basicOpen s, hV₁'.basicOpen s, hx₁, e, heq ▸ ?_⟩
    apply IsStandardSmoothOfRelativeDimension.comp ?_ hf₂
    haveI : IsLocalization.Away r Γ(Y, Y.basicOpen r) := hV₂.isLocalization_basicOpen r
    exact (isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).left
      _ r _ hf₁

instance {Z : Scheme.{u}} (g : Y ⟶ Z) [SmoothOfRelativeDimension 0 f]
    [SmoothOfRelativeDimension 0 g] :
    SmoothOfRelativeDimension 0 (f ≫ g) :=
  inferInstanceAs <| SmoothOfRelativeDimension (0 + 0) (f ≫ g)

/-- Smooth of relative dimension `0` is multiplicative. -/
instance : MorphismProperty.IsMultiplicative (@SmoothOfRelativeDimension 0) where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance

/-- Smooth morphisms are locally of finite presentation. -/
instance (priority := 100) [hf : Smooth f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
  rw [HasRingHomProperty.eq_affineLocally @Smooth] at hf
  exact affineLocally_le (fun hf ↦ hf.finitePresentation) f hf

lemma formallySmooth_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens)
      (hU : IsAffineOpen U) (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
      (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallySmooth ↔
      hV.primeIdealOf ⟨x, hx⟩ ∈ Algebra.smoothLocus Γ(Y, U) Γ(X, V) := by
  letI := (f.appLE U V hVU).hom.toAlgebra
  have : (hV.primeIdealOf ⟨x, hx⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  trans Algebra.FormallySmooth
    (Localization.AtPrime (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal)
    (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
  · rw [← formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

set_option backward.isDefEq.respectTransparency false in
lemma exists_smooth_of_formallySmooth_stalk
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallySmooth) :
    ∃ (U : Y.Opens) (_ : IsAffineOpen U) (V : X.Opens) (_ : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U),
      x ∈ V ∧ (f.appLE U V hVU).hom.Smooth := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsSmoothAt _ _ := (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.IsSmoothAt.exists_notMem_smooth Γ(Y, U)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  refine ⟨_, hU, _, hV.basicOpen r, (X.basicOpen_le r).trans hVU, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have := hV.isLocalization_basicOpen r
    rw [← RingHom.smooth_algebraMap] at hr
    convert RingHom.Smooth.propertyIsLocal.respectsIso.1 _
      (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
    ext
    dsimp
    simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
      IsLocalization.map_eq]
    simp only [algebraMap_toAlgebra, RingHomCompTriple.comp_apply, ← ConcreteCategory.comp_apply,
      Scheme.Hom.appLE_map]

lemma Scheme.Hom.isOpen_smoothLocus [LocallyOfFinitePresentation f] :
    IsOpen { x | (f.stalkMap x).hom.FormallySmooth } := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ := exists_smooth_of_formallySmooth_stalk f x hx
  algebraize [(f.appLE U V hVU).hom]
  exact ⟨V, fun y hy ↦ (formallySmooth_stalkMap_iff U hU V hV hVU hy).mpr
    (inferInstanceAs (Algebra.IsSmoothAt _ _)), V.2, hxV⟩

/-- The set of points smooth over a base, as a `Scheme.Opens`. -/
def Scheme.Hom.smoothLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] : X.Opens :=
  ⟨{ x | (f.stalkMap x).hom.FormallySmooth }, f.isOpen_smoothLocus⟩

lemma Scheme.Hom.mem_smoothLocus {f : X ⟶ Y} [LocallyOfFinitePresentation f] {x : X} :
    x ∈ f.smoothLocus ↔ (f.stalkMap x).hom.FormallySmooth := .rfl

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Hom.smoothLocus_eq_top (f : X ⟶ Y) [Smooth f] :
    f.smoothLocus = ⊤ := by
  rw [← top_le_iff]
  rintro x -
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  rw [Scheme.Hom.mem_smoothLocus, formallySmooth_stalkMap_iff U hU V hV hVU hxV]
  exact inferInstanceAs (Algebra.IsSmoothAt _ _)

lemma Scheme.Hom.smoothLocus_eq_top_iff {f : X ⟶ Y} [LocallyOfFinitePresentation f] :
    f.smoothLocus = ⊤ ↔ Smooth f := by
  refine ⟨fun H ↦ ?_, fun _ ↦ f.smoothLocus_eq_top⟩
  refine IsZariskiLocalAtSource.iff_exists_resLE.mpr fun x ↦ ?_
  obtain ⟨U, hU, V, hV, hVU, hxV, H⟩ :=
    exists_smooth_of_formallySmooth_stalk f _ (H.ge (Set.mem_univ x))
  refine ⟨U, V, hxV, hVU, ?_⟩
  have : IsAffine _ := hU
  have : IsAffine _ := hV
  rw [HasRingHomProperty.iff_of_isAffine (P := @Smooth)]
  exact (RingHom.Smooth.propertyIsLocal.respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V hVU)).mpr H

lemma Scheme.Hom.preimage_smoothLocus_eq {U : Scheme.{u}}
    (f : U ⟶ X) (g : X ⟶ Y) [IsOpenImmersion f] [LocallyOfFinitePresentation g] :
    f ⁻¹ᵁ g.smoothLocus = (f ≫ g).smoothLocus := by
  ext x
  refine (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ (f.stalkMap x)).symm.trans ?_
  rw [← CommRingCat.hom_comp, ← stalkMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField
    {K : Type u} [Field K] [PerfectField K] [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] : genericPoint X ∈ f.smoothLocus := by
  have := LocallyOfFiniteType.stalkMap f (genericPoint X)
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(f.stalkMap (genericPoint X)).hom]
  let K' := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X))
  let e : K ≃ₐ[K] K' := IsLocalization.atUnits _ (f (genericPoint X)).asIdeal.primeCompl
      (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic K K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField K)).toField
  let : Field ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) := this
  have : PerfectField ((Spec (.of K)).presheaf.stalk (f (genericPoint X))) :=
    Algebra.IsAlgebraic.perfectField (K := K)
      (L := (Spec.structureSheaf K).presheaf.stalk (f (genericPoint X)))
  exact Algebra.FormallySmooth.of_perfectField

instance {X : Scheme} [IsReduced X] (U : X.Opens) : IsReduced U :=
  isReduced_of_isOpenImmersion U.ι


lemma Scheme.Hom.dense_smoothLocus_of_perfectField
    {K : Type u} [Field K] [PerfectField K] [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] : Dense (f.smoothLocus : Set X) := by
  wlog H : CompactSpace X generalizing X
  · rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨_, ⟨U : X.Opens, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have := this (U.ι ≫ f) (isCompact_iff_compactSpace.mp hU.isCompact) ⟨x, hxU⟩
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.coe_preimage,
      ← U.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage U.ι.continuous,
      Set.mem_preimage, U.ι_apply] at this
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  let U : X.Opens :=
    ⟨(⋃₀ (irreducibleComponents X \ {irreducibleComponent x}))ᶜ, by
      rw [Set.sUnion_eq_biUnion, isOpen_compl_iff]
      exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.diff.isClosed_biUnion
        fun W hW ↦ isClosed_of_mem_irreducibleComponents W hW.1⟩
  have hU : closure U = irreducibleComponent x :=
    closure_sUnion_irreducibleComponents_diff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
      _ (irreducibleComponent_mem_irreducibleComponents x)
  have : AlgebraicGeometry.IsIntegral U :=
    have : IrreducibleSpace U := isIrreducible_iff_irreducibleSpace.mp
      (isIrreducible_iff_closure.mp (hU ▸ isIrreducible_irreducibleComponent))
    isIntegral_of_irreducibleSpace_of_isReduced _
  have : U.ι (genericPoint U) ∈ f.smoothLocus := by
    have := (U.ι ≫ f).genericPoint_mem_smoothLocus_of_perfectField
    rwa [← preimage_smoothLocus_eq, Scheme.Hom.mem_preimage] at this
  exact (((genericPoint_spec U).image U.ι.continuous).specializes (y := x)
    (by rw [Set.image_univ, U.range_ι, hU]; exact mem_irreducibleComponent)).mem_closed
    isClosed_closure (subset_closure this)

end AlgebraicGeometry
