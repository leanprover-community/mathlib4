/-
Copyright (c) 2026 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.SmallObject.Iteration.Nonempty
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!

# Existence of Flat extension

-/

@[expose] public section

universe w u v

open IsLocalRing CategoryTheory SmallObject Limits

open scoped Polynomial

variable (R : Type u) [CommRing R]

section instances

instance {S : Type*} [Semiring S] [Algebra R S] : IsLocalHom (AlgHom.id R S) := ⟨fun _ h ↦ h⟩

instance {S₁ S₂ S₃ : Type*} [Semiring S₁] [Semiring S₂] [Semiring S₃] [Algebra R S₁] [Algebra R S₂]
    [Algebra R S₃] (f : S₁ →ₐ[R] S₂) (g : S₂ →ₐ[R] S₃) [locf : IsLocalHom f] [locg : IsLocalHom g] :
    IsLocalHom (g.comp f) :=
  ⟨fun a ha ↦ locf.map_nonunit a (locg.map_nonunit (f a) ha)⟩

private lemma AlgHom.comp_toRingHom' {S₁ S₂ S₃ : Type*} [Semiring S₁] [Semiring S₂] [Semiring S₃]
    [Algebra R S₁] [Algebra R S₂] [Algebra R S₃] (f : S₁ →ₐ[R] S₂) (g : S₂ →ₐ[R] S₃) :
    (g.comp f) = (RingHomClass.toRingHom g).comp (RingHomClass.toRingHom f) := rfl

instance [IsLocalRing R] [Small.{w} R] : IsLocalRing (Shrink R) :=
  let := IsLocalHom.of_surjective (Shrink.ringEquiv R).symm.toRingHom
    (Shrink.ringEquiv R).symm.surjective
  IsLocalRing.of_surjective (Shrink.ringEquiv R).symm.toRingHom (Shrink.ringEquiv R).symm.surjective

lemma IsScalarTower.algebraMap_range_le (S T : Type*) [CommRing S] [Ring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    (algebraMap R T).range ≤ (algebraMap S T).range := by
  rintro x ⟨y, hy⟩
  use algebraMap R S y
  rw [← hy, IsScalarTower.algebraMap_apply R S T]

instance (J : Type w) [Preorder J] [Nonempty J] [IsDirectedOrder J] : IsFiltered J where
  cocone_objs a b := by
    obtain ⟨c, ha, hb⟩ := exists_ge_ge a b
    exact ⟨c, ha.hom, hb.hom, trivial⟩
  cocone_maps _ b _ _ := ⟨b, (le_refl b).hom, rfl⟩

instance (J : Type w) [LinearOrder J] [Nonempty J] (C : Type u) [Category.{v} C]
    [HasFilteredColimitsOfSize.{w, w} C] : HasIterationOfShape J C where
  hasColimitsOfShape_of_isSuccLimit j hj := by
    have : Nonempty (Set.Iio j) := Set.Nonempty.coe_sort (Set.Iio_nonempty.mpr hj.not_isMin)
    infer_instance

end instances

variable [IsLocalRing R] (K : Type v) [Field K] [Algebra (ResidueField R) K]

section monogenic

variable (S : Type w) [CommRing S] [IsLocalRing S] [Algebra (ResidueField S) K]

noncomputable def minpolyLift (x : K) (int : IsIntegral (ResidueField S) x) : S[X] :=
  Classical.choose (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (IsLocalRing.residue S) IsLocalRing.residue_surjective
    (minpoly (ResidueField S) x)) (minpoly.monic int))

lemma minpolyLift_spec (x : K) (int : IsIntegral (ResidueField S) x) :
    Polynomial.map (IsLocalRing.residue S) (minpolyLift K S x int) = minpoly (ResidueField S) x ∧
    (minpolyLift K S x int).natDegree = (minpoly (ResidueField S) x).natDegree
    ∧ (minpolyLift K S x int).Monic :=
    Classical.choose_spec (Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective (IsLocalRing.residue S) IsLocalRing.residue_surjective
    (minpoly (ResidueField S) x)) (minpoly.monic int))

abbrev adjoinAlgebraic (x : K) (int : IsIntegral (ResidueField S) x) : Type w :=
  S[X] ⧸ Ideal.span {minpolyLift K S x int}

instance (x : K) (int : IsIntegral (ResidueField S) x) :
    Module.Finite S (adjoinAlgebraic K S x int) :=
  (minpolyLift_spec K S x int).2.2.finite_quotient

instance (x : K) (int : IsIntegral (ResidueField S) x) :
    Module.Free S (adjoinAlgebraic K S x int) :=
  (minpolyLift_spec K S x int).2.2.free_quotient

noncomputable abbrev adjoinAlgebraicToResidueAux (x : K) :
    S[X] →+* (ResidueField S)[X] ⧸ Ideal.span {minpoly (ResidueField S) x} :=
  (Ideal.Quotient.mk (Ideal.span {(minpoly (ResidueField S) x)})).comp
    (Polynomial.mapRingHom (IsLocalRing.residue S))

lemma adjoinAlgebraicToResidueAux_ker (x : K) (int : IsIntegral (ResidueField S) x) :
    RingHom.ker (adjoinAlgebraicToResidueAux K S x) =
    Ideal.span {minpolyLift K S x int} ⊔ (maximalIdeal S).map Polynomial.C := by
  have eqmap : Ideal.span {(minpoly (ResidueField S) x)} =
    (Ideal.span {minpolyLift K S x int}).map (Polynomial.mapRingHom (IsLocalRing.residue S)) := by
    simp [Ideal.map_span, (minpolyLift_spec K S x int).1]
  rw [← RingHom.comap_ker, Ideal.mk_ker, eqmap, Ideal.comap_map_of_surjective' _
      (Polynomial.map_surjective _ residue_surjective), Polynomial.ker_mapRingHom, ker_residue]

noncomputable abbrev adjoinAlgebraicToResidue (x : K) (int : IsIntegral (ResidueField S) x) :
    (adjoinAlgebraic K S x int) →+*
    (ResidueField S)[X] ⧸ Ideal.span {minpoly (ResidueField S) x} :=
  Ideal.Quotient.lift _ (adjoinAlgebraicToResidueAux K S x) (fun _ h ↦
    (le_of_le_of_eq le_sup_left (adjoinAlgebraicToResidueAux_ker K S x int).symm) h)

lemma adjoinAlgebraicToResidue_surjective (x : K) (int : IsIntegral (ResidueField S) x) :
    Function.Surjective (adjoinAlgebraicToResidue K S x int) := by
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact (Ideal.Quotient.mk_surjective.comp (Polynomial.map_surjective _ residue_surjective))

lemma adjoinAlgebraicToResidue_ker (x : K) (int : IsIntegral (ResidueField S) x) :
    RingHom.ker (adjoinAlgebraicToResidue K S x int) =
    (maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int)) := by
  apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
  rw [RingHom.comap_ker, Ideal.Quotient.lift_comp_mk,
    adjoinAlgebraicToResidueAux_ker _ _ _ int, IsScalarTower.algebraMap_eq S S[X]]
  simp [← Ideal.map_map]

set_option backward.isDefEq.respectTransparency false in
lemma adjoinAlgebraic_maximalIdeal_map (x : K) (int : IsIntegral (ResidueField S) x) :
    ((maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int))).IsMaximal := by
  let : Fact _ := ⟨minpoly.irreducible int⟩
  let := Ideal.Quotient.field (Ideal.span {(minpoly (ResidueField S) x)})
  rw [← adjoinAlgebraicToResidue_ker K S x int]
  exact RingHom.ker_isMaximal_of_surjective _ (adjoinAlgebraicToResidue_surjective K S x int)

instance adjoinAlgebraic_isLocalRing (x : K) (int : IsIntegral (ResidueField S) x) :
    IsLocalRing (adjoinAlgebraic K S x int) := by
  have := adjoinAlgebraic_maximalIdeal_map K S x int
  apply IsLocalRing.of_unique_max_ideal
  use (maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int)), this
  intro m hm
  exact (this.eq_of_le hm.ne_top (Ideal.map_le_iff_le_comap.mpr (le_of_eq (eq_maximalIdeal
    m.isMaximal_comap_of_isIntegral_of_isMaximal).symm))).symm

lemma adjoinAlgebraic_maximalIdeal_eq_map (x : K) (int : IsIntegral (ResidueField S) x) :
    maximalIdeal (adjoinAlgebraic K S x int) =
    (maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int)) :=
  (eq_maximalIdeal (adjoinAlgebraic_maximalIdeal_map K S x int)).symm

noncomputable abbrev adjoinAlgebraicResidueFieldEquiv (x : K)
    (int : IsIntegral (ResidueField S) x) :
    ResidueField (adjoinAlgebraic K S x int) ≃+*
    (ResidueField S)[X] ⧸ Ideal.span {minpoly (ResidueField S) x} :=
  (Ideal.quotEquivOfEq ((adjoinAlgebraic_maximalIdeal_eq_map K S x int).trans
    (adjoinAlgebraicToResidue_ker K S x int).symm)).trans
  (RingHom.quotientKerEquivOfSurjective (adjoinAlgebraicToResidue_surjective K S x int))

lemma adjoinAlgebraicResidueFieldEquiv_apply_residue (x : K)
    (int : IsIntegral (ResidueField S) x) (y : adjoinAlgebraic K S x int) :
    (adjoinAlgebraicResidueFieldEquiv K S x int) (residue _ y) =
    (adjoinAlgebraicToResidue K S x int) y := rfl

lemma adjoinAlgebraic_algebraMap_isLocalHom (x : K) (int : IsIntegral (ResidueField S) x) :
    IsLocalHom (algebraMap S (adjoinAlgebraic K S x int)) :=
  ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
    (le_of_eq (adjoinAlgebraic_maximalIdeal_eq_map K S x int).symm)

noncomputable abbrev adjoinAlgebraicResidueToK (x : K) :
    (ResidueField S)[X] ⧸ Ideal.span {minpoly (ResidueField S) x} →+* K :=
  Ideal.Quotient.lift _ (Polynomial.aeval x).toRingHom (fun _ h ↦
    ((Ideal.span_singleton_le_iff_mem _).mpr (minpoly.aeval _ x) :
      _ ≤ RingHom.ker (Polynomial.aeval x).toRingHom) h)

noncomputable abbrev adjoinAlgebraicAlgebraK (x : K) (int : IsIntegral (ResidueField S) x) :
    Algebra (ResidueField (adjoinAlgebraic K S x int)) K :=
  ((adjoinAlgebraicResidueToK K S x).comp
    (adjoinAlgebraicResidueFieldEquiv K S x int).toRingHom).toAlgebra

abbrev adjoinAlgebraicIsScalarTower (x : K) (int : IsIntegral (ResidueField S) x) :
    letI := adjoinAlgebraic_algebraMap_isLocalHom K S x int
    letI := adjoinAlgebraicAlgebraK K S x int
    IsScalarTower (ResidueField S) (ResidueField (adjoinAlgebraic K S x int)) K := by
  let := adjoinAlgebraic_algebraMap_isLocalHom K S x int
  let := adjoinAlgebraicAlgebraK K S x int
  refine IsScalarTower.of_algebraMap_eq (fun z ↦ ?_)
  rcases residue_surjective z with ⟨y, hy⟩
  simp only [← hy, RingHom.algebraMap_toAlgebra, RingEquiv.toRingHom_eq_coe,
    ResidueField.algebraMap_residue, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
    adjoinAlgebraicResidueFieldEquiv_apply_residue]
  rw [IsScalarTower.algebraMap_eq S S[X]]
  simp

lemma adjoinAlgebraic_mem_range (x : K) (int : IsIntegral (ResidueField S) x) :
    letI := adjoinAlgebraicAlgebraK K S x int
    x ∈ (algebraMap (ResidueField (adjoinAlgebraic K S x int)) K).range := by
  simp only [RingHom.algebraMap_toAlgebra]
  use residue _ (Ideal.Quotient.mk _ Polynomial.X)
  simp [adjoinAlgebraicResidueFieldEquiv_apply_residue]

abbrev adjoinTranscendental : Type w :=
  Localization.AtPrime ((maximalIdeal S).map Polynomial.C)

lemma adjoinTranscendental_maximalIdeal_eq_map :
    maximalIdeal (adjoinTranscendental S) =
    (maximalIdeal S).map (algebraMap S (adjoinTranscendental S)) := by
  rw [IsScalarTower.algebraMap_eq S S[X], ← Ideal.map_map]
  exact Localization.AtPrime.map_eq_maximalIdeal.symm

instance : IsLocalHom (algebraMap S (adjoinTranscendental S)) :=
  ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
    (le_of_eq (adjoinTranscendental_maximalIdeal_eq_map S).symm)

lemma adjoinTranscendental_aeval_ker (x : K) (nint : ¬ IsIntegral (ResidueField S) x)
    [Algebra S K] [IsScalarTower S (ResidueField S) K] :
    RingHom.ker (Polynomial.aeval x) = (maximalIdeal S).map Polynomial.C := by
  have : (Polynomial.aeval x).toRingHom = (Polynomial.aeval x).toRingHom.comp
    (Polynomial.mapRingHom (IsLocalRing.residue S)) :=
    RingHom.ext (fun p ↦ (Polynomial.aeval_map_algebraMap (ResidueField S) _ _).symm)
  have inj : Function.Injective (Polynomial.aeval (R := ResidueField S) x) := by
    apply (iff_not_comm.mpr isAlgebraic_iff_not_injective).mpr
    exact isAlgebraic_iff_isIntegral.not.mpr nint
  change RingHom.ker (Polynomial.aeval x).toRingHom = _
  rw [this, RingHom.ker_comp_of_injective _ inj, Polynomial.ker_mapRingHom, ker_residue]

noncomputable abbrev adjoinTranscendentalToK (x : K) (nint : ¬ IsIntegral (ResidueField S) x)
    [Algebra S K] [IsScalarTower S (ResidueField S) K] : adjoinTranscendental S →+* K :=
  IsLocalization.lift (M := ((maximalIdeal S).map Polynomial.C).primeCompl)
    (g := (Polynomial.aeval x).toRingHom) (fun y ↦ by
      simpa [← RingHom.mem_ker, adjoinTranscendental_aeval_ker K S x nint] using
        Ideal.mem_primeCompl_iff.mp y.2)

lemma adjoinTranscendentalToK_ker (x : K) (nint : ¬ IsIntegral (ResidueField S) x)
    [Algebra S K] [IsScalarTower S (ResidueField S) K] :
    RingHom.ker (adjoinTranscendentalToK K S x nint) =
    maximalIdeal (adjoinTranscendental S) := by
  apply le_antisymm (le_maximalIdeal (RingHom.ker_ne_top _))
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
    IsLocalization.lift_comp]
  exact le_of_eq (adjoinTranscendental_aeval_ker K S x nint).symm

noncomputable abbrev adjoinTranscendentalAlgebraK (x : K) (nint : ¬ IsIntegral (ResidueField S) x)
    [Algebra S K] [IsScalarTower S (ResidueField S) K] :
    Algebra (ResidueField (adjoinTranscendental S)) K :=
  (Ideal.Quotient.lift _ (adjoinTranscendentalToK K S x nint) (fun _ h ↦
    le_of_eq (adjoinTranscendentalToK_ker K S x nint).symm h)).toAlgebra

lemma adjoinTranscendentalAlgebraK_apply_residue (x : K) (nint : ¬ IsIntegral (ResidueField S) x)
    (y : adjoinTranscendental S) [Algebra S K] [IsScalarTower S (ResidueField S) K] :
    letI := adjoinTranscendentalAlgebraK K S x nint
    algebraMap (ResidueField (adjoinTranscendental S)) K (residue _ y) =
    adjoinTranscendentalToK K S x nint y := rfl

abbrev adjoinTranscendentalIsScalarTower (x : K) (nint : ¬ IsIntegral (ResidueField S) x)
    [Algebra S K] [IsScalarTower S (ResidueField S) K] :
    letI := adjoinTranscendentalAlgebraK K S x nint
    IsScalarTower (ResidueField S) (ResidueField (adjoinTranscendental S)) K := by
  let _ := adjoinTranscendentalAlgebraK K S x nint
  refine IsScalarTower.of_algebraMap_eq (fun z ↦ ?_)
  rcases residue_surjective z with ⟨y, hy⟩
  simp only [← hy, ResidueField.algebraMap_residue, adjoinTranscendentalAlgebraK_apply_residue]
  rw [IsScalarTower.algebraMap_eq S S[X], RingHom.comp_apply, IsLocalization.lift_eq]
  simpa using (IsScalarTower.algebraMap_apply S (ResidueField S) K y).symm

lemma adjoinTranscendental_mem_range (x : K) (nint : ¬ IsIntegral (ResidueField S) x)
    [Algebra S K] [IsScalarTower S (ResidueField S) K] :
    letI := adjoinTranscendentalAlgebraK K S x nint
    x ∈ (algebraMap (ResidueField (adjoinTranscendental S)) K).range := by
  let := adjoinTranscendentalAlgebraK K S x nint
  use residue _ (algebraMap S[X] _ Polynomial.X)
  simp [adjoinTranscendentalAlgebraK_apply_residue]

end monogenic

structure FlatExtension where
  Ring : Type w
  [commRing : CommRing Ring]
  [isLocalRing : IsLocalRing Ring]
  [algebra : Algebra R Ring]
  [isLocalHom : IsLocalHom (algebraMap R Ring)]
  [algebraK : Algebra (ResidueField Ring) K]
  [isScalarTower : IsScalarTower (ResidueField R) (ResidueField Ring) K]
  [flat : Module.Flat R Ring]
  eqmap : maximalIdeal Ring = (maximalIdeal R).map (algebraMap R Ring)

namespace FlatExtension

attribute [instance] commRing algebra isLocalRing isLocalHom algebraK isScalarTower flat

noncomputable def mk' (S : Type w) [CommRing S] [Algebra R S] [Module.Flat R S]
    [IsLocalRing S] (hf : IsLocalHom (algebraMap R S)) (g : (ResidueField S) →+* K)
    (hg : g.comp (ResidueField.map (algebraMap R S)) = algebraMap (ResidueField R) K)
    (eqmap : maximalIdeal S = (maximalIdeal R).map (algebraMap R S)) : FlatExtension.{w} R K := by
  algebraize [g]
  have : IsLocalHom (algebraMap R S) := hf
  have : IsScalarTower (ResidueField R) (ResidueField S) K :=
    IsScalarTower.of_algebraMap_eq' hg.symm
  exact FlatExtension.mk S eqmap

noncomputable def mk'' (S : Type w) [CommRing S] (h_isLocalRing : IsLocalRing S)
    (f : R →+* S) (hf : IsLocalHom f) (hf_flat : f.Flat) (g : (ResidueField S) →+* K)
    (hg : g.comp (ResidueField.map f) = algebraMap (ResidueField R) K)
    (eqmap : maximalIdeal S = (maximalIdeal R).map f) : FlatExtension.{w} R K := by
  algebraize [f, g]
  have : IsLocalHom (algebraMap R S) := hf
  have : IsScalarTower (ResidueField R) (ResidueField S) K :=
    IsScalarTower.of_algebraMap_eq' hg.symm
  exact FlatExtension.mk S eqmap

noncomputable def trivial [Small.{w} R] : FlatExtension R K := by
  let e : R ≃+* Shrink.{w} R := (Shrink.ringEquiv R).symm
  let : Algebra (ResidueField (Shrink.{w} R)) K :=
    ((algebraMap (ResidueField R) K).comp
      (ResidueField.mapEquiv (Shrink.ringEquiv R)).toRingHom).toAlgebra
  let : IsScalarTower (ResidueField R) (ResidueField (Shrink.{w, u} R)) K := by
    refine IsScalarTower.of_algebraMap_eq (fun x ↦ ?_)
    rcases residue_surjective x with ⟨y, hy⟩
    simp [RingHom.algebraMap_toAlgebra, ← hy, ResidueField.map_residue, Equiv.algebraMap_def,
      Shrink.ringEquiv]
  refine ⟨Shrink.{w} R, ?_⟩
  apply (IsLocalRing.eq_maximalIdeal _).symm
  exact (Ideal.isMaximal_map_iff_of_bijective _ e.bijective).2 inferInstance

variable {R K} in
structure Hom (S₁ S₂ : FlatExtension.{w} R K) where
  algHom : S₁.Ring →ₐ[R] S₂.Ring
  [isLocalHom : IsLocalHom algHom]
  comm : (algebraMap (ResidueField S₂.Ring) K).comp (ResidueField.map algHom) =
    (algebraMap (ResidueField S₁.Ring) K)

attribute [instance] Hom.isLocalHom

variable {R K}

def Hom.id (S : FlatExtension.{w} R K) : Hom S S := ⟨AlgHom.id R S.Ring, by simp⟩

def Hom.comp {S₁ S₂ S₃ : FlatExtension.{w} R K} (f : Hom S₁ S₂) (g : Hom S₂ S₃) :
    Hom S₁ S₃ := ⟨g.algHom.comp f.algHom, by
  simp [← f.comm, ← g.comm, AlgHom.comp_toRingHom', ResidueField.map_comp, ← RingHom.comp_assoc]⟩

instance : Category.{w} (FlatExtension.{w} R K) where
  Hom S₁ S₂ := Hom S₁ S₂
  id S := Hom.id S
  comp f g := f.comp g

noncomputable abbrev adjoinAlgebraic (S : FlatExtension.{w} R K) (x : K)
    (int : IsIntegral (ResidueField S.Ring) x) : FlatExtension.{w} R K :=
  let : IsLocalHom (algebraMap R (_root_.adjoinAlgebraic K S.Ring x int)) := by
    rw [IsScalarTower.algebraMap_eq R S.Ring]
    apply RingHom.isLocalHom_comp
  let := adjoinAlgebraicAlgebraK K S.Ring x int
  let := adjoinAlgebraicIsScalarTower K S.Ring x int
  { Ring := _root_.adjoinAlgebraic K S.Ring x int
    isLocalRing := adjoinAlgebraic_isLocalRing K S.Ring x int
    isScalarTower := IsScalarTower.to₁₃₄ (ResidueField R) (ResidueField S.Ring) _ K
    flat := Module.Flat.trans R S.Ring _
    eqmap := by
      rw [adjoinAlgebraic_maximalIdeal_eq_map K S.Ring x int, IsScalarTower.algebraMap_eq R S.Ring,
        ← Ideal.map_map, S.eqmap] }

noncomputable abbrev toAdjoinAlgebraic (S : FlatExtension.{w} R K) (x : K)
    (int : IsIntegral (ResidueField S.Ring) x) : S ⟶ S.adjoinAlgebraic x int where
  algHom := IsScalarTower.toAlgHom R S.Ring _
  isLocalHom := ⟨by simp⟩
  comm :=
    let := adjoinAlgebraicAlgebraK K S.Ring x int
    let := adjoinAlgebraicIsScalarTower K S.Ring x int
    (IsScalarTower.algebraMap_eq _ _ K).symm

noncomputable abbrev adjoinTranscendental (S : FlatExtension.{w} R K) (x : K)
    (nint : ¬ IsIntegral (ResidueField S.Ring) x) : FlatExtension.{w} R K :=
  let : IsLocalHom (algebraMap R (_root_.adjoinTranscendental S.Ring)) := by
    rw [IsScalarTower.algebraMap_eq R S.Ring]
    apply RingHom.isLocalHom_comp
  let := ((algebraMap (ResidueField S.Ring) K).comp
    (algebraMap S.Ring (ResidueField S.Ring))).toAlgebra
  let : IsScalarTower S.Ring (ResidueField S.Ring) K := IsScalarTower.of_algebraMap_eq' rfl
  let := adjoinTranscendentalAlgebraK K S.Ring x nint
  let := adjoinTranscendentalIsScalarTower K S.Ring x nint
  { Ring := _root_.adjoinTranscendental S.Ring
    isScalarTower := IsScalarTower.to₁₃₄ (ResidueField R) (ResidueField S.Ring) _ K
    flat := Module.Flat.trans R S.Ring _
    eqmap := by
      rw [adjoinTranscendental_maximalIdeal_eq_map S.Ring, IsScalarTower.algebraMap_eq R S.Ring,
        ← Ideal.map_map, ← S.eqmap] }

noncomputable abbrev toAdjoinTranscendental (S : FlatExtension.{w} R K) (x : K)
    (nint : ¬ IsIntegral (ResidueField S.Ring) x) : S ⟶ S.adjoinTranscendental x nint where
  algHom := IsScalarTower.toAlgHom R S.Ring _
  isLocalHom := ⟨by simp⟩
  comm :=
    let := ((algebraMap (ResidueField S.Ring) K).comp
      (algebraMap S.Ring (ResidueField S.Ring))).toAlgebra
    let : IsScalarTower S.Ring (ResidueField S.Ring) K := IsScalarTower.of_algebraMap_eq' rfl
    let := adjoinTranscendentalAlgebraK K S.Ring x nint
    let := adjoinTranscendentalIsScalarTower K S.Ring x nint
    (IsScalarTower.algebraMap_eq _ _ K).symm

variable (R K)

open Classical in
noncomputable def SuccStruct [Small.{w} R] : SuccStruct (FlatExtension.{w} R K) where
  X₀ := trivial R K
  succ S := if surj : Function.Surjective (algebraMap (ResidueField S.Ring) K) then S else
      if int : IsIntegral (ResidueField S.Ring) (Classical.choose (Decidable.not_forall.mp surj))
        then adjoinAlgebraic S _ int
        else adjoinTranscendental S _ int
  toSucc S := if surj : Function.Surjective (algebraMap (ResidueField S.Ring) K) then by
        simpa only [surj, ↓reduceDIte] using 𝟙 S else
      if int : IsIntegral (ResidueField S.Ring) (Classical.choose (Decidable.not_forall.mp surj))
        then by simpa only [surj, int, ↓reduceDIte] using toAdjoinAlgebraic S _ int
        else by simpa only [surj, int, ↓reduceDIte] using toAdjoinTranscendental S _ int

lemma algebraMap_range_lt_of_not_surjective [Small.{w} R] (S : FlatExtension R K)
    (nsurj : ¬ Function.Surjective (algebraMap (ResidueField S.Ring) K)) :
    (algebraMap (ResidueField S.Ring) K).range <
    (algebraMap (ResidueField ((FlatExtension.SuccStruct R K).succ S).Ring) K).range := by
  classical
  by_cases int : IsIntegral (ResidueField S.Ring) (Classical.choose (Decidable.not_forall.mp nsurj))
  · have : (FlatExtension.SuccStruct R K).succ S = adjoinAlgebraic S _ int := by
      simp only [↓reduceDIte, SuccStruct, nsurj, int]
    rw [this]
    let := adjoinAlgebraicAlgebraK K S.Ring _ int
    let := adjoinAlgebraicIsScalarTower K S.Ring _ int
    exact Set.ssubset_iff_exists.mpr ⟨IsScalarTower.algebraMap_range_le _ _ _,
      Classical.choose (Decidable.not_forall.mp nsurj),
      adjoinAlgebraic_mem_range K S.Ring _ int,
      Classical.choose_spec (Decidable.not_forall.mp nsurj)⟩
  · have : (FlatExtension.SuccStruct R K).succ S = adjoinTranscendental S _ int := by
      simp only [↓reduceDIte, SuccStruct, nsurj, int]
    rw [this]
    let := ((algebraMap (ResidueField S.Ring) K).comp
      (algebraMap S.Ring (ResidueField S.Ring))).toAlgebra
    let : IsScalarTower S.Ring (ResidueField S.Ring) K := IsScalarTower.of_algebraMap_eq' rfl
    let := adjoinTranscendentalAlgebraK K S.Ring _ int
    let := adjoinTranscendentalIsScalarTower K S.Ring _ int
    exact Set.ssubset_iff_exists.mpr ⟨IsScalarTower.algebraMap_range_le _ _ _,
      Classical.choose (Decidable.not_forall.mp nsurj),
      adjoinTranscendental_mem_range K S.Ring _ int,
      Classical.choose_spec (Decidable.not_forall.mp nsurj)⟩

instance : CoeSort (FlatExtension.{w} R K) (Type w) := ⟨FlatExtension.Ring⟩

attribute [coe] FlatExtension.Ring

instance (S S' : FlatExtension R K) :
    FunLike {f : S →+* S' // f.comp (algebraMap R S) = algebraMap R S' ∧
    ∃ _ : IsLocalHom f, (algebraMap (ResidueField S') K).comp
    (ResidueField.map f) = (algebraMap (ResidueField S) K)} S S' where
  coe f := f
  coe_injective' _ _ h := Subtype.ext (RingHom.ext fun x ↦ congr($h x))

instance : ConcreteCategory (FlatExtension R K)
    fun S S' ↦ {f : S →+* S' // f.comp (algebraMap R S) = algebraMap R S' ∧
    ∃ _ : IsLocalHom f, (algebraMap (ResidueField S') K).comp
    (ResidueField.map f) = (algebraMap (ResidueField S) K)} where
  hom {S S'} f := ⟨f.algHom, by simp, ⟨isLocalHom_toRingHom f.algHom, f.comm⟩⟩
  ofHom {S S'} f := {
    algHom := ⟨f, fun r ↦ congr($(f.2.1) r)⟩
    isLocalHom := by
      obtain ⟨inst, _⟩ := f.2.2
      exact ⟨inst.map_nonunit⟩
    comm := by
      obtain ⟨_, h⟩ := f.2.2
      exact h
  }

def Hom.mk' {S₁ S₂ : FlatExtension.{w} R K} (f : S₁ →ₐ[R] S₂)
    (isl : IsLocalHom f) (comm : (algebraMap (ResidueField S₂) K).comp
      (ResidueField.map f) = (algebraMap (ResidueField S₁) K)) : S₁.Hom S₂ where
  algHom := f
  comm := comm

abbrev Hom.hom {X Y : FlatExtension.{w} R K} (f : X ⟶ Y) := ConcreteCategory.hom f

abbrev ofHom {S S' : FlatExtension.{w} R K}
    (f : {f : S →+* S' // f.comp (algebraMap R S) = algebraMap R S' ∧
    ∃ _ : IsLocalHom f, (algebraMap (ResidueField S') K).comp
    (ResidueField.map f) = (algebraMap (ResidueField S) K)}) :=
  ConcreteCategory.ofHom (X := S) f

instance : HasForget₂ (FlatExtension.{w} R K) CommRingCat.{w} where
  forget₂ := {
    obj R := CommRingCat.of R.Ring
    map f := CommRingCat.ofHom f.hom.1 }

instance : HasForget₂ (FlatExtension.{w} R K) (CommAlgCat.{w} R) where
  forget₂ := {
    obj S := CommAlgCat.of R S.Ring
    map f := CommAlgCat.ofHom f.1 }

/-
namespace FilteredColimit

variable {R K} {J : Type w} [Category.{w} J] [IsFiltered J] {F : J ⥤ FlatExtension.{w} R K}

noncomputable def coconeOfCoconeForget (c : Cocone (F ⋙ (forget₂ _ CommRingCat.{w})))
    (hc : IsColimit c) : Cocone F where
  pt := by
    apply FlatExtension.mk' R K c.pt
    all_goals sorry
  ι := {
    app j := by
      refine FlatExtension.ofHom R K ⟨(c.ι.app j).hom, ?_, ?_⟩
      all_goals sorry
    naturality j j' f := by
      ext x
      exact congr($(c.ι.naturality f) x)
  }

noncomputable def isColimit_coconeOfCoconeForget (c : Cocone (F ⋙ (forget₂ _ CommRingCat.{w})))
    (hc : IsColimit c) : IsColimit (coconeOfCoconeForget c hc) := by
  refine IsColimit.ofFaithful (forget₂ (FlatExtension.{w} R K) CommRingCat.{w}) hc
    (fun s ↦ FlatExtension.ofHom R K ⟨(hc.desc ((forget₂ _ CommRingCat.{w}).mapCocone s)).hom,
    ?_, ?_, ?_⟩) (fun s ↦ rfl)
  all_goals sorry

instance : HasColimitsOfShape J (FlatExtension.{w} R K) where
  has_colimit F := by
    obtain ⟨⟨c, hc⟩⟩ : HasColimit (F ⋙ (forget₂ _ CommRingCat.{w})) := inferInstance
    exact ⟨⟨⟨coconeOfCoconeForget c hc, isColimit_coconeOfCoconeForget c hc⟩⟩⟩

instance : HasFilteredColimitsOfSize.{w, w} (FlatExtension.{w} R K) where
  HasColimitsOfShape _ _ _ := inferInstance

end FilteredColimit
-/

namespace FilteredColimit

variable {R K} {J : Type w} [Category.{w} J] [IsFiltered J] {F : J ⥤ FlatExtension.{w} R K}

lemma isLocalRing_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) : IsLocalRing c.pt := by
  sorry

lemma isLocalHom_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) : IsLocalHom (algebraMap R c.pt) := by
  sorry

lemma flat_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) : Module.Flat R c.pt := by
  sorry

def residueFieldDescOfIsColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) :
    haveI := isLocalRing_of_isColimit c hc
    ResidueField c.pt →+* K := by
  sorry

noncomputable def coconeOfCoconeForgetPt (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) : FlatExtension R K := by
  have := isLocalRing_of_isColimit c hc
  have := flat_of_isColimit c hc
  refine FlatExtension.mk' R K c.pt (isLocalHom_of_isColimit c hc)
    (residueFieldDescOfIsColimit c hc) ?_ ?_
  · sorry
  · sorry

lemma coconeOfCoconeForgetPt_algebraMap_eq (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) :
    (algebraMap (ResidueField (coconeOfCoconeForgetPt c hc)) K) =
    residueFieldDescOfIsColimit c hc := rfl

lemma ι_isLocalHom_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) (j : J) : IsLocalHom (c.ι.app j).hom := by
  sorry

noncomputable def coconeOfCoconeForget (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) : Cocone F where
  pt := coconeOfCoconeForgetPt c hc
  ι := {
    app j := by
      refine FlatExtension.Hom.mk' R K (c.ι.app j).hom (ι_isLocalHom_of_isColimit c hc j) ?_
      change (residueFieldDescOfIsColimit c hc).comp _ = _

      sorry
    naturality j j' f := by
      ext x
      exact congr($(c.ι.naturality f) x)
  }

noncomputable def isColimit_coconeOfCoconeForget (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat.{w} R))))
    (hc : IsColimit c) : IsColimit (coconeOfCoconeForget c hc) := by
  refine IsColimit.ofFaithful (forget₂ (FlatExtension.{w} R K) (CommAlgCat.{w} R)) hc
    (fun s ↦ FlatExtension.Hom.mk' R K (hc.desc ((forget₂ _ (CommAlgCat.{w} R)).mapCocone s)).hom ?_
      ?_) (fun s ↦ rfl)
  · sorry
  · sorry

instance : HasColimitsOfShape J (FlatExtension.{w} R K) where
  has_colimit F := by
    obtain ⟨⟨c, hc⟩⟩ : HasColimit (F ⋙ (forget₂ _ (CommAlgCat.{w} R))) :=
      sorry
    exact ⟨⟨⟨coconeOfCoconeForget c hc, isColimit_coconeOfCoconeForget c hc⟩⟩⟩

instance : HasFilteredColimitsOfSize.{w, w} (FlatExtension.{w} R K) where
  HasColimitsOfShape _ _ _ := inferInstance

end FilteredColimit

end FlatExtension

set_option backward.isDefEq.respectTransparency false in
lemma exists_isLocalHom_flat : ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R')
    (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[ResidueField R] (ResidueField R')) := by
  obtain ⟨setK, ⟨e⟩⟩ : ∃ S : Type max u v, Nonempty (S ≃ Set K) := ⟨ULift (Set K), ⟨Equiv.ulift⟩⟩
  let ⟨lin, wf⟩ := exists_wellFoundedLT setK
  let : WellFoundedLT (WithTop setK) := WithTop.instWellFoundedLT
  let : SuccOrder (WithTop setK) := SuccOrder.ofLinearWellFoundedLT _
  let : OrderBot (WithTop setK) := WellFoundedLT.toOrderBot _
  obtain ⟨φ⟩ : Nonempty ((FlatExtension.SuccStruct.{max u v} R K).Iteration (⊤ : WithTop setK)) :=
    inferInstance
  let fi : WithTop setK ≃o Set.Iic (⊤ : WithTop setK) := OrderIso.IicTop.symm
  let φobj := fun i ↦ (algebraMap (ResidueField ((φ.F.obj (fi i)).Ring)) K).range
  let φtop := φ.F.obj (fi ⊤)
  suffices h : (algebraMap (ResidueField φtop.Ring) K).range = ⊤ by
    let f := algebraMap (ResidueField φtop.Ring) K
    have : Function.Bijective f := ⟨RingHom.injective f, RingHom.range_eq_top.mp h⟩
    let f := RingEquiv.ofBijective f this
    refine ⟨φtop.Ring, φtop.commRing, φtop.isLocalRing, φtop.algebra, φtop.isLocalHom, φtop.flat,
      φtop.eqmap, ⟨AlgEquiv.ofRingEquiv (f := f.symm) fun x ↦ f.injective ?_⟩⟩
    · simp only [RingEquiv.apply_symm_apply]
      exact IsScalarTower.algebraMap_apply (ResidueField R) (ResidueField φtop.Ring) K x
  have mono : Monotone φobj := fun a b hab ↦ by
    let mapab := φ.F.map (homOfLE (fi.monotone hab))
    rintro _ ⟨x, rfl⟩
    exact ⟨ResidueField.map mapab.algHom x, congr($mapab.comm x)⟩
  by_contra hne
  have hlt : ∀ i, i < ⊤ → ∃ u, u ∈ φobj (Order.succ i) ∧ ¬ u ∈ φobj i := by
    rintro i h
    have := FlatExtension.algebraMap_range_lt_of_not_surjective R K (φ.F.obj (fi i)) <|
      fun H ↦ hne (eq_top_iff.mpr (le_of_eq_of_le (RingHom.range_eq_top.mpr H).symm (mono le_top)))
    obtain ⟨x, hx⟩ := Set.exists_of_ssubset this
    have : φ.F.obj (fi (Order.succ i)) = (FlatExtension.SuccStruct R K).succ (φ.F.obj (fi i)) := by
      rw [← φ.obj_succ]
      · rfl
      · exact h
    unfold φobj
    exact ⟨x, this ▸ hx⟩
  let uh := fun i : setK ↦ hlt (fi i) (WithTop.coe_lt_top _)
  let u : setK → K := fun i ↦ Classical.choose (uh i)
  have hu : Function.Injective u := by
    refine Function.Injective.of_lt_imp_ne fun x y hxy heq ↦ ?_
    absurd (Classical.choose_spec (uh x)).1
    change u x ∉ _
    rw [heq]
    refine fun h ↦ (Classical.choose_spec (uh y)).2 ((mono ?_) h)
    exact Order.succ_le_of_lt <| Subtype.mk_lt_mk.mpr (WithTop.coe_lt_coe.mpr hxy)
  absurd Cardinal.lift_mk_le_lift_mk_of_injective (hu.comp e.symm.injective)
  simpa using Cardinal.cantor (Cardinal.mk K)
