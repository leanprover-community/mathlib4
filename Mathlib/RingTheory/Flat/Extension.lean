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
public import Mathlib.CategoryTheory.ObjectProperty.Ind
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

instance [IsLocalRing R] [Small R] : IsLocalRing (Shrink R) :=
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

theorem isLocalHom_of_toRingHom {R S : Type*} [Semiring R] [Semiring S]
    {F : Type*} [FunLike F R S] [RingHomClass F R S] (f : F) [inst : IsLocalHom (f : R →+* S)] :
  IsLocalHom f := ⟨inst.map_nonunit⟩

instance : PreservesFilteredColimits (forget₂ (CommAlgCat.{u} R) CommRingCat) := sorry

end instances

section from_proetale

open CategoryTheory Limits IsLocalRing

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) {c : Cocone F}
  [h_obj : ∀ (j : J), IsLocalRing (F.obj j)]
  [h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom]

namespace CommRingCat.FilteredColimit

omit h_obj in
lemma isLocalHom_ι (hc : IsColimit c) (j : J) : IsLocalHom (c.ι.app j).hom := by sorry

theorem isLocalRing_of_isColimit (hc : IsColimit c) : IsLocalRing c.pt := by sorry

lemma maximalIdeal_eq_iUnion_of_isColimit (hc : IsColimit c) :
    (isLocalRing_of_isColimit F hc).maximalIdeal =
    ⋃ (j : J), ((c.ι.app j) '' (maximalIdeal (F.obj j)) : Set c.pt) := sorry

/-- The functor of taking residue fields from a functor `F : J ⥤ CommRingCat`, when the `F.obj` are
  local rings and `F.map` are local ring homomorphisms. -/
noncomputable def residueFieldFunctor : J ⥤ CommRingCat.{u} where
  obj j := CommRingCat.of <| ResidueField (F.obj j)
  map f := CommRingCat.ofHom <| ResidueField.map (F.map f).hom

-- [NOTE]: This is newly written.
variable (c) in
noncomputable def residueFieldCocone' [c_pt : IsLocalRing c.pt]
    [c_ι : ∀ j, IsLocalHom (c.ι.app j).hom] : Cocone (residueFieldFunctor F) where
  pt := CommRingCat.of <| ResidueField c.pt
  ι := {
    app j := CommRingCat.ofHom <| @ResidueField.map _ _ _ _ _ _ (c.ι.app j).hom (c_ι j)
    naturality j j' f := by
      simp [residueFieldFunctor, ← ofHom_comp, ← ResidueField.map_comp, ← hom_comp]
  }

/-- The cocone constructed from a filtered colimit cocone of local homomorphisms between local
  rings. -/
noncomputable def residueFieldCocone (hc : IsColimit c) : Cocone (residueFieldFunctor F) :=
  residueFieldCocone' F c (c_pt := isLocalRing_of_isColimit F hc)
    (c_ι := fun j ↦ isLocalHom_ι F hc j)

noncomputable def isColimit_residueFieldCocone (hc : IsColimit c) :
    IsColimit (residueFieldCocone F hc) := sorry

variable (s : Cocone F) [s_pt : IsLocalRing s.pt] [s_ι : ∀ j, IsLocalHom (s.ι.app j).hom]

theorem isLocalHom_desc (hc : IsColimit c) : IsLocalHom (hc.desc s).hom := sorry

theorem residueField_map_desc_eq_isColimit_residueFieldCocone_desc (hc : IsColimit c) :
  @ResidueField.map _ _ _ (isLocalRing_of_isColimit F hc) _ _ (hc.desc s).hom
  (isLocalHom_desc F s hc) =
  ((isColimit_residueFieldCocone F hc).desc (residueFieldCocone' F s)).hom := sorry

end CommRingCat.FilteredColimit

namespace CommAlgCat

variable {R : Type u} [CommRing R]

/-- The object property of flat `R`-algebras. -/
def flat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat R) := sorry

@[simp]
lemma flat_iff {S : CommAlgCat R} : flat R S ↔ Module.Flat R S := sorry

lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  sorry

end CommAlgCat

end from_proetale

variable [IsLocalRing R] (K : Type u) [Field K] [Algebra (ResidueField R) K]

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
  Ring : Type u
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

instance : CoeSort (FlatExtension R K) (Type u) := ⟨FlatExtension.Ring⟩

attribute [coe] FlatExtension.Ring

noncomputable def mk' (S : Type u) [CommRing S] [Algebra R S] [Module.Flat R S]
    [IsLocalRing S] (hf : IsLocalHom (algebraMap R S)) (g : (ResidueField S) →+* K)
    (hg : g.comp (ResidueField.map (algebraMap R S)) = algebraMap (ResidueField R) K)
    (eqmap : maximalIdeal S = (maximalIdeal R).map (algebraMap R S)) : FlatExtension R K := by
  algebraize [g]
  have : IsLocalHom (algebraMap R S) := hf
  have : IsScalarTower (ResidueField R) (ResidueField S) K :=
    IsScalarTower.of_algebraMap_eq' hg.symm
  exact FlatExtension.mk S eqmap

/-
noncomputable def mk'' (S : Type w) [CommRing S] (h_isLocalRing : IsLocalRing S)
    (f : R →+* S) (hf : IsLocalHom f) (hf_flat : f.Flat) (g : (ResidueField S) →+* K)
    (hg : g.comp (ResidueField.map f) = algebraMap (ResidueField R) K)
    (eqmap : maximalIdeal S = (maximalIdeal R).map f) : FlatExtension R K := by
  algebraize [f, g]
  have : IsLocalHom (algebraMap R S) := hf
  have : IsScalarTower (ResidueField R) (ResidueField S) K :=
    IsScalarTower.of_algebraMap_eq' hg.symm
  exact FlatExtension.mk S eqmap
-/

noncomputable def trivial : FlatExtension R K where
  Ring := R
  isScalarTower := IsScalarTower.left (ResidueField R)
  eqmap := by simp

variable {R K} in
structure Hom (S₁ S₂ : FlatExtension R K) where
  algHom : S₁.Ring →ₐ[R] S₂.Ring
  [isLocalHom : IsLocalHom algHom]
  comm : (algebraMap (ResidueField S₂.Ring) K).comp (ResidueField.map algHom) =
    (algebraMap (ResidueField S₁.Ring) K)

attribute [instance] Hom.isLocalHom

variable {R K}

def Hom.id (S : FlatExtension R K) : Hom S S := ⟨AlgHom.id R S.Ring, by simp⟩

def Hom.comp {S₁ S₂ S₃ : FlatExtension R K} (f : Hom S₁ S₂) (g : Hom S₂ S₃) :
    Hom S₁ S₃ := ⟨g.algHom.comp f.algHom, by
  simp [← f.comm, ← g.comm, AlgHom.comp_toRingHom', ResidueField.map_comp, ← RingHom.comp_assoc]⟩

instance : Category (FlatExtension R K) where
  Hom S₁ S₂ := Hom S₁ S₂
  id S := Hom.id S
  comp f g := f.comp g

noncomputable abbrev adjoinAlgebraic (S : FlatExtension R K) (x : K)
    (int : IsIntegral (ResidueField S.Ring) x) : FlatExtension R K :=
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

noncomputable abbrev toAdjoinAlgebraic (S : FlatExtension R K) (x : K)
    (int : IsIntegral (ResidueField S.Ring) x) : S ⟶ S.adjoinAlgebraic x int where
  algHom := IsScalarTower.toAlgHom R S.Ring _
  isLocalHom := ⟨by simp⟩
  comm :=
    let := adjoinAlgebraicAlgebraK K S.Ring x int
    let := adjoinAlgebraicIsScalarTower K S.Ring x int
    (IsScalarTower.algebraMap_eq _ _ K).symm

noncomputable abbrev adjoinTranscendental (S : FlatExtension R K) (x : K)
    (nint : ¬ IsIntegral (ResidueField S.Ring) x) : FlatExtension R K :=
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

noncomputable abbrev toAdjoinTranscendental (S : FlatExtension R K) (x : K)
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
noncomputable def SuccStruct : SuccStruct (FlatExtension R K) where
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

lemma algebraMap_range_lt_of_not_surjective (S : FlatExtension R K)
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

instance (S S' : FlatExtension R K) :
    FunLike {f : S →ₐ[R] S' //
      ∃ _ : IsLocalHom f, (algebraMap (ResidueField S') K).comp
        (ResidueField.map f) = (algebraMap (ResidueField S) K)} S S' where
  coe f := f
  coe_injective' _ _ h := Subtype.ext (AlgHom.ext fun x ↦ congr($h x))

instance : ConcreteCategory (FlatExtension R K)
    fun S S' ↦ {f : S →ₐ[R] S' //
    ∃ _ : IsLocalHom f, (algebraMap (ResidueField S') K).comp
    (ResidueField.map f) = (algebraMap (ResidueField S) K)} where
  hom {S S'} f := ⟨f.algHom, f.isLocalHom, f.comm⟩
  ofHom {S S'} f := {
    algHom := f.1
    isLocalHom := f.2.1
    comm := f.2.2 }

def Hom.mk' {S₁ S₂ : FlatExtension R K} (f : S₁ →ₐ[R] S₂)
    (isl : IsLocalHom f) (comm : (algebraMap (ResidueField S₂) K).comp
      (ResidueField.map f) = (algebraMap (ResidueField S₁) K)) : S₁.Hom S₂ where
  algHom := f
  comm := comm

instance : HasForget₂ (FlatExtension R K) (CommAlgCat R) where
  forget₂ := {
    obj S := CommAlgCat.of R S.Ring
    map f := CommAlgCat.ofHom f.1 }

namespace FilteredColimit

variable {R K} {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ FlatExtension R K}

lemma isLocalRing_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : IsLocalRing c.pt :=
  @CommRingCat.FilteredColimit.isLocalRing_of_isColimit _ _ _ _
  ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c) (fun j ↦ (F.obj j).isLocalRing)
  (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom) (isColimitOfPreserves _ hc)


lemma isLocalHom_ι_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) (j : J) : IsLocalHom (c.ι.app j).hom := by
  have := @CommRingCat.FilteredColimit.isLocalHom_ι _ _ _ _
    ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c)
    (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom) (isColimitOfPreserves _ hc) j
  simp only [Functor.comp_obj, CommAlgCat.forget₂_commRingCat_obj, Functor.mapCocone_pt,
    Functor.const_obj_obj, Functor.mapCocone_ι_app, CommAlgCat.forget₂_commRingCat_map,
    ConcreteCategory.hom_ofHom] at this
  exact isLocalHom_of_toRingHom _ (inst := this)

lemma isLocalHom_algebraMap_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : IsLocalHom (algebraMap R c.pt) := by
  obtain ⟨j⟩ : Nonempty J := ‹IsFiltered J›.2
  have : algebraMap R c.pt = (RingHomClass.toRingHom (c.ι.app j).hom).comp
    (algebraMap R (F.obj j)) := (AlgHom.comp_algebraMap (CommAlgCat.Hom.hom (c.ι.app j))).symm
  rw [this]
  exact @RingHom.isLocalHom_comp _ _ _ _ _ _ _ _
    (@isLocalHom_toRingHom _ _ _ _ _ _ _ _ <| isLocalHom_ι_of_isColimit c hc j) (F.obj j).isLocalHom

lemma flat_of_isColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : Module.Flat R c.pt := by
  rw [← CommAlgCat.flat_iff, ← CommAlgCat.ind_flat]
  refine ⟨J, inferInstance, inferInstance, ⟨F ⋙ (forget₂ _ (CommAlgCat R)), c.ι, hc⟩, fun j ↦ ?_⟩
  simpa using (F.obj j).flat

variable (F) in
noncomputable def residueFieldFunctor :=
  @CommRingCat.FilteredColimit.residueFieldFunctor _ _
  (F ⋙ (forget₂ _ (CommAlgCat R)) ⋙ (forget₂ _ CommRingCat)) (fun j ↦ (F.obj j).isLocalRing)
  (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom)

noncomputable def residueFieldCocone (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : Cocone (residueFieldFunctor F) :=
  @CommRingCat.FilteredColimit.residueFieldCocone
    _ _ _ _ ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c)
    (fun j ↦ (F.obj j).isLocalRing) (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom)
    (isColimitOfPreserves _ hc)

noncomputable def isColimitResidueFieldCocone (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : IsColimit (residueFieldCocone c hc) :=
  @CommRingCat.FilteredColimit.isColimit_residueFieldCocone
    _ _ _ _ ((forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c)
    (fun j ↦ (F.obj j).isLocalRing) (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom)
    (isColimitOfPreserves _ hc)

noncomputable def residueFieldCoconeK : Cocone (residueFieldFunctor F) where
  pt := CommRingCat.of K
  ι := {
    app j := CommRingCat.ofHom <| algebraMap (ResidueField (F.obj j)) K
    naturality j j' f := by
      simpa [residueFieldFunctor, CommRingCat.FilteredColimit.residueFieldFunctor,
        ← CommRingCat.ofHom_comp] using congr(CommRingCat.ofHom $((F.map f).comm))
  }

noncomputable def residueFieldDescOfIsColimit (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) :
    haveI := isLocalRing_of_isColimit c hc
    ResidueField c.pt →+* K :=
  ((isColimitResidueFieldCocone c hc).desc residueFieldCoconeK).hom

noncomputable def coconeOfCoconeForgetPt (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : FlatExtension R K := by
  have := isLocalRing_of_isColimit c hc
  have := flat_of_isColimit c hc
  let c' := (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c
  let hc' : IsColimit c' := isColimitOfPreserves _ hc
  have heq (j : J) : algebraMap R c.pt = (c'.ι.app j).hom.comp (algebraMap R (F.obj j)) :=
      (AlgHom.comp_algebraMap (CommAlgCat.Hom.hom (c.ι.app j))).symm
  refine FlatExtension.mk' R K c.pt (isLocalHom_algebraMap_of_isColimit c hc)
    (residueFieldDescOfIsColimit c hc) ?_ ?_
  · obtain ⟨j⟩ := ‹IsFiltered J›.2
    have : IsLocalRing (((Functor.const J).obj c'.pt).obj j) := isLocalRing_of_isColimit c hc
    have : IsLocalHom (c'.ι.app j).hom := @isLocalHom_toRingHom _ _ _ _ _ _ _ _ <|
      (isLocalHom_ι_of_isColimit c hc j)
    have h1 := @ResidueField.map_comp _ _ _ _ _ _ _ _ _ (algebraMap R (F.obj j)) (c'.ι.app j).hom
      inferInstance this
    have : (residueFieldDescOfIsColimit c hc).comp
      (@ResidueField.map _ _ _ (inferInstanceAs (IsLocalRing (F.obj j))) _ _ _ this) =
      algebraMap (ResidueField (F.obj j)) K := congr(CommRingCat.Hom.hom
      $(((isColimitResidueFieldCocone c hc).fac residueFieldCoconeK) j))
    simp_rw [heq j]
    erw [h1, ← RingHom.comp_assoc, this]
    exact (F.obj j).isScalarTower.algebraMap_eq.symm
  · refine le_antisymm (fun x hx ↦ ?_) (((local_hom_TFAE (algebraMap R c.pt)).out 0 2).mp
      (isLocalHom_algebraMap_of_isColimit c hc))
    obtain ⟨j, x, hx', rfl⟩ := Set.mem_iUnion.mp <| (le_of_eq <|
      @CommRingCat.FilteredColimit.maximalIdeal_eq_iUnion_of_isColimit _ _ _ _
      c' (fun j ↦ (F.obj j).isLocalRing) (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom) hc') hx
    change x ∈ maximalIdeal (F.obj j) at hx'
    rw [(F.obj j).eqmap] at hx'
    rw [heq j]
    erw [← Ideal.map_map]
    exact Ideal.mem_map_of_mem (c'.ι.app j).hom hx'

lemma coconeOfCoconeForgetPt_algebraMap_eq (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) :
    (algebraMap (ResidueField (coconeOfCoconeForgetPt c hc)) K) =
    residueFieldDescOfIsColimit c hc := rfl

noncomputable def coconeOfCoconeForget (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : Cocone F where
  pt := coconeOfCoconeForgetPt c hc
  ι := {
    app j := by
      let h := isColimitResidueFieldCocone c hc
      refine FlatExtension.Hom.mk' R K (c.ι.app j).hom (isLocalHom_ι_of_isColimit c hc j) ?_
      change (h.desc residueFieldCoconeK).hom.comp ((residueFieldCocone c hc).ι.app j).hom =
        (residueFieldCoconeK.ι.app j).hom
      simp only [Functor.const_obj_obj, ← CommRingCat.hom_comp]
      exact congr(CommRingCat.Hom.hom <| $(h.fac residueFieldCoconeK j))
    naturality j j' f := by
      ext x
      exact congr($(c.ι.naturality f) x) }

#check Category
noncomputable def isColimit_coconeOfCoconeForget (c : Cocone (F ⋙ (forget₂ _ (CommAlgCat R))))
    (hc : IsColimit c) : IsColimit (coconeOfCoconeForget c hc) := by
  let c' := (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone c
  let hc' : IsColimit c' := isColimitOfPreserves _ hc
  have heq (s : Cocone F) : RingHomClass.toRingHom
    (hc.desc ((forget₂ (FlatExtension R K) (CommAlgCat R)).mapCocone s)).hom =
    (hc'.desc <| (forget₂ _ CommRingCat).mapCocone <|
    (forget₂ (FlatExtension R K) (CommAlgCat R)).mapCocone s).hom := by
    simp only [hc', preserves_desc_mapCocone]
    rfl
  -- have heq' (s : Cocone F) := congr(CommRingCat.ofHom $(heq s))
  -- simp only [CommRingCat.ofHom_hom] at heq'
  refine IsColimit.ofFaithful (forget₂ (FlatExtension R K) (CommAlgCat R)) hc
    (fun s ↦ FlatExtension.Hom.mk' R K (hc.desc ((forget₂ _ (CommAlgCat R)).mapCocone s)).hom
      (@isLocalHom_of_toRingHom _ _ _ _ _ _ _ _ ?_) ?_) (fun s ↦ rfl)
  · erw [heq s]
    exact @CommRingCat.FilteredColimit.isLocalHom_desc _ _ _ _ c'
      (fun j ↦ inferInstanceAs (IsLocalRing (F.obj j)))
      (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom)
      _ s.pt.isLocalRing (fun j ↦ isLocalHom_toRingHom (s.ι.app j).algHom) hc'
  · conv =>
      enter [1, 2, 1]
      erw [heq s]
    have := @CommRingCat.FilteredColimit.residueField_map_desc_eq_isColimit_residueFieldCocone_desc
      _ _ _ _ c' (fun j ↦ inferInstanceAs (IsLocalRing (F.obj j)))
      (fun _ _ f ↦ isLocalHom_toRingHom (F.map f).algHom)
      ((forget₂ _ CommRingCat).mapCocone <|
      (forget₂ (FlatExtension R K) (CommAlgCat R)).mapCocone s) s.pt.isLocalRing
      (fun j ↦ isLocalHom_toRingHom (s.ι.app j).algHom) hc'
    erw [this]
    change (CommRingCat.ofHom _).hom.comp _ = _
    erw [← CommRingCat.hom_comp]
    congr 1
    refine (isColimitResidueFieldCocone c hc).uniq residueFieldCoconeK _ fun j ↦ ?_
    replace := congr(CommRingCat.ofHom $this)
    simp only [CommRingCat.ofHom_hom] at this
    simp only [← this, residueFieldCocone, residueFieldCoconeK,
      CommRingCat.FilteredColimit.residueFieldCocone]
    simp only [CommRingCat.FilteredColimit.residueFieldCocone', Functor.mapCocone_pt,
      CommAlgCat.forget₂_commRingCat_obj, Functor.comp_obj, Functor.const_obj_obj,
      Functor.mapCocone_ι_app, CommAlgCat.forget₂_commRingCat_map, CommRingCat.hom_ofHom]
    -- show RingHomClass.toRingHom (c.ι.app j).hom = (c'.app j).hom from rfl
    -- ← Category.assoc
    -- ← CommRingCat.ofHom_comp
    -- ← ResidueField.map_comp
    -- hc'.fac _
    sorry


set_option pp.universes true in
instance : HasColimitsOfShape J (FlatExtension R K) where
  has_colimit F := by
    obtain ⟨⟨c, hc⟩⟩ : HasColimit (F ⋙ (forget₂ _ (CommAlgCat R))) := inferInstance
    exact ⟨⟨⟨coconeOfCoconeForget c hc, isColimit_coconeOfCoconeForget c hc⟩⟩⟩

instance : HasFilteredColimitsOfSize.{u, u} (FlatExtension R K) where
  HasColimitsOfShape _ _ _ := inferInstance

end FilteredColimit

end FlatExtension

/-- In this version the universe levels of `R` and `K` are assumed to be the same, see
  `exists_isLocalHom_flat` for a version where they have different universe levels. -/
lemma exists_isLocalHom_flat' : ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R')
    (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[ResidueField R] (ResidueField R')) := by
  obtain ⟨setK, ⟨e⟩⟩ : ∃ S : Type u, Nonempty (S ≃ Set K) := ⟨ULift (Set K), ⟨Equiv.ulift⟩⟩
  let ⟨lin, wf⟩ := exists_wellFoundedLT setK
  let : WellFoundedLT (WithTop setK) := WithTop.instWellFoundedLT
  let : SuccOrder (WithTop setK) := SuccOrder.ofLinearWellFoundedLT _
  let : OrderBot (WithTop setK) := WellFoundedLT.toOrderBot _
  obtain ⟨φ⟩ : Nonempty ((FlatExtension.SuccStruct R K).Iteration (⊤ : WithTop setK)) :=
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

lemma exists_isLocalHom_flat (K : Type u) [Field K] [Algebra (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R')
    (_ : Algebra R R') (_ : IsLocalHom (algebraMap R R')), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[ResidueField R] (ResidueField R')) := by
  -- obtain ⟨R₁, _, _, _, _, h⟩ := exists_isLocalHom_flat' (ULift.{v, u} R) (ULift.{u, v} K)
  sorry
