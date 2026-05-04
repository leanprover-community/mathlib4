/-
Copyright (c) 2026 Nailin Guan, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Jingting Wang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Algebra.Shrink
public import Mathlib.Algebra.Field.ULift
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

universe u v

open IsLocalRing CategoryTheory SmallObject Limits

open Polynomial

variable (R : Type u) [CommRing R]

section preliminaries

lemma IsScalarTower.algebraMap_range_le (S T : Type*) [CommRing S] [Ring T] [Algebra R S]
    [Algebra R T] [Algebra S T] [IsScalarTower R S T] :
    (algebraMap R T).range ≤ (algebraMap S T).range := by
  rintro x ⟨y, hy⟩
  use algebraMap R S y
  rw [← hy, IsScalarTower.algebraMap_apply R S T]

end preliminaries

section from_proetale

open CategoryTheory Limits IsLocalRing

variable {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{u}) {c : Cocone F}
  [h_obj : ∀ (j : J), IsLocalRing (F.obj j)]
  [h_hom : ∀ (j j' : J) (f : j ⟶ j'), IsLocalHom (F.map f).hom]

namespace CommRingCat.FilteredColimit

theorem isLocalRing_of_isColimit (hc : IsColimit c) : IsLocalRing c.pt := by sorry

lemma maximalIdeal_eq_iUnion_of_isColimit (hc : IsColimit c) :
    (isLocalRing_of_isColimit F hc).maximalIdeal =
    ⋃ (j : J), ((c.ι.app j) '' (maximalIdeal (F.obj j)) : Set c.pt) := sorry

end CommRingCat.FilteredColimit

end from_proetale

variable [IsLocalRing R] (K : Type u) [Field K] [Algebra R K] [IsLocalHom (algebraMap R K)]

namespace Monogenic

variable (S : Type u) [CommRing S] [Algebra S K]

variable [IsLocalRing S] [IsLocalHom (algebraMap S K)]

variable {S K} in
lemma algebraMap_eq_zero (x : S) (mem : x ∈ maximalIdeal S) : algebraMap S K x = 0 := by
  simp only [mem_maximalIdeal, mem_nonunits_iff] at mem
  exact (iff_not_comm.mp isUnit_iff_ne_zero).mpr ((IsLocalHom.map_nonunit x).mt mem)

local instance [IsLocalHom (algebraMap S K)] : Algebra (ResidueField S) K :=
  (Ideal.Quotient.lift _ (algebraMap S K) (fun x hx ↦ algebraMap_eq_zero x hx)).toAlgebra

local instance : IsScalarTower S (ResidueField S) K :=
  IsScalarTower.of_algebraMap_eq' rfl

lemma isIntegral_residueField_iff (x : K) : IsIntegral (ResidueField S) x ↔ IsIntegral S x := by
  refine ⟨fun ⟨f, hf, eval⟩ ↦ ?_, fun h ↦ IsIntegral.tower_top h⟩
  rcases Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.map_surjective (residue S) residue_surjective f) hf with ⟨g, hg, deg, mon⟩
  use g, mon
  rw [← eval, ← hg]
  exact (Polynomial.aeval_map_algebraMap _ x g).symm

lemma minpoly_residueField_eq_map (x : K) (int : IsIntegral S x) :
    minpoly (ResidueField S) x = Polynomial.map (residue S) (minpoly S x) := by
  apply (minpoly.unique_of_degree_le_degree_minpoly _ _ ((minpoly.monic int).map _) _ _).symm
  · exact (Polynomial.aeval_map_algebraMap _ _ _).trans (minpoly.aeval S x)
  · apply Polynomial.degree_map_le.trans
    have mon : (minpoly (ResidueField S) x).Monic := minpoly.monic (IsIntegral.tower_top int)
    rcases Polynomial.lifts_and_degree_eq_and_monic
      (Polynomial.map_surjective (residue S) residue_surjective _) mon with ⟨g, hg, deg, mon⟩
    rw [← deg]
    apply minpoly.min _ _ mon
    rw [← minpoly.aeval (ResidueField S) x, ← hg]
    exact (Polynomial.aeval_map_algebraMap _ x g).symm

set_option linter.unusedVariables false in
abbrev adjoinAlgebraic (x : K) (int : IsIntegral S x) : Type u := S[X] ⧸ Ideal.span {minpoly S x}

instance (x : K) (int : IsIntegral S x) : Module.Finite S (adjoinAlgebraic K S x int) :=
  (minpoly.monic int).finite_quotient

instance (x : K) (int : IsIntegral S x) : Module.Free S (adjoinAlgebraic K S x int) :=
  (minpoly.monic int).free_quotient

lemma adjoinAlgebraic_maximalIdeal_map_isMaximal (x : K) (int : IsIntegral S x) :
    ((maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int))).IsMaximal := by
  let f : adjoinAlgebraic K S x int →+*
    (ResidueField S)[X] ⧸ Ideal.span {minpoly (ResidueField S) x} :=
    Ideal.quotientMap _ (mapRingHom (residue S))
      (by simp [← minpoly_residueField_eq_map K S x int])
  have kerf : RingHom.ker f = (maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int)) := by
    apply Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    have eqmap : Ideal.span {minpoly (ResidueField S) x} =
      (Ideal.span {minpoly S x}).map (mapRingHom (residue S)) := by
      simp [minpoly_residueField_eq_map K S x int, Ideal.map_span]
    rw [RingHom.comap_ker, IsScalarTower.algebraMap_eq S S[X], Ideal.quotientMap_comp_mk]
    simp [← Ideal.map_map, ← RingHom.comap_ker, eqmap, ker_mapRingHom, ker_residue,
      Ideal.comap_map_of_surjective' (mapRingHom _) (map_surjective _ residue_surjective)]
  rw [← kerf]
  let : Fact _ := ⟨minpoly.irreducible ((isIntegral_residueField_iff K S x).mpr int)⟩
  let := Ideal.Quotient.field (Ideal.span {(minpoly (ResidueField S) x)})
  exact RingHom.ker_isMaximal_of_surjective _
    (Ideal.quotientMap_surjective (map_surjective _ residue_surjective))

instance adjoinAlgebraic_isLocalRing (x : K) (int : IsIntegral S x) :
    IsLocalRing (adjoinAlgebraic K S x int) := by
  have := adjoinAlgebraic_maximalIdeal_map_isMaximal K S x int
  apply IsLocalRing.of_unique_max_ideal
  use (maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int)), this
  intro m hm
  exact (this.eq_of_le hm.ne_top (Ideal.map_le_iff_le_comap.mpr (le_of_eq (eq_maximalIdeal
    m.isMaximal_comap_of_isIntegral_of_isMaximal).symm))).symm

lemma adjoinAlgebraic_maximalIdeal_eq_map (x : K) (int : IsIntegral S x) :
    maximalIdeal (adjoinAlgebraic K S x int) =
    (maximalIdeal S).map (algebraMap S (adjoinAlgebraic K S x int)) :=
  (eq_maximalIdeal (adjoinAlgebraic_maximalIdeal_map_isMaximal K S x int)).symm

omit [IsLocalRing S] [IsLocalHom (algebraMap S K)] in
lemma span_minpoly_le_ker (x : K) : Ideal.span {minpoly S x} ≤
    RingHom.ker (Polynomial.aeval x) := by
  simp

noncomputable abbrev adjoinAlgebraicToK (x : K) (int : IsIntegral S x) :
    adjoinAlgebraic K S x int →+* K :=
  Ideal.Quotient.lift _ (Polynomial.aeval x).toRingHom (fun _ h ↦ span_minpoly_le_ker K S x h)

noncomputable instance (x : K) (int : IsIntegral S x) : Algebra (adjoinAlgebraic K S x int) K :=
  (adjoinAlgebraicToK K S x int).toAlgebra

noncomputable instance (x : K) (int : IsIntegral S x) :
    IsScalarTower S (adjoinAlgebraic K S x int) K := by
  apply IsScalarTower.of_algebraMap_eq (fun y ↦ ?_)
  rw [IsScalarTower.algebraMap_eq S S[X] (adjoinAlgebraic K S x int)]
  simp [RingHom.algebraMap_toAlgebra]

omit [IsLocalRing S] [IsLocalHom (algebraMap S K)] in
lemma adjoinAlgebraic_mem_range (x : K) (int : IsIntegral S x) :
    x ∈ (algebraMap (adjoinAlgebraic K S x int) K).range := by
  use Ideal.Quotient.mk _ Polynomial.X
  simp [RingHom.algebraMap_toAlgebra]

set_option linter.unusedVariables false in
abbrev adjoinTranscendental (x : K) (nint : ¬ IsIntegral S x) : Type u :=
  Localization.AtPrime ((maximalIdeal S).map Polynomial.C)

omit [IsLocalHom (algebraMap S K)] in
lemma adjoinTranscendental_maximalIdeal_eq_map (x : K) (nint : ¬ IsIntegral S x) :
    maximalIdeal (adjoinTranscendental K S x nint) =
    (maximalIdeal S).map (algebraMap S (adjoinTranscendental K S x nint)) := by
  rw [IsScalarTower.algebraMap_eq S S[X], ← Ideal.map_map]
  exact Localization.AtPrime.map_eq_maximalIdeal.symm

lemma adjoinTranscendental_aeval_ker (x : K) (nint : ¬ IsIntegral S x) :
    RingHom.ker (Polynomial.aeval x) = (maximalIdeal S).map Polynomial.C := by
  have : (Polynomial.aeval x).toRingHom = (Polynomial.aeval x).toRingHom.comp
    (Polynomial.mapRingHom (IsLocalRing.residue S)) :=
    RingHom.ext (fun p ↦ (Polynomial.aeval_map_algebraMap (ResidueField S) _ _).symm)
  have inj : Function.Injective (Polynomial.aeval (R := ResidueField S) x) := by
    apply (iff_not_comm.mpr isAlgebraic_iff_not_injective).mpr
    exact isAlgebraic_iff_isIntegral.not.mpr ((isIntegral_residueField_iff K S x).not.mpr nint)
  change RingHom.ker (Polynomial.aeval x).toRingHom = _
  rw [this, RingHom.ker_comp_of_injective _ inj, Polynomial.ker_mapRingHom, ker_residue]

noncomputable abbrev adjoinTranscendentalToK (x : K) (nint : ¬ IsIntegral S x) :
    adjoinTranscendental K S x nint →+* K :=
  IsLocalization.lift (M := ((maximalIdeal S).map Polynomial.C).primeCompl)
    (g := (Polynomial.aeval x).toRingHom) (fun y ↦ by
      simpa [← RingHom.mem_ker, adjoinTranscendental_aeval_ker K S x nint] using
        Ideal.mem_primeCompl_iff.mp y.2)

noncomputable instance (x : K) (nint : ¬ IsIntegral S x) :
    Algebra (adjoinTranscendental K S x nint) K :=
  (adjoinTranscendentalToK K S x nint).toAlgebra

noncomputable instance (x : K) (nint : ¬ IsIntegral S x) :
    IsScalarTower S (adjoinTranscendental K S x nint) K := by
  apply IsScalarTower.of_algebraMap_eq (fun y ↦ ?_)
  rw [IsScalarTower.algebraMap_eq S S[X] (adjoinTranscendental K S x nint)]
  simp [RingHom.algebraMap_toAlgebra]

lemma adjoinTranscendental_mem_range (x : K) (nint : ¬ IsIntegral S x) :
    x ∈ (algebraMap (adjoinTranscendental K S x nint) K).range := by
  use algebraMap S[X] _ Polynomial.X
  simp [RingHom.algebraMap_toAlgebra]

end Monogenic

structure FlatExtension where
  Ring : Type u
  [commRing : CommRing Ring]
  [isLocalRing : IsLocalRing Ring]
  [algebra : Algebra R Ring]
  [algebraK : Algebra Ring K]
  [isScalarTower : IsScalarTower R Ring K]
  [flat : Module.Flat R Ring]
  eqmap : maximalIdeal Ring = (maximalIdeal R).map (algebraMap R Ring)

namespace FlatExtension

attribute [instance] commRing algebra isLocalRing algebraK isScalarTower flat

instance : CoeSort (FlatExtension R K) (Type u) := ⟨FlatExtension.Ring⟩

attribute [coe] FlatExtension.Ring

instance (S : FlatExtension R K) : IsLocalHom (algebraMap R S) :=
  ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr (le_of_eq S.eqmap.symm)

instance (S : FlatExtension R K) : IsLocalHom (algebraMap S K) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 0 2).mpr
  rw [S.eqmap, Ideal.map_map, ← IsScalarTower.algebraMap_eq R]
  exact ((IsLocalRing.local_hom_TFAE _).out 0 2).mp ‹_›

noncomputable def trivial : FlatExtension R K where
  Ring := R
  isScalarTower := IsScalarTower.left R
  eqmap := by simp

variable {R K} in
structure Hom (S₁ S₂ : FlatExtension R K) where
  algHom : S₁.Ring →ₐ[R] S₂.Ring
  comm : (IsScalarTower.toAlgHom R S₂ K).comp algHom = IsScalarTower.toAlgHom R S₁ K

instance (S₁ S₂ : FlatExtension R K) (f : S₁.Hom S₂) : IsLocalHom f.algHom.toRingHom := by
  apply ((IsLocalRing.local_hom_TFAE f.algHom.toRingHom).out 0 2).mpr
  have : f.algHom.toRingHom.comp (algebraMap R S₁) = (algebraMap R S₂) :=
    AlgHom.comp_algebraMap_of_tower _ _
  rw [S₁.eqmap, Ideal.map_map, this, ← S₂.eqmap]

variable {R K}

def Hom.id (S : FlatExtension R K) : Hom S S := ⟨AlgHom.id R S.Ring, by simp⟩

def Hom.comp {S₁ S₂ S₃ : FlatExtension R K} (f : Hom S₁ S₂) (g : Hom S₂ S₃) :
    Hom S₁ S₃ := ⟨g.algHom.comp f.algHom, by simp [← AlgHom.comp_assoc, g.comm, f.comm]⟩

instance : Category (FlatExtension R K) where
  Hom S₁ S₂ := Hom S₁ S₂
  id S := Hom.id S
  comp f g := f.comp g

noncomputable abbrev adjoinAlgebraic (S : FlatExtension R K) (x : K)
    (int : IsIntegral S x) : FlatExtension R K where
  Ring := Monogenic.adjoinAlgebraic K S x int
  isScalarTower := IsScalarTower.to₁₃₄ R S _ K
  flat := Module.Flat.trans R S _
  eqmap := by
    rw [Monogenic.adjoinAlgebraic_maximalIdeal_eq_map K S x int,
      IsScalarTower.algebraMap_eq R S, ← Ideal.map_map, S.eqmap]

noncomputable abbrev toAdjoinAlgebraic (S : FlatExtension R K) (x : K)
    (int : IsIntegral S x) : S ⟶ S.adjoinAlgebraic x int where
  algHom := IsScalarTower.toAlgHom R S.Ring _
  comm := by
    ext y
    simp [← IsScalarTower.algebraMap_apply S _ K y]

noncomputable abbrev adjoinTranscendental (S : FlatExtension R K) (x : K)
    (nint : ¬ IsIntegral S x) : FlatExtension R K where
  Ring := Monogenic.adjoinTranscendental K S x nint
  isScalarTower := IsScalarTower.to₁₃₄ R S _ K
  flat := Module.Flat.trans R S _
  eqmap := by
    rw [Monogenic.adjoinTranscendental_maximalIdeal_eq_map K S x nint,
      IsScalarTower.algebraMap_eq R S, ← Ideal.map_map, ← S.eqmap]

noncomputable abbrev toAdjoinTranscendental (S : FlatExtension R K) (x : K)
    (nint : ¬ IsIntegral S x) : S ⟶ S.adjoinTranscendental x nint where
  algHom := IsScalarTower.toAlgHom R S.Ring _
  comm := by
    ext y
    simp [← IsScalarTower.algebraMap_apply S _ K y]

variable (R K)

open Classical in
noncomputable def SuccStruct : SuccStruct (FlatExtension R K) where
  X₀ := trivial R K
  succ S := if surj : Function.Surjective (algebraMap S K) then S else
      if int : IsIntegral S (Classical.choose (Decidable.not_forall.mp surj))
        then adjoinAlgebraic S _ int
        else adjoinTranscendental S _ int
  toSucc S := if surj : Function.Surjective (algebraMap S K) then by
        simpa only [surj, ↓reduceDIte] using 𝟙 S else
      if int : IsIntegral S (Classical.choose (Decidable.not_forall.mp surj))
        then by simpa only [surj, int, ↓reduceDIte] using toAdjoinAlgebraic S _ int
        else by simpa only [surj, int, ↓reduceDIte] using toAdjoinTranscendental S _ int

lemma algebraMap_range_lt_of_not_surjective (S : FlatExtension R K)
    (nsurj : ¬ Function.Surjective (algebraMap S K)) :
    (algebraMap S K).range <
    (algebraMap ((FlatExtension.SuccStruct R K).succ S) K).range := by
  classical
  by_cases int : IsIntegral S (Classical.choose (Decidable.not_forall.mp nsurj))
  · have : (FlatExtension.SuccStruct R K).succ S = adjoinAlgebraic S _ int := by
      simp only [↓reduceDIte, SuccStruct, nsurj, int]
    rw [this]
    exact Set.ssubset_iff_exists.mpr
      ⟨IsScalarTower.algebraMap_range_le S (Monogenic.adjoinAlgebraic K S _ int) K,
        Classical.choose (Decidable.not_forall.mp nsurj),
          Monogenic.adjoinAlgebraic_mem_range K S.Ring _ int,
            Classical.choose_spec (Decidable.not_forall.mp nsurj)⟩
  · have : (FlatExtension.SuccStruct R K).succ S = adjoinTranscendental S _ int := by
      simp only [↓reduceDIte, SuccStruct, nsurj, int]
    rw [this]
    exact Set.ssubset_iff_exists.mpr
      ⟨IsScalarTower.algebraMap_range_le S (Monogenic.adjoinTranscendental K S _ int) K,
        Classical.choose (Decidable.not_forall.mp nsurj),
          Monogenic.adjoinTranscendental_mem_range K S.Ring _ int,
            Classical.choose_spec (Decidable.not_forall.mp nsurj)⟩

instance (S₁ S₂ : FlatExtension R K) :
    FunLike {f : S₁ →ₐ[R] S₂ //
      (IsScalarTower.toAlgHom R S₂ K).comp f = IsScalarTower.toAlgHom R S₁ K} S₁ S₂ where
  coe f := f
  coe_injective' _ _ h := Subtype.ext (AlgHom.ext fun x ↦ congr($h x))

instance : ConcreteCategory (FlatExtension R K)
    fun S₁ S₂ ↦ {f : S₁ →ₐ[R] S₂ //
      (IsScalarTower.toAlgHom R S₂ K).comp f = IsScalarTower.toAlgHom R S₁ K} where
  hom {S₁ S₂} f := ⟨f.algHom, f.comm⟩
  ofHom {S₁ S₂} f := ⟨f.1, f.2⟩

namespace FilteredColimit

variable {R K} {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ FlatExtension R K}

instance : HasColimitsOfShape J (FlatExtension R K) where
  has_colimit F := by
    sorry

instance : HasFilteredColimitsOfSize.{u, u} (FlatExtension R K) where
  HasColimitsOfShape _ _ _ := inferInstance

end FilteredColimit

end FlatExtension

/-- In this version the universe levels of `R` and `K` are assumed to be the same, see
  `exists_isLocalHom_flat` for a version where they have different universe levels. -/
lemma exists_isLocalHom_flat' : ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R')
    (_ : Algebra R R'), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[R] (ResidueField R')) := by
  obtain ⟨setK, ⟨e⟩⟩ : ∃ S : Type u, Nonempty (S ≃ Set K) := ⟨ULift (Set K), ⟨Equiv.ulift⟩⟩
  let ⟨lin, wf⟩ := exists_wellFoundedLT setK
  let : WellFoundedLT (WithTop setK) := WithTop.instWellFoundedLT
  let : SuccOrder (WithTop setK) := SuccOrder.ofLinearWellFoundedLT _
  let : OrderBot (WithTop setK) := WellFoundedLT.toOrderBot _
  let : HasIterationOfShape (WithTop setK) (FlatExtension R K) := {
    hasColimitsOfShape_of_isSuccLimit j hj := inferInstance
    hasColimitsOfShape := inferInstance }
  obtain ⟨φ⟩ : Nonempty ((FlatExtension.SuccStruct R K).Iteration (⊤ : WithTop setK)) :=
    inferInstance
  let fi : WithTop setK ≃o Set.Iic (⊤ : WithTop setK) := OrderIso.IicTop.symm
  let φobj := fun i ↦ (algebraMap (φ.F.obj (fi i)) K).range
  let φtop := φ.F.obj (fi ⊤)
  suffices h : (algebraMap φtop K).range = ⊤ by
    let f : (ResidueField φtop) →+* K :=
      (Ideal.Quotient.lift _ (algebraMap φtop K) (fun x hx ↦ Monogenic.algebraMap_eq_zero x hx))
    have : Function.Bijective f := ⟨RingHom.injective f,
      Ideal.Quotient.lift_surjective_of_surjective _ _ (RingHom.range_eq_top.mp h)⟩
    let f' := RingEquiv.ofBijective f this
    refine ⟨φtop.Ring, inferInstance, inferInstance, inferInstance, inferInstance,
      φtop.eqmap, ⟨AlgEquiv.ofRingEquiv (f := f'.symm) fun x ↦ f'.injective ?_⟩⟩
    simp only [RingEquiv.apply_symm_apply, RingEquiv.coe_ofBijective, f', f]
    rw [IsScalarTower.algebraMap_apply R φtop (ResidueField φtop)]
    exact IsScalarTower.algebraMap_apply R φtop K x
  have mono : Monotone φobj := fun a b hab ↦ by
    let mapab := φ.F.map (homOfLE (fi.monotone hab))
    rintro _ ⟨x, rfl⟩
    exact ⟨mapab.algHom.toRingHom x, congr($mapab.comm x)⟩
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

lemma exists_isLocalHom_flat (K : Type v) [Field K] [Algebra R K] [IsLocalHom (algebraMap R K)] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : IsLocalRing R')
    (_ : Algebra R R'), Module.Flat R R' ∧
    maximalIdeal R' = (maximalIdeal R).map (algebraMap R R') ∧
    Nonempty (K ≃ₐ[R] (ResidueField R')) := by
  obtain ⟨R', _, ⟨eR⟩⟩ : ∃ (R' : Type (max u v)) (_ : CommRing R'), Nonempty (R ≃+* R') :=
    ⟨ULift.{v, u} R, inferInstance, ⟨ULift.ringEquiv.symm⟩⟩
  let K' := ULift.{u, v} K
  let eK : K ≃+* K' := ULift.ringEquiv.symm
  have : IsLocalRing R' := eR.isLocalRing
  let : Algebra R R' := eR.toRingHom.toAlgebra
  let : Algebra R K' := ULift.algebra
  let : Algebra R' K := ((algebraMap R K).comp eR.symm.toRingHom).toAlgebra
  let : Algebra R' K' := ULift.algebra
  let : IsScalarTower R R' K :=
    IsScalarTower.of_algebraMap_eq (fun x ↦ by simp [RingHom.algebraMap_toAlgebra])
  have : IsLocalHom (algebraMap R' K') := by
    have : IsLocalHom eR.symm.toRingHom := IsLocalHom.of_surjective _ eR.symm.surjective
    have := RingHom.isLocalHom_comp (algebraMap R K) eR.symm.toRingHom
    exact RingHom.isLocalHom_comp eK.toRingHom ((algebraMap R K).comp eR.symm.toRingHom)
  obtain ⟨S, _, _, _, _, eqmap, ⟨e⟩⟩ := exists_isLocalHom_flat' R' K'
  let : Algebra R S := ((algebraMap R' S).comp eR.toRingHom).toAlgebra
  let : Module.Flat R R' := RingHom.Flat.of_bijective eR.bijective
  let : IsScalarTower R R' S := IsScalarTower.of_algebraMap_eq (fun x ↦ rfl)
  refine ⟨S, inferInstance, inferInstance, inferInstance, Module.Flat.trans R R' S, ?_, ?_⟩
  · rw [eqmap, ← map_maximalIdeal_of_surjective eR.toRingHom eR.surjective, Ideal.map_map]
    simp [RingHom.algebraMap_toAlgebra]
  · let eK' : K ≃ₐ[R] K' := {
      __ := eK
      commutes' r := rfl }
    exact ⟨eK'.trans (e.restrictScalars R)⟩
