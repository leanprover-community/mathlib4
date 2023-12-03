/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.Single
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
/-!
# The homology of single complexes

The main definition in this file is `HomologicalComplex.homologyFunctorSingleIso`
which is a natural isomorphism `single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`.

-/

universe v u

open CategoryTheory Category Limits ZeroObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

namespace HomologicalComplex

variable (A : C)

instance (i : ι) : ((single C c j).obj A).HasHomology i := by
  apply ShortComplex.hasHomology_of_zeros

lemma exactAt_single_obj (A : C) (i : ι) (hi : i ≠ j) :
    ExactAt ((single C c j).obj A) i :=
  ShortComplex.exact_of_isZero_X₂ _ (isZero_single_obj_X c _ _ _ hi)

lemma isZero_single_obj_homology (A : C) (i : ι) (hi : i ≠ j) :
    IsZero (((single C c j).obj A).homology i) := by
  simpa only [← exactAt_iff_isZero_homology]
    using exactAt_single_obj c j A i hi

/-- The canonical isomorphism `((single C c j).obj A).cycles j ≅ A` -/
noncomputable def singleObjCyclesSelfIso :
    ((single C c j).obj A).cycles j ≅ A :=
  ((single C c j).obj A).iCyclesIso j _ rfl rfl ≪≫ singleObjXSelf c j A

@[reassoc]
lemma singleObjCyclesSelfIso_hom :
    (singleObjCyclesSelfIso c j A).hom =
      ((single C c j).obj A).iCycles j ≫ (singleObjXSelf c j A).hom := rfl

/-- The canonical isomorphism `((single C c j).obj A).opcycles j ≅ A` -/
noncomputable def singleObjOpcyclesSelfIso :
    A ≅ ((single C c j).obj A).opcycles j :=
  (singleObjXSelf c j A).symm ≪≫ ((single C c j).obj A).pOpcyclesIso _ j rfl rfl

@[reassoc]
lemma singleObjOpcyclesSelfIso_hom :
    (singleObjOpcyclesSelfIso c j A).hom =
      (singleObjXSelf c j A).inv ≫ ((single C c j).obj A).pOpcycles j := rfl

/-- The canonical isomorphism `((single C c j).obj A).homology j ≅ A` -/
noncomputable def singleObjHomologySelfIso :
    ((single C c j).obj A).homology j ≅ A :=
  (((single C c j).obj A).isoHomologyπ _ j rfl rfl).symm ≪≫ singleObjCyclesSelfIso c j A

@[reassoc (attr := simp)]
lemma singleObjCyclesSelfIso_inv_iCycles :
    (singleObjCyclesSelfIso _ _ _).inv ≫ ((single C c j).obj A).iCycles j =
      (singleObjXSelf c j A).inv := by
  simp [singleObjCyclesSelfIso]

@[reassoc (attr := simp)]
lemma homologyπ_singleObjHomologySelfIso_hom :
    ((single C c j).obj A).homologyπ j ≫ (singleObjHomologySelfIso _ _ _).hom =
      (singleObjCyclesSelfIso _ _ _).hom := by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]
lemma singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv :
    (singleObjCyclesSelfIso c j A).hom ≫ (singleObjHomologySelfIso c j A).inv =
      ((single C c j).obj A).homologyπ j := by
  simp only [← cancel_mono (singleObjHomologySelfIso _ _ _).hom, assoc,
    Iso.inv_hom_id, comp_id, homologyπ_singleObjHomologySelfIso_hom]

@[reassoc (attr := simp)]
lemma singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (singleObjCyclesSelfIso c j A).hom ≫ (singleObjOpcyclesSelfIso c j A).hom =
      ((single C c j).obj A).iCycles j ≫ ((single C c j).obj A).pOpcycles j := by
  simp [singleObjCyclesSelfIso, singleObjOpcyclesSelfIso]

@[reassoc (attr := simp)]
lemma singleObjCyclesSelfIso_inv_homologyπ  :
    (singleObjCyclesSelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyπ j =
      (singleObjHomologySelfIso _ _ _).inv := by
  simp [singleObjCyclesSelfIso, singleObjHomologySelfIso]

@[reassoc (attr := simp)]
lemma singleObjHomologySelfIso_inv_homologyι :
    (singleObjHomologySelfIso _ _ _).inv ≫ ((single C c j).obj A).homologyι j =
      (singleObjOpcyclesSelfIso _ _ _).hom := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom,
    singleObjHomologySelfIso_hom_singleObjHomologySelfIso_inv_assoc, homology_π_ι,
    singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom]

@[reassoc (attr := simp)]
lemma homologyι_singleObjOpcyclesSelfIso_inv :
    ((single C c j).obj A).homologyι j ≫ (singleObjOpcyclesSelfIso _ _ _).inv =
      (singleObjHomologySelfIso _ _ _).hom := by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv,
    singleObjHomologySelfIso_inv_homologyι_assoc, Iso.hom_inv_id, Iso.inv_hom_id]

@[reassoc (attr := simp)]
lemma singleObjHomologySelfIso_hom_singleObjOpcyclesSelfIso_hom :
    (singleObjHomologySelfIso _ _ _).hom ≫ (singleObjOpcyclesSelfIso _ _ _).hom =
      ((single C c j).obj A).homologyι j := by
  rw [← cancel_epi (singleObjHomologySelfIso _ _ _).inv,
    Iso.inv_hom_id_assoc, singleObjHomologySelfIso_inv_homologyι]

variable {A}
variable {B : C} (f : A ⟶ B)

@[reassoc (attr := simp)]
lemma singleObjCyclesSelfIso_hom_naturality :
    cyclesMap ((single C c j).map f) j ≫ (singleObjCyclesSelfIso c j B).hom =
      (singleObjCyclesSelfIso c j A).hom ≫ f := by
  rw [← cancel_mono (singleObjCyclesSelfIso c j B).inv, assoc, assoc, Iso.hom_inv_id, comp_id,
    ← cancel_mono (iCycles _ _)]
  simp only [cyclesMap_i, singleObjCyclesSelfIso, Iso.trans_hom, iCyclesIso_hom, Iso.trans_inv,
    assoc, iCyclesIso_inv_hom_id, comp_id, single_map_f_self]

@[reassoc (attr := simp)]
lemma singleObjCyclesSelfIso_inv_naturality :
    (singleObjCyclesSelfIso c j A).inv ≫ cyclesMap ((single C c j).map f) j =
      f ≫ (singleObjCyclesSelfIso c j B).inv := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom, Iso.hom_inv_id_assoc,
    ← singleObjCyclesSelfIso_hom_naturality_assoc, Iso.hom_inv_id, comp_id]

@[reassoc (attr := simp)]
lemma singleObjHomologySelfIso_hom_naturality :
    homologyMap ((single C c j).map f) j ≫ (singleObjHomologySelfIso c j B).hom =
      (singleObjHomologySelfIso c j A).hom ≫ f := by
  rw [← cancel_epi (((single C c j).obj A).homologyπ j),
    homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom_naturality, homologyπ_singleObjHomologySelfIso_hom_assoc]

@[reassoc (attr := simp)]
lemma singleObjHomologySelfIso_inv_naturality :
    (singleObjHomologySelfIso c j A).inv ≫ homologyMap ((single C c j).map f) j =
      f ≫ (singleObjHomologySelfIso c j B).inv := by
  rw [← cancel_mono (singleObjHomologySelfIso c j B).hom, assoc, assoc,
    singleObjHomologySelfIso_hom_naturality,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, comp_id]

@[reassoc (attr := simp)]
lemma singleObjOpcyclesSelfIso_hom_naturality :
    (singleObjOpcyclesSelfIso c j A).hom ≫ opcyclesMap ((single C c j).map f) j  =
      f ≫ (singleObjOpcyclesSelfIso c j B).hom := by
  rw [← cancel_epi (singleObjCyclesSelfIso c j A).hom,
    singleObjCyclesSelfIso_hom_singleObjOpcyclesSelfIso_hom_assoc, p_opcyclesMap,
    single_map_f_self, assoc, assoc, singleObjCyclesSelfIso_hom,
    singleObjOpcyclesSelfIso_hom, assoc]

@[reassoc (attr := simp)]
lemma singleObjOpcyclesSelfIso_inv_naturality :
    opcyclesMap ((single C c j).map f) j ≫ (singleObjOpcyclesSelfIso c j B).inv =
      (singleObjOpcyclesSelfIso c j A).inv ≫ f := by
  rw [← cancel_mono (singleObjOpcyclesSelfIso c j B).hom, assoc, assoc, Iso.inv_hom_id,
    comp_id, ← singleObjOpcyclesSelfIso_hom_naturality, Iso.inv_hom_id_assoc]

variable (C)

/-- The computation of the homology of single complexes, as a natural isomorphism
`single C c j ⋙ homologyFunctor C c j ≅ 𝟭 C`. -/
@[simps!]
noncomputable def homologyFunctorSingleIso [CategoryWithHomology C] :
    single C c j ⋙ homologyFunctor C c j ≅ 𝟭 _ :=
  NatIso.ofComponents (fun A => (singleObjHomologySelfIso c j A))
    (fun f => singleObjHomologySelfIso_hom_naturality c j f)

end HomologicalComplex

variable (C)

namespace ChainComplex

variable [HasEqualizers C] [HasCokernels C] [HasImages C] [HasImageMaps C]

/-- Sending objects to chain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homology'Functor0Single₀ : single₀ C ⋙ homology'Functor C _ 0 ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => homology'.congr _ _ (by simp) (by simp) ≪≫ homology'ZeroZero)
    fun f => by
      -- Porting note: why can't `aesop_cat` do this?
      dsimp
      ext
      simp
#align chain_complex.homology_functor_0_single₀ ChainComplex.homology'Functor0Single₀

/-- Sending objects to chain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homology'FunctorSuccSingle₀ (n : ℕ) :
    single₀ C ⋙ homology'Functor C _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology'.congr _ _ (by simp) (by simp) ≪≫
        homology'ZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun f => (Functor.zero_obj _).eq_of_tgt _ _
#align chain_complex.homology_functor_succ_single₀ ChainComplex.homology'FunctorSuccSingle₀

end ChainComplex

namespace CochainComplex

variable [HasEqualizers C] [HasCokernels C] [HasImages C] [HasImageMaps C]

/-- Sending objects to cochain complexes supported at `0` then taking `0`-th homology
is the same as doing nothing.
-/
noncomputable def homologyFunctor0Single₀ : single₀ C ⋙ homology'Functor C _ 0 ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => homology'.congr _ _ (by simp) (by simp) ≪≫ homology'ZeroZero)
    fun f => by
      -- Porting note: why can't `aesop_cat` do this?
      dsimp
      ext
      simp
#align cochain_complex.homology_functor_0_single₀ CochainComplex.homologyFunctor0Single₀

/-- Sending objects to cochain complexes supported at `0` then taking `(n+1)`-st homology
is the same as the zero functor.
-/
noncomputable def homology'FunctorSuccSingle₀ (n : ℕ) :
    single₀ C ⋙ homology'Functor C _ (n + 1) ≅ 0 :=
  NatIso.ofComponents
    (fun X =>
      homology'.congr _ _ (by simp) (by simp) ≪≫
        homology'ZeroZero ≪≫ (Functor.zero_obj _).isoZero.symm)
    fun f => (Functor.zero_obj _).eq_of_tgt _ _
#align cochain_complex.homology_functor_succ_single₀ CochainComplex.homology'FunctorSuccSingle₀

end CochainComplex

namespace ChainComplex

open HomologicalComplex

variable {C}

lemma exactAt_succ_single_obj (A : C) (n : ℕ) :
    ExactAt ((single₀ C).obj A) (n + 1) :=
  exactAt_single_obj _ _ _ _ (by simp)

end ChainComplex

namespace CochainComplex

open HomologicalComplex

variable {C}

lemma exactAt_succ_single_obj (A : C) (n : ℕ) :
    ExactAt ((single₀ C).obj A) (n + 1) :=
  exactAt_single_obj _ _ _ _ (by simp)

end CochainComplex
