/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Flat is stable under filtered colimits
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TensorProduct

namespace CategoryTheory

lemma ObjectProperty.ind_inverseImage_le
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) (P : ObjectProperty D)
    [PreservesFilteredColimitsOfSize.{w, w} F] :
    ind.{w} (P.inverseImage F) ≤ (ind.{w} P).inverseImage F := by
  intro X ⟨J, _, _, pres, h⟩
  simp only [prop_inverseImage_iff]
  use J, inferInstance, inferInstance, pres.map F, h

end CategoryTheory

lemma Module.FaithfullyFlat.of_nontrivial_tensor_quotient
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (H : ∀ (m : Ideal R), m.IsMaximal → Nontrivial ((R ⧸ m) ⊗[R] M)) :
    Module.FaithfullyFlat R M where
  submodule_ne_top m hm := by
    rw [ne_eq, ← Submodule.Quotient.subsingleton_iff, not_subsingleton_iff_nontrivial,
      (TensorProduct.quotTensorEquivQuotSMul M m).symm.nontrivial_congr]
    exact H m hm

section

variable (R : Type u) [CommRing R]

instance : PreservesFilteredColimitsOfSize.{u, u, u, u, u + 1, u + 1}
    (forget₂ (CommAlgCat R) (AlgCat R)) :=
  sorry

instance : PreservesFilteredColimitsOfSize.{u, u, u, u, u + 1, u + 1}
    (forget₂ (AlgCat R) (ModuleCat R)) :=
  sorry

instance : PreservesFilteredColimits.{u}
    (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}) :=
  sorry

set_option backward.isDefEq.respectTransparency false in
instance preservesColimitsOfShape_tensorLeft
    {J : Type*} [Category J] [IsFiltered J] (M : CommAlgCat R) :
    PreservesColimitsOfShape J (MonoidalCategory.tensorLeft M) := by
  sorry

end

namespace ModuleCat

/-- The object property of flat modules. -/
def flat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.Flat R M

variable (R : Type u) [CommRing R]

@[simp]
lemma flat_iff (M : ModuleCat R) : flat R M ↔ Module.Flat R M :=
  .rfl

/-- The object property of faithfully flat modules. -/
def faithfullyFlat (R : Type*) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.FaithfullyFlat R M

@[simp]
lemma faithfullyFlat_iff (M : ModuleCat R) : faithfullyFlat R M ↔ Module.FaithfullyFlat R M :=
  .rfl

variable {R} in
open MonoidalCategory in
lemma flat_of_colimitPresentation {M : ModuleCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J M)
    (h : ∀ j, Module.Flat R (pres.diag.obj j)) :
    Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]
  intro C hC
  let S : ShortComplex (J ⥤ ModuleCat.{u} R) :=
    { X₁ := pres.diag ⋙ tensorRight C.X₁
      X₂ := pres.diag ⋙ tensorRight C.X₂
      X₃ := pres.diag ⋙ tensorRight C.X₃
      f := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.f
      g := pres.diag.whiskerLeft <| (curriedTensor (ModuleCat.{u} R)).flip.map C.g
      zero := by simp [← CategoryTheory.Functor.whiskerLeft_comp, ← Functor.map_comp, C.zero] }
  apply colim.exact_mapShortComplex (S := S)
      (hc₁ := isColimitOfPreserves _ pres.isColimit)
      (hc₂ := isColimitOfPreserves _ pres.isColimit)
      (hc₃ := isColimitOfPreserves _ pres.isColimit)
  · rw [CategoryTheory.ShortComplex.exact_iff_evaluation]
    intro j
    exact Module.Flat.lTensor_shortComplex_exact (pres.diag.obj j) C hC
  · simp [S, whisker_exchange]
  · simp [S, whisker_exchange]

@[simp]
lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  refine le_antisymm (fun M ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  exact flat_of_colimitPresentation pres h

end ModuleCat

namespace CommAlgCat

variable {R : Type u} [CommRing R]

/-- The object property of flat `R`-algebras. -/
def flat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.flat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)

@[simp]
lemma flat_iff {S : CommAlgCat R} : flat R S ↔ Module.Flat R S := .rfl

lemma ind_flat : ObjectProperty.ind.{u} (flat.{u} R) = flat.{u} R := by
  refine le_antisymm ?_ (ObjectProperty.le_ind _)
  rw [flat]
  refine le_trans (ObjectProperty.ind_inverseImage_le _ _) ?_
  rw [ModuleCat.ind_flat]

/-- The object property of faithfully-flat `R`-algebras. -/
def faithfullyFlat (R : Type u) [CommRing R] : ObjectProperty (CommAlgCat.{w} R) :=
  (ModuleCat.faithfullyFlat R).inverseImage (forget₂ _ (AlgCat R) ⋙ forget₂ _ _)

@[simp]
lemma faithfullyFlat_iff {S : CommAlgCat R} :
    faithfullyFlat R S ↔ Module.FaithfullyFlat R S := .rfl

lemma faithfullyFlat_of_colimitPresentation {S : CommAlgCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J S)
    (h : ∀ j, Module.FaithfullyFlat R (pres.diag.obj j)) :
    Module.FaithfullyFlat R S := by
  have : Module.Flat R S := by
    rw [← flat_iff, flat, ObjectProperty.inverseImage, ← ModuleCat.ind_flat R,
      ← ObjectProperty.prop_inverseImage_iff (ModuleCat.flat.{u} R).ind]
    refine ObjectProperty.ind_inverseImage_le _ _ _ ⟨J, ‹_›, ‹_›, pres, fun j ↦ ?_⟩
    exact (h j).1
  refine Module.FaithfullyFlat.of_nontrivial_tensor_quotient fun m hm ↦ ?_
  let qpres : ColimitPresentation J (CommAlgCat.of R <| (R ⧸ m) ⊗[R] S) :=
    pres.map <| MonoidalCategory.tensorLeft (CommAlgCat.of R (R ⧸ m))
  have (j : J) : Nontrivial ((qpres.diag ⋙ forget₂ (CommAlgCat R) CommRingCat).obj j) := by
    simp only [ColimitPresentation.map_diag, Functor.comp_obj,
      MonoidalCategory.curriedTensor_obj_obj, forget₂_commRingCat_obj, coe_tensorObj,
      Module.FaithfullyFlat.nontrivial_tensorProduct_iff_left, qpres]
    infer_instance
  change Nontrivial ((forget₂ _ CommRingCat).mapCocone qpres.cocone).pt
  exact CommRingCat.FilteredColimits.nontrivial (isColimitOfPreserves _ qpres.isColimit)

lemma ind_faithfullyFlat :
    ObjectProperty.ind.{u} (faithfullyFlat.{u} R) = faithfullyFlat.{u} R := by
  refine le_antisymm (fun S ⟨J, _, _, pres, h⟩ ↦ ?_) (ObjectProperty.le_ind _)
  exact faithfullyFlat_of_colimitPresentation pres h

end CommAlgCat
