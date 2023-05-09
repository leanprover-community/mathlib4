import Mathlib.Algebra.Homology.HomotopyCategory.ShiftHomologyFunctorIso
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

open CategoryTheory Category Limits Pretriangulated

variable (C : Type _) [Category C] [Abelian C]

instance : IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ)) := sorry

namespace HomotopyCategory

def subcategoryAcyclic :
    Triangulated.Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) :=
  Functor.homologicalKernel (newHomologyFunctor C (ComplexShape.up ℤ) 0)

lemma mem_subCategoryAcyclic_iff (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    X ∈ (subcategoryAcyclic C).set ↔ ∀ (n : ℤ), IsZero ((newHomologyFunctor _ _ n).obj X) := by
  dsimp [subcategoryAcyclic, Functor.homologicalKernel]
  simp only [← fun n => ((shiftFunctorHomologyIso C n 0 n (zero_add n)).app X).isZero_iff]
  rfl

def qis : MorphismProperty (HomotopyCategory C (ComplexShape.up ℤ)) := (subcategoryAcyclic C).W

lemma mem_qis_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    qis _ f ↔ ∀ (n : ℤ), IsIso ((newHomologyFunctor _ _ n).map f) := by
  dsimp only [qis, subcategoryAcyclic]
  rw [← Functor.IsHomological.W_eq_homologicalKernelW]
  dsimp only [Functor.IsHomological.W]
  simp only [← fun n => NatIso.isIso_map_iff ((shiftFunctorHomologyIso C n 0 n (zero_add n))) f]
  rfl

lemma mem_qis_iff' {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    qis C ((quotient _ _).map f) ↔
    ∀ (n : ℤ), IsIso ((HomologicalComplex.newHomologyFunctor _ _ n).map f) := by
  simp only [mem_qis_iff,
    ← fun n => NatIso.isIso_map_iff (newHomologyFunctorFactors C (ComplexShape.up ℤ) n) f]
  rfl

end HomotopyCategory

def DerivedCategory := (HomotopyCategory.qis C).Localization

namespace DerivedCategory

instance : Category (DerivedCategory C) := by
  dsimp only [DerivedCategory]
  infer_instance

noncomputable instance : Preadditive (DerivedCategory C) := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

noncomputable instance : HasShift (DerivedCategory C) ℤ := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

instance : HasZeroObject (DerivedCategory C) := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

instance (n : ℤ) : (shiftFunctor (DerivedCategory C) n).Additive := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

noncomputable instance : Pretriangulated (DerivedCategory C) := by
  dsimp only [DerivedCategory, HomotopyCategory.qis]
  infer_instance

variable {C}

def Qh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ DerivedCategory C :=
  MorphismProperty.Q _

instance : Qh.IsLocalization (HomotopyCategory.qis C) := by
  dsimp only [Qh, DerivedCategory]
  infer_instance

noncomputable instance : (Qh : _ ⥤ DerivedCategory C).HasCommShift ℤ := by
  dsimp only [Qh, DerivedCategory]
  infer_instance

instance : (Qh : _ ⥤ DerivedCategory C).IsTriangulated := by
  dsimp only [Qh, DerivedCategory, HomotopyCategory.qis]
  infer_instance

def Q : CochainComplex C ℤ ⥤ DerivedCategory C :=
  (HomotopyCategory.quotient _ _ ) ⋙ Qh

noncomputable instance : (Q : CochainComplex C ℤ ⥤ _).HasCommShift ℤ := by
  dsimp only [Q]
  infer_instance

@[reassoc]
lemma Q_commShiftIso_hom_app (X : CochainComplex C ℤ) (n : ℤ) :
    (Q.commShiftIso n).hom.app X =
      Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).hom.app X) ≫
        (Qh.commShiftIso n).hom.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) :=
  by apply Functor.commShiftIso_comp_hom_app

@[reassoc]
lemma Q_commShiftIso_inv_app (X : CochainComplex C ℤ) (n : ℤ) :
    (Q.commShiftIso n).inv.app X =
      (Qh.commShiftIso n).inv.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) ≫
      Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).inv.app X) :=
  by apply Functor.commShiftIso_comp_inv_app

@[reassoc]
lemma Qh_commShiftIso_hom_app (X : CochainComplex C ℤ) (n : ℤ) :
    Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).hom.app X) =
      (Q.commShiftIso n).hom.app X ≫
        (Qh.commShiftIso n).inv.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) := by
  simp only [Q_commShiftIso_hom_app, Functor.comp_obj, assoc, Iso.hom_inv_id_app, comp_id]

@[reassoc]
lemma Qh_commShiftIso_inv_app (X : CochainComplex C ℤ) (n : ℤ) :
    (Qh.commShiftIso n).inv.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) =
      (Q.commShiftIso n).inv.app X ≫
      Qh.map (((HomotopyCategory.quotient C _).commShiftIso n).hom.app X) := by
  simp only [Q_commShiftIso_inv_app, assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    Functor.comp_obj, Paths.of_obj, CategoryTheory.Functor.map_id, comp_id]

lemma isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.qis C f := by
  constructor
  . intro hf
    sorry
  . intro hf
    exact Localization.inverts Qh (HomotopyCategory.qis C) _ hf

lemma isIso_Q_map_iff {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    IsIso (Q.map φ) ↔
      ∀ (n : ℤ), IsIso ((HomologicalComplex.newHomologyFunctor C _ n).map φ) := by
  dsimp only [Q, Functor.comp]
  rw [← HomotopyCategory.mem_qis_iff', isIso_Qh_map_iff]

-- this will appear in Algebra.Homology.HomotopyCategory.ShortExact
noncomputable def _root_.CochainComplex.MappingCone.fromOfShortComplex (S : ShortComplex (CochainComplex C ℤ)):
  CochainComplex.mappingCone S.f ⟶ S.X₃ := CochainComplex.MappingCone.desc S.f 0 S.g (by simp)
lemma _root_.CochainComplex.MappingCone.isIso_homologyMap_fromOfShortComplex
  {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (CochainComplex.MappingCone.fromOfShortComplex S) n) := sorry

section

variable {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)

lemma isIso_Q_map_fromOfShortComplex :
    IsIso (Q.map (CochainComplex.MappingCone.fromOfShortComplex S)) := by
  rw [isIso_Q_map_iff]
  exact CochainComplex.MappingCone.isIso_homologyMap_fromOfShortComplex hS

noncomputable def triangleOfSESδ :
  Q.obj (S.X₃) ⟶ (Q.obj S.X₁)⟦(1 : ℤ)⟧ :=
    have := isIso_Q_map_fromOfShortComplex hS
    inv (Q.map (CochainComplex.MappingCone.fromOfShortComplex S)) ≫
      Q.map (CochainComplex.MappingCone.triangleδ S.f) ≫
      (Q.commShiftIso (1 : ℤ)).hom.app S.X₁

noncomputable def triangleOfSES : Triangle (DerivedCategory C) :=
  Triangle.mk (Q.map S.f) (Q.map S.g) (triangleOfSESδ hS)

lemma triangleOfSES_distinguished :
  triangleOfSES hS ∈ distTriang (DerivedCategory C) := sorry

end


end DerivedCategory
