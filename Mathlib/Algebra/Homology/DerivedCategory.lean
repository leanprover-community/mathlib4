import Mathlib.Algebra.Homology.HomotopyCategory.ShiftHomologyFunctorIso
import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.ShortComplex.Abelian

open CategoryTheory Category Limits

variable (C : Type _) [Category C] [Abelian C]

/-instance : IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ)) := sorry


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

end DerivedCategory-/

example : ℕ := 42
