import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.IsLE
import Mathlib.CategoryTheory.Triangulated.Subcategory

open CategoryTheory Category Limits Triangulated ZeroObject Pretriangulated

variable (C : Type _) [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {D : Type _} [Category D] [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D]
  (A : Type _) [Category A] [Abelian A]

namespace HomotopyCategory

def subcategoryPlus : Subcategory (HomotopyCategory C (ComplexShape.up ℤ)) where
  set K := ∃ (n : ℤ), CochainComplex.IsStrictlyGE K.1 n
  zero' := by
    refine' ⟨⟨0⟩, _, ⟨0, _⟩⟩
    · change IsZero ((quotient _ _).obj 0)
      rw [IsZero.iff_id_eq_zero, ← (quotient _ _).map_id, id_zero, Functor.map_zero]
    · dsimp
      infer_instance
  shift := by
    rintro ⟨X : CochainComplex C ℤ⟩ n ⟨k, _ : X.IsStrictlyGE k⟩
    refine' ⟨k - n, _⟩
    erw [Quotient.functor_obj_shift]
    exact X.isStrictlyGE_shift k n (k - n) (by linarith)
  ext₂' T hT := by
    rintro ⟨n₁, _⟩ ⟨n₃, _⟩
    obtain ⟨f : T.obj₃.as ⟶ T.obj₁.as⟦(1 : ℤ)⟧, hf⟩ := (quotient _ _ ).map_surjective
      (T.mor₃ ≫ ((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).inv.app T.obj₁.as)
    let T₁ := T.rotate.rotate
    have hT₁ : T₁ ∈ distTriang _ := rot_of_distTriang _ (rot_of_distTriang _ hT)
    let T₂ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
      (CochainComplex.mappingCone.triangle f)
    have hT₂ : T₂ ∈ distTriang _ := by exact ⟨_, _, f, ⟨Iso.refl _⟩⟩
    have e := isoTriangleOfIso₁₂ T₁ T₂ hT₁ hT₂ (Iso.refl _)
      (((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).symm.app T.obj₁.as)
      (by dsimp; rw [id_comp, hf])
    refine' ⟨(quotient C (ComplexShape.up ℤ)).obj ((shiftFunctor (CochainComplex C ℤ) (-1)).obj
      (CochainComplex.mappingCone f)), _, ⟨_⟩⟩
    · let n₀ : ℤ := min n₁ n₃ - 1
      have := min_le_left n₁ n₃
      have := min_le_right n₁ n₃
      have : (CochainComplex.mappingCone f).IsStrictlyGE n₀ := ⟨fun i hi => by
        simp only [CochainComplex.mappingCone.isZero_X_iff]
        constructor
        · exact CochainComplex.isZero_of_isStrictlyGE T.obj₃.as n₃ (i + 1)
            (by dsimp at hi; linarith)
        · exact CochainComplex.isZero_of_isStrictlyGE T.obj₁.as n₁ (i + 1)
            (by dsimp at hi; linarith)⟩
      exact ⟨_,
        (CochainComplex.mappingCone f).isStrictlyGE_shift n₀ (-1) (n₀ + 1) (by linarith)⟩
    · exact (shiftEquiv _ (1 : ℤ)).unitIso.app T.obj₂ ≪≫
        (shiftFunctor _ (-1)).mapIso (Triangle.π₃.mapIso e) ≪≫
        ((quotient _ _).commShiftIso (-1)).symm.app (CochainComplex.mappingCone f)

abbrev Plus := (subcategoryPlus C).category

namespace Plus

abbrev ι : Plus C ⥤ HomotopyCategory C (ComplexShape.up ℤ) := (subcategoryPlus C).ι

def qis : MorphismProperty (Plus A) := (HomotopyCategory.qis A _).inverseImage (ι A)

instance : (qis A).IsMultiplicative := by
  dsimp only [qis]
  infer_instance

end Plus

end HomotopyCategory

namespace CategoryTheory

namespace Functor

variable {C}
variable (F : C ⥤ D) [F.Additive]

def mapHomotopyCategoryPlus : HomotopyCategory.Plus C ⥤ HomotopyCategory.Plus D :=
  (HomotopyCategory.subcategoryPlus D).lift
    (HomotopyCategory.Plus.ι C ⋙ F.mapHomotopyCategory (ComplexShape.up ℤ)) (by
      rintro ⟨X, ⟨n, _⟩⟩
      refine' ⟨n, _⟩
      dsimp [HomotopyCategory.Plus.ι, Subcategory.ι, HomotopyCategory.quotient, Quotient.functor]
      infer_instance)

noncomputable instance : (F.mapHomotopyCategoryPlus).CommShift ℤ := by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance

instance : (F.mapHomotopyCategoryPlus).IsTriangulated := by
  dsimp only [mapHomotopyCategoryPlus]
  infer_instance

noncomputable instance [Full F] [Faithful F] : Full F.mapHomotopyCategoryPlus where
  preimage f := (F.mapHomotopyCategory _).preimage f
  witness f := (F.mapHomotopyCategory _).image_preimage f

noncomputable instance [Full F] [Faithful F] : Faithful F.mapHomotopyCategoryPlus where
  map_injective h := (F.mapHomotopyCategory _).map_injective h

end Functor

end CategoryTheory
