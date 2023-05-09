import Mathlib.Algebra.Homology.HomotopyCategory.ShiftHomologyFunctorIso
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.Refinements

open CategoryTheory Category Limits Pretriangulated

variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

open HomologicalComplex

namespace MappingCone

attribute [simp] comp_liftCycles_assoc

lemma homology_triangle_exact {K L : CochainComplex C ℤ} (φ : K ⟶ L) (n : ℤ) :
  (ShortComplex.mk ((newHomologyFunctor _ _ n).map φ)
    ((newHomologyFunctor _ _ n).map (inr φ))
      (by dsimp ; rw [← homologyMap_comp, (homotopySelfCompInr φ).homologyMap_eq,
        homologyMap_zero])).Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  dsimp
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, z₂, hz₂, hz₂'⟩ :=
    L.eq_liftCycles_homologyπ_up_to_refinements x₂ (n+1) (by simp)
  have hz₂'' := hz₂' =≫ homologyMap (inr φ) n
  simp [hx₂] at hz₂''
  replace hz₂'' := hz₂''.symm
  rw [liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements
    _ _ _ _ _ (n-1) (by simp)] at hz₂''
  obtain ⟨A₂, π₂, hπ₂, x₃, hx₃⟩ := hz₂''
  obtain ⟨y₁, y₂, hy⟩ := to_break _ x₃ n (by rw [sub_add_cancel])
  simp [hy, to_ext_iff _ _ _ (n+1) rfl] at hx₃
  refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _,
    K.liftCycles' y₁ (n+1) (by simp) hx₃.1 ≫ K.homologyπ n, _⟩
  simp [hz₂', hx₃.2]
  rw [liftCycles_comp_homologyπ_eq_iff_up_to_refinements _ _ _ _ _ _ _ (n-1) (by simp)]
  refine' ⟨_, 𝟙 _, inferInstance, y₂, by simp⟩

end MappingCone

end CochainComplex

namespace HomotopyCategory

instance (n : ℤ) : (newHomologyFunctor C (ComplexShape.up ℤ) n).IsHomological :=
  Functor.IsHomological.mk' _ (by
    rintro T ⟨K, L, φ, ⟨e⟩⟩
    refine' ⟨_, e, _⟩
    refine' (ShortComplex.exact_iff_of_iso _).1
      (CochainComplex.MappingCone.homology_triangle_exact φ n)
    refine' ShortComplex.mkIso
      ((newHomologyFunctorFactors C (ComplexShape.up ℤ) n).app _).symm
      ((newHomologyFunctorFactors C (ComplexShape.up ℤ) n).app _).symm
      ((newHomologyFunctorFactors C (ComplexShape.up ℤ) n).app _).symm _ _
    all_goals
      dsimp
      erw [← NatTrans.naturality]
      rfl)

end HomotopyCategory
