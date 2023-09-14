import Mathlib.Algebra.Homology.HomotopyCategory.Plus
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

open CategoryTheory Triangulated

variable {C : Type*} [Category C] [Abelian C]
  [HasDerivedCategory C]

namespace DerivedCategory

open TStructure

namespace Plus

def Qh : HomotopyCategory.Plus C ⥤ Plus C :=
  t.plus.lift (HomotopyCategory.Plus.ι _ ⋙ DerivedCategory.Qh) (by
    rintro ⟨⟨X⟩, n, h⟩
    dsimp at h
    have : (DerivedCategory.Q.obj X).IsGE n := inferInstance
    refine' ⟨n, ⟨_⟩⟩
    dsimp [t]
    change (DerivedCategory.Q.obj X).IsGE n
    infer_instance)

noncomputable instance : (Qh : _ ⥤ Plus C).CommShift ℤ := by
  dsimp only [Qh]
  infer_instance

instance : (Qh : _ ⥤ Plus C).IsTriangulated := by
  dsimp only [Qh]
  infer_instance

lemma Qh_map_bijective_of_isKInjective (K L : HomotopyCategory.Plus C)
    (_ : CochainComplex.IsKInjective L.1.as) : Function.Bijective (Qh.map : (K ⟶ L) → _) :=
  CochainComplex.Qh_map_bijective_of_isKInjective K.1 L.1.as

end Plus


end DerivedCategory
