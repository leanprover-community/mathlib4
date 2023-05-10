import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated

open CategoryTheory Category Limits Pretriangulated

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

namespace CochainComplex

namespace MappingCone

open HomComplex

@[simps! mor₁ mor₂ mor₃]
noncomputable def mappingConeCompTriangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (map' f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map' (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    (triangleδ g ≫ (inr f)⟦1⟧')

namespace MappingConeCompHomotopyEquiv

@[simp]
noncomputable def hom : mappingCone g ⟶ mappingCone (mappingConeCompTriangle f g).mor₁ :=
  lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_self 1)) sorry

lemma inv : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g := sorry

end MappingConeCompHomotopyEquiv

noncomputable def mappingConeCompHomotopyEquiv : HomotopyEquiv (mappingCone g)
    (mappingCone (mappingConeCompTriangle f g).mor₁) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := sorry
  homotopyInvHomId := sorry

lemma mappingConeCompHomotopyEquiv_comm₁ :
  inr (mappingConeCompTriangle f g).mor₁ ≫
    (mappingConeCompHomotopyEquiv f g).inv = (mappingConeCompTriangle f g).mor₂ := sorry

lemma mappingConeCompHomotopyEquiv_comm₂ :
  (mappingConeCompHomotopyEquiv f g).hom ≫
    triangleδ (mappingConeCompTriangle f g).mor₁ =
  (mappingConeCompTriangle f g).mor₃ := sorry

end MappingCone

end CochainComplex

namespace HomotopyCategory

lemma mappingConeCompTriangle_distinguished :
  (quotient _ _).mapTriangle.obj (CochainComplex.MappingCone.mappingConeCompTriangle f g) ∈
    distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := sorry

--attribute [local simp] CochainComplex.MappingCone.map'

instance : IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ)) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁ : CochainComplex C ℤ⟩ ⟨X₂ : CochainComplex C ℤ⟩ ⟨X₃ : CochainComplex C ℤ⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₂₃'
    have pif := mappingCone_triangle_distinguished u₁₂
    refine' ⟨_, _, _, _, _, _, _, _,
      Iso.refl _, Iso.refl _, Iso.refl _, by dsimp ; simp, by dsimp ; simp,
        _, _, mappingCone_triangle_distinguished u₁₂,
        _, _, mappingCone_triangle_distinguished u₂₃,
        _, _, mappingCone_triangle_distinguished (u₁₂ ≫ u₂₃), ⟨_⟩⟩
    let α := CochainComplex.MappingCone.triangleMap' u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw [id_comp])
    let β := CochainComplex.MappingCone.triangleMap' (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw [comp_id])
    apply Triangulated.Octahedron.mk ((HomotopyCategory.quotient _ _).map α.hom₃)
      ((HomotopyCategory.quotient _ _).map β.hom₃)
      ((quotient C (ComplexShape.up ℤ)).mapTriangle.map α).comm₂
      (((quotient C (ComplexShape.up ℤ)).mapTriangle.map α).comm₃.symm.trans
        (Eq.trans (by congr ; dsimp ; simp) (comp_id _)))
      (((HomotopyCategory.quotient _ _).mapTriangle.map β).comm₂.trans (id_comp _))
      (((HomotopyCategory.quotient _ _).mapTriangle.map β).comm₃)
    refine' isomorphic_distinguished _ (mappingConeCompTriangle_distinguished u₁₂ u₂₃) _ _
    refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _ _
    . dsimp
      simp
    . dsimp
      simp
    . dsimp
      erw [CategoryTheory.Functor.map_id, comp_id, id_comp, Functor.map_comp, assoc, assoc,
        ← NatTrans.naturality]
      rfl)

end HomotopyCategory
