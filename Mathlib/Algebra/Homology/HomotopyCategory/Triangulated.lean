/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.ComposableArrows

/-! The triangulated structure on the homotopy category of complexes

In this file, we show that for any additive category `C`,
the pretriangulated category `HomotopyCategory C (ComplexShape.up ℤ)` is triangulated.

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Pretriangulated ComposableArrows

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe v

variable {C : Type*} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {X₁ X₂ X₃ : CochainComplex C ℤ} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)

namespace CochainComplex

open HomComplex mappingCone

/-- Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`. -/
@[simps! mor₁ mor₂ mor₃ obj₁ obj₂ obj₃]
noncomputable def mappingConeCompTriangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp]))
    (map (f ≫ g) g f (𝟙 X₃) (by rw [comp_id]))
    ((triangle g).mor₃ ≫ (inr f)⟦1⟧')

/-- Given two composable morphisms `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` in the category
of cochain complexes, this is the canonical triangle
`mappingCone f ⟶ mappingCone (f ≫ g) ⟶ mappingCone g ⟶ (mappingCone f)⟦1⟧`
in the homotopy category. It is a distinguished triangle,
see `HomotopyCategory.mappingConeCompTriangleh_distinguished`. -/
noncomputable def mappingConeCompTriangleh :
    Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient _ _).mapTriangle.obj (mappingConeCompTriangle f g)

@[reassoc]
lemma mappingConeCompTriangle_mor₃_naturality {Y₁ Y₂ Y₃ : CochainComplex C ℤ} (f' : Y₁ ⟶ Y₂)
    (g' : Y₂ ⟶ Y₃) (φ : mk₂ f g ⟶ mk₂ f' g') :
    map g g' (φ.app 1) (φ.app 2) (naturality' φ 1 2) ≫ (mappingConeCompTriangle f' g').mor₃ =
      (mappingConeCompTriangle f g).mor₃ ≫
        (map f f' (φ.app 0) (φ.app 1) (naturality' φ 0 1))⟦1⟧' := by
  ext n
  dsimp [map]
  -- the following list of lemmas was obtained by doing simp? [ext_from_iff _ (n + 1) _ rfl]
  simp only [Int.reduceNeg, Fin.isValue, assoc, inr_f_desc_f, HomologicalComplex.comp_f,
    ext_from_iff _ (n + 1) _ rfl, inl_v_desc_f_assoc, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    inl_v_triangle_mor₃_f_assoc, triangle_obj₁, shiftFunctor_obj_X', shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.neg_comp,
    id_comp, Preadditive.comp_neg, inr_f_desc_f_assoc, inr_f_triangle_mor₃_f_assoc, zero_comp,
    comp_zero, and_self]

namespace MappingConeCompHomotopyEquiv

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes, this
is the canonical morphism (which is an homotopy equivalence) from `mappingCone g` to
the mapping cone of the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
noncomputable def hom :
    mappingCone g ⟶ mappingCone (mappingConeCompTriangle f g).mor₁ :=
  lift _ (descCocycle g (Cochain.ofHom (inr f)) 0 (zero_add 1) (by simp))
    (descCochain _ 0 (Cochain.ofHom (inr (f ≫ g))) (neg_add_cancel 1)) (by
      ext p _ rfl
      dsimp [mappingConeCompTriangle, map]
      simp [ext_from_iff _ _ _ rfl, inl_v_d_assoc _ (p+1) p (p+2) (by omega) (by omega)])

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes, this
is the canonical morphism (which is an homotopy equivalence) from the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)` to `mappingCone g`. -/
noncomputable def inv : mappingCone (mappingConeCompTriangle f g).mor₁ ⟶ mappingCone g :=
  desc _ ((snd f).comp (inl g) (zero_add (-1)))
    (desc _ ((Cochain.ofHom f).comp (inl g) (zero_add (-1))) (inr g) (by simp)) (by
      ext p
      rw [ext_from_iff _ (p + 1) _ rfl, ext_to_iff _ _ (p + 1) rfl]
      simp [map, δ_zero_cochain_comp,
        Cochain.comp_v _ _ (add_neg_cancel 1) p (p+1) p (by omega) (by omega)])
@[reassoc (attr := simp)]
lemma hom_inv_id : hom f g ≫ inv f g = 𝟙 _ := by
  ext n
  simp [hom, inv, lift_desc_f _ _ _ _ _ _ _ n (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the `homotopyInvHomId` field of the homotopy equivalence
`mappingConeCompHomotopyEquiv f g` between `mappingCone g` and the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
noncomputable def homotopyInvHomId : Homotopy (inv f g ≫ hom f g) (𝟙 _) :=
  (Cochain.equivHomotopy _ _).symm ⟨-((snd _).comp ((fst (f ≫ g)).1.comp
    ((inl f).comp (inl _) (by decide)) (show 1 + (-2) = -1 by decide)) (zero_add (-1))), by
      rw [δ_neg, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
        Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
        δ_comp _ _ (show 1 + (-2) = -1 by decide) 2 (-1) 0 (by decide)
          (by decide) (by decide),
        δ_comp _ _ (show (-1) + (-1) = -2 by decide) 0 0 (-1) (by decide)
          (by decide) (by decide), Int.negOnePow_neg, Int.negOnePow_neg,
        Int.negOnePow_even 2 ⟨1, by decide⟩, Int.negOnePow_one, Units.neg_smul,
        one_smul, one_smul, δ_inl, δ_inl, δ_snd, Cocycle.δ_eq_zero, Cochain.zero_comp, add_zero,
        Cochain.neg_comp, neg_neg]
      ext n
      rw [ext_from_iff _ (n + 1) n rfl, ext_from_iff _ (n + 1) n rfl,
        ext_from_iff _ (n + 2) (n + 1) (by omega)]
      dsimp [hom, inv]
      simp [ext_to_iff _ n (n + 1) rfl, map, Cochain.comp_v _ _
          (add_neg_cancel 1) n (n + 1) n (by omega) (by omega),
        Cochain.comp_v _ _ (show 1 + -2 = -1 by decide) (n + 1) (n + 2) n
          (by omega) (by omega),
        Cochain.comp_v _ _ (show (-1) + -1 = -2 by decide) (n + 2) (n + 1) n
          (by omega) (by omega)]⟩

end MappingConeCompHomotopyEquiv

/-- Given two composable morphisms `f` and `g` in the category of cochain complexes,
this is the homotopy equivalence `mappingConeCompHomotopyEquiv f g`
between `mappingCone g` and the mapping cone of
the morphism `mappingCone f ⟶ mappingCone (f ≫ g)`. -/
noncomputable def mappingConeCompHomotopyEquiv : HomotopyEquiv (mappingCone g)
    (mappingCone (mappingConeCompTriangle f g).mor₁) where
  hom := MappingConeCompHomotopyEquiv.hom f g
  inv := MappingConeCompHomotopyEquiv.inv f g
  homotopyHomInvId := Homotopy.ofEq (by simp)
  homotopyInvHomId := MappingConeCompHomotopyEquiv.homotopyInvHomId f g

@[reassoc (attr := simp)]
lemma mappingConeCompHomotopyEquiv_hom_inv_id :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (mappingConeCompHomotopyEquiv f g).inv = 𝟙 _ := by
  simp [mappingConeCompHomotopyEquiv]

@[reassoc]
lemma mappingConeCompHomotopyEquiv_comm₁ :
    inr (map f (f ≫ g) (𝟙 X₁) g (by rw [id_comp])) ≫
      (mappingConeCompHomotopyEquiv f g).inv = (mappingConeCompTriangle f g).mor₂ := by
  simp [map, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.inv]

@[reassoc]
lemma mappingConeCompHomotopyEquiv_comm₂ :
    (mappingConeCompHomotopyEquiv f g).hom ≫
      (triangle (mappingConeCompTriangle f g).mor₁).mor₃ =
      (mappingConeCompTriangle f g).mor₃ := by
  ext n
  simp [map, mappingConeCompHomotopyEquiv, MappingConeCompHomotopyEquiv.hom,
    lift_f _ _ _ _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl]

@[reassoc (attr := simp)]
lemma mappingConeCompTriangleh_comm₁ :
    (mappingConeCompTriangleh f g).mor₂ ≫
      (HomotopyCategory.quotient _ _).map (mappingConeCompHomotopyEquiv f g).hom =
    (HomotopyCategory.quotient _ _).map (mappingCone.inr _) := by
  rw [← cancel_mono (HomotopyCategory.isoOfHomotopyEquiv
      (mappingConeCompHomotopyEquiv f g)).inv, assoc]
  dsimp [mappingConeCompTriangleh]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    mappingConeCompHomotopyEquiv_hom_inv_id, comp_id,
    mappingConeCompHomotopyEquiv_comm₁ f g,
    mappingConeCompTriangle_mor₂]

end CochainComplex

namespace HomotopyCategory

open CochainComplex

variable [HasZeroObject C]

lemma mappingConeCompTriangleh_distinguished :
    (mappingConeCompTriangleh f g) ∈
      distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  refine ⟨_, _, (mappingConeCompTriangle f g).mor₁, ⟨?_⟩⟩
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (isoOfHomotopyEquiv
    (mappingConeCompHomotopyEquiv f g)) (by cat_disch) (by simp) ?_
  dsimp [mappingConeCompTriangleh]
  rw [CategoryTheory.Functor.map_id, comp_id, ← Functor.map_comp_assoc]
  congr 2
  exact (mappingConeCompHomotopyEquiv_comm₂ f g).symm

noncomputable instance : IsTriangulated (HomotopyCategory C (ComplexShape.up ℤ)) :=
  IsTriangulated.mk' (by
    rintro ⟨X₁ : CochainComplex C ℤ⟩ ⟨X₂ : CochainComplex C ℤ⟩ ⟨X₃ : CochainComplex C ℤ⟩ u₁₂' u₂₃'
    obtain ⟨u₁₂, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₁₂'
    obtain ⟨u₂₃, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective u₂₃'
    refine ⟨_, _, _, _, _, _, _, _, Iso.refl _, Iso.refl _, Iso.refl _, by simp, by simp,
        _, _, mappingCone_triangleh_distinguished u₁₂,
        _, _, mappingCone_triangleh_distinguished u₂₃,
        _, _, mappingCone_triangleh_distinguished (u₁₂ ≫ u₂₃), ⟨?_⟩⟩
    let α := mappingCone.triangleMap u₁₂ (u₁₂ ≫ u₂₃) (𝟙 X₁) u₂₃ (by rw [id_comp])
    let β := mappingCone.triangleMap (u₁₂ ≫ u₂₃) u₂₃ u₁₂ (𝟙 X₃) (by rw [comp_id])
    refine Triangulated.Octahedron.mk ((HomotopyCategory.quotient _ _).map α.hom₃)
      ((HomotopyCategory.quotient _ _).map β.hom₃) ?_ ?_ ?_ ?_ ?_
    · exact ((quotient _ _).mapTriangle.map α).comm₂
    · exact ((quotient _ _).mapTriangle.map α).comm₃.symm.trans (by dsimp [α]; simp)
    · exact ((quotient _ _).mapTriangle.map β).comm₂.trans (by dsimp [β]; simp)
    · exact ((quotient _ _).mapTriangle.map β).comm₃
    · refine isomorphic_distinguished _ (mappingConeCompTriangleh_distinguished u₁₂ u₂₃) _ ?_
      exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by dsimp [α, mappingConeCompTriangleh]; simp)
        (by dsimp [β, mappingConeCompTriangleh]; simp)
        (by dsimp [mappingConeCompTriangleh]; simp))

end HomotopyCategory
