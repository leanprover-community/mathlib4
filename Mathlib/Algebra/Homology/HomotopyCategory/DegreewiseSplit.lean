/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-! Degreewise split exact sequences of cochain complexes

The main result of this file is the lemma
`HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` which asserts
that a triangle in `HomotopyCategory C (ComplexShape.up ℤ)`
is distinguished iff it is isomorphic to the triangle attached to a
degreewise split short exact sequence of cochain complexes.

-/

open CategoryTheory Category Limits Pretriangulated Preadditive

variable {C : Type*} [Category C] [Preadditive C]

namespace CochainComplex

open HomologicalComplex HomComplex

variable (S : ShortComplex (CochainComplex C ℤ))
  (σ : ∀ n, (S.map (eval C _ n)).Splitting)

/-- The `1`-cocycle attached to a degreewise split short exact sequence of cochain complexes. -/
def cocycleOfDegreewiseSplit : Cocycle S.X₃ S.X₁ 1 :=
  Cocycle.mk
    (Cochain.mk (fun p q hpq => (σ p).s ≫ S.X₂.d p q ≫ (σ q).r)) 2 (by linarith) (by
      ext p _ rfl
      sorry)

/-- The canonical morphism `S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧` attached to a degreewise split
short exact sequence of cochain complexes. -/
def homOfDegreewiseSplit : S.X₃ ⟶ S.X₁⟦(1 : ℤ)⟧ :=
  ((Cocycle.equivHom _ _).symm ((cocycleOfDegreewiseSplit S σ).rightShift 1 0 (zero_add 1)))

@[simp]
lemma homOfDegreewiseSplit_f (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n =
      (cocycleOfDegreewiseSplit S σ).1.v n (n + 1) rfl := by
  simp [homOfDegreewiseSplit, Cochain.rightShift_v _ _ _ _ _ _ _ _ rfl]

/-- The triangle in `CochainComplex C ℤ` attached to a degreewise split short exact sequence
of cochain complexes. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂ mor₃]
def triangleOfDegreewiseSplit : Triangle (CochainComplex C ℤ) :=
  Triangle.mk S.f S.g (homOfDegreewiseSplit S σ)

/-- The (distinguished) triangle in `HomotopyCategory C (ComplexShape.up ℤ)` attached to a
degreewise split short exact sequence of cochain complexes. -/
noncomputable abbrev trianglehOfDegreewiseSplit :
    Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj (triangleOfDegreewiseSplit S σ)

variable [HasBinaryBiproducts C]

/-- The canonical isomorphism `(mappingCone (homOfDegreewiseSplit S σ)).X p ≅ S.X₂.X q`
when `p + 1 = q`. -/
noncomputable def mappingConeHomOfDegreewiseSplitXIso (p q : ℤ) (hpq : p + 1 = q) :
    (mappingCone (homOfDegreewiseSplit S σ)).X p ≅ S.X₂.X q where
  hom := (mappingCone.fst (homOfDegreewiseSplit S σ)).1.v p q hpq ≫ (σ q).s -
    (mappingCone.snd (homOfDegreewiseSplit S σ)).v p p (add_zero p) ≫
      by exact (Cochain.ofHom S.f).v (p + 1) q (by linarith)
  inv := S.g.f q ≫ (mappingCone.inl (homOfDegreewiseSplit S σ)).v q p (by linarith) -
    by exact (σ q).r ≫ (S.X₁.XIsoOfEq hpq.symm).hom ≫
      (mappingCone.inr (homOfDegreewiseSplit S σ)).f p
  hom_inv_id := by
    subst hpq
    have s_g := (σ (p + 1)).s_g
    have f_r := (σ (p + 1)).f_r
    dsimp at s_g f_r ⊢
    simp? [mappingCone.ext_from_iff _ (p + 1) _ rfl, reassoc_of% f_r, reassoc_of% s_g] says
      simp only [Cochain.ofHom_v, id_comp, comp_sub, sub_comp, assoc, reassoc_of% s_g,
        ShortComplex.Splitting.s_r_assoc, ShortComplex.map_X₃, eval_obj, ShortComplex.map_X₁,
        zero_comp, comp_zero, reassoc_of% f_r, zero_sub, sub_neg_eq_add,
        mappingCone.ext_from_iff _ (p + 1) _ rfl, comp_add, mappingCone.inl_v_fst_v_assoc,
        mappingCone.inl_v_snd_v_assoc, shiftFunctor_obj_X', sub_zero, add_zero, comp_id,
        mappingCone.inr_f_fst_v_assoc, mappingCone.inr_f_snd_v_assoc, add_left_eq_self,
        neg_eq_zero, true_and]
    rw [← comp_f_assoc, S.zero, zero_f, zero_comp]
  inv_hom_id := by
    subst hpq
    have h := (σ (p + 1)).id
    dsimp at h ⊢
    simp only [id_comp, Cochain.ofHom_v, comp_sub, sub_comp, assoc, mappingCone.inl_v_fst_v_assoc,
      mappingCone.inr_f_fst_v_assoc, shiftFunctor_obj_X', zero_comp, comp_zero, sub_zero,
      mappingCone.inl_v_snd_v_assoc, mappingCone.inr_f_snd_v_assoc, zero_sub, sub_neg_eq_add, ← h]
    abel

/-- The canonical isomorphism `mappingCone (homOfDegreewiseSplit S σ) ≅ S.X₂⟦(1 : ℤ)⟧`. -/
@[simps!]
noncomputable def mappingConeHomOfDegreewiseSplitIso :
    mappingCone (homOfDegreewiseSplit S σ) ≅ S.X₂⟦(1 : ℤ)⟧ :=
  Hom.isoOfComponents (fun p => mappingConeHomOfDegreewiseSplitXIso S σ p _ rfl) (by
    rintro p _ rfl
    have r_f : ∀ n, (σ n).r ≫ S.f.f n = 𝟙 _ - S.g.f n ≫ (σ n).s := fun n => by
      have h := (σ n).id
      dsimp at h
      simp only [← h, ShortComplex.map_X₂, eval_obj, ShortComplex.map_X₁, add_sub_cancel]
    have s_g := (σ (p + 1)).s_g
    dsimp at s_g
    simp [mappingConeHomOfDegreewiseSplitXIso, mappingCone.ext_from_iff _ _ _ rfl,
      mappingCone.inl_v_d_assoc _ (p + 1) _ (p + 1 + 1) (by linarith) (by linarith),
      cocycleOfDegreewiseSplit, r_f]
    rw [← S.g.comm_assoc, reassoc_of% s_g]
    abel)

@[reassoc (attr := simp)]
lemma shift_f_comp_mappingConeHomOfDegreewiseSplitIso_inv :
    S.f⟦(1 : ℤ)⟧' ≫ (mappingConeHomOfDegreewiseSplitIso S σ).inv = -mappingCone.inr _ := by
  ext n
  have h := (σ (n + 1)).f_r
  dsimp at h
  dsimp [mappingConeHomOfDegreewiseSplitXIso]
  rw [id_comp, comp_sub, ← comp_f_assoc, S.zero, zero_f, zero_comp, zero_sub, reassoc_of% h]

@[reassoc (attr := simp)]
lemma mappingConeHomOfDegreewiseSplitIso_inv_comp_triangle_mor₃ :
    (mappingConeHomOfDegreewiseSplitIso S σ).inv ≫
      (mappingCone.triangle (homOfDegreewiseSplit S σ)).mor₃ = -S.g⟦(1 : ℤ)⟧' := by
  ext n
  simp [mappingConeHomOfDegreewiseSplitXIso]

/-- The canonical isomorphism of triangles
`(triangleOfDegreewiseSplit S σ).rotate.rotate ≅ mappingCone.triangle (homOfDegreewiseSplit S σ)`
when `S` is a degreewise split short exact sequence of cochain complexes. -/
noncomputable def triangleOfDegreewiseSplitRotateRotateIso :
    (triangleOfDegreewiseSplit S σ).rotate.rotate ≅
      mappingCone.triangle (homOfDegreewiseSplit S σ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mappingConeHomOfDegreewiseSplitIso S σ).symm
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

/-- The canonical isomorphism between `(trianglehOfDegreewiseSplit S σ).rotate.rotate` and
`mappingCone.triangleh (homOfDegreewiseSplit S σ)` when `S` is a degreewise split
short exact sequence of cochain complexes. -/
noncomputable def trianglehOfDegreewiseSplitRotateRotateIso :
    (trianglehOfDegreewiseSplit S σ).rotate.rotate ≅
      mappingCone.triangleh (homOfDegreewiseSplit S σ) :=
  (rotate _).mapIso ((HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _) ≪≫
    (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleOfDegreewiseSplitRotateRotateIso S σ)

namespace mappingCone

variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

/-- Given a morphism of cochain complexes `φ`, this is the short complex
given by `(triangle φ).rotate`. -/
@[simps]
noncomputable def triangleRotateShortComplex : ShortComplex (CochainComplex C ℤ) :=
  ShortComplex.mk (triangle φ).rotate.mor₁ (triangle φ).rotate.mor₂ (by simp)

/-- `triangleRotateShortComplex φ` is a degreewise split short exact sequence of
cochain complexes. -/
@[simps]
noncomputable def triangleRotateShortComplexSplitting (n : ℤ) :
    ((triangleRotateShortComplex φ).map (eval _ _ n)).Splitting where
  s := -(inl φ).v (n + 1) n (by linarith)
  r := (snd φ).v n n (add_zero n)
  id := by simp [ext_from_iff φ _ _ rfl]

@[simp]
lemma cocycleOfDegreewiseSplit_triangleRotateShortComplexSplitting_v (p : ℤ) :
    (cocycleOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ)).1.v p _ rfl =
      -φ.f _ := by
  simp [cocycleOfDegreewiseSplit, d_snd_v φ p (p + 1) rfl]

/-- The triangle `(triangle φ).rotate` is isomorphic to a triangle attached to a
degreewise split short exact sequence of cochain complexes. -/
noncomputable def triangleRotateIsoTriangleOfDegreewiseSplit :
    (triangle φ).rotate ≅
      triangleOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by aesop_cat) (by aesop_cat) (by aesop_cat)

/-- The triangle `(triangleh φ).rotate` is isomorphic to a triangle attached to a
degreewise split short exact sequence of cochain complexes. -/
noncomputable def trianglehRotateIsoTrianglehOfDegreewiseSplit :
    (triangleh φ).rotate ≅
      trianglehOfDegreewiseSplit _ (triangleRotateShortComplexSplitting φ) :=
  (HomotopyCategory.quotient _ _).mapTriangleRotateIso.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso
      (triangleRotateIsoTriangleOfDegreewiseSplit φ)

end mappingCone

end CochainComplex

namespace HomotopyCategory

variable [HasZeroObject C] [HasBinaryBiproducts C]

lemma distinguished_iff_iso_trianglehOfDegreewiseSplit
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    (T ∈ distTriang _) ↔ ∃ (S : ShortComplex (CochainComplex C ℤ))
      (σ : ∀ n, (S.map (HomologicalComplex.eval C _ n)).Splitting),
      Nonempty (T ≅ CochainComplex.trianglehOfDegreewiseSplit S σ) := by
  constructor
  · intro hT
    obtain ⟨K, L, φ, ⟨e⟩⟩ := inv_rot_of_distTriang _ hT
    exact ⟨_, _, ⟨(triangleRotation _).counitIso.symm.app _ ≪≫ (rotate _).mapIso e ≪≫
      CochainComplex.mappingCone.trianglehRotateIsoTrianglehOfDegreewiseSplit φ⟩⟩
  · rintro ⟨S, σ, ⟨e⟩⟩
    rw [rotate_distinguished_triangle, rotate_distinguished_triangle]
    refine isomorphic_distinguished _ ?_ _
      ((rotate _ ⋙ rotate _).mapIso e ≪≫
        CochainComplex.trianglehOfDegreewiseSplitRotateRotateIso S σ)
    exact ⟨_, _, _, ⟨Iso.refl _⟩⟩

end HomotopyCategory
