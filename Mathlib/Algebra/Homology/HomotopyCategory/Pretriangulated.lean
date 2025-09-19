/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
import Mathlib.CategoryTheory.Triangulated.Functor

/-! The pretriangulated structure on the homotopy category of complexes

In this file, we define the pretriangulated structure on the homotopy
category `HomotopyCategory C (ComplexShape.up ℤ)` of an additive category `C`.
The distinguished triangles are the triangles that are isomorphic to the
image in the homotopy category of the standard triangle
`K ⟶ L ⟶ mappingCone φ ⟶ K⟦(1 : ℤ)⟧` for some morphism of
cochain complexes `φ : K ⟶ L`.

This result first appeared in the Liquid Tensor Experiment. In the LTE, the
formalization followed the Stacks Project: in particular, the distinguished
triangles were defined using degreewise-split short exact sequences of cochain
complexes. Here, we follow the original definitions in [Verdiers's thesis, I.3][verdier1996]
(with the better sign conventions from the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000]).

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*][verdier1996]
* [Brian Conrad, Grothendieck duality and base change][conrad2000]
* https://stacks.math.columbia.edu/tag/014P

-/

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits CochainComplex.HomComplex Pretriangulated

variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [HasBinaryBiproducts C]
  [Preadditive D] [HasBinaryBiproducts D]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L)

namespace CochainComplex

namespace mappingCone

/-- The standard triangle `K ⟶ L ⟶ mappingCone φ ⟶ K⟦(1 : ℤ)⟧` in `CochainComplex C ℤ`
attached to a morphism `φ : K ⟶ L`. It involves `φ`, `inr φ : L ⟶ mappingCone φ` and
the morphism induced by the `1`-cocycle `-mappingCone.fst φ`. -/
@[simps! obj₁ obj₂ obj₃ mor₁ mor₂]
noncomputable def triangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk φ (inr φ) (Cocycle.homOf ((-fst φ).rightShift 1 0 (zero_add 1)))

@[reassoc (attr := simp)]
lemma inl_v_triangle_mor₃_f (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ).v p q hpq ≫ (triangle φ).mor₃.f q =
      -(K.shiftFunctorObjXIso 1 q p (by rw [← hpq, neg_add_cancel_right])).inv := by
  dsimp [triangle]
  -- the following list of lemmas was obtained by doing
  -- simp? [Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by omega)]
  simp only [Int.reduceNeg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by cutsat), shiftFunctor_obj_X,
    shiftFunctorObjXIso, Preadditive.comp_neg, inl_v_fst_v_assoc]

@[reassoc (attr := simp)]
lemma inr_f_triangle_mor₃_f (p : ℤ) : (inr φ).f p ≫ (triangle φ).mor₃.f p = 0 := by
  dsimp [triangle]
  -- the following list of lemmas was obtained by doing
  -- simp? [Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p+1) rfl]
  simp only [Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p + 1) rfl, shiftFunctor_obj_X,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id,
    Preadditive.comp_neg, inr_f_fst_v, neg_zero]

@[reassoc (attr := simp)]
lemma inr_triangleδ : inr φ ≫ (triangle φ).mor₃ = 0 := by ext; simp

/-- The (distinguished) triangle in the homotopy category that is associated to
a morphism `φ : K ⟶ L` in the category `CochainComplex C ℤ`. -/
noncomputable abbrev triangleh : Triangle (HomotopyCategory C (ComplexShape.up ℤ)) :=
  (HomotopyCategory.quotient _ _).mapTriangle.obj (triangle φ)

variable (K) in
/-- The mapping cone of the identity is contractible. -/
noncomputable def homotopyToZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
  descHomotopy (𝟙 K) _ _ 0 (inl _) (by simp) (by simp)

section mapOfHomotopy

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

/-- The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a square that
is commutative up to homotopy. -/
noncomputable def mapOfHomotopy :
    mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _) +
    ((Cochain.equivHomotopy _ _) H).1.comp (Cochain.ofHom (inr φ₂)) (add_zero _))
    (b ≫ inr φ₂) (by simp)

@[reassoc]
lemma triangleMapOfHomotopy_comm₂ :
    inr φ₁ ≫ mapOfHomotopy H = b ≫ inr φ₂ := by
  simp [mapOfHomotopy]

@[reassoc]
lemma triangleMapOfHomotopy_comm₃ :
    mapOfHomotopy H ≫ (triangle φ₂).mor₃ = (triangle φ₁).mor₃ ≫ a⟦1⟧' := by
  ext p
  dsimp [mapOfHomotopy, triangle]
  -- the following list of lemmas as been obtained by doing
  -- simp? [ext_from_iff _ _ _ rfl, Cochain.rightShift_v _ 1 0 _ p p _ (p + 1) rfl]
  simp only [Int.reduceNeg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
    Cochain.rightShift_v _ 1 0 _ p p _ (p + 1) rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id, Preadditive.comp_neg,
    Preadditive.neg_comp, ext_from_iff _ _ _ rfl, inl_v_desc_f_assoc, Cochain.add_v,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v, Preadditive.add_comp,
    assoc, inl_v_fst_v, inr_f_fst_v, comp_zero, add_zero, inl_v_fst_v_assoc, inr_f_desc_f_assoc,
    HomologicalComplex.comp_f, neg_zero, inr_f_fst_v_assoc, zero_comp, and_self]

/-- The morphism `triangleh φ₁ ⟶ triangleh φ₂` that is induced by a square that
is commutative up to homotopy. -/
@[simps]
noncomputable def trianglehMapOfHomotopy :
    triangleh φ₁ ⟶ triangleh φ₂ where
  hom₁ := (HomotopyCategory.quotient _ _).map a
  hom₂ := (HomotopyCategory.quotient _ _).map b
  hom₃ := (HomotopyCategory.quotient _ _).map (mapOfHomotopy H)
  comm₁ := by
    dsimp
    simp only [← Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ H
  comm₂ := by
    dsimp
    simp only [← Functor.map_comp, triangleMapOfHomotopy_comm₂]
  comm₃ := by
    dsimp
    rw [← Functor.map_comp_assoc, triangleMapOfHomotopy_comm₃, Functor.map_comp, assoc, assoc]
    simp

end mapOfHomotopy

section map

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (φ₃ : K₃ ⟶ L₃)
  (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)

/-- The morphism `mappingCone φ₁ ⟶ mappingCone φ₂` that is induced by a commutative square. -/
noncomputable def map (comm : φ₁ ≫ b = a ≫ φ₂) : mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _)) (b ≫ inr φ₂)
    (by simp [reassoc_of% comm])

variable (comm : φ₁ ≫ b = a ≫ φ₂)

lemma map_eq_mapOfHomotopy : map φ₁ φ₂ a b comm = mapOfHomotopy (Homotopy.ofEq comm) := by
  simp [map, mapOfHomotopy]

lemma map_id : map φ φ (𝟙 _) (𝟙 _) (by rw [id_comp, comp_id]) = 𝟙 _ := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map]

variable (a' : K₂ ⟶ K₃) (b' : L₂ ⟶ L₃)

@[reassoc]
lemma map_comp (comm' : φ₂ ≫ b' = a' ≫ φ₃) :
    map φ₁ φ₃ (a ≫ a') (b ≫ b') (by rw [reassoc_of% comm, comm', assoc]) =
      map φ₁ φ₂ a b comm ≫ map φ₂ φ₃ a' b' comm' := by
  ext n
  simp [ext_from_iff _ (n + 1) n rfl, map]

/-- The morphism `triangle φ₁ ⟶ triangle φ₂` that is induced by a commutative square. -/
@[simps]
noncomputable def triangleMap :
    triangle φ₁ ⟶ triangle φ₂ where
  hom₁ := a
  hom₂ := b
  hom₃ := map φ₁ φ₂ a b comm
  comm₁ := comm
  comm₂ := by
    dsimp
    rw [map_eq_mapOfHomotopy, triangleMapOfHomotopy_comm₂]
  comm₃ := by
    dsimp
    rw [map_eq_mapOfHomotopy, triangleMapOfHomotopy_comm₃]

end map

section Rotate

/-- Given `φ : K ⟶ L`, `K⟦(1 : ℤ)⟧` is homotopy equivalent to
the mapping cone of `inr φ : L ⟶ mappingCone φ`. -/
noncomputable def rotateHomotopyEquiv :
    HomotopyEquiv (K⟦(1 : ℤ)⟧) (mappingCone (inr φ)) where
  hom := lift (inr φ) (-(Cocycle.ofHom φ).leftShift 1 1 (zero_add 1))
    (-(inl φ).leftShift 1 0 (neg_add_cancel 1)) (by
      -- the following list of lemmas has been obtained by doing
      -- simp? [Cochain.δ_leftShift _ 1 0 1 (neg_add_cancel 1) 0 (zero_add 1)]
      simp only [Int.reduceNeg, δ_neg,
        Cochain.δ_leftShift _ 1 0 1 (neg_add_cancel 1) 0 (zero_add 1),
        Int.negOnePow_one, δ_inl, Cochain.ofHom_comp, Cochain.leftShift_comp_zero_cochain,
        Units.neg_smul, one_smul, neg_neg, Cocycle.coe_neg, Cocycle.leftShift_coe,
        Cocycle.ofHom_coe, Cochain.neg_comp, add_neg_cancel])
  inv := desc (inr φ) 0 (triangle φ).mor₃
    (by simp only [δ_zero, inr_triangleδ, Cochain.ofHom_zero])
  homotopyHomInvId := Homotopy.ofEq (by
    ext n
    -- the following list of lemmas has been obtained by doing
    -- simp? [lift_desc_f _ _ _ _ _ _ _ _ _ rfl,
    --   (inl φ).leftShift_v 1 0 _ _ n _ (n + 1) (by simp only [add_neg_cancel_right])]
    simp only [shiftFunctor_obj_X', Int.reduceNeg, HomologicalComplex.comp_f,
      lift_desc_f _ _ _ _ _ _ _ _ _ rfl, Cocycle.coe_neg, Cocycle.leftShift_coe,
      Cocycle.ofHom_coe, Cochain.neg_v, Cochain.zero_v,
      comp_zero, (inl φ).leftShift_v 1 0 _ _ n _ (n + 1) (by simp only [add_neg_cancel_right]),
      shiftFunctor_obj_X, mul_zero, sub_self, Int.zero_ediv, add_zero, Int.negOnePow_zero,
      shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp, one_smul,
      Preadditive.neg_comp, inl_v_triangle_mor₃_f, Iso.refl_inv, neg_neg, zero_add,
      HomologicalComplex.id_f])
  homotopyInvHomId := (Cochain.equivHomotopy _ _).symm
    ⟨-(snd (inr φ)).comp ((snd φ).comp (inl (inr φ)) (zero_add (-1))) (zero_add (-1)), by
      ext n
      -- the following list of lemmas has been obtained by doing
      -- simp? [ext_to_iff _ _ (n + 1) rfl, ext_from_iff _ (n + 1) _ rfl,
      --   δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
      --   (inl φ).leftShift_v 1 0 (neg_add_cancel 1) n n (add_zero n) (n + 1) (by omega),
      --   (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) n (n + 1) rfl (n + 1) (by omega),
      --   Cochain.comp_v _ _ (add_neg_cancel 1) n (n + 1) n rfl (by omega)]
      simp only [Int.reduceNeg, Cochain.ofHom_comp, ofHom_desc, ofHom_lift, Cocycle.coe_neg,
        Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.comp_zero_cochain_v,
        shiftFunctor_obj_X', δ_neg, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1), δ_inl,
        Int.negOnePow_neg, Int.negOnePow_one, δ_snd, Cochain.neg_comp,
        Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, Units.neg_smul, one_smul,
        neg_neg, Cochain.comp_add, inr_snd_assoc, neg_add_rev, Cochain.add_v, Cochain.neg_v,
        Cochain.comp_v _ _ (add_neg_cancel 1) n (n + 1) n rfl (by omega),
        Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.id_f,
        ext_to_iff _ _ (n + 1) rfl, assoc, liftCochain_v_fst_v,
        (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) n (n + 1) rfl (n + 1) (by omega),
        shiftFunctor_obj_X, mul_one, sub_self, mul_zero, Int.zero_ediv, add_zero,
        shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp,
        Preadditive.add_comp, Preadditive.neg_comp, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero,
        neg_zero, neg_add_cancel_comm, ext_from_iff _ (n + 1) _ rfl, inl_v_descCochain_v_assoc,
        Cochain.zero_v, zero_comp, Preadditive.comp_neg, inl_v_snd_v_assoc,
        inr_f_descCochain_v_assoc, inr_f_snd_v_assoc, inl_v_triangle_mor₃_f_assoc, triangle_obj₁,
        Iso.refl_inv, inl_v_fst_v_assoc, inr_f_triangle_mor₃_f_assoc, inr_f_fst_v_assoc, and_self,
        liftCochain_v_snd_v,
        (inl φ).leftShift_v 1 0 (neg_add_cancel 1) n n (add_zero n) (n + 1) (by omega),
        Int.negOnePow_zero, inl_v_snd_v, inr_f_snd_v, zero_add, inl_v_descCochain_v,
        inr_f_descCochain_v, inl_v_triangle_mor₃_f, inr_f_triangle_mor₃_f, neg_add_cancel]⟩

/-- Auxiliary definition for `rotateTrianglehIso`. -/
noncomputable def rotateHomotopyEquivComm₂Homotopy :
    Homotopy ((triangle φ).mor₃ ≫ (rotateHomotopyEquiv φ).hom)
      (inr (CochainComplex.mappingCone.inr φ)) := (Cochain.equivHomotopy _ _).symm
      ⟨-(snd φ).comp (inl (inr φ)) (zero_add (-1)), by
        ext p
        dsimp [rotateHomotopyEquiv]
        -- the following list of lemmas has been obtained by doing
        -- simp? [ext_from_iff _ _ _ rfl, ext_to_iff _ _ _ rfl,
        --  (inl φ).leftShift_v 1 0 (neg_add_cancel 1) p p (add_zero p) (p + 1) (by omega),
        --  δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
        --  Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p rfl (by omega),
        --  (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by omega)]⟩
        simp only [Int.reduceNeg, Cochain.ofHom_comp, ofHom_lift, Cocycle.coe_neg,
          Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.comp_zero_cochain_v,
          shiftFunctor_obj_X', Cochain.ofHom_v, δ_neg, δ_zero_cochain_comp _ _ _ (neg_add_cancel 1),
          δ_inl, Int.negOnePow_neg, Int.negOnePow_one, δ_snd, Cochain.neg_comp,
          Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, Units.neg_smul, one_smul, neg_neg,
          neg_add_rev, Cochain.add_v, Cochain.neg_v,
          Cochain.comp_v _ _ (add_neg_cancel 1) p (p + 1) p rfl (by cutsat),
          Cochain.zero_cochain_comp_v, ext_from_iff _ _ _ rfl, inl_v_triangle_mor₃_f_assoc,
          triangle_obj₁, shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
          Iso.refl_inv, Preadditive.neg_comp, id_comp, Preadditive.comp_add, Preadditive.comp_neg,
          inl_v_fst_v_assoc, inl_v_snd_v_assoc, zero_comp, neg_zero, add_zero, ext_to_iff _ _ _ rfl,
          liftCochain_v_fst_v,
          (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by cutsat), mul_one,
          sub_self, mul_zero, Int.zero_ediv, Iso.refl_hom, Preadditive.add_comp, assoc, inl_v_fst_v,
          comp_id, inr_f_fst_v, comp_zero, liftCochain_v_snd_v,
          (inl φ).leftShift_v 1 0 (neg_add_cancel 1) p p (add_zero p) (p + 1) (by cutsat),
          Int.negOnePow_zero, inl_v_snd_v, inr_f_snd_v, zero_add, and_self,
          inr_f_triangle_mor₃_f_assoc, inr_f_fst_v_assoc, inr_f_snd_v_assoc, neg_add_cancel]⟩

@[reassoc (attr := simp)]
lemma rotateHomotopyEquiv_comm₂ :
    (HomotopyCategory.quotient _ _ ).map (triangle φ).mor₃ ≫
      (HomotopyCategory.quotient _ _ ).map (rotateHomotopyEquiv φ).hom =
      (HomotopyCategory.quotient _ _ ).map (inr (inr φ)) := by
  simpa only [Functor.map_comp]
    using HomotopyCategory.eq_of_homotopy _ _  (rotateHomotopyEquivComm₂Homotopy φ)

@[reassoc (attr := simp)]
lemma rotateHomotopyEquiv_comm₃ :
    (rotateHomotopyEquiv φ).hom ≫ (triangle (inr φ)).mor₃ = -φ⟦1⟧' := by
  ext p
  dsimp [rotateHomotopyEquiv]
  -- the following list of lemmas has been obtained by doing
  -- simp? [lift_f _ _ _ _ _ (p + 1) rfl,
  --   (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by omega)]
  simp only [Int.reduceNeg, lift_f _ _ _ _ _ (p + 1) rfl, shiftFunctor_obj_X', Cocycle.coe_neg,
    Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.neg_v,
    (Cochain.ofHom φ).leftShift_v 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (by cutsat),
    shiftFunctor_obj_X, mul_one, sub_self, mul_zero, Int.zero_ediv, add_zero, Int.negOnePow_one,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Cochain.ofHom_v, id_comp,
    Units.neg_smul, one_smul, neg_neg, Preadditive.neg_comp, Preadditive.add_comp, assoc,
    inl_v_triangle_mor₃_f, Iso.refl_inv, Preadditive.comp_neg, comp_id, inr_f_triangle_mor₃_f,
    comp_zero, neg_zero]

/-- The canonical isomorphism of triangles `(triangleh φ).rotate ≅ (triangleh (inr φ))`. -/
noncomputable def rotateTrianglehIso :
    (triangleh φ).rotate ≅ (triangleh (inr φ)) :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).symm.app K ≪≫
      HomotopyCategory.isoOfHomotopyEquiv (rotateHomotopyEquiv φ))
        (by simp) (by simp) (by
        dsimp
        rw [CategoryTheory.Functor.map_id, comp_id, assoc, ← Functor.map_comp_assoc,
          rotateHomotopyEquiv_comm₃, Functor.map_neg, Preadditive.neg_comp,
          Functor.commShiftIso_hom_naturality, Preadditive.comp_neg,
          Iso.inv_hom_id_app_assoc])

end Rotate

section Shift

/-- The canonical isomorphism `(mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧')`. -/
noncomputable def shiftIso (n : ℤ) : (mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧') where
  hom := lift _ (n.negOnePow • (fst φ).shift n) ((snd φ).shift n) (by
    ext p q hpq
    dsimp
    simp only [Cochain.δ_shift, δ_snd, Cochain.shift_neg, smul_neg, Cochain.neg_v,
      shiftFunctor_obj_X', Cochain.units_smul_v, Cochain.shift_v', Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, Cochain.units_smul_comp, shiftFunctor_map_f', neg_add_cancel])
  inv := desc _ (n.negOnePow • (inl φ).shift n) ((inr φ)⟦n⟧') (by
    ext p
    dsimp
    simp only [Int.reduceNeg, δ_units_smul, Cochain.δ_shift, δ_inl, Cochain.ofHom_comp, smul_smul,
      Int.units_mul_self, one_smul, Cochain.shift_v', Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, shiftFunctor_obj_X', shiftFunctor_map_f'])
  hom_inv_id := by
    ext p
    dsimp
    simp only [Int.reduceNeg, lift_desc_f _ _ _ _ _ _ _ _ (p + 1) rfl, shiftFunctor_obj_X',
      Cocycle.coe_units_smul, Cocycle.shift_coe, Cochain.units_smul_v, Cochain.shift_v',
      Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Int.units_mul_self, one_smul,
      shiftFunctor_map_f', id_X]
  inv_hom_id := by
    ext p
    dsimp
    simp only [Int.reduceNeg, ext_from_iff _ (p + 1) _ rfl, shiftFunctor_obj_X',
      inl_v_desc_f_assoc, Cochain.units_smul_v, Cochain.shift_v', Linear.units_smul_comp, comp_id,
      ext_to_iff _ _ (p + 1) rfl, assoc, lift_f_fst_v,
      Cocycle.coe_units_smul, Cocycle.shift_coe, Linear.comp_units_smul, inl_v_fst_v, smul_smul,
      Int.units_mul_self, one_smul, lift_f_snd_v, inl_v_snd_v, smul_zero, and_self,
      inr_f_desc_f_assoc, shiftFunctor_map_f', inr_f_fst_v, inr_f_snd_v]

/-- The canonical isomorphism `(triangle φ)⟦n⟧ ≅ triangle (φ⟦n⟧')`. -/
noncomputable def shiftTriangleIso (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj (triangle φ) ≅ triangle (φ⟦n⟧') := by
  refine Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (shiftIso φ n) ?_ ?_ ?_
  · dsimp
    simp only [Linear.comp_units_smul, comp_id, id_comp, smul_smul,
      Int.units_mul_self, one_smul]
  · ext p
    dsimp
    simp only [Units.smul_def, shiftIso, Int.reduceNeg, Linear.smul_comp, id_comp,
      ext_to_iff _ _ (p + 1) rfl, shiftFunctor_obj_X', assoc, lift_f_fst_v, Cocycle.coe_smul,
      Cocycle.shift_coe, Cochain.smul_v, Cochain.shift_v', Linear.comp_smul, inr_f_fst_v,
      smul_zero, lift_f_snd_v, inr_f_snd_v, and_true]
  · ext p
    dsimp
    simp only [triangle, Triangle.mk_mor₃, Cocycle.homOf_f, Cocycle.rightShift_coe,
      Cocycle.coe_neg, Cochain.rightShift_neg, Cochain.neg_v, shiftFunctor_obj_X',
      (fst φ).1.rightShift_v 1 0 (zero_add 1) (p + n) (p + n) (add_zero (p + n)) (p + 1 + n)
        (by cutsat),
      shiftFunctor_obj_X, shiftFunctorObjXIso, shiftFunctorComm_hom_app_f, Preadditive.neg_comp,
      assoc, Iso.inv_hom_id, comp_id, smul_neg, Units.smul_def, shiftIso, Int.reduceNeg,
      (fst (φ⟦n⟧')).1.rightShift_v 1 0 (zero_add 1) p p (add_zero p) (p + 1) rfl,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Preadditive.comp_neg, lift_f_fst_v,
      Cocycle.coe_smul, Cocycle.shift_coe, Cochain.smul_v, Cochain.shift_v']

/-- The canonical isomorphism `(triangleh φ)⟦n⟧ ≅ triangleh (φ⟦n⟧')`. -/
noncomputable def shiftTrianglehIso (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj (triangleh φ) ≅ triangleh (φ⟦n⟧') :=
  ((HomotopyCategory.quotient _ _).mapTriangle.commShiftIso n).symm.app _ ≪≫
    (HomotopyCategory.quotient _ _).mapTriangle.mapIso (shiftTriangleIso φ n)

end Shift

section

open Preadditive

variable (G : C ⥤ D) [G.Additive]

lemma map_δ :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).map (triangle φ).mor₃ ≫
      NatTrans.app ((Functor.mapHomologicalComplex G (ComplexShape.up ℤ)).commShiftIso  1).hom K =
    (mapHomologicalComplexIso φ G).hom ≫
      (triangle ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ)).mor₃ := by
  ext n
  dsimp [mapHomologicalComplexIso]
  rw [mapHomologicalComplexXIso_eq φ G n (n + 1) rfl, mapHomologicalComplexXIso'_hom]
  simp only [Functor.mapHomologicalComplex_obj_X, add_comp, assoc, inl_v_triangle_mor₃_f,
    shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    comp_neg, comp_id, inr_f_triangle_mor₃_f, comp_zero, add_zero]
  dsimp [triangle]
  rw [Cochain.rightShift_v _ 1 0 (by cutsat) n n (by cutsat) (n + 1) (by cutsat)]
  simp only [shiftFunctor_obj_X, Cochain.neg_v, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id, Functor.map_neg]

/-- If `φ : K ⟶ L` is a morphism of cochain complexes in `C` and `G : C ⥤ D` is an
additive functor, then the image by `G` of the triangle `triangle φ` identifies to
the triangle associated to the image of `φ` by `G`. -/
noncomputable def mapTriangleIso :
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangle.obj (triangle φ) ≅
      triangle ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (mapHomologicalComplexIso φ G) ?_ ?_ ?_
  · dsimp
    simp only [comp_id, id_comp]
  · dsimp
    rw [map_inr, id_comp]
  · dsimp
    simp only [CategoryTheory.Functor.map_id, comp_id, map_δ]

/-- If `φ : K ⟶ L` is a morphism of cochain complexes in `C` and `G : C ⥤ D` is an
additive functor, then the image by `G` of the triangle `triangleh φ` identifies to
the triangle associated to the image of `φ` by `G`. -/
noncomputable def mapTrianglehIso :
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).mapTriangle.obj (triangleh φ) ≅
      triangleh ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) :=
  (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
    (Functor.mapTriangleIso (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ))).app _ ≪≫
    (Functor.mapTriangleCompIso _ _).app _ ≪≫
    (HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapTriangle.mapIso
      (CochainComplex.mappingCone.mapTriangleIso φ G)

end

end mappingCone

end CochainComplex

namespace HomotopyCategory

variable (C)

namespace Pretriangulated

/-- A triangle in `HomotopyCategory C (ComplexShape.up ℤ)` is distinguished if it is isomorphic to
the triangle `CochainComplex.mappingCone.triangleh φ` for some morphism of cochain
complexes `φ`. -/
def distinguishedTriangles : Set (Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :=
  fun T => ∃ (X Y : CochainComplex C ℤ) (φ : X ⟶ Y),
    Nonempty (T ≅ CochainComplex.mappingCone.triangleh φ)

variable {C}

lemma isomorphic_distinguished (T₁ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles C := by
  obtain ⟨X, Y, f, ⟨e'⟩⟩ := hT₁
  exact ⟨X, Y, f, ⟨e ≪≫ e'⟩⟩

variable [HasZeroObject C] in
lemma contractible_distinguished (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    Pretriangulated.contractibleTriangle X ∈ distinguishedTriangles C := by
  obtain ⟨X⟩ := X
  refine ⟨_, _, 𝟙 X, ⟨?_⟩⟩
  have h := (isZero_quotient_obj_iff _).2 ⟨CochainComplex.mappingCone.homotopyToZeroOfId X⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) h.isoZero.symm
    (by simp) (h.eq_of_tgt _ _) (by dsimp; ext)

lemma distinguished_cocone_triangle {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory C (ComplexShape.up ℤ)) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective f
  exact ⟨_, _, _, ⟨_, _, f, ⟨Iso.refl _⟩⟩⟩

lemma rotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) : T.rotate ∈ distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨(rotate _).mapIso e ≪≫ CochainComplex.mappingCone.rotateTrianglehIso φ⟩⟩

lemma shift_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) (n : ℤ) :
      (Triangle.shiftFunctor _ n).obj T ∈ distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  exact ⟨_, _, _, ⟨Functor.mapIso _ e ≪≫ CochainComplex.mappingCone.shiftTrianglehIso φ n⟩⟩

lemma invRotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) : T.invRotate ∈ distinguishedTriangles C :=
  isomorphic_distinguished _
    (shift_distinguished_triangle _ (rotate_distinguished_triangle' _
      (rotate_distinguished_triangle' _ hT)) _) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

lemma rotate_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  constructor
  · exact rotate_distinguished_triangle' T
  · intro hT
    exact isomorphic_distinguished _ (invRotate_distinguished_triangle' T.rotate hT) _
      ((triangleRotation _).unitIso.app T)

open CochainComplex.mappingCone in
lemma complete_distinguished_triangle_morphism
    (T₁ T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (hT₂ : T₂ ∈ distinguishedTriangles C)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂) (fac : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ (c : T₁.obj₃ ⟶ T₂.obj₃), T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ a⟦(1 : ℤ)⟧' = c ≫ T₂.mor₃ := by
  obtain ⟨K₁, L₁, φ₁, ⟨e₁⟩⟩ := hT₁
  obtain ⟨K₂, L₂, φ₂, ⟨e₂⟩⟩ := hT₂
  obtain ⟨a', ha'⟩ : ∃ (a' : (quotient _ _).obj K₁ ⟶ (quotient _ _).obj K₂),
    a' = e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ (b' : (quotient _ _).obj L₁ ⟶ (quotient _ _).obj L₂),
    b' = e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂ := ⟨_, rfl⟩
  obtain ⟨a'', rfl⟩ := (quotient _ _).map_surjective a'
  obtain ⟨b'', rfl⟩ := (quotient _ _).map_surjective b'
  have H : Homotopy (φ₁ ≫ b'') (a'' ≫ φ₂) := homotopyOfEq _ _ (by
    have comm₁₁ := e₁.inv.comm₁
    have comm₁₂ := e₂.hom.comm₁
    dsimp at comm₁₁ comm₁₂
    simp only [Functor.map_comp, ha', hb', reassoc_of% comm₁₁,
      reassoc_of% fac, comm₁₂, assoc])
  let γ := e₁.hom ≫ trianglehMapOfHomotopy H ≫ e₂.inv
  have comm₂ := γ.comm₂
  have comm₃ := γ.comm₃
  dsimp [γ] at comm₂ comm₃
  simp only [ha', hb'] at comm₂ comm₃
  refine ⟨γ.hom₃, ?_, ?_⟩
  -- the following list of lemmas was obtained by doing simpa? [γ] using comm₂
  · simpa only [triangleCategory_comp, Functor.mapTriangle_obj, triangle_obj₁, triangle_obj₂,
      triangle_obj₃, triangle_mor₁, triangle_mor₂, TriangleMorphism.comp_hom₃, Triangle.mk_obj₃,
      trianglehMapOfHomotopy_hom₃, TriangleMorphism.comm₂_assoc, Triangle.mk_obj₂,
      Triangle.mk_mor₂, assoc, Iso.hom_inv_id_triangle_hom₂, comp_id,
      Iso.hom_inv_id_triangle_hom₂_assoc, γ] using comm₂
  -- the following list of lemmas was obtained by doing simpa? [γ] using comm₃
  · simpa only [triangleCategory_comp, Functor.mapTriangle_obj, triangle_obj₁, triangle_obj₂,
      triangle_obj₃, triangle_mor₁, triangle_mor₂, TriangleMorphism.comp_hom₃, Triangle.mk_obj₃,
      trianglehMapOfHomotopy_hom₃, assoc, Triangle.mk_obj₁, Iso.hom_inv_id_triangle_hom₁, comp_id,
      Iso.hom_inv_id_triangle_hom₁_assoc, γ] using comm₃

end Pretriangulated

variable [HasZeroObject C]

noncomputable instance : Pretriangulated (HomotopyCategory C (ComplexShape.up ℤ)) where
  distinguishedTriangles := Pretriangulated.distinguishedTriangles C
  isomorphic_distinguished := Pretriangulated.isomorphic_distinguished
  contractible_distinguished := Pretriangulated.contractible_distinguished
  distinguished_cocone_triangle := Pretriangulated.distinguished_cocone_triangle
  rotate_distinguished_triangle := Pretriangulated.rotate_distinguished_triangle
  complete_distinguished_triangle_morphism :=
    Pretriangulated.complete_distinguished_triangle_morphism

variable {C}

lemma mappingCone_triangleh_distinguished {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
    CochainComplex.mappingCone.triangleh f ∈ distTriang (HomotopyCategory _ _) :=
  ⟨_, _, f, ⟨Iso.refl _⟩⟩

variable [HasZeroObject D]

instance (G : C ⥤ D) [G.Additive] :
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).IsTriangulated where
  map_distinguished := by
    rintro T ⟨K, L, f, ⟨e⟩⟩
    exact ⟨_, _, _, ⟨(G.mapHomotopyCategory (ComplexShape.up ℤ)).mapTriangle.mapIso e ≪≫
      CochainComplex.mappingCone.mapTrianglehIso f G⟩⟩

end HomotopyCategory
