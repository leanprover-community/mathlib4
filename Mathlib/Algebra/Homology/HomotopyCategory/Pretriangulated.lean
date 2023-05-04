import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Instances

import Mathlib.Tactic.LibrarySearch

open CategoryTheory Category Limits CochainComplex.HomComplex Pretriangulated ZeroObject
  Preadditive

variable {C : Type _} [Category C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable {K L : CochainComplex C ℤ} (φ : K ⟶ L)

namespace CochainComplex

namespace MappingCone

noncomputable def triangleδ : mappingCone φ ⟶ K⟦(1 : ℤ)⟧ :=
  Cocycle.homOf ((-fst φ).rightShift 1 0 (zero_add 1))

@[reassoc (attr := simp)]
lemma inl_v_triangleδ_f (p q : ℤ) (hpq : p + (-1) = q) :
    (inl φ : Cochain K (mappingCone φ) (-1)).v p q hpq ≫ (triangleδ φ).f q =
      -(K.shiftFunctorObjXIso 1 q p (by rw [← hpq, neg_add_cancel_right])).inv := by
  dsimp only [triangleδ]
  simp only [Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.coe_neg,
    Cochain.rightShift_neg, Cochain.neg_v, comp_neg, shiftFunctor_obj_X, shiftFunctorObjXIso,
    Cochain.rightShift_v _ 1 0 (zero_add 1) q q (add_zero q) p (by linarith), inl_v_fst_v_assoc]

@[reassoc (attr := simp)]
lemma inr_f_triangleδ_f (p : ℤ) : (inr φ).f p ≫ (triangleδ φ).f p = 0 := by
  dsimp [triangleδ]
  simp only [Cochain.rightShift_v _ 1 0 _ p p (add_zero p) (p+1) rfl, Cochain.neg_v,
    comp_neg, neg_comp, inr_f_fst_v_assoc, zero_comp, neg_zero]

@[simp]
lemma inr_triangleδ : inr φ ≫ triangleδ φ = 0 := by aesop_cat

@[simp]
noncomputable def triangle : Triangle (CochainComplex C ℤ) :=
  Triangle.mk φ (inr φ) (triangleδ φ)

variable (K)

noncomputable def homotopyToZeroOfId : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
  descHomotopy (𝟙 K) _ _ 0 (inl _) (by simp) (by simp)

variable {K}

section map

variable {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂}
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))

noncomputable def map : mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _) +
      ((Cochain.equivHomotopy _ _) H : Cochain K₁ L₂ (-1)).comp
    (Cochain.ofHom (inr φ₂)) (add_zero _)) (b ≫ inr φ₂) (by simp)

@[reassoc]
lemma triangleMap_comm₂ : inr φ₁ ≫ map H = b ≫ inr φ₂ := by
  simp only [map, Cochain.equivHomotopy_apply_coe, inr_desc]

@[reassoc]
lemma triangleMap_comm₃ : map H ≫ triangleδ φ₂ = triangleδ φ₁ ≫ a⟦1⟧' := by
  ext p
  rw [from_ext_iff _ _ _ _ rfl]
  dsimp [triangleδ, map]
  simp only [Cochain.rightShift_v _ 1 0 _ p p _ (p+1) rfl,
    shiftFunctor_obj_X, Cochain.neg_v, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id, neg_comp,
    comp_neg, inl_v_fst_v_assoc, inl_v_desc_f_assoc,
    Cochain.add_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v,
    add_comp, assoc, inl_v_fst_v, inr_f_fst_v, comp_zero, add_zero,
    inr_f_fst_v_assoc, zero_comp, neg_zero, inr_f_desc_f_assoc,
    HomologicalComplex.comp_f, and_self]

@[simps]
noncomputable def triangleMap :
    (HomotopyCategory.quotient _ _).mapTriangle.obj (CochainComplex.MappingCone.triangle φ₁) ⟶
    (HomotopyCategory.quotient _ _).mapTriangle.obj (CochainComplex.MappingCone.triangle φ₂) where
  hom₁ := (HomotopyCategory.quotient _ _).map a
  hom₂ := (HomotopyCategory.quotient _ _).map b
  hom₃ := (HomotopyCategory.quotient _ _).map (map H)
  comm₁ := by
    dsimp
    simp only [← Functor.map_comp]
    exact HomotopyCategory.eq_of_homotopy _ _ H
  comm₂ := by
    dsimp
    simp only [← Functor.map_comp, triangleMap_comm₂]
  comm₃ := by
    dsimp
    rw [← Functor.map_comp_assoc, triangleMap_comm₃, Functor.map_comp, assoc, assoc]
    erw [← NatTrans.naturality]
    rfl

end map

section rotate

noncomputable def rotateHomotopyEquiv :
  HomotopyEquiv (K⟦(1 : ℤ)⟧) (mappingCone (inr φ)) where
  hom := lift (inr φ) (-(Cocycle.ofHom φ).leftShift 1 1 (zero_add 1))
    (-(inl φ).leftShift 1 0 (neg_add_self 1)) (by
      simp only [δ_neg, Cocycle.coe_neg, Cocycle.leftShift_coe, Cochain.neg_comp,
        Cochain.δ_leftShift _ 1 0 1 (neg_add_self 1) 0 (zero_add 1), ε_1, neg_smul, one_smul,
        neg_neg, δ_inl, Cochain.leftShift_comp_zero_cochain, Cocycle.ofHom_coe,
        Cochain.ofHom_comp, add_right_neg])
  inv := desc (inr φ) 0 (triangleδ φ) (by simp)
  homotopyHomInvId := Homotopy.ofEq (by
    ext p
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      lift_desc_f _ _ _ _ _ _ _ _ _ rfl, Cochain.zero_v, comp_zero, zero_add,
      (inl φ).leftShift_v 1 0 (neg_add_self 1) p p (add_zero p) (p+1) (by linarith),
      mul_zero, sub_self, EuclideanDomain.zero_div, ε_0, one_smul, triangleδ,
      Cocycle.homOf_f, Cocycle.rightShift_coe, Cocycle.coe_neg, Cochain.rightShift_neg,
      Cochain.neg_v, Cochain.rightShift_v _ 1 0 (zero_add 1) p p (add_zero p) (p+1) rfl,
      comp_neg, neg_comp, neg_neg, assoc, inl_v_fst_v_assoc, Iso.hom_inv_id])
  homotopyInvHomId := (Cochain.equivHomotopy _ _).symm
    ⟨-(snd (inr φ)).comp ((snd φ).comp (inl (inr φ)) (zero_add (-1))) (zero_add (-1)), by
      ext p
      simp only [Cochain.ofHom_comp, ofHom_desc, ofHom_lift, Cocycle.coe_neg,
        Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.zero_cochain_comp_v, δ_neg,
        Cochain.add_v, Cochain.neg_v, Cochain.ofHom_v, HomologicalComplex.id_f,
        from_ext_iff _ _ _ _ rfl, to_ext_iff _ _ _ _ rfl,
        assoc, δ_zero_cochain_comp _ _ _ (neg_add_self 1),
        Cochain.comp_v _ _ (add_neg_self 1) p (p + 1) p rfl (by linarith),
        Cochain.leftShift_v _ 1 1 (zero_add 1) p (p+1) rfl (p+1) (add_zero _),
        Cochain.leftShift_v _ 1 0 (neg_add_self 1) p p (add_zero p) (p+1) (by linarith),
        liftCochain_v_fst_v, comp_neg, inl_v_descCochain_v_assoc, Cochain.zero_v,
        zero_comp, neg_zero, δ_inl, Cochain.ofHom_comp, ε_neg, ε_1, ε_0, δ_snd,
        Cochain.neg_comp, Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, neg_smul,
        one_smul, neg_neg, Cochain.comp_add, inr_snd_assoc,
        Cochain.zero_cochain_comp_v, neg_add_rev, add_comp, neg_comp,
        inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero, add_zero, id_comp, neg_add_cancel_comm,
        inl_v_snd_v_assoc, inr_f_descCochain_v_assoc, inr_f_snd_v_assoc, inl_v_fst_v_assoc,
        inr_f_fst_v_assoc, inr_f_triangleδ_f_assoc, sub_self, one_mul,
        EuclideanDomain.zero_div, inl_v_triangleδ_f_assoc,
        Iso.refl_inv, Iso.refl_hom, shiftFunctor_obj_X, shiftFunctorObjXIso,
        HomologicalComplex.XIsoOfEq_rfl, zero_add,
        liftCochain_v_snd_v_assoc, inr_f_snd_v, inl_v_snd_v, add_left_neg]⟩

end rotate

end MappingCone

end CochainComplex

namespace HomotopyCategory

variable (C)

def distinguishedTriangles : Set (Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :=
  fun T => ∃ (X Y : CochainComplex C ℤ) (f : X ⟶ Y),
    Nonempty (T ≅ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
      (CochainComplex.MappingCone.triangle f))

variable {C}

lemma isomorphic_distinguished (T₁ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT₁ : T₁ ∈ distinguishedTriangles C) (T₂ : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (e : T₂ ≅ T₁) : T₂ ∈ distinguishedTriangles C := by
  obtain ⟨X, Y, f, ⟨e'⟩⟩ := hT₁
  exact ⟨X, Y, f, ⟨e ≪≫ e'⟩⟩

lemma contractible_distinguished (X : HomotopyCategory C (ComplexShape.up ℤ)) :
    contractibleTriangle X ∈ distinguishedTriangles C := by
  obtain ⟨X⟩ := X
  refine' ⟨_, _, 𝟙 X, ⟨_⟩⟩
  have h := (isZero_quotient_obj_iff _).2 ⟨CochainComplex.MappingCone.homotopyToZeroOfId X⟩
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) h.isoZero.symm
    (by simp) (h.eq_of_tgt _ _) (by dsimp ; ext)

lemma distinguished_cocone_triangle (X Y : HomotopyCategory C (ComplexShape.up ℤ)) (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory C (ComplexShape.up ℤ)) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := quotient_map_surjective f
  exact ⟨_, _, _, ⟨_, _, f, ⟨Iso.refl _⟩⟩⟩

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
  obtain ⟨a'', rfl⟩ := quotient_map_surjective a'
  obtain ⟨b'', rfl⟩ := quotient_map_surjective b'
  have H : Homotopy (φ₁ ≫ b'') (a'' ≫ φ₂) := homotopyOfEq _ _ (by
    have comm₁₁ := e₁.inv.comm₁
    have comm₁₂ := e₂.hom.comm₁
    dsimp at comm₁₁ comm₁₂
    simp only [Functor.map_comp, ha', hb', reassoc_of% comm₁₁,
      reassoc_of% fac, comm₁₂, assoc])
  let γ := e₁.hom ≫ CochainComplex.MappingCone.triangleMap H ≫ e₂.inv
  have comm₂ := γ.comm₂
  have comm₃ := γ.comm₃
  dsimp at comm₂ comm₃
  simp only [ha', hb', assoc, Iso.hom_inv_id_triangle_hom₁_assoc,
    Iso.hom_inv_id_triangle_hom₁, Iso.hom_inv_id_triangle_hom₂_assoc, comp_id] at comm₂ comm₃
  exact ⟨γ.hom₃, comm₂, by dsimp ; simpa only [assoc] using comm₃⟩

lemma rotate_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
  T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := sorry

instance : Pretriangulated (HomotopyCategory C (ComplexShape.up ℤ)) where
  distinguishedTriangles := distinguishedTriangles C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

end HomotopyCategory
