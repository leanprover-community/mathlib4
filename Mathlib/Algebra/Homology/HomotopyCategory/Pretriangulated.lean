import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Instances

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

variable {K₁ L₁ K₂ L₂ K₃ L₃ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁} {φ₂ : K₂ ⟶ L₂} (φ₃ : K₃ ⟶ L₃)
  {a : K₁ ⟶ K₂} {b : L₁ ⟶ L₂} (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂))
  (a' : K₂ ⟶ K₃) (b' : L₂ ⟶ L₃)

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

variable (φ₁ φ₂ a b)
variable (comm : φ₁ ≫ b = a ≫ φ₂) (comm' : φ₂ ≫ b' = a' ≫ φ₃)

noncomputable def map' : mappingCone φ₁ ⟶ mappingCone φ₂ :=
  desc φ₁ ((Cochain.ofHom a).comp (inl φ₂) (zero_add _)) (b ≫ inr φ₂)
    (by simp only [δ_ofHom_comp, δ_inl, reassoc_of% comm, Cochain.ofHom_comp])

lemma map'_eq_map : map' φ₁ φ₂ a b comm = map (Homotopy.ofEq comm) := by
  dsimp only [map, map']
  simp

lemma map'_id : map' φ φ (𝟙 _) (𝟙 _) (by rw [id_comp, comp_id]) = 𝟙 _ := by
  ext n
  simp [from_ext_iff _ _ _ (n+1) rfl, map']

lemma map'_comp : map' φ₁ φ₃ (a ≫ a') (b ≫ b') (by rw [reassoc_of% comm, comm', assoc]) =
    map' φ₁ φ₂ a b comm ≫ map' φ₂ φ₃ a' b' comm' := by
  ext n
  simp [from_ext_iff _ _ _ (n+1) rfl, map']

noncomputable def arrowFunctor : Arrow (CochainComplex C ℤ) ⥤ CochainComplex C ℤ where
  obj f := mappingCone f.hom
  map {f₁ f₂} φ := map' f₁.hom f₂.hom φ.left φ.right φ.w.symm
  map_id f := map'_id f.hom
  map_comp {f₁ f₂ f₃}  φ₁ φ₂ := map'_comp f₁.hom f₂.hom f₃.hom φ₁.left φ₁.right
    φ₂.left φ₂.right φ₁.w.symm φ₂.w.symm

@[simps]
noncomputable def triangleMap' :
    CochainComplex.MappingCone.triangle φ₁ ⟶ CochainComplex.MappingCone.triangle φ₂ where
  hom₁ := a
  hom₂ := b
  hom₃ := map' _ _ _ _ comm
  comm₁ := comm
  comm₂ := by dsimp [triangle, map'] ; simp only [inr_desc]
  comm₃ := by dsimp ; simp only [map'_eq_map, triangleMap_comm₃]

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

noncomputable def rotateHomotopyEquivComm₂Homotopy :
  Homotopy (triangleδ φ ≫ (rotateHomotopyEquiv φ).hom)
    (inr (CochainComplex.MappingCone.inr φ)) := (Cochain.equivHomotopy _ _).symm
      ⟨-(snd φ).comp ((inl (inr φ))) (zero_add (-1)), by
        ext p
        dsimp [rotateHomotopyEquiv]
        simp only [Cochain.ofHom_comp, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
          lift_f _ _ _ _ p (p+1) rfl,
          Cocycle.coe_neg, Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.neg_v,
          Cochain.leftShift_v _ 1 1 (zero_add 1) p (p + 1) rfl (p + 1) (add_zero _),
          Cochain.leftShift_v _ 1 0 (neg_add_self 1) p p (add_zero p) (p + 1) (by linarith),
          δ_comp _ _ (zero_add (-1)) 1 0 0 (neg_add_self 1) (zero_add 1) (neg_add_self 1),
          Cochain.comp_v _ _ (add_neg_self 1) p (p + 1) p rfl (by linarith),
          from_ext_iff _ _ _ _ rfl, shiftFunctor_obj_X, mul_one, sub_self,
          mul_zero, EuclideanDomain.zero_div, add_zero, ε_1, shiftFunctorObjXIso,
          HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, id_comp, neg_smul,
          one_smul, neg_neg, ε_0, neg_comp, comp_add, comp_neg, δ_neg, δ_inl,
          ε_neg, δ_snd, Cochain.neg_comp, inl_v_triangleδ_f_assoc, Iso.refl_inv,
          Cochain.comp_assoc_of_second_is_zero_cochain, smul_neg, neg_add_rev, Cochain.add_v,
          inl_v_fst_v_assoc, inl_v_snd_v_assoc, zero_comp, neg_zero, inr_f_triangleδ_f_assoc,
          inr_f_fst_v_assoc, inr_f_snd_v_assoc, zero_add, add_left_neg, and_self]⟩

@[reassoc (attr := simp)]
lemma rotateHomotopyEquiv_comm₂ :
    (HomotopyCategory.quotient _ _ ).map (triangleδ φ) ≫
      (HomotopyCategory.quotient _ _ ).map (rotateHomotopyEquiv φ).hom =
      (HomotopyCategory.quotient _ _ ).map (inr (inr φ)) := by
  simpa only [Functor.map_comp]
    using HomotopyCategory.eq_of_homotopy _ _  (rotateHomotopyEquivComm₂Homotopy φ)

@[reassoc (attr := simp)]
lemma rotateHomotopyEquiv_comm₃ :
    (rotateHomotopyEquiv φ).hom ≫ triangleδ (inr φ) = -φ⟦1⟧' := by
  ext p
  dsimp [rotateHomotopyEquiv]
  simp only [lift_f _ _ _ _ p (p+1) rfl, Cocycle.coe_neg, Cochain.neg_v,
    Cocycle.leftShift_coe, Cocycle.ofHom_coe, neg_comp, add_comp, assoc,
    inl_v_triangleδ_f, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_neg, comp_id, neg_neg,
    inr_f_triangleδ_f, comp_zero, neg_zero, add_zero,
    Cochain.leftShift_v _ 1 1 (zero_add 1) p (p+1) rfl (p+1) (by linarith), mul_one,
    sub_self, EuclideanDomain.zero_div, one_mul, ε_1, neg_smul, one_smul, Iso.refl_hom,
    id_comp, Cochain.ofHom_v]

@[reassoc (attr := simp)]
lemma rotateHomotopyEquiv_comm₃' :
    (HomotopyCategory.quotient _ _).map (rotateHomotopyEquiv φ).hom ≫
      (HomotopyCategory.quotient _ _).map (triangleδ (inr φ)) =
      -(HomotopyCategory.quotient _ _).map (φ⟦1⟧') := by
  rw [← Functor.map_comp, rotateHomotopyEquiv_comm₃, Functor.map_neg]

end rotate

section shift

noncomputable def shiftIso (n : ℤ) : (mappingCone φ)⟦n⟧ ≅ mappingCone (φ⟦n⟧') where
  hom := lift _ (ε n • (fst φ).shift n) ((snd φ).shift n) (by
    ext ⟨p, q, hpq⟩
    dsimp
    simp only [Cochain.δ_shift, δ_snd, Cochain.shift_neg, smul_neg,
      Cochain.neg_v, Cochain.zsmul_v, Cochain.shift_v, Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, shiftFunctor_map_f', zsmul_comp, neg_add_self])
  inv := desc _ (ε n • (inl φ).shift n) ((inr φ)⟦n⟧') (by
    ext p
    dsimp
    simp only [δ_zsmul, Cochain.δ_shift, δ_inl, Cochain.ofHom_comp, smul_smul,
      mul_ε_self, one_smul, Cochain.shift_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      shiftFunctor_map_f'])
  hom_inv_id := by
    ext p
    dsimp
    simp only [lift_f _ _ _ _ _ _ rfl, desc_f _ _ _ _ _ _ rfl,
      Cocycle.coe_zsmul, Cocycle.shift_coe, Cochain.zsmul_v, Cochain.shift_v,
      shiftFunctor_map_f', comp_add, add_comp, assoc, inl_v_fst_v_assoc, inr_f_fst_v_assoc,
      zero_comp, comp_zero, add_zero, inl_v_snd_v_assoc, inr_f_snd_v_assoc, zero_add,
      comp_zsmul, zsmul_comp, smul_smul, mul_ε_self, one_smul, smul_zero]
    exact (id φ (p+n) (p+1+n) (by linarith)).symm
  inv_hom_id := by
    ext p
    dsimp
    simp only [lift_f _ _ _ _ _ _ rfl, desc_f _ _ _ _ _ _ rfl,
      Cochain.zsmul_v, Cochain.shift_v, comp_zsmul, shiftFunctor_map_f',
      Cocycle.coe_zsmul, Cocycle.shift_coe, zsmul_comp, comp_add, add_comp, assoc,
      inl_v_fst_v_assoc, inr_f_fst_v_assoc, zero_comp, comp_zero, add_zero, smul_smul,
      mul_ε_self, one_smul, inl_v_snd_v_assoc, smul_zero, inr_f_snd_v_assoc, zero_add]
    exact (id (φ⟦n⟧') p (p+1) (by linarith)).symm

set_option maxHeartbeats 400000 in
noncomputable def shiftTriangleIso (n : ℤ) :
    (Triangle.shiftFunctor _ n).obj (triangle φ) ≅ triangle (φ⟦n⟧') :=
  Triangle.isoMk _ _ (Iso.refl _) (mulIso ((-1 : Units ℤ) ^ n) (Iso.refl _)) (shiftIso φ n)
    (by
      dsimp
      simp only [zsmul_comp, comp_zsmul, smul_smul, id_comp, comp_id]
      erw [mul_ε_self, one_smul])
    (by
      ext p
      dsimp [shiftIso]
      rw [lift_f _ _ _ _ p (p+1) rfl]
      simp only [Cocycle.coe_zsmul, Cocycle.shift_coe, Cochain.zsmul_v,
        Cochain.shift_v, zsmul_comp, comp_add, comp_zsmul, inr_f_fst_v_assoc, zero_comp,
        inr_f_snd_v_assoc, id_comp, smul_smul, mul_ε_self, one_smul, zero_add]
      rfl)
    (by
      ext p
      dsimp [shiftIso]
      rw [lift_f _ _ _ _ p (p+1) rfl]
      simp only [Cocycle.coe_zsmul, Cocycle.shift_coe, Cochain.zsmul_v, Cochain.shift_v,
        add_comp, assoc, inl_v_triangleδ_f, shiftFunctor_obj_X, shiftFunctorObjXIso,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_neg, comp_id, inr_f_triangleδ_f,
        comp_zero, add_zero, zsmul_comp, shiftFunctorComm_hom_app_f]
      dsimp [triangleδ]
      simp only [Cochain.rightShift_v _ 1 0 (zero_add 1) (p+n) (p+n) (add_zero _) (p+n+1) rfl,
        shiftFunctorObjXIso, assoc, neg_comp, smul_neg, neg_inj, Cochain.neg_v,
        HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, comp_id,
        Cochain.v_comp_XIsoOfEq_hom_assoc]
      erw [comp_id])

end shift

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

lemma distinguished_cocone_triangle {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    ∃ (Z : HomotopyCategory C (ComplexShape.up ℤ)) (g : Y ⟶ Z) (h : Z ⟶ X⟦1⟧),
      Triangle.mk f g h ∈ distinguishedTriangles C := by
  obtain ⟨X⟩ := X
  obtain ⟨Y⟩ := Y
  obtain ⟨f, rfl⟩ := (quotient _ _).map_surjective f
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
  obtain ⟨a'', rfl⟩ := (quotient _ _).map_surjective a'
  obtain ⟨b'', rfl⟩ := (quotient _ _).map_surjective b'
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

lemma rotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) : T.rotate ∈ distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  let T₀ := (quotient C (ComplexShape.up ℤ)).mapTriangle.obj
    (CochainComplex.MappingCone.triangle φ)
  suffices T₀.rotate ∈ distinguishedTriangles C from
    isomorphic_distinguished _ this _ ((rotate _).mapIso e)
  refine' ⟨_, _ , CochainComplex.MappingCone.inr φ, ⟨_⟩⟩
  refine' Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (((quotient C (ComplexShape.up ℤ)).commShiftIso (1 : ℤ)).symm.app K ≪≫
      HomotopyCategory.isoOfHomotopyEquiv (CochainComplex.MappingCone.rotateHomotopyEquiv φ)) _ _ _
  . dsimp
    simp only [comp_id, id_comp]
  . dsimp
    simp only [assoc, Iso.hom_inv_id_app_assoc,
      CochainComplex.MappingCone.rotateHomotopyEquiv_comm₂, id_comp]
  . dsimp
    simp only [CategoryTheory.Functor.map_id, comp_id, assoc,
      CochainComplex.MappingCone.rotateHomotopyEquiv_comm₃'_assoc,
      neg_comp, comp_neg, neg_inj]
    erw [← NatTrans.naturality_assoc, Iso.inv_hom_id_app, comp_id]
    rfl

lemma shift_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) (n : ℤ) :
      (Triangle.shiftFunctor _ n).obj T ∈ distinguishedTriangles C := by
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  let T₀ := (quotient _ _).mapTriangle.obj (CochainComplex.MappingCone.triangle φ)
  suffices (Triangle.shiftFunctor _ n).obj T₀ ∈ distinguishedTriangles C from
    isomorphic_distinguished _ this _ ((Triangle.shiftFunctor _ n).mapIso e)
  exact ⟨_, _, φ⟦n⟧',
    ⟨((quotient C (ComplexShape.up ℤ)).mapTriangleCommShiftIso n).symm.app _ ≪≫
      (quotient _ _).mapTriangle.mapIso (CochainComplex.MappingCone.shiftTriangleIso φ n)⟩⟩

lemma invRotate_distinguished_triangle' (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distinguishedTriangles C) : T.invRotate ∈ distinguishedTriangles C := by
  let e := (invRotateIsoRotateRotateShiftFunctorNegOne _).app T
  refine' isomorphic_distinguished  _ _ _ e
  apply shift_distinguished_triangle
  apply rotate_distinguished_triangle'
  apply rotate_distinguished_triangle'
  exact hT

lemma rotate_distinguished_triangle (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ))) :
    T ∈ distinguishedTriangles C ↔ T.rotate ∈ distinguishedTriangles C := by
  constructor
  . exact rotate_distinguished_triangle' T
  . intro hT
    exact isomorphic_distinguished _ (invRotate_distinguished_triangle' T.rotate hT) _
      ((triangleRotation _).unitIso.app T)

instance : Pretriangulated (HomotopyCategory C (ComplexShape.up ℤ)) where
  distinguishedTriangles := distinguishedTriangles C
  isomorphic_distinguished := isomorphic_distinguished
  contractible_distinguished := contractible_distinguished
  distinguished_cocone_triangle := distinguished_cocone_triangle
  rotate_distinguished_triangle := rotate_distinguished_triangle
  complete_distinguished_triangle_morphism := complete_distinguished_triangle_morphism

lemma mappingCone_triangle_distinguished {X Y : CochainComplex C ℤ} (f : X ⟶ Y) :
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.obj
      (CochainComplex.MappingCone.triangle f) ∈ distTriang (HomotopyCategory _ _) :=
  ⟨_, _, f, ⟨Iso.refl _⟩⟩

end HomotopyCategory
