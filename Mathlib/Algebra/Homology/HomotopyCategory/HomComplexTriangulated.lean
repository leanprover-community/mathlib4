import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.Triangulated.Opposite
import Mathlib.Algebra.Category.GroupCat.Abelian

open CategoryTheory Category Limits Preadditive Pretriangulated.Opposite

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

lemma shiftFunctorOpIso_inv_app_f (K : (CochainComplex C ℤ)ᵒᵖ) (n m : ℤ) (h : n + m = 0) (i : ℤ) :
  ((Pretriangulated.shiftFunctorOpIso (CochainComplex C ℤ) n m h).inv.app K).unop.f i =
    (K.unop.XIsoOfEq (by dsimp; linarith)).hom := by
  obtain rfl : m = -n := by linarith
  rfl

lemma shiftFunctorOpIso_hom_app_f (K : (CochainComplex C ℤ)ᵒᵖ) (n m : ℤ) (h : n + m = 0) (i : ℤ) :
  ((Pretriangulated.shiftFunctorOpIso (CochainComplex C ℤ) n m h).hom.app K).unop.f i =
    (K.unop.XIsoOfEq (by dsimp; linarith)).hom := by
  obtain rfl : m = -n := by linarith
  rfl

lemma MappingCone.X_break {K L : CochainComplex AddCommGroupCat ℤ}
    {φ : K ⟶ L} {n : ℤ} (α : (mappingCone φ).X n) (m : ℤ) (hm : n + 1 = m) :
    ∃ (α₁ : K.X m) (α₂ : L.X n), α = (MappingCone.inl φ).v m n (by linarith) α₁ +
        (MappingCone.inr φ).f n α₂ :=
  ⟨(MappingCone.fst φ).1.v n m hm α,
    (MappingCone.snd φ).v n n (add_zero n) α, by
      erw [← comp_apply, ← comp_apply, ← AddMonoidHom.add_apply,
      ← MappingCone.id_X,
      id_apply]⟩

namespace HomComplex

@[simps! obj map_f_apply]
def functor (K : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex AddCommGroupCat ℤ where
  obj L := HomComplex K L
  map {L₁ L₂} φ :=
    { f := fun i => AddCommGroupCat.ofHom
        (AddMonoidHom.mk' (fun α => α.comp (Cochain.ofHom φ) (add_zero i)) (by simp)) }

def homotopyFunctorMap (K : CochainComplex C ℤ) {L₁ L₂ : CochainComplex C ℤ}
  {f₁ f₂ : L₁ ⟶ L₂} (h : Homotopy f₁ f₂) :
    Homotopy ((CochainComplex.HomComplex.functor K).map f₁)
      ((CochainComplex.HomComplex.functor K).map f₂) := (Cochain.equivHomotopy _ _).symm (by
  refine' ⟨Cochain.mk (fun p q hpq => AddCommGroupCat.ofHom
    (AddMonoidHom.mk' (fun α => α.comp (Cochain.ofHomotopy h) hpq) (by simp))), _⟩
  ext n (α : Cochain K L₁ n)
  apply Cochain.ext
  intro p q hpq
  dsimp
  simp only [Cochain.ofHom_v, functor_map_f_apply, Cochain.comp_zero_cochain_v]
  erw [Cochain.add_v]
  rw [δ_v (-1) 0 (neg_add_self 1) _ _ _ _ (n-1) (n+1) rfl rfl]
  dsimp
  simp only [add_left_neg, Int.negOnePow_zero, ComplexShape.up_Rel, not_true, one_smul, AddCommGroupCat.coe_comp,
    Function.comp_apply, HomComplex_d_apply, AddCommGroupCat.ofHom_apply, AddMonoidHom.mk'_apply,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
  rw [Cochain.add_v, δ_comp _ _ _ (n + 1) 0 n (by linarith) (by linarith) (by linarith),
    Cochain.add_v, Cochain.comp_v _ _ (add_zero n) p q q hpq (by linarith)]
  simp only [δ_ofHomotopy, Cochain.sub_v, Cochain.ofHom_v, comp_sub, Int.negOnePow_neg,
    Int.negOnePow_one, neg_smul, one_smul, Cochain.neg_v, neg_add_cancel_right, sub_add_cancel])

variable (C)

@[simps! obj map_app_f_apply]
def bifunctor : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤
    CochainComplex AddCommGroupCat ℤ where
  obj K := functor K.unop
  map {K₁ K₂} φ :=
    { app := fun L =>
        { f := fun i => AddCommGroupCat.ofHom
            (AddMonoidHom.mk' (fun α => (Cochain.ofHom φ.unop).comp α (zero_add i)) (by simp)) } }

variable {C}

def homotopyBifunctorMapApp {K₁ K₂: CochainComplex C ℤ} {f₁ f₂ : K₁ ⟶ K₂}
    (h : Homotopy f₁ f₂) (L : CochainComplex C ℤ) :
    Homotopy (((CochainComplex.HomComplex.bifunctor C).map f₁.op).app L)
      (((CochainComplex.HomComplex.bifunctor C).map f₂.op).app L) :=
  (Cochain.equivHomotopy _ _).symm (by
    refine' ⟨Cochain.mk (fun p q hpq => AddCommGroupCat.ofHom
      (AddMonoidHom.mk' (fun α => p.negOnePow • (Cochain.ofHomotopy h).comp α (by linarith)) (by simp))), _⟩
    ext n (α : Cochain K₂ L n)
    apply Cochain.ext
    intro p q hpq
    dsimp [bifunctor]
    erw [bifunctor_map_app_f_apply]--, bifunctor_map_app_f_apply]
    simp only [Opposite.unop_op, Quiver.Hom.unop_op, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    erw [Cochain.add_v]
    rw [δ_v (-1) 0 (neg_add_self 1) _ _ _ _ (n-1) (n+1) rfl rfl]
    dsimp
    simp only [δ_zsmul, add_left_neg, Int.negOnePow_zero, ComplexShape.up_Rel, not_true, one_smul,
      AddCommGroupCat.coe_comp, Function.comp_apply, HomComplex_d_apply, AddCommGroupCat.ofHom_apply,
      AddMonoidHom.mk'_apply]
    rw [δ_comp _ _ _ 0 (n+1) _ (by linarith) (by linarith) rfl]
    simp only [δ_ofHomotopy, Cochain.sub_comp, zsmul_sub, smul_add, smul_smul,
      Int.negOnePow_mul_self, one_smul, Int.negOnePow_succ, neg_smul, add_neg_cancel_comm,
      Cochain.sub_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, sub_add_cancel]
    rfl)

section

variable {K L : CochainComplex C ℤ} {n : ℤ}

@[simp]
lemma XIsoOfEq_hom_apply_v (α : Cochain K L n) (n' : ℤ) (h : n = n') (p q : ℤ) (hpq : p + n' = q) :
    (((HomComplex K L).XIsoOfEq h).hom α).v p q hpq = α.v p q (by linarith) := by
  subst h
  rfl

@[simp]
lemma XIsoOfEq_inv_apply_v (α : Cochain K L n) (n' : ℤ) (h : n' = n) (p q : ℤ) (hpq : p + n' = q) :
    (((HomComplex K L).XIsoOfEq h).inv α).v p q hpq = α.v p q (by linarith) := by
  subst h
  rfl

variable (K L n)

def rightShiftIso : HomComplex K (L⟦n⟧) ≅ (HomComplex K L)⟦n⟧ :=
  Iso.symm
    (HomologicalComplex.Hom.isoOfComponents
      (fun i => shiftFunctorObjXIso (HomComplex K L) n i (i + n) rfl ≪≫
        AddEquiv.toAddCommGroupCatIso (Cochain.rightShiftAddEquiv K L (i + n) n i rfl)) (by
      rintro i _ rfl
      dsimp
      erw [id_comp, id_comp]
      ext1 (α : Cochain K L (i + n))
      change δ i (i + 1) (Cochain.rightShift α n i rfl) =
        Cochain.rightShift (n.negOnePow • δ (i + n) (i + 1 + n) α) n (i + 1) rfl
      rw [Cochain.δ_rightShift α n i (i + 1) rfl _ rfl, Cochain.rightShift_zsmul]))

variable {K L n}

lemma rightShiftIso_hom_f_apply {i : ℤ} (α : (HomComplex K (L⟦n⟧)).X i) (j : ℤ) (h : j = i + n) :
    (rightShiftIso K L n).hom.f i α =
      (shiftFunctorObjXIso (HomComplex K L) n i j h).inv (α.rightUnshift j h.symm) := by
  subst h
  rfl

lemma rightShiftIso_inv_f_apply {i : ℤ} (α : ((HomComplex K L)⟦n⟧).X i) (j : ℤ) (h : j = i + n) :
    (rightShiftIso K L n).inv.f i α =
      ((shiftFunctorObjXIso (HomComplex K L) n i j h).hom α).rightShift n i h.symm := by
  subst h
  rfl

instance : (functor K).CommShift ℤ where
  iso n := NatIso.ofComponents (fun L => rightShiftIso K L n) (fun {L₁ L₂} φ => by
    ext i (α : Cochain K (L₁⟦n⟧) i)
    dsimp
    erw [rightShiftIso_hom_f_apply _ (i + n) rfl, rightShiftIso_hom_f_apply _ (i + n) rfl]
    simp only [HomComplex_X, shiftFunctor_obj_X, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, AddCommGroupCat.coe_id, id_eq]
    erw [functor_map_f_apply]
    apply Cochain.ext
    intro p q hpq
    obtain rfl : q = p + i + n := by linarith
    rw [Cochain.rightUnshift_v _ _ _ p (p + i + n) (by linarith) (p + i) rfl]
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, shiftFunctor_map_f',
      shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, assoc,
      α.rightUnshift_v (i + n) rfl p (p + i + n) (by linarith) (p + i) rfl]
    erw [comp_id, id_comp])
  zero := by
    ext L i (α : Cochain K (L⟦(0 : ℤ)⟧) i)
    dsimp
    erw [rightShiftIso_hom_f_apply α i (add_zero i).symm]
    apply Cochain.ext
    intro p q hpq
    simp only [HomComplex_X, shiftFunctor_obj_X, shiftFunctorObjXIso,
      Functor.CommShift.isoZero_hom_app, functor_obj,
      HomologicalComplex.comp_f, AddCommGroupCat.coe_comp, Function.comp_apply,
      functor_map_f_apply]
    erw [XIsoOfEq_inv_apply_v,
      α.rightUnshift_v i (add_zero i) p q (by linarith) q (by linarith),
      CochainComplex.shiftFunctorZero_inv_app_f]
    erw [XIsoOfEq_hom_apply_v]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, Cochain.comp_zero_cochain_v,
      Cochain.ofHom_v, CochainComplex.shiftFunctorZero_hom_app_f]
  add a b := by
    ext L i (α : Cochain K (L⟦a + b⟧) i)
    dsimp
    erw [rightShiftIso_hom_f_apply α (i + a + b) (by linarith)]
    apply Cochain.ext
    intro p q hpq
    dsimp
    simp only [Functor.CommShift.isoAdd_hom_app, functor_obj, Functor.comp_obj, NatIso.ofComponents_hom_app,
      HomologicalComplex.comp_f, HomComplex_X, shiftFunctor_map_f', AddCommGroupCat.coe_comp, Function.comp_apply,
      functor_map_f_apply, CochainComplex.shiftFunctorAdd_inv_app_f]
    dsimp
    erw [XIsoOfEq_inv_apply_v,
      α.rightUnshift_v (i + a + b) (by linarith) p q (by linarith) (p + i) rfl]
    erw [XIsoOfEq_hom_apply_v]
    erw [rightShiftIso_hom_f_apply _ (i + b) rfl]
    erw [rightShiftIso_hom_f_apply _ (i + a + b) (by linarith)]
    dsimp
    erw [XIsoOfEq_inv_apply_v]
    rw [Cochain.rightUnshift_v _ _ _ _ _ _ (p + i + b) (by linarith),
      Cochain.rightUnshift_v _ _ _ _ _ _ (p + i) (by linarith)]
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, shiftFunctor_obj_X, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, assoc]
    erw [id_comp]
    rw [CochainComplex.shiftFunctorAdd_hom_app_f]
    simp only [HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom]

instance (K : (CochainComplex C ℤ)ᵒᵖ) : ((bifunctor C).obj K).CommShift ℤ := by
  dsimp
  infer_instance

@[simp]
lemma functor_commShiftIso_hom_app (K L : CochainComplex C ℤ) (n : ℤ) :
    ((functor K).commShiftIso n).hom.app L = (rightShiftIso K L n).hom := rfl

@[simp]
lemma functor_commShiftIso_inv_app (K L : CochainComplex C ℤ) (n : ℤ) :
    ((functor K).commShiftIso n).inv.app L = (rightShiftIso K L n).inv := rfl

instance {K₁ K₂ : (CochainComplex C ℤ)ᵒᵖ} (φ : K₁ ⟶ K₂) :
    NatTrans.CommShift ((bifunctor C).map φ) ℤ where
  comm' n := by
    ext L i (α : Cochain K₁.unop (L⟦n⟧) i)
    dsimp
    erw [bifunctor_map_app_f_apply]
    apply Cochain.ext
    intro p q hpq
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    erw [rightShiftIso_hom_f_apply _ (i + n) rfl,
      rightShiftIso_hom_f_apply _ (i + n) rfl]
    dsimp
    simp only [Cochain.rightUnshift_v _ (i + n) rfl p q hpq (p + i) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, assoc]

section

variable (K) {L₁ L₂ : CochainComplex C ℤ} (φ : L₁ ⟶ L₂)
  [HasBinaryBiproducts C]

set_option maxHeartbeats 400000 in
@[simps]
noncomputable def rightMappingConeIsoX (i : ℤ) :
    (HomComplex K (mappingCone φ)).X i ≅ (mappingCone ((functor K).map φ)).X i where
  hom := AddMonoidHom.mk' (fun (α : Cochain K (mappingCone φ) i) =>
    (MappingCone.inl ((functor K).map φ)).v (i+1) i (by linarith) (Cochain.comp α (MappingCone.fst φ).1 rfl) +
      (MappingCone.inr ((functor K).map φ)).f i (Cochain.comp α (MappingCone.snd φ) (add_zero i))) (by
      intros
      dsimp
      rw [Cochain.add_comp, Cochain.add_comp,
        map_add, map_add]
      abel)
  inv := AddMonoidHom.mk'
    (fun α => Cochain.comp ((MappingCone.fst ((functor K).map φ)).1.v i (i+1) rfl α)
        (MappingCone.inl φ) (by linarith) +
      ((MappingCone.snd ((functor K).map φ)).v i i (add_zero i) α).comp
        (Cochain.ofHom (MappingCone.inr φ)) (add_zero i)) (by
          intros
          dsimp
          rw [map_add, map_add, Cochain.add_comp, Cochain.add_comp]
          abel)
  hom_inv_id := by
    ext (α : Cochain K (mappingCone φ) i)
    rw [MappingCone.cochain_to_ext_iff _ _ _ (i+1) rfl]
    constructor
    · dsimp
      simp only [map_add]
      erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply]
      simp only [HomComplex_X, MappingCone.inl_v_fst_v, id_apply, MappingCone.inr_f_fst_v,
        MappingCone.inl_v_snd_v, MappingCone.inr_f_snd_v]
      dsimp
      erw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, add_zero, zero_add,
        Cochain.add_comp]
      simp only [Cochain.comp_assoc_of_second_degree_eq_neg_third_degree,
        Cochain.comp_assoc_of_second_is_zero_cochain, Cochain.comp_zero, add_zero,
        MappingCone.inl_fst, Cochain.comp_id, Cochain.comp_assoc_of_first_is_zero_cochain,
        MappingCone.inr_fst]
    · dsimp
      simp only [map_add]
      erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply]
      simp only [HomComplex_X, MappingCone.inl_v_fst_v, id_apply, MappingCone.inr_f_fst_v,
        MappingCone.inl_v_snd_v, MappingCone.inr_f_snd_v]
      erw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, add_zero, zero_add,
        Cochain.add_comp]
      simp only [Cochain.comp_assoc_of_second_degree_eq_neg_third_degree, Cochain.comp_assoc_of_second_is_zero_cochain,
        Cochain.comp_assoc_of_third_is_zero_cochain, MappingCone.inl_snd, Cochain.comp_zero,
        Cochain.comp_assoc_of_first_is_zero_cochain, MappingCone.inr_snd, Cochain.comp_id, zero_add]
  inv_hom_id := by
    ext α
    obtain ⟨α₁, α₂, rfl⟩ := MappingCone.X_break α _ rfl
    dsimp
    rw [map_add, map_add]
    erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply]
    simp only [HomComplex_X, MappingCone.inl_v_fst_v, id_apply, MappingCone.inr_f_fst_v,
      MappingCone.inl_v_snd_v, MappingCone.inr_f_snd_v]
    erw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
    simp only [add_zero, zero_add]
    rw [Cochain.add_comp, Cochain.add_comp]
    simp only [Cochain.comp_assoc_of_second_degree_eq_neg_third_degree, MappingCone.inl_fst, Cochain.comp_id,
      Cochain.comp_assoc_of_second_is_zero_cochain, MappingCone.inr_fst, Cochain.comp_zero, add_zero,
      Cochain.comp_assoc_of_third_is_zero_cochain, MappingCone.inl_snd, MappingCone.inr_snd, zero_add]

/-
some proofs broke after merging, let us wait before fixing it

@[simps!]
noncomputable def rightMappingConeIso :
    HomComplex K (mappingCone φ) ≅ mappingCone ((HomComplex.functor K).map φ) :=
  HomologicalComplex.Hom.isoOfComponents (rightMappingConeIsoX K φ) (by
    rintro n _ rfl
    ext (α : Cochain K (mappingCone φ) n)
    obtain ⟨α₁, α₂, rfl⟩ := MappingCone.cochain_to_break _ α (n+1) rfl
    dsimp
    rw [map_add]
    erw [← comp_apply, ← comp_apply]
    simp only [HomComplex_X, ComplexShape.up_Rel, not_true, Cochain.add_comp,
      Cochain.comp_assoc_of_second_degree_eq_neg_third_degree, MappingCone.inl_fst, Cochain.comp_id,
      Cochain.comp_assoc_of_second_is_zero_cochain, MappingCone.inr_fst, Cochain.comp_zero, add_zero, comp_apply,
      HomologicalComplex.Hom.comm, Cochain.comp_assoc_of_third_is_zero_cochain, MappingCone.inl_snd,
      MappingCone.inr_snd, zero_add, δ_add,
      δ_comp α₁ (MappingCone.inl φ) (show _ = n by linarith) (n + 1 + 1) 0 (n + 1) rfl rfl (neg_add_self 1),
      MappingCone.δ_inl, Cochain.ofHom_comp, Int.negOnePow_neg, Int.negOnePow_one, neg_smul, one_smul, δ_comp_ofHom,
      Cochain.comp_assoc_of_first_is_zero_cochain, Cochain.neg_comp, map_neg, neg_zero]
    erw [HomComplex_d_apply, AddMonoidHom.map_add, Int.negOnePow_succ]
    dsimp
    erw [← comp_apply]
    rw [MappingCone.inl_v_d _ _ _ (n + 1 + 1) (by linarith) (by linarith)]
    dsimp
    erw [AddMonoidHom.sub_apply, comp_apply, comp_apply]
    dsimp
    simp
    abel_nf)

noncomputable def mappingConeTriangleIso :
    (functor K).mapTriangle.obj (MappingCone.triangle φ) ≅
      MappingCone.triangle ((HomComplex.functor K).map φ) := by
  refine' Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
    (rightMappingConeIso K φ) (by aesop_cat) _ _
  · dsimp
    rw [id_comp]
    ext i (α : Cochain K L₂ i)
    dsimp
    erw [rightMappingConeIso_hom_f_apply]
    simp only [Cochain.comp_assoc_of_second_is_zero_cochain, MappingCone.inr_fst, Cochain.comp_zero,
      MappingCone.inr_snd, Cochain.comp_id, add_left_eq_self]
    rw [map_zero]
  · dsimp
    rw [CategoryTheory.Functor.map_id, comp_id]
    ext i (α : Cochain K (mappingCone φ) i)
    obtain ⟨α₁, α₂, rfl⟩ := MappingCone.cochain_to_break _ α _ rfl
    apply Cochain.ext
    intro p q (hpq : p + (i + 1) = q)
    dsimp [MappingCone.triangleδ]
    erw [rightMappingConeIso_hom_f_apply]
    simp only [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.rightShift_coe, Cocycle.coe_neg, Cochain.rightShift_neg,
      Cochain.comp_neg, Cochain.add_comp, Cochain.comp_assoc_of_third_is_zero_cochain,
      Cochain.comp_assoc_of_second_is_zero_cochain, neg_add_rev, Cochain.neg_v,
      Cochain.comp_assoc_of_second_degree_eq_neg_third_degree, MappingCone.inl_fst, Cochain.comp_id,
      MappingCone.inr_fst, Cochain.comp_zero, add_zero, MappingCone.inl_snd, MappingCone.inr_snd, zero_add, map_add]
    rw [map_add, map_neg, map_neg]
    erw [← comp_apply, ← comp_apply]
    erw [rightShiftIso_hom_f_apply _ (i+1) rfl,
      rightShiftIso_hom_f_apply _ (i+1) rfl]
    rw [Cochain.add_v, Cochain.neg_v]
    dsimp
    erw [Cochain.rightUnshift_v _ _ _ _ _ _ (p + i) rfl]
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, shiftFunctor_obj_X, shiftFunctorObjXIso, assoc, comp_neg]
    erw [Cochain.rightShift_v _ _ _ _ _ _ _ q (by linarith)]
    dsimp
    simp only [assoc, Iso.inv_hom_id, comp_id, MappingCone.inr_f_fst_v, comp_zero, neg_zero, zero_add]
    rw [Cochain.neg_v]
    erw [Cochain.rightUnshift_v _ _ _ _ _ _ (p + i) rfl]
    dsimp
    rw [Cochain.comp_v _ _ (show i + 1 + (-1) = i by linarith) p q
      (p + i) (by linarith) (by linarith),
      Cochain.comp_v _ _ (add_zero (-1)) q (p + i) (p + i)
        (by linarith) (by linarith),
      Cochain.rightShift_v _ _ _ _ _ _ _ q (by linarith),
      Cochain.rightShift_v _ _ _ _ _ _ _ (i + 1) rfl]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, MappingCone.inl_v_fst_v_assoc, assoc, Iso.inv_hom_id, comp_id,
      HomComplex_X, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, MappingCone.inl_v_fst_v, MappingCone.inr_f_fst_v,
      neg_zero]
    rw [AddMonoidHom.zero_apply]
    simp only [add_zero]
    rfl-/

end

end

section

variable (n m : ℤ) (hm : n + m = 0) (K L : CochainComplex C ℤ)

def leftShiftIso : HomComplex (K⟦m⟧) L ≅ (HomComplex K L)⟦n⟧ :=
  Iso.symm
    (HomologicalComplex.Hom.isoOfComponents (fun i =>
      (shiftFunctorObjXIso (HomComplex K L) n i (i + n) rfl) ≪≫
        (AddEquiv.toAddCommGroupCatIso
          (Cochain.leftShiftAddEquiv K L (i+n) m i (by linarith)))) (by
            rintro i _ rfl
            dsimp
            erw [id_comp, id_comp]
            ext (α : Cochain K L (i + n))
            dsimp
            erw [Cochain.leftShiftAddEquiv_apply, Cochain.leftShiftAddEquiv_apply]
            erw [Cochain.leftShift_zsmul]
            rw [HomComplex_d_apply, α.δ_leftShift m i (i+1)
              (by linarith) (i + 1 + n) (by linarith)]
            obtain rfl : m = -n := by linarith
            simp only [Int.negOnePow_neg]))

variable {K L}

lemma leftShiftIso_hom_f_apply {i : ℤ} (α : (HomComplex (K⟦m⟧) L).X i) (j : ℤ) (h : j = i + n) :
  (leftShiftIso n m hm K L).hom.f i α =
    (shiftFunctorObjXIso (HomComplex K L) n i j h).inv (α.leftUnshift j (by linarith)) := by
  subst h
  rfl

lemma leftShiftIso_inv_f_apply {i : ℤ} (α : (HomComplex K L⟦n⟧).X i) (j : ℤ) (h : j = i + n) :
    (leftShiftIso n m hm K L).inv.f i α =
      Cochain.leftShift ((shiftFunctorObjXIso (HomComplex K L) n i j h).hom α)
        m i (by linarith) := by
  subst h
  rfl

namespace BifunctorFlipObjCommShift

variable (L)

noncomputable def iso :
    CategoryTheory.shiftFunctor (CochainComplex C ℤ)ᵒᵖ n ⋙ (Functor.flip (bifunctor C)).obj L ≅
      (Functor.flip (bifunctor C)).obj L ⋙
        CategoryTheory.shiftFunctor (CochainComplex AddCommGroupCat ℤ) n :=
  isoWhiskerRight (Pretriangulated.shiftFunctorOpIso
    (CochainComplex C ℤ) _ _ (add_neg_self n)) _ ≪≫ NatIso.ofComponents
      (fun K => leftShiftIso _ _ (add_neg_self n) K.unop L) (by
        intro K₁ K₂ φ
        ext i (α : Cochain (K₁.unop⟦-n⟧) L i)
        dsimp
        erw [leftShiftIso_hom_f_apply _ _ (add_neg_self n) _ (i + n) rfl,
          leftShiftIso_hom_f_apply _ _ (add_neg_self n) _ (i + n) rfl]
        simp only [HomComplex_X, shiftFunctor_obj_X, shiftFunctorObjXIso,
          HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, AddCommGroupCat.coe_id, id_eq]
        erw [bifunctor_map_app_f_apply, bifunctor_map_app_f_apply]
        dsimp
        apply Cochain.ext
        intro p q hpq
        rw [Cochain.leftUnshift_v _ (i+n) (by linarith) p q hpq (p + n) (by linarith),
          Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_cochain_comp_v,
          Cochain.leftUnshift_v _ (i+n) (by linarith) p q hpq (p + n) (by linarith),
          comp_zsmul, shiftFunctor_map_f'' φ.unop (-n) (p+n) p (by linarith)]
        dsimp
        simp only [assoc, Iso.inv_hom_id_assoc, Cochain.ofHom_v])

lemma iso_hom_app (K : (CochainComplex C ℤ)ᵒᵖ) :
    (iso n L).hom.app K =
      ((bifunctor C).map ((Pretriangulated.shiftFunctorOpIso _ _ _ hm).hom.app K)).app L ≫
        (leftShiftIso _ _ hm K.unop L).hom := by
  obtain rfl : m = -n := by linarith
  rfl

lemma iso_inv_app (K : (CochainComplex C ℤ)ᵒᵖ) :
    (iso n L).inv.app K =
      (leftShiftIso _ _ hm K.unop L).inv ≫
      ((bifunctor C).map ((Pretriangulated.shiftFunctorOpIso _ _ _ hm).inv.app K)).app L := by
  obtain rfl : m = -n := by linarith
  rfl

attribute [irreducible] iso

lemma two_mul_injective (a b : ℤ) (h : 2 * a = 2 * b) : a = b := by
  rw [← @EuclideanDomain.mul_div_cancel _ _ a 2 (by simp), mul_comm a 2, h]
  simp only [Int.mul_ediv_cancel_left]

lemma mul_pred_div_two_eq_even (n : ℤ) : ((2 * n) * (2 * n - 1))/2 = n * (2 * n - 1) :=
  (EuclideanDomain.eq_div_of_mul_eq_left (by simp) (by ring)).symm

lemma mul_pred_div_two_eq_odd (n : ℤ) : ((2 * n + 1) * (2 * n + 1 - 1))/2 = n * (2 * n + 1) :=
  (EuclideanDomain.eq_div_of_mul_eq_left (by simp) (by ring)).symm

lemma two_mul_mul_pred_div_two (a : ℤ) :
    2 * ((a * (a - 1))/2) = a * (a - 1) := by
  by_cases Even a
  · obtain ⟨n, hn⟩ := h
    obtain rfl : a = 2 * n := by linarith
    rw [mul_pred_div_two_eq_even]
    ring
  · rw [← Int.odd_iff_not_even] at h
    obtain ⟨n, rfl⟩ := h
    rw [mul_pred_div_two_eq_odd]
    ring

lemma signs_compatibility (a b i : ℤ) :
    (-(a + b) * i + -(a + b) * (-(a + b) - 1) / 2).negOnePow =
      (-a * (i + b) + -a * (-a - 1) / 2).negOnePow * (-b * i + -b * (-b - 1) / 2).negOnePow := by
  have h : (-(a + b) * (-(a + b) - 1)) / 2 = (-a * (-a -1))/2 + (-b * (-b -1))/2 + a * b := by
    apply two_mul_injective
    rw [two_mul_mul_pred_div_two, mul_add 2, mul_add 2, two_mul_mul_pred_div_two,
      two_mul_mul_pred_div_two]
    ring
  rw [← Int.negOnePow_add, Int.negOnePow_eq_iff, h]
  exact ⟨a * b, by ring⟩

end BifunctorFlipObjCommShift

/-
this broke after merging master

set_option maxHeartbeats 800000 in
noncomputable instance : ((bifunctor C).flip.obj L).CommShift ℤ where
  iso n := BifunctorFlipObjCommShift.iso n L
  zero := by
    ext K i (α : Cochain (K⟦0⟧).unop L i)
    dsimp
    rw [BifunctorFlipObjCommShift.iso_hom_app 0 0 (zero_add 0) L K]
    dsimp
    erw [leftShiftIso_hom_f_apply 0 0 (zero_add 0) _ i (add_zero i).symm]
    apply Cochain.ext
    intro p q hpq
    dsimp
    erw [XIsoOfEq_inv_apply_v, Cochain.leftUnshift_v _ i _ p q (by linarith) p (by linarith),
      zero_mul, zero_mul, zero_add, EuclideanDomain.zero_div, Int.negOnePow_zero, one_smul]
    erw [bifunctor_map_app_f_apply]
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, Functor.CommShift.isoZero_hom_app, Functor.flip_obj_obj,
      bifunctor_obj, functor_obj, Functor.flip_obj_map, HomologicalComplex.comp_f, HomComplex_X,
      AddCommGroupCat.coe_comp, Function.comp_apply, bifunctor_map_app_f_apply,
      shiftFunctorZero_inv_app_f]
    erw [XIsoOfEq_hom_apply_v]
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Pretriangulated.shiftFunctorZero_op_hom_app,
      unop_comp, HomologicalComplex.comp_f, assoc]
    simp only [Functor.op_obj, Opposite.unop_op, Functor.id_obj, Quiver.Hom.unop_op]
    rw [shiftFunctorZero_inv_app_f]
    rfl
  add a b := by
    ext K i (α : Cochain (K⟦a + b⟧).unop L i)
    dsimp
    simp only [Functor.CommShift.isoAdd_hom_app, Functor.flip_obj_obj, bifunctor_obj, functor_obj, Functor.comp_obj,
      Functor.flip_obj_map, HomologicalComplex.comp_f, HomComplex_X, shiftFunctor_map_f', AddCommGroupCat.coe_comp,
      Function.comp_apply, bifunctor_map_app_f_apply, Functor.op_obj, Opposite.unop_op,
      BifunctorFlipObjCommShift.iso_hom_app  _ _ (add_neg_self a),
      BifunctorFlipObjCommShift.iso_hom_app  _ _ (add_neg_self b),
      BifunctorFlipObjCommShift.iso_hom_app  _ _ (add_neg_self (a + b))]
    erw [bifunctor_map_app_f_apply, bifunctor_map_app_f_apply]
    dsimp
    apply Cochain.ext
    intro p q hpq
    dsimp at hpq ⊢
    erw [leftShiftIso_hom_f_apply _ _ (add_neg_self (a + b)) _ (i + a + b) (by linarith),
      XIsoOfEq_inv_apply_v,
      leftShiftIso_hom_f_apply _ _ (add_neg_self b) _ (i + b) (by linarith),
      comp_apply, leftShiftIso_hom_f_apply _ _ (add_neg_self a) _ (i + a + b) (by linarith)]
    dsimp
    rw [Cochain.leftUnshift_v _ (i + a + b) (by linarith) p q (by linarith) (p + a + b) (by linarith),
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, shiftFunctorAdd_inv_app_f]
    dsimp
    erw [XIsoOfEq_hom_apply_v, XIsoOfEq_inv_apply_v]
    rw [Cochain.leftUnshift_v _ (i + a + b) (by linarith) p q (by linarith) (p + a) (by linarith)]
    erw [bifunctor_map_app_f_apply]
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.leftUnshift_v _ (i + b) (by linarith) (p + a) q (by linarith) (p + a + b) (by linarith),
      comp_zsmul, comp_zsmul, smul_smul, Cochain.zero_cochain_comp_v,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.ofHom_v,
      BifunctorFlipObjCommShift.signs_compatibility]
    congr 1
    rw [← shiftFunctorAdd'_eq_shiftFunctorAdd,
      Pretriangulated.shiftFunctorAdd'_op_hom_app K a b (a + b) rfl _ _ _
        (add_neg_self a) (add_neg_self b) (add_neg_self (a + b)),
      Pretriangulated.shiftFunctor_op_map _ _ (add_neg_self b)]
    dsimp
    simp only [assoc, shiftFunctorOpIso_hom_app_f,
      shiftFunctorOpIso_inv_app_f, shiftFunctorAdd'_inv_app_f']
    dsimp [HomologicalComplex.XIsoOfEq]
    erw [id_comp, id_comp, id_comp, id_comp, id_comp, id_comp, id_comp]
    erw [eqToHom_trans_assoc, eqToHom_trans_assoc]-/

end

section

/-variable {K₁ K₂ : CochainComplex C ℤ} (φ : K₁ ⟶ K₂) (L : CochainComplex C ℤ)
  [HasBinaryBiproducts C]

set_option maxHeartbeats 1000000 in
@[simps! hom_apply inv_apply]
noncomputable def leftMappingConeIsoX (i j : ℤ) (hij : j + 1 = i) :
    (HomComplex (mappingCone φ) L).X i ≅
      (mappingCone (((bifunctor C).map φ.op).app L)).X j where
  hom := AddMonoidHom.mk' (fun (α : Cochain (mappingCone φ) L i) =>
    (MappingCone.inl (((bifunctor C).map φ.op).app L)).v i j (by linarith)
      ((Cochain.ofHom (MappingCone.inr φ)).comp α (zero_add i)) +
      j.negOnePow • (MappingCone.inr (((bifunctor C).map φ.op).app L)).f j
        ((MappingCone.inl φ).comp α (by linarith))) (fun α₁ α₂ => by
          dsimp
          rw [Cochain.comp_add, map_add, Cochain.comp_add, map_add, smul_add]
          abel)
  inv := AddMonoidHom.mk' (fun α =>
    (MappingCone.snd φ).comp ((MappingCone.fst
        (((bifunctor C).map φ.op).app L)).1.v j i hij α) (zero_add i) +
      j.negOnePow • ((MappingCone.fst φ).1.comp ((MappingCone.snd
        (((bifunctor C).map φ.op).app L)).v j j (add_zero j) α) (by linarith))) (fun α₁ α₂ => by
          dsimp
          rw [map_add, Cochain.comp_add, map_add, Cochain.comp_add, smul_add]
          abel)
  hom_inv_id := by
    ext (α : Cochain (mappingCone φ) L i)
    obtain ⟨α₁, α₂, rfl⟩ := MappingCone.cochain_from_break _ α j hij
    dsimp
    simp
    erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply]
    simp only [HomComplex_X, MappingCone.inl_v_fst_v, id_apply, MappingCone.inr_f_fst_v, MappingCone.inl_v_snd_v,
      MappingCone.inr_f_snd_v]
    rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, smul_zero, add_zero, zero_add,
      Cochain.comp_zsmul, smul_smul, Int.negOnePow_mul_self, one_smul]
    apply add_comm
  inv_hom_id := by
    ext α
    obtain ⟨α₁, α₂, rfl⟩ := MappingCone.X_break α i hij
    dsimp
    rw [map_add, map_add]
    erw [← comp_apply, ← comp_apply, ← comp_apply, ← comp_apply]
    dsimp
    simp only [MappingCone.inl_v_fst_v, HomComplex_X, id_apply,
      MappingCone.inr_f_fst_v, MappingCone.inl_v_snd_v, MappingCone.inr_f_snd_v]
    rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
    simp only [zero_add, add_zero]
    rw [Cochain.comp_add, Cochain.comp_add]
    simp [smul_smul]

set_option maxHeartbeats 400000 in
noncomputable def leftMappingConeIso :
    (HomComplex (mappingCone φ) L)⟦(1 : ℤ)⟧ ≅ (mappingCone (((bifunctor C).map φ.op).app L)) :=
  HomologicalComplex.Hom.isoOfComponents
      (fun i => leftMappingConeIsoX φ L (i+1) i rfl) (by
    -- needs some cleaning up...
    rintro n _ rfl
    ext (α : Cochain (mappingCone φ) L (n + 1))
    dsimp [leftMappingConeIsoX]
    simp
    erw [← comp_apply, ← comp_apply]
    rw [MappingCone.inl_v_d _ _ _ (n + 1 + 1) (by linarith) (by linarith),
      MappingCone.inr_f_d]
    erw [comp_apply]
    obtain ⟨α₁, α₂, rfl⟩ := MappingCone.cochain_from_break _ α n rfl
    simp
    erw [AddMonoidHom.sub_apply]
    erw [map_add]
    rw [Cochain.comp_add]
    rw [map_add]
    erw [AddMonoidHom.neg_apply]
    erw [HomComplex_d_apply]
    erw [HomComplex_d_apply]
    erw [δ_comp _ _ (add_comm 1 n) 2 (n+1) _ (by linarith) (by linarith) (by linarith)]
    simp
    rw [Cochain.comp_neg, Cochain.comp_add, Cochain.comp_neg]
    erw [AddMonoidHom.neg_apply]
    simp
    erw [map_zero, zero_add]
    rw [Cochain.comp_neg]
    erw [HomComplex_d_apply]
    rw [Cochain.comp_neg]
    simp
    rw [δ_comp _ _ (zero_add (n+1)) 1 (n + 1 + 1) _ (by linarith) (by linarith) (by linarith)]
    simp
    erw [comp_apply, comp_apply]
    erw [HomComplex_d_apply]
    rw [map_add, map_neg, smul_add, map_zsmul, smul_smul, smul_neg, Int.negOnePow_mul_self,
      one_smul, Int.negOnePow_succ, neg_smul, neg_neg]
    have : ∀ (a b c : (mappingCone (NatTrans.app ((bifunctor C).map φ.op) L)).X (n + 1)),
      a - b + c = -b + (c + a) := by intros; abel
    apply this)

lemma leftMappingConeIso_hom_f_apply (i j : ℤ) (h : i + 1 = j)
    (α : (HomComplex (mappingCone φ) L )⟦(1 : ℤ)⟧.X i) :
      (leftMappingConeIso φ L).hom.f i α =
        (leftMappingConeIsoX φ L j i h).hom
          ((shiftFunctorObjXIso (HomComplex (mappingCone φ) L) 1 i j h.symm).hom α) := by
  subst h
  rfl-/

/-set_option maxHeartbeats 400000 in
def mappingConeTriangleIso' :
    ((bifunctor C).flip.obj L).mapTriangle.obj
      ((Pretriangulated.triangleOpEquivalence (CochainComplex C ℤ)).functor.obj
          (Opposite.op (MappingCone.triangle φ))) ≅
            (MappingCone.triangle (((bifunctor C).map φ.op).app L)).invRotate := by
  refine' Pretriangulated.Triangle.isoMk _ _
    ((shiftEquiv (CochainComplex AddCommGroupCat ℤ) (1 : ℤ)).unitIso.app _ ≪≫
      (CategoryTheory.shiftFunctor (CochainComplex AddCommGroupCat ℤ) (-1 : ℤ)).mapIso
        (leftMappingConeIso φ L)) (Iso.refl _) (Iso.refl _) _ _ _
  · dsimp
    simp only [comp_id, comp_neg, assoc]
    ext i (α : Cochain (mappingCone φ) L i)
    obtain ⟨α₁, α₂, rfl⟩ := MappingCone.cochain_from_break _ α (i+ (-1)) (by linarith)
    rw [map_add]
    erw [bifunctor_map_app_f_apply, bifunctor_map_app_f_apply, MappingCone.inr_fst_assoc,
      zero_add, MappingCone.inr_snd_assoc]
    rw [HomologicalComplex.neg_f_apply, AddMonoidHom.neg_apply]
    simp only [functor_obj, HomComplex_X, Eq.ndrec, Int.rawCast, Int.cast_id, Nat.rawCast, Nat.cast_id, Int.ofNat_one,
      Int.ofNat_eq_coe, Int.ofNat_zero, eq_mp_eq_cast, HomologicalComplex.comp_f, shiftFunctor_map_f',
      AddCommGroupCat.coe_comp, Function.comp_apply]
    apply Cochain.ext
    intro p q hpq
    rw [Cochain.neg_v]
    erw [leftMappingConeIso_hom_f_apply _ _ _ i (by linarith)]
    rw [leftMappingConeIsoX_hom_apply]
    dsimp [MappingCone.triangleδ]
    rw [Cochain.rightShift_v _ _ _ _ _ _ _ i (by linarith)]
    dsimp
    simp only [neg_comp]
    sorry
  · dsimp
    simp
  · dsimp
    simp
    sorry-/

end

end HomComplex

end CochainComplex

namespace HomotopyCategory

namespace HomComplex

def functor' (K : CochainComplex C ℤ) :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤
      HomotopyCategory AddCommGroupCat (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift _
    (CochainComplex.HomComplex.functor K ⋙ HomotopyCategory.quotient _ _) (by
      intro L₁ L₂ f₁ f₂ ⟨h⟩
      apply HomotopyCategory.eq_of_homotopy
      exact CochainComplex.HomComplex.homotopyFunctorMap K h)

def functor'Factors (K : CochainComplex C ℤ) :
  HomotopyCategory.quotient C _ ⋙ functor' K ≅
    CochainComplex.HomComplex.functor K ⋙ HomotopyCategory.quotient AddCommGroupCat _ :=
  Quotient.lift.isLift _ _ _

noncomputable instance (K : CochainComplex C ℤ) :
    (functor' K).CommShift ℤ :=
  Quotient.liftCommShift _ _ _ _

instance (K : CochainComplex C ℤ) : NatTrans.CommShift (functor'Factors K).hom ℤ :=
  Quotient.liftCommShift_compatibility _ _ _ _

/-instance [HasZeroObject C] [HasBinaryBiproducts C] (K : CochainComplex C ℤ) :
    (functor' K).IsTriangulated where
  map_distinguished T hT := by
    obtain ⟨L₁, L₂, φ, ⟨e⟩⟩ := hT
    refine' isomorphic_distinguished _
      (mappingCone_triangle_distinguished ((CochainComplex.HomComplex.functor K).map φ)) _ _
    exact (functor' K).mapTriangle.mapIso e ≪≫
      (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫
      (Functor.mapTriangleIso (functor'Factors K)).app _ ≪≫
      (Functor.mapTriangleCompIso _ _).app _ ≪≫
      (HomotopyCategory.quotient AddCommGroupCat (ComplexShape.up ℤ)).mapTriangle.mapIso
        (CochainComplex.HomComplex.mappingConeTriangleIso K φ)-/

variable (C)

def bifunctor' : CochainComplex C ℤ ⥤
    (HomotopyCategory C (ComplexShape.up ℤ) ⥤ HomotopyCategory AddCommGroupCat (ComplexShape.up ℤ))ᵒᵖ where
  obj K := Opposite.op (functor' K)
  map {K₁ K₂} f :=
    Quiver.Hom.op (Quotient.natTransLift _
      (whiskerRight ((CochainComplex.HomComplex.bifunctor C).map f.op)
        (HomotopyCategory.quotient _ _)))

variable {C}

@[simp]
lemma bifunctor'_map_unop_quotient_obj {K₁ K₂ : CochainComplex C ℤ} (f : K₁ ⟶ K₂)
    (L : CochainComplex C ℤ) : ((bifunctor' C).map f).unop.app ((quotient _ _).obj L) =
      (quotient AddCommGroupCat (ComplexShape.up ℤ)).map
        (((CochainComplex.HomComplex.bifunctor C).map f.op).app L) := rfl

variable (C)

def bifunctor :
    (HomotopyCategory C (ComplexShape.up ℤ))ᵒᵖ ⥤
      HomotopyCategory C (ComplexShape.up ℤ) ⥤
        HomotopyCategory AddCommGroupCat (ComplexShape.up ℤ) :=
  Functor.leftOp (CategoryTheory.Quotient.lift _ (bifunctor' C) (by
    intro K₁ K₂ f₁ f₂ ⟨h⟩
    apply Quiver.Hom.unop_inj
    ext L
    apply HomotopyCategory.eq_of_homotopy
    exact CochainComplex.HomComplex.homotopyBifunctorMapApp h L.1))

noncomputable instance (K : (HomotopyCategory C (ComplexShape.up ℤ))ᵒᵖ) :
    ((bifunctor C).obj K).CommShift ℤ :=
  (inferInstance : (functor' K.unop.1).CommShift ℤ)

section

/-noncomputable instance [HasZeroObject C] [HasBinaryBiproducts C]
    (K : (HomotopyCategory C (ComplexShape.up ℤ))ᵒᵖ) :
    ((bifunctor C).obj K).IsTriangulated :=
  (inferInstance : (functor' K.unop.1).IsTriangulated)-/

end

/-
-- better develop a lifting of functors from the opposite category
-- of a quotient category, and do a general constructor for the
-- induced `CommShift` similarly as `liftCommShift` in `Shift.Quotient`
instance (L : HomotopyCategory C (ComplexShape.up ℤ)) :
    ((bifunctor C).flip.obj L).CommShift ℤ := sorry

instance [HasZeroObject C] [HasBinaryBiproducts C] (L : HomotopyCategory C (ComplexShape.up ℤ)) :
    ((bifunctor C).flip.obj L).IsTriangulated := by
  sorry-/

end HomComplex

end HomotopyCategory

-- TODO:
-- * compatibility with the mappingCone (done)
-- * the induced functor on the homotopy cateory is triangulated (done)
-- * do the same for the left shift
-- * state a compatibility (up to sign) of both left/right `CommShift`
-- * the right derived functor (on D^+ when we have enough injectives) computes the Ext
