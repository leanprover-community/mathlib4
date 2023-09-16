import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Category.GroupCat.Abelian

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace CochainComplex

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
    dsimp
    erw [bifunctor_map_app_f_apply, bifunctor_map_app_f_apply]
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
      Cochain.sub_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, sub_add_cancel])

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
    rw [rightShiftIso_hom_f_apply _ (i + n) rfl, rightShiftIso_hom_f_apply _ (i + n) rfl]
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
    rw [XIsoOfEq_inv_apply_v,
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
    rw [XIsoOfEq_inv_apply_v,
      α.rightUnshift_v (i + a + b) (by linarith) p q (by linarith) (p + i) rfl]
    erw [XIsoOfEq_hom_apply_v]
    rw [rightShiftIso_hom_f_apply _ (i + b) rfl]
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
    rw [rightShiftIso_hom_f_apply _ (i + n) rfl,
      rightShiftIso_hom_f_apply _ (i + n) rfl]
    dsimp
    simp only [Cochain.rightUnshift_v _ (i + n) rfl p q hpq (p + i) rfl,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v, assoc]

section

variable (K) {L₁ L₂ : CochainComplex C ℤ} (φ : L₁ ⟶ L₂)
  [∀ (p : ℤ), HasBinaryBiproduct (L₁.X (p + 1)) (L₂.X p)]

set_option maxHeartbeats 400000 in
@[simps]
noncomputable def mappingConeIsoX (i : ℤ) :
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
      rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, add_zero, zero_add,
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
      rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, add_zero, zero_add,
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
    rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply]
    simp only [add_zero, zero_add]
    rw [Cochain.add_comp, Cochain.add_comp]
    simp only [Cochain.comp_assoc_of_second_degree_eq_neg_third_degree, MappingCone.inl_fst, Cochain.comp_id,
      Cochain.comp_assoc_of_second_is_zero_cochain, MappingCone.inr_fst, Cochain.comp_zero, add_zero,
      Cochain.comp_assoc_of_third_is_zero_cochain, MappingCone.inl_snd, MappingCone.inr_snd, zero_add]

@[simps!]
noncomputable def mappingConeIso :
    HomComplex K (mappingCone φ) ≅ mappingCone ((HomComplex.functor K).map φ) :=
  HomologicalComplex.Hom.isoOfComponents (mappingConeIsoX K φ) (by
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
    rw [HomComplex_d_apply, AddMonoidHom.map_add]
    erw [← comp_apply]
    rw [MappingCone.inl_v_d _ _ _ (n + 1 + 1) (by linarith) (by linarith)]
    dsimp
    erw [AddMonoidHom.sub_apply, comp_apply, comp_apply]
    abel)

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

end HomComplex

end HomotopyCategory

-- TODO:
-- * compatibility with the mappingCone
-- * the induced functor on the homotopy cateory is triangulated
-- * do the same for the left shift
-- * state a compatibility (up to sign) of both left/right `CommShift`
-- * the right derived functor (on D^+ when we have enough injectives) computes the Ext
