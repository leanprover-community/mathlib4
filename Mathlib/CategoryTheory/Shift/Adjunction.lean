import Mathlib.CategoryTheory.Shift.CommShift

namespace CategoryTheory

open Category

lemma Iso.ext' {C : Type*} [Category C] {X Y : C} {e₁ e₂ : X ≅ Y}
    (h : e₁.inv = e₂.inv) : e₁ = e₂ := by
  change e₁.symm.symm = e₂.symm.symm
  congr 1
  ext
  exact h

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {G₁ G₂ G₃ : C ⥤ D} {F₁ F₂ F₃ : D ⥤ C} (adj₁ : G₁ ⊣ F₁) (adj₂ : G₂ ⊣ F₂) (adj₃ : G₃ ⊣ F₃)

@[simps! apply_app symm_apply_app]
def natTransEquiv : (G₁ ⟶ G₂) ≃ (F₂ ⟶ F₁) where
  toFun α := F₂.rightUnitor.inv ≫ whiskerLeft F₂ adj₁.unit ≫ whiskerLeft _ (whiskerRight α _) ≫
    (Functor.associator _ _ _).inv ≫ whiskerRight adj₂.counit F₁ ≫ F₁.leftUnitor.hom
  invFun β := G₁.leftUnitor.inv ≫ whiskerRight adj₂.unit G₁ ≫ whiskerRight (whiskerLeft _ β ) _ ≫
    (Functor.associator _ _ _ ).hom ≫ whiskerLeft G₂ adj₁.counit ≫ G₂.rightUnitor.hom
  left_inv α := by aesop_cat
  right_inv α := by
    ext X
    dsimp
    simp only [Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc,
      unit_naturality_assoc, right_triangle_components_assoc, ← α.naturality]

@[simp]
lemma natTransEquiv_id : natTransEquiv adj₁ adj₁ (𝟙 _) = 𝟙 _ := by aesop_cat

@[simp]
lemma natTransEquiv_symm_id : (natTransEquiv adj₁ adj₁).symm (𝟙 _) = 𝟙 _ := by aesop_cat

@[reassoc (attr := simp)]
lemma natTransEquiv_comp (α : G₁ ⟶ G₂) (β : G₂ ⟶ G₃) :
    natTransEquiv adj₂ adj₃ β ≫ natTransEquiv adj₁ adj₂ α =
      natTransEquiv adj₁ adj₃ (α ≫ β) := by
  ext X
  exact (adj₁.homEquiv _ _).symm.injective (by simp)

@[reassoc (attr := simp)]
lemma natTransEquiv_symm_comp (α : F₃ ⟶ F₂) (β : F₂ ⟶ F₁) :
    (natTransEquiv adj₁ adj₂).symm β ≫ (natTransEquiv adj₂ adj₃).symm α =
      (natTransEquiv adj₁ adj₃).symm (α ≫ β) := by
  obtain ⟨α', rfl⟩ := (natTransEquiv adj₂ adj₃).surjective α
  obtain ⟨β', rfl⟩ := (natTransEquiv adj₁ adj₂).surjective β
  simp

@[simps]
def natIsoEquiv : (G₁ ≅ G₂) ≃ (F₁ ≅ F₂) where
  toFun e :=
    { hom := natTransEquiv adj₂ adj₁ e.inv
      inv := natTransEquiv adj₁ adj₂ e.hom }
  invFun e :=
    { hom := (natTransEquiv adj₁ adj₂).symm e.inv
      inv := (natTransEquiv adj₂ adj₁).symm e.hom }
  left_inv e := by dsimp; ext1; simp only [Equiv.symm_apply_apply]
  right_inv e := by dsimp; ext1; simp only [Equiv.apply_symm_apply]

end Adjunction

namespace Adjunction

variable {C D : Type*} [Category C] [Category D]
  {G : C ⥤ D} {F : D ⥤ C} (adj : G ⊣ F) (A Z : Type*) [AddMonoid A] [AddGroup Z]
  [HasShift C A] [HasShift D A] [F.CommShift A] [G.CommShift A]
  [HasShift C Z] [HasShift D Z]

class CommShift : Prop where
  commShift_unit : NatTrans.CommShift adj.unit A := by infer_instance
  commShift_counit : NatTrans.CommShift adj.counit A := by infer_instance

namespace CommShift

attribute [instance] commShift_unit commShift_counit

lemma mk' (h : NatTrans.CommShift adj.unit A) :
    adj.CommShift A where
  commShift_counit := ⟨by
    intro a
    ext X
    have eq := NatTrans.CommShift.app_shift adj.unit a (F.obj X)
    dsimp at eq ⊢
    simp only [Functor.CommShift.commShiftIso_id_hom_app, Functor.comp_obj,
      Functor.id_obj, Functor.commShiftIso_comp_inv_app, id_comp,
      Functor.commShiftIso_comp_hom_app, assoc, comp_id] at eq ⊢
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_unit, adj.homEquiv_unit, F.map_comp]
    dsimp
    rw [adj.unit_naturality_assoc]
    simp only [eq, assoc, ← F.map_comp, Iso.inv_hom_id_app_assoc, right_triangle_components,
      ← F.commShiftIso_inv_naturality, ← Functor.map_comp_assoc, Functor.map_id, id_comp,
      Iso.hom_inv_id_app, Functor.comp_obj]⟩

end CommShift

variable {A}

@[reassoc]
lemma shift_unit_app [adj.CommShift A] (a : A) (X : C) :
    (adj.unit.app X)⟦a⟧' =
      adj.unit.app (X⟦a⟧) ≫
        F.map ((G.commShiftIso a).hom.app X) ≫
          (F.commShiftIso a).hom.app (G.obj X) := by
  simpa [Functor.commShiftIso_comp_hom_app] using NatTrans.CommShift.comm_app adj.unit a X

@[reassoc]
lemma shift_counit_app [adj.CommShift A] (a : A) (X : D) :
    (adj.counit.app X)⟦a⟧' =
      (G.commShiftIso a).inv.app (F.obj X) ≫ G.map ((F.commShiftIso a).inv.app X)
        ≫ adj.counit.app (X⟦a⟧) := by
  have eq := NatTrans.CommShift.comm_app adj.counit a X
  simp only [Functor.comp_obj, Functor.id_obj, Functor.commShiftIso_comp_hom_app, assoc,
    Functor.CommShift.commShiftIso_id_hom_app, comp_id] at eq
  simp only [← eq, Functor.comp_obj, ← G.map_comp_assoc, Iso.inv_hom_id_app,
    Functor.map_id, id_comp, Iso.inv_hom_id_app_assoc]

namespace RightAdjointCommShift

variable {Z}
variable (a b : Z) (h : b + a = 0)

noncomputable def adj₁ : G ⋙ shiftFunctor D b ⊣ shiftFunctor D a ⋙ F :=
  adj.comp (shiftEquiv' D b a h).toAdjunction

noncomputable def adj₂ : shiftFunctor C b ⋙ G ⊣ F ⋙ shiftFunctor C a :=
  (shiftEquiv' C b a h).toAdjunction.comp adj

variable [G.CommShift Z]

noncomputable def adj₃ : G ⋙ shiftFunctor D b ⊣ F ⋙ shiftFunctor C a :=
  (adj₂ adj a b h).ofNatIsoLeft (G.commShiftIso b)

noncomputable def iso' : shiftFunctor D a ⋙ F ≅ F ⋙ shiftFunctor C a :=
  Adjunction.natIsoEquiv (adj₁ adj a b h) (adj₃ adj a b h) (Iso.refl _)

noncomputable def iso : shiftFunctor D a ⋙ F ≅ F ⋙ shiftFunctor C a := iso' adj _ _ (neg_add_self a)

lemma iso_hom_app (X : D) :
    (iso adj a).hom.app X =
      (shiftFunctorCompIsoId C b a h).inv.app (F.obj ((shiftFunctor D a).obj X)) ≫
        (adj.unit.app ((shiftFunctor C b).obj (F.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
          (F.map ((G.commShiftIso b).hom.app (F.obj ((shiftFunctor D a).obj X))))⟦a⟧' ≫
            (F.map ((shiftFunctor D b).map (adj.counit.app ((shiftFunctor D a).obj X))))⟦a⟧' ≫
              (F.map ((shiftFunctorCompIsoId D a b
                (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app X))⟦a⟧' := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_self]
  simp [iso, iso', adj₃, ofNatIsoLeft, adj₂, comp, Equivalence.toAdjunction, shiftEquiv',
    equivHomsetLeftOfNatIso, adj₁]
  dsimp
  simp

lemma iso_inv_app (X : D) :
    (iso adj a).inv.app X =
      adj.unit.app ((shiftFunctor C a).obj (F.obj X)) ≫
          F.map ((shiftFunctorCompIsoId D b a h).inv.app (G.obj ((shiftFunctor C a).obj (F.obj X)))) ≫
            F.map ((shiftFunctor D a).map ((shiftFunctor D b).map ((G.commShiftIso a).hom.app (F.obj X)))) ≫
              F.map ((shiftFunctor D a).map ((shiftFunctorCompIsoId D a b
                  (by rw [← add_left_inj a, add_assoc, h, zero_add, add_zero])).hom.app
                    (G.obj (F.obj X)))) ≫
                F.map ((shiftFunctor D a).map (adj.counit.app X)) := by
  obtain rfl : b = -a := by rw [← add_left_inj a, h, neg_add_self]
  simp [iso, iso', adj₃, ofNatIsoLeft, adj₂, comp, Equivalence.toAdjunction, shiftEquiv',
    equivHomsetLeftOfNatIso, adj₁]

end RightAdjointCommShift

@[simps]
noncomputable def rightAdjointCommShift [G.CommShift Z] : F.CommShift Z where
  iso a := RightAdjointCommShift.iso adj a
  zero := by
    apply Iso.ext'
    ext X
    apply (adj.homEquiv _ _).symm.injective
    dsimp
    simp [RightAdjointCommShift.iso_inv_app adj _ _ (add_zero (0 : Z)) X]
    erw [← NatTrans.naturality_assoc]
    dsimp
    rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc, Functor.commShiftIso_zero,
      Functor.CommShift.isoZero_hom_app, assoc]
    erw [← NatTrans.naturality]
    rfl
  add a b := by
    apply Iso.ext'
    ext X
    apply (adj.homEquiv _ _).symm.injective
    dsimp
    simp [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_self (a + b)) X,
      RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_self a) X,
      RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_self b)]
    erw [← NatTrans.naturality_assoc]
    dsimp
    rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc]
    rw [Functor.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
    simp
    simp only [← Functor.map_comp_assoc, assoc]
    erw [← (shiftFunctorCompIsoId D _ _ (neg_add_self a)).inv.naturality]
    dsimp
    rw [← NatTrans.naturality]
    rw [← F.map_comp, assoc, shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app]
    dsimp
    rw [comp_id]
    simp only [Functor.map_comp, assoc]; congr 1; simp only [← assoc]; congr 1; simp only [assoc]
    erw [← NatTrans.naturality_assoc]
    dsimp
    rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc]
    simp only [← Functor.map_comp, ← Functor.map_comp_assoc, assoc]
    apply (adj.homEquiv _ _).injective
    dsimp
    simp only [Functor.map_comp, homEquiv_unit, Functor.id_obj, Functor.comp_obj, assoc,
      Functor.commShiftIso_hom_naturality_assoc]
    congr 1
    simp only [← F.map_comp, assoc]
    congr 2
    simp only [← Functor.map_comp, assoc]
    congr 1
    dsimp
    simp

lemma commShift_of_leftAdjoint [G.CommShift Z] :
    letI := adj.rightAdjointCommShift Z
    adj.CommShift Z := by
  suffices h : ∀ X (a : Z), (adj.unit.app X)⟦a⟧' = adj.unit.app (X⟦a⟧) ≫ F.map ((G.commShiftIso a).hom.app X) ≫
      (RightAdjointCommShift.iso adj a).hom.app (G.obj X) by
    letI := adj.rightAdjointCommShift Z
    apply CommShift.mk'
    refine' ⟨fun a => _⟩
    ext X
    dsimp
    simp only [Functor.CommShift.commShiftIso_id_hom_app, Functor.comp_obj,
      Functor.id_obj, id_comp, Functor.commShiftIso_comp_hom_app]
    exact h X a
  intro X a
  rw [← cancel_mono ((RightAdjointCommShift.iso adj a).inv.app (G.obj X)), assoc, assoc,
    Iso.hom_inv_id_app]
  dsimp
  rw [comp_id]
  simp [RightAdjointCommShift.iso_inv_app adj _ _ (neg_add_self a)]
  apply (adj.homEquiv _ _).symm.injective
  dsimp
  simp
  erw [← NatTrans.naturality_assoc]
  dsimp
  rw [shift_shiftFunctorCompIsoId_hom_app, Iso.inv_hom_id_app_assoc,
    Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp,
    left_triangle_components, Functor.map_id, comp_id]

end Adjunction

namespace Equivalence

variable {C D : Type*} [Category C] [Category D] (E : C ≌ D)
  (A Z : Type*) [AddMonoid A] [AddGroup Z]
  [HasShift C A] [HasShift D A] [HasShift C Z] [HasShift D Z]

class CommShift [E.functor.CommShift A] [E.inverse.CommShift A] : Prop where
  commShift_unitIso_hom : NatTrans.CommShift E.unitIso.hom A := by infer_instance
  commShift_counitIso_hom : NatTrans.CommShift E.counitIso.hom A := by infer_instance

namespace CommShift

attribute [instance] commShift_unitIso_hom commShift_counitIso_hom

instance [h : E.functor.CommShift A] : E.symm.inverse.CommShift A := h
instance [h : E.inverse.CommShift A] : E.symm.functor.CommShift A := h

lemma mk' [E.functor.CommShift A] [E.inverse.CommShift A]
    (h : NatTrans.CommShift E.unitIso.hom A) :
    E.CommShift A where
  commShift_counitIso_hom :=
    (Adjunction.CommShift.mk' E.toAdjunction A h).commShift_counit

lemma mk'' [E.functor.CommShift A] [E.inverse.CommShift A]
    (h : NatTrans.CommShift E.counitIso.hom A) :
    E.CommShift A where
  commShift_unitIso_hom := by
    have h' := NatTrans.CommShift.of_iso_inv E.counitIso A
    have : NatTrans.CommShift E.unitIso.symm.hom A :=
      (Adjunction.CommShift.mk' E.symm.toAdjunction A h').commShift_counit
    exact NatTrans.CommShift.of_iso_inv E.unitIso.symm A

instance [E.functor.CommShift A] [E.inverse.CommShift A] [E.CommShift A] :
    E.toAdjunction.CommShift A where
  commShift_unit := commShift_unitIso_hom
  commShift_counit := commShift_counitIso_hom


instance [E.functor.CommShift A] [E.inverse.CommShift A] [E.CommShift A] :
    E.symm.CommShift A := mk' _ _ (by
  dsimp only [Equivalence.symm, Iso.symm]
  infer_instance)

end CommShift

noncomputable def commShiftInverse [E.functor.CommShift Z] : E.inverse.CommShift Z :=
  E.toAdjunction.rightAdjointCommShift Z

lemma commShift_of_functor [E.functor.CommShift Z] :
    letI := E.commShiftInverse Z
    E.CommShift Z := by
  letI := E.commShiftInverse Z
  exact CommShift.mk' _ _ (E.toAdjunction.commShift_of_leftAdjoint Z).commShift_unit

noncomputable def commShiftFunctor [E.inverse.CommShift Z] : E.functor.CommShift Z :=
  E.symm.toAdjunction.rightAdjointCommShift Z

lemma commShift_of_inverse [E.inverse.CommShift Z] :
    letI := E.commShiftFunctor Z
    E.CommShift Z := by
  letI := E.commShiftFunctor Z
  apply CommShift.mk''
  have : NatTrans.CommShift E.counitIso.symm.hom Z := (E.symm.toAdjunction.commShift_of_leftAdjoint Z).commShift_unit
  exact NatTrans.CommShift.of_iso_inv E.counitIso.symm Z

end Equivalence

end CategoryTheory
