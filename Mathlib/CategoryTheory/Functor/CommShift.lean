import Mathlib.CategoryTheory.Shift

namespace CategoryTheory

namespace Functor

variable {C D E : Type _} [Category C] [Category D] [Category E]
  (F : C ⥤ D) (G : D ⥤ E) (A : Type _) [AddMonoid A]
  [HasShift C A] [HasShift D A] [HasShift E A]

namespace CommShift

@[simps!]
noncomputable def iso_zero :
  shiftFunctor C (0 : A) ⋙ F ≅ F ⋙ shiftFunctor D (0 : A) :=
  isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫
     F.rightUnitor.symm ≪≫ isoWhiskerLeft F (shiftFunctorZero D A).symm

variable {F A}

@[simps!]
noncomputable def iso_add' {a b c : A} (h : a + b = c)
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C c ⋙ F ≅ F ⋙ shiftFunctor D c :=
  isoWhiskerRight (shiftFunctorAdd' C _ _ _ h) F ≪≫ Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ e₂ ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e₁ _ ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftFunctorAdd' D _ _ _ h).symm

noncomputable def iso_add {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) :
    shiftFunctor C (a + b) ⋙ F ≅ F ⋙ shiftFunctor D (a + b) :=
  CommShift.iso_add' rfl e₁ e₂

@[simp]
lemma iso_add_hom_app  {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.iso_add e₁ e₂).hom.app X =
        F.map ((shiftFunctorAdd C a b).hom.app X) ≫ e₂.hom.app ((shiftFunctor C a).obj X) ≫
          (shiftFunctor D b).map (e₁.hom.app X) ≫ (shiftFunctorAdd D a b).inv.app (F.obj X) := by
  simp only [iso_add, iso_add'_hom_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

@[simp]
lemma iso_add_inv_app  {a b : A}
    (e₁ : shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a)
    (e₂ : shiftFunctor C b ⋙ F ≅ F ⋙ shiftFunctor D b) (X : C) :
      (CommShift.iso_add e₁ e₂).inv.app X = (shiftFunctorAdd D a b).hom.app (F.obj X) ≫
        (shiftFunctor D b).map (e₁.inv.app X) ≫ e₂.inv.app ((shiftFunctor C a).obj X) ≫
        F.map ((shiftFunctorAdd C a b).inv.app X) := by
  simp only [iso_add, iso_add'_inv_app, shiftFunctorAdd'_eq_shiftFunctorAdd]

end CommShift

structure CommShift where
  iso : ∀ (a : A), shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a
  zero : iso 0 = CommShift.iso_zero F A := by aesop_cat
  add : ∀ (a b : A), iso (a + b) = CommShift.iso_add (iso a) (iso b) := by aesop_cat

namespace CommShift

variable (C)

def id : CommShift (𝟭 C) A where
  iso := fun a => rightUnitor _ ≪≫ (leftUnitor _).symm

variable {C F G A}

variable (hF : F.CommShift A) (hG : G.CommShift A)

@[simps!]
def comp_iso (a : A) :
    shiftFunctor C a ⋙ (F ⋙ G) ≅ (F ⋙ G) ⋙ shiftFunctor E a := by
  refine' (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (hF.iso a) _ ≪≫
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (hG.iso a) ≪≫
    (Functor.associator _ _ _).symm

def comp :
    (F ⋙ G).CommShift A where
  iso := comp_iso hF hG
  zero := by
    ext X
    simp only [comp_obj, comp_iso_hom_app, iso_zero_hom_app, comp_map,
      CommShift.zero, Category.assoc, ← G.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp
    rw [Category.comp_id]
  add := fun a b => by
    ext X
    simp only [comp_obj, comp_iso_hom_app, iso_add_hom_app, comp_map, Category.assoc,
      CommShift.add, ← G.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
    simp only [map_comp, Category.assoc]
    erw [← NatTrans.naturality_assoc]
    rfl

end CommShift

class HasCommShift where
  commShift : CommShift F A

variable {A}

def commShiftIso [F.HasCommShift A] (a : A) :
    shiftFunctor C a ⋙ F ≅ F ⋙ shiftFunctor D a :=
  (HasCommShift.commShift : CommShift F A).iso a

variable (A)

lemma commShiftIso_zero [F.HasCommShift A] :
  F.commShiftIso (0 : A) = CommShift.iso_zero F A :=
  (HasCommShift.commShift : CommShift F A).zero

variable {A}

lemma commShiftIso_add [F.HasCommShift A] (a b : A):
  F.commShiftIso (a + b) = CommShift.iso_add (F.commShiftIso a) (F.commShiftIso b) :=
  (HasCommShift.commShift : CommShift F A).add a b

lemma commShiftIso_add' [F.HasCommShift A] {a b c : A} (h : a + b = c) :
  F.commShiftIso c = CommShift.iso_add' h (F.commShiftIso a) (F.commShiftIso b) := by
  subst h
  simp only [commShiftIso_add, CommShift.iso_add]

variable (A)

instance HasCommShift.comp [F.HasCommShift A] [G.HasCommShift A] :
    (F ⋙ G).HasCommShift A :=
  ⟨(HasCommShift.commShift : CommShift F A).comp (HasCommShift.commShift : CommShift G A)⟩

variable {A}

lemma commShiftIso_comp_hom_app [F.HasCommShift A] [G.HasCommShift A] (a : A) (X : C) :
    (commShiftIso (F ⋙ G) a).hom.app X =
      G.map ((commShiftIso F a).hom.app X) ≫ (commShiftIso G a).hom.app (F.obj X) := by
  apply CommShift.comp_iso_hom_app

lemma commShiftIso_comp_inv_app [F.HasCommShift A] [G.HasCommShift A] (a : A) (X : C) :
    (commShiftIso (F ⋙ G) a).inv.app X =
      (commShiftIso G a).inv.app (F.obj X) ≫ G.map ((commShiftIso F a).inv.app X) := by
  apply CommShift.comp_iso_inv_app

end Functor

namespace NatTrans

variable {C D : Type _} [Category C] [Category D]
  {F₁ F₂ F₃ : C ⥤ D} (τ : F₁ ⟶ F₂) (τ' : F₂ ⟶ F₃) (e : F₁ ≅ F₂)
  (A : Type _) [AddMonoid A] [HasShift C A] [HasShift D A]
  [F₁.HasCommShift A] [F₂.HasCommShift A] [F₃.HasCommShift A]

class CommShift : Prop :=
  comm' : ∀ (a : A), (F₁.commShiftIso a).hom ≫ whiskerRight τ _ =
    whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom

namespace CommShift

section

variable {A}
variable [NatTrans.CommShift τ A]

lemma comm (a : A) : (F₁.commShiftIso a).hom ≫ whiskerRight τ _ =
    whiskerLeft _ τ ≫ (F₂.commShiftIso a).hom := by
  apply comm'

@[reassoc]
lemma comm_app (a : A) (X : C) :
    (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' =
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X :=
  NatTrans.congr_app (comm τ a) X

lemma shift_app (a : A) (X : C) :
    (τ.app X)⟦a⟧' = (F₁.commShiftIso a).inv.app X ≫
      τ.app (X⟦a⟧) ≫ (F₂.commShiftIso a).hom.app X := by
  rw [← comm_app, Iso.inv_hom_id_app_assoc]

lemma app_shift (a : A) (X : C) :
    τ.app (X⟦a⟧) = (F₁.commShiftIso a).hom.app X ≫ (τ.app X)⟦a⟧' ≫
      (F₂.commShiftIso a).inv.app X := by
  erw [comm_app_assoc, Iso.hom_inv_id_app, Category.comp_id]

end

instance of_iso_inv [NatTrans.CommShift e.hom A] :
  NatTrans.CommShift e.inv A := ⟨fun a => by
  ext X
  dsimp
  rw [← cancel_epi (e.hom.app (X⟦a⟧)), e.hom_inv_id_app_assoc, ← comm_app_assoc,
    ← Functor.map_comp, e.hom_inv_id_app, Functor.map_id]
  dsimp
  rw [Category.comp_id]⟩

lemma of_isIso [IsIso τ] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (inv τ) A := by
  haveI : NatTrans.CommShift (asIso τ).hom A := by
    dsimp
    infer_instance
  change NatTrans.CommShift (asIso τ).inv A
  infer_instance

variable (F₁)

instance id : NatTrans.CommShift (𝟙 F₁) A := ⟨by aesop_cat⟩

instance comp [NatTrans.CommShift τ A] [NatTrans.CommShift τ' A] :
    NatTrans.CommShift (τ ≫ τ') A := ⟨fun a => by
  ext X
  simp [comm_app_assoc, comm_app]⟩


-- TODO : whisker_left, whisker_right, of_map_faithful

end CommShift

end NatTrans

end CategoryTheory
