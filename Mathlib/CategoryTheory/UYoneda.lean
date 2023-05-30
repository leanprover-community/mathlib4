import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Whiskering

import Mathlib.CategoryTheory.Yoneda
import Mathlib.Data.ULift

universe v₃ v₂ v₁ u₃ u₂ u₁ w

namespace CategoryTheory

open Opposite

-- precedence?
local notation:max "↿" x:max => ULift.up x
local notation:max "⇃" x:max => ULift.down x

variable {C : Type u₁} [Category.{v₁} C]

def uyoneda : C ⥤ Cᵒᵖ ⥤ Type (max v₁ w) :=
  yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{(max v₁ w), v₁}

def ucoyoneda : Cᵒᵖ ⥤ C ⥤ Type (max v₁ w) :=
  coyoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{(max v₁ w), v₁}

namespace UYoneda

@[simp]
theorem naturality {X Y : C} (α : uyoneda.{v₁, u₁, w}.obj X ⟶ uyoneda.{v₁, u₁, w}.obj Y)
    {Z Z' : C} (f : Z ⟶ Z') (h : Z' ⟶ X)
    : f ≫ ⇃ (α.app (op Z') ↿h) = ⇃(α.app (op Z) ↿(f ≫ h)) :=
  congr_arg ULift.down (FunctorToTypes.naturality _ _ α f.op ↿h).symm

noncomputable
instance uyonedaFull : Full (uyoneda.{v₁, u₁, w} : C ⥤ Cᵒᵖ ⥤ Type (max v₁ w)) :=
  Full.comp _ _

instance uyoneda_faithful : Faithful (uyoneda.{v₁, u₁, w} : C ⥤ Cᵒᵖ ⥤ Type (max v₁ w)) :=
  Faithful.comp _ _

end UYoneda

namespace UCoyoneda

@[simp]
theorem naturality {X Y : Cᵒᵖ} (α : ucoyoneda.{v₁, u₁, w}.obj X ⟶ ucoyoneda.{v₁, u₁, w}.obj Y)
    {Z Z' : C} (f : Z' ⟶ Z)
    (h : unop X ⟶ Z') : ⇃(α.app Z' ↿h) ≫ f = ⇃(α.app Z ↿(h ≫ f)) :=
  congr_arg ULift.down (FunctorToTypes.naturality _ _ α f ↿h).symm

noncomputable
instance ucoyonedaFull : Full (ucoyoneda.{v₁, u₁, w} : Cᵒᵖ ⥤ C ⥤ Type _) :=
  Full.comp _ _

instance ucoyoneda_faithful : Faithful (ucoyoneda.{v₁, u₁, w} : Cᵒᵖ ⥤ C ⥤ Type _) :=
  Faithful.comp _ _

/-- The ULift functor `Type v₁ → Type (max v₁ w)` is isomorphic to the coyoneda functor coming from `punit`. -/
def punitIso : ucoyoneda.{v₁, v₁+1, w}.obj (Opposite.op (PUnit : Type v₁)) ≅ uliftFunctor.{w, v₁} :=
  NatIso.ofComponents
    (fun X =>
      { hom := fun f => ULift.up.{w, v₁} (⇃f ⟨⟩)
        inv := fun x => ↿(fun _ => ⇃x) })
    (by aesop_cat)

/-- Taking the `unop` of morphisms is a natural isomorphism. -/
@[simps!]
def objOpOp (X : C) : ucoyoneda.{v₁, u₁, w}.obj (op (op X))
                    ≅ uyoneda.{v₁, u₁, w}.obj X :=
  isoWhiskerRight (Coyoneda.objOpOp X) _

end UCoyoneda

namespace Functor

class URepresentable (F : Cᵒᵖ ⥤ Type (max v₁ w)) : Prop where
  has_representation : ∃ (X : _) (f : uyoneda.{v₁, u₁, w}.obj X ⟶ F), IsIso f

instance {X : C} : URepresentable.{v₁, u₁, w} (uyoneda.{v₁, u₁, w}.obj X) where
  has_representation := ⟨X, 𝟙 _, inferInstance⟩

class UCorepresentable (F : C ⥤ Type (max v₁ w)) : Prop where
  has_corepresentation : ∃ (X : _) (f : ucoyoneda.{v₁, u₁, w}.obj X ⟶ F), IsIso f

instance {X : Cᵒᵖ} : UCorepresentable.{v₁, u₁, w} (ucoyoneda.{v₁, u₁, w}.obj X) where
  has_corepresentation := ⟨X, 𝟙 _, inferInstance⟩

section URepresentable

variable (F : Cᵒᵖ ⥤ Type (max v₁ w))

variable [URepresentable.{v₁, u₁, w} F]

noncomputable def ureprX : C :=
  (URepresentable.has_representation : ∃ (_ : _) (_ : _ ⟶ F), _).choose
set_option linter.uppercaseLean3 false

noncomputable def ureprF : uyoneda.{v₁, u₁, w}.obj (Functor.ureprX F) ⟶ F :=
  URepresentable.has_representation.choose_spec.choose

noncomputable def ureprx : F.obj (op F.ureprX) :=
  F.ureprF.app (op F.ureprX) ↿(𝟙 F.ureprX)

instance : IsIso F.ureprF :=
  URepresentable.has_representation.choose_spec.choose_spec

noncomputable def ureprW : uyoneda.{v₁, u₁, w}.obj (Functor.ureprX F) ≅ F :=
  asIso F.ureprF

@[simp]
theorem ureprW_hom : F.ureprW.hom = F.ureprF :=
  rfl

theorem ureprW_app_hom (X : Cᵒᵖ) (f : unop X ⟶ F.ureprX) :
    (F.ureprW.app X).hom ↿f = F.map f.op F.ureprx := by
  change F.ureprF.app X ↿f = (F.ureprF.app (op F.ureprX) ≫ F.map f.op) ↿(𝟙 F.ureprX)
  rw [← F.ureprF.naturality]
  dsimp [uyoneda, whiskerRight]
  simp

end URepresentable

section UCorepresentable

variable (F : C ⥤ Type (max v₁ w))

variable [Functor.UCorepresentable.{v₁, u₁, w} F]

noncomputable def ucoreprX : C :=
  (UCorepresentable.has_corepresentation : ∃ (_ : _)(_ : _ ⟶ F), _).choose.unop
set_option linter.uppercaseLean3 false

noncomputable def ucoreprF : ucoyoneda.{v₁, u₁, w}.obj (op F.ucoreprX) ⟶ F :=
  UCorepresentable.has_corepresentation.choose_spec.choose

noncomputable def ucoreprx : F.obj F.ucoreprX :=
  F.ucoreprF.app F.ucoreprX ↿(𝟙 F.ucoreprX)

instance : IsIso F.ucoreprF :=
  UCorepresentable.has_corepresentation.choose_spec.choose_spec

noncomputable def ucoreprW : ucoyoneda.{v₁, u₁, w}.obj (op F.ucoreprX) ≅ F :=
  asIso F.ucoreprF

theorem ucoreprW_app_hom (X : C) (f : F.ucoreprX ⟶ X) :
    (F.ucoreprW.app X).hom ↿f = F.map f F.ucoreprx := by
  change F.ucoreprF.app X ↿f = (F.ucoreprF.app F.ucoreprX ≫ F.map f) ↿(𝟙 F.ucoreprX)
  rw [← F.ucoreprF.naturality]
  dsimp [ucoyoneda, whiskerRight]
  simp

end UCorepresentable

end Functor

theorem urepresentable_of_nat_iso (F : Cᵒᵖ ⥤ Type (max v₁ w)) {G} (i : F ≅ G)
  [Functor.URepresentable.{v₁, u₁, w} F] : Functor.URepresentable.{v₁, u₁, w} G :=
  { has_representation := ⟨F.ureprX, F.ureprF ≫ i.hom, inferInstance⟩ }

theorem ucorepresentable_of_nat_iso (F : C ⥤ Type (max v₁ w)) {G} (i : F ≅ G)
  [Functor.UCorepresentable.{v₁, u₁, w} F] : Functor.UCorepresentable.{v₁, u₁, w} G :=
  { has_corepresentation := ⟨op F.ucoreprX, F.ucoreprF ≫ i.hom, inferInstance⟩ }

instance : Functor.UCorepresentable.{v₁, v₁+1, w} (uliftFunctor.{max v₁ w, v₁}) :=
  ucorepresentable_of_nat_iso (ucoyoneda.{v₁, v₁+1, w}.obj (op PUnit)) UCoyoneda.punitIso

open Opposite

variable (C)

open Yoneda

def uyonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type (max v₁ w)) ⥤ Type (max u₁ v₁ w) :=
  evaluationUncurried Cᵒᵖ (Type (max v₁ w)) ⋙ uliftFunctor.{u₁}

example : yonedaEvaluation.{v₁, u₁} = uyonedaEvaluation.{v₁, u₁, v₁} := rfl

@[simp]
theorem uyonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type (max v₁ w))) (α : P ⟶ Q)
    (x : (uyonedaEvaluation.{v₁, u₁, w} C).obj P) :
    ((uyonedaEvaluation.{v₁, u₁, w} C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

def uyonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type (max v₁ w)) ⥤ Type max u₁ v₁ w :=
  Functor.prod uyoneda.{v₁, u₁, w}.op (𝟭 (Cᵒᵖ ⥤ Type (max v₁ w)))
  ⋙ Functor.hom (Cᵒᵖ ⥤ Type (max v₁ w))

@[simp]
theorem uyonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type (max v₁ w))) (α : P ⟶ Q)
  (β : (uyonedaPairing.{v₁, u₁, w} C).obj P)
  : (uyonedaPairing.{v₁, u₁, w} C).map α β = uyoneda.{v₁, u₁, w}.map α.1.unop ≫ β ≫ α.2 :=
  rfl

def uyoneda_ULiftHom_equiv_iso_ULiftHom_equiv_yoneda
    : uyoneda.{v₁, u₁, w} ⋙ ULiftHom.equiv.op.congrLeft.functor
    ≅ (ULiftHom.equiv.{v₁, u₁, w}.functor : C ⥤ ULiftHom C) ⋙ yoneda := {
  hom := {
    app := fun X => {
      app := fun Y f => ↿⇃f
    }
  }
  inv := {
    app := fun X => {
      app := fun Y f => ↿⇃f
    }
  }
}

def prodFunctorToProdFunctorProd
    (A : Type u₁) [inst : Category.{v₁} A]
    (B : Type u₂) [inst : Category.{v₂} B]
    (P : Type u₃) [inst : Category.{v₃} P]
    (Q : Type u₄) [inst : Category.{v₄} Q]
    : (A ⥤ P) × (B ⥤ Q) ⥤ (A × B) ⥤ (P × Q) where
  obj := fun X => X.1.prod X.2
  map := fun {F G} η => NatTrans.prod η.1 η.2

def prodComp
    {A : Type u₁} [inst : Category.{v₁} A] {P : Type u₄} [inst : Category.{v₄} P]
    {B : Type u₂} [inst : Category.{v₂} B] {Q : Type u₅} [inst : Category.{v₅} Q]
    {C : Type u₃} [inst : Category.{v₃} C] {R : Type u₆} [inst : Category.{v₆} R]
    (F : A ⥤ B) (G : B ⥤ C) (H : P ⥤ Q) (K : Q ⥤ R)
    : F.prod H ⋙ G.prod K ≅ (F ⋙ G).prod (H ⋙ K) where
  hom := {
    app := fun X => (𝟙 (G.obj (F.obj X.1)), 𝟙 (K.obj (H.obj X.2)))
  }
  inv := {
    app := fun X => (𝟙 (G.obj (F.obj X.1)), 𝟙 (K.obj (H.obj X.2)))
  }

def precomp_equiv_comp_hom_iso_hom
    {A : Type u₁} [inst : Category.{v₁} A] {B : Type u₂} [inst : Category.{v₁} B]
    (e : A ≌ B) : Functor.hom B ≅ e.inverse.op.prod e.inverse ⋙ Functor.hom A where
  hom := { app := fun p => e.inverse.map }
  inv := { app := fun p f => e.counitInv.app p.1.unop ≫ e.functor.map f ≫ e.counit.app p.2,
           naturality := by
            rintro ⟨⟨X⟩, X'⟩ ⟨⟨Y⟩, Y'⟩ ⟨f, g⟩
            ext h
            simp [Functor.prod, Functor.hom] }
  hom_inv_id := by
    ext p f
    rcases p with ⟨⟨X⟩, X'⟩
    simp
  inv_hom_id := by
    ext p f
    rcases p with ⟨⟨X⟩, X'⟩
    simp
    rw [← Category.assoc]
    refine' Eq.trans (congr_arg₂ _ _ rfl) (Category.id_comp f)
    exact e.symm.functor_unitIso_comp X

def uyonedaPairing_iso_conj_uLift_equiv.{v, u, w'}
    (C : Type u) [Category C]
    : uyonedaPairing.{v, u, w'} C
    ≅ (ULiftHom.equiv.op.prodCongr ULiftHom.equiv.op.congrLeft).functor
      ⋙ yonedaPairing (ULiftHom.{w'} C) :=
  let e1 : (Cᵒᵖ ⥤ Type (max v w')) ≌ ((ULiftHom C)ᵒᵖ ⥤ Type (max v w'))
         := ULiftHom.equiv.{v, u, w'}.op.congrLeft
  let ϕ := prodFunctorToProdFunctorProd
             Cᵒᵖ (Cᵒᵖ ⥤ Type (max v w'))
             (Cᵒᵖ ⥤ Type (max v w'))ᵒᵖ (Cᵒᵖ ⥤ Type (max v w'))
  let i1 := Functor.associator uyoneda.{v, u, w'} e1.functor e1.inverse
            ≪≫ NatIso.hcomp (Iso.refl uyoneda.{v, u, w'}) e1.unitIso.symm
            ≪≫ uyoneda.{v, u, w'}.rightUnitor
  let i2 : (uyoneda ⋙ e1.functor) ⋙ e1.inverse
         ≅ (ULiftHom.equiv.functor ⋙ yoneda) ⋙ e1.inverse
         := isoWhiskerRight (uyoneda_ULiftHom_equiv_iso_ULiftHom_equiv_yoneda.{v, u, w'} C)
                            (ULiftHom.equiv.op.congrLeft).inverse
  let i3 := (Functor.opHom _ _).mapIso (i2.symm ≪≫ i1).op
  let i4 := prodComp (Functor.op (@ULiftHom.equiv.{v, u, w'} C _).functor)
                         (Functor.op (@yoneda (ULiftHom.{w'} C) _))
                         ((whiskeringLeft (ULiftHom.{w'} C)ᵒᵖ Cᵒᵖ (Type (max v w'))).obj
                           (Functor.op ULiftHom.equiv.{v, u, w'}.inverse))
                         (𝟭 ((ULiftHom.{w'} C)ᵒᵖ ⥤ Type (max v w')))
  isoWhiskerRight (ϕ.mapIso (Iso.prod i3 e1.unitIso)) _
  ≪≫ isoWhiskerRight (prodComp (Functor.op ULiftHom.equiv.{v, u, w'}.functor ⋙ Functor.op yoneda)
                               (Functor.op e1.inverse) e1.functor e1.inverse).symm _
  ≪≫ Functor.associator _ _ _
  ≪≫ isoWhiskerLeft _ (precomp_equiv_comp_hom_iso_hom e1).symm
  ≪≫ isoWhiskerRight (Functor.mapIso (prodFunctorToProdFunctorProd
                                         Cᵒᵖ (Cᵒᵖ ⥤ Type (max v w'))
                                         ((ULiftHom C)ᵒᵖ ⥤ Type (max v w'))ᵒᵖ
                                         ((ULiftHom C)ᵒᵖ ⥤ Type (max v w')))
                                             (Iso.prod (Iso.refl _) (Functor.rightUnitor _).symm)
                      ≪≫ i4.symm) _
  ≪≫ Functor.associator _ _ _

lemma uyonedaPairing_iso_conj_uLift_equiv_hom_app
    (F) (X : C) (η)
    : (uyonedaPairing_iso_conj_uLift_equiv.{v₁, u₁, w} C).hom.app (op X, F) η
      = { app := fun y f => F.map (op ⇃f) (η.app (op X) ↿(𝟙 X))
          naturality := fun A B ⟨f⟩ => funext (fun g =>
            show F.map (f ≫ g).down.op (η.app (op X) ↿(𝟙 X))
                = F.map f.down.op (F.map g.down.op (η.app (op X) ↿(𝟙 X)))
            from Eq.trans (congr_arg₂ _ (Eq.trans (congr_arg op (ULiftHom.down.map_comp f g))
                                                  (@op_comp _ _ _ _ _ f.down g.down)) rfl)
                          (FunctorToTypes.map_comp_apply _ _ _ _)) } := by
  apply NatTrans.ext
  ext x f
  obtain ⟨x⟩ := x
  dsimp [Equivalence.prodCongr, ULiftHom.equiv] at f
  simp only [Equivalence.op, ULiftHom.equiv, Functor.id_obj, Functor.comp_obj, ULiftHom.up_obj, ULiftHom.down_obj,
    objDown_objUp, eqToIso_refl, objUp_objDown, Equivalence.congrLeft, Equivalence.mk, Equivalence.adjointifyη,
    Iso.instTransIso_trans, Functor.prod_obj, Functor.op_obj, unop_op, uyonedaPairing_iso_conj_uLift_equiv,
    prodFunctorToProdFunctorProd, prod_Hom, Functor.opHom_obj, Iso.trans_assoc, Iso.trans_symm, Iso.symm_symm_eq,
    prodComp, whiskeringLeft_obj_obj, Iso.symm_mk, precomp_equiv_comp_hom_iso_hom, Functor.hom_obj,
    Equivalence.Equivalence_mk'_counitInv, NatIso.ofComponents_inv_app, whiskeringLeft_obj_map, Equivalence.counit,
    NatIso.ofComponents_hom_app, Functor.op_map, Quiver.Hom.unop_op, Iso.trans_hom, isoWhiskerRight_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom, Iso.symm_hom, isoWhiskerRight_inv, NatIso.hcomp_hom, Iso.refl_hom,
    Iso.symm_inv, isoWhiskerLeft_inv, op_comp, Category.assoc, Functor.map_comp, isoWhiskerLeft_hom, whiskerRight_comp,
    FunctorToTypes.comp, whiskerRight_app, NatTrans.prod_app, NatTrans.comp_app, Functor.opHom_map_app,
    Functor.rightUnitor_hom_app, op_id, NatTrans.hcomp_app, Functor.leftUnitor_inv_app, Functor.comp_map,
    whiskerLeft_twice, Functor.associator_hom_app, whiskerLeft_app, Functor.associator_inv_app,
    Functor.leftUnitor_hom_app, Category.id_comp, NatTrans.id_app, Functor.id_map, Category.comp_id, Functor.hom_map,
    unop_comp, unop_id, types_id_apply, whiskerLeft_comp, Functor.rightUnitor_inv_app,
    Equivalence.invFunIdAssoc_inv_app, NatIso.op_hom, NatTrans.op_app, yoneda_obj_map, unop_id_op,
    Equivalence.funInvIdAssoc_inv_app, Equivalence.Equivalence_mk'_unit, NatIso.op_inv, Iso.refl_inv,
    FunctorToTypes.map_id_apply, Equivalence.invFunIdAssoc_hom_app, Equivalence.funInvIdAssoc_hom_app,
    Equivalence.Equivalence_mk'_unitInv, yoneda_obj_obj]
  dsimp [uyoneda_ULiftHom_equiv_iso_ULiftHom_equiv_yoneda]
  refine' Eq.trans (Eq.trans _ (congr_fun (η.naturality _) _)) (types_comp_apply _ _ _)
  exact congr_arg _ (congr_arg _ (Eq.trans (Category.comp_id f.down) (unop_op _)).symm)

lemma uyonedaPairing_iso_conj_uLift_equiv_inv_app
    (F) (X : C) (η)
    : (uyonedaPairing_iso_conj_uLift_equiv.{v₁, u₁, w} C).inv.app (op X, F) η
      = { app := fun Y f => F.map (op ⇃f) (η.app (op X) ↿(𝟙 X))
          naturality := fun A B ⟨f⟩ => funext (fun g =>
                show F.map (f ≫ g.down).op (η.app (op X) ↿(𝟙 X))
                     = F.map ⟨f⟩ (F.map g.down.op (η.app (op X) ↿(𝟙 X)))
                from Eq.trans (congr_arg₂ _ (@op_comp _ _ _ _ _ f g.down) rfl)
                              (FunctorToTypes.map_comp_apply _ _ _ _) ) } := by
  apply NatTrans.ext
  ext x f
  obtain ⟨x⟩ := x
  obtain ⟨f⟩ := f
  simp only [Functor.prod_obj, Functor.op_obj, unop_op, Functor.id_obj, Equivalence.op, ULiftHom.equiv,
    Functor.comp_obj, ULiftHom.up_obj, ULiftHom.down_obj, objDown_objUp, eqToIso_refl, objUp_objDown,
    Equivalence.congrLeft, Equivalence.mk, Equivalence.adjointifyη, Iso.instTransIso_trans,
    uyonedaPairing_iso_conj_uLift_equiv, prodFunctorToProdFunctorProd, prod_Hom, Functor.opHom_obj, Iso.trans_assoc,
    Iso.trans_symm, Iso.symm_symm_eq, prodComp, whiskeringLeft_obj_obj, Iso.symm_mk, precomp_equiv_comp_hom_iso_hom,
    Functor.hom_obj, Equivalence.Equivalence_mk'_counitInv, NatIso.ofComponents_inv_app, whiskeringLeft_obj_map,
    Equivalence.counit, NatIso.ofComponents_hom_app, Functor.op_map, Quiver.Hom.unop_op, Iso.trans_inv,
    isoWhiskerRight_inv, Functor.mapIso_inv, Iso.prod_inv, Iso.refl_inv, Iso.symm_inv, whiskerRight_comp,
    isoWhiskerLeft_inv, Category.assoc, Iso.op_inv, NatIso.hcomp_inv, isoWhiskerLeft_hom, Iso.symm_hom,
    isoWhiskerRight_hom, op_comp, Functor.map_comp, FunctorToTypes.comp, Functor.associator_inv_app, types_id_apply,
    whiskerRight_app, Functor.hom_map, unop_id, Category.comp_id, Category.id_comp, NatTrans.prod_app, NatTrans.id_app,
    Functor.rightUnitor_hom_app, whiskerLeft_app, NatTrans.comp_app, Functor.opHom_map_app, op_id, NatTrans.hcomp_app,
    Functor.leftUnitor_inv_app, Functor.associator_hom_app, Functor.comp_map, whiskerLeft_twice,
    Functor.leftUnitor_hom_app, whiskerLeft_id', Functor.rightUnitor_inv_app, unop_comp,
    Equivalence.funInvIdAssoc_inv_app, Equivalence.Equivalence_mk'_unit, NatIso.op_inv, NatTrans.op_app,
    Equivalence.invFunIdAssoc_inv_app, NatIso.op_hom, Iso.refl_hom, FunctorToTypes.map_id_apply,
    Equivalence.funInvIdAssoc_hom_app, Equivalence.Equivalence_mk'_unitInv, Equivalence.invFunIdAssoc_hom_app]
  refine' Eq.trans _ ((congr_fun (η.naturality (ULiftHom.up.map f).op) _).trans
                        (types_comp_apply _ _ _))
  refine' congr_arg (η.app (op x)) _
  refine' ((ULiftHom.up.map_comp (𝟙 x) f).trans
          $ (congr_arg₂ _ (ULiftHom.up.map_id x) rfl).trans
          $ (Category.id_comp _).trans
          $ (Category.comp_id _).symm.trans
          $ congr_arg₂ _ rfl (ULiftHom.up.map_id X).symm)

def evaluationUncurriedTransport {C : Type u₁} [Category.{v₁} C]
    {C' : Type u₂} [Category.{v₂} C'] {D : Type u₃} [Category.{v₃} D] (e : C ≌ C')
    : evaluationUncurried C D
    ≅ Functor.prod e.functor ((whiskeringLeft C' C D).obj e.inverse)
      ⋙ evaluationUncurried C' D where
  hom := { app := fun p => p.snd.map (e.unit.app p.fst)
           naturality := by
            rintro ⟨X, F⟩ ⟨Y, G⟩ ⟨ϕ, η⟩
            dsimp [evaluationUncurried]
            rw [← Category.assoc, η.naturality]
            simp only [Category.assoc, Equivalence.inv_fun_map,
                       Functor.comp_obj, Functor.id_obj, Functor.map_comp,
                       NatTrans.naturality, NatTrans.naturality_assoc]
            rw [← G.map_comp, ← G.map_comp, ← G.map_comp, Equivalence.unit,
                ← Category.assoc, ← Category.assoc, Equivalence.unitInv,
                ← NatTrans.comp_app, Iso.hom_inv_id]
            congr
            exact Eq.symm (Category.id_comp ϕ) }
  inv := { app := fun p => p.snd.map (e.unitInv.app p.fst)
           naturality := by
            rintro ⟨X, F⟩ ⟨Y, G⟩ ⟨ϕ, η⟩
            dsimp [evaluationUncurried]
            rw [← Category.assoc, η.naturality]
            simp only [Equivalence.inv_fun_map, Functor.comp_obj,
                       Functor.id_obj, Functor.map_comp, Category.assoc,
                       NatTrans.naturality, NatTrans.naturality_assoc]
            rw [← G.map_comp, ← G.map_comp,
                Equivalence.unit, Equivalence.unitInv,
                ← NatTrans.comp_app, e.unitIso.hom_inv_id]
            congr
            exact Category.comp_id ϕ }
  hom_inv_id := by
    ext p
    obtain ⟨X, F⟩ := p
    dsimp [Equivalence.unit, Equivalence.unitInv]
    rw [← F.map_comp, ← NatTrans.comp_app, Iso.hom_inv_id, NatTrans.id_app]
    exact F.map_id _
  inv_hom_id := by
    ext p
    obtain ⟨X, F⟩ := p
    dsimp [Equivalence.unit, Equivalence.unitInv]
    rw [← F.map_comp, ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
    exact F.map_id _

def uyonedaEvaluation_iso_conj_uLift_equiv
    : uyonedaEvaluation.{v₁, u₁, w} C
    ≅ (ULiftHom.equiv.op.prodCongr ULiftHom.equiv.op.congrLeft).functor
      ⋙ yonedaEvaluation (ULiftHom.{w} C) := by
  dsimp [yonedaEvaluation, uyonedaEvaluation]
  refine' isoWhiskerRight _ _ ≪≫ Functor.associator _ _ _
  apply evaluationUncurriedTransport

def uyonedaLemma.{u, v, w'} (D : Type u) [Category.{v} D]
    : uyonedaPairing.{v, u, w'} D ≅ uyonedaEvaluation.{v, u, w'} D :=
  uyonedaPairing_iso_conj_uLift_equiv D
  ≪≫ isoWhiskerLeft _ (yonedaLemma (ULiftHom D))
  ≪≫ (uyonedaEvaluation_iso_conj_uLift_equiv D).symm

variable {C}

@[simps!]
def uyonedaSections (X : C) (F : Cᵒᵖ ⥤ Type (max v₁ w))
    : (uyoneda.{v₁, u₁, w}.obj X ⟶ F) ≅ ULift.{u₁} (F.obj (op X)) :=
  (uyonedaLemma.{u₁, v₁, w} C).app (op X, F)

lemma uyonedaLemmaApp (X : C) (F : Cᵒᵖ ⥤ Type (max v₁ w)) (η)
    : (uyonedaSections.{v₁, u₁, w} X F).hom η = ULift.up (η.app (op X) (↿ (𝟙 X))) := by
  dsimp [uyonedaSections]
  rw [← NatIso.app_hom]
  delta uyonedaLemma
  rw [NatIso.trans_app, NatIso.trans_app]
  dsimp [Iso.symm]
  rw [uyonedaPairing_iso_conj_uLift_equiv_hom_app]
  refine' @Eq.trans _ _ ((uyonedaEvaluation_iso_conj_uLift_equiv.{v₁, u₁, w} C).inv.app (op X, F)
                        $ ULift.up (η.app (op X) _)) _
                        (congr_arg _
                         $ congr_arg _
                         $ (congr_fun (F.map_id _) _).trans (types_id_apply _ _))
                        _
  simp [uyonedaEvaluation_iso_conj_uLift_equiv, evaluationUncurriedTransport,
        Equivalence.op, ULiftHom.equiv]

lemma uyonedaLemmaInvApp (X : C) (F : Cᵒᵖ ⥤ Type (max v₁ w)) (s)
    : (uyonedaSections.{v₁, u₁, w} X F).inv s
    = { app := fun Y f => F.map f.down.op s.down
        naturality := fun ⟨A⟩ ⟨B⟩ ⟨f⟩ => funext $ fun ⟨g⟩ => FunctorToTypes.map_comp_apply F _ _ _ } := by
  dsimp [uyonedaSections]
  delta uyonedaLemma
  rw [← NatIso.app_inv, NatIso.trans_app, NatIso.trans_app]
  dsimp [Iso.symm, uyonedaEvaluation_iso_conj_uLift_equiv, ULiftHom.equiv,
         evaluationUncurriedTransport, Equivalence.unit, Equivalence.op,
         Equivalence.prodCongr, ULiftHom.objUp]
  refine' Eq.trans (uyonedaPairing_iso_conj_uLift_equiv_inv_app.{v₁, u₁, w} C F X _) _
  ext Y g
  simp only [Functor.prod_obj, Functor.op_obj, unop_op, Functor.id_obj,
             FunctorToTypes.map_id_apply]
  refine' congr_arg _ _

  have h := @yonedaEquiv_symm_app_apply (ULiftHom.{w} C) _ X
                                        (Functor.op ULiftHom.down ⋙ F)
  dsimp [yonedaEquiv, yonedaSections, Equiv.ulift] at h
  exact (congr_fun
          (congr_fun
            (congr_arg NatTrans.app
            $ congr_arg _ $ congr_arg _
            $ (congr_fun (F.map_id (op X)) _).symm) _) _).trans
        $ (h (F.map (𝟙 (op X)) s.down) (op X) ↿(𝟙 X)).trans
        $ (congr_fun (F.map_id (op X)) _).trans
        $ congr_fun (F.map_id (op X)) _

def uyonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
  : (uyoneda.{v₁, u₁, w}.obj X ⟶ F) ≃ F.obj (op X) :=
  (uyonedaSections.{v₁, u₁, w} X F).toEquiv.trans Equiv.ulift

lemma Equivalence.mk_functor {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D) (G : D ⥤ C) (α β h)
  : (CategoryTheory.Equivalence.mk' F G α β h).functor = F :=
  rfl

lemma NatTrans.id_def {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  : 𝟙 F = NatTrans.mk (fun X => 𝟙 (F.obj X)) := rfl

lemma NatIso.trans_symm {D : Type u₂} [Category.{v₂} D] {F G H : C ⥤ D}
  (α : F ≅ G) (β : G ≅ H) : (α ≪≫ β).symm = β.symm ≪≫ α.symm := rfl

@[simp]
theorem uyonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
    (f : uyoneda.{v₁, u₁, w}.obj X ⟶ F) :
    uyonedaEquiv f = f.app (op X) ↿(𝟙 X) :=
  show ULift.down ((uyonedaSections X F).hom f) = f.app (op X) ↿(𝟙 X)
  from by rw [uyonedaLemmaApp]

@[simp]
theorem uyonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
    (x : F.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X)
    : (uyonedaEquiv.{v₁, u₁, w}.symm x).app Y ↿f = F.map f.op x := by
  delta uyonedaEquiv
  rw [Equiv.symm_trans_apply, Iso.toEquiv]
  dsimp
  rw [uyonedaLemmaInvApp]
  simp only [op_unop]
  exact rfl

theorem uyonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
  (f : uyoneda.{v₁, u₁, w}.obj X ⟶ F) (g : Y ⟶ X)
    : F.map g.op (uyonedaEquiv f) = uyonedaEquiv.{v₁, u₁, w} (uyoneda.map g ≫ f) := by
  rw [uyonedaEquiv_apply, uyonedaEquiv_apply]
  simp [uyoneda]
  refine' Eq.trans (types_comp_apply _ _ _).symm _
  rw [← NatTrans.naturality]
  simp

def uyonedaSectionsSmall {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type (max u₁ w)) :
    (uyoneda.{u₁, u₁, w}.obj X ⟶ F) ≅ F.obj (op X) :=
  uyonedaSections.{u₁, u₁, w} X F ≪≫ uliftSmaller.{w, u₁} (F.obj (op X))

@[simp]
theorem uyonedaSectionsSmall_hom {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type (max u₁ w))
    (f : uyoneda.{u₁, u₁, w}.obj X ⟶ F)
    : (uyonedaSectionsSmall.{u₁, w} X F).hom f = f.app _ ↿(𝟙 _) := by
  dsimp only [uyonedaSectionsSmall, uliftSmaller, Iso.trans, types_comp_apply]
  rw [uyonedaLemmaApp]
  exact rfl

@[simp]
theorem uyonedaSectionsSmall_inv_app_apply {C : Type u₁} [SmallCategory C] (X : C)
    (F : Cᵒᵖ ⥤ Type (max u₁ w)) (t : F.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    ((uyonedaSectionsSmall.{u₁, w} X F).inv t).app Y ↿f = F.map f.op t := by
  dsimp only [uyonedaSectionsSmall, uliftSmaller, Iso.trans, types_comp_apply]
  rw [uyonedaLemmaInvApp]

attribute [local ext] Functor.ext

def curriedUYonedaLemma {C : Type u₁} [SmallCategory C] :
    (uyoneda.{u₁, u₁, w}.op ⋙ coyoneda.{max u₁ w, max (u₁ + 1) (w + 1)}
      : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max u₁ w)) ⥤ Type (max u₁ w))
    ≅ evaluation Cᵒᵖ (Type (max u₁ w)) := by
  refine' eqToIso _ ≪≫ curry.mapIso (uyonedaLemma.{u₁, u₁, w} C ≪≫ isoWhiskerLeft (evaluationUncurried Cᵒᵖ (Type (max u₁ w))) uliftFunctorSmaller.{w, u₁}) ≪≫ eqToIso _
  . apply Functor.ext
    . intro X Y f
      simp only [curry, uyoneda, ucoyoneda, curryObj, uyonedaPairing]
      dsimp
      apply NatTrans.ext
      dsimp at *
      funext F g
      apply NatTrans.ext
      simp
    . intro X
      simp only [curry, uyoneda, ucoyoneda, curryObj, uyonedaPairing]
      aesop_cat
  . apply Functor.ext
    . intro X Y f
      simp only [curry, uyoneda, ucoyoneda, curryObj, uyonedaPairing]
      dsimp
      apply NatTrans.ext
      dsimp at *
      funext F g
      simp
    . intro X
      simp only [curry, uyoneda, ucoyoneda, curryObj, uyonedaPairing]
      aesop_cat

def curriedUYonedaLemma' {C : Type u₁} [SmallCategory C] :
    @yoneda (Cᵒᵖ ⥤ Type (max u₁ w)) _
      ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type (max u₁ w))ᵒᵖ (Type (max u₁ w))).obj
           uyoneda.{u₁, u₁, w}.op
    ≅ 𝟭 (Cᵒᵖ ⥤ Type (max u₁ w)) := by
  refine eqToIso ?_ ≪≫ curry.mapIso (isoWhiskerLeft (Prod.swap _ _) (uyonedaLemma.{u₁, u₁, w} C ≪≫ isoWhiskerLeft (evaluationUncurried Cᵒᵖ (Type (max u₁ w))) uliftFunctorSmaller.{w, u₁} : _)) ≪≫ eqToIso ?_
  · apply Functor.ext
    · intro X Y f
      simp only [curry, uyoneda, ucoyoneda, curryObj, uyonedaPairing]
      aesop_cat
  · apply Functor.ext
    · intro X Y f
      aesop_cat

end CategoryTheory
