import Mathlib.CategoryTheory.Types
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Products
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
  ≅ (ULiftHom.equiv.{v₁, u₁, w}.functor : C ⥤ ULiftHom C) ⋙ yoneda := sorry

def uyonedaPairing_iso_conj_uLift_equiv
  : uyonedaPairing.{v₁, u₁, w} C
  ≅ (ULiftHom.equiv.op.prodCongr ULiftHom.equiv.op.congrLeft).functor
    ⋙ yonedaPairing (ULiftHom.{max v₁ w} C) := sorry

def uyonedaEvaluation_iso_conj_uLift_equiv
  : uyonedaEvaluation.{v₁, u₁, w} C
  ≅ (ULiftHom.equiv.op.prodCongr ULiftHom.equiv.op.congrLeft).functor
    ⋙ yonedaEvaluation (ULiftHom.{max v₁ w} C) := sorry

def uyonedaLemma : uyonedaPairing.{v₁, u₁, w} C ≅ uyonedaEvaluation.{v₁, u₁, w} C :=
  uyonedaPairing_iso_conj_uLift_equiv C
  ≪≫ isoWhiskerLeft _ (yonedaLemma (ULiftHom C))
  ≪≫ (uyonedaEvaluation_iso_conj_uLift_equiv C).symm

variable {C}

@[simps!]
def uyonedaSections (X : C) (F : Cᵒᵖ ⥤ Type (max v₁ w))
  : (uyoneda.{v₁, u₁, w}.obj X ⟶ F) ≅ ULift.{u₁} (F.obj (op X)) :=
  (uyonedaLemma.{v₁, u₁, w} C).app (op X, F)

def uyonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
  : (uyoneda.{v₁, u₁, w}.obj X ⟶ F) ≃ F.obj (op X) :=
  (uyonedaSections.{v₁, u₁, w} X F).toEquiv.trans Equiv.ulift

@[simp]
theorem uyonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
    (f : uyoneda.{v₁, u₁, w}.obj X ⟶ F) :
    uyonedaEquiv f = f.app (op X) ↿(𝟙 X) := sorry

@[simp]
theorem uyonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
    (x : F.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X)
    : (uyonedaEquiv.{v₁, u₁, w}.symm x).app Y ↿f = F.map f.op x := sorry

theorem uyonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type (max v₁ w)}
  (f : uyoneda.{v₁, u₁, w}.obj X ⟶ F) (g : Y ⟶ X)
  : F.map g.op (uyonedaEquiv f) = uyonedaEquiv.{v₁, u₁, w} (uyoneda.map g ≫ f) := by
  admit
  -- change (f.app (op X) ≫ F.map g.op) ↿(𝟙 X) = f.app (op Y) ↿(𝟙 Y ≫ g)
  -- rw [← f.naturality]
  -- dsimp
  -- simp

def uyonedaSectionsSmall {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type (max u₁ w)) :
    (uyoneda.{u₁, u₁, w}.obj X ⟶ F) ≅ F.obj (op X) :=
  uyonedaSections.{u₁, u₁, w} X F ≪≫ uliftSmaller.{u₁, w} (F.obj (op X))

@[simp]
theorem uyonedaSectionsSmall_hom {C : Type u₁} [SmallCategory C] (X : C) (F : Cᵒᵖ ⥤ Type (max u₁ w))
    (f : uyoneda.{u₁, u₁, w}.obj X ⟶ F)
    : (uyonedaSectionsSmall.{u₁, w} X F).hom f = f.app _ ↿(𝟙 _) := sorry

@[simp]
theorem uyonedaSectionsSmall_inv_app_apply {C : Type u₁} [SmallCategory C] (X : C)
    (F : Cᵒᵖ ⥤ Type (max u₁ w)) (t : F.obj (op X)) (Y : Cᵒᵖ) (f : Y.unop ⟶ X) :
    ((uyonedaSectionsSmall.{u₁, w} X F).inv t).app Y ↿f = F.map f.op t := sorry

attribute [local ext] Functor.ext

def curriedUYonedaLemma {C : Type u₁} [SmallCategory C] :
    (uyoneda.{u₁, u₁, w}.op ⋙ coyoneda.{max u₁ w, max (u₁ + 1) (w + 1)}
      : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type (max u₁ w)) ⥤ Type (max u₁ w))
    ≅ evaluation Cᵒᵖ (Type (max u₁ w)) := sorry

/-- The curried version of yoneda lemma when `C` is small. -/
def curriedUYonedaLemma' {C : Type u₁} [SmallCategory C] :
    @yoneda (Cᵒᵖ ⥤ Type (max u₁ w)) _
      ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type (max u₁ w))ᵒᵖ (Type (max u₁ w))).obj
           uyoneda.{u₁, u₁, w}.op
    ≅ 𝟭 (Cᵒᵖ ⥤ Type (max u₁ w))
    := by admit

end CategoryTheory
