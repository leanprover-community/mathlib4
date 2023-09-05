import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

open CategoryTheory Category ZeroObject Limits

variable (C D E E' : Type*) [Category C] [Category D] [Category E] [Category E']
  (A : Type*) [AddMonoid A] [HasShift D A] [HasShift E A] [HasShift E' A]

namespace CategoryTheory

structure SingleFunctors where
  functor : A → C ⥤ D
  shiftIso (n a a' : A) (ha' : n + a = a') : functor a' ⋙ shiftFunctor D n ≅ functor a
  shiftIso_zero (a : A) :
    shiftIso 0 a a (zero_add a) = isoWhiskerLeft _ (shiftFunctorZero D A)
  shiftIso_add (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') :
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerLeft _ (shiftFunctorAdd D m n) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (shiftIso m a' a'' ha'') _ ≪≫ shiftIso n a a' ha'

variable {C D E A}
variable (F G H : SingleFunctors C D A)

namespace SingleFunctors

lemma shiftIso_add_hom_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
      (shiftFunctorAdd D m n).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫
        (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add_inv_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (F.shiftIso n a a' ha').inv.app X ≫
      ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd D m n).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

lemma shiftIso_add' (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerLeft _ (shiftFunctorAdd' D m n mn hnm) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (F.shiftIso m a' a'' ha'') _ ≪≫ F.shiftIso n a a' ha' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd, shiftIso_add]

lemma shiftIso_add'_hom_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
      (shiftFunctorAdd' D m n mn hnm).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫ (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

lemma shiftIso_add'_inv_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
        (F.shiftIso n a a' ha').inv.app X ≫
        ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd' D m n mn hnm).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[simp]
lemma shiftIso_zero_hom_app (a : A) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).hom.app X = (shiftFunctorZero D A).hom.app _ := by
  rw [shiftIso_zero]
  rfl

@[simp]
lemma shiftIso_zero_inv_app (a : A) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).inv.app X = (shiftFunctorZero D A).inv.app _ := by
  rw [shiftIso_zero]
  rfl

@[ext]
structure Hom where
  hom (a : A) : F.functor a ⟶ G.functor a
  comm (n a a' : A) (ha' : n + a = a') : (F.shiftIso n a a' ha').hom ≫ hom a =
    whiskerRight (hom a') (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom := by aesop_cat

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

@[simps]
def id : Hom F F where
  hom a := 𝟙 _

variable {F G H}

@[simps]
def comp (α : Hom F G) (β : Hom G H) : Hom F H where
  hom a := α.hom a ≫ β.hom a

end Hom

instance : Category (SingleFunctors C D A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
lemma id_hom (a : A) : Hom.hom (𝟙 F) a = 𝟙 _ := rfl

variable {F G H}

@[simp, reassoc]
lemma comp_hom (f : F ⟶ G) (g : G ⟶ H) (a : A) : (f ≫ g).hom a = f.hom a ≫ g.hom a := rfl

@[ext]
lemma hom_ext (f g : F ⟶ G) (h : f.hom = g.hom) : f = g := Hom.ext f g h

def isoMk (iso : ∀ a, (F.functor a ≅ G.functor a))
    (comm : ∀ (n a a' : A) (ha' : n + a = a'), (F.shiftIso n a a' ha').hom ≫ (iso a).hom =
      whiskerRight (iso a').hom (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom) : F ≅ G where
  hom :=
    { hom := fun a => (iso a).hom
      comm := comm }
  inv :=
    { hom := fun a => (iso a).inv
      comm := fun n a a' ha' => by
        dsimp only
        rw [← cancel_mono (iso a).hom, assoc, assoc, Iso.inv_hom_id, comp_id, comm,
          ← whiskerRight_comp_assoc, Iso.inv_hom_id, whiskerRight_id', id_comp] }

@[simps! functor shiftIso_hom_app shiftIso_inv_app]
def postComp (G : D ⥤ E) [G.CommShift A] :
    SingleFunctors C E A where
  functor a := F.functor a ⋙ G
  shiftIso n a a' ha' :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' ha') G
  shiftIso_zero a := by
    ext X
    dsimp
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_inv_app,
      SingleFunctors.shiftIso_zero_hom_app,id_comp, assoc, ← G.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Functor.id_obj, comp_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [F.shiftIso_add_hom_app n m a a' a'' ha' ha'', Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, id_comp, assoc,
      Functor.commShiftIso_inv_naturality_assoc]
    simp only [← G.map_comp, Iso.inv_hom_id_app_assoc]

@[simps!]
def postCompPostCompIso (G : D ⥤ E) (G' : E ⥤ E') [G.CommShift A] [G'.CommShift A] :
    (F.postComp G).postComp G' ≅ F.postComp (G ⋙ G') :=
  isoMk (fun a => Functor.associator _ _ _) (fun n a a' ha' => by
    ext X
    simp [Functor.commShiftIso_comp_inv_app])

end SingleFunctors

end CategoryTheory
