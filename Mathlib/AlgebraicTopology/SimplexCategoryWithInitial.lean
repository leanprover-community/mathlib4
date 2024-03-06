/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.Products.Associator
import Mathlib.CategoryTheory.WithTerminal
import Mathlib.CategoryTheory.Whiskering
import Mathlib.AlgebraicTopology.SimplexCategory

/-! # The simplex category with initial

Sometimes called the augmented simplex category.

## Remarks

- We define basic functions mirroring those of `SimplexCategory`.
- We define the join functor from `WithInitial SimplexCategory × WithInitial SimplexCategory`
  to `WithInitial SimplexCategory`.
- We define the notion of a split of an object and morphism in `WithInitial SimplexCategory`. This
  is important in defining the join of functors `(WithInitial SimplexCategory)ᵒᵖ ⥤ Type u`.

-/

universe v

open CategoryTheory CategoryTheory.Limits

section lifts
namespace CategoryTheory
variable {C : Type} [Category.{v} C]

@[simps!]
def Functor.objLift  (F : C ⥤ Type) {c : C} (i : F.obj c) : F.Elements := ⟨c, i⟩

@[simps!]
def Functor.ObjEqIso (F : C ⥤ Type) {c : C} {i j : F.obj c} (h : i = j) :
    F.objLift i ≅ F.objLift j where
  hom := ⟨𝟙 c, by
    simp
    subst h
    rfl
    ⟩
  inv := ⟨𝟙 c, by
    simp
    subst h
    rfl⟩

lemma Functor.ObjEqIso_refl (F : C ⥤ Type) {c : C} {i : F.obj c}
    (h : i = i) : F.ObjEqIso h = Iso.refl (F.objLift i) := by
  rfl

lemma Functor.ObjEqIso_symm (F : C ⥤ Type) {c : C} {i j : F.obj c} (h : i = j) :
    F.ObjEqIso h ≪≫ F.ObjEqIso h.symm  = Iso.refl (F.objLift i) := by
  subst h
  rw [F.ObjEqIso_refl]
  simp

lemma Functor.ObjEqIso_trans (F : C ⥤ Type) {c : C} {i j k : F.obj c} (h1 : i = j) (h2 : j = k) :
    F.ObjEqIso h1 ≪≫ F.ObjEqIso h2  = F.ObjEqIso (h1.trans h2) := by
  subst h1 h2
  rw [ObjEqIso_refl]
  simp

@[simps!]
def Functor.coCartesianLift (F : C ⥤ Type) {c1 c2 : C} (f : c1 ⟶ c2) (i : F.obj c1) :
    F.objLift i ⟶ F.objLift ((F.map f) i) := ⟨f, by rfl⟩

@[simp]
lemma Functor.coCartesianLift_id (F : C ⥤ Type) {c1 : C} (i : F.obj c1) :
    F.coCartesianLift (𝟙 c1) i = (F.ObjEqIso (by rw [F.map_id]; rfl)).hom := rfl

@[simp]
lemma Functor.coCartesianLift_comp  (F : C ⥤ Type) {c1 c2 c3 : C} (f : c1 ⟶ c2) (g : c2 ⟶ c3)
    (i : F.obj c1) :
    F.coCartesianLift (f ≫ g) i ≫ (F.ObjEqIso (by rw [F.map_comp]; rfl)).hom
    = F.coCartesianLift f i ≫ F.coCartesianLift g (F.map f i) := by
  ext
  simp_all only [Functor.objLift_fst, Functor.objLift_snd, CategoryOfElements.comp_val,
    Functor.coCartesianLift_coe, Functor.ObjEqIso_hom_coe, Category.comp_id]

inductive Functor.liftType  (F : C ⥤ Type) (G : F.Elements ⥤ Type) (c : C) where
  | as : (i : F.obj c) → G.obj (F.objLift i) → F.liftType G c

lemma Functor.liftType_ext(F : C ⥤ Type) {G : F.Elements ⥤ Type} {c : C}
     (s t : F.liftType G c)
     (h1 : s.1 = t.1)
     (h2 : (G.map (F.ObjEqIso h1).hom) s.2 = t.2 ) :
      s = t := by
  match s, t with
  | ⟨s1, s2⟩, ⟨t1, t2⟩ =>
    congr
    simp at h1
    subst h1
    rw [F.ObjEqIso_refl] at h2
    simp at h2
    simp only [heq_eq_eq]
    exact h2

@[simp]
def Functor.liftTypeMap (F : C ⥤ Type) (G : F.Elements ⥤ Type) {c1 c2 : C} (f : c1 ⟶ c2)
    (s : F.liftType G c1) : F.liftType G c2 :=
  ⟨(F.map f) s.1, (G.map (F.coCartesianLift f s.1)) s.2⟩

def Functor.liftFunc (F : C ⥤ Type) (G : F.Elements ⥤ Type) : C ⥤ Type where
  obj := F.liftType G
  map := F.liftTypeMap G
  map_id c := by
    ext a
    refine F.liftType_ext _ _ ?_ ?_
    simp only [liftTypeMap, coCartesianLift_id, FunctorToTypes.map_id_apply, types_id_apply]
    simp only [types_id_apply, liftTypeMap, coCartesianLift_id, id_eq, eq_mpr_eq_cast]
    rw [← types_comp_apply (G.map _) (G.map _)]
    rw [← G.map_comp, ← Iso.trans_hom, F.ObjEqIso_symm]
    rw [Iso.refl_hom, G.map_id]
    rfl
  map_comp {c1 c2 c3} f g := by
    ext a
    apply F.liftType_ext _ _ ?_ ?_
    simp only [liftTypeMap, FunctorToTypes.map_comp_apply, types_comp_apply]
    simp
    repeat rw [← types_comp_apply (G.map _) (G.map _), ← G.map_comp]
    apply congrFun
    apply congrArg
    exact F.coCartesianLift_comp _ _ _

def Functor.liftNatTrans (F : C ⥤ Type) {G H : F.Elements ⥤ Type} (η : G ⟶ H) :
    F.liftFunc G ⟶ F.liftFunc H where
  app X := fun s => ⟨s.1, η.app ⟨X, s.1⟩ s.2⟩
  naturality {X Y} f := by
    ext a
    refine F.liftType_ext _ _ ?_ ?_
    congr
    simp
    erw [← types_comp_apply (G.map _) (η.app _)]
    rw [η.naturality, F.ObjEqIso_refl]
    simp
    rfl

@[simps!]
def Functor.liftFuncFunc (F : C ⥤ Type) : (F.Elements ⥤ Type) ⥤ (C ⥤ Type) where
  obj := F.liftFunc
  map := F.liftNatTrans

@[simps!]
def CategoryOfElements.mapIso {F1 F2 : C ⥤ Type} (η : F1 ≅ F2) :
    F1.Elements ≌ F2.Elements where
  functor := CategoryOfElements.map η.hom
  inverse := CategoryOfElements.map η.inv
  unitIso := NatIso.ofComponents (fun X => F1.ObjEqIso (by simp))
  counitIso := NatIso.ofComponents (fun X => F2.ObjEqIso (by simp))


lemma CategoryOfElements.mapIso_of_ObjEquiv {F1 F2 : C ⥤ Type} (η : F1 ≅ F2) {c : C}
    {i j : F1.obj c} (h : i = j) :
    (mapIso η).functor.map (F1.ObjEqIso h).hom =
    (F2.ObjEqIso (by rw [h]  : η.hom.app c i = η.hom.app c j )).hom := rfl

def CategoryOfElements.mapIsoToTypes  {F1 F2 : C ⥤ Type} (η : F1 ≅ F2) :
    (F2.Elements ⥤ Type) ≌ (F1.Elements ⥤ Type) :=
  CategoryTheory.Equivalence.mk
    ((CategoryTheory.whiskeringLeft _ _ _).obj (mapIso η).functor)
    ((CategoryTheory.whiskeringLeft _ _ _).obj (mapIso η).inverse)
    ((CategoryTheory.whiskeringLeft _ _ _).mapIso (mapIso η).counitIso.symm)
    ((CategoryTheory.whiskeringLeft _ _ _).mapIso (mapIso η).unitIso.symm)


--  I want a natural isomorphism between F2.liftFuncFunc and
-- (mapIsoToTypes η).functor ⋙ F1.liftFuncFunc
-- The first thing we will estblish is, for each G in F2.Elements ⥤  Type, an
-- isomorphism between F2.liftFunc G and (F1.liftFunc) ((mapIsoToTypes η).functor.obj G)
@[simps!]
def CategoryOfElements.isoTypes {F1 F2 : C ⥤ Type} (η : F1 ≅ F2) (G : F2.Elements ⥤ Type)
    (X : C) :
    (F2.liftFunc G).obj X ≅ (F1.liftFunc ((mapIso η).functor ⋙ G)).obj X where
  hom := fun s => ⟨η.inv.app X s.1, G.map (F2.ObjEqIso (by simp)).hom s.2 ⟩
  inv := fun s => ⟨η.hom.app X s.1, G.map (F2.ObjEqIso (by simp)).hom s.2 ⟩
  hom_inv_id := by
    funext s
    refine F2.liftType_ext _ _ ?_ ?_
    simp
    simp
    repeat rw [← types_comp_apply (G.map _) (G.map _), ← G.map_comp]
    rw [← Iso.trans_hom, ← Iso.trans_hom, F2.ObjEqIso_trans, F2.ObjEqIso_trans,
     F2.ObjEqIso_refl]
    simp
  inv_hom_id := by
    funext s
    refine F1.liftType_ext _ _ ?_ ?_
    simp
    simp
    rw [mapIso_of_ObjEquiv]
    repeat rw [← types_comp_apply (G.map _) (G.map _), ← G.map_comp]
    rw [← Iso.trans_hom, ← Iso.trans_hom, F2.ObjEqIso_trans, F2.ObjEqIso_trans,
     F2.ObjEqIso_refl]
    simp

@[simps!]
def CategoryOfElements.isoTypesF {F1 F2 : C ⥤ Type} (η : F1 ≅ F2) (G : F2.Elements ⥤ Type) :
    (F2.liftFunc G) ≅ (F1.liftFunc ((mapIso η).functor ⋙ G)) :=
  NatIso.ofComponents (isoTypes η G) (by
   intro X Y f
   funext s
   rw [types_comp_apply, types_comp_apply]
   refine F1.liftType_ext _ _ ?_ ?_
   simp [Functor.liftFunc]
   rw [← types_comp_apply (F2.map _) (η.inv.app _)]
   erw [η.inv.naturality]
   rfl
   simp [Functor.liftFunc]
   repeat rw [← types_comp_apply (G.map _) (G.map _), ← G.map_comp]
   apply congrFun
   apply congrArg
   ext
   simp only [Functor.objLift_fst, mapIso_functor_obj_fst, Functor.objLift_snd,
     mapIso_functor_obj_snd, isoTypes_hom, comp_val, Functor.coCartesianLift_coe,
     Functor.ObjEqIso_hom_coe, mapIso_functor_map_coe, Category.comp_id, Category.id_comp]
  )

def CategoryOfElements.liftIsoFunc {F1 F2 : C ⥤ Type} (η : F1 ≅ F2) :
    F2.liftFuncFunc ≅ (mapIsoToTypes η).functor ⋙ F1.liftFuncFunc :=
  NatIso.ofComponents (isoTypesF η) (by
    intro G1 G2 ηG
    apply NatTrans.ext
    funext c
    funext s
    refine F1.liftType_ext _ _ (by rfl) ?_
    simp
    change G2.map ((mapIso η).functor.map (F1.ObjEqIso _).hom) _ = _
    rw [mapIso_of_ObjEquiv η]
    repeat rw [← types_comp_apply (G2.map _) (G2.map _), ← G2.map_comp]
    rw [← Iso.trans_hom, F2.ObjEqIso_trans]
    change  (ηG.app _ ≫ _) _ = _
    erw [← ηG.naturality]
    rfl
  )

end CategoryTheory
end lifts

namespace SimplexCategory
namespace WithInitial
open WithInitial
open SimplexCategory

/-- A function from `WithInitial SimplexCategory` to `ℕ` taking the initial object to `0` and
the object `of x` to `x.len+1`. -/
def len (X : WithInitial SimplexCategory) : ℕ :=
  match X with
  | star => 0
  | of x => Nat.succ x.len

/-- Isomorphic objects have the same length. -/
lemma len_iso {X Y : WithInitial SimplexCategory} (f : X ≅ Y) : len X = len Y := by
  simp [len]
  match X, Y with
  | star, star => rfl
  | of x, of y =>
    simp
    let f' : x ≅  y :=
      {hom := f.hom,
       inv := f.inv,
       hom_inv_id := f.hom_inv_id,
       inv_hom_id := f.inv_hom_id}
    have hm : Mono f'.hom := by exact StrongMono.mono
    have he : Epi f'.hom := by exact StrongEpi.epi
    exact Nat.le_antisymm (len_le_of_mono hm) (len_le_of_epi he)


/-- A function from `ℕ` to `WithInitial SimplexCategory` taking `0` to `start` and
 `Nat.succ x` to `of (mk x)`. -/
def mk (i : ℕ) : WithInitial SimplexCategory :=
  match i with
  | Nat.zero => star
  | Nat.succ x => of (SimplexCategory.mk x)

@[simp]
lemma len_mk (i : ℕ) : len (mk i) = i := by
  match i with
  | Nat.zero => rfl
  | Nat.succ x => rfl

/-- Given a morphism `f : X ⟶ Y` in `WithInitial SimplexCategory`, the corresponding ordered
homomorphism from `Fin (len X)` to  `Fin (len Y)`.  -/
def toOrderHom {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) : Fin (len X) →o Fin (len Y) :=
  match X, Y, f with
  | of _, of _, f => f.toOrderHom
  | star, of x, _ => (OrderEmbedding.ofIsEmpty.toOrderHom :  (Fin 0) →o (Fin (len (of x))))
  | star, star, _ => OrderHom.id

@[simp]
lemma toOrderHom_id {Z : WithInitial SimplexCategory} : toOrderHom (𝟙 Z) = OrderHom.id := by
  match Z with
  | of z => rfl
  | star => rfl

lemma toOrderHom_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z):
    toOrderHom (f ≫ g) = (toOrderHom g).comp (toOrderHom f) := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g =>
    apply OrderHom.ext
    exact List.ofFn_inj.mp rfl
  | of x, of y, of z, f, g => rfl

/-- Given an isomorphism `X ≅ Y` the corresponding OrderIso `Fin (len X) ≃o Fin (len Y)`. -/
def orderIsoOfIso {X Y : WithInitial SimplexCategory} (f : X ≅ Y) : Fin (len X) ≃o Fin (len Y) :=
  Equiv.toOrderIso {
    toFun := toOrderHom f.hom
    invFun := toOrderHom f.inv
    left_inv := fun i => by
      simpa only [toOrderHom_comp, toOrderHom_id] using
       congr_arg (fun φ => (toOrderHom φ) i) f.hom_inv_id
    right_inv := fun i => by
      simpa only [toOrderHom_comp, toOrderHom_id] using
       congr_arg (fun φ => (toOrderHom φ) i) f.inv_hom_id}
    (toOrderHom f.hom).monotone (toOrderHom f.inv).monotone

lemma toOrderHomIso_apply {X Y : WithInitial SimplexCategory} (f : X ≅ Y) (a : Fin (len X)) :
    toOrderHom f.hom a = ⟨a, by rw [← len_iso f]; exact a.prop⟩ := by
  rw [Fin.eq_iff_veq]
  exact Fin.coe_orderIso_apply (orderIsoOfIso f) a

lemma toOrderHomIso_apply_inv {X Y : WithInitial SimplexCategory} (f : X ≅ Y) (a : Fin (len Y)) :
    toOrderHom f.inv a = ⟨a, by rw [len_iso f]; exact a.prop⟩ := by
  change toOrderHom f.symm.hom a = _
  exact toOrderHomIso_apply f.symm _

lemma hom_eq_if_toOrderHom_eq {X Y : WithInitial SimplexCategory} {f g: X ⟶ Y}
    (h : toOrderHom f = toOrderHom g) : f = g := by
  match X, Y, f with
  | star, star, _ => rfl
  | star, of x , _ => rfl
  | of x, of y, f =>
    simp [toOrderHom] at h
    let f': x ⟶ y := f
    let g': x ⟶ y :=g
    change f' = g'
    exact Hom.ext f' g' h

/-- The morphism `X ⟶ Y` generated from an OrderHom `Fin (len X) →o Fin (len Y)`. -/
def homMk {X Y : WithInitial SimplexCategory} (f : Fin (len X) →o Fin (len Y)) : X ⟶ Y :=
  match X, Y, f with
  | star, star, _ => 𝟙 star
  | star, of y, _ => starInitial.to (of y)
  | of _, of _, f => SimplexCategory.Hom.mk f
  | of x, star, f => Fin.elim0 (f ⟨0, Nat.succ_pos (SimplexCategory.len x)⟩)

lemma homMk_id {X  : WithInitial SimplexCategory}: homMk (OrderHom.id ) = 𝟙 X :=
  match X with
  | star => rfl
  | of _ => rfl

lemma homMk_comp {X Y Z : WithInitial SimplexCategory}
    (f : Fin (len X) →o Fin (len Y)) (g : Fin (len Y) →o Fin (len Z)) :
    homMk (g.comp f) = homMk f ≫ homMk g := by
  match X, Y, Z, f, g with
  | star, star, star, f, g => rfl
  | star, star, of _, f, g => rfl
  | star, of _, of _, f, g => rfl
  | of _, of _, of _, f, g => rfl
  | star, of _, star, f, g => rfl
  | of x, star, star, f, g => exact Fin.elim0 (f ⟨0, Nat.succ_pos (SimplexCategory.len x)⟩)
  | of _, of y, star, f, g => exact Fin.elim0 (g ⟨0, Nat.succ_pos (SimplexCategory.len y)⟩)
  | of x, star, of _, f, g => exact Fin.elim0 (f ⟨0, Nat.succ_pos (SimplexCategory.len x)⟩)


def isoOfOrderIso {X Y : WithInitial SimplexCategory} (f :  Fin (len X) ≃o Fin (len Y)) :
    X ≅ Y where
  hom := homMk (OrderHomClass.toOrderHom f)
  inv := homMk (OrderHomClass.toOrderHom f.symm)
  hom_inv_id := by
    rw [← homMk_comp, ← homMk_id]
    apply congrArg
    ext
    simp only [OrderHom.comp_coe, OrderHomClass.coe_coe, Function.comp_apply,
      OrderIso.symm_apply_apply, OrderHom.id_coe, id_eq]
  inv_hom_id := by
    rw [← homMk_comp, ← homMk_id]
    apply congrArg
    ext
    simp only [OrderHom.comp_coe, OrderHomClass.coe_coe, Function.comp_apply,
      OrderIso.apply_symm_apply, OrderHom.id_coe, id_eq]

/-- An isomorphism between objects of equal lengths. -/
def lenIso {X Y : WithInitial SimplexCategory} (h : len X = len Y) : X ≅ Y :=
  isoOfOrderIso (Fin.castIso h)

lemma lenIso_refl {X : WithInitial SimplexCategory} :
    lenIso (by rfl  : len X = len X) = Iso.refl X := by
  match X with
  | star => rfl
  | of x => rfl

lemma lenIso_comp_symm_refl {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    lenIso h ≪≫ lenIso h.symm = Iso.refl X := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl

lemma lenIso_comp_trans {X Y Z : WithInitial SimplexCategory} (h1 : len X = len Y)
    (h2 : len Y = len Z) : lenIso h1 ≪≫ lenIso h2 = lenIso (Eq.trans h1 h2) := by
  match X, Y, Z with
  | star, star, star => rfl
  | of x, of y, of z => rfl

lemma orderIso_of_lenIso {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    toOrderHom (lenIso h).hom = Fin.castIso h := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl

lemma toOrderHom_of_lenIso_hom {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    toOrderHom (lenIso h).hom = Fin.castIso h := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl

lemma toOrderHom_of_lenIso_inv {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    toOrderHom (lenIso h).inv = Fin.castIso h.symm := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl


lemma toOrderHom_homMk {X Y : WithInitial SimplexCategory} (f : Fin (len X) →o Fin (len Y)) :
    toOrderHom (homMk f)  = f:= by
  match X, Y with
  | star, star =>
    apply OrderHom.ext
    funext a
    exact Fin.elim0 a
  | star, of y =>
    apply OrderHom.ext
    funext a
    exact Fin.elim0 a
  | of x, star =>
    apply OrderHom.ext
    funext a
    exact Fin.elim0 (f a)
  | of x, of y =>
    rfl

/-- The functor from `WithInitial SimplexCategory × WithInitial SimplexCategory` to
`WithInitial SimplexCategory` which concatenates objects and morphisms. -/
def join :
    WithInitial SimplexCategory × WithInitial SimplexCategory ⥤ WithInitial SimplexCategory where
  obj X :=
    match X with
    | (star, star) => star
    | (of x, star) => of x
    | (star, of x) => of x
    | (of x, of y) => of (Join.func.obj (x,y))
  map {X Y} f :=
    match X, Y, f with
    | (star, star), (star, star), _ => 𝟙 star
    | (star, star), (star, of y), _ => starInitial.to (of y)
    | (star, star), (of y, star), _ => starInitial.to (of y)
    | (star, star), (of y1, of y2), _ => starInitial.to (of (Join.func.obj (y1,y2)))
    | (star, of x), (star, of y), f => f.2
    | (of x, star), (of y, star), f => f.1
    | (of x1, of x2), (of y1, of y2), f => Join.func.map f
    | (of x1, star), (of y1, of y2), f => f.1 ≫ (Join.incl₁ y1 y2)
    | (star, of x2), (of y1, of y2), f => f.2 ≫ (Join.incl₂ y1 y2)
  map_id X :=
    match X with
    | (star, star) => rfl
    | (of x, star) => rfl
    | (star, of x) => rfl
    | (of x, of y) => Join.func.map_id (x,y)
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | (star, star), liftStar_hom, _, f, g => rfl
    | (star, of x), (star, of y), (star, of z), f, g => rfl
    | (of x, star), (of y, star), (of z, star), f, g => rfl
    | (star, of x), (star, of y), (of z1, of z2), f, g => rfl
    | (of x, star), (of y, star), (of z1, of z2), f, g => rfl
    | (star, of x), (of y1, of y2), (of z1, of z2), f, g =>
       simp
       apply congrArg
       let g' : (y1, y2) ⟶ (z1, z2) := g
       change g'.2 ≫ _ = Join.incl₂ y1 y2 ≫ Join.func.toPrefunctor.map g'
       exact (Join.incl₂_map g').symm
    | (of x, star), (of y1, of y2), (of z1, of z2), f, g =>
       simp
       apply congrArg
       let g' : (y1, y2) ⟶ (z1, z2) := g
       change g'.1 ≫ _ = Join.incl₁ y1 y2 ≫ Join.func.toPrefunctor.map g'
       exact (Join.incl₁_map g').symm
    | (of x1, of x2), (of y1, of y2), (of z1, of z2), f, g =>
       let g' : (y1, y2) ⟶ (z1, z2) := g
       let f' : (x1, x2) ⟶ (y1, y2) := f
       exact Join.func.map_comp f' g'

lemma len_of_join (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    len (join.obj X) = (len X.1) + (len X.2) := by
  match X with
  | (star, star) => rfl
  | (star, of x) =>
    simp [join]
    rfl
  | (of x, star) =>
    simp [join]
    rfl
  | (of x, of y) =>
    simp [join, len, Join.func, Nat.succ_eq_add_one]
    omega

lemma len_of_fst_lt_len_of_join_plus_one
    (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    len X.1 < Nat.succ (len (join.obj X)) := by
  rw [len_of_join]
  refine Nat.lt_succ.mpr ?_
  exact Nat.le_add_right (len X.1) (len X.2)

lemma len_of_snd_lt_len_of_join_plus_one
    (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    len X.2 < Nat.succ (len (join.obj X)) := by
  rw [len_of_join]
  refine Nat.lt_succ.mpr ?_
  exact Nat.le_add_left (len X.2) (len X.1)

lemma sub_fst_lt_snd_if_fst_le {X : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (a :  Fin (len (join.obj X))) (h : len (X.1) ≤ a.val) : a.val - len X.1 < len X.2 := by
  have ha := a.prop
  simp [len_of_join] at ha
  exact Nat.sub_lt_left_of_lt_add h ha

lemma toOrderHom_join_apply_on_lt_fst
    {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len (join.obj X))) (ha : a.val < len (X.1)) :
    (toOrderHom (join.map f) a).val = (toOrderHom f.1 ⟨a, ha⟩).val := by
  match X, Y, f with
  | (star, star), _, _ =>
    simp only [len, not_lt_zero'] at ha
  | (star, of x), _, f =>
    simp only [len, not_lt_zero'] at ha
  | (of x, star), (of y, star), f => rfl
  | (of x1, star), (of y1, of y2), f => rfl
  | (of x1, of x2), (of y1, of y2), f =>
    simp only [toOrderHom]
    erw [OrderHom.coe_mk]
    split_ifs
    rfl
    rename_i ht
    simp at ha
    exact (ht ha).elim

lemma toOrderHom_join_apply_on_fst_le
    {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len (join.obj X))) (ha : len (X.1) ≤ a.val) :
    (toOrderHom (join.map f) a).val =
    (toOrderHom f.2 ⟨a.val-len X.1, sub_fst_lt_snd_if_fst_le a ha⟩).val + len Y.1 := by
  simp [join]
  match X, Y, f with
  | (star, star), _, _ =>
    exact Fin.elim0 a
  | (star, of x), (star, of y), f => rfl
  | (star, of x2), (of y1, of y2), f => rfl
  | (of x, star), _, f =>
    simpa [len] using (sub_fst_lt_snd_if_fst_le a ha)
  | (of x1, of x2), (of y1, of y2), f =>
    simp [toOrderHom, Join.func]
    erw [OrderHom.coe_mk]
    split_ifs
    rename_i han
    simp [len] at ha
    rw [Nat.succ_eq_add_one] at ha
    exact ((Nat.not_le.mpr han) ha).elim
    simp [len]


lemma toOrderHom_fst_apply {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len X.1)) :
    (toOrderHom f.1 a).val = ((toOrderHom (join.map f)) ⟨a.val, by
     rw [len_of_join]; exact Nat.lt_add_right (len X.2) a.prop⟩).val := by
  rw [toOrderHom_join_apply_on_lt_fst f]

lemma toOrderHom_snd_apply {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len X.2)) :
    ((toOrderHom f.2) a).val = ((toOrderHom (join.map f)) ⟨a.val + len X.1, by
     rw [len_of_join, add_comm]
     exact Nat.add_lt_add_left a.prop (len X.1)
     ⟩).val - len Y.1:= by
  rw [toOrderHom_join_apply_on_fst_le f]
  simp only [add_tsub_cancel_right, Fin.eta]
  simp only [le_add_iff_nonneg_left, zero_le]

section sourceValue

/-- Given a morphism `f : X ⟶ Y` and a `i` in `Fin (Nat.succ (len Y))`, the element `p` of
`Fin (Nat.succ (len X))` specifying the value to split `X` at in order to generate a
morphism `obj X p` to `obj Y i` from `f`.  -/
def sourceValue {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    Fin (Nat.succ (len X)) :=
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  match k with
  | some k => k.castSucc
  | none => Fin.last (len X)

lemma sourceValue_iff {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y)))
    (a : Fin (Nat.succ (len X))) : sourceValue f i = a ↔
    ∀ (j : Fin (len X)), (j.castSucc < a ↔ (toOrderHom f j).castSucc < i) := by
  simp [sourceValue]
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    apply Iff.intro
    · intro ha
      subst ha
      intro j
      apply Iff.intro
        (fun hj => lt_iff_not_le.mpr ((hk.right j).mt (lt_iff_not_le.mp
          (Fin.castSucc_lt_castSucc_iff.mp hj))))
      intro hj
      by_contra hn
      exact lt_iff_not_le.mp (LT.lt.trans_le hj hk.left) ((toOrderHom f).monotone'
      ((Fin.castSucc_le_castSucc_iff.mp  (not_lt.mp hn))))
    · intro h
      have hx := ((h x).mp.mt)
      simp only [not_lt] at hx
      by_cases ha : a.val < len X
      · have hap := h ⟨a.val, ha⟩
        simp only [Fin.castSucc_mk, Fin.eta, lt_self_iff_false, gt_iff_lt, false_iff, not_lt] at hap
        ext
        exact Nat.le_antisymm (hk.right ⟨a.val, ha⟩ hap) (hx hk.left)
      · exact (lt_iff_not_le.mp x.prop (le_trans (not_lt.mp ha) (hx hk.left)) ).elim
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    apply Iff.intro
    · intro h
      subst h
      exact fun _ => Iff.intro (fun _ ↦ Fin.not_le.mp (hk _)) (fun _ ↦ Fin.castSucc_lt_last _)
    · intro h
      match X with
      | star =>
        simp only [Fin.eq_iff_veq, len, Fin.coe_fin_one]
      | of x =>
        simp_all only [not_le, iff_true, len]
        exact (Fin.last_le_iff.mp (h (Fin.last (SimplexCategory.len x)))).symm



lemma sourceValue_cond {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y))) :
    ∀ (j : Fin (len X)), (j.castSucc < (sourceValue f i) ↔ (toOrderHom f j).castSucc < i) :=
  (sourceValue_iff f i (sourceValue f i)).mp (by rfl)

lemma sourceValue_val_iff {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y)))
    (a : ℕ) : (sourceValue f i).val = a ↔ a < Nat.succ (len X) ∧
    ∀ (j : Fin (len X)), (j.val < a ↔ (toOrderHom f j).castSucc < i) := by
  apply Iff.intro
  intro ha
  subst ha
  apply And.intro
  exact (sourceValue f i).prop
  exact sourceValue_cond f i
  intro ha
  suffices h : (sourceValue f i) = ⟨a, ha.left⟩ from (Fin.eq_iff_veq _ _).mp h
  rw [sourceValue_iff]
  exact ha.right


lemma sourceValue_monotone {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)  :
    Monotone (sourceValue f) := by
  intro a b hab
  have hj : ∀ (j : Fin (len X)),  Fin.castSucc j < sourceValue f a →
      Fin.castSucc j < sourceValue f b := by
    intro j
    rw [sourceValue_cond f b j, sourceValue_cond f a j]
    intro hj
    exact LT.lt.trans_le hj hab
  by_contra hab
  simp only [not_le] at hab
  have hb : (sourceValue f b).val < (len X) :=  Nat.lt_of_lt_of_le hab
    (Nat.lt_succ.mp (sourceValue f a).prop )
  exact LT.lt.false ((hj ⟨(sourceValue f b).val, hb⟩) hab)

lemma sourceValue_of_iso_hom {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len X))) :
    sourceValue f.hom i = ⟨i.val, by rw [len_iso f]; exact i.prop⟩ := by
  rw [sourceValue_iff]
  intro j
  rw [toOrderHomIso_apply]
  rfl

lemma sourceValue_of_iso_inv {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len Y))) :
    sourceValue f.inv i = ⟨i.val, by rw [← len_iso f]; exact i.prop⟩ := by
  change sourceValue (f.symm).hom i =_
  rw [sourceValue_of_iso_hom]

lemma sourceValue_of_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    sourceValue (𝟙 X) i = i := by
  change sourceValue (Iso.refl X).hom i = i
  rw [sourceValue_of_iso_hom]

lemma sourceValue_of_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z))) : sourceValue f (sourceValue g i) = sourceValue (f ≫ g) i := by
  rw [sourceValue_iff]
  intro j
  apply Iff.intro
  · intro hj
    have hjj := (sourceValue_cond (f ≫ g) i  j).mp hj
    rw [toOrderHom_comp] at hjj
    simp only [OrderHom.comp_coe, Function.comp_apply] at hjj
    exact (sourceValue_cond g i  ((toOrderHom f) j)).mpr hjj
  · intro hj
    have hjj := (sourceValue_cond g i  ((toOrderHom f) j)).mp hj
    change  Fin.castSucc (((toOrderHom g).comp (toOrderHom f)) ( j)) < i at hjj
    rw [← toOrderHom_comp] at hjj
    exact (sourceValue_cond (f ≫ g) i  j).mpr hjj

@[simps!]
def sourceValueOrder {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) :
    Fin ((SimplexCategory.mk ((len Y))).len+1) →o Fin ((SimplexCategory.mk ((len X))).len+1) :=
    ((OrderHomClass.toOrderHom (@Fin.castIso (Nat.succ (len X))
      ((SimplexCategory.mk ((len X))).len+1) (by simp )) ).comp
    {toFun := sourceValue f, monotone' := sourceValue_monotone f }).comp
    (OrderHomClass.toOrderHom (@Fin.castIso ((SimplexCategory.mk ((len Y))).len+1)
    (Nat.succ (len Y)) (by simp )))

def func : WithInitial SimplexCategory ⥤ SimplexCategoryᵒᵖ  where
  obj X := Opposite.op (SimplexCategory.mk (len X))
  map {X Y} f := Opposite.op (SimplexCategory.Hom.mk (sourceValueOrder f))
  map_id X := by
    rw [← op_id]
    simp
    repeat apply congrArg
    apply OrderHom.ext
    funext a
    simp [sourceValueOrder, sourceValue_of_id]
    rfl
  map_comp {X Y Z} f g := by
    simp
    change _=  Opposite.op (Hom.mk ((sourceValueOrder f).comp (sourceValueOrder g)))
    repeat apply congrArg
    apply OrderHom.ext
    funext a
    simp [sourceValueOrder, sourceValue_of_comp]
    erw [sourceValue_of_comp f g]

lemma sourceValue_of_join {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) : sourceValue (join.map f) ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    = ⟨len X.1, len_of_fst_lt_len_of_join_plus_one X⟩ := by
  rw [sourceValue_iff]
  intro j
  apply Iff.intro
  · intro hj
    rw [Fin.lt_def]
    exact lt_of_eq_of_lt (toOrderHom_join_apply_on_lt_fst f j hj)
      ((toOrderHom f.1) ⟨j.val, hj⟩).prop
  · intro hj
    by_contra hn
    have ht := toOrderHom_join_apply_on_fst_le f j (not_lt.mp hn)
    simp_all only [Fin.lt_def, Fin.coe_castSucc, add_lt_iff_neg_right, not_lt_zero']

end sourceValue


section classifyingMap

@[simps!]
def joinClassifying : (WithInitial SimplexCategory)ᵒᵖ ⥤ Type where
  obj X :=
   match X with
   | ⟨X⟩ =>  Fin (Nat.succ (len X))
  map {X Y f} :=
   match X, Y, f with
   | ⟨X⟩, ⟨Y⟩, ⟨f⟩ => sourceValue f
  map_id X := by
    match X with
    | ⟨X⟩ =>
     funext i
     exact sourceValue_of_id i
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | ⟨X⟩, ⟨Y⟩, ⟨Z⟩, ⟨f⟩, ⟨g⟩ =>
     funext i
     exact (sourceValue_of_comp g f i).symm
@[simps!]
def π : joinClassifying.Elementsᵒᵖ ⥤ WithInitial SimplexCategory :=
  (CategoryOfElements.π joinClassifying).leftOp

@[simps!]
def objClass : joinClassifying.Elementsᵒᵖ → WithInitial SimplexCategory × WithInitial SimplexCategory :=
  fun s => (mk s.1.2.val, mk s.1.2.rev.val)

@[simp]
lemma len_obj₁ (Xi : joinClassifying.Elementsᵒᵖ)  : len (objClass Xi).1 = Xi.1.2.val := by
  simp only [objClass_fst, len_mk, joinClassifying_obj]

@[simp]
lemma len_obj₂ (Xi : joinClassifying.Elementsᵒᵖ)  :
    len (objClass Xi).2 = (len (π.obj Xi)) - Xi.1.2.val := by
  simp only [objClass_snd, len_mk, π_obj, joinClassifying_obj]

lemma incl₁_cond {Xi : joinClassifying.Elementsᵒᵖ} (a : Fin (len (objClass Xi).1)) :
    a.val < len (π.obj Xi) := by
  have ha := a.prop
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (objClass Xi).1)` into `Fin (len (π.obj Xi))`. -/
@[simps!]
def incl₁ {Xi : joinClassifying.Elementsᵒᵖ} :
    Fin (len (objClass Xi).1) →o Fin (len (π.obj Xi)) where
  toFun := fun a => ⟨a.val, incl₁_cond a⟩
  monotone' := by
    intro a b hab
    exact hab

lemma incl₂_cond  {Xi : joinClassifying.Elementsᵒᵖ} (a : Fin (len (objClass Xi).2)) :
    a.val + Xi.1.2.val < len (π.obj Xi) := by
  have ha := a.prop
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (objClass Xi).2)` into `Fin (len (π.obj Xi))`. -/
@[simps!]
def incl₂ {Xi : joinClassifying.Elementsᵒᵖ} :
    Fin (len (objClass Xi).2) →o Fin (len (π.obj Xi)) where
  toFun := fun a => ⟨a.val + Xi.1.2.val, incl₂_cond a⟩
  monotone' := by
    intro a b hab
    simp only [π_obj, joinClassifying_obj, Fin.mk_le_mk, add_le_add_iff_right, Fin.val_fin_le]
    exact hab

lemma mapOrderHom₁_cond {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp)
    (a : Fin (len (objClass Xi).1)) : (toOrderHom f.1.1.1 (incl₁ a)).val < len (objClass Yp).1 :=
  let ht := lt_of_eq_of_lt' ((Fin.eq_iff_veq _ _).mp f.1.2).symm
    ( lt_of_eq_of_lt' (len_obj₁ Xi) a.prop )
  lt_of_eq_of_lt' (len_obj₁ Yp).symm
    ( Fin.lt_def.mp ((sourceValue_cond f.1.1.1 Yp.1.2 (incl₁ a)).mp ht))

@[simps!]
def mapOrderHom₁ {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp) :
    Fin (len (objClass Xi).1) →o Fin (len (objClass Yp).1) where
  toFun := fun a => ⟨(toOrderHom f.1.1.1 (incl₁ a)).val, mapOrderHom₁_cond f a⟩
  monotone' := by
    intro a b h
    exact (toOrderHom f.1.1.1).monotone' h

@[simp]
lemma mapOrderHom₁_apply {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp)
    (a : Fin (len (objClass Xi).1)) :
    incl₁ (mapOrderHom₁ f a)= (toOrderHom f.1.1.1) (incl₁ a) := rfl

@[simp]
lemma mapOrderHom₁_apply_val {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp)
    (a : Fin (len (objClass Xi).1)) :
    (mapOrderHom₁ f a).val= ((toOrderHom f.1.1.1) (incl₁ a)).val := rfl


@[simp]
lemma mapOrderHom₁_id (Xi : joinClassifying.Elementsᵒᵖ) :
    mapOrderHom₁ (𝟙 Xi) = OrderHom.id := by
  apply OrderHom.ext
  funext a
  ext
  rw [Eq.trans (incl₁_coe_val _).symm ((Fin.eq_iff_veq _ _).mp (mapOrderHom₁_apply (𝟙 Xi) a))]
  erw [congr_arg toOrderHom (by rfl), toOrderHom_id]
  rfl

@[simp]
lemma mapOrderHom₁_comp {Xi Yp Zr : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp) (g : Yp ⟶ Zr) :
    mapOrderHom₁ (f ≫ g) = (mapOrderHom₁ g).comp (mapOrderHom₁ f) := by
  apply OrderHom.ext
  funext a
  ext
  simp only [objClass_fst, OrderHom.comp_coe, Function.comp_apply]
  erw [Eq.trans (incl₁_coe_val _).symm ((Fin.eq_iff_veq _ _).mp (mapOrderHom₁_apply (f ≫ g) a))]
  erw [Eq.trans (incl₁_coe_val _).symm ((Fin.eq_iff_veq _ _).mp (mapOrderHom₁_apply g _))]
  erw [(mapOrderHom₁_apply (f) _)]
  erw [toOrderHom_comp]
  rfl


@[simp]
lemma mapOrderHom₂_cond' {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp)
    (a : Fin (len (objClass Xi).2)) : Yp.1.2.val ≤ (toOrderHom f.1.1.1 (incl₂ a)).val := by
  have h0 : Xi.1.2.val ≤ (incl₂ a).val := (Nat.le_add_left Xi.1.2.val a.val)
  rw [← (Fin.eq_iff_veq _ _).mp f.1.2] at h0
  exact Fin.le_def.mp
    (not_lt.mp ((sourceValue_cond f.1.1.1 Yp.1.2 (incl₂ a)).mpr.mt (not_lt.mpr h0)))

@[simp]
lemma mapOrderHom₂_cond {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp)
    (a : Fin (len (objClass Xi).2)) :
    (toOrderHom f.1.1.1 (incl₂ a)).val - Yp.1.2.val <  len (objClass Yp).2 := by
  rw [tsub_lt_iff_right]
  simp only [joinClassifying_obj, joinClassifying_map, π_obj, objClass_snd, len_mk]
  rw [tsub_add_cancel_iff_le.mpr (Yp.unop.snd.is_le)]
  exact ((toOrderHom f.unop.1.unop) (incl₂ a)).prop
  exact mapOrderHom₂_cond' _ _

@[simps!]
def mapOrderHom₂ {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp) :
    Fin (len (objClass Xi).2) →o Fin (len (objClass Yp).2) where
  toFun := fun a => ⟨(toOrderHom f.1.1.1 (incl₂ a)).val - Yp.1.2.val, mapOrderHom₂_cond f a⟩
  monotone' := by
    intro a b h
    simp only [joinClassifying_obj, joinClassifying_map, π_obj, Fin.mk_le_mk, tsub_le_iff_right]
    rw [tsub_add_cancel_iff_le.mpr]
    exact (toOrderHom f.1.1.1).monotone' (incl₂.monotone' h)
    exact mapOrderHom₂_cond' _ _

@[simp]
lemma mapOrderHom₂_apply {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp)
    (a : Fin (len (objClass Xi).2)) :
    incl₂ (mapOrderHom₂ f a)= (toOrderHom f.1.1.1) (incl₂ a) := by
  ext
  rw [incl₂_coe_val, mapOrderHom₂]
  refine tsub_add_cancel_of_le ?_
  exact mapOrderHom₂_cond' _ _

lemma mapOrderHom₂_apply_val {Xi Yp : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp)
    (a : Fin (len (objClass Xi).2)) :
    (mapOrderHom₂ f a).val = ((toOrderHom f.1.1.1) (incl₂ a)).val - Yp.1.2.val := by
  rw [mapOrderHom₂]
  simp only [joinClassifying_obj, joinClassifying_map, π_obj, OrderHom.coe_mk]

@[simp]
lemma mapOrderHom₂_id (Xi : joinClassifying.Elementsᵒᵖ) : mapOrderHom₂ (𝟙 Xi) = OrderHom.id := by
  apply OrderHom.ext
  funext a
  ext
  have ha := Eq.trans (incl₂_coe_val _).symm ((Fin.eq_iff_veq _ _).mp (mapOrderHom₂_apply (𝟙 Xi) a))
  erw [congr_arg toOrderHom (by rfl), toOrderHom_id, incl₂_coe_val] at ha
  exact Nat.add_right_cancel ha

@[simp]
lemma mapOrderHom₂_comp {Xi Yp Zr : joinClassifying.Elementsᵒᵖ} (f : Xi ⟶ Yp) (g : Yp ⟶ Zr) :
    mapOrderHom₂ (f ≫ g) = (mapOrderHom₂ g).comp (mapOrderHom₂ f) := by
  apply OrderHom.ext
  funext a
  ext
  simp only [objClass_fst, OrderHom.comp_coe, Function.comp_apply]
  have ha := Eq.trans (incl₂_coe_val _).symm ((Fin.eq_iff_veq _ _).mp
    (mapOrderHom₂_apply (f ≫ g) a))
  have hb := Eq.trans (incl₂_coe_val _).symm ((Fin.eq_iff_veq _ _).mp
    (mapOrderHom₂_apply g ((mapOrderHom₂ f) a)))
  erw [(mapOrderHom₂_apply (f) _)] at hb
  erw [toOrderHom_comp, ← hb] at ha
  exact Nat.add_right_cancel ha

@[simps!]
def toWithInitialWithInitial : joinClassifying.Elementsᵒᵖ ⥤
    WithInitial SimplexCategory × WithInitial SimplexCategory where
  obj := objClass
  map f := (homMk (mapOrderHom₁ f), homMk (mapOrderHom₂ f))
  map_id X := by
    simp [homMk_id]
    rfl
  map_comp := by
    simp [homMk_comp]

section inverse

@[simps!]
def invObj (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    joinClassifying.Elementsᵒᵖ :=
  ⟨⟨⟨join.obj X⟩, ⟨len X.1, by
  simp only [len_of_join]
  exact Nat.lt_succ_iff.mpr (Nat.le_add_right (len X.1) (len X.2))
   ⟩⟩⟩

@[simps!]
def invMap {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory} (f : X ⟶ Y) :
    invObj X ⟶ invObj Y :=
  ⟨⟨⟨join.map f⟩, by
  simp
  erw [sourceValue_of_join]
  rfl
  ⟩⟩

lemma mapOrderHom₁_of_invMap {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) : homMk (mapOrderHom₁ (invMap f)) =
    (lenIso (by simp )).hom ≫ f.1 ≫ (lenIso (by simp )).hom := by
  apply hom_eq_if_toOrderHom_eq
  rw [toOrderHom_homMk, toOrderHom_comp, toOrderHom_comp, toOrderHom_of_lenIso_hom,
    toOrderHom_of_lenIso_hom]
  apply OrderHom.ext
  funext a
  ext
  erw [toOrderHom_fst_apply]
  rfl

lemma mapOrderHom₂_of_invMap {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) : homMk (mapOrderHom₂ (invMap f)) =
    (lenIso (by simp [len_of_join])).hom ≫ f.2 ≫ (lenIso (by simp [len_of_join] )).hom := by
  apply hom_eq_if_toOrderHom_eq
  rw [toOrderHom_homMk, toOrderHom_comp, toOrderHom_comp, toOrderHom_of_lenIso_hom,
    toOrderHom_of_lenIso_hom]
  apply OrderHom.ext
  funext a
  ext
  erw [toOrderHom_snd_apply]
  rfl

@[simps!]
def invFun : WithInitial SimplexCategory × WithInitial SimplexCategory ⥤
    joinClassifying.Elementsᵒᵖ where
  obj := invObj
  map := invMap
  map_id X := by
    simp [invMap]
    congr
  map_comp {X Y Z} f g := by
    simp [invMap]
    congr
    erw [join.map_comp]
    rfl

@[simps!]
def unitApp (X : WithInitial SimplexCategory × WithInitial SimplexCategory) :
    (invFun ⋙ toWithInitialWithInitial).obj X ≅ X where
  hom := ((lenIso (by simp)).hom, (lenIso (by simp [len_of_join])).hom)
  inv := ((lenIso (by simp)).inv, (lenIso (by simp [len_of_join])).inv)

def unit : invFun ⋙ toWithInitialWithInitial ≅
    𝟭 (WithInitial SimplexCategory × WithInitial SimplexCategory) :=
  NatIso.ofComponents unitApp (by
   intro X Y f
   simp
   rw [mapOrderHom₁_of_invMap, mapOrderHom₂_of_invMap]
   simp
   rw [← Iso.trans_hom, ← Iso.trans_hom, lenIso_comp_symm_refl, lenIso_comp_symm_refl]
   simp
  )

def coUnitApp (X : joinClassifying.Elementsᵒᵖ) : X  ≅
    (toWithInitialWithInitial ⋙ invFun).obj X where
  hom := ⟨⟨⟨(lenIso (by
   simp [len_of_join]
   rw [add_comm]
   refine (Nat.sub_add_cancel X.unop.snd.is_le).symm
  )).hom⟩, by simp [sourceValue_of_iso_hom] ⟩⟩
  inv := ⟨⟨⟨(lenIso (by
   simp [len_of_join]
   rw [add_comm]
   refine (Nat.sub_add_cancel X.unop.snd.is_le).symm
  )).inv⟩, by simp [sourceValue_of_iso_inv, invObj] ⟩⟩
  hom_inv_id := by
    erw [← op_id, ← op_comp]
    apply congrArg
    apply CategoryOfElements.ext
    simp
    erw [← op_comp]
    simp
  inv_hom_id := by
    erw [← op_id, ← op_comp]
    apply congrArg
    apply CategoryOfElements.ext
    simp
    erw [← op_comp]
    simp
    rfl

def coUnit : 𝟭 (joinClassifying.Elementsᵒᵖ) ≅ toWithInitialWithInitial ⋙ invFun
     :=
  NatIso.ofComponents coUnitApp (by
    intro X Y f
    match X, Y, f with
    | ⟨⟨⟨X⟩,i⟩⟩, ⟨⟨⟨Y⟩,p⟩⟩, ⟨⟨⟨f⟩,h⟩⟩ =>
    erw [← Iso.inv_comp_eq]
    simp only [CategoryStruct.comp]
    apply congrArg
    apply CategoryOfElements.ext
    erw [Subtype.coe_mk, Subtype.coe_mk]
    apply congrArg
    change ((lenIso _).inv ≫ f ≫ (lenIso _).hom) = (join.map (homMk (_), homMk (mapOrderHom₂ _)))
    apply hom_eq_if_toOrderHom_eq
    apply OrderHom.ext
    funext a
    ext
    rw [toOrderHom_comp, toOrderHom_comp, toOrderHom_of_lenIso_inv, toOrderHom_of_lenIso_hom]
    by_cases ha : a < len (objClass ⟨⟨⟨X⟩,i⟩⟩).1
    · rw [toOrderHom_join_apply_on_lt_fst]
      swap
      exact ha
      change _ = (incl₁ (toOrderHom (homMk (mapOrderHom₁ _)) ⟨a,ha⟩)).val
      rw [toOrderHom_homMk, mapOrderHom₁_apply]
      rfl
    · simp at ha
      rw [toOrderHom_join_apply_on_fst_le]
      swap
      simpa using ha
      rw [toOrderHom_homMk]
      simp
      rw [tsub_add_cancel_iff_le.mpr]
      repeat apply congrArg
      ext
      exact (tsub_add_cancel_iff_le.mpr ha).symm
      let ap : Fin (len X) := ⟨a.val, by
       have ha' :=  lt_of_eq_of_lt' (len_of_join _) a.prop
       simp at ha'
       rw [add_comm] at ha'
       rw [tsub_add_cancel_iff_le.mpr i.is_le] at ha'
       exact ha'
       ⟩
      have hx : ¬Fin.castSucc ap < sourceValue f p  := by
        simp only [joinClassifying_obj, Fin.castSucc_mk, not_lt]
        simp only [joinClassifying_obj, joinClassifying_map] at h
        rw [h]
        exact ha
      refine le_of_eq_of_le' ?_ (Nat.not_lt.mp (((sourceValue_cond f p ap).mpr.mt hx)))
      rw [Fin.coe_castSucc]
      repeat apply congrArg
      ext
      exact Nat.eq_add_of_sub_eq ha rfl
  )

@[simps!]
def joinClassifyEquiv :
    joinClassifying.Elementsᵒᵖ ≌ WithInitial SimplexCategory × WithInitial SimplexCategory :=
  CategoryTheory.Equivalence.mk toWithInitialWithInitial invFun coUnit unit

@[simps!]
def joinClassifyEquivOp : joinClassifying.Elements  ≌
    (WithInitial SimplexCategory × WithInitial SimplexCategory)ᵒᵖ :=
  (opOpEquivalence (joinClassifying.Elements)).symm.trans joinClassifyEquiv.op

@[simps!]
def joinClassifyEquivOpOp : joinClassifying.Elements  ≌
    (WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ :=
  joinClassifyEquivOp.trans (prodOpEquiv (WithInitial SimplexCategory))

end inverse

@[simps!]
def joinLiftObj {X : (WithInitial SimplexCategory)ᵒᵖ} (i : joinClassifying.obj X) :
    joinClassifying.Elements := ⟨X, i⟩

@[simps!]
def joinLiftObjEqIso {X : (WithInitial SimplexCategory)ᵒᵖ} {i j : joinClassifying.obj X}
    (h : i = j) : joinLiftObj i ≅ joinLiftObj j where
  hom := ⟨𝟙 X, by
    simp
    subst h
    erw [congr_arg sourceValue (by rfl : (𝟙 X).unop = 𝟙 (Opposite.unop X))]
    erw [sourceValue_of_id]⟩
  inv := ⟨𝟙 X, by
    simp
    subst h
    erw [congr_arg sourceValue (by rfl : (𝟙 X).unop = 𝟙 (Opposite.unop X))]
    erw [sourceValue_of_id]⟩
  hom_inv_id := by
    ext
    simp only [joinClassifying_obj, joinLiftObj_fst, joinLiftObj_snd, joinClassifying_map,
      CategoryOfElements.comp_val, Category.comp_id, CategoryOfElements.id_val]
  inv_hom_id := by
    ext
    simp only [joinClassifying_obj, joinLiftObj_fst, joinLiftObj_snd, joinClassifying_map,
      CategoryOfElements.comp_val, Category.comp_id, CategoryOfElements.id_val]

lemma joinLiftObjEqIso_refl {X : (WithInitial SimplexCategory)ᵒᵖ} {i : joinClassifying.obj X}
    (h : i = i) : joinLiftObjEqIso h = Iso.refl (joinLiftObj i) := by
  rfl

@[simp]
lemma joinLiftObjEqIso_symm {X : (WithInitial SimplexCategory)ᵒᵖ} {i j: joinClassifying.obj X}
    (h : i = j) : joinLiftObjEqIso h ≪≫ joinLiftObjEqIso h.symm = Iso.refl (joinLiftObj i) := by
  subst h
  rw [joinLiftObjEqIso_refl]
  ext
  simp only [joinClassifying_obj, joinLiftObj_fst, joinLiftObj_snd, joinClassifying_map,
    Iso.trans_refl, Iso.refl_hom, CategoryOfElements.id_val]


@[simps!]
def coCartesianLift {X Y : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y)
    (i : joinClassifying.obj X) :
    joinLiftObj i ⟶ joinLiftObj ((joinClassifying.map f) i) := ⟨f, by rfl⟩

@[simp]
lemma coCartesianLift_id (X : (WithInitial SimplexCategory)ᵒᵖ) (i : joinClassifying.obj X) :
    coCartesianLift (𝟙 X) i = (joinLiftObjEqIso (by rw [joinClassifying.map_id]; rfl)).hom := rfl

@[simp]
lemma coCartesianLift_comp {X Y Z : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : joinClassifying.obj X) :
    coCartesianLift (f ≫ g) i ≫ (joinLiftObjEqIso (by {
      rw [joinClassifying.map_comp]
      rfl})).hom = coCartesianLift f i ≫ coCartesianLift g (joinClassifying.map f i) := by
  simp_all only [joinClassifying_map]
  ext
  simp_all only [joinClassifying_obj, joinLiftObj_fst, joinLiftObj_snd, joinClassifying_map,
    CategoryOfElements.comp_val, coCartesianLift_coe, joinLiftObjEqIso_hom_coe, Category.comp_id]



end classifyingMap


section joinAssoc

def assocType1Part : joinClassifying.Elements ⥤ Type :=
  joinClassifyEquivOpOp.functor ⋙ CategoryTheory.Prod.fst _ _ ⋙ joinClassifying

def assocTypeSndPart : joinClassifying.Elements ⥤ Type :=
  joinClassifyEquivOpOp.functor ⋙ CategoryTheory.Prod.snd _ _ ⋙ joinClassifying

inductive assocType1 (X : (WithInitial SimplexCategory)ᵒᵖ)
  | as : (i : joinClassifying.obj X ) →
    (p : (assocType1Part).obj (joinLiftObj i)) → assocType1 X

inductive assocTypeSnd (X : (WithInitial SimplexCategory)ᵒᵖ)
  | as : (i : joinClassifying.obj X ) →
    (p : (assocTypeSndPart).obj (joinLiftObj i)) → assocTypeSnd X


lemma assocType1_ext  {X : (WithInitial SimplexCategory)ᵒᵖ} (s t : assocType1 X)
    (h1 : s.1 = t.1)
    (h2 : ((assocType1Part).map (joinLiftObjEqIso h1).hom) s.2 = t.2) :
    s = t := by
  match s, t with
  | ⟨s1, s2⟩, ⟨t1, t2⟩ =>
    congr
    simp at h1
    subst h1
    erw [assocType1Part.map_id] at h2
    simp at h2
    simpa using h2

lemma assocType1_ext_val  {X : (WithInitial SimplexCategory)ᵒᵖ} (s t : assocType1 X)
    (h1 : s.1 = t.1) (h2 : s.2.val = t.2.val) :
    s = t := by
  refine assocType1_ext _ _ h1 ?_
  rw [Fin.eq_iff_veq]
  rw [← h2]
  simp only [joinClassifyEquivOp_functor_obj, Opposite.unop_op, objClass_fst, joinLiftObj_fst,
    joinLiftObj_snd, assocType1Part, Functor.comp_map,
    Prod.fst_obj, Prod.fst_map, joinClassifying_map]
  change (sourceValue (((CategoryTheory.Prod.fst _ _).mapIso
  (joinClassifyEquivOpOp.functor.mapIso (joinLiftObjEqIso h1))).unop.hom) s.2).val
    = s.2.val
  rw [sourceValue_of_iso_hom]


lemma assocTypeSnd_ext  {X : (WithInitial SimplexCategory)ᵒᵖ} (s t : assocTypeSnd X)
    (h1 : s.1 = t.1)
    (h2 : ((assocTypeSndPart).map (joinLiftObjEqIso h1).hom) s.2 = t.2) :
    s = t := by
  match s, t with
  | ⟨s1, s2⟩, ⟨t1, t2⟩ =>
    congr
    simp at h1
    subst h1
    erw [assocTypeSndPart.map_id] at h2
    simp at h2
    simpa using h2

lemma assocTypeSnd_ext_val  {X : (WithInitial SimplexCategory)ᵒᵖ} (s t : assocTypeSnd X)
    (h1 : s.1 = t.1) (h2 : s.2.val = t.2.val) :
    s = t := by
  refine assocTypeSnd_ext _ _ h1 ?_
  rw [Fin.eq_iff_veq]
  rw [← h2]
  simp only [joinClassifyEquivOp_functor_obj, Opposite.unop_op, objClass_fst, joinLiftObj_fst,
    joinLiftObj_snd, assocType1Part, Functor.comp_map,
    Prod.fst_obj, Prod.fst_map, joinClassifying_map]
  change (sourceValue (((CategoryTheory.Prod.snd _ _).mapIso
  (joinClassifyEquivOpOp.functor.mapIso (joinLiftObjEqIso h1))).unop.hom) s.2).val
    = s.2.val
  rw [sourceValue_of_iso_hom]

@[simp]
def assocType1Map {X Y : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y) (s : assocType1 X) :
    assocType1 Y :=
    assocType1.as
      (joinClassifying.map f s.1)
      ((assocType1Part).map (coCartesianLift f s.1) s.2)

def assocTypeSndMap {X Y : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y) (s : assocTypeSnd X) :
  assocTypeSnd Y :=
    assocTypeSnd.as
      (joinClassifying.map f s.1)
      ((assocTypeSndPart).map (coCartesianLift f s.1) s.2)


@[simps!]
def assocClassifier1 : (WithInitial SimplexCategory)ᵒᵖ ⥤ Type where
  obj := assocType1
  map := assocType1Map
  map_id X := by
    funext a
    simp only [assocType1Map]
    refine assocType1_ext _ _ ?_ ?_
    simp only [joinClassifying.map_id]
    rfl
    rw [← types_comp_apply (assocType1Part.map _) (assocType1Part.map _)]
    rw [← assocType1Part.map_comp, coCartesianLift_id]
    erw [← Iso.trans_hom, joinLiftObjEqIso_symm, assocType1Part.map_id]
    rfl
  map_comp {X Y Z} f g := by
    funext a
    simp only [assocType1Map]
    refine assocType1_ext _ _ ?_ ?_
    simp only [joinClassifying.map_comp]
    rfl
    simp only
    rw [← types_comp_apply (assocType1Part.map _) (assocType1Part.map _)]
    rw [← assocType1Part.map_comp, coCartesianLift_comp, assocType1Part.map_comp]
    rfl

@[simps!]
def assocClassifierSnd : (WithInitial SimplexCategory)ᵒᵖ ⥤ Type where
  obj := assocTypeSnd
  map := assocTypeSndMap
  map_id X := by
    funext a
    simp only [assocTypeSndMap]
    refine assocTypeSnd_ext _ _ ?_ ?_
    simp only [joinClassifying.map_id]
    rfl
    rw [← types_comp_apply (assocTypeSndPart.map _) (assocTypeSndPart.map _)]
    rw [← assocTypeSndPart.map_comp, coCartesianLift_id]
    erw [← Iso.trans_hom, joinLiftObjEqIso_symm, assocTypeSndPart.map_id]
    rfl
  map_comp {X Y Z} f g := by
    funext a
    simp only [assocTypeSndMap]
    refine assocTypeSnd_ext _ _ ?_ ?_
    simp only [joinClassifying.map_comp]
    rfl
    simp only
    rw [← types_comp_apply (assocTypeSndPart.map _) (assocTypeSndPart.map _)]
    rw [← assocTypeSndPart.map_comp, coCartesianLift_comp, assocTypeSndPart.map_comp]
    rfl

@[simps!]
def assocIsoComponents (X : (WithInitial SimplexCategory)ᵒᵖ) :
    assocClassifier1.obj X ≅ assocClassifierSnd.obj X where
  hom := fun s => ⟨ ⟨s.2.val, by
      have hs1 := Nat.lt_succ_iff.mp s.1.prop
      have hs2 := Nat.lt_succ_iff.mp s.2.prop
      simp_all
      exact Nat.lt_succ_iff.mpr (hs2.trans hs1)
    ⟩
    , ⟨s.1.val - s.2.val, by
      rw [Nat.lt_succ_iff]
      have hs1 := Nat.lt_succ_iff.mp s.1.prop
      have hs2 := Nat.lt_succ_iff.mp s.2.prop
      simp_all
      rw [tsub_add_cancel_iff_le.mpr (hs2.trans hs1)]
      exact hs1
    ⟩⟩
  inv := fun s => ⟨ ⟨s.1.val + s.2.val, by
      have hs1 := Nat.lt_succ_iff.mp s.1.prop
      have hs2 := Nat.lt_succ_iff.mp s.2.prop
      simp_all
      rw [le_tsub_iff_left hs1] at hs2
      rw [Nat.lt_succ_iff]
      exact hs2
    ⟩,
    ⟨s.1.val, by
      simp
      rw [Nat.lt_succ_iff]
      exact Nat.le_add_right s.1.val s.2.val
    ⟩⟩
  hom_inv_id := by
    funext s
    have hs2 := Nat.lt_succ_iff.mp s.2.prop
    refine assocType1_ext_val _ _ ?_ ?_
    simp_all
    simp
  inv_hom_id := by
    funext s
    refine assocTypeSnd_ext_val _ _ ?_ ?_
    simp
    simp_all

-- ↑(sourceValue (homMk (mapOrderHom₁ (coCartesianLift f s.1).op)).op.unop s.2) =
-- ↑(sourceValue f.unop { val := ↑s.2, isLt := _ })
lemma mapOrderHom₁_map {X Y : (WithInitial SimplexCategory)ᵒᵖ}  (f : X ⟶ Y)
    (s : assocClassifier1.obj X) :
    (joinClassifying.map (joinClassifyEquivOpOp.functor.map (coCartesianLift f s.1)).1 s.2).val
    = (joinClassifying.map f (((assocIsoComponents X).hom s).1)).val := by
  simp
  have h2 := Nat.lt_succ.mp s.2.prop
  simp at h2
  rw [sourceValue_val_iff]
  apply And.intro
  · rw [Nat.lt_succ]
    simp
    refine sourceValue_monotone f.unop ?_
    rw [Fin.le_def]
    exact h2
  · intro j
    erw [toOrderHom_homMk]
    exact sourceValue_cond f.unop ⟨s.2.val, assocIsoComponents.proof_1 X s ⟩ (incl₁ j)



lemma mapOrderHom₂_map {X Y : (WithInitial SimplexCategory)ᵒᵖ}  (f : X ⟶ Y)
    (s : assocClassifier1.obj X) : (joinClassifying.map f s.1).val -
    (joinClassifying.map f (((assocIsoComponents X).hom s).1)).val
    = (joinClassifying.map (joinClassifyEquivOpOp.functor.map
    (coCartesianLift f ((assocIsoComponents X).hom s).1)).2 ((assocIsoComponents X).hom s).2).val
    := by
  let x := (joinClassifying.map f (((assocIsoComponents X).hom s).1))
  let y := (joinClassifying.map f s.1)
  have hx := Nat.lt_succ_iff.mp x.prop
  symm
  erw [sourceValue_val_iff]
  apply And.intro
  · simp
    rw [Nat.lt_succ_iff]
    exact (Nat.sub_le_sub_iff_right hx).mpr (Nat.lt_succ_iff.mp y.prop)
  · intro j
    rw [Fin.lt_def]
    simp only [assocClassifier1_obj, assocClassifierSnd_obj,
      joinClassifying_map, joinClassifyEquivOp_functor_obj, Opposite.unop_op, objClass_fst,
      joinLiftObj_fst, joinLiftObj_snd, joinClassifyEquivOp_functor_map, Quiver.Hom.unop_op,
      Fin.coe_castSucc]
    rw [toOrderHom_homMk, mapOrderHom₂_apply_val]
    change _ ↔ (toOrderHom f.unop (incl₂ j)).val - s.2.val < s.1.val - s.2.val
    by_cases hr : s.2.val < s.1.val
    · apply Iff.intro
      · intro hj
        have hs := Fin.lt_def.mp ((sourceValue_cond f.unop s.1 (incl₂ j)).mp
          (Nat.add_lt_of_lt_sub hj))
        omega
      · intro hj
        have hk : ↑((toOrderHom f.unop) (incl₂ j)) < s.1.val := by
          exact lt_of_tsub_lt_tsub_right hj
        have hs := Fin.lt_def.mp (((sourceValue_cond f.unop s.1 (incl₂ j)).mpr) hk)
        simp
        simp at hs
        exact Nat.lt_sub_of_add_lt hs
    · have hs1 := Nat.lt_succ.mp s.2.prop
      simp at hs1
      have hr2 : s.2.val = s.1.val := by
        omega
      have hr3 : ((assocIsoComponents X).hom s).1  = s.1 := by
        rw [Fin.eq_iff_veq]
        exact hr2
      rw [← hr2]
      simp only [incl₂, joinClassifying_obj, Equivalence.symm_functor, opOpEquivalence_inverse,
        assocClassifier1_obj, assocClassifierSnd_obj, joinClassifying_map, opOp_obj,
        Opposite.unop_op, joinLiftObj_snd, joinClassifyEquivOp_functor_obj, objClass_fst,
        joinLiftObj_fst, ge_iff_le, le_refl, tsub_eq_zero_of_le, not_lt_zero', iff_false, not_lt,
        tsub_le_iff_right]
      erw [← hr3]
      exact Nat.le_add_left ↑(sourceValue f.unop ((assocIsoComponents X).hom s).1) ↑j



@[simps!]
def assocIso : assocClassifier1 ≅ assocClassifierSnd :=
  NatIso.ofComponents assocIsoComponents (by
    intro X Y f
    funext s
    rw [types_comp_apply, types_comp_apply]
    apply assocTypeSnd_ext_val
    rw [Fin.eq_iff_veq]
    exact mapOrderHom₁_map f s
    simp [assocType1Map,assocType1Part, assocTypeSndMap, assocTypeSndPart]
    erw [mapOrderHom₁_map f s]
    exact mapOrderHom₂_map f s
  )

lemma assocEqIffJoinEq {X Y : (WithInitial SimplexCategory)ᵒᵖ} {f : X ⟶ Y}
    {t : assocClassifier1.obj X} {s : assocClassifier1.obj Y}
    (h : assocClassifier1.map f t = s) : joinClassifying.map f t.1 = s.1 := by
  subst h
  rfl


lemma assocEqIffSndJoinEq {X Y : (WithInitial SimplexCategory)ᵒᵖ} {f : X ⟶ Y}
    {t : assocClassifierSnd.obj X} {s : assocClassifierSnd.obj Y}
    (h : assocClassifierSnd.map f t = s) : joinClassifying.map f t.1 = s.1 := by
  subst h
  rfl

@[simps!]
def assoc1ToJoin : assocClassifier1.Elements ⥤ joinClassifying.Elements where
  obj X := ⟨X.1,X.2.1⟩
  map f := ⟨f.1, assocEqIffJoinEq f.2⟩

@[simps!]
def assocSndToJoin : assocClassifierSnd.Elements ⥤ joinClassifying.Elements where
  obj X := ⟨X.1,X.2.1⟩
  map f := ⟨f.1, assocEqIffSndJoinEq f.2⟩

lemma assocFst_cond_on_snd' {X Y : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y)
    {t : assocClassifier1.obj X} {s : assocClassifier1.obj Y}
    (h : assocClassifier1.map f t = s) (f' : assoc1ToJoin.obj ⟨X,t⟩ ⟶ assoc1ToJoin.obj ⟨Y,s⟩)
    (hf : f' = ⟨f, assocEqIffJoinEq h⟩):
    (joinClassifying.map ((homMk (mapOrderHom₁ f'.op))).op t.2).val
    = s.2.val:= by
  subst hf h
  rfl

lemma assocFst_cond_on_snd {X Y: assocClassifier1.Elements} (f : X ⟶ Y) :
    (joinClassifying.map ((homMk (mapOrderHom₁ ((assoc1ToJoin.map f)).op))).op X.2.2)
    = Y.2.2 := by
  rw [Fin.eq_iff_veq]
  refine assocFst_cond_on_snd' f.1 f.2 (assoc1ToJoin.map f) (by rfl )

lemma assocSnd_cond_on_snd' {X Y : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y)
    {t : assocClassifierSnd.obj X} {s : assocClassifierSnd.obj Y}
    (h : assocClassifierSnd.map f t = s) (f' : assocSndToJoin.obj ⟨X,t⟩ ⟶ assocSndToJoin.obj ⟨Y,s⟩)
    (hf : f' = ⟨f, assocEqIffSndJoinEq h⟩):
    (joinClassifying.map ((homMk (mapOrderHom₂ f'.op))).op t.2).val
    = s.2.val:= by
  subst hf h
  rfl

lemma assocSnd_cond_on_snd {X Y: assocClassifierSnd.Elements} (f : X ⟶ Y) :
    (joinClassifying.map ((homMk (mapOrderHom₂ ((assocSndToJoin.map f)).op))).op X.2.2)
    = Y.2.2 := by
  rw [Fin.eq_iff_veq]
  refine assocSnd_cond_on_snd' f.1 f.2 (assocSndToJoin.map f) (by rfl )

@[simps!]
def assoc1ToWithInitialWithInitial : assocClassifier1.Elements ⥤
    (joinClassifying.Elements) × (WithInitial SimplexCategory)ᵒᵖ where
  obj X :=
    let X' := (assoc1ToJoin ⋙ joinClassifyEquivOpOp.functor).obj X
    (⟨(CategoryTheory.Prod.fst _ _ ).obj X', X.2.2⟩, (CategoryTheory.Prod.snd _ _ ).obj X')
  map {X Y} f :=
    let f' := (assoc1ToJoin ⋙ joinClassifyEquivOpOp.functor).map f
    (⟨(CategoryTheory.Prod.fst _ _ ).map f',  assocFst_cond_on_snd f⟩,
    (CategoryTheory.Prod.snd _ _ ).map f')
  map_id X := by
    simp [homMk_id]
    apply And.intro
    · rfl
    · rfl
  map_comp {X Y Z} f g := by
    simp [homMk_comp]
    rfl

def assoc1Join : (joinClassifying.Elements) × (WithInitial SimplexCategory)ᵒᵖ ⥤
    joinClassifying.Elements :=
  (CategoryOfElements.π joinClassifying).prod (𝟭 (WithInitial SimplexCategory)ᵒᵖ)
  ⋙ joinClassifyEquivOpOp.inverse



@[simps!]
def assocSndToWithInitialWithInitial : assocClassifierSnd.Elements ⥤
    (WithInitial SimplexCategory)ᵒᵖ × (joinClassifying.Elements)  where
  obj X :=
    let X' := (assocSndToJoin ⋙ joinClassifyEquivOpOp.functor).obj X
    ((CategoryTheory.Prod.fst _ _ ).obj X', ⟨(CategoryTheory.Prod.snd _ _ ).obj X', X.2.2⟩ )
  map f :=
    let f' := (assocSndToJoin ⋙ joinClassifyEquivOpOp.functor).map f
    ((CategoryTheory.Prod.fst _ _ ).map f', ⟨(CategoryTheory.Prod.snd _ _ ).map f',
     assocSnd_cond_on_snd f⟩)
  map_id X := by
    simp [homMk_id]
    apply And.intro
    · rfl
    · rfl
  map_comp {X Y Z} f g := by
    simp [homMk_comp]
    rfl

@[simps!]
def assocSndTo3WithInitial : assocClassifierSnd.Elements ⥤
    (WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ
    × (WithInitial SimplexCategory)ᵒᵖ  :=
  assocSndToWithInitialWithInitial ⋙ (𝟭 ((WithInitial SimplexCategory)ᵒᵖ)).prod
  joinClassifyEquivOpOp.functor

@[simps!]
def assocFstTo3WithInitial : assocClassifier1.Elements ⥤
    (WithInitial SimplexCategory)ᵒᵖ × (WithInitial SimplexCategory)ᵒᵖ
    × (WithInitial SimplexCategory)ᵒᵖ  :=
  assoc1ToWithInitialWithInitial ⋙ (joinClassifyEquivOpOp.functor.prod
   (𝟭 ((WithInitial SimplexCategory)ᵒᵖ))) ⋙ (prod.associativity _ _ _).functor

@[simp]
lemma assocFstTo3WithInitial_fst_apply {X Y : assocClassifier1.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocFstTo3WithInitial.obj Y).1.unop)) :
    (toOrderHom (assocFstTo3WithInitial.map f).1.1 a).val =
    ((toOrderHom f.1.1) ⟨a.val , by sorry⟩).val := by
  change (toOrderHom (homMk _) a).val = _
  rw [toOrderHom_homMk]
  erw [mapOrderHom₁_apply_val]
  simp
  erw [Quiver.Hom.op_unop]
  erw [toOrderHom_homMk, mapOrderHom₁_apply_val]

@[simp]
lemma assocSndTo3WithInitial_fst_apply {X Y : assocClassifierSnd.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocSndTo3WithInitial.obj Y).1.unop)) :
    (toOrderHom (assocSndTo3WithInitial.map f).1.1 a).val =
    ((toOrderHom f.1.1) ⟨a.val , by sorry⟩).val := by
  change (toOrderHom (homMk _) a).val = _
  rw [toOrderHom_homMk]
  erw [mapOrderHom₁_apply_val]

@[simp]
lemma assocFstTo3WithInitial_snd_apply {X Y : assocClassifier1.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocFstTo3WithInitial.obj Y).2.1.unop)) :
    (toOrderHom (assocFstTo3WithInitial.map f).2.1.1 a).val =
    ((toOrderHom f.1.1) ⟨a.val + Y.2.2.val , by sorry⟩).val - X.2.2.val := by
  change (toOrderHom (homMk _) a).val = _
  rw [toOrderHom_homMk]
  erw [mapOrderHom₂_apply_val]
  simp [assoc1ToJoin]
  erw [Quiver.Hom.op_unop]
  erw [toOrderHom_homMk, mapOrderHom₁_apply_val]
  simp [assoc1ToWithInitialWithInitial]

@[simp]
lemma assocSndTo3WithInitial_snd_apply {X Y : assocClassifierSnd.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocSndTo3WithInitial.obj Y).2.1.unop)) :
    (toOrderHom (assocSndTo3WithInitial.map f).2.1.1 a).val =
    ((toOrderHom f.1.1) ⟨a.val + Y.2.1.val , by sorry⟩).val - X.2.1.val := by
  change (toOrderHom (homMk _) a).val = _
  rw [toOrderHom_homMk]
  erw [mapOrderHom₁_apply_val]
  simp [assocSndToJoin]
  erw [Quiver.Hom.op_unop]
  erw [toOrderHom_homMk, mapOrderHom₂_apply_val]
  simp [assoc1ToWithInitialWithInitial]
  rfl

@[simp]
lemma assocFstTo3WithInitial_thd_apply {X Y : assocClassifier1.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocFstTo3WithInitial.obj Y).2.2.unop)) :
    (toOrderHom (assocFstTo3WithInitial.map f).2.2.1 a).val =
    ((toOrderHom f.1.1) ⟨a.val + Y.2.1.val , by sorry⟩).val - X.2.1.val := by
  change (toOrderHom (homMk _) a).val = _
  rw [toOrderHom_homMk]
  erw [mapOrderHom₂_apply_val]
  simp [assoc1ToJoin]
  erw [Quiver.Hom.op_unop]
  rfl

@[simp]
lemma assocSndTo3WithInitial_thd_apply {X Y : assocClassifierSnd.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocSndTo3WithInitial.obj Y).2.2.unop)) :
    (toOrderHom (assocSndTo3WithInitial.map f).2.2.1 a).val =
    ((toOrderHom f.1.1) ⟨a.val + Y.2.2.val + Y.2.1.val , by sorry⟩).val - X.2.1.val- X.2.2.val := by
  change (toOrderHom (homMk _) a).val = _
  rw [toOrderHom_homMk]
  erw [mapOrderHom₂_apply_val]
  simp [assocSndToJoin]
  erw [Quiver.Hom.op_unop]
  erw [toOrderHom_homMk, mapOrderHom₂_apply_val]
  simp [assocSndToWithInitialWithInitial]
  rfl

@[simps!]
def assocIsoWithInitialComponents  (X : assocClassifier1.Elements) :
    assocFstTo3WithInitial.obj X ≅ ((CategoryOfElements.mapIso assocIso).functor ⋙
    assocSndTo3WithInitial).obj X :=
  Iso.prod (Iso.op (
  lenIso (rfl))) (Iso.prod (Iso.op (lenIso ( by simp ))) (Iso.op (lenIso (by
   simp
   sorry
  ))))

lemma nat_assocIsoWithInitial_fst {X Y : assocClassifier1.Elements} (f : X ⟶ Y) :
    (assocFstTo3WithInitial.map f ≫ (assocIsoWithInitialComponents Y).hom).1 =
      ((assocIsoWithInitialComponents X).hom ≫
      ((CategoryOfElements.mapIso assocIso).functor ⋙ assocSndTo3WithInitial).map f).1
       := by
  change (((assocFstTo3WithInitial.map f).1 ≫ (assocIsoWithInitialComponents Y).hom.1)).unop.op
    =  ((assocIsoWithInitialComponents X).hom.1 ≫
        (((CategoryOfElements.mapIso assocIso).functor ⋙ assocSndTo3WithInitial).map f).1).unop.op
  apply congrArg
  apply hom_eq_if_toOrderHom_eq
  ext a
  erw [toOrderHom_comp, toOrderHom_comp]
  erw [assocFstTo3WithInitial_fst_apply]
  simp only [assocClassifier1_obj, assocClassifier1_map, Functor.comp_obj, prod_Hom,
    assocIsoWithInitialComponents_hom, Quiver.Hom.unop_op, Functor.comp_map, OrderHom.comp_coe,
    Function.comp_apply]
  erw [toOrderHom_of_lenIso_hom, toOrderHom_of_lenIso_hom]
  simp only [assocClassifier1_obj, Fin.castIso_refl, OrderHomClass.coe_coe,
    Fin.coe_orderIso_apply]
  erw [assocSndTo3WithInitial_fst_apply]
  rfl

lemma nat_assocIsoWithInitial_snd {X Y : assocClassifier1.Elements} (f : X ⟶ Y) :
    (assocFstTo3WithInitial.map f ≫ (assocIsoWithInitialComponents Y).hom).2.1 =
      ((assocIsoWithInitialComponents X).hom ≫
      ((CategoryOfElements.mapIso assocIso).functor ⋙ assocSndTo3WithInitial).map f).2.1
       := by
  change (((assocFstTo3WithInitial.map f).2.1 ≫ (assocIsoWithInitialComponents Y).hom.2.1)).unop.op
    =  ((assocIsoWithInitialComponents X).hom.2.1 ≫
        (((CategoryOfElements.mapIso assocIso).functor ⋙ assocSndTo3WithInitial).map f).2.1).unop.op
  apply congrArg
  apply hom_eq_if_toOrderHom_eq
  ext a
  erw [toOrderHom_comp, toOrderHom_comp]
  erw [assocFstTo3WithInitial_snd_apply]
  simp only [assocClassifier1_obj, assocClassifier1_map, Functor.comp_obj, prod_Hom,
    assocIsoWithInitialComponents_hom, Quiver.Hom.unop_op, joinClassifyEquivOp_functor_obj,
    Opposite.unop_op, objClass_fst, joinLiftObj_fst, joinLiftObj_snd, Functor.comp_map,
    OrderHom.comp_coe, Function.comp_apply]
  erw [toOrderHom_of_lenIso_hom, toOrderHom_of_lenIso_hom]
  simp only [assocClassifier1_obj, OrderHomClass.coe_coe, Fin.castIso_apply, Fin.coe_cast]
  erw [assocSndTo3WithInitial_snd_apply]
  rfl

lemma nat_assocIsoWithInitial_thd {X Y : assocClassifier1.Elements} (f : X ⟶ Y) :
    (assocFstTo3WithInitial.map f ≫ (assocIsoWithInitialComponents Y).hom).2.2 =
      ((assocIsoWithInitialComponents X).hom ≫
      ((CategoryOfElements.mapIso assocIso).functor ⋙ assocSndTo3WithInitial).map f).2.2
       := by
  change (((assocFstTo3WithInitial.map f).2.2 ≫ (assocIsoWithInitialComponents Y).hom.2.2)).unop.op
    =  ((assocIsoWithInitialComponents X).hom.2.2 ≫
        (((CategoryOfElements.mapIso assocIso).functor ⋙ assocSndTo3WithInitial).map f).2.2).unop.op
  apply congrArg
  apply hom_eq_if_toOrderHom_eq
  ext a
  erw [toOrderHom_comp, toOrderHom_comp]
  simp only [Functor.comp_obj, prod_Hom, assocIsoWithInitialComponents_hom, Quiver.Hom.unop_op,
    OrderHom.comp_coe, Function.comp_apply, Functor.comp_map]
  erw [toOrderHom_of_lenIso_hom, toOrderHom_of_lenIso_hom]
  erw [assocFstTo3WithInitial_thd_apply, assocSndTo3WithInitial_thd_apply]
  simp
  sorry

def assocIsoWithInitial : assocFstTo3WithInitial ≅ ((CategoryOfElements.mapIso assocIso).functor ⋙
    assocSndTo3WithInitial) := NatIso.ofComponents assocIsoWithInitialComponents (by
  intro X Y f
  simp only [prod_Hom]
  ext
  · exact nat_assocIsoWithInitial_fst f
  · simp only [prod_Hom]
    ext
    · exact nat_assocIsoWithInitial_snd f
    · exact nat_assocIsoWithInitial_thd f)





end joinAssoc

namespace Split



/-- Splits an object `X` into two parts based on an element of `Fin (Nat.succ (len X))`. -/
def obj (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))):
    WithInitial SimplexCategory × WithInitial SimplexCategory := (mk i, mk i.rev)



/-- The fiber above an object of the join functor. -/
def fiberObj (X : WithInitial SimplexCategory) :
    Discrete (Fin (Nat.succ (len X))) ⥤
    WithInitial SimplexCategory × WithInitial SimplexCategory :=
  Discrete.functor (obj X)

lemma len_obj₁ (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    len (obj X i).1 = i.val := by
  simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk]

lemma len_obj₂ (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    len (obj X i).2 = (len X) - i.val := by
  simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk]

/-- An isomorphism between `obj X i` and `obj X j` when `i=j`. -/
def indexEqToIso {X : WithInitial SimplexCategory} {i j : Fin (Nat.succ (len X))}
    (h : i = j) : obj X i ≅ obj X j where
  hom := ((lenIso (by rw [h])).hom, (lenIso (by rw [h])).hom)
  inv := ((lenIso (by rw [h])).inv, (lenIso (by rw [h])).inv)

lemma indexEqToIso_refl {X : WithInitial SimplexCategory} {i  : Fin (Nat.succ (len X))} :
    indexEqToIso (by rfl : i = i) = Iso.refl (obj X i) := by
  ext
  simp [indexEqToIso, lenIso_refl]
  rfl

lemma toOrderHom_indexEqToIso_inv_fst_apply {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) (a : Fin (len (obj X j).1)) :
    (toOrderHom (indexEqToIso h).inv.1) a = ⟨a.val, by subst h; exact a.prop⟩ := by
  simp [indexEqToIso]
  subst h
  rw [lenIso_refl]
  simp only [Iso.refl_inv, toOrderHom_id, OrderHom.id_coe, id_eq, Fin.eta]

lemma toOrderHom_indexEqToIso_inv_snd_apply {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) (a : Fin (len (obj X j).2)) :
    (toOrderHom (indexEqToIso h).inv.2) a = ⟨a.val, by subst h; exact a.prop⟩ := by
  simp [indexEqToIso]
  subst h
  rw [lenIso_refl]
  simp only [Iso.refl_inv, toOrderHom_id, OrderHom.id_coe, id_eq, Fin.eta]

lemma indexEqToIso_inv_comp_symm_inv {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) :
    (indexEqToIso h).inv ≫ (indexEqToIso h.symm).inv = 𝟙 _ := by
  rw [prod_id]
  simp [indexEqToIso]
  subst h
  rw [lenIso_refl, lenIso_refl]
  simp
  rw [Category.id_comp (𝟙 (obj X i).1), Category.id_comp (𝟙 (obj X i).2)]
  simp only [and_self]


lemma incl₁_cond {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (len (obj Y p).1)) : a.val < len Y := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

lemma inclSucc₁_cond {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (Nat.succ (len (obj Y p).1))) : a.val < Nat.succ (len Y) := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (obj X i).1)` into `Fin (len X)`. -/
def incl₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len (obj X i).1)) : Fin (len X) := ⟨a.val, incl₁_cond a⟩

/-- The inclusion of `Fin (Nat.succ (len (obj X i).1))` into `Fin (Nat.succ (len X))`. -/
@[simp]
def inclSucc₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (Nat.succ (len (obj X i).1))) : Fin (Nat.succ (len X)) := ⟨a.val, inclSucc₁_cond a⟩

/-- The preimage of an object in `Fin (len X)` under `incl₁` when it exists. -/
def preimageIncl₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : a.val < len (obj X i).1) : Fin (len (obj X i).1) := ⟨a.val, ha⟩
@[simp]
def preimageInclSucc₁  {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (Nat.succ (len X))) (ha : a.val < Nat.succ (len (obj X i).1) ) :
    Fin (Nat.succ (len (obj X i).1)) := ⟨a.val, ha⟩


lemma incl₂_cond  {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (len (obj Y p).2)) :
    a.val + p.val < len Y := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (obj X i).2)` into `Fin X`. -/
@[simp]
def incl₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len (obj X i).2)) : Fin (len X) := ⟨a.val + i.val, incl₂_cond a⟩

lemma inclSucc₂_cond {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (Nat.succ (len (obj Y p).2))) : a.val + p.val < Nat.succ (len Y) := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (Nat.succ (len (obj X i).1))` into `Fin (Nat.succ (len X))`. -/
@[simp]
def inclSucc₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (Nat.succ (len (obj X i).2))) : Fin (Nat.succ (len X)) :=
  ⟨a.val + i.val, inclSucc₂_cond a⟩

lemma preimageIncl₂_cond  {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : len (obj X i).1 ≤ a.val) :
    a.val - (len (obj X i).1) < len (obj X i).2 := by
  simp_all [obj, len_mk]
  refine lt_tsub_of_add_lt_right ?_
  rw [tsub_add_cancel_iff_le.mpr ha]
  omega

lemma preimageInclSucc₂_cond  {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (Nat.succ (len X))) (ha : len (obj X i).1 ≤ a.val) :
    a.val - (len (obj X i).1) < Nat.succ (len (obj X i).2) := by
  simp_all [obj, len_mk]
  rw [← Nat.succ_sub i.is_le]
  refine lt_tsub_of_add_lt_right ?_
  rw [tsub_add_cancel_iff_le.mpr ha]
  omega

/-- The preimage of an object in `Fin (len X)` under `incl₂` when it exists. -/
def preimageIncl₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : len (obj X i).1 ≤ a.val) :
    Fin (len (obj X i).2) := ⟨a.val - len (obj X i).1 , preimageIncl₂_cond a ha⟩

@[simp]
def preimageInclSucc₂  {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (Nat.succ (len X))) (ha : len (obj X i).1 ≤ a.val) :
    Fin (Nat.succ (len (obj X i).2)) := ⟨a.val - len (obj X i).1 , preimageInclSucc₂_cond a ha⟩

@[simp]
def preimageInclSucc₂' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) : Fin (Nat.succ (len (obj X (inclSucc₁ p)).2)) :=
  Split.preimageInclSucc₂ i (
    le_of_eq_of_le (Split.len_obj₁ X (inclSucc₁ p))
        (le_of_eq_of_le' (Split.len_obj₁ X i) (Nat.lt_succ.mp p.prop)))

lemma preimageInclSucc₂'_inclSucc₂ {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) : inclSucc₂ (preimageInclSucc₂' i p) = i := by
  simp only [inclSucc₂, inclSucc₁, preimageInclSucc₂', preimageInclSucc₂, len_obj₁, Fin.eq_iff_veq]
  refine tsub_add_cancel_of_le ?_
  exact le_of_eq_of_le' (Split.len_obj₁ X i) (Nat.lt_succ.mp p.prop)


@[simp]
def preimageInclSucc₁' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) : Fin (Nat.succ (len (obj X (inclSucc₂ p)).1)) :=
  Split.preimageInclSucc₁ i ( by
    apply Nat.lt_succ.mpr
    apply le_of_eq_of_le' (Split.len_obj₁ X (inclSucc₂ p)).symm
    simp only [inclSucc₂, le_add_iff_nonneg_left, zero_le]
   )

lemma preimageInclSucc₁'_inclSucc₁ {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) : inclSucc₁ (preimageInclSucc₁' i p) = i := by
  simp only [inclSucc₂, inclSucc₁, preimageInclSucc₁', preimageInclSucc₁, len_obj₁, Fin.eq_iff_veq]

/--
For (p : Fin (Nat.succ (len (obj X i).1))), (i : Fin (Nat.succ (len X))) we have an isomorphism
between the objects
-/
inductive assocFiberType1 (X : WithInitial SimplexCategory)
  | as : (i : Fin (Nat.succ (len X))) → (p : Fin (Nat.succ (len (obj X i).1))) → assocFiberType1 X

lemma assocFiberType1_ext {X : WithInitial SimplexCategory} (s t : assocFiberType1 X)
    (h1 : s.1 = t.1) (h2 : s.2.val = t.2.val) : s = t := by
  match s with
  |  assocFiberType1.as s1 s2 =>
  simp_all
  subst h1
  congr
  rw [Fin.eq_iff_veq]
  exact h2

inductive assocFiberType2 (X : WithInitial SimplexCategory)
  | as : (i : Fin (Nat.succ (len X))) → (p : Fin (Nat.succ (len (obj X i).2))) → assocFiberType2 X

lemma assocFiberType2_ext {X : WithInitial SimplexCategory} (s t : assocFiberType2 X)
    (h1 : s.1 = t.1) (h2 : s.2.val = t.2.val) : s = t := by
  match s with
  |  assocFiberType2.as s1 s2 =>
  simp_all
  subst h1
  congr
  rw [Fin.eq_iff_veq]
  exact h2

def assocFiberEquiv (X : WithInitial SimplexCategory) :
    assocFiberType1 X ≃ assocFiberType2 X where
  toFun s := assocFiberType2.as (inclSucc₁ s.2) (preimageInclSucc₂' s.1 s.2)
  invFun s := assocFiberType1.as (inclSucc₂ s.2) (preimageInclSucc₁' s.1 s.2)
  left_inv := by
    intro s
    simp
    apply assocFiberType1_ext
    simp only [inclSucc₂, inclSucc₁, preimageInclSucc₂', preimageInclSucc₂, len_obj₁,
      Fin.eq_iff_veq]
    exact tsub_add_cancel_of_le (le_of_eq_of_le' (len_obj₁ X s.1) (Nat.lt_succ.mp s.2.prop))
    rfl
  right_inv := by
    intro s
    simp
    apply assocFiberType2_ext
    simp only [inclSucc₂, inclSucc₁, preimageInclSucc₁', preimageInclSucc₁, len_obj₁,
      Fin.eq_iff_veq]
    simp only [inclSucc₂, preimageInclSucc₁', preimageInclSucc₁, inclSucc₁, Fin.eta,
      preimageInclSucc₂', preimageInclSucc₂, len_obj₁, add_tsub_cancel_right]

def assocFiberCatEquiv (X : WithInitial SimplexCategory) :
    Discrete (assocFiberType1 X) ≌  Discrete (assocFiberType2 X) :=
  Discrete.equivalence (assocFiberEquiv X)

/-- The fiber of the functor (join × 𝟭) ⋙ join. -/
def assocFiber1 (X : WithInitial SimplexCategory) :
    Discrete (assocFiberType1 X) ⥤
    WithInitial SimplexCategory × WithInitial SimplexCategory × WithInitial SimplexCategory :=
  Discrete.functor (fun s =>
    ((obj (obj X s.1).1 s.2).1, (obj (obj X s.1).1 s.2).2, (obj X s.1).2))

/-- The fiber of the functor (𝟭 × join) ⋙ join. -/
def assocFiber2 (X : WithInitial SimplexCategory) :
    Discrete (assocFiberType2 X) ⥤
    WithInitial SimplexCategory × WithInitial SimplexCategory × WithInitial SimplexCategory :=
  Discrete.functor (fun s =>
    ((obj X s.1).1, (obj (obj X s.1).2 s.2).1, (obj (obj X s.1).2 s.2).2))



def swap₁ {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) :
    (Split.obj (Split.obj X i).1 p).2  ≅
    (Split.obj (Split.obj X  (inclSucc₁ p)).2 (preimageInclSucc₂' i p)).1 :=
  lenIso (by
    simp only [len_obj₂, len_obj₁, inclSucc₁, preimageInclSucc₂', preimageInclSucc₂]
    )

def swap₁' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) :
    (Split.obj (Split.obj X i).2 p).1  ≅
    (Split.obj (Split.obj X (inclSucc₂ p)).1 (preimageInclSucc₁' i p)).2 :=
  lenIso (by
    simp only [len_obj₂, len_obj₁, inclSucc₁, preimageInclSucc₁', preimageInclSucc₁, inclSucc₂]
    exact eq_tsub_of_add_eq rfl
  )

def swap₂ {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) :
    (Split.obj X i).2 ≅ (Split.obj (Split.obj X  (inclSucc₁ p)).2 (preimageInclSucc₂' i p)).2 :=
  lenIso (by
    simp only [len_obj₂, len_obj₁, inclSucc₁, preimageInclSucc₂', preimageInclSucc₂]
    rw [Nat.sub_sub, add_comm p.val _, tsub_add_cancel_iff_le.mpr]
    exact le_of_eq_of_le' (Split.len_obj₁ X i) (Nat.lt_succ.mp p.prop)
  )

def swap₂' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) :
    (Split.obj (Split.obj X i).2 p).2  ≅ (Split.obj X (inclSucc₂ p)).2  :=
  lenIso (by
    simp only [len_obj₂, len_obj₁, inclSucc₁, preimageInclSucc₁', preimageInclSucc₁, inclSucc₂]
    exact (tsub_add_eq_tsub_tsub_swap (len X) ↑p ↑i).symm
  )

def swap₃ {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) : (obj (obj X i).1 p).1 ≅ (obj X (inclSucc₁ p)).1 :=
  lenIso (by rfl)

def swap₃' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) :
    (Split.obj X i).1 ≅ (Split.obj (Split.obj X (inclSucc₂ p)).1 (preimageInclSucc₁' i p)).1 :=
  lenIso (by
    simp only [len_obj₂, len_obj₁, inclSucc₁, preimageInclSucc₁', preimageInclSucc₁]
  )

lemma  swap₁_swap₁' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) :
    (swap₁ i p) ≪≫  (swap₁' (Split.inclSucc₁ p) (Split.preimageInclSucc₂' i p))
    = lenIso (by
    rw [len_obj₂, len_obj₂]
    simp [len_obj₁, preimageInclSucc₂'_inclSucc₂]

    ) := by
  simp [swap₁, swap₁']
  exact lenIso_comp_trans _ _

lemma swap₁'_swap₁  {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) :
    (swap₁' i p) ≪≫  (swap₁ (Split.inclSucc₂ p) (Split.preimageInclSucc₁' i p)) =
    lenIso (by
     simp [len_obj₂, inclSucc₁, preimageInclSucc₁', preimageInclSucc₂',  preimageInclSucc₁,
       preimageInclSucc₂, len_obj₁, inclSucc₂]
    ) := by
  simp [swap₁', swap₁]
  exact lenIso_comp_trans _ _


lemma  swap₂_swap₂' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) :
    (swap₂ i p) ≪≫  (swap₂' (Split.inclSucc₁ p) (Split.preimageInclSucc₂' i p))
    = lenIso (by
    rw [len_obj₂ X i, len_obj₂ X ((inclSucc₂ (preimageInclSucc₂' i p))),
    preimageInclSucc₂'_inclSucc₂ i p]
    ) := by
  simp [swap₂, swap₂']
  exact lenIso_comp_trans _ _

lemma swap₂'_swap₂  {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) :
    (swap₂' i p) ≪≫  (swap₂ (Split.inclSucc₂ p) (Split.preimageInclSucc₁' i p)) =
    lenIso (by
     simp [len_obj₂, inclSucc₁, preimageInclSucc₁', preimageInclSucc₂',  preimageInclSucc₁,
       preimageInclSucc₂, len_obj₁, inclSucc₂]
    ) := by
  simp [swap₂', swap₂]
  exact lenIso_comp_trans _ _

lemma  swap₃_swap₃' {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).1))) :
    (swap₃ i p) ≪≫  (swap₃' (Split.inclSucc₁ p) (Split.preimageInclSucc₂' i p))
    = Iso.refl (obj (obj X i).1 p).1 := by
  simp [swap₃, swap₃']
  exact lenIso_comp_symm_refl _

lemma swap₃'_swap₃  {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X)))
    (p : Fin (Nat.succ (len (obj X i).2))) :
    (swap₃' i p) ≪≫  (swap₃ (Split.inclSucc₂ p) (Split.preimageInclSucc₁' i p)) =
    Iso.refl (obj X i).1 := by
  simp [swap₃', swap₃]
  exact lenIso_comp_symm_refl _

lemma join_split_len (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    len X = len (join.obj (Split.obj X i))  := by
  simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_of_join, len_mk]
  omega

/-- An isomorphism between an object and the join of a split of that object. -/
def joinSplitIso (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    X ≅ join.obj (obj X i) := lenIso (join_split_len X i)


lemma toOrderHom_apply_on_lt_sourceValue {X Y : WithInitial SimplexCategory} {f : X ⟶ Y}
    {i : Fin (Nat.succ (len Y))} {a : Fin (len X)} (ha : a.val < len (obj X (sourceValue f i)).1) :
    ((toOrderHom f) a).val < len (obj Y i).1 :=
  let ha' :=  lt_of_eq_of_lt' (len_obj₁ X (sourceValue f i)) ha
  lt_of_eq_of_lt' (len_obj₁ Y i).symm (Fin.lt_def.mp ((sourceValue_cond f i a).mp ha'))

lemma toOrderHom_apply_on_sourceValue_le {X Y : WithInitial SimplexCategory} {f : X ⟶ Y}
    {i : Fin (Nat.succ (len Y))}  {a : Fin (len X)}
    (ha : len (obj X (sourceValue f i)).1 ≤ a.val) :
    len (obj Y i).1 ≤ ((toOrderHom f) a).val  :=
  let ha' := le_of_eq_of_le (len_obj₁ X (sourceValue f i)).symm ha
  le_of_eq_of_le (len_obj₁ Y i)
    (Fin.le_def.mp (not_lt.mp ((sourceValue_cond f i a).mpr.mt (not_lt.mpr ha'))))

/-- Given a `X` and `Y` in `WithInitial SimplexCategory` and an `i` in `Fin (Nat.succ (len X))`,
the type of split versions of homomorphisms from `Y` to `X`. -/
inductive hom (Y X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))  where
  | split : (p : Fin (Nat.succ (len Y))) → (obj Y p ⟶ obj X i) → hom Y X i

lemma hom_ext (Y X: WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    (s t : hom Y X i) (h1 : s.1 = t.1) (h2 : (indexEqToIso h1).inv ≫ s.2 = t.2) :
    s = t := by
  match s, t with
  | hom.split ps s, hom.split pt t =>
    simp at h1
    subst h1
    congr
    rw [indexEqToIso_refl] at h2
    simp  at h2
    exact h2

lemma sourceValue_of_joinSplitIso_comp_join_comp_joinSplitIso {X Y : WithInitial SimplexCategory}
    (i : Fin (Nat.succ (len X))) (p : Fin (Nat.succ (len Y))) (f : (obj Y p) ⟶ (obj X i)) :
    sourceValue ((joinSplitIso Y p).hom ≫ join.toPrefunctor.map f ≫ (joinSplitIso X i).inv) i
    = p := by
  have ht := (Fin.eq_iff_veq _ _).mp (sourceValue_of_join f)
  simp [obj, len_mk] at ht
  rw [← sourceValue_of_comp, ← sourceValue_of_comp,
    sourceValue_of_iso_hom, sourceValue_of_iso_inv, Fin.eq_iff_veq, ← ht]

/-- Given a morphism `f : X ⟶ Y`, and an element of `Fin (Nat.succ (len Y))`, the corresponding
morphism between `obj X (sourceValue f i) ` and `obj Y i`. -/
def map {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    obj X (sourceValue f i) ⟶ obj Y i:=
  (homMk {
    toFun := fun a =>
      preimageIncl₁ (toOrderHom f (incl₁ a)) (toOrderHom_apply_on_lt_sourceValue (a.prop))
    monotone' := by
      intro a b h
      exact (toOrderHom f).monotone' h
  },
  homMk {
    toFun := fun a => preimageIncl₂ (toOrderHom f (incl₂ a)) (by
      refine toOrderHom_apply_on_sourceValue_le ?_
      simp [obj, len_mk, incl₂]
    )
    monotone' := by
      intro a b h
      simp [preimageIncl₂]
      rw [tsub_add_cancel_iff_le.mpr]
      apply (toOrderHom f).monotone'
      simp [incl₂]
      exact h
      apply toOrderHom_apply_on_sourceValue_le
      simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk, incl₂, le_add_iff_nonneg_left,
        zero_le]
  })



def fiberMap {Y X : WithInitial SimplexCategory}  (f : Y ⟶ X) (i : Fin (Nat.succ (len X))) :
    Fin 2  ⥤  WithInitial SimplexCategory × WithInitial SimplexCategory  where
  obj i' :=
    match i' with
    | ⟨0, _⟩ => (fiberObj Y).obj (Discrete.mk (sourceValue f i))
    | ⟨1, _⟩ => (fiberObj X).obj (Discrete.mk i)
  map {i' j'} t :=
    match i', j', t with
    | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
    | ⟨0, _⟩, ⟨1, _⟩, _ => map f i
    | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _
  map_id i := by
    match i with
    | 0 => rfl
    | 1 => rfl
  map_comp {i' j k} a b := by
    match i', j, k, a, b with
    | ⟨0, _⟩ , ⟨0, _⟩, ⟨0, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, Category.comp_id]
    | ⟨0, _⟩ , ⟨0, _⟩, ⟨1, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, Category.id_comp]
    | ⟨0, _⟩ , ⟨1, _⟩, ⟨1, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, Category.comp_id]
    | ⟨1, _⟩ , ⟨1, _⟩, ⟨1, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, Category.comp_id]

lemma map_lenIso_inv_fst {X Y : WithInitial SimplexCategory} (f : X ≅ Y)
    (i : Fin (Nat.succ (len X))) :
    (map f.inv i).1 = (lenIso (
    (Eq.trans (len_obj₁ Y (sourceValue f.inv i)) (Eq.trans ((Fin.eq_iff_veq _ _).mp
    (sourceValue_of_iso_inv f i)) (len_obj₁ X i).symm)).symm :
    len (obj X i).1 = len (obj Y (sourceValue f.inv i)).1 )).inv  := by
  simp [map, lenIso, isoOfOrderIso, preimageIncl₁]
  apply congrArg
  apply OrderHom.ext
  funext a
  rw [Fin.eq_iff_veq]
  simp
  rw [toOrderHomIso_apply_inv f _]
  rfl

lemma map_lenIso_inv_snd {X Y : WithInitial SimplexCategory} (f : X ≅ Y)
    (i : Fin (Nat.succ (len X))) :
    (map f.inv i).2 = (lenIso ( by
    rw [len_obj₂, len_obj₂, sourceValue_of_iso_inv]
    simp only [len_iso f]
    : len (obj X i).2 = len (obj Y (sourceValue f.inv i)).2 )).inv  := by
  simp [map, lenIso, isoOfOrderIso, preimageIncl₁]
  apply congrArg
  apply OrderHom.ext
  funext a
  rw [Fin.eq_iff_veq]
  simp [preimageIncl₂, incl₂]
  rw [toOrderHomIso_apply_inv f _]
  simp [sourceValue_of_iso_inv f, len_obj₁]

lemma map_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    (indexEqToIso (sourceValue_of_id i)).inv ≫ map (𝟙 X) i = 𝟙 (obj X i) := by
  simp [map, indexEqToIso, lenIso, isoOfOrderIso]
  rw [prod_id, Prod.mk.injEq]
  rw [← homMk_comp, ← homMk_comp, ← @homMk_id (obj X i).1, ← @homMk_id (obj X i).2]
  apply And.intro
  rfl
  match X with
  | star =>
    simp_all only [obj, len_mk, Fin.val_rev, Fin.coe_fin_one, add_zero, Fin.eta, tsub_zero,
      preimageIncl₂]
    rfl
  | of x =>
    apply congrArg
    apply OrderHom.ext
    funext a
    rw [Fin.eq_iff_veq]
    simp only [obj, Fin.val_rev, preimageIncl₂, Nat.succ_sub_succ_eq_sub, len_mk, OrderHom.comp_coe,
      Function.comp_apply, OrderHom.id_coe, id_eq]
    change a.val + (sourceValue (𝟙 (of x)) i).val -i = a.val
    rw [sourceValue_of_id i]
    exact Nat.add_sub_cancel ↑a ↑i

lemma map_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z)))  : map (f ≫ g) i
    =  (indexEqToIso (sourceValue_of_comp f g i)).inv ≫ map f (sourceValue g i) ≫ map g i := by
  match X, Y, Z, f, g with
  | star, _, _, f, g => rfl
  | of x, of y, of z, f, g =>
    simp [map, indexEqToIso, lenIso, isoOfOrderIso, ← homMk_comp]
    apply And.intro
    all_goals apply congrArg
    rfl
    apply OrderHom.ext
    funext a
    simp only [obj, Fin.val_rev, preimageIncl₂, toOrderHom_comp, incl₂, OrderHom.comp_coe,
      Function.comp_apply, Nat.succ_sub_succ_eq_sub, len_mk, (sourceValue_of_comp f g i),
      Fin.eq_iff_veq]
    erw [OrderHom.coe_mk]
    simp only [OrderHom.coe_mk, OrderHom.comp_coe, Function.comp_apply]
    change _ = ((toOrderHom g) ⟨((toOrderHom f) ⟨a.val + (sourceValue (f ≫ g) i).val, _⟩).val
      - (sourceValue g i).val + (sourceValue g i).val, _⟩)  - i.val
    apply congrFun
    repeat apply congrArg
    simp [Fin.eq_iff_veq, ← sourceValue_of_comp f g i]
    rw [tsub_add_cancel_of_le]
    apply (not_lt.mp ((sourceValue_cond _ _ _).mpr.mt (not_lt.mpr _)))
    simp only [Fin.le_def, Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le]

def fiberComp {Z Y X : WithInitial SimplexCategory} (f : Z ⟶ Y) (g : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) :
    Fin 3  ⥤  WithInitial SimplexCategory × WithInitial SimplexCategory where
  obj k :=
    match k with
    | ⟨0, _⟩ => (fiberObj Z).obj (Discrete.mk (sourceValue (f ≫ g) i))
    | ⟨1, _⟩ => (fiberObj Y).obj (Discrete.mk (sourceValue g i))
    | ⟨2, _⟩ => (fiberObj X).obj (Discrete.mk i)
  map {k j} a :=
    match k, j, a with
    | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
    | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _
    | ⟨2, _⟩, ⟨2, _⟩, _ => 𝟙 _
    | ⟨0, _⟩, ⟨1, _⟩, _ => (indexEqToIso (sourceValue_of_comp f g i)).inv ≫ map f (sourceValue g i)
    | ⟨0, _⟩, ⟨2, _⟩, _ => map (f ≫ g) i
    | ⟨1, _⟩, ⟨2, _⟩, _ => map g i
  map_id k := by
    match k with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  map_comp {k j l} a b:= by
    match k, j, l, a, b with
    | ⟨0, _⟩, ⟨0, _⟩, ⟨0, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, Category.comp_id]
    | ⟨0, _⟩, ⟨0, _⟩, ⟨1, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.id_comp]
    | ⟨0, _⟩, ⟨0, _⟩, ⟨2, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.id_comp]
    | ⟨0, _⟩, ⟨1, _⟩, ⟨1, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.comp_id]
    | ⟨0, _⟩, ⟨1, _⟩, ⟨2, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.assoc]
      exact map_comp f g i
    | ⟨0, _⟩, ⟨2, _⟩, ⟨2, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.comp_id]
    | ⟨1, _⟩, ⟨1, _⟩, ⟨1, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.comp_id]
    | ⟨1, _⟩, ⟨1, _⟩, ⟨2, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.id_comp]
    | ⟨1, _⟩, ⟨2, _⟩, ⟨2, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.comp_id]
    | ⟨2, _⟩, ⟨2, _⟩, ⟨2, _⟩, _, _ =>
      simp only [prod_Hom, Fin.zero_eta, Fin.mk_one, prod_comp, Fin.val_rev, Category.comp_id]


lemma toOrderHom_on_lt_fst_eq {X Y: WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len Y))
    (ha : a.val < len (obj Y (sourceValue f i)).1) :
    (toOrderHom f a).val = (toOrderHom (map f i).1 (preimageIncl₁ a ha)).val := by
  simp only [map, toOrderHom_homMk, OrderHom.coe_mk]
  rfl

lemma toOrderHom_fst_apply {X Y : WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len (obj Y (sourceValue f i)).1)) :
    (toOrderHom (map f i).1 a).val = ((toOrderHom f) (incl₁ a)).val := by
  rw [toOrderHom_on_lt_fst_eq f i (incl₁ a)]
  rfl

lemma toOrderHom_on_fst_le_eq {X Y: WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len Y))
    (ha : len (obj Y (sourceValue f i)).1 ≤ a.val) :
    (toOrderHom f a).val = (toOrderHom (map f i).2 (preimageIncl₂ a ha)).val + i.val := by
  simp [preimageIncl₂]
  change _= ↑((toOrderHom (map f i).2).toFun _) + i.val
  simp only [map, preimageIncl₂, toOrderHom_homMk, OrderHom.toFun_eq_coe, OrderHom.coe_mk]
  nth_rewrite 2 [OrderHom.coe_mk]
  simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk, OrderHom.toFun_eq_coe]
  rw [tsub_add_cancel_iff_le.mpr]
  repeat apply congrArg
  rw [Fin.eq_iff_veq]
  refine (tsub_add_cancel_iff_le.mpr (Nat.not_lt.mp ?_)).symm
  simp [obj, len_mk] at ha
  exact Nat.not_lt.mpr ha
  apply (not_lt.mp ((sourceValue_cond _ _ _).mpr.mt (not_lt.mpr _)))
  simp only [Fin.le_def, Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le, incl₂]

lemma toOrderHom_snd_apply {X Y : WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len (obj Y (sourceValue f i)).2)) :
    (toOrderHom (map f i).2 a).val
    = ((toOrderHom f) (incl₂ a) ).val - i.val := by
  rw [toOrderHom_on_fst_le_eq f i (incl₂ a)]
  simp [incl₂, preimageIncl₂, obj, len_mk]
  simp [incl₂, obj, len_mk]

@[simp]
def assocTypeMap1 {X Y: WithInitial SimplexCategory} (f : X ⟶ Y) (p : assocFiberType1 Y) :
    assocFiberType1 X :=
  assocFiberType1.as (sourceValue f p.1) (sourceValue (map f p.1).1 p.2)

@[simp]
def assocTypeMap2 {X Y: WithInitial SimplexCategory} (f : X ⟶ Y) (p : assocFiberType2 Y) :
    assocFiberType2 X :=
  assocFiberType2.as (sourceValue f p.1) (sourceValue (map f p.1).2 p.2)

lemma sourceValue_map₁ {X Y: WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y)))
    (p : Fin (Nat.succ (len (obj Y i).1))) :
    inclSucc₁ (sourceValue (map f i).1 p) = sourceValue f (inclSucc₁ p) := by
  symm
  rw [sourceValue_iff]
  have hs := sourceValue_cond (map f i).1 p
  intro j
  apply Iff.intro
  · intro hj
    have hjv : j.val < len (obj X (sourceValue f i)).1 := by
      rw [len_obj₁]
      have hp := (sourceValue (map f i).1 p).prop
      rw [Fin.lt_def] at hj
      simp [len_obj₁] at hp
      exact Nat.lt_of_lt_of_le hj (Nat.lt_succ.mp hp)
    have hsj := (hs ⟨j.val, hjv⟩).mp hj
    simp [Fin.lt_def, toOrderHom_fst_apply] at hsj
    rw [Fin.lt_def]
    exact hsj
  · intro hj
    have hjv : j < len (obj X (sourceValue f i)).1 := by
      rw [len_obj₁]
      by_contra hn
      exact lt_iff_not_le.mp (Fin.lt_def.mp hj)
        ((le_of_eq_of_le' (len_obj₁ Y i) (Nat.lt_succ.mp p.prop)).trans
          (Fin.le_def.mp (not_lt.mp ((sourceValue_cond f i j).mpr.mt (hn)))))
    have hsj := (hs ⟨j.val, hjv⟩).mpr
    simp [Fin.lt_def, toOrderHom_fst_apply] at hsj
    exact hsj hj

lemma assocTypeMap_comm  {X Y: WithInitial SimplexCategory} (f : X ⟶ Y) :
    (assocFiberEquiv X).toFun ∘ assocTypeMap1 f = assocTypeMap2 f ∘ (assocFiberEquiv Y).toFun  := by
  funext p
  refine assocFiberType2_ext _ _ (sourceValue_map₁ f p.1 p.2) ?_
  simp [assocFiberEquiv, preimageInclSucc₂', preimageInclSucc₂, len_obj₁, inclSucc₁]
  refine tsub_eq_of_eq_add_rev ?_
  have hp2 := Nat.lt_succ_iff.mp (sourceValue (map f (inclSucc₁ p.2)).2
     (preimageInclSucc₂' p.1 p.2)).prop
  have hs2 := sourceValue_cond (map f (inclSucc₁ p.2)).2  (preimageInclSucc₂' p.1 p.2)
  have hv : ↑(sourceValue (map f p.1).1 p.2)  = (sourceValue f (inclSucc₁ p.2)).val  :=
    (Fin.eq_iff_veq _ _).mp (sourceValue_map₁ f p.1 p.2)
  simp [len_obj₂] at hp2
  rw [sourceValue_val_iff]
  apply And.intro
  have h1 := Nat.add_le_of_le_sub  (Nat.lt_succ_iff.mp (sourceValue f (inclSucc₁ p.2)).prop) hp2
  rw [← hv, add_comm] at h1
  simp [inclSucc₁, preimageInclSucc₂', preimageInclSucc₂, len_obj₁] at h1
  exact Nat.lt_succ_iff.mpr h1
  intro j
  apply Iff.intro
  · intro hj
    simp_all
    by_cases hjlt : j.val < (sourceValue f (inclSucc₁ p.2)).val
    · refine lt_of_lt_of_le (Fin.lt_def.mp ((sourceValue_cond f (inclSucc₁ p.2) j).mp hjlt)) ?_
      rw [Fin.le_def]
      exact le_of_eq_of_le' (len_obj₁ Y p.1) (Nat.lt_succ_iff.mp (p.2.prop))
    · let k : Fin (len (obj X (sourceValue f (inclSucc₁ p.2))).2) :=
        ⟨j.val -  (sourceValue f (inclSucc₁ p.2)).val, by
         rw [len_obj₂]
         exact  (tsub_lt_tsub_iff_right (Nat.not_lt.mp hjlt)).mpr j.prop ⟩
      have hkv : k.val < (sourceValue (map f (inclSucc₁ p.2)).2  (preimageInclSucc₂' p.1 p.2)).val := by
        simp [len_obj₁]
        exact Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp hjlt) hj
      let hs2k := Fin.lt_def.mp ((hs2 k).mp hkv)
      simp only [inclSucc₁, Fin.coe_castSucc, len_obj₁, toOrderHom_snd_apply] at hs2k
      apply lt_of_tsub_lt_tsub_right at hs2k
      rw [Fin.lt_def]
      change ((toOrderHom f) (incl₂ k)).val < p.1.val at hs2k
      have hin : incl₂ k  = j := by
        rw [ Fin.eq_iff_veq]
        exact (tsub_add_cancel_iff_le.mpr (Nat.not_lt.mp hjlt))
      rw [hin] at hs2k
      exact hs2k
  · intro hj
    by_cases hjlt : ((toOrderHom f) j).val < p.2.val
    · rw [hv]
      exact Nat.lt_add_right _ (Fin.lt_def.mp ((sourceValue_cond f (inclSucc₁ p.2) j).mpr hjlt ))
    · have hs1j := (sourceValue_cond f (inclSucc₁ p.2) j).mp.mt hjlt
      let k : Fin (len (obj X (sourceValue f (inclSucc₁ p.2))).2) :=
        ⟨j.val -  (sourceValue f (inclSucc₁ p.2)).val, by
         rw [len_obj₂]
         exact  (tsub_lt_tsub_iff_right (Nat.not_lt.mp hs1j)).mpr j.prop ⟩
      have hin : incl₂ k  = j := by
        rw [ Fin.eq_iff_veq]
        exact tsub_add_cancel_iff_le.mpr (Nat.not_lt.mp hs1j)
      have hkv : Fin.castSucc ((toOrderHom (map f (inclSucc₁ p.2)).2) k) <
         preimageInclSucc₂' p.1 p.2 := by
        rw [Fin.lt_def]
        simp only [Fin.coe_castSucc, toOrderHom_snd_apply, preimageInclSucc₂', preimageInclSucc₂,
         len_obj₁, inclSucc₁]
        change ((toOrderHom f) (incl₂ k)).val - p.2.val < p.1.val - p.2.val
        rw [hin]
        refine (tsub_lt_tsub_iff_right (Nat.not_lt.mp hjlt)).mpr (Fin.lt_def.mp hj)
      let hs2k := Fin.lt_def.mp ((hs2 k).mpr hkv)
      simp only [Fin.castSucc_mk] at hs2k
      rw [← hv] at hs2k
      simp only [inclSucc₁, preimageInclSucc₂', preimageInclSucc₂, len_obj₁] at hs2k
      refine (tsub_lt_iff_left ?_).mp hs2k
      rw [hv]
      exact Nat.not_lt.mp hs1j

lemma mapOrderHom₂_map_lt_p1 {X Y : (WithInitial SimplexCategory)ᵒᵖ}  (f : X ⟶ Y)
    (s : assocClassifier1.obj X)
    (j : Fin (len Y.unop))
    (hj : j.val < (joinClassifying.map f (((assocIsoComponents X).hom s).1)).val +
    (joinClassifying.map (joinClassifyEquivOpOp.functor.map
    (coCartesianLift f ((assocIsoComponents X).hom s).1)).2 ((assocIsoComponents X).hom s).2).val):
    Fin.castSucc ((toOrderHom f.unop) j) < s.1 := by
  let x := (joinClassifying.map f (((assocIsoComponents X).hom s).1))
  let y := (joinClassifying.map (joinClassifyEquivOpOp.functor.map
    (coCartesianLift f ((assocIsoComponents X).hom s).1)).2 ((assocIsoComponents X).hom s).2)
  by_cases hjlt : j.val < x.val
  · let hs1 := (sourceValue_cond f.unop ((assocIsoComponents X).hom s).1 j).mp hjlt
    refine lt_of_lt_of_le (Fin.lt_def.mp hs1) ?_
    rw [Fin.le_def]
    have hsprop := (Nat.lt_succ_iff.mp (s.2.prop))
    simp_all
  · have hyC := sourceValue_cond (joinClassifyEquivOpOp.functor.map
      (coCartesianLift f ((assocIsoComponents X).hom s).1)).2.unop ((assocIsoComponents X).hom s).2
    sorry

lemma mapOrderHom₂_map_lt {X Y : (WithInitial SimplexCategory)ᵒᵖ}  (f : X ⟶ Y)
    (s : assocClassifier1.obj X)  :
    (joinClassifying.map f (((assocIsoComponents X).hom s).1)).val +
    (joinClassifying.map (joinClassifyEquivOpOp.functor.map
    (coCartesianLift f ((assocIsoComponents X).hom s).1)).2 ((assocIsoComponents X).hom s).2).val
    < Nat.succ (len Y.unop) := by
  let x := (joinClassifying.map f (((assocIsoComponents X).hom s).1))
  let y := (joinClassifying.map (joinClassifyEquivOpOp.functor.map
    (coCartesianLift f ((assocIsoComponents X).hom s).1)).2 ((assocIsoComponents X).hom s).2)
  have hx : x.val ≤  _ := Nat.lt_succ.mp x.prop
  have hy : y.val ≤  _ := Nat.lt_succ.mp y.prop
  simp at hy
  change y.val ≤ len Y.unop - x.val at hy
  rw [Nat.lt_succ, add_comm]
  exact  Nat.add_le_of_le_sub hx hy








/-- Given a map `f : Z ⟶ Y`, the corresponding map from `hom Y X i` to `hom Z X i`. -/
def homMap {Y Z : WithInitial SimplexCategory} (X : WithInitial SimplexCategory)
    (i : Fin (Nat.succ (len X))) (f : Z ⟶ Y) (s : hom Y X i) : hom Z X i :=
  hom.split (sourceValue f s.1) (map f s.1 ≫ s.2)

def fiberMapIso  {Y X : WithInitial SimplexCategory}  (f : Y ⟶ X) (i :  Fin (Nat.succ (len X))) :
    (ComposableArrows.mk₁ f) ≅ (fiberMap f i) ⋙ join :=
  NatIso.ofComponents
  (fun k =>
    match k with
    | ⟨0, _⟩ => (joinSplitIso Y (sourceValue f i))
    | ⟨1, _⟩ => (joinSplitIso X i)
  )
  (by
  intro j k a
  match j, k, a with
  | ⟨0, hk⟩, ⟨0, hj⟩, a =>
    have ha : a = 𝟙 (⟨0, hk⟩ : Fin 2)  := rfl
    subst ha
    simp
  | ⟨0, _⟩, ⟨1, _⟩, b =>
    simp [fiberMap]
    rw [← Iso.eq_comp_inv, Category.assoc]
    symm
    apply hom_eq_if_toOrderHom_eq
    apply OrderHom.ext
    funext a
    rw [toOrderHom_comp, toOrderHom_comp, Split.joinSplitIso, Split.joinSplitIso]
    rw [toOrderHom_of_lenIso_hom, toOrderHom_of_lenIso_inv, Fin.eq_iff_veq]
    by_cases ha : a.val < len (Split.obj Y (sourceValue f i)).1
    · rw [toOrderHom_on_lt_fst_eq f i a ha]
      exact toOrderHom_join_apply_on_lt_fst (Split.map f i)
        (Fin.cast (Split.join_split_len Y (sourceValue f i)) a) ha
    · rw [Split.toOrderHom_on_fst_le_eq f i a (Nat.not_lt.mp ha)]
      simp only [OrderHom.comp_coe, OrderHomClass.coe_coe, Function.comp_apply, Fin.castIso_apply,
        Fin.coe_cast]
      erw [toOrderHom_join_apply_on_fst_le (Split.map f i) (Fin.cast _ a)]
      simp [Split.obj, len_mk, preimageIncl₂]
      simp_all [obj, len_mk]
  | ⟨1, h1⟩, ⟨1, _⟩, a =>
    have ha : a = 𝟙 (⟨1, h1⟩ : Fin 2) := rfl
    subst ha
    simp
  )



/-- An equivalance between the type `hom X Y i` and the type `Y ⟶ X`. In the forward direction
maps are joined and in the inverse direction maps are split based in the index `i`. -/
def splitJoinUnitEquiv (X Y : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    hom Y X i ≃ (Y ⟶ X) where
  toFun s :=
    match s with
    | Split.hom.split p fs =>
    (joinSplitIso Y p).hom ≫ join.map fs ≫ (joinSplitIso X i).inv
  invFun f := Split.hom.split (sourceValue f i) (Split.map f i)
  left_inv := fun s => by
    refine Split.hom_ext _ _ _ _ _
      (sourceValue_of_joinSplitIso_comp_join_comp_joinSplitIso i s.1 s.2) ?_
    apply Prod.ext
    all_goals apply hom_eq_if_toOrderHom_eq
    all_goals apply OrderHom.ext
    all_goals funext a
    · simp only [prod_comp_fst, toOrderHom_comp, prod_Hom, OrderHom.comp_coe, Function.comp_apply]
      rw [Split.toOrderHom_indexEqToIso_inv_fst_apply, Fin.eq_iff_veq, Split.toOrderHom_fst_apply]
      simp only [joinSplitIso, toOrderHom_comp, toOrderHom_of_lenIso_inv,
        toOrderHom_of_lenIso_hom, incl₁, OrderHom.comp_coe, OrderHomClass.coe_coe,
        Function.comp_apply, Fin.castIso_apply, Fin.cast_mk, Fin.coe_cast,
        WithInitial.toOrderHom_fst_apply]
    · simp only [prod_comp_snd, toOrderHom_comp, prod_Hom, OrderHom.comp_coe, Function.comp_apply]
      rw [Split.toOrderHom_indexEqToIso_inv_snd_apply, Fin.eq_iff_veq, Split.toOrderHom_snd_apply]
      simp only [Split.joinSplitIso, toOrderHom_comp, toOrderHom_of_lenIso_inv,
        toOrderHom_of_lenIso_hom, Split.incl₂, OrderHom.comp_coe, OrderHomClass.coe_coe,
        Function.comp_apply, Fin.castIso_apply, Fin.cast_mk, Fin.coe_cast,
        WithInitial.toOrderHom_snd_apply]
      simp [Split.obj, len_mk]
      apply congrFun
      repeat apply congrArg
      simp [Split.obj, len_mk]
      exact (Fin.eq_iff_veq _ _).mp
          (sourceValue_of_joinSplitIso_comp_join_comp_joinSplitIso i s.1 s.2)
  right_inv := fun f => by
    have h := (fiberMapIso f i).hom.naturality (@LE.le.hom (Fin 2) _ ⟨0,Nat.le.step Nat.le.refl⟩
      ⟨1, Nat.le.refl⟩ (Nat.le.step Nat.le.refl))
    simp [fiberMapIso, fiberMap] at h
    rw [← Iso.eq_comp_inv, Category.assoc] at h
    symm
    exact h





lemma splitJoinUnitEquiv_naturality (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    {Z Y : WithInitial SimplexCategory} (f : Z ⟶ Y) :
    ((Split.splitJoinUnitEquiv X Z i).symm).toFun ∘ (CategoryStruct.comp f) =
    (homMap X i f) ∘ ((Split.splitJoinUnitEquiv X Y i).symm).toFun := by
  funext s
  refine Split.hom_ext _ _ _ _ _ (sourceValue_of_comp f s i).symm ?_
  simp only [Split.splitJoinUnitEquiv,  Equiv.toFun_as_coe, Equiv.coe_fn_symm_mk,
    Function.comp_apply, homMap,  Fin.val_rev, Prod.mk.injEq]
  rw [Split.map_comp, ← Category.assoc, ← Category.id_comp (Split.map f (sourceValue s i))]
  rw [← Category.assoc, ← Category.assoc, Category.comp_id, indexEqToIso_inv_comp_symm_inv]
  rfl

lemma splitJoinUnitEquiv_naturality_equiv (X : WithInitial SimplexCategory)
    (i : Fin (Nat.succ (len X))) {Z Y : WithInitial SimplexCategory} (f : Z ⟶ Y) :
    (Equiv.toIso (Split.splitJoinUnitEquiv X Z i).symm).hom ∘ (CategoryStruct.comp f) =
    (homMap X i f) ∘ (Equiv.toIso (Split.splitJoinUnitEquiv X Y i).symm).hom := by
  exact Split.splitJoinUnitEquiv_naturality X i f

end Split
end WithInitial
end SimplexCategory
