/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.Order.Category.LinOrd
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
    len (join.obj X) = len X.1 + len X.2 := by
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
def joinClassifyMap {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    Fin (Nat.succ (len X)) :=
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  match k with
  | some k => k.castSucc
  | none => Fin.last (len X)

lemma joinClassifyMap_iff {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y)))
    (a : Fin (Nat.succ (len X))) : joinClassifyMap f i = a ↔
    ∀ (j : Fin (len X)), (j.castSucc < a ↔ (toOrderHom f j).castSucc < i) := by
  simp [joinClassifyMap]
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


lemma joinClassifyMap_cond {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y))) :
    ∀ (j : Fin (len X)), (j.castSucc < (joinClassifyMap f i) ↔ (toOrderHom f j).castSucc < i) :=
  (joinClassifyMap_iff f i (joinClassifyMap f i)).mp (by rfl)

lemma joinClassifyMap_iff_val {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y)))
    (a : ℕ) : (joinClassifyMap f i).val = a ↔ a < Nat.succ (len X) ∧
    ∀ (j : Fin (len X)), (j.val < a ↔ (toOrderHom f j).castSucc < i) := by
  apply Iff.intro
  intro ha
  subst ha
  apply And.intro
  exact (joinClassifyMap f i).prop
  exact joinClassifyMap_cond f i
  intro ha
  suffices h : (joinClassifyMap f i) = ⟨a, ha.left⟩ from (Fin.eq_iff_veq _ _).mp h
  rw [joinClassifyMap_iff]
  exact ha.right


lemma joinClassifyMap_monotone {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)  :
    Monotone (joinClassifyMap f) := by
  intro a b hab
  have hj : ∀ (j : Fin (len X)),  Fin.castSucc j < joinClassifyMap f a →
      Fin.castSucc j < joinClassifyMap f b := by
    intro j
    rw [joinClassifyMap_cond f b j, joinClassifyMap_cond f a j]
    intro hj
    exact LT.lt.trans_le hj hab
  by_contra hab
  simp only [not_le] at hab
  have hb : (joinClassifyMap f b).val < (len X) :=  Nat.lt_of_lt_of_le hab
    (Nat.lt_succ.mp (joinClassifyMap f a).prop )
  exact LT.lt.false ((hj ⟨(joinClassifyMap f b).val, hb⟩) hab)

lemma joinClassifyMap_of_iso_hom {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len X))) :
    joinClassifyMap f.hom i = ⟨i.val, by rw [len_iso f]; exact i.prop⟩ := by
  rw [joinClassifyMap_iff]
  intro j
  rw [toOrderHomIso_apply]
  rfl

lemma joinClassifyMap_of_iso_inv {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len Y))) :
    joinClassifyMap f.inv i = ⟨i.val, by rw [← len_iso f]; exact i.prop⟩ := by
  change joinClassifyMap (f.symm).hom i =_
  rw [joinClassifyMap_of_iso_hom]

lemma joinClassifyMap_of_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    joinClassifyMap (𝟙 X) i = i := by
  change joinClassifyMap (Iso.refl X).hom i = i
  rw [joinClassifyMap_of_iso_hom]

lemma joinClassifyMap_of_comp {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z))) :
    joinClassifyMap f (joinClassifyMap g i) = joinClassifyMap (f ≫ g) i := by
  rw [joinClassifyMap_iff]
  intro j
  apply Iff.intro
  · intro hj
    have hjj := (joinClassifyMap_cond (f ≫ g) i  j).mp hj
    rw [toOrderHom_comp] at hjj
    simp only [OrderHom.comp_coe, Function.comp_apply] at hjj
    exact (joinClassifyMap_cond g i  ((toOrderHom f) j)).mpr hjj
  · intro hj
    have hjj := (joinClassifyMap_cond g i  ((toOrderHom f) j)).mp hj
    change  Fin.castSucc (((toOrderHom g).comp (toOrderHom f)) ( j)) < i at hjj
    rw [← toOrderHom_comp] at hjj
    exact (joinClassifyMap_cond (f ≫ g) i  j).mpr hjj

lemma joinClassifyMap_of_join {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) : joinClassifyMap (join.map f) ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    = ⟨len X.1, len_of_fst_lt_len_of_join_plus_one X⟩ := by
  rw [joinClassifyMap_iff]
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
   | ⟨X⟩, ⟨Y⟩, ⟨f⟩ => joinClassifyMap f
  map_id X := by
    match X with
    | ⟨X⟩ =>
     funext i
     exact joinClassifyMap_of_id i
  map_comp {X Y Z} f g := by
    match X, Y, Z, f, g with
    | ⟨X⟩, ⟨Y⟩, ⟨Z⟩, ⟨f⟩, ⟨g⟩ =>
     funext i
     exact (joinClassifyMap_of_comp g f i).symm

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
    ( Fin.lt_def.mp ((joinClassifyMap_cond f.1.1.1 Yp.1.2 (incl₁ a)).mp ht))

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
    (not_lt.mp ((joinClassifyMap_cond f.1.1.1 Yp.1.2 (incl₂ a)).mpr.mt (not_lt.mpr h0)))

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
  erw [joinClassifyMap_of_join]
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
  )).hom⟩, by simp [joinClassifyMap_of_iso_hom] ⟩⟩
  inv := ⟨⟨⟨(lenIso (by
   simp [len_of_join]
   rw [add_comm]
   refine (Nat.sub_add_cancel X.unop.snd.is_le).symm
  )).inv⟩, by simp [joinClassifyMap_of_iso_inv, invObj] ⟩⟩
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
      have hx : ¬Fin.castSucc ap < joinClassifyMap f p  := by
        simp only [joinClassifying_obj, Fin.castSucc_mk, not_lt]
        simp only [joinClassifying_obj, joinClassifying_map] at h
        rw [h]
        exact ha
      refine le_of_eq_of_le' ?_ (Nat.not_lt.mp (((joinClassifyMap_cond f p ap).mpr.mt hx)))
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



end classifyingMap


section joinAssoc

def assocType1Part : joinClassifying.Elements ⥤ Type :=
  joinClassifyEquivOpOp.functor ⋙ CategoryTheory.Prod.fst _ _ ⋙ joinClassifying

def assocTypeSndPart : joinClassifying.Elements ⥤ Type :=
  joinClassifyEquivOpOp.functor ⋙ CategoryTheory.Prod.snd _ _ ⋙ joinClassifying

inductive assocType1 (X : (WithInitial SimplexCategory)ᵒᵖ)
  | as : (i : joinClassifying.obj X ) →
    (p : (assocType1Part).obj (joinClassifying.objLift i)) → assocType1 X

inductive assocTypeSnd (X : (WithInitial SimplexCategory)ᵒᵖ)
  | as : (i : joinClassifying.obj X ) →
    (p : (assocTypeSndPart).obj (joinClassifying.objLift i)) → assocTypeSnd X


lemma assocType1_ext  {X : (WithInitial SimplexCategory)ᵒᵖ} (s t : assocType1 X)
    (h1 : s.1 = t.1)
    (h2 : ((assocType1Part).map (joinClassifying.ObjEqIso h1).hom) s.2 = t.2) :
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
  simp only [joinClassifyEquivOp_functor_obj, Opposite.unop_op, objClass_fst, Functor.objLift_fst,
    Functor.objLift_snd]
  change (joinClassifyMap (((CategoryTheory.Prod.fst _ _).mapIso
  (joinClassifyEquivOpOp.functor.mapIso (joinClassifying.ObjEqIso h1))).unop.hom) s.2).val
    = s.2.val
  rw [joinClassifyMap_of_iso_hom]


lemma assocTypeSnd_ext  {X : (WithInitial SimplexCategory)ᵒᵖ} (s t : assocTypeSnd X)
    (h1 : s.1 = t.1)
    (h2 : ((assocTypeSndPart).map (joinClassifying.ObjEqIso h1).hom) s.2 = t.2) :
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
  simp only [joinClassifyEquivOp_functor_obj, Opposite.unop_op]
  change (joinClassifyMap (((CategoryTheory.Prod.snd _ _).mapIso
  (joinClassifyEquivOpOp.functor.mapIso (joinClassifying.ObjEqIso h1))).unop.hom) s.2).val
    = s.2.val
  rw [joinClassifyMap_of_iso_hom]

@[simp]
def assocType1Map {X Y : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y) (s : assocType1 X) :
    assocType1 Y :=
    assocType1.as
      (joinClassifying.map f s.1)
      ((assocType1Part).map (joinClassifying.coCartesianLift f s.1) s.2)

def assocTypeSndMap {X Y : (WithInitial SimplexCategory)ᵒᵖ} (f : X ⟶ Y) (s : assocTypeSnd X) :
  assocTypeSnd Y :=
    assocTypeSnd.as
      (joinClassifying.map f s.1)
      ((assocTypeSndPart).map (joinClassifying.coCartesianLift f s.1) s.2)


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
    rw [← assocType1Part.map_comp, joinClassifying.coCartesianLift_id]
    erw [← Iso.trans_hom, joinClassifying.ObjEqIso_symm, assocType1Part.map_id]
    rfl
  map_comp {X Y Z} f g := by
    funext a
    simp only [assocType1Map]
    refine assocType1_ext _ _ ?_ ?_
    simp only [joinClassifying.map_comp]
    rfl
    simp only
    rw [← types_comp_apply (assocType1Part.map _) (assocType1Part.map _)]
    rw [← assocType1Part.map_comp, joinClassifying.coCartesianLift_comp, assocType1Part.map_comp]
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
    rw [← assocTypeSndPart.map_comp, joinClassifying.coCartesianLift_id]
    erw [← Iso.trans_hom, joinClassifying.ObjEqIso_symm, assocTypeSndPart.map_id]
    rfl
  map_comp {X Y Z} f g := by
    funext a
    simp only [assocTypeSndMap]
    refine assocTypeSnd_ext _ _ ?_ ?_
    simp only [joinClassifying.map_comp]
    rfl
    simp only
    rw [← types_comp_apply (assocTypeSndPart.map _) (assocTypeSndPart.map _)]
    rw [← assocTypeSndPart.map_comp, joinClassifying.coCartesianLift_comp, assocTypeSndPart.map_comp]
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
    (joinClassifying.map
    (joinClassifyEquivOpOp.functor.map (joinClassifying.coCartesianLift f s.1)).1 s.2).val
    = (joinClassifying.map f (((assocIsoComponents X).hom s).1)).val := by
  simp
  have h2 := Nat.lt_succ.mp s.2.prop
  simp at h2
  rw [joinClassifyMap_iff_val]
  apply And.intro
  · rw [Nat.lt_succ]
    simp
    refine joinClassifyMap_monotone f.unop ?_
    rw [Fin.le_def]
    exact h2
  · intro j
    erw [toOrderHom_homMk]
    exact joinClassifyMap_cond f.unop ⟨s.2.val, assocIsoComponents.proof_1 X s ⟩ (incl₁ j)



lemma mapOrderHom₂_map {X Y : (WithInitial SimplexCategory)ᵒᵖ}  (f : X ⟶ Y)
    (s : assocClassifier1.obj X) : (joinClassifying.map f s.1).val -
    (joinClassifying.map f (((assocIsoComponents X).hom s).1)).val
    = (joinClassifying.map (joinClassifyEquivOpOp.functor.map
    (joinClassifying.coCartesianLift f ((assocIsoComponents X).hom s).1)).2 ((assocIsoComponents X).hom s).2).val
    := by
  let x := (joinClassifying.map f (((assocIsoComponents X).hom s).1))
  let y := (joinClassifying.map f s.1)
  have hx := Nat.lt_succ_iff.mp x.prop
  symm
  erw [joinClassifyMap_iff_val]
  apply And.intro
  · simp
    rw [Nat.lt_succ_iff]
    exact (Nat.sub_le_sub_iff_right hx).mpr (Nat.lt_succ_iff.mp y.prop)
  · intro j
    rw [Fin.lt_def]
    simp only [assocClassifier1_obj, assocClassifierSnd_obj, joinClassifying_map,
      joinClassifyEquivOp_functor_obj, Opposite.unop_op, objClass_fst,
      joinClassifyEquivOp_functor_map, Quiver.Hom.unop_op, Fin.coe_castSucc]
    rw [toOrderHom_homMk, mapOrderHom₂_apply_val]
    change _ ↔ (toOrderHom f.unop (incl₂ j)).val - s.2.val < s.1.val - s.2.val
    by_cases hr : s.2.val < s.1.val
    · apply Iff.intro
      · intro hj
        have hs := Fin.lt_def.mp ((joinClassifyMap_cond f.unop s.1 (incl₂ j)).mp
          (Nat.add_lt_of_lt_sub hj))
        omega
      · intro hj
        have hk : ↑((toOrderHom f.unop) (incl₂ j)) < s.1.val := by
          exact lt_of_tsub_lt_tsub_right hj
        have hs := Fin.lt_def.mp (((joinClassifyMap_cond f.unop s.1 (incl₂ j)).mpr) hk)
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
      simp only [Equivalence.symm_functor, opOpEquivalence_inverse, assocClassifier1_obj,
        assocClassifierSnd_obj, joinClassifying_map, opOp_obj, Opposite.unop_op, incl₂,
        joinClassifying_obj, joinClassifyEquivOp_functor_obj, objClass_fst, ge_iff_le, le_refl,
        tsub_eq_zero_of_le, not_lt_zero', iff_false, not_lt, tsub_le_iff_right]
      erw [← hr3]
      exact Nat.le_add_left ↑(joinClassifyMap f.unop ((assocIsoComponents X).hom s).1) ↑j

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


@[simps!]
def inclFst₁ {Y : assocClassifier1.Elements} :
    Fin (len (assocFstTo3WithInitial.obj Y).1.unop) →o Fin (len Y.1.unop) :=
  (@incl₁ (Opposite.op (assoc1ToJoin.obj Y))).comp
  (@incl₁ (Opposite.op (assoc1ToWithInitialWithInitial.obj Y).1))

@[simps!]
def inclFst₂ {Y : assocClassifier1.Elements} :
    Fin (len (assocFstTo3WithInitial.obj Y).2.1.unop) →o Fin (len Y.1.unop) :=
  (@incl₁ (Opposite.op ⟨Y.fst, Y.snd.1⟩)).comp
  (@incl₂ (Opposite.op (assoc1ToWithInitialWithInitial.obj Y).1))

@[simps!]
def inclFst₃ {Y : assocClassifier1.Elements}
    (a : Fin (len (assocFstTo3WithInitial.obj Y).2.2.unop)) : Fin (len Y.1.unop) :=
  @incl₂ (Opposite.op ⟨Y.fst,  Y.snd.1⟩) a

@[simps!]
def inclSnd₁ {Y : assocClassifierSnd.Elements}
    (a : Fin (len (assocSndTo3WithInitial.obj Y).1.unop)) : Fin (len Y.1.unop) :=
  @incl₁ (Opposite.op (assocSndToJoin.obj Y)) a

@[simps!]
def inclSnd₂ {Y : assocClassifierSnd.Elements}
    (a : Fin (len (assocSndTo3WithInitial.obj Y).2.1.unop)) : Fin (len Y.1.unop) :=
  @incl₂ (Opposite.op ⟨Y.fst, Y.snd.1⟩)
  (@incl₁ (Opposite.op (assocSndToWithInitialWithInitial.toPrefunctor.obj Y).2) a)

@[simps!]
def inclSnd₃ {Y : assocClassifierSnd.Elements}
    (a : Fin (len (assocSndTo3WithInitial.obj Y).2.2.unop)) : Fin (len Y.1.unop) :=
  @incl₂ (Opposite.op ⟨Y.fst, Y.snd.1⟩)
  (@incl₂ (Opposite.op (assocSndToWithInitialWithInitial.toPrefunctor.obj Y).2) a)



@[simp]
lemma assocFstTo3WithInitial_fst_apply {X Y : assocClassifier1.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocFstTo3WithInitial.obj Y).1.unop)) :
    (toOrderHom (assocFstTo3WithInitial.map f).1.1 a).val =
    ((toOrderHom f.1.1) (inclFst₁ a)).val := by
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
    ((toOrderHom f.1.1) (inclSnd₁ a)).val := by
  change (toOrderHom (homMk _) a).val = _
  rw [toOrderHom_homMk]
  erw [mapOrderHom₁_apply_val]


@[simp]
lemma assocFstTo3WithInitial_snd_apply {X Y : assocClassifier1.Elements} (f : X ⟶ Y)
    (a : Fin (len (assocFstTo3WithInitial.obj Y).2.1.unop)) :
    (toOrderHom (assocFstTo3WithInitial.map f).2.1.1 a).val =
    ((toOrderHom f.1.1) (inclFst₂ a)).val - X.2.2.val := by
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
    ((toOrderHom f.1.1) (inclSnd₂ a)).val - X.2.1.val := by
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
    ((toOrderHom f.1.1) (inclFst₃ a)).val
     - X.2.1.val := by
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
    ((toOrderHom f.1.1) (inclSnd₃ a)).val - X.2.1.val- X.2.2.val := by
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
   have h1 := Nat.lt_succ.mp X.2.1.prop
   have h2 := Nat.lt_succ.mp X.2.2.prop
   simp at h2
   omega
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
    Opposite.unop_op, objClass_fst, Functor.comp_map, OrderHom.comp_coe, Function.comp_apply]
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
  have h2 := Nat.lt_succ.mp X.2.2.prop
  simp at h2
  rw [tsub_tsub, add_tsub_cancel_of_le h2]
  apply congrFun
  repeat apply congrArg
  rw [Fin.eq_iff_veq]
  simp [incl₂]
  change a.val + Y.2.1.val = a.val + (Y.2.1.val - Y.2.2.val) + Y.2.2.val
  rw [add_assoc, tsub_add_cancel_iff_le.mpr]
  have hy := Nat.lt_succ.mp Y.2.2.prop
  simp at hy
  exact hy


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
end WithInitial
end SimplexCategory
