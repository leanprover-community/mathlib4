/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Linarith
import Mathlib.CategoryTheory.Skeletal
import Mathlib.Data.Fintype.Sort
import Mathlib.Order.Category.NonemptyFinLinOrd
import Mathlib.CategoryTheory.Functor.ReflectsIso
import Mathlib.CategoryTheory.WithTerminal
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

/-- An isomorphism between objects of equal lengths. -/
def lenIso {X Y : WithInitial SimplexCategory} (h : len X = len Y) : X ≅ Y where
  hom :=
    match X, Y with
    | star, star => 𝟙 _
    | of x, of y => Hom.mk (Fin.castIso h : Fin (len (of x)) →o Fin (len (of y )))
  inv :=
    match X, Y with
    | star, star => 𝟙 _
    | of x, of y => Hom.mk (Fin.castIso h.symm : Fin (len (of y)) →o Fin (len (of x)))

/-- A function from `ℕ` to `WithInitial SimplexCategory` taking `0` to `start` and
 `Nat.succ x` to `of (mk x)`. -/
def mk (i : ℕ) : WithInitial SimplexCategory :=
  match i with
  | Nat.zero => star
  | Nat.succ x => of (SimplexCategory.mk x)

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
def toOrderHomIso {X Y : WithInitial SimplexCategory} (f : X ≅ Y) : Fin (len X) ≃o Fin (len Y) where
  toFun := toOrderHom f.hom
  invFun := toOrderHom f.inv
  left_inv := by
    intro s
    change ((toOrderHom f.inv).comp (toOrderHom f.hom)) s = s
    rw [← toOrderHom_comp]
    rw [f.hom_inv_id]
    rw [toOrderHom_id]
    rfl
  right_inv := by
    intro s
    change ((toOrderHom f.hom).comp (toOrderHom f.inv)) s = s
    rw [← toOrderHom_comp]
    rw [f.inv_hom_id]
    rw [toOrderHom_id]
    rfl
  map_rel_iff' := by
    intro a b
    simp
    apply Iff.intro
    intro h1
    by_contra hn
    simp at hn
    have h3 : (toOrderHom f.hom) a = (toOrderHom f.hom) b := by
      rw [Fin.eq_iff_veq]
      exact Nat.le_antisymm h1 ((toOrderHom f.hom).monotone'
        (Fin.succ_le_succ_iff.mp (Nat.le.step hn)))
    apply congrArg (toOrderHom f.inv) at h3
    change ((toOrderHom f.inv).comp (toOrderHom f.hom)) a =
      ((toOrderHom f.inv).comp (toOrderHom f.hom)) b at h3
    rw [← toOrderHom_comp] at h3
    rw [f.hom_inv_id] at h3
    rw [toOrderHom_id] at h3
    simp at h3
    subst h3
    simp_all only [lt_self_iff_false]
    intro h1
    exact (toOrderHom f.hom).monotone' h1

lemma toOrderHomIso_apply {X Y : WithInitial SimplexCategory} (f : X ≅ Y) (a : Fin (len X)) :
    toOrderHom f.hom a = ⟨a, by rw [← len_iso f]; exact a.prop⟩ := by
  rw [Fin.eq_iff_veq]
  exact Fin.coe_orderIso_apply (toOrderHomIso f) a

lemma Hom.exe {X Y : WithInitial SimplexCategory} {f g: X ⟶ Y}
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

lemma toOrderHom_of_lenIso_hom {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    toOrderHom (lenIso h).hom = (Fin.castIso h : Fin (len X) →o Fin (len Y)) := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl

lemma toOrderHom_of_lenIso_inv {X Y : WithInitial SimplexCategory} (h : len X = len Y) :
    toOrderHom (lenIso h).inv = (Fin.castIso h.symm : Fin (len Y) →o Fin (len X)) := by
  match X, Y with
  | star, star => rfl
  | of x, of y => rfl

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
    | (star, star), (star, star), (star, star), f, g => rfl
    | (star, star), (star, star), (star, of z), f, g => rfl
    | (star, star), (star, star), (of z, star), f, g => rfl
    | (star, star), (star, star), (of z1, of z2), f, g => rfl
    | (star, star), (star, of y), (star, of z), f, g => rfl
    | (star, star), (of y, star), (of z, star), f, g => rfl
    | (star, star), (star, of y), (of z1, of z2), f, g => rfl
    | (star, star), (of y, star), (of z1, of z2), f, g => rfl
    | (star, star), (of y1, of y2), (of z1, of z2), f, g => rfl
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
  | (star, star), (star, star), _ => rfl
  | (star, star), (star, of y), _ =>
    simp [len] at ha
  | (star, star), (of y, star), _ =>  rfl
  | (star, star), (of y1, of y2), f =>
    simp [len] at ha
  | (star, of x), (star, of y), f =>
    simp [len] at ha
  | (of x, star), (of y, star), f => rfl
  | (of x1, of x2), (of y1, of y2), f =>
    simp [toOrderHom, Join.func]
    have hx {n m  : ℕ } (f : Fin n → Fin m ) (mo : Monotone f) (a : Fin  n) :
    (({toFun := f, monotone' := mo } : Fin n →o Fin m) a).val = (f a).val := rfl
    erw [hx]
    split_ifs
    rfl
    rename_i ht
    simp at ha
    exact (ht ha).elim
  | (of x1, star), (of y1, of y2), f => rfl
  | (star, of x2), (of y1, of y2), f =>
    simp [len] at ha

lemma toOrderHom_join_apply_on_fst_le
    {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) (a : Fin (len (join.obj X))) (ha : len (X.1) ≤ a.val) :
    (toOrderHom (join.map f) a).val =
    (toOrderHom f.2 ⟨a.val-len X.1, sub_fst_lt_snd_if_fst_le a ha⟩).val + len Y.1 := by
  simp [join]
  match X, Y, f with
  | (star, star), (star, star), _ => rfl
  | (star, star), (star, of y), _ => rfl
  | (star, star), (of y, star), _ =>
    exact Fin.elim0 a
  | (star, star), (of y1, of y2), f =>
    exact Fin.elim0 a
  | (star, of x), (star, of y), f => rfl
  | (of x, star), (of y, star), f =>
    have hx := sub_fst_lt_snd_if_fst_le a ha
    simp [len] at hx
  | (of x1, of x2), (of y1, of y2), f =>
    simp [toOrderHom, Join.func]
    have hx {n m  : ℕ } (f : Fin n → Fin m ) (mo : Monotone f) (a : Fin  n) :
    (({toFun := f, monotone' := mo } : Fin n →o Fin m) a).val = (f a).val := rfl
    erw [hx]
    split_ifs
    rename_i han
    simp [len] at ha
    rw [Nat.succ_eq_add_one] at ha
    exact ((Nat.not_le.mpr han) ha).elim
    simp [len]
  | (of x1, star), (of y1, of y2), f =>
    have hx := sub_fst_lt_snd_if_fst_le a ha
    simp [len] at hx
  | (star, of x2), (of y1, of y2), f => rfl

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

namespace Split

/-- Splits an object `X` into two parts based on an element of `Fin (Nat.succ (len X))`. -/
def obj (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))):
    WithInitial SimplexCategory × WithInitial SimplexCategory := (mk i, mk i.rev)

lemma incl₁_cond {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (len (obj Y p).1)) : a.val < len Y := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (obj X i).1)` into `Fin X`. -/
def incl₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len (obj X i).1)) : Fin (len X) := ⟨a.val, incl₁_cond a⟩

/-- The preimage of an object in `Fin (len X)` under `incl₁` when it exists. -/
def preimageIncl₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : a.val < len (obj X i).1) : Fin (len (obj X i).1) := ⟨a.val, ha⟩

lemma incl₂_cond  {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (len (obj Y p).2)) :
    a.val + p.val < len Y := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (len (obj X i).2)` into `Fin X`. -/
def incl₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len (obj X i).2)) : Fin (len X) := ⟨a.val + i.val, incl₂_cond a⟩

lemma preimageIncl₂_cond  {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : len (obj X i).1 ≤ a.val) :
    a.val - (len (obj X i).1) < len (obj X i).2 := by
  simp_all [obj, len_mk]
  refine lt_tsub_of_add_lt_right ?_
  rw [tsub_add_cancel_iff_le.mpr ha]
  have h := a.prop
  unfold obj at h
  simp [len_mk] at h
  omega

/-- The preimage of an object in `Fin (len X)` under `incl₂` when it exists. -/
def preimageIncl₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : len (obj X i).1 ≤ a.val) :
    Fin (len (obj X i).2) := ⟨a.val - (len (obj X i).1) , preimageIncl₂_cond a ha⟩

/-- An isomorphism between `obj X i` and `obj X j` when `i=j`. -/
def indexEqToIso {X : WithInitial SimplexCategory} {i j : Fin (Nat.succ (len X))}
    (h : i = j) : obj X i ≅ obj X j where
  hom := (homMk (Fin.castIso (by rw [h] : len (obj X i).1 = len (obj X j).1)),
          homMk (Fin.castIso (by rw [h] : len (obj X i).2 = len (obj X j).2)))
  inv := (homMk (Fin.castIso (by rw [h] : len (obj X i).1 = len (obj X j).1).symm),
          homMk (Fin.castIso (by rw [h] : len (obj X i).2 = len (obj X j).2).symm))
  hom_inv_id := by
    simp only [obj, Fin.val_rev, prod_Hom, prod_comp, prod_id, Prod.mk.injEq]
    rw [← homMk_comp, ← homMk_comp]
    change homMk (OrderHom.id) = _ ∧ homMk (OrderHom.id) = _
    simp only [homMk_id, and_self, mk]
  inv_hom_id := by
    simp [obj]
    rw [← homMk_comp, ← homMk_comp]
    change homMk (OrderHom.id) =_ ∧ homMk (OrderHom.id) =_
    simp only [homMk_id, and_self, mk]

lemma indexEqToIso_refl {X : WithInitial SimplexCategory} {i  : Fin (Nat.succ (len X))} :
    indexEqToIso (by rfl : i = i) = Iso.refl (obj X i) := by
  ext
  simp [indexEqToIso]
  change (homMk (OrderHom.id), homMk (OrderHom.id)) =_
  rw [homMk_id, homMk_id, prod_id]

lemma toOrderHom_indexEqToIso_inv_fst_apply {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) (a : Fin (len (obj X j).1)) :
    (toOrderHom (indexEqToIso h).inv.1) a = ⟨a.val, by subst h; exact a.prop⟩ := by
  simp [indexEqToIso, toOrderHom_homMk]
  rw [Fin.eq_iff_veq]
  rfl

lemma toOrderHom_indexEqToIso_inv_snd_apply {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) (a : Fin (len (obj X j).2)) :
    (toOrderHom (indexEqToIso h).inv.2) a = ⟨a.val, by subst h; exact a.prop⟩ := by
  simp [indexEqToIso, toOrderHom_homMk]
  rw [Fin.eq_iff_veq]
  rfl

lemma indexEqToIso_inv_comp_symm_inv {X : WithInitial SimplexCategory}
    {i j : Fin (Nat.succ (len X))} (h : i = j) :
    (indexEqToIso h).inv ≫ (indexEqToIso h.symm).inv = 𝟙 _ := by
  rw [prod_id]
  simp [indexEqToIso]
  apply And.intro <;>
    apply Hom.exe
    <;> apply OrderHom.ext
    <;> funext a
    <;> rw [toOrderHom_comp, toOrderHom_homMk, toOrderHom_homMk, Fin.eq_iff_veq]
  · have h : (toOrderHom (𝟙 (obj X j).1)) = OrderHom.id := by
      rw [toOrderHom_id]
    simp [h]
    rfl
  · have h : (toOrderHom (𝟙 (obj X j).2)) = OrderHom.id := by
      rw [toOrderHom_id]
    simp [h]
    rfl

lemma join_split_len (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    len X = len (join.obj (Split.obj X i))  := by
  rw [len_of_join]
  simp [Split.obj]
  rw [len_mk, len_mk]
  omega

/-- An isomorphism between an object and the join of a split of that object. -/
def joinSplitIso (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    X ≅ join.obj (Split.obj X i) := lenIso (Split.join_split_len X i)

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

/-- Given a morphism `f : X ⟶ Y` and a `i` in `Fin (Nat.succ (len Y))`, the element `p` of
`Fin (Nat.succ (len X))` specifying the value to split `X` at in order to generate a
morphism `obj X p` to `obj Y i` from `f`.  -/
def sourceValue {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    Fin (Nat.succ (len X)) :=
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  match k with
  | some k => k.castSucc
  | none => Fin.last (len X)

lemma sourceValue_of_iso_hom {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len X))) :
    sourceValue f.hom i = ⟨i.val, by rw [len_iso f]; exact i.prop⟩ := by
  simp [sourceValue]
  let k := Fin.find (fun a => i ≤ (toOrderHom f.hom a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f.hom a).castSucc) = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    let hkl := hk.left
    rw [toOrderHomIso_apply f] at hkl
    simp [Fin.le_def] at hkl
    let hkr := hk.right ⟨i, Nat.lt_of_le_of_lt hkl x.prop⟩
    rw [toOrderHomIso_apply f] at hkr
    simp [Fin.le_def] at hkr
    simp [Fin.eq_iff_veq]
    exact Nat.le_antisymm hkr hkl
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    ext
    simp only [Fin.val_last]
    match X, Y with
    | star, star =>
      simp [len]
    | of x, of y =>
      have h1 := hk (Fin.last (y.len))
      rw [toOrderHomIso_apply f] at h1
      simp  [Fin.lt_def] at h1
      have ht := Fin.is_le i
      simp [← len_iso f] at ht
      exact Nat.le_antisymm h1 ht

lemma sourceValue_of_iso_inv {X Y : WithInitial SimplexCategory} (f : Y ≅ X)
    (i : Fin (Nat.succ (len Y))) :
    sourceValue f.inv i = ⟨i.val, by rw [← len_iso f]; exact i.prop⟩ := by
  change sourceValue (f.symm).hom i =_
  rw [sourceValue_of_iso_hom]

lemma sourceValue_of_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    sourceValue (𝟙 X) i = i := by
  change sourceValue (Iso.refl X).hom i = i
  rw [sourceValue_of_iso_hom]

lemma toOrderHom_apply_on_lt_sourceValue {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y)))  (a : Fin (len X)) (ha : a.castSucc < sourceValue f i) :
    ((toOrderHom f) a).castSucc < i := by
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact Fin.not_le.mp ((hk.right a).mt (Fin.not_le.mpr ha))
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    exact Fin.not_le.mp (hk a)

lemma toOrderHom_apply_on_sourceValue_le {X Y : WithInitial SimplexCategory} (f : X ⟶ Y)
    (i : Fin (Nat.succ (len Y)))  (a : Fin (len X)) (ha : sourceValue f i ≤  a.castSucc):
    i ≤ ((toOrderHom f) a).castSucc  := by
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact hk.left.trans ((toOrderHom f).monotone' ha )
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    rw [Fin.eq_iff_veq] at ha
    simp at ha
    omega

lemma toOrderHom_apply_on_lt_sourceValue' {X Y : WithInitial SimplexCategory} {f : X ⟶ Y}
    {i : Fin (Nat.succ (len Y))} {a : Fin (len X)} (ha : a.val < len (obj X (sourceValue f i)).1) :
    ((toOrderHom f) a).val < len (obj Y i).1 := by
  simp_all [obj, len_mk]
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    exact Fin.not_le.mp ((hk.right a).mt (Fin.not_le.mpr ha))
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    exact Fin.not_le.mp (hk a)

lemma toOrderHom_apply_on_sourceValue_le' {X Y : WithInitial SimplexCategory} {f : X ⟶ Y}
    {i : Fin (Nat.succ (len Y))}  {a : Fin (len X)}
    (ha : len (obj X (sourceValue f i)).1 ≤ a.val) :
    len (obj Y i).1 ≤ ((toOrderHom f) a).val  := by
  simp_all [obj, len_mk]
  let k := Fin.find (fun a => i ≤ (toOrderHom f a).castSucc)
  have hk : Fin.find (fun a => i ≤ (toOrderHom f a).castSucc) = k := rfl
  simp [sourceValue, hk] at ha
  match k with
  | some k =>
    simp_all
    rw [Fin.find_eq_some_iff] at hk
    have hkl := hk.left
    let hm := (toOrderHom f).monotone' ha
    rw [Fin.le_def] at hm hkl
    simp at hm hkl
    exact hkl.trans hm
  | none =>
    simp_all
    rw [Fin.find_eq_none_iff] at hk
    omega

lemma sourceValue_of_comp  {X Y Z: WithInitial SimplexCategory} (f : X ⟶ Y) (g : Y ⟶ Z)
    (i : Fin (Nat.succ (len Z))) :
    sourceValue f (sourceValue g i) = sourceValue (f ≫ g) i := by
  rw [sourceValue, sourceValue, sourceValue]
  repeat apply congrFun
  apply congrArg
  let k := Fin.find fun a ↦ i ≤ Fin.castSucc ((toOrderHom g) a)
  have hk : Fin.find fun a ↦ i ≤ Fin.castSucc ((toOrderHom g) a) = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    simp only [Fin.castSucc_le_castSucc_iff, toOrderHom_comp, OrderHom.comp_coe,
      Function.comp_apply]
    let k2 := (Fin.find fun a ↦ x ≤ (toOrderHom f) a)
    have hk2 : (Fin.find fun a ↦ x ≤ (toOrderHom f) a) =k2  := rfl
    rw [hk2]
    match k2 with
    | some x2 =>
      symm
      rw [Fin.find_eq_some_iff]
      rw [Fin.find_eq_some_iff] at hk2
      apply And.intro
      · exact hk.left.trans ((toOrderHom g).monotone' hk2.left )
      · intro j hj
        exact hk2.right j (hk.right ((toOrderHom f) j) hj)
    | none =>
      symm
      rw [Fin.find_eq_none_iff]
      rw [Fin.find_eq_none_iff] at hk2
      intro j
      simp
      by_contra hn
      simp at hn
      exact hk2 j (hk.right ((toOrderHom f) j) hn )
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    simp
    have h1 : Fin.find fun a ↦ Fin.castSucc ((toOrderHom f) a) = Fin.last (len Y) = none := by
      rw [Fin.find_eq_none_iff]
      intro i
      have := ((toOrderHom f) i).prop
      rw [Fin.eq_iff_veq]
      omega
    rw [h1]
    symm
    rw [Fin.find_eq_none_iff, toOrderHom_comp]
    exact fun l => hk ((toOrderHom f) l)

lemma splitValue_of_join {X Y : WithInitial SimplexCategory × WithInitial SimplexCategory}
    (f : X ⟶ Y) : Split.sourceValue (join.map f) ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    = ⟨len X.1, len_of_fst_lt_len_of_join_plus_one X⟩ := by
  simp only [Split.sourceValue]
  let k :=  Fin.find fun a => ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    ≤  ((toOrderHom (join.map f)) a).castSucc
  have hk : Fin.find fun a => ⟨len Y.1, len_of_fst_lt_len_of_join_plus_one Y⟩
    ≤  ((toOrderHom (join.map f)) a).castSucc  = k := rfl
  rw [hk]
  match k with
  | some x =>
    rw [Fin.find_eq_some_iff] at hk
    by_cases hX2 : len X.2 = 0
    · let hkl := hk.left
      rw [Fin.le_def] at hkl
      simp at hkl
      have hx := x.prop
      simp only [len_of_join] at hx
      rw [hX2, add_zero] at hx
      rw [toOrderHom_join_apply_on_lt_fst f x hx] at hkl
      exact ((Nat.not_le.mpr ((toOrderHom f.1) ⟨x.val, hx⟩).prop) hkl).elim
    · have hx := @Nat.lt_add_of_pos_right (len X.2) (len X.1) (Nat.pos_of_ne_zero hX2)
      rw [← len_of_join] at hx
      let X1 : Fin (len (join.obj X)) := ⟨len X.1, hx⟩
      have hkr := hk.right X1
      rw [Fin.le_def, Fin.coe_castSucc, toOrderHom_join_apply_on_fst_le] at hkr
      have hkr2 : x ≤ X1 := hkr (Nat.le_add_left (len Y.1) _)
      have hkl := hk.left
      by_cases hlt : x < X1
      · rw [Fin.le_def, Fin.coe_castSucc, toOrderHom_join_apply_on_lt_fst f x hlt] at hkl
        exact ((Nat.not_le.mpr ((toOrderHom f.1) ⟨ x,hlt ⟩).prop) hkl).elim
      · change Fin.castSucc x = Fin.castSucc X1
        refine Fin.castSucc_inj.mpr ?_
        rw [Fin.eq_iff_veq]
        rw [Fin.le_def] at hkr2
        rw [Fin.lt_def, ← Nat.not_le] at  hlt
        simp at hlt hkr2
        exact Nat.le_antisymm hkr2 hlt
      rfl
  | none =>
    rw [Fin.find_eq_none_iff] at hk
    simp at hk
    rw [Fin.eq_iff_veq]
    simp [len_of_join]
    by_contra hX2
    have hx := @Nat.lt_add_of_pos_right (len X.2) (len X.1) (Nat.pos_of_ne_zero hX2)
    rw [← len_of_join] at hx
    refine (Nat.not_le.mpr (Fin.lt_def.mp (hk ⟨len X.1, hx⟩))) ?_
    rw [Fin.coe_castSucc, toOrderHom_join_apply_on_fst_le]
    exact  Nat.le_add_left (len Y.1) _
    rfl

/-- Given a morphism `f : X ⟶ Y`, and an element of `Fin (Nat.succ (len Y))`, the corresponding
morphism between `obj X (sourceValue f i) ` and `obj Y i`. -/
def map {X Y : WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y))) :
    obj X (sourceValue f i) ⟶ obj Y i:=
  (homMk {
    toFun := fun a =>
      preimageIncl₁ (toOrderHom f (incl₁ a)) (toOrderHom_apply_on_lt_sourceValue' (a.prop))
    monotone' := by
      intro a b h
      apply (toOrderHom f).monotone'
      exact h
  },
  homMk {
    toFun := fun a => preimageIncl₂ (toOrderHom f (incl₂ a)) (by
      refine toOrderHom_apply_on_sourceValue_le' ?_
      simp [obj, len_mk, incl₂]
    )
    monotone' := by
      intro a b h
      simp [preimageIncl₂]
      rw [tsub_add_cancel_iff_le.mpr]
      apply (toOrderHom f).monotone'
      simp [incl₂]
      exact h
      apply toOrderHom_apply_on_sourceValue_le'
      simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk, incl₂, le_add_iff_nonneg_left,
        zero_le]
  })

lemma map_id {X : WithInitial SimplexCategory} (i : Fin (Nat.succ (len X))) :
    (indexEqToIso (sourceValue_of_id i)).inv ≫ map (𝟙 X) i = 𝟙 (obj X i) := by
  simp [map, indexEqToIso]
  rw [prod_id, Prod.mk.injEq]
  rw [← homMk_comp, ← homMk_comp, ← @homMk_id (obj X i).1, ← @homMk_id (obj X i).2]
  apply And.intro
  match X with
  | star => rfl
  | of x => rfl
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
  | star, star, star, f, g => rfl
  | star, star, of z, f, g => rfl
  | star, of y, of z, f, g => rfl
  | of x, of y, of z, f, g =>
     simp [map, indexEqToIso, ← homMk_comp]
     apply And.intro
     all_goals apply congrArg
     rfl
     apply OrderHom.ext
     funext a
     simp only [obj, Fin.val_rev, preimageIncl₂, toOrderHom_comp, incl₂, OrderHom.comp_coe,
       Function.comp_apply, Nat.succ_sub_succ_eq_sub, len_mk, (sourceValue_of_comp f g i),
       Fin.eq_iff_veq]
     change ((toOrderHom g) ((toOrderHom f) ⟨a.val + (sourceValue (f ≫ g) i).val, _⟩)).val - i.val =
       ((toOrderHom g) ⟨((toOrderHom f) ⟨a.val + (sourceValue (f ≫ g) i).val, _⟩).val
        - (sourceValue g i).val + (sourceValue g i).val, _⟩)  - i.val
     apply congrFun
     repeat apply congrArg
     simp [Fin.eq_iff_veq, ← (sourceValue_of_comp f g i)]
     rw [tsub_add_cancel_of_le]
     apply toOrderHom_apply_on_sourceValue_le
     simp only [Fin.le_def, Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le]

lemma toOrderHom_on_lt_fst_eq {X Y: WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len Y))
    (ha : a.val < len (obj Y (sourceValue f i)).1) :
    (toOrderHom f a).val = (toOrderHom (map f i).1 (preimageIncl₁ a ha)).val := by
  simp [map]
  rw [toOrderHom_homMk]
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
  have hx {n m  : ℕ } (f : Fin n → Fin m ) (mo : Monotone f) (a : Fin  n) :
    (({toFun := f, monotone' := mo } : Fin n →o Fin m) a).val = (f a).val := rfl
  nth_rewrite 2 [hx]
  simp only [obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk, OrderHom.toFun_eq_coe]
  rw [tsub_add_cancel_iff_le.mpr]
  repeat apply congrArg
  rw [Fin.eq_iff_veq]
  refine (tsub_add_cancel_iff_le.mpr (Nat.not_lt.mp ?_)).symm
  simp [obj, len_mk] at ha
  exact Nat.not_lt.mpr ha
  apply toOrderHom_apply_on_sourceValue_le
  simp only [Fin.le_def, Fin.castSucc_mk, le_add_iff_nonneg_left, zero_le, incl₂]

lemma toOrderHom_snd_apply {X Y : WithInitial SimplexCategory} (f : Y ⟶ X)
    (i : Fin (Nat.succ (len X))) (a : Fin (len (obj Y (sourceValue f i)).2)) :
    (toOrderHom (map f i).2 a).val
    = ((toOrderHom f) (incl₂ a) ).val - i.val := by
  rw [toOrderHom_on_fst_le_eq f i (incl₂ a)]
  simp [incl₂, preimageIncl₂, obj, len_mk]
  simp [incl₂, obj, len_mk]

/-- Given a map `f : Z ⟶ Y`, the corresponding map from `hom Y X i` to `hom Z X i`. -/
def homMap {Y Z : WithInitial SimplexCategory} (X : WithInitial SimplexCategory)
    (i : Fin (Nat.succ (len X))) (f : Z ⟶ Y) (s : hom Y X i) : hom Z X i :=
  hom.split (sourceValue f s.1) (map f s.1 ≫ s.2)

/-- An equivalance between the type `hom X Y i` and the type `Y ⟶ X`. In the forward direction
maps are joined and in the inverse direction maps are split based in the index `i`. -/
def splitJoinUnitEquiv (X Y : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X))) :
    hom Y X i ≃ (Y ⟶ X) where
  toFun s :=
    match s with
    | Split.hom.split p fs =>
    (Split.joinSplitIso Y p).hom ≫ join.map fs ≫ (Split.joinSplitIso X i).inv
  invFun f := Split.hom.split (Split.sourceValue f i) (Split.map f i)
  left_inv := by
    intro s
    have hs : s.1.val =
        (⟨len (Split.obj Y s.1).1,
        len_of_fst_lt_len_of_join_plus_one (Split.obj Y s.1)⟩ : Fin _).val := by
      simp only [Split.obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk]
    refine Split.hom_ext _ _ _ _ _ ?_ ?_
    simp
    rw [← Split.sourceValue_of_comp, ← Split.sourceValue_of_comp]
    rw [Split.sourceValue_of_iso_hom (Split.joinSplitIso Y s.1)]
    rw [Split.sourceValue_of_iso_inv (Split.joinSplitIso X i)]
    simp [Fin.eq_iff_veq]
    rw [hs, ← (Split.splitValue_of_join s.2)]
    repeat apply congrArg
    simp only [Split.obj, Fin.val_rev, Nat.succ_sub_succ_eq_sub, len_mk]
    apply Prod.ext
    all_goals apply Hom.exe
    rw [prod_comp_fst, toOrderHom_comp]
    apply OrderHom.ext
    funext a
    simp
    rw [Split.toOrderHom_indexEqToIso_inv_fst_apply, Fin.eq_iff_veq, Split.toOrderHom_fst_apply]
    simp [Split.incl₁, toOrderHom_comp, Split.joinSplitIso, toOrderHom_of_lenIso_hom,
      toOrderHom_of_lenIso_inv]
    rw [WithInitial.toOrderHom_fst_apply]
    rw [prod_comp_snd, toOrderHom_comp]
    apply OrderHom.ext
    funext a
    simp
    rw [Split.toOrderHom_indexEqToIso_inv_snd_apply, Fin.eq_iff_veq, Split.toOrderHom_snd_apply]
    simp only [Split.joinSplitIso, toOrderHom_comp, toOrderHom_of_lenIso_inv,
      toOrderHom_of_lenIso_hom, Split.incl₂, OrderHom.comp_coe, OrderHomClass.coe_coe,
      Function.comp_apply, Fin.castIso_apply, Fin.cast_mk, Fin.coe_cast]
    rw [WithInitial.toOrderHom_snd_apply]
    simp [Split.obj, len_mk]
    apply congrFun
    repeat apply congrArg
    simp [Fin.eq_iff_veq, Split.obj, len_mk]
    rw [← Split.sourceValue_of_comp, ← Split.sourceValue_of_comp, Split.sourceValue_of_iso_hom]
    change (Split.sourceValue (join.map s.2) _).val =_
    rw [hs, ← (Split.splitValue_of_join s.2)]
    repeat apply congrArg
    simp [Split.sourceValue_of_iso_inv, Split.obj, len_mk]
  right_inv := by
    intro f
    apply Hom.exe
    rw [toOrderHom_comp, toOrderHom_comp]
    rw [Split.joinSplitIso, Split.joinSplitIso]
    rw [toOrderHom_of_lenIso_hom, toOrderHom_of_lenIso_inv]
    apply OrderHom.ext
    funext a
    rw [Fin.eq_iff_veq]
    simp
    by_cases ha : a.val < len (Split.obj Y (Split.sourceValue f i)).1
    rw [Split.toOrderHom_on_lt_fst_eq f i a ha]
    exact toOrderHom_join_apply_on_lt_fst (Split.map f i)
      (Fin.cast (Split.join_split_len Y (Split.sourceValue f i)) a) ha
    rw [Split.toOrderHom_on_fst_le_eq f i a (Nat.not_lt.mp ha)]
    rw [toOrderHom_join_apply_on_fst_le (Split.map f i) (Fin.cast _ a)]
    simp [Split.obj, len_mk, preimageIncl₂]
    simp_all [obj, len_mk]

lemma splitJoinUnitEquiv_naturality (X : WithInitial SimplexCategory) (i : Fin (Nat.succ (len X)))
    {Z Y : WithInitial SimplexCategory} (f : Z ⟶ Y) :
    ((Split.splitJoinUnitEquiv X Z i).symm).toFun ∘ (CategoryStruct.comp f) =
    (homMap X i f) ∘ ((Split.splitJoinUnitEquiv X Y i).symm).toFun := by
  funext s
  refine Split.hom_ext _ _ _ _ _ ?_ ?_
  exact (Split.sourceValue_of_comp f s i).symm
  simp only [Split.splitJoinUnitEquiv,  Equiv.toFun_as_coe, Equiv.coe_fn_symm_mk,
    Function.comp_apply, homMap,  Fin.val_rev, Prod.mk.injEq]
  rw [Split.map_comp]
  change _ = Split.map f (Split.sourceValue s i) ≫ Split.map s i
  repeat rw [← Category.assoc]
  apply congrFun
  apply congrArg
  have h : Split.map f (Split.sourceValue s i) = 𝟙 _ ≫ Split.map f (Split.sourceValue s i) := by
    simp
  rw [h]
  repeat rw [← Category.assoc]
  apply congrFun
  apply congrArg
  rw [Category.comp_id]
  rw [Split.indexEqToIso_inv_comp_symm_inv]
  rfl

lemma splitJoinUnitEquiv_naturality_equiv (X : WithInitial SimplexCategory)
    (i : Fin (Nat.succ (len X))) {Z Y : WithInitial SimplexCategory} (f : Z ⟶ Y) :
    (Equiv.toIso (Split.splitJoinUnitEquiv X Z i).symm).hom ∘ (CategoryStruct.comp f) =
    (homMap X i f) ∘ (Equiv.toIso (Split.splitJoinUnitEquiv X Y i).symm).hom := by
  exact Split.splitJoinUnitEquiv_naturality X i f
end Split
end WithInitial
end SimplexCategory
