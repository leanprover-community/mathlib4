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
def inclSucc₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (Nat.succ (len (obj X i).1))) : Fin (Nat.succ (len X)) := ⟨a.val, inclSucc₁_cond a⟩

/-- The preimage of an object in `Fin (len X)` under `incl₁` when it exists. -/
def preimageIncl₁ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len X)) (ha : a.val < len (obj X i).1) : Fin (len (obj X i).1) := ⟨a.val, ha⟩

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
def incl₂ {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (len (obj X i).2)) : Fin (len X) := ⟨a.val + i.val, incl₂_cond a⟩

lemma inclSucc₂_cond {Y : WithInitial SimplexCategory} {p : Fin (Nat.succ (len Y))}
    (a : Fin (Nat.succ (len (obj Y p).2))) : a.val + p.val < Nat.succ (len Y) := by
  have ha := a.prop
  unfold obj at ha
  simp [len_mk] at ha
  omega

/-- The inclusion of `Fin (Nat.succ (len (obj X i).1))` into `Fin (Nat.succ (len X))`. -/
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

def preimageInclSucc₂  {X : WithInitial SimplexCategory} {i : Fin (Nat.succ (len X))}
    (a : Fin (Nat.succ (len X))) (ha : len (obj X i).1 ≤ a.val) :
    Fin (Nat.succ (len (obj X i).2)) := ⟨a.val - len (obj X i).1 , preimageInclSucc₂_cond a ha⟩

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
    rfl
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

def assocTypeMap1 {X Y: WithInitial SimplexCategory} (f : X ⟶ Y) (p : assocFiberType1 Y) :
    assocFiberType1 X :=
  assocFiberType1.as (sourceValue f p.1) (sourceValue (map f p.1).1 p.2)

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
  sorry


lemma sourceValue_map₂ {X Y: WithInitial SimplexCategory} (f : X ⟶ Y) (i : Fin (Nat.succ (len Y)))
    (p : Fin (Nat.succ (len (obj Y i).1))) :
     preimageInclSucc₂' (sourceValue f i) (sourceValue (map f i).1 p) =
     sourceValue (map f (inclSucc₁ p)).2 (preimageInclSucc₂' i p) := by
  sorry
  -- Fin (Nat.succ (len (obj X (inclSucc₁ (sourceValue (map f i).1 p))).2))
  -- Fin (Nat.succ (len (obj X (sourceValue f (inclSucc₁ p))).2))

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
