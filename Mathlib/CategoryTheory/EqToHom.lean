/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Opposites

/-!
# Morphisms from equations between objects.

When working categorically, sometimes one encounters an equation `h : X = Y` between objects.

Your initial aversion to this is natural and appropriate:
you're in for some trouble, and if there is another way to approach the problem that won't
rely on this equality, it may be worth pursuing.

You have two options:
1. Use the equality `h` as one normally would in Lean (e.g. using `rw` and `subst`).
   This may immediately cause difficulties, because in category theory everything is dependently
   typed, and equations between objects quickly lead to nasty goals with `eq.rec`.
2. Promote `h` to a morphism using `eqToHom h : X ⟶ Y`, or `eqToIso h : X ≅ Y`.

This file introduces various `simp` lemmas which in favourable circumstances
result in the various `eqToHom` morphisms to drop out at the appropriate moment!
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category theory universes].
namespace CategoryTheory

open Opposite

/-- An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `𝟙 _`
which usually leads to dependent type theory hell.
-/
def eqToHom {C : Type u₁} [CategoryStruct.{v₁} C] {X Y : C} (p : X = Y) :
    X ⟶ Y := by
  rw [p]
  exact 𝟙 _

@[simp]
theorem eqToHom_refl {C : Type u₁} [CategoryStruct.{v₁} C] (X : C) (p : X = X) :
    eqToHom p = 𝟙 X :=
  rfl

variable {C : Type u₁} [Category.{v₁} C]

@[reassoc (attr := simp)]
theorem eqToHom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToHom p ≫ eqToHom q = eqToHom (p.trans q) := by
  cases p
  cases q
  simp

/-- `eqToHom h` is heterogeneously equal to the identity of its domain. -/
lemma eqToHom_heq_id_dom (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 X := by
  subst h; rfl

/-- `eqToHom h` is heterogeneously equal to the identity of its codomain. -/
lemma eqToHom_heq_id_cod (X Y : C) (h : X = Y) : eqToHom h ≍ 𝟙 Y := by
  subst h; rfl

/-- Two morphisms are conjugate via eqToHom if and only if they are heterogeneously equal.
Note this used to be in the Functor namespace, where it doesn't belong. -/
theorem conj_eqToHom_iff_heq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) :
    f = eqToHom h ≫ g ≫ eqToHom h'.symm ↔ f ≍ g := by
  cases h
  cases h'
  simp

theorem conj_eqToHom_iff_heq' {C} [Category* C] {W X Y Z : C}
    (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : Z = X) :
    f = eqToHom h ≫ g ≫ eqToHom h' ↔ f ≍ g := conj_eqToHom_iff_heq _ _ _ h'.symm

theorem comp_eqToHom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
    f ≫ eqToHom p = g ↔ f = g ≫ eqToHom p.symm :=
  { mp h := by simp [← h]
    mpr h := by simp [eq_whisker h (eqToHom p)] }

theorem eqToHom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
    eqToHom p ≫ g = f ↔ g = eqToHom p.symm ≫ f :=
  { mp h := by simp [← h]
    mpr h := by simp [h] }

theorem eqToHom_comp_heq {C} [Category* C] {W X Y : C}
    (f : Y ⟶ X) (h : W = Y) : eqToHom h ≫ f ≍ f := by
  rw [← conj_eqToHom_iff_heq _ _ h rfl, eqToHom_refl, Category.comp_id]

@[simp] theorem eqToHom_comp_heq_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    eqToHom h ≫ f ≍ g ↔ f ≍ g :=
  ⟨(eqToHom_comp_heq ..).symm.trans, (eqToHom_comp_heq ..).trans⟩

@[simp] theorem heq_eqToHom_comp_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : Y ⟶ X) (g : Z ⟶ Z') (h : W = Y) :
    g ≍ eqToHom h ≫ f ↔ g ≍ f :=
  ⟨(·.trans (eqToHom_comp_heq ..)), (·.trans (eqToHom_comp_heq ..).symm)⟩

theorem comp_eqToHom_heq {C} [Category* C] {X Y Z : C}
    (f : X ⟶ Y) (h : Y = Z) : f ≫ eqToHom h ≍ f := by
  rw [← conj_eqToHom_iff_heq' _ _ rfl h, eqToHom_refl, Category.id_comp]

@[simp] theorem comp_eqToHom_heq_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    f ≫ eqToHom h ≍ g ↔ f ≍ g :=
  ⟨(comp_eqToHom_heq ..).symm.trans, (comp_eqToHom_heq ..).trans⟩

@[simp] theorem heq_comp_eqToHom_iff {C} [Category* C] {W X Y Z Z' : C}
    (f : X ⟶ Y) (g : Z ⟶ Z') (h : Y = W) :
    g ≍ f ≫ eqToHom h ↔ g ≍ f :=
  ⟨(·.trans (comp_eqToHom_heq ..)), (·.trans (comp_eqToHom_heq ..).symm)⟩

theorem heq_comp {C} [Category* C] {X Y Z X' Y' Z' : C}
    {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}
    (eq1 : X = X') (eq2 : Y = Y') (eq3 : Z = Z')
    (H1 : f ≍ f') (H2 : g ≍ g') :
    f ≫ g ≍ f' ≫ g' := by
  grind

variable {β : Sort*}

/-- We can push `eqToHom` to the left through families of morphisms. -/
@[reassoc (attr := simp)]
theorem eqToHom_naturality {f g : β → C} (z : ∀ b, f b ⟶ g b) {j j' : β} (w : j = j') :
    z j ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ z j' := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
@[reassoc (attr := simp)]
theorem eqToHom_iso_hom_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).hom ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').hom := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
@[reassoc (attr := simp)]
theorem eqToHom_iso_inv_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).inv ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').inv := by
  cases w
  simp

/-- Reducible form of `congrArg_mpr_hom_left` -/
@[simp]
theorem congrArg_cast_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    cast (congrArg (fun W : C => W ⟶ Z) p.symm) q = eqToHom p ≫ q := by
  cases p
  simp

/-- If we (perhaps unintentionally) perform equational rewriting on
the source object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
theorem congrArg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    (congrArg (fun W : C => W ⟶ Z) p).mpr q = eqToHom p ≫ q := by
  cases p
  simp

/-- Reducible form of `congrArg_mpr_hom_right` -/
@[simp]
theorem congrArg_cast_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    cast (congrArg (fun W : C => X ⟶ W) q.symm) p = p ≫ eqToHom q.symm := by
  cases q
  simp

/-- If we (perhaps unintentionally) perform equational rewriting on
the target object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eqToHom`.

It may be advisable to introduce any necessary `eqToHom` morphisms manually,
rather than relying on this lemma firing.
-/
theorem congrArg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    (congrArg (fun W : C => X ⟶ W) q).mpr p = p ≫ eqToHom q.symm := by
  cases q
  simp

/-- An equality `X = Y` gives us an isomorphism `X ≅ Y`.

It is typically better to use this, rather than rewriting by the equality then using `Iso.refl _`
which usually leads to dependent type theory hell.
-/
def eqToIso {X Y : C} (p : X = Y) : X ≅ Y :=
  ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩

@[simp]
theorem eqToIso.hom {X Y : C} (p : X = Y) : (eqToIso p).hom = eqToHom p :=
  rfl

@[simp]
theorem eqToIso.inv {X Y : C} (p : X = Y) : (eqToIso p).inv = eqToHom p.symm :=
  rfl

@[simp]
theorem eqToIso_refl {X : C} (p : X = X) : eqToIso p = Iso.refl X :=
  rfl

@[simp]
theorem eqToIso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToIso p ≪≫ eqToIso q = eqToIso (p.trans q) := by ext; simp

@[simp]
theorem eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h).op = eqToHom (congr_arg op h.symm) := by
  cases h
  rfl

@[simp]
theorem eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) :
    (eqToHom h).unop = eqToHom (congr_arg unop h.symm) := by
  cases h
  rfl

instance {X Y : C} (h : X = Y) : IsIso (eqToHom h) :=
  (eqToIso h).isIso_hom

@[simp]
theorem inv_eqToHom {X Y : C} (h : X = Y) : inv (eqToHom h) = eqToHom h.symm := by
  cat_disch

variable {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f,
      F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm := by cat_disch) :
    F = G := by
  match F, G with
  | mk F_obj _ _ _, mk G_obj _ _ _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simpa using h_map X Y f

lemma ext_of_iso {F G : C ⥤ D} (e : F ≅ G) (hobj : ∀ X, F.obj X = G.obj X)
    (happ : ∀ X, e.hom.app X = eqToHom (hobj X) := by cat_disch) : F = G :=
  Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y), e.hom.naturality f, happ, happ, Category.assoc,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

/-- Proving equality between functors using heterogeneous equality. -/
theorem hext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G :=
  Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 <| h_map _ _ f

-- Using equalities between functors.
theorem congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X := by rw [h]

@[reassoc]
theorem congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_obj h Y).symm := by
  subst h; simp

theorem congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
    (hY : F.obj Y = G.obj Y)
    (h₂ : F.map e.hom = eqToHom (by rw [hX]) ≫ G.map e.hom ≫ eqToHom (by rw [hY])) :
    F.map e.inv = eqToHom (by rw [hY]) ≫ G.map e.inv ≫ eqToHom (by rw [hX]) := by
  simp only [← IsIso.Iso.inv_hom e, Functor.map_inv, h₂, IsIso.inv_comp, inv_eqToHom,
    Category.assoc]

section HEq

-- Composition of functors and maps w.r.t. heq
variable {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

theorem map_comp_heq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
    (hf : F.map f ≍ G.map f) (hg : F.map g ≍ G.map g) :
    F.map (f ≫ g) ≍ G.map (f ≫ g) := by
  rw [F.map_comp, G.map_comp]
  congr

theorem map_comp_heq' (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) :
    F.map (f ≫ g) ≍ G.map (f ≫ g) := by
  rw [Functor.hext hobj fun _ _ => hmap]

theorem precomp_map_heq (H : E ⥤ C) (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) {X Y : E}
    (f : X ⟶ Y) : (H ⋙ F).map f ≍ (H ⋙ G).map f :=
  hmap _

theorem postcomp_map_heq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
    (hmap : F.map f ≍ G.map f) : (F ⋙ H).map f ≍ (G ⋙ H).map f := by
  dsimp
  congr

theorem postcomp_map_heq' (H : D ⥤ E) (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), F.map f ≍ G.map f) :
    (F ⋙ H).map f ≍ (G ⋙ H).map f := by rw [Functor.hext hobj fun _ _ => hmap]

theorem hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : F.map f ≍ G.map f := by
  rw [h]

end HEq

end Functor

/-- This is not always a good idea as a `@[simp]` lemma,
as we lose the ability to use results that interact with `F`,
e.g. the naturality of a natural transformation.

In some files it may be appropriate to use `attribute [local simp] eqToHom_map`, however.
-/
theorem eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congr_arg F.obj p) := by cases p; simp

@[reassoc (attr := simp)]
theorem eqToHom_map_comp (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.map (eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToHom <| p.trans q) := by cat_disch

/-- See the note on `eqToHom_map` regarding using this as a `simp` lemma.
-/
theorem eqToIso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.mapIso (eqToIso p) = eqToIso (congr_arg F.obj p) := by ext; cases p; simp

@[simp]
theorem eqToIso_map_trans (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.mapIso (eqToIso p) ≪≫ F.mapIso (eqToIso q) = F.mapIso (eqToIso <| p.trans q) := by cat_disch

@[simp]
theorem eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X) := by subst h; rfl

theorem NatTrans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
    α.app X = F.map (eqToHom h) ≫ α.app Y ≫ G.map (eqToHom h.symm) := by
  rw [α.naturality_assoc]
  simp [eqToHom_map]

theorem eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : f = eqToHom rfl ≫ f ≫ eqToHom rfl := by
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]

theorem dcongr_arg {ι : Type*} {F G : ι → C} (α : ∀ i, F i ⟶ G i) {i j : ι} (h : i = j) :
    α i = eqToHom (congr_arg F h) ≫ α j ≫ eqToHom (congr_arg G h.symm) := by
  subst h
  simp

@[simp]
lemma InducedCategory.eqToHom_hom {C D : Type*} [Category D] {F : C → D}
    {X Y : InducedCategory D F} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

@[simp]
lemma ObjectProperty.eqToHom_hom {C : Type*} [Category C] {P : ObjectProperty C}
    {X Y : P.FullSubcategory} (h : X = Y) :
    (eqToHom h).hom = eqToHom (by subst h; rfl) := by
  subst h
  rfl

/-- If `T ≃ D` is a bijection and `D` is a category, then
`InducedCategory D e` is equivalent to `D`. -/
@[simps]
def Equivalence.induced {T : Type*} (e : T ≃ D) :
    InducedCategory D e ≌ D where
  functor := inducedFunctor e
  inverse :=
    { obj := e.symm
      map f := InducedCategory.homMk (eqToHom (by simp) ≫ f ≫ eqToHom (by simp)) }
  unitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))
  counitIso := NatIso.ofComponents (fun _ ↦ eqToIso (by simp))

end CategoryTheory
