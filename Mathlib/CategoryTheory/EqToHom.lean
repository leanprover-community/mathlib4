/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison
-/
import Mathlib.CategoryTheory.Opposites

#align_import category_theory.eq_to_hom from "leanprover-community/mathlib"@"dc6c365e751e34d100e80fe6e314c3c3e0fd2988"

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

universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [CategoryTheory universes].
namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C]

/-- An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `𝟙 _`
which usually leads to dependent type theory hell.
-/
def eqToHom {X Y : C} (p : X = Y) : X ⟶ Y := by rw [p]; exact 𝟙 _
#align category_theory.eq_to_hom CategoryTheory.eqToHom

@[simp]
theorem eqToHom_refl (X : C) (p : X = X) : eqToHom p = 𝟙 X :=
  rfl
#align category_theory.eq_to_hom_refl CategoryTheory.eqToHom_refl

@[reassoc (attr := simp)]
theorem eqToHom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToHom p ≫ eqToHom q = eqToHom (p.trans q) := by
  cases p
  cases q
  simp
#align category_theory.eq_to_hom_trans CategoryTheory.eqToHom_trans

theorem comp_eqToHom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
    f ≫ eqToHom p = g ↔ f = g ≫ eqToHom p.symm :=
  { mp := fun h => h ▸ by simp
    mpr := fun h => by simp [eq_whisker h (eqToHom p)] }
#align category_theory.comp_eq_to_hom_iff CategoryTheory.comp_eqToHom_iff

theorem eqToHom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
    eqToHom p ≫ g = f ↔ g = eqToHom p.symm ≫ f :=
  { mp := fun h => h ▸ by simp
    mpr := fun h => h ▸ by simp [whisker_eq _ h] }
#align category_theory.eq_to_hom_comp_iff CategoryTheory.eqToHom_comp_iff

variable {β : Sort*}

/-- We can push `eqToHom` to the left through families of morphisms. -/
-- The simpNF linter incorrectly claims that this will never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
@[reassoc (attr := simp, nolint simpNF)]
theorem eqToHom_naturality {f g : β → C} (z : ∀ b, f b ⟶ g b) {j j' : β} (w : j = j') :
    z j ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ z j' := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
-- The simpNF linter incorrectly claims that this will never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
@[reassoc (attr := simp, nolint simpNF)]
theorem eqToHom_iso_hom_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).hom ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').hom := by
  cases w
  simp

/-- A variant on `eqToHom_naturality` that helps Lean identify the families `f` and `g`. -/
-- The simpNF linter incorrectly claims that this will never apply.
-- https://github.com/leanprover-community/mathlib4/issues/5049
@[reassoc (attr := simp, nolint simpNF)]
theorem eqToHom_iso_inv_naturality {f g : β → C} (z : ∀ b, f b ≅ g b) {j j' : β} (w : j = j') :
    (z j).inv ≫ eqToHom (by simp [w]) = eqToHom (by simp [w]) ≫ (z j').inv := by
  cases w
  simp

/- Porting note: simpNF complains about this not reducing but it is clearly used
in `congrArg_mpr_hom_left`. It has been no-linted. -/
/-- Reducible form of congrArg_mpr_hom_left -/
@[simp, nolint simpNF]
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
#align category_theory.congr_arg_mpr_hom_left CategoryTheory.congrArg_mpr_hom_left

/- Porting note: simpNF complains about this not reducing but it is clearly used
in `congrArg_mrp_hom_right`. It has been no-linted. -/
/-- Reducible form of `congrArg_mpr_hom_right` -/
@[simp, nolint simpNF]
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
#align category_theory.congr_arg_mpr_hom_right CategoryTheory.congrArg_mpr_hom_right

/-- An equality `X = Y` gives us an isomorphism `X ≅ Y`.

It is typically better to use this, rather than rewriting by the equality then using `Iso.refl _`
which usually leads to dependent type theory hell.
-/
def eqToIso {X Y : C} (p : X = Y) : X ≅ Y :=
  ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩
#align category_theory.eq_to_iso CategoryTheory.eqToIso

@[simp]
theorem eqToIso.hom {X Y : C} (p : X = Y) : (eqToIso p).hom = eqToHom p :=
  rfl
#align category_theory.eq_to_iso.hom CategoryTheory.eqToIso.hom

@[simp]
theorem eqToIso.inv {X Y : C} (p : X = Y) : (eqToIso p).inv = eqToHom p.symm :=
  rfl
#align category_theory.eq_to_iso.inv CategoryTheory.eqToIso.inv

@[simp]
theorem eqToIso_refl {X : C} (p : X = X) : eqToIso p = Iso.refl X :=
  rfl
#align category_theory.eq_to_iso_refl CategoryTheory.eqToIso_refl

@[simp]
theorem eqToIso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToIso p ≪≫ eqToIso q = eqToIso (p.trans q) := by ext; simp
#align category_theory.eq_to_iso_trans CategoryTheory.eqToIso_trans

@[simp]
theorem eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h).op = eqToHom (congr_arg op h.symm) := by
  cases h
  rfl
#align category_theory.eq_to_hom_op CategoryTheory.eqToHom_op

@[simp]
theorem eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) :
    (eqToHom h).unop = eqToHom (congr_arg unop h.symm) := by
  cases h
  rfl
#align category_theory.eq_to_hom_unop CategoryTheory.eqToHom_unop

instance {X Y : C} (h : X = Y) : IsIso (eqToHom h) :=
  (eqToIso h).isIso_hom

@[simp]
theorem inv_eqToHom {X Y : C} (h : X = Y) : inv (eqToHom h) = eqToHom h.symm := by
  aesop_cat
#align category_theory.inv_eq_to_hom CategoryTheory.inv_eqToHom

variable {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f,
      F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm := by aesop_cat) :
    F = G := by
  match F, G with
  | mk F_pre _ _ , mk G_pre _ _ =>
    match F_pre, G_pre with  -- Porting note: did not unfold the Prefunctor unlike Lean3
    | Prefunctor.mk F_obj _ , Prefunctor.mk G_obj _ =>
    obtain rfl : F_obj = G_obj := by
      ext X
      apply h_obj
    congr
    funext X Y f
    simpa using h_map X Y f
#align category_theory.functor.ext CategoryTheory.Functor.ext

lemma ext_of_iso {F G : C ⥤ D} (e : F ≅ G) (hobj : ∀ X, F.obj X = G.obj X)
    (happ : ∀ X, e.hom.app X = eqToHom (hobj X)) : F = G :=
  Functor.ext hobj (fun X Y f => by
    rw [← cancel_mono (e.hom.app Y), e.hom.naturality f, happ, happ, Category.assoc,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])

/-- Two morphisms are conjugate via eqToHom if and only if they are heterogeneously equal. -/
theorem conj_eqToHom_iff_heq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) :
    f = eqToHom h ≫ g ≫ eqToHom h'.symm ↔ HEq f g := by
  cases h
  cases h'
  simp
#align category_theory.functor.conj_eq_to_hom_iff_heq CategoryTheory.Functor.conj_eqToHom_iff_heq

/-- Proving equality between functors using heterogeneous equality. -/
theorem hext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y) (f : X ⟶ Y), HEq (F.map f) (G.map f)) : F = G :=
  Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_heq _ _ (h_obj _) (h_obj _)).2 <| h_map _ _ f
#align category_theory.functor.hext CategoryTheory.Functor.hext

-- Using equalities between functors.
theorem congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X := by rw [h]
#align category_theory.functor.congr_obj CategoryTheory.Functor.congr_obj

theorem congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_obj h Y).symm := by
  subst h; simp
#align category_theory.functor.congr_hom CategoryTheory.Functor.congr_hom

theorem congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
    (hY : F.obj Y = G.obj Y)
    (h₂ : F.map e.hom = eqToHom (by rw [hX]) ≫ G.map e.hom ≫ eqToHom (by rw [hY])) :
    F.map e.inv = eqToHom (by rw [hY]) ≫ G.map e.inv ≫ eqToHom (by rw [hX]) := by
  simp only [← IsIso.Iso.inv_hom e, Functor.map_inv, h₂, IsIso.inv_comp, inv_eqToHom,
    Category.assoc]
#align category_theory.functor.congr_inv_of_congr_hom CategoryTheory.Functor.congr_inv_of_congr_hom

section HEq

-- Composition of functors and maps w.r.t. heq
variable {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

theorem map_comp_heq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
    (hf : HEq (F.map f) (G.map f)) (hg : HEq (F.map g) (G.map g)) :
    HEq (F.map (f ≫ g)) (G.map (f ≫ g)) := by
  rw [F.map_comp, G.map_comp]
  congr
#align category_theory.functor.map_comp_heq CategoryTheory.Functor.map_comp_heq

theorem map_comp_heq' (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) :
    HEq (F.map (f ≫ g)) (G.map (f ≫ g)) := by
  rw [Functor.hext hobj fun _ _ => hmap]
#align category_theory.functor.map_comp_heq' CategoryTheory.Functor.map_comp_heq'

theorem precomp_map_heq (H : E ⥤ C) (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) {X Y : E}
    (f : X ⟶ Y) : HEq ((H ⋙ F).map f) ((H ⋙ G).map f) :=
  hmap _
#align category_theory.functor.precomp_map_heq CategoryTheory.Functor.precomp_map_heq

theorem postcomp_map_heq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
    (hmap : HEq (F.map f) (G.map f)) : HEq ((F ⋙ H).map f) ((G ⋙ H).map f) := by
  dsimp
  congr
#align category_theory.functor.postcomp_map_heq CategoryTheory.Functor.postcomp_map_heq

theorem postcomp_map_heq' (H : D ⥤ E) (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) :
    HEq ((F ⋙ H).map f) ((G ⋙ H).map f) := by rw [Functor.hext hobj fun _ _ => hmap]
#align category_theory.functor.postcomp_map_heq' CategoryTheory.Functor.postcomp_map_heq'

theorem hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  rw [h]
#align category_theory.functor.hcongr_hom CategoryTheory.Functor.hcongr_hom

end HEq

end Functor

/-- This is not always a good idea as a `@[simp]` lemma,
as we lose the ability to use results that interact with `F`,
e.g. the naturality of a natural transformation.

In some files it may be appropriate to use `attribute [local simp] eqToHom_map`, however.
-/
theorem eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congr_arg F.obj p) := by cases p; simp
#align category_theory.eq_to_hom_map CategoryTheory.eqToHom_map

@[reassoc (attr := simp)]
theorem eqToHom_map_comp (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.map (eqToHom p) ≫ F.map (eqToHom q) = F.map (eqToHom <| p.trans q) := by aesop_cat

/-- See the note on `eqToHom_map` regarding using this as a `simp` lemma.
-/
theorem eqToIso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.mapIso (eqToIso p) = eqToIso (congr_arg F.obj p) := by ext; cases p; simp
#align category_theory.eq_to_iso_map CategoryTheory.eqToIso_map

@[simp]
theorem eqToIso_map_trans (F : C ⥤ D) {X Y Z : C} (p : X = Y) (q : Y = Z) :
    F.mapIso (eqToIso p) ≪≫ F.mapIso (eqToIso q) = F.mapIso (eqToIso <| p.trans q) := by aesop_cat

@[simp]
theorem eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X) := by subst h; rfl
#align category_theory.eq_to_hom_app CategoryTheory.eqToHom_app

theorem NatTrans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
    α.app X = F.map (eqToHom h) ≫ α.app Y ≫ G.map (eqToHom h.symm) := by
  rw [α.naturality_assoc]
  simp [eqToHom_map]
#align category_theory.nat_trans.congr CategoryTheory.NatTrans.congr

theorem eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : f = eqToHom rfl ≫ f ≫ eqToHom rfl := by
  simp only [Category.id_comp, eqToHom_refl, Category.comp_id]
#align category_theory.eq_conj_eq_to_hom CategoryTheory.eq_conj_eqToHom

theorem dcongr_arg {ι : Type*} {F G : ι → C} (α : ∀ i, F i ⟶ G i) {i j : ι} (h : i = j) :
    α i = eqToHom (congr_arg F h) ≫ α j ≫ eqToHom (congr_arg G h.symm) := by
  subst h
  simp
#align category_theory.dcongr_arg CategoryTheory.dcongr_arg

end CategoryTheory
