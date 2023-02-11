/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Scott Morrison

! This file was ported from Lean 3 source module category_theory.eq_to_hom
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Opposites

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
2. Promote `h` to a morphism using `eq_to_hom h : X ⟶ Y`, or `eq_to_iso h : X ≅ Y`.

This file introduces various `simp` lemmas which in favourable circumstances
result in the various `eq_to_hom` morphisms to drop out at the appropriate moment!
-/


universe v₁ v₂ v₃ u₁ u₂ u₃

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C]

/-- An equality `X = Y` gives us a morphism `X ⟶ Y`.

It is typically better to use this, rather than rewriting by the equality then using `𝟙 _`
which usually leads to dependent type theory hell.
-/
def eqToHom {X Y : C} (p : X = Y) : X ⟶ Y := by rw [p] <;> exact 𝟙 _
#align category_theory.eq_to_hom CategoryTheory.eqToHom

@[simp]
theorem eqToHom_refl (X : C) (p : X = X) : eqToHom p = 𝟙 X :=
  rfl
#align category_theory.eq_to_hom_refl CategoryTheory.eqToHom_refl

@[simp, reassoc.1]
theorem eqToHom_trans {X Y Z : C} (p : X = Y) (q : Y = Z) :
    eqToHom p ≫ eqToHom q = eqToHom (p.trans q) :=
  by
  cases p
  cases q
  simp
#align category_theory.eq_to_hom_trans CategoryTheory.eqToHom_trans

theorem comp_eqToHom_iff {X Y Y' : C} (p : Y = Y') (f : X ⟶ Y) (g : X ⟶ Y') :
    f ≫ eqToHom p = g ↔ f = g ≫ eqToHom p.symm :=
  { mp := fun h => h ▸ by simp
    mpr := fun h => by simp [eq_whisker h (eq_to_hom p)] }
#align category_theory.comp_eq_to_hom_iff CategoryTheory.comp_eqToHom_iff

theorem eqToHom_comp_iff {X X' Y : C} (p : X = X') (f : X ⟶ Y) (g : X' ⟶ Y) :
    eqToHom p ≫ g = f ↔ g = eqToHom p.symm ≫ f :=
  { mp := fun h => h ▸ by simp
    mpr := fun h => h ▸ by simp [whisker_eq _ h] }
#align category_theory.eq_to_hom_comp_iff CategoryTheory.eqToHom_comp_iff

/-- If we (perhaps unintentionally) perform equational rewriting on
the source object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eq_to_hom`.

It may be advisable to introduce any necessary `eq_to_hom` morphisms manually,
rather than relying on this lemma firing.
-/
@[simp]
theorem congr_arg_mpr_hom_left {X Y Z : C} (p : X = Y) (q : Y ⟶ Z) :
    (congr_arg (fun W : C => W ⟶ Z) p).mpr q = eqToHom p ≫ q :=
  by
  cases p
  simp
#align category_theory.congr_arg_mpr_hom_left CategoryTheory.congr_arg_mpr_hom_left

/-- If we (perhaps unintentionally) perform equational rewriting on
the target object of a morphism,
we can replace the resulting `_.mpr f` term by a composition with an `eq_to_hom`.

It may be advisable to introduce any necessary `eq_to_hom` morphisms manually,
rather than relying on this lemma firing.
-/
@[simp]
theorem congr_arg_mpr_hom_right {X Y Z : C} (p : X ⟶ Y) (q : Z = Y) :
    (congr_arg (fun W : C => X ⟶ W) q).mpr p = p ≫ eqToHom q.symm :=
  by
  cases q
  simp
#align category_theory.congr_arg_mpr_hom_right CategoryTheory.congr_arg_mpr_hom_right

/-- An equality `X = Y` gives us an isomorphism `X ≅ Y`.

It is typically better to use this, rather than rewriting by the equality then using `iso.refl _`
which usually leads to dependent type theory hell.
-/
def eqToIso {X Y : C} (p : X = Y) : X ≅ Y :=
  ⟨eqToHom p, eqToHom p.symm, by simp, by simp⟩
#align category_theory.eq_to_iso CategoryTheory.eqToIso

@[simp]
theorem eqToIso.hom {X Y : C} (p : X = Y) : (eqToIso p).Hom = eqToHom p :=
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
    eqToIso p ≪≫ eqToIso q = eqToIso (p.trans q) := by ext <;> simp
#align category_theory.eq_to_iso_trans CategoryTheory.eqToIso_trans

@[simp]
theorem eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h).op = eqToHom (congr_arg op h.symm) :=
  by
  cases h
  rfl
#align category_theory.eq_to_hom_op CategoryTheory.eqToHom_op

@[simp]
theorem eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqToHom h).unop = eqToHom (congr_arg unop h.symm) :=
  by
  cases h
  rfl
#align category_theory.eq_to_hom_unop CategoryTheory.eqToHom_unop

instance {X Y : C} (h : X = Y) : IsIso (eqToHom h) :=
  IsIso.of_iso (eqToIso h)

@[simp]
theorem inv_eqToHom {X Y : C} (h : X = Y) : inv (eqToHom h) = eqToHom h.symm :=
  by
  ext
  simp
#align category_theory.inv_eq_to_hom CategoryTheory.inv_eqToHom

variable {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Proving equality between functors. This isn't an extensionality lemma,
  because usually you don't really want to do this. -/
theorem ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToHom (h_obj Y).symm) : F = G :=
  by
  cases' F with F_obj _ _ _
  cases' G with G_obj _ _ _
  obtain rfl : F_obj = G_obj := by
    ext X
    apply h_obj
  congr
  funext X Y f
  simpa using h_map X Y f
#align category_theory.functor.ext CategoryTheory.Functor.ext

/-- Two morphisms are conjugate via eq_to_hom if and only if they are heterogeneously equal. -/
theorem conj_eqToHom_iff_hEq {W X Y Z : C} (f : W ⟶ X) (g : Y ⟶ Z) (h : W = Y) (h' : X = Z) :
    f = eqToHom h ≫ g ≫ eqToHom h'.symm ↔ HEq f g :=
  by
  cases h
  cases h'
  simp
#align category_theory.functor.conj_eq_to_hom_iff_heq CategoryTheory.Functor.conj_eqToHom_iff_hEq

/-- Proving equality between functors using heterogeneous equality. -/
theorem hext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
    (h_map : ∀ (X Y) (f : X ⟶ Y), HEq (F.map f) (G.map f)) : F = G :=
  Functor.ext h_obj fun _ _ f => (conj_eqToHom_iff_hEq _ _ (h_obj _) (h_obj _)).2 <| h_map _ _ f
#align category_theory.functor.hext CategoryTheory.Functor.hext

-- Using equalities between functors.
theorem congr_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X := by subst h
#align category_theory.functor.congr_obj CategoryTheory.Functor.congr_obj

theorem congr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
    F.map f = eqToHom (congr_obj h X) ≫ G.map f ≫ eqToHom (congr_obj h Y).symm := by
  subst h <;> simp
#align category_theory.functor.congr_hom CategoryTheory.Functor.congr_hom

theorem congr_inv_of_congr_hom (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (hX : F.obj X = G.obj X)
    (hY : F.obj Y = G.obj Y)
    (h₂ : F.map e.Hom = eqToHom (by rw [hX]) ≫ G.map e.Hom ≫ eqToHom (by rw [hY])) :
    F.map e.inv = eqToHom (by rw [hY]) ≫ G.map e.inv ≫ eqToHom (by rw [hX]) := by
  simp only [← is_iso.iso.inv_hom e, functor.map_inv, h₂, is_iso.inv_comp, inv_eq_to_hom,
    category.assoc]
#align category_theory.functor.congr_inv_of_congr_hom CategoryTheory.Functor.congr_inv_of_congr_hom

theorem congr_map (F : C ⥤ D) {X Y : C} {f g : X ⟶ Y} (h : f = g) : F.map f = F.map g := by rw [h]
#align category_theory.functor.congr_map CategoryTheory.Functor.congr_map

section HEq

-- Composition of functors and maps w.r.t. heq
variable {E : Type u₃} [Category.{v₃} E] {F G : C ⥤ D} {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}

theorem map_comp_hEq (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y) (hz : F.obj Z = G.obj Z)
    (hf : HEq (F.map f) (G.map f)) (hg : HEq (F.map g) (G.map g)) :
    HEq (F.map (f ≫ g)) (G.map (f ≫ g)) :=
  by
  rw [F.map_comp, G.map_comp]
  congr
#align category_theory.functor.map_comp_heq CategoryTheory.Functor.map_comp_hEq

theorem map_comp_heq' (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) : HEq (F.map (f ≫ g)) (G.map (f ≫ g)) :=
  by rw [functor.hext hobj fun _ _ => hmap]
#align category_theory.functor.map_comp_heq' CategoryTheory.Functor.map_comp_heq'

theorem precomp_map_hEq (H : E ⥤ C) (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) {X Y : E}
    (f : X ⟶ Y) : HEq ((H ⋙ F).map f) ((H ⋙ G).map f) :=
  hmap _
#align category_theory.functor.precomp_map_heq CategoryTheory.Functor.precomp_map_hEq

theorem postcomp_map_hEq (H : D ⥤ E) (hx : F.obj X = G.obj X) (hy : F.obj Y = G.obj Y)
    (hmap : HEq (F.map f) (G.map f)) : HEq ((F ⋙ H).map f) ((G ⋙ H).map f) :=
  by
  dsimp
  congr
#align category_theory.functor.postcomp_map_heq CategoryTheory.Functor.postcomp_map_hEq

theorem postcomp_map_heq' (H : D ⥤ E) (hobj : ∀ X : C, F.obj X = G.obj X)
    (hmap : ∀ {X Y} (f : X ⟶ Y), HEq (F.map f) (G.map f)) : HEq ((F ⋙ H).map f) ((G ⋙ H).map f) :=
  by rw [functor.hext hobj fun _ _ => hmap]
#align category_theory.functor.postcomp_map_heq' CategoryTheory.Functor.postcomp_map_heq'

theorem hcongr_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  subst h
#align category_theory.functor.hcongr_hom CategoryTheory.Functor.hcongr_hom

end HEq

end Functor

/-- This is not always a good idea as a `@[simp]` lemma,
as we lose the ability to use results that interact with `F`,
e.g. the naturality of a natural transformation.

In some files it may be appropriate to use `local attribute [simp] eq_to_hom_map`, however.
-/
theorem eqToHom_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.map (eqToHom p) = eqToHom (congr_arg F.obj p) := by cases p <;> simp
#align category_theory.eq_to_hom_map CategoryTheory.eqToHom_map

/-- See the note on `eq_to_hom_map` regarding using this as a `simp` lemma.
-/
theorem eqToIso_map (F : C ⥤ D) {X Y : C} (p : X = Y) :
    F.mapIso (eqToIso p) = eqToIso (congr_arg F.obj p) := by ext <;> cases p <;> simp
#align category_theory.eq_to_iso_map CategoryTheory.eqToIso_map

@[simp]
theorem eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X) := by subst h <;> rfl
#align category_theory.eq_to_hom_app CategoryTheory.eqToHom_app

theorem NatTrans.congr {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (h : X = Y) :
    α.app X = F.map (eqToHom h) ≫ α.app Y ≫ G.map (eqToHom h.symm) :=
  by
  rw [α.naturality_assoc]
  simp [eq_to_hom_map]
#align category_theory.nat_trans.congr CategoryTheory.NatTrans.congr

theorem eq_conj_eqToHom {X Y : C} (f : X ⟶ Y) : f = eqToHom rfl ≫ f ≫ eqToHom rfl := by
  simp only [category.id_comp, eq_to_hom_refl, category.comp_id]
#align category_theory.eq_conj_eq_to_hom CategoryTheory.eq_conj_eqToHom

theorem dcongr_arg {ι : Type _} {F G : ι → C} (α : ∀ i, F i ⟶ G i) {i j : ι} (h : i = j) :
    α i = eqToHom (congr_arg F h) ≫ α j ≫ eqToHom (congr_arg G h.symm) :=
  by
  subst h
  simp
#align category_theory.dcongr_arg CategoryTheory.dcongr_arg

end CategoryTheory

