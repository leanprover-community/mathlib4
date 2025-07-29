/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Functors which reflect isomorphisms

A functor `F` reflects isomorphisms if whenever `F.map f` is an isomorphism, `f` was too.

It is formalized as a `Prop` valued typeclass `ReflectsIsomorphisms F`.

Any fully faithful functor reflects isomorphisms.
-/

namespace CategoryTheory

open Functor

variable {C : Type*} [Category C]
  {D : Type*} [Category D]
  {E : Type*} [Category E]

section ReflectsIso

/-- Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class Functor.ReflectsIsomorphisms (F : C ⥤ D) : Prop where
  /-- For any `f`, if `F.map f` is an iso, then so was `f`. -/
  reflects : ∀ {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f

/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
theorem isIso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)]
    [F.ReflectsIsomorphisms] : IsIso f :=
  ReflectsIsomorphisms.reflects F f

lemma isIso_iff_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] :
    IsIso (F.map f) ↔ IsIso f :=
  ⟨fun _ => isIso_of_reflects_iso f F, fun _ => inferInstance⟩

lemma Functor.FullyFaithful.reflectsIsomorphisms {F : C ⥤ D} (hF : F.FullyFaithful) :
    F.ReflectsIsomorphisms where
  reflects _ _ := hF.isIso_of_isIso_map _

instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful
    (F : C ⥤ D) [F.Full] [F.Faithful] :
    F.ReflectsIsomorphisms :=
  (Functor.FullyFaithful.ofFullyFaithful F).reflectsIsomorphisms

instance reflectsIsomorphisms_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.ReflectsIsomorphisms] [G.ReflectsIsomorphisms] :
    (F ⋙ G).ReflectsIsomorphisms :=
  ⟨fun f (hf : IsIso (G.map _)) => by
    haveI := isIso_of_reflects_iso (F.map f) G
    exact isIso_of_reflects_iso f F⟩

lemma reflectsIsomorphisms_of_comp (F : C ⥤ D) (G : D ⥤ E)
    [(F ⋙ G).ReflectsIsomorphisms] : F.ReflectsIsomorphisms where
  reflects f _ := by
    rw [← isIso_iff_of_reflects_iso _ (F ⋙ G)]
    dsimp
    infer_instance

instance (F : D ⥤ E) [F.ReflectsIsomorphisms] :
    ((whiskeringRight C D E).obj F).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro Z
    rw [← isIso_iff_of_reflects_iso _ F]
    change IsIso ((((whiskeringRight C D E).obj F).map f).app Z)
    infer_instance

end ReflectsIso

end CategoryTheory
