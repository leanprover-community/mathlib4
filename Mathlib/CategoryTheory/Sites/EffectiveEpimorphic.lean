/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.CategoryTheory.Limits.Shapes.KernelPair

namespace CategoryTheory

open Limits

variable {C : Type _} [Category C]

def Sieve.EffectiveEpimorphic {X : C} (S : Sieve X) : Prop :=
  Nonempty (IsColimit (S : Presieve X).cocone)

abbrev Presieve.EffectiveEpimorphic {X : C} (S : Presieve X) : Prop :=
  (Sieve.generate S).EffectiveEpimorphic

inductive Sieve.generate_singleton_aux {X Y : C} (f : Y ⟶ X) : (Z : C) → (Z ⟶ X) → Prop where
  | mk (Z : C) (g : Z ⟶ Y) : Sieve.generate_singleton_aux _ _ (g ≫ f)

def Sieve.generate_singleton {X Y : C} (f : Y ⟶ X) : Sieve X where
  arrows Z g := ∃ (e : Z ⟶ Y), e ≫ f = g
  downward_closed := by
    rintro W Z g ⟨e,rfl⟩ q
    refine ⟨q ≫ e, by simp⟩

lemma Sieve.generate_singleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generate_singleton f := by
  ext Z ; intro g
  constructor
  · rintro ⟨W,i,p,⟨⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨g,h⟩
    exact ⟨Y,g,f,⟨⟩,h⟩

noncomputable
def isColimitKernelPairOfIsColimitPresieveCocone {X Y R : C}
    (f : Y ⟶ X) (a b : R ⟶ Y) (k : IsKernelPair f a b)
    (h : IsColimit ((Sieve.generate_singleton f) : Presieve X).cocone) :
    IsColimit (Cofork.ofπ f k.w) :=
  letI aux : Cofork a b → Cocone (Sieve.generate_singleton f).arrows.diagram :=
    fun S => ⟨S.pt,
    { app := fun ⟨T,hT⟩ => hT.choose ≫ S.π
      naturality := by
        rintro ⟨x,hx⟩ ⟨y,hy⟩ (g : x ⟶ y)
        dsimp ; simp only [Category.comp_id]
        let x' : x.left ⟶ Y := hx.choose
        let y' : y.left ⟶ Y := hy.choose
        change g.left ≫ y' ≫ _ = x' ≫ _
        have hh : (g.left ≫ y') ≫ f = x' ≫ f := by
          simp [hx.choose_spec, Category.assoc, hy.choose_spec]
        let e := k.lift (g.left ≫ y') x' hh
        have hea : g.left ≫ y' = e ≫ a := by rw [k.lift_fst]
        have heb : x' = e ≫ b := by rw [k.lift_snd]
        rw [reassoc_of% hea, heb, Category.assoc, S.condition] }⟩
  Cofork.IsColimit.mk _
    (fun S => h.desc <| aux S)
    (by
      intro S
      let H : ∃ e : Y ⟶ Y, e ≫ f = f := ⟨𝟙 _, by simp⟩
      let D := FullSubcategory fun (T : Over X) =>
        (Sieve.generate_singleton f).arrows T.hom
      let T : D := ⟨Over.mk f, H⟩
      have := h.fac (aux S) T
      dsimp at this ⊢
      rw [this] ; clear this
      let e : Y ⟶ R := k.lift H.choose (𝟙 _) (by simp [H.choose_spec])
      have hH : H.choose = e ≫ a := by rw [k.lift_fst]
      rw [hH, Category.assoc, Cofork.condition, ← Category.assoc,
        k.lift_snd, Category.id_comp])
    (by
      intro S m hm
      apply h.hom_ext
      rintro ⟨T,⟨(g : T.left ⟶ Y),hg⟩⟩
      have := h.fac (aux S) ⟨T,g,hg⟩
      dsimp at this hm ⊢
      rw [this, ← hm, ← Category.assoc] ; congr 1
      generalize_proofs hh
      exact hh.choose_spec.symm )

def isColimitPresieveCoconeOfIsColimitKernelPair {X Y R : C}
    (f : Y ⟶ X) (a b : R ⟶ Y) (k : IsKernelPair f a b)
    (h : IsColimit (Cofork.ofπ f k.w)) :
    IsColimit (Sieve.generate_singleton f : Presieve X).cocone where
  desc := fun S => Cofork.IsColimit.desc h (S.ι.app ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩) <| by
    dsimp
    let D := FullSubcategory fun (T : Over X) => (Sieve.generate_singleton f) T.hom
    let F : D ⥤ C := Presieve.diagram (Sieve.generate_singleton f).arrows
    let a' : D := ⟨Over.mk (a ≫ f), ⟨a, rfl⟩⟩
    let b' : D := ⟨Over.mk (b ≫ f), ⟨b, rfl⟩⟩
    let t : D := ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩
    let i : a' ⟶ t := Over.homMk a rfl
    let j : b' ⟶ t := Over.homMk b rfl
    have ha : F.map i = a := rfl
    have hb : F.map j = b := rfl
    rw [← ha, ← hb, S.w, S.w]
    dsimp
    congr 3
    exact k.w
  fac := by
    rintro S ⟨T,g,hT⟩
    dsimp
    nth_rewrite 1 [← hT]
    rw [Category.assoc]
    change g ≫ (Cofork.ofπ f k.w).π ≫ _ = _
    rw [Cofork.IsColimit.π_desc' h]
    let D := FullSubcategory fun (T : Over X) => Sieve.generate_singleton f T.hom
    let A : D := ⟨Over.mk T.hom, ⟨g,hT⟩⟩
    let B : D := ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩
    let t : A ⟶ B := Over.homMk g
    exact S.w t
  uniq := by
    intro S m hm
    dsimp
    apply Cofork.IsColimit.hom_ext h
    rw [Cofork.IsColimit.π_desc']
    exact hm ⟨Over.mk f, ⟨𝟙 _, by simp⟩⟩

lemma Presieve.effectiveEpimorphic_iff_kernel_pair {X Y R : C}
    (f : Y ⟶ X) (a b : R ⟶ Y) (k : IsKernelPair f a b) :
    (Presieve.singleton f).EffectiveEpimorphic ↔
    Nonempty (IsColimit <| Cofork.ofπ f k.w) := by
  dsimp only [EffectiveEpimorphic]
  rw [Sieve.generate_singleton_eq]
  constructor
  · rintro ⟨h⟩
    exact ⟨isColimitKernelPairOfIsColimitPresieveCocone _ _ _ k h⟩
  · rintro ⟨h⟩
    exact ⟨isColimitPresieveCoconeOfIsColimitKernelPair _ _ _ k h⟩

end CategoryTheory
