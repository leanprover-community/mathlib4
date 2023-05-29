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
  arrows := Sieve.generate_singleton_aux f
  downward_closed := by
    rintro W Z e ⟨a⟩ g
    rw [← Category.assoc]
    apply Sieve.generate_singleton_aux.mk

lemma Sieve.generate_singleton_eq {X Y : C} (f : Y ⟶ X) :
    Sieve.generate (Presieve.singleton f) = Sieve.generate_singleton f := by
  ext Z ; intro g
  constructor
  · rintro ⟨W,i,p,⟨⟩,rfl⟩
    apply Sieve.generate_singleton_aux.mk
  · rintro ⟨g⟩
    refine ⟨Y,g,f,⟨⟩,rfl⟩

def isColimitKernelPairOfIsColimitPresieveCocone {X Y R : C}
    (f : Y ⟶ X) (a b : R ⟶ Y) (k : IsKernelPair f a b)
    (h : IsColimit ((Sieve.generate_singleton f) : Presieve X).cocone) :
    IsColimit (Cofork.ofπ f k.w) := sorry

def isColimitPresieveCoconeOfIsColimitKernelPair {X Y R : C}
    (f : Y ⟶ X) (a b : R ⟶ Y) (k : IsKernelPair f a b)
    (h : IsColimit (Cofork.ofπ f k.w)) :
    IsColimit (Sieve.generate_singleton f : Presieve X).cocone := sorry

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
