/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact

@[expose] public section

namespace CategoryTheory.ShortExact

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory Limits Preadditive

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F]

lemma reflects_shortExact_of_faithful [F.Faithful] [F.ReflectsEpimorphisms]
    [F.ReflectsMonomorphisms] {S : ShortComplex C} (hS : (S.map F).ShortExact) : S.ShortExact where
  exact := F.reflects_exact_of_faithful _ hS.1
  mono_f := ReflectsMonomorphisms.reflects _ hS.mono_f
  epi_g := ReflectsEpimorphisms.reflects _ hS.epi_g

lemma map_shortExact_iff [F.Faithful] [F.ReflectsEpimorphisms] [F.ReflectsMonomorphisms]
    [PreservesFiniteColimits F] [PreservesFiniteLimits F] {S : ShortComplex C} :
    (S.map F).ShortExact ↔ S.ShortExact :=
  ⟨reflects_shortExact_of_faithful F, fun h ↦ ShortComplex.ShortExact.map_of_exact h F⟩

end CategoryTheory.ShortExact
