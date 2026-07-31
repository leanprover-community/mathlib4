/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau, Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Abelian.Subobject

/-! # Short Exact Sequences in Abelian Categories

This file contains lemmas about short exact sequences in abelian categories.

## Main results

* `ShortComplex.Exact.subobjectOrderIso`: a correspondence theorem for a short exact sequence.

-/

public section

namespace CategoryTheory.ShortExact

universe v₁ v₂ u₁ u₂

open CategoryTheory Limits Preadditive CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable (F : C ⥤ D) [PreservesZeroMorphisms F] [F.Faithful]
variable {S : ShortComplex C}

lemma reflects_shortExact_of_faithful (hS : (S.map F).ShortExact) : S.ShortExact where
  exact := F.reflects_exact_of_faithful _ hS.1
  mono_f := ReflectsMonomorphisms.reflects _ hS.mono_f
  epi_g := ReflectsEpimorphisms.reflects _ hS.epi_g

lemma shortExact_map_iff [PreservesFiniteColimits F] [PreservesFiniteLimits F] :
    (S.map F).ShortExact ↔ S.ShortExact :=
  ⟨reflects_shortExact_of_faithful F, fun h ↦ ShortComplex.ShortExact.map_of_exact h F⟩

end CategoryTheory.ShortExact

namespace CategoryTheory.ShortComplex

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {S : ShortComplex C}

/-- The correspondence theorem for short exact sequences: the subobjects of the final object are
order-isomorphic to the subobjects of the middle object containing the first object. -/
noncomputable def Exact.subobjectOrderIso (hS : S.Exact) [Mono S.f] [Epi S.g] :
    Subobject S.X₃ ≃o Set.Ici (Subobject.mk S.f) :=
  (Abelian.Subobject.epiOrderIso S.g).trans (OrderIso.setCongr _ _
    (by rw [← Limits.imageSubobject_mono S.f, (exact_iff_image_eq_kernel S).mp hS]))

end CategoryTheory.ShortComplex
