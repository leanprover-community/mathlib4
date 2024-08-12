/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Data.Set.Basic
/-!

This file defines the type `f.Fibers` of fibers of a function `f : Y → Z`, and provides some API
to work with and construct terms of this type.

Note: this API is designed to be useful when defining the counit of the adjunction between
the functor which takes a set to the condensed set corresponding to locally constant maps to that
set, and the forgetful functor from the category of condensed sets to the category of sets
(see PR #14027).
-/

variable {X Y Z : Type*}

namespace Function

/-- The indexing set of the partition. -/
def Fibers (f : Y → Z) : Type _ := Set.range (fun (x : Set.range f) ↦ f ⁻¹' {x.val})

namespace Fibers

/--
Any `a : Fibers f` is of the form `f ⁻¹' {x}` for some `x` in the image of `f`. We define `a.image` 
as an arbitrary such `x`.
-/
noncomputable def image (f : Y → Z) (a : Fibers f) : Z := a.2.choose.1

lemma eq_fiber_image  (f : Y → Z) (a : Fibers f) : a.1 = f ⁻¹' {a.image} := a.2.choose_spec.symm

/--
Given `y : Y`, `Fibers.mk f y` is the fiber of `f` that `y` belongs to, as an element of `Fibers f`.
-/
def mk (f : Y → Z) (y : Y) : Fibers f := ⟨f ⁻¹' {f y}, by simp⟩

/-- `y : Y` as a term of the type `Fibers.mk f y` -/
def mkSelf (f : Y → Z) (y : Y) : (mk f y).val := ⟨y, rfl⟩

lemma map_eq_image (f : Y → Z) (a : Fibers f) (x : a.1) : f x = a.image := by
  have := a.2.choose_spec
  rw [← Set.mem_singleton_iff, ← Set.mem_preimage]
  convert x.prop

lemma mk_image (f : Y → Z) (y : Y) : (Fibers.mk f y).image = f y :=
  (map_eq_image (x := mkSelf f y)).symm

lemma mem_iff_eq_image (f : Y → Z) (y : Y) (a : Fibers f) : y ∈ a.val ↔ f y = a.image :=
  ⟨fun h ↦ a.map_eq_image _ ⟨y, h⟩, fun h ↦ by rw [a.eq_fiber_image]; exact h⟩

/-- An arbitrary element of `a : Fibers f`. -/
noncomputable def preimage (f : Y → Z) (a : Fibers f) : Y := a.2.choose.2.choose

lemma map_preimage_eq_image (f : Y → Z) (a : Fibers f) : f a.preimage = a.image :=
  a.2.choose.2.choose_spec

lemma fibers_nonempty (f : Y → Z) (a : Fibers f) : Set.Nonempty a.val := by
  refine ⟨preimage f a, ?_⟩
  rw [mem_iff_eq_image, ← map_preimage_eq_image]

lemma map_preimage_eq_image_map {W : Type*} (f : Y → Z) (g : Z → W) (a : Fibers (g ∘ f)) :
    g (f a.preimage) = a.image := by rw [← map_preimage_eq_image]; rfl

lemma image_eq_image_mk (f : Y → Z) (g : X → Y) (a : Fibers (f ∘ g)) :
    a.image = (Fibers.mk f (g (a.preimage _))).image := by
  rw [← map_preimage_eq_image_map _ _ a, mk_image]

end Function.Fibers
