/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!

# Exactness of functors for change of rings.

In this file we provide exactness of restrictScalars for general universe level using it preserves
short exact sequences.
Note : previously exactness of `ModuleCat.restrictScalars` is synthesized via being adjoint functor,
however this needs the universe level to be some `max u v`, where `u` is the universe level
of the ring.

-/

@[expose] public section

universe v u u'

variable {R : Type u} [CommRing R] {R' : Type u'} [CommRing R']

open CategoryTheory

section

variable (f : R →+* R')

lemma ModuleCat.restrictScalars_map_exact (S : ShortComplex (ModuleCat.{v} R')) (h : S.Exact) :
    (S.map (ModuleCat.restrictScalars.{v} f)).Exact := by
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h ⊢
  exact h

instance : Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact this.1

instance : Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  have := ((CategoryTheory.Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 1 3).mp
    (ModuleCat.restrictScalars_map_exact f)
  exact this.2

end
