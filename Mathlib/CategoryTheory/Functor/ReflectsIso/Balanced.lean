/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Robin Carlier
-/
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.Balanced
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Balanced categories and functors reflecting isomorphisms

If a category is `C`, and a functor out of `C` reflects epimorphisms and monomorphisms,
then the functor reflects isomorphisms.
Furthermore, categories that admits a functor that `ReflectsIsomorphisms`, `PreservesEpimorphisms`
and `PreservesMonomorphisms` are balanced.

-/

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type*} [Category C]
  {D : Type*} [Category D]

instance (priority := 100) reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
    [Balanced C] (F : C ⥤ D) [ReflectsMonomorphisms F] [ReflectsEpimorphisms F] :
    F.ReflectsIsomorphisms where
  reflects f hf := by
    haveI : Epi f := epi_of_epi_map F inferInstance
    haveI : Mono f := mono_of_mono_map F inferInstance
    exact isIso_of_mono_of_epi f

lemma Functor.balanced_of_preserves (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [F.PreservesEpimorphisms] [F.PreservesMonomorphisms] [Balanced D] :
    Balanced C where
  isIso_of_mono_of_epi f _ _ := by
    rw [← isIso_iff_of_reflects_iso (F := F)]
    exact isIso_of_mono_of_epi _

end CategoryTheory
