/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Limits.Preserves.Filtered

/-!

# Forgetful functor from `Over X` preserves cofiltered limits

Note that `Over.forget X : Over X ⥤ C` already preserves all colimits because it is a left adjoint.
See `Mathlib/CategoryTheory/Adjunction/Over.lean`

-/

namespace CategoryTheory.Limits

variable {C : Type*} [Category C]

attribute [local instance] IsFiltered.nonempty IsCofiltered.nonempty

instance {X : C} : PreservesCofilteredLimitsOfSize (Over.forget X) := by
  refine ⟨fun J hJ hJ' ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨.ofExistsUnique fun s ↦ ?_⟩⟩⟩⟩
  obtain i := Nonempty.some (inferInstanceAs (Nonempty J))
  let s' : Cone F := ⟨Over.mk (s.π.app i ≫ (F.obj i).hom), fun j ↦ Over.homMk (s.π.app j) (by
    obtain ⟨k, hik, hjk, -⟩ := IsCofilteredOrEmpty.cone_objs i j
    simp only [Functor.const_obj_obj, Over.mk_left, Over.mk_hom,
      ← s.w hjk, ← s.w hik]
    simp), fun j k e ↦ by ext; simpa using (s.w e).symm⟩
  refine ⟨(hc.lift s').left, fun j ↦ congr($(hc.fac s' j).left), fun f hf ↦ ?_⟩
  dsimp at hf
  exact congr($(hc.uniq s' (Over.homMk f (by simp [s', ← hf]))
    fun j ↦ Over.OverMorphism.ext (hf j)).left)

instance {X : C} : PreservesFilteredColimitsOfSize (Under.forget X) := by
  refine ⟨fun J hJ hJ' ↦ ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨.ofExistsUnique fun s ↦ ?_⟩⟩⟩⟩
  obtain i := Nonempty.some (inferInstanceAs (Nonempty J))
  let s' : Cocone F := ⟨Under.mk ((F.obj i).hom ≫ s.ι.app i), fun j ↦ Under.homMk (s.ι.app j) (by
    obtain ⟨k, hik, hjk, -⟩ := IsFilteredOrEmpty.cocone_objs i j
    simp only [Functor.const_obj_obj, Functor.id_obj, Under.mk_right, Under.mk_hom,
      ← s.w hjk, ← s.w hik]
    simp), fun j k e ↦ by ext; simpa using s.w e⟩
  refine ⟨(hc.desc s').right, fun j ↦ congr($(hc.fac s' j).right), fun f hf ↦ ?_⟩
  dsimp at hf
  exact congr($(hc.uniq s' (Under.homMk f (by simp [s', ← hf]))
    fun j ↦ Under.UnderMorphism.ext (hf j)).right)

end CategoryTheory.Limits
