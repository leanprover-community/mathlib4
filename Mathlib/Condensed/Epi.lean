import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Condensed.Module

universe u

open CategoryTheory Sheaf

namespace CondensedMod

variable (R : Type (u+1)) [Ring R]

lemma isLocallySurjective_iff_epi {X Y : CondensedMod.{u} R} (f : X ⟶ Y) :
    IsLocallySurjective f ↔ Epi f  :=
  isLocallySurjective_iff_epi' _ f
