import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Finite

universe u v

open CategoryTheory Limits

instance : AddCommGrp.uliftFunctor.{u, v}.Faithful := by
  refine {map_injective := ?_}
  intro X Y f g
  intro heq
  ext a
  apply_fun (fun h ↦ h {down := a}) at heq
  simp at heq
  exact heq

instance : PreservesFiniteLimits AddCommGrp.uliftFunctor.{u,v} := sorry

instance : PreservesFiniteColimits AddCommGrp.uliftFunctor.{u,v} := sorry

instance : AddCommGrp.uliftFunctor.{u,v}.PreservesZeroMorphisms := {map_zero := fun X Y ↦ by rfl}
