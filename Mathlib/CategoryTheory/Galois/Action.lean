/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Galois.Examples
import Mathlib.CategoryTheory.Galois.Prorepresentability

/-!

# Induced functor to finite `Aut F`-sets

Any (fiber) functor `F : C ⥤ FintypeCat` factors via the forgetful functor
from finite `Aut F`-sets to finite sets. In this file we collect basic properties
of the induced functor `H : C ⥤ Action FintypeCat (Aut F)`.

See `Mathlib/CategoryTheory/Galois/Full.lean` for the proof that `H` is (faithfully) full.

-/

universe u

namespace CategoryTheory

namespace PreGaloisCategory

open Limits Functor

variable {C : Type*} [Category C] (F : C ⥤ FintypeCat.{u})

/-- Any (fiber) functor `F : C ⥤ FintypeCat` naturally factors via
the forgetful functor from `Action FintypeCat (Aut F)` to `FintypeCat`. -/
def functorToAction : C ⥤ Action FintypeCat.{u} (Aut F) where
  obj X := Action.FintypeCat.ofMulAction (Aut F) (F.obj X)
  map f := {
    hom := F.map f
    comm := fun g ↦ symm <| g.hom.naturality f
  }

lemma functorToAction_comp_forget₂_eq : functorToAction F ⋙ forget₂ _ FintypeCat = F := rfl

@[simp]
lemma functorToAction_map {X Y : C} (f : X ⟶ Y) : ((functorToAction F).map f).hom = F.map f :=
  rfl

instance (X : C) : MulAction (Aut X) ((functorToAction F).obj X).V :=
  inferInstanceAs <| MulAction (Aut X) (F.obj X)

variable [GaloisCategory C] [FiberFunctor F]

instance (X : C) [IsGalois X] : MulAction.IsPretransitive (Aut X) ((functorToAction F).obj X).V :=
  isPretransitive_of_isGalois F X

instance : Functor.Faithful (functorToAction F) :=
  have : Functor.Faithful (functorToAction F ⋙ forget₂ _ FintypeCat) :=
    inferInstanceAs <| Functor.Faithful F
  Functor.Faithful.of_comp (functorToAction F) (forget₂ _ FintypeCat)

instance : PreservesMonomorphisms (functorToAction F) :=
  have : PreservesMonomorphisms (functorToAction F ⋙ forget₂ _ FintypeCat) :=
    inferInstanceAs <| PreservesMonomorphisms F
  preservesMonomorphisms_of_preserves_of_reflects (functorToAction F) (forget₂ _ FintypeCat)

instance : ReflectsMonomorphisms (functorToAction F) := reflectsMonomorphisms_of_faithful _

instance : Functor.ReflectsIsomorphisms (functorToAction F) where
  reflects f _ :=
    have : IsIso (F.map f) := (forget₂ _ FintypeCat).map_isIso ((functorToAction F).map f)
    isIso_of_reflects_iso f F

noncomputable instance : PreservesFiniteCoproducts (functorToAction F) :=
  ⟨fun _ ↦ Action.preservesColimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesColimitsOfShape (Discrete _) F)⟩

noncomputable instance : PreservesFiniteProducts (functorToAction F) :=
  ⟨fun _ ↦ Action.preservesLimitsOfShape_of_preserves (functorToAction F)
    (inferInstanceAs <| PreservesLimitsOfShape (Discrete _) F)⟩

noncomputable instance (G : Type*) [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) (functorToAction F) :=
  Action.preservesColimitsOfShape_of_preserves _ <|
    inferInstanceAs <| PreservesColimitsOfShape (SingleObj G) F

instance : PreservesIsConnected (functorToAction F) :=
  ⟨fun {X} _ ↦ FintypeCat.Action.isConnected_of_transitive (Aut F) (F.obj X)⟩

end PreGaloisCategory

end CategoryTheory
