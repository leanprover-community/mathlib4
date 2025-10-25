/-
Copyright (c) 2024 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Limits.Shapes.SplitEqualizer
import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Special equalizers associated to a comonad

Associated to a comonad `T : C ⥤ C` we have important equalizer constructions:
Any coalgebra is an equalizer (in the category of coalgebras) of cofree coalgebras. Furthermore,
this equalizer is coreflexive.
In `C`, this fork diagram is a split equalizer (in particular, it is still an equalizer).
This split equalizer is known as the Beck equalizer (as it features heavily in Beck's
comonadicity theorem).

This file is adapted from `Mathlib/CategoryTheory/Monad/Coequalizer.lean`.
Please try to keep them in sync.

-/


universe v₁ u₁

namespace CategoryTheory

namespace Comonad

open Limits

variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Comonad C} (X : Coalgebra T)

/-!
Show that any coalgebra is an equalizer of cofree coalgebras.
-/


/-- The top map in the equalizer diagram we will construct. -/
@[simps!]
def CofreeEqualizer.topMap :  (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) :=
  (Comonad.cofree T).map X.a

/-- The bottom map in the equalizer diagram we will construct. -/
@[simps]
def CofreeEqualizer.bottomMap :
    (Comonad.cofree T).obj X.A ⟶ (Comonad.cofree T).obj (T.obj X.A) where
  f := T.δ.app X.A
  h := T.coassoc X.A

/-- The fork map in the equalizer diagram we will construct. -/
@[simps]
def CofreeEqualizer.ι : X ⟶ (Comonad.cofree T).obj X.A where
  f := X.a
  h := X.coassoc.symm

theorem CofreeEqualizer.condition :
    CofreeEqualizer.ι X ≫ CofreeEqualizer.topMap X =
      CofreeEqualizer.ι X ≫ CofreeEqualizer.bottomMap X :=
  Coalgebra.Hom.ext X.coassoc.symm

instance : IsCoreflexivePair (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) := by
  apply IsCoreflexivePair.mk' _ _ _
  · apply (cofree T).map (T.ε.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp, X.counit, Functor.map_id]
  · ext
    apply Comonad.right_counit

/-- Construct the Beck fork in the category of coalgebras. This fork is coreflexive as well as an
equalizer.
-/
@[simps!]
def beckCoalgebraFork : Fork (CofreeEqualizer.topMap X) (CofreeEqualizer.bottomMap X) :=
  Fork.ofι _ (CofreeEqualizer.condition X)

/-- The fork constructed is a limit. This shows that any coalgebra is a (coreflexive) equalizer of
cofree coalgebras.
-/
def beckCoalgebraEqualizer : IsLimit (beckCoalgebraFork X) :=
  Fork.IsLimit.mk' _ fun s => by
    have h₁ :  s.ι.f ≫ (T : C ⥤ C).map X.a = s.ι.f ≫ T.δ.app X.A :=
      congr_arg Comonad.Coalgebra.Hom.f s.condition
    have h₂ :  s.pt.a ≫ (T : C ⥤ C).map s.ι.f = s.ι.f ≫ T.δ.app X.A := s.ι.h
    refine ⟨⟨s.ι.f ≫ T.ε.app _, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp, reassoc_of% h₂, Comonad.right_counit]
      dsimp
      rw [Category.comp_id, Category.assoc, ← T.counit_naturality,
        reassoc_of% h₁, Comonad.left_counit]
      simp
    · ext
      simpa [← T.ε.naturality_assoc, T.left_counit_assoc] using h₁ =≫ T.ε.app ((T : C ⥤ C).obj X.A)
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      simp [beckCoalgebraFork, X.counit]

/-- The Beck fork is a split equalizer. -/
def beckSplitEqualizer : IsSplitEqualizer (T.map X.a) (T.δ.app _) X.a :=
  ⟨T.ε.app _, T.ε.app _, X.coassoc.symm, X.counit, T.left_counit _, (T.ε.naturality _)⟩

/-- This is the Beck fork. It is a split equalizer, in particular a equalizer. -/
@[simps! pt]
def beckFork : Fork (T.map X.a) (T.δ.app _) :=
  (beckSplitEqualizer X).asFork

@[simp]
theorem beckFork_ι : (beckFork X).ι = X.a :=
  rfl

/-- The Beck fork is a equalizer. -/
def beckEqualizer : IsLimit (beckFork X) :=
  (beckSplitEqualizer X).isEqualizer

@[simp]
theorem beckEqualizer_lift (s : Fork (T.toFunctor.map X.a) (T.δ.app X.A)) :
    (beckEqualizer X).lift s = s.ι ≫ T.ε.app _ :=
  rfl

end Comonad

end CategoryTheory
