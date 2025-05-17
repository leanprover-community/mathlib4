/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Monad.Algebra

/-!
# Special coequalizers associated to a monad

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Beck coequalizer (as it features heavily in Beck's
monadicity theorem).

This file has been adapted to `Mathlib/CategoryTheory/Monad/Equalizer.lean`.
Please try to keep them in sync.

-/


universe v₁ u₁

namespace CategoryTheory

namespace Monad

open Limits

variable {C : Type u₁}
variable [Category.{v₁} C]
variable {T : Monad C} (X : Algebra T)

/-!
Show that any algebra is a coequalizer of free algebras.
-/


/-- The top map in the coequalizer diagram we will construct. -/
@[simps!]
def FreeCoequalizer.topMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A :=
  (Monad.free T).map X.a

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def FreeCoequalizer.bottomMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  f := T.μ.app X.A
  h := T.assoc X.A

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
def FreeCoequalizer.π : (Monad.free T).obj X.A ⟶ X where
  f := X.a
  h := X.assoc.symm

theorem FreeCoequalizer.condition :
    FreeCoequalizer.topMap X ≫ FreeCoequalizer.π X =
      FreeCoequalizer.bottomMap X ≫ FreeCoequalizer.π X :=
  Algebra.Hom.ext X.assoc.symm

instance : IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) := by
  apply IsReflexivePair.mk' _ _ _
  · apply (free T).map (T.η.app X.A)
  · ext
    dsimp
    rw [← Functor.map_comp, X.unit, Functor.map_id]
  · ext
    apply Monad.right_unit

/-- Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simps!]
def beckAlgebraCofork : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) :=
  Cofork.ofπ _ (FreeCoequalizer.condition X)

/-- The cofork constructed is a colimit. This shows that any algebra is a (reflexive) coequalizer of
free algebras.
-/
def beckAlgebraCoequalizer : IsColimit (beckAlgebraCofork X) :=
  Cofork.IsColimit.mk' _ fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
      congr_arg Monad.Algebra.Hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.pt.a = T.μ.app X.A ≫ s.π.f := s.π.h
    refine ⟨⟨T.η.app _ ≫ s.π.f, ?_⟩, ?_, ?_⟩
    · dsimp
      rw [Functor.map_comp, Category.assoc, h₂, Monad.right_unit_assoc,
        show X.a ≫ _ ≫ _ = _ from T.η.naturality_assoc _ _, h₁, Monad.left_unit_assoc]
    · ext
      simpa [← T.η.naturality_assoc, T.left_unit_assoc] using T.η.app ((T : C ⥤ C).obj X.A) ≫= h₁
    · intro m hm
      ext
      dsimp only
      rw [← hm]
      apply (X.unit_assoc _).symm

/-- The Beck cofork is a split coequalizer. -/
def beckSplitCoequalizer : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a :=
  ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps! pt]
def beckCofork : Cofork (T.map X.a) (T.μ.app _) :=
  (beckSplitCoequalizer X).asCofork

@[simp]
theorem beckCofork_π : (beckCofork X).π = X.a :=
  rfl

/-- The Beck cofork is a coequalizer. -/
def beckCoequalizer : IsColimit (beckCofork X) :=
  (beckSplitCoequalizer X).isCoequalizer

@[simp]
theorem beckCoequalizer_desc (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A)) :
    (beckCoequalizer X).desc s = T.η.app _ ≫ s.π :=
  rfl

end Monad

end CategoryTheory
