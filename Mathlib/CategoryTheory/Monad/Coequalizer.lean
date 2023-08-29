/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Limits.Shapes.Reflexive
import Mathlib.CategoryTheory.Limits.Shapes.SplitCoequalizer
import Mathlib.CategoryTheory.Monad.Algebra

#align_import category_theory.monad.coequalizer from "leanprover-community/mathlib"@"3a061790136d13594ec10c7c90d202335ac5d854"

/-!
# Special coequalizers associated to a monad

Associated to a monad `T : C ⥤ C` we have important coequalizer constructions:
Any algebra is a coequalizer (in the category of algebras) of free algebras. Furthermore, this
coequalizer is reflexive.
In `C`, this cofork diagram is a split coequalizer (in particular, it is still a coequalizer).
This split coequalizer is known as the Beck coequalizer (as it features heavily in Beck's
monadicity theorem).
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
#align category_theory.monad.free_coequalizer.top_map CategoryTheory.Monad.FreeCoequalizer.topMap

/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def FreeCoequalizer.bottomMap : (Monad.free T).obj (T.obj X.A) ⟶ (Monad.free T).obj X.A where
  f := T.μ.app X.A
  h := T.assoc X.A
#align category_theory.monad.free_coequalizer.bottom_map CategoryTheory.Monad.FreeCoequalizer.bottomMap

/-- The cofork map in the coequalizer diagram we will construct. -/
@[simps]
def FreeCoequalizer.π : (Monad.free T).obj X.A ⟶ X where
  f := X.a
  h := X.assoc.symm
#align category_theory.monad.free_coequalizer.π CategoryTheory.Monad.FreeCoequalizer.π

theorem FreeCoequalizer.condition :
    FreeCoequalizer.topMap X ≫ FreeCoequalizer.π X =
      FreeCoequalizer.bottomMap X ≫ FreeCoequalizer.π X :=
  Algebra.Hom.ext _ _ X.assoc.symm
#align category_theory.monad.free_coequalizer.condition CategoryTheory.Monad.FreeCoequalizer.condition

instance : IsReflexivePair (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) := by
  apply IsReflexivePair.mk' _ _ _
  apply (free T).map (T.η.app X.A)
  -- ⊢ (free T).map (NatTrans.app (η T) X.A) ≫ FreeCoequalizer.topMap X = 𝟙 ((free  …
  · ext
    -- ⊢ ((free T).map (NatTrans.app (η T) X.A) ≫ FreeCoequalizer.topMap X).f = (𝟙 (( …
    dsimp
    -- ⊢ T.map (NatTrans.app (η T) X.A) ≫ T.map X.a = 𝟙 (T.obj X.A)
    rw [← Functor.map_comp, X.unit, Functor.map_id]
    -- 🎉 no goals
  · ext
    -- ⊢ ((free T).map (NatTrans.app (η T) X.A) ≫ FreeCoequalizer.bottomMap X).f = (𝟙 …
    apply Monad.right_unit
    -- 🎉 no goals

/-- Construct the Beck cofork in the category of algebras. This cofork is reflexive as well as a
coequalizer.
-/
@[simps!]
def beckAlgebraCofork : Cofork (FreeCoequalizer.topMap X) (FreeCoequalizer.bottomMap X) :=
  Cofork.ofπ _ (FreeCoequalizer.condition X)
#align category_theory.monad.beck_algebra_cofork CategoryTheory.Monad.beckAlgebraCofork

/-- The cofork constructed is a colimit. This shows that any algebra is a (reflexive) coequalizer of
free algebras.
-/
def beckAlgebraCoequalizer : IsColimit (beckAlgebraCofork X) :=
  Cofork.IsColimit.mk' _ fun s => by
    have h₁ : (T : C ⥤ C).map X.a ≫ s.π.f = T.μ.app X.A ≫ s.π.f :=
      congr_arg Monad.Algebra.Hom.f s.condition
    have h₂ : (T : C ⥤ C).map s.π.f ≫ s.pt.a = T.μ.app X.A ≫ s.π.f := s.π.h
    -- ⊢ { l // Cofork.π (beckAlgebraCofork X) ≫ l = Cofork.π s ∧ ∀ {m : ((Functor.co …
    refine' ⟨⟨T.η.app _ ≫ s.π.f, _⟩, _, _⟩
    · dsimp
      -- ⊢ T.map (NatTrans.app (η T) X.1 ≫ (Cofork.π s).f) ≫ s.pt.a = X.a ≫ NatTrans.ap …
      rw [Functor.map_comp, Category.assoc, h₂, Monad.right_unit_assoc,
        show X.a ≫ _ ≫ _ = _ from T.η.naturality_assoc _ _, h₁, Monad.left_unit_assoc]
    · ext
      -- ⊢ (Cofork.π (beckAlgebraCofork X) ≫ Algebra.Hom.mk (NatTrans.app (η T) (beckAl …
      simpa [← T.η.naturality_assoc, T.left_unit_assoc] using T.η.app ((T : C ⥤ C).obj X.A) ≫= h₁
      -- 🎉 no goals
    · intro m hm
      -- ⊢ m = Algebra.Hom.mk (NatTrans.app (η T) (beckAlgebraCofork X).pt.1 ≫ (Cofork. …
      ext
      -- ⊢ m.f = (Algebra.Hom.mk (NatTrans.app (η T) (beckAlgebraCofork X).pt.1 ≫ (Cofo …
      dsimp only
      -- ⊢ m.f = NatTrans.app (η T) (beckAlgebraCofork X).pt.1 ≫ (Cofork.π s).f
      rw [← hm]
      -- ⊢ m.f = NatTrans.app (η T) (beckAlgebraCofork X).pt.1 ≫ (Cofork.π (beckAlgebra …
      apply (X.unit_assoc _).symm
      -- 🎉 no goals
#align category_theory.monad.beck_algebra_coequalizer CategoryTheory.Monad.beckAlgebraCoequalizer

/-- The Beck cofork is a split coequalizer. -/
def beckSplitCoequalizer : IsSplitCoequalizer (T.map X.a) (T.μ.app _) X.a :=
  ⟨T.η.app _, T.η.app _, X.assoc.symm, X.unit, T.left_unit _, (T.η.naturality _).symm⟩
#align category_theory.monad.beck_split_coequalizer CategoryTheory.Monad.beckSplitCoequalizer

/-- This is the Beck cofork. It is a split coequalizer, in particular a coequalizer. -/
@[simps! pt]
def beckCofork : Cofork (T.map X.a) (T.μ.app _) :=
  (beckSplitCoequalizer X).asCofork
#align category_theory.monad.beck_cofork CategoryTheory.Monad.beckCofork

@[simp]
theorem beckCofork_π : (beckCofork X).π = X.a :=
  rfl
#align category_theory.monad.beck_cofork_π CategoryTheory.Monad.beckCofork_π

/-- The Beck cofork is a coequalizer. -/
def beckCoequalizer : IsColimit (beckCofork X) :=
  (beckSplitCoequalizer X).isCoequalizer
#align category_theory.monad.beck_coequalizer CategoryTheory.Monad.beckCoequalizer

@[simp]
theorem beckCoequalizer_desc (s : Cofork (T.toFunctor.map X.a) (T.μ.app X.A)) :
    (beckCoequalizer X).desc s = T.η.app _ ≫ s.π :=
  rfl
#align category_theory.monad.beck_coequalizer_desc CategoryTheory.Monad.beckCoequalizer_desc

end Monad

end CategoryTheory
