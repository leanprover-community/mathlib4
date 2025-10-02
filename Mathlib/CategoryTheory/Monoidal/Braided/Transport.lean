/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Transport

/-!

# Transport a symmetric monoidal structure along an equivalence of categories
-/

universe v₁ v₂ u₁ u₂

open CategoryTheory Category Monoidal MonoidalCategory

noncomputable section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace CategoryTheory.Monoidal

open Functor.LaxMonoidal Functor.OplaxMonoidal

instance Transported.instBraidedCategory (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    BraidedCategory (Transported e) :=
  BraidedCategory.ofFullyFaithful (equivalenceTransported e).inverse

local notation "e'" e => equivalenceTransported e

instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).inverse.Braided where
  braided X Y := by
    simp [Transported.instBraidedCategory, BraidedCategory.ofFullyFaithful,
      BraidedCategory.ofFaithful]

/--
This is a def because once we have that both `(e' e).inverse` and `(e' e).functor` are
braided, this causes a diamond.
-/
def transportedFunctorCompInverseLaxBraided (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).LaxBraided :=
  Functor.LaxBraided.ofNatIso (e' e).unitIso

attribute [local instance] transportedFunctorCompInverseLaxBraided in
/--
This is a def because once we have that both `(e' e).inverse` and `(e' e).functor` are
braided, this causes a diamond.
-/
def transportedFunctorCompInverseBraided (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    ((e' e).functor ⋙ (e' e).inverse).Braided where

attribute [local instance] transportedFunctorCompInverseBraided in
instance (e : C ≌ D) [MonoidalCategory C] [BraidedCategory C] :
    (e' e).functor.Braided where
  braided X Y := by
    apply (e' e).inverse.map_injective
    have : Functor.LaxMonoidal.μ (((e' e).functor ⋙ (e' e).inverse)) X Y ≫
        ((e' e).functor ⋙ (e' e).inverse).map (β_ X Y).hom ≫
          Functor.OplaxMonoidal.δ ((e' e).functor ⋙ (e' e).inverse) Y X =
            (β_ (((e' e).functor ⋙ (e' e).inverse).obj X)
              (((e' e).functor ⋙ (e' e).inverse).obj Y)).hom := by
      simp only [((e' e).functor ⋙ (e' e).inverse).map_braiding X Y,
        Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, assoc,
        Functor.Monoidal.μ_δ, comp_id, Functor.Monoidal.μ_δ_assoc]
    simp? [-Adjunction.rightAdjointLaxMonoidal_μ]  at this says
      simp only [Functor.comp_obj, Functor.CoreMonoidal.toMonoidal_toLaxMonoidal,
        Equivalence.symm_inverse, Equivalence.symm_functor,
        Functor.CoreMonoidal.toMonoidal_toOplaxMonoidal, comp_μ, Functor.comp_map,
        Equivalence.inv_fun_map, Functor.id_obj, comp_δ, assoc] at this
    simp [-Adjunction.rightAdjointLaxMonoidal_μ, ← this]

instance Transported.instSymmetricCategory (e : C ≌ D) [MonoidalCategory C]
    [SymmetricCategory C] : SymmetricCategory (Transported e) :=
  symmetricCategoryOfFullyFaithful (equivalenceTransported e).inverse

end CategoryTheory.Monoidal
