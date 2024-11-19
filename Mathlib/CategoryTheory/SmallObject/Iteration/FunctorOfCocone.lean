/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.CategoryTheory.SmallObject.Iteration.Basic

/-!
# ...

-/

universe u

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C : Type*} [Category C]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J]
  {j : J} {F : Set.Iio j ⥤ C} (c : Cocone F)

namespace ofCocone

def obj (i : J) (_ : i ≤ j) : C :=
  if hi : i < j then
    F.obj ⟨i, hi⟩
  else c.pt

def objIso (i : J) (hi : i < j) :
    obj c i hi.le ≅ F.obj ⟨i, hi⟩ :=
  eqToIso (dif_pos hi)

def objIsoPt :
    obj c j (by rfl) ≅ c.pt :=
  eqToIso (dif_neg (by simp))

def map (i₁ i₂ : J) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ j) :
    obj c i₁ (hi.trans hi₂) ⟶ obj c i₂ hi₂ :=
  if h₂ : i₂ < j then
    (objIso c i₁ (lt_of_le_of_lt hi h₂)).hom ≫ F.map (homOfLE hi) ≫ (objIso c i₂ h₂).inv
  else
    have h₂' : i₂ = j := le_antisymm hi₂ (by simpa using h₂)
    if h₁ : i₁ < j then
      (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫ (objIsoPt c).inv ≫ eqToHom (by subst h₂'; rfl)
    else
      have h₁' : i₁ = j := le_antisymm (hi.trans hi₂) (by simpa using h₁)
      eqToHom (by subst h₁' h₂'; rfl)

end ofCocone

open ofCocone in
def ofCocone : Set.Iic j ⥤ C where
  obj i := obj c i.1 i.2
  map f := map c _ _ (leOfHom f) _
  map_id := sorry
  map_comp := sorry

end Functor

end CategoryTheory
