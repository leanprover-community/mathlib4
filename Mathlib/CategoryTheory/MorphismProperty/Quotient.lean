/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.Quotient

/-!
# Classes of morphisms induced on quotient categories

-/

@[expose] public section

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type*} [Category C]

class HasQuotient (W : MorphismProperty C) (homRel : HomRel C) : Prop where
  iff (W) : ∀ ⦃X Y : C⦄ ⦃f g : X ⟶ Y⦄, homRel f g → (W f ↔ W g)
  compClosure_eq_self : Quotient.CompClosure homRel = homRel

variable (W : MorphismProperty C) {homRel : HomRel C}

lemma HasQuotient.iff_of_eqvGen [W.HasQuotient homRel] {X Y : C} {f g : X ⟶ Y}
    (h : Relation.EqvGen (@homRel _ _) f g) : W f ↔ W g := by
  induction h with
  | rel _ _ h => exact iff W h
  | refl => rfl
  | symm _ _ _ h => exact h.symm
  | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂

variable (homRel)

@[nolint unusedArguments]
def quotient [W.HasQuotient homRel] : MorphismProperty (Quotient homRel) :=
  fun ⟨X⟩ ⟨Y⟩ f ↦ ∃ (f' : X ⟶ Y) (_ : W f'), f = (Quotient.functor _).map f'

lemma quotient_iff [W.HasQuotient homRel] {X Y : C} (f : X ⟶ Y) :
    W.quotient homRel ((Quotient.functor homRel).map f) ↔ W f := by
  constructor
  · rintro ⟨f', hf', h⟩
    rw [← Functor.homRel_iff, Quotient.functor_homRel_eq_compClosure_eqvGen,
      HasQuotient.compClosure_eq_self (W := W)] at h
    rwa [HasQuotient.iff_of_eqvGen W h]
  · intro hf
    exact ⟨f, hf, rfl⟩

lemma eq_inverseImage_quotientFunctor [W.HasQuotient homRel] :
    W = (W.quotient homRel).inverseImage (Quotient.functor _) := by
  ext
  symm
  apply quotient_iff

end MorphismProperty

end CategoryTheory
