/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.Prod

/-!
# Localization of product categories

In this file, it is shown that if for all `j : J` (with `J` finite),
functors `L j : C j ⥤ D j` are localization functors with respect
to a class of morphisms `W j : MorphismProperty (C j)`, then the product
functor `Functor.pi L : (∀ j, C j) ⥤ ∀ j, D j` is a localization
functor for the product class of morphisms `MorphismProperty.pi W`.
The proof proceeds by induction on the cardinal of `J` using the
main result of the file `Mathlib.CategoryTheory.Localization.Prod`.

-/

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsLocalization

instance pi {J : Type w} [Finite J] {C : J → Type u₁} {D : J → Type u₂}
    [∀ j, Category.{v₁} (C j)] [∀ j, Category.{v₂} (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).ContainsIdentities] [∀ j, (L j).IsLocalization (W j)] :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) := by
  revert J
  apply Finite.induction_empty_option
  · intro J₁ J₂ e hJ₁ C₂ D₂ _ _ L₂ W₂ _ _
    let L₁ := fun j => (L₂ (e j))
    let E := Pi.equivalenceOfEquiv C₂ e
    let E' := Pi.equivalenceOfEquiv D₂ e
    haveI : CatCommSq E.functor (Functor.pi L₁) (Functor.pi L₂) E'.functor :=
      (CatCommSq.hInvEquiv E (Functor.pi L₁) (Functor.pi L₂) E').symm ⟨Iso.refl _⟩
    refine IsLocalization.of_equivalences (Functor.pi L₁)
      (MorphismProperty.pi (fun j => (W₂ (e j)))) (Functor.pi L₂)
      (MorphismProperty.pi W₂) E E' ?_
      (MorphismProperty.IsInvertedBy.pi _ _ (fun _ => Localization.inverts _ _))
    intro _ _ f hf
    refine ⟨_, _, E.functor.map f, fun i => ?_, ⟨Iso.refl _⟩⟩
    have H : ∀ {j j' : J₂} (h : j = j') {X Y : C₂ j} (g : X ⟶ Y) (_ : W₂ j g),
        W₂ j' ((Pi.eqToEquivalence C₂ h).functor.map g) := by
      rintro j _ rfl _ _ g hg
      exact hg
    exact H (e.apply_symm_apply i) _ (hf (e.symm i))
  · intro C D _ _ L W _ _
    haveI : ∀ j, IsEquivalence (L j) := by rintro ⟨⟩
    refine IsLocalization.of_isEquivalence _ _ (fun _ _ _ _ => ?_)
    rw [MorphismProperty.isomorphisms.iff, isIso_pi_iff]
    rintro ⟨⟩
  · intro J _ hJ C D _ _ L W _ _
    let L₁ := (L none).prod (Functor.pi (fun j => L (some j)))
    haveI : CatCommSq (Pi.optionEquivalence C).symm.functor L₁ (Functor.pi L)
      (Pi.optionEquivalence D).symm.functor :=
        ⟨NatIso.pi' (by rintro (_|i) <;> apply Iso.refl)⟩
    refine IsLocalization.of_equivalences L₁
      ((W none).prod (MorphismProperty.pi (fun j => W (some j)))) (Functor.pi L) _
      (Pi.optionEquivalence C).symm (Pi.optionEquivalence D).symm ?_ ?_
    · intro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ f ⟨hf₁, hf₂⟩
      refine ⟨_, _, (Pi.optionEquivalence C).inverse.map f, ?_, ⟨Iso.refl _⟩⟩
      · rintro (_|i)
        · exact hf₁
        · apply hf₂
    · apply MorphismProperty.IsInvertedBy.pi
      rintro (_|i) <;> apply Localization.inverts

end CategoryTheory.Functor.IsLocalization
