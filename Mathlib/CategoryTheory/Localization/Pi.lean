import Mathlib.CategoryTheory.Localization.Prod

universe v₁ v₂ v₃ u₀ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable (J : Type u₀) (C : J → Type u₁) {D : J → Type u₂}
  [∀ j, Category.{v₁} (C j)] [∀ j, Category.{v₂} (D j)]
  (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
  [∀ j, (W j).ContainsIdentities]
  [∀ j, (L j).IsLocalization (W j)]

namespace Functor

namespace IsLocalization

instance pi [Finite J] :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) := by
  let P : Type u₀ → Prop := fun J => ∀ {C : J → Type u₁} {D : J → Type u₂}
    [∀ j, Category.{v₁} (C j)] [∀ j, Category.{v₂} (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).ContainsIdentities] [∀ j, (L j).IsLocalization (W j)],
      (Functor.pi L).IsLocalization (MorphismProperty.pi W)
  suffices P J
    by apply this
  apply @Finite.induction_empty_option P
  . intro J₁ J₂ e hJ₁ C₂ D₂ hC₂ _ L₂ W₂ _ _
    let C₁ := fun j => (C₂ (e j))
    let D₁ := fun j => (D₂ (e j))
    let L₁ : ∀ j, C₁ j ⥤ D₁ j := fun j => (L₂ (e j))
    let W₁ : ∀ j, MorphismProperty (C₁ j) := fun j => (W₂ (e j))
    replace hJ₁ := hJ₁ L₁ W₁
    letI : ∀ i, Category (C₂ i) := by apply hC₂
    let E := pi_equivalence_of_equiv C₂ e
    let E' := pi_equivalence_of_equiv D₂ e
    haveI : CatCommSq E.functor (Functor.pi L₁) (Functor.pi L₂) E'.functor :=
      (CatCommSq.hInvEquiv E (Functor.pi L₁) (Functor.pi L₂) E').symm ⟨Iso.refl _⟩
    refine' IsLocalization.of_equivalences (Functor.pi L₁)
      (MorphismProperty.pi W₁) (Functor.pi L₂) (MorphismProperty.pi W₂) E E' _
      (MorphismProperty.IsInvertedBy.pi _ _ (fun j => Localization.inverts _ _))
    intro _ _ f hf
    refine' ⟨_, _, E.functor.map f, _, ⟨Iso.refl _⟩⟩
    intro i
    have hf' := hf (e.symm i)
    dsimp
    have H : ∀ {j j' : J₂} (h : j = j') {X Y : C₂ j} (g : X ⟶ Y) (_ : W₂ j g),
        W₂ j' ((Pi.equivalence_of_eq C₂ h).functor.map g) := by
      rintro j _ rfl _ _ g hg
      exact hg
    exact H (e.apply_symm_apply i) _ hf'
  . intro C D _ _ L W _ _
    haveI : ∀ j, IsEquivalence (L j) := by rintro ⟨⟩
    refine' of_equivalence _ _ (fun _ _ _ _ => _)
    rw [MorphismProperty.isomorphisms.iff, isIso_pi_iff]
    rintro ⟨⟩
  . intro J _ hJ C D _ _ L W _ _
    let C' := fun j => C (some j)
    let D' := fun j => D (some j)
    let L' : ∀ j, C' j ⥤ D' j := fun j => L (some j)
    let W' : ∀ j, MorphismProperty (C' j) := fun j => W (some j)
    replace hJ := hJ L' W'
    haveI : IsLocalization ((L none).prod (Functor.pi L'))
      ((W none).prod (MorphismProperty.pi W')) := inferInstance
    let L₁ := (L none).prod (Functor.pi L')
    let L₂ := Functor.pi L
    let W₁ := (W none).prod (MorphismProperty.pi W')
    let W₂ := MorphismProperty.pi W
    haveI : CatCommSq (pi_option_equivalence C).symm.functor L₁ L₂
      (pi_option_equivalence D).symm.functor :=
        ⟨NatIso.pi' (by rintro (_|i) <;> apply Iso.refl)⟩
    refine' IsLocalization.of_equivalences L₁ W₁ L₂ W₂
      (pi_option_equivalence C).symm (pi_option_equivalence D).symm _ _
    . intro ⟨X₁, X₂⟩ ⟨Y₁, Y₂⟩ f ⟨hf₁, hf₂⟩
      refine' ⟨_, _, (pi_option_equivalence C).inverse.map f, _, ⟨Iso.refl _⟩⟩
      . rintro (_|i)
        . exact hf₁
        . apply hf₂
    . apply MorphismProperty.IsInvertedBy.pi
      rintro (_|i) <;> apply Localization.inverts

instance pi' [Finite J] :
    (Functor.pi (fun j => (W j).Q)).IsLocalization (MorphismProperty.pi W) :=
  inferInstance

end IsLocalization

end Functor

end CategoryTheory
