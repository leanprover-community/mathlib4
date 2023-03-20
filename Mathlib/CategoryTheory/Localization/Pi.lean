import Mathlib.CategoryTheory.Localization.Prod

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (J : Type) {C : J → Type u₁} {D : J → Type u₂}
  [∀ j, Category.{v₁} (C j)] [∀ j, Category.{v₂} (D j)]
  (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
  [∀ j, (W j).ContainsIdentities]
  [∀ j, (L j).IsLocalization (W j)]

namespace Functor

namespace IsLocalization

lemma pi [Finite J] :
    (Functor.pi L).IsLocalization (MorphismProperty.pi W) := by
  let P : Type → Prop := fun J => ∀ {C : J → Type u₁} {D : J → Type u₂}
    [∀ j, Category.{v₁} (C j)] [∀ j, Category.{v₂} (D j)]
    (L : ∀ j, C j ⥤ D j) (W : ∀ j, MorphismProperty (C j))
    [∀ j, (W j).ContainsIdentities] [∀ j, (L j).IsLocalization (W j)],
      (Functor.pi L).IsLocalization (MorphismProperty.pi W)
  suffices P J
    by apply this
  apply @Finite.induction_empty_option P
  . intro J₁ J₂ e hJ₁ C D _ _ L W _ _
    sorry
  . intro C D _ _ L W _ _
    haveI : ∀ j, IsEquivalence (L j) := by rintro ⟨⟩
    refine' of_equivalence _ _ (fun _ _ _ _ => _)
    rw [MorphismProperty.isomorphisms.iff, isIso_pi_iff]
    rintro ⟨⟩
  . intro J _ hJ C D _ _ L W _ _
    let C' := fun j => C (some j)
    let D' := fun j => D (some j)
    let W' := fun j => W (some j)
    let L' : ∀ j, C' j ⥤ D' j := fun j => L (some j)
    replace hJ := hJ L' W'
    --haveI : IsLocalization ((L none).prod (Functor.pi L'))
    --  ((W none).prod (MorphismProperty.pi W')) := inferInstance
    sorry

instance pi' [Finite J] :
    (Functor.pi (fun j => (W j).Q)).IsLocalization (MorphismProperty.pi W) :=
  pi _ _ _

end IsLocalization

end Functor

end CategoryTheory
