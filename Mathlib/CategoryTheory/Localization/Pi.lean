import Mathlib.CategoryTheory.Localization.Prod

universe v₁ v₂ v₃ u₁ u₂ u₃ u₄

namespace CategoryTheory

def Pi.equivalence_of_eq {I : Type u₂} (C : I → Type u₁)
  [∀ i, Category.{v₁} (C i)] {i j : I} (h : i = j) :
    C i ≌ C j := by
  subst h
  rfl

@[simp]
def Pi.eval_comp_equivalence_of_eq_functor {I : Type u₂} (C : I → Type u₁)
  [∀ i, Category.{v₁} (C i)] {i j : I} (h : i = j) :
  Pi.eval C i ⋙ (Pi.equivalence_of_eq _ h).functor ≅
    Pi.eval C j := eqToIso (by subst h; rfl)

@[simp]
def Pi.equivalence_of_eq_functor_iso {I : Type u₂} {I' : Type u₃}
  (C : I → Type u₁) [∀ i, Category.{v₁} (C i)] {i' j' : I'}
  (f : I' → I) (h : i' = j') :
    (Pi.equivalence_of_eq C (show f i' = f j' by rw [h])).functor ≅
      (Pi.equivalence_of_eq (fun i' => C (f i')) h).functor := eqToIso (by subst h; rfl)

@[simp]
def Functor.pi'_eval_iso {I : Type u₂} {C : I → Type u₁}
  [∀ i, Category.{v₁} (C i)] {A : Type u₄} [Category.{v₄} A]
  (f : ∀ i, A ⥤ C i) (i : I) : pi' f ⋙  Pi.eval C i ≅ f i :=
  eqToIso (Functor.pi'_eval _ _)

-- should be moved to Pi.Basic
noncomputable def pi_equivalence_of_equiv {I : Type u₂} {I' : Type u₃} (C : I → Type u₁)
  [∀ i, Category.{v₁} (C i)] (e : I' ≃ I) :
  (∀ j, C (e j)) ≌ (∀ i, C i) :=
{ functor := Functor.pi' (fun i => Pi.eval _ (e.symm i) ⋙
    (Pi.equivalence_of_eq C (by simp)).functor)
  inverse := Functor.pi' (fun i' => Pi.eval _ (e i'))
  unitIso := NatIso.pi' (fun i' => Functor.leftUnitor _ ≪≫
    (Pi.eval_comp_equivalence_of_eq_functor (fun j => C (e j)) (e.symm_apply_apply i')).symm ≪≫
      isoWhiskerLeft _ ((Pi.equivalence_of_eq_functor_iso C e (e.symm_apply_apply i')).symm) ≪≫
      (Functor.pi'_eval_iso _ _).symm ≪≫ isoWhiskerLeft _ (Functor.pi'_eval_iso _ _).symm ≪≫
      (Functor.associator _ _ _).symm)
  counitIso := NatIso.pi' (fun i => (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Functor.pi'_eval_iso _ _) _ ≪≫
    Pi.eval_comp_equivalence_of_eq_functor C (e.apply_symm_apply i) ≪≫
    (Functor.leftUnitor _).symm)
  functor_unitIso_comp := by
    intro
    ext
    dsimp
    simp [eqToHom_map] }

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
  . intro J₁ J₂ e hJ₁ C₂ D₂ hC₂ _ L₂ W₂ _ _
    let C₁ := fun j => (C₂ (e j))
    let D₁ := fun j => (D₂ (e j))
    let L₁ : ∀ j, C₁ j ⥤ D₁ j := fun j => (L₂ (e j))
    let W₁ : ∀ j, MorphismProperty (C₁ j) := fun j => (W₂ (e j))
    replace hJ₁ := hJ₁ L₁ W₁
    letI : ∀ i, Category (C₂ i) := by apply hC₂
    let E := pi_equivalence_of_equiv C₂ e
    let E' := pi_equivalence_of_equiv D₂ e
    haveI : CatCommSq (Functor.pi L₁) E.functor (Functor.pi L₂) E'.functor :=
      CatCommSq.hInv' _ _ _ _ ⟨Iso.refl _⟩
    refine' IsLocalization.of_equivalences (Functor.pi L₁)
      (MorphismProperty.pi W₁) (Functor.pi L₂) (MorphismProperty.pi W₂) E E' _
      (MorphismProperty.IsInvertedBy.pi _ _ (fun j => Localization.inverts _ _))
    sorry
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
    haveI : CatCommSq L₁ (pi_option_equivalence C).symm.functor L₂
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
  pi _ _ _

end IsLocalization

end Functor

end CategoryTheory
