import Mathlib.CategoryTheory.Monoidal.Discrete

namespace CategoryTheory

namespace Discrete

variable {α β γ : Type*} [AddMonoid α] [AddMonoid β] [AddMonoid γ]
  (i : α →+ β) (p : β →+ γ) {C : Type*} [Category C] [MonoidalCategory C]

structure QuotientData where
  σ : γ → β
  hσ (c : γ) : p (σ c) = c
  --add_inj (a : α) (b : β) (h : b + i a = b) : a = 0
  exact (b₁ b₂ : β) : p b₁ = p b₂ ↔ ∃ (b₀ : β) (a₁ a₂ : α), b₀ + i a₁ = b₁ ∧ b₀ + i a₂ = b₂

variable {i p}

namespace QuotientData

attribute [simp] hσ

end QuotientData

attribute [local simp] eqToHom_map

open MonoidalCategory

structure InducedFunctorData (F : MonoidalFunctor (Discrete β) C) (q : QuotientData i p) where
  iso (a : α) : F.obj ⟨i a⟩ ≅ 𝟙_ C
  iso_zero : iso 0 = F.mapIso (eqToIso (by aesop)) ≪≫ F.εIso.symm
  iso_add (a b : α) : iso (a + b) = F.mapIso (eqToIso (by aesop)) ≪≫
    (F.μIso ⟨i a⟩ ⟨i b⟩).symm ≪≫ (iso a ⊗ iso b) ≪≫ λ_ _

variable {F : MonoidalFunctor (Discrete β) C} {q : QuotientData i p}

namespace InducedFunctorData

variable (hF : InducedFunctorData F q)

noncomputable def addIso (b₁ b₂ : β) (a : α) (h : b₁ + i a = b₂) : F.obj ⟨b₁⟩ ≅ F.obj ⟨b₂⟩ :=
  (ρ_ _).symm ≪≫ (Iso.refl (F.obj ⟨b₁⟩) ⊗ hF.iso a).symm ≪≫ F.μIso ⟨b₁⟩ ⟨i a⟩ ≪≫
    (eqToIso (by subst h; rfl))

noncomputable def addAddIso (b₁ b₂ b₀ : β) (a₁ a₂ : α)
    (h₁ : b₀ + i a₁ = b₁) (h₂ : b₀ + i a₂ = b₂) : F.obj ⟨b₁⟩ ≅ F.obj ⟨b₂⟩ :=
  (hF.addIso b₀ b₁ a₁ h₁).symm ≪≫ hF.addIso b₀ b₂ a₂ h₂

/-lemma addAddIso_eq (b₁ b₂ b₀ b₀' : β) (a₁ a₂ a₁' a₂' : α)
    (h₁ : b₀ + i a₁ = b₁) (h₂ : b₀ + i a₂ = b₂)
    (h₁' : b₀' + i a₁' = b₁) (h₂' : b₀' + i a₂' = b₂) :
    hF.addAddIso b₁ b₂ b₀ a₁ a₂ h₁ h₂ = hF.addAddIso b₁ b₂ b₀' a₁' a₂' h₁' h₂' := by
  sorry-/

noncomputable def iso' (b₁ b₂ : β) (h : p b₁ = p b₂) :
    F.obj ⟨b₁⟩ ≅ F.obj ⟨b₂⟩ :=
  hF.addAddIso b₁ b₂ _ _ _ ((q.exact b₁ b₂).1 h).choose_spec.choose_spec.choose_spec.1
    ((q.exact b₁ b₂).1 h).choose_spec.choose_spec.choose_spec.2

/-lemma iso'_eq (b₁ b₂ b₀ : β) (a₁ a₂ : α)
    (h₁ : b₀ + i a₁ = b₁) (h₂ : b₀ + i a₂ = b₂) :
    hF.iso' b₁ b₂ ((q.exact b₁ b₂).2 ⟨_, _, _, h₁, h₂⟩) =
      hF.addAddIso b₁ b₂ b₀ a₁ a₂ h₁ h₂ := by
  apply addAddIso_eq-/

/-noncomputable def inducedFunctor : MonoidalFunctor (Discrete γ) C where
  obj := fun ⟨x⟩ => F.obj ⟨q.σ x⟩
  map {X Y} f := F.map (eqToHom (by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    obtain ⟨⟨rfl⟩⟩ := f
    rfl))
  map_id := by aesop_cat
  map_comp := by aesop_cat
  ε := F.ε ≫ (hF.iso' _ _ (by simp)).hom
  μ _ _ := F.μ _ _ ≫ (hF.iso' _ _ (by simp)).hom
  μ_natural := by
    rintro ⟨c₁⟩ ⟨c₁'⟩ ⟨c₂⟩ ⟨c₂'⟩ f g
    obtain rfl : c₁ = c₁' := by
      obtain ⟨⟨rfl⟩⟩ := f
      rfl
    obtain rfl : c₂ = c₂' := by
      obtain ⟨⟨rfl⟩⟩ := g
      rfl
    obtain rfl := Subsingleton.elim f (𝟙 _)
    obtain rfl := Subsingleton.elim g (𝟙 _)
    dsimp
    simp
  ε_isIso := by dsimp; infer_instance
  μ_isIso _ _ := by dsimp; infer_instance
  left_unitality := sorry
  right_unitality := sorry
  associativity := sorry-/

end InducedFunctorData

end Discrete

end CategoryTheory
