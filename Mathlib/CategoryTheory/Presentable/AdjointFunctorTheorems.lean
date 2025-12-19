module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Presentable.StrongGenerator
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

universe v u

open CategoryTheory Limits Functor

namespace CategoryTheory.Adjunction

variable {C D : Type u} [Category.{v} C] [Category.{v} D] [IsLocallyPresentable.{v} C]
    [IsLocallyPresentable.{v} D]

lemma presentableAdjointFunctorTheorem₁ (L : C ⥤ D) [PreservesColimits L] [HasColimits C] :
    L.IsLeftAdjoint := by
  sorry

lemma presentableAdjointFunctorTheorem₂ (R : C ⥤ D) [IsAccessible.{v} R] [PreservesLimits R]
    [HasLimits C] : R.IsRightAdjoint := by
  refine isRightAdjoint_of_preservesLimits_of_solutionSetCondition _ fun A ↦ ?_
  obtain ⟨κ₁, _, ⟨h⟩⟩ := IsAccessible.exists_cardinal (F := R)
  obtain ⟨κ₀₁, _, h₁⟩ := IsLocallyPresentable.exists_cardinal (C := C)
  obtain ⟨κ₀₂, _, h₂⟩ := IsLocallyPresentable.exists_cardinal (C := D)
  obtain ⟨κ₀, _, hC, hD⟩ : ∃ (κ₀ : Cardinal.{v}) (_ : Fact κ₀.IsRegular),
      IsCardinalLocallyPresentable C κ₀ ∧ IsCardinalLocallyPresentable D κ₀ := by
    have : Fact (κ₀₁ ⊔ κ₀₂).IsRegular := ⟨iteInduction (fun a ↦ Fact.out) (fun a ↦ Fact.out)⟩
    have h₀₁ : κ₀₁ ≤ κ₀₁ ⊔ κ₀₂ := by simp
    have h₀₂ : κ₀₂ ≤ κ₀₁ ⊔ κ₀₂ := by simp
    refine ⟨κ₀₁ ⊔ κ₀₂, inferInstance, .of_le _ h₀₁, .of_le _ h₀₂⟩
  obtain ⟨P, _, ⟨le, h⟩⟩ := hD.1
  obtain ⟨J, _, cf, ⟨⟨⟨diag, ι, hc⟩, hx⟩⟩⟩ := h A
  obtain ⟨κ', hκ', lt⟩ := HasCardinalLT.exists_regular_cardinal (Arrow J)
  obtain ⟨κ, _, h₀, h₁, ⟨_⟩⟩ : ∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular), κ₀ ≤ κ ∧ κ₁ ≤ κ ∧
      isCardinalPresentable D κ A := by
    have : Fact (κ₀ ⊔ κ₁ ⊔ κ').IsRegular :=
      ⟨iteInduction (fun a ↦ hκ') (fun a ↦ iteInduction (fun a ↦ Fact.out) (fun a ↦ Fact.out))⟩
    have hκ₀ : κ₀ ≤ κ₀ ⊔ κ₁ ⊔ κ' := by simp
    have hκ₁ : κ₁ ≤ κ₀ ⊔ κ₁ ⊔ κ' := by simp
    have (k : J) : IsCardinalPresentable (diag.obj k) (κ₀ ⊔ κ₁ ⊔ κ') := by
      have := le _ (hx k)
      dsimp [isCardinalPresentable] at this
      apply isCardinalPresentable_of_le _ hκ₀
    exact ⟨κ₀ ⊔ κ₁ ⊔ κ', inferInstance, hκ₀, hκ₁,
      isCardinalPresentable_of_isColimit _ hc _ (lt.of_le (by simp))⟩
  obtain ⟨P, _, ⟨_, h⟩⟩ := (IsCardinalLocallyPresentable.of_le C h₀).1
  obtain ⟨Q, _, hQP, hPQ⟩ := ObjectProperty.EssentiallySmall.exists_small_le P
  refine ⟨(X : Shrink (Subtype Q)) × (A ⟶ R.obj ((equivShrink _).symm X).val),
    fun X ↦ ((equivShrink _).symm X.fst).val, fun X ↦ X.snd, fun X f ↦ ?_⟩
  obtain ⟨J, _, _, ⟨⟨⟨diag, ι, hc⟩, hx⟩⟩⟩ := h X
  have : IsCardinalFiltered J κ₁ := IsCardinalFiltered.of_le J h₁
  replace hc := isColimitOfPreserves (coyoneda.obj ⟨A⟩) (isColimitOfPreserves R hc)
  obtain ⟨j, hj, w⟩ := Types.jointly_surjective_of_isColimit hc f
  obtain ⟨d, hd, ⟨i⟩⟩ := hPQ _ (hx j)
  exact ⟨⟨equivShrink _ ⟨d, hd⟩, hj ≫ R.map i.hom ≫ R.map (eqToHom (by simp))⟩,
    eqToHom (by simp) ≫ i.inv ≫ ι.app _, by simp [← w]⟩

end CategoryTheory.Adjunction
