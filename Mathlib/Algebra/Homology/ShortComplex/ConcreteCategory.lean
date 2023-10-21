import Mathlib.Algebra.Homology.ShortComplex.Ab

namespace CategoryTheory

namespace ShortComplex

section

variable {C : Type _} [Category C] [ConcreteCategory C] [Limits.HasZeroMorphisms C]
  [HasForget₂ C Ab] [(forget₂ C Ab).PreservesZeroMorphisms]-- [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

@[simp]
lemma zero_apply (x : (forget₂ C Ab).obj S.X₁) :
    ((forget₂ C Ab).map S.g) (((forget₂ C Ab).map S.f) x) = 0 := by
  erw [← comp_apply, ← Functor.map_comp, S.zero, Functor.map_zero]
  rfl

end

end ShortComplex

section abelian

variable {C : Type _} [Category C] [ConcreteCategory C]
  [HasForget₂ C Ab] [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  (S : ShortComplex C)

lemma Abelian.mono_iff_injective {X Y : C} (f : X ⟶ Y) :
    Mono f ↔ Function.Injective ((forget₂ C Ab).map f) := by
  rw [← AddCommGroupCat.mono_iff_injective]
  constructor
  · intro
    infer_instance
  · apply Functor.mono_of_mono_map

lemma Abelian.epi_iff_injective {X Y : C} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective ((forget₂ C Ab).map f) := by
  rw [← AddCommGroupCat.epi_iff_surjective]
  constructor
  · intro
    infer_instance
  · apply Functor.epi_of_epi_map

namespace ShortComplex

lemma exact_iff_exact_map_forget₂ : S.Exact ↔ (S.map (forget₂ C Ab)).Exact :=
  (S.exact_map_iff_of_faithful (forget₂ C Ab)).symm

lemma exact_iff_of_concrete_category :
  S.Exact ↔ ∀ (x₂ : (forget₂ C Ab).obj S.X₂) (_ : ((forget₂ C Ab).map S.g) x₂ = 0),
    ∃ (x₁ : (forget₂ C Ab).obj S.X₁), ((forget₂ C Ab).map S.f) x₁ = x₂ := by
  rw [S.exact_iff_exact_map_forget₂, ab_exact_iff]
  rfl

variable {S}

lemma ShortExact.injective_f (hS : S.ShortExact) :
    Function.Injective ((forget₂ C Ab).map S.f) := by
  rw [← Abelian.mono_iff_injective]
  exact hS.mono_f

lemma ShortExact.surjective_g (hS : S.ShortExact) :
    Function.Surjective ((forget₂ C Ab).map S.g) := by
  rw [← Abelian.epi_iff_injective]
  exact hS.epi_g

end ShortComplex

end abelian

end CategoryTheory
