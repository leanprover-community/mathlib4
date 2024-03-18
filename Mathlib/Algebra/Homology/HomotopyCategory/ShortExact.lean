import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Refinements
import Mathlib.Algebra.Homology.HomologicalComplexLimits

open CategoryTheory Category Limits Preadditive
  HomologicalComplex
variable {C : Type _} [Category C] [Abelian C]

namespace CochainComplex

variable (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)

namespace mappingCone

noncomputable def fromOfShortComplex :
  mappingCone S.f ⟶ S.X₃ := desc S.f 0 S.g (by simp)

variable {S}

lemma isIso_homologyMap_fromOfShortComplex (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (fromOfShortComplex S) n) := by
  have hS' := fun i => hS.map_of_exact (HomologicalComplex.eval C (ComplexShape.up ℤ) i)
  have : ∀ i, Mono (S.f.f i) := fun i => (hS' i).mono_f
  have : ∀ i, Epi (S.g.f i) := fun i => (hS' i).epi_g
  rw [isIso_iff_mono_and_epi]
  constructor
  · rw [mono_homologyMap_iff_up_to_refinements _ (n-1) n (n+1) (by simp) (by simp)]
    intro A₀ a ha b hb
    obtain ⟨a₁, a₂, ha₁₂⟩ := to_break _ a _ rfl
    simp [ha₁₂, ext_to_iff _ _ (n+2) (show n + 1 + 1 = n + 2 by linarith),
      inl_v_d_assoc _ (n + 1) n (n + 2) (by linarith) (by linarith)] at ha
    obtain ⟨A₁, π₁, hπ₁, c, hc⟩ := surjective_up_to_refinements_of_epi (S.g.f (n-1)) b
    obtain ⟨A₂, π₂, hπ₂, e, he⟩ := (hS' n).exact.exact_up_to_refinements
      (π₁ ≫ a₂ - c ≫ S.X₂.d (n-1) n) (by
        dsimp
        simp only [sub_comp, assoc, ← S.g.comm, ← reassoc_of% hc, ← hb, ha₁₂, add_comp,
          fromOfShortComplex, inl_v_desc_f, HomComplex.Cochain.zero_v, comp_zero,
          inr_f_desc_f, zero_add, sub_self])
    dsimp at e he
    simp only [comp_sub] at he
    refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _, e ≫ (inl S.f).v n (n - 1) (by linarith) +
      π₂ ≫ c ≫ (inr S.f).f (n - 1), _⟩
    simp only [ext_to_iff _ _ (n + 1) rfl, ha₁₂, comp_add, assoc, sub_add_cancel,
      add_comp, inr_f_d, inl_v_fst_v, comp_id, inr_f_fst_v, comp_zero, add_zero,
      d_fst_v', comp_neg, inl_v_fst_v_assoc, inl_v_snd_v, inr_f_snd_v, zero_add,
      d_snd_v', inl_v_snd_v_assoc, zero_comp]
    constructor
    · simp only [← cancel_mono (S.f.f (n+1)), assoc, neg_comp, ← S.f.comm,
        ← reassoc_of% he, d_comp_d, sub_comp, comp_zero, sub_zero]
      simp only [← add_eq_zero_iff_eq_neg, ← comp_add, ha.2, comp_zero]
    · rw [← he, sub_add_cancel]
  · rw [epi_homologyMap_iff_up_to_refinements _ (n-1) n (n+1) (by simp) (by simp)]
    intro A₀ a ha
    obtain ⟨A₁, π₁, hπ₁, b, hb⟩ := surjective_up_to_refinements_of_epi (S.g.f n) a
    obtain ⟨A₂, π₂, hπ₂, c, hc⟩ := (hS' (n+1)).exact.exact_up_to_refinements (b ≫ S.X₂.d n (n+1)) (by
      dsimp
      simp only [assoc, ← S.g.comm, ← reassoc_of% hb, ha, comp_zero])
    dsimp at c hc
    refine' ⟨A₂, π₂ ≫ π₁, epi_comp _ _ , -c ≫ (inl S.f).v (n+1) n (by linarith) +
        π₂ ≫ b ≫ (inr S.f).f n, _, 0, _ ⟩
    · dsimp
      simp [ext_to_iff _ _ (n + 2) (show n + 1 + 1 = n + 2 by linarith),
        d_fst_v _ n (n+1) (n+2) (by linarith) (by linarith)]
      constructor
      · simp only [← cancel_mono (S.f.f (n+2)), assoc, zero_comp, ← S.f.comm,
          ← reassoc_of% hc, d_comp_d, comp_zero]
      · dsimp
        simp only [d_snd_v _ n (n + 1) rfl, comp_add, inl_v_fst_v_assoc,
          inl_v_snd_v_assoc, zero_comp, add_zero, hc, add_left_neg]
    · dsimp [fromOfShortComplex]
      simp only [hb, assoc, add_comp, neg_comp, inl_v_desc_f, HomComplex.Cochain.zero_v,
        comp_zero, neg_zero, inr_f_desc_f, zero_add, ComplexShape.up_Rel,
        sub_add_cancel, not_true, zero_comp, add_zero]

end mappingCone

end CochainComplex
