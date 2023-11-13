import Mathlib.CategoryTheory.Sites.RegularExtensive

open CategoryTheory Limits

variable {C : Type*} [Category C] [FinitaryPreExtensive C] [Preregular C]
  [∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [EffectiveEpi f] [EffectiveEpi g], EffectiveEpi (f ≫ g)]

instance : Precoherent C where
  pullback {B₁ B₂} f α _ X₁ π₁ h := by
    refine ⟨α, inferInstance, ?_⟩
    obtain ⟨Y, g, _, g', hg⟩ := Preregular.exists_fac f (Sigma.desc π₁)
    have hh : IsIso (Sigma.desc (fun a ↦ Sigma.ι X₁ a)) := by
      suffices Sigma.desc (fun a ↦ Sigma.ι X₁ a) = 𝟙 _ by rw [this]; infer_instance
      ext; simp
    let X₂ := fun a ↦ pullback g' (Sigma.ι X₁ a)
    have hi : IsIso (Sigma.desc (fun a ↦ Sigma.ι X₂ a)) := by
      suffices Sigma.desc (fun a ↦ Sigma.ι X₂ a) = 𝟙 _ by rw [this]; infer_instance
      ext; simp
    let π₂ := fun a ↦ pullback.fst (f := g') (g := Sigma.ι X₁ a) ≫ g
    let π' := fun a ↦ pullback.fst (f := g') (g := Sigma.ι X₁ a)
    have _ : IsIso (Sigma.desc π') := FinitaryPreExtensive.sigma_desc_iso (fun a ↦ Sigma.ι X₁ a) g' hh
    refine ⟨X₂, π₂, ⟨⟨@EffectiveEpiFamilyOfEffectiveEpiDesc _ _ _ _ X₂ π₂ _ ?_ ?_ ?_ ?_⟩⟩, ?_⟩
    · have : (Sigma.desc π' ≫ g) = Sigma.desc π₂ := by ext; simp
      rw [← this]
      exact ⟨⟨EffectiveEpiStruct_of_comp_splitEpi g (Sigma.desc π')⟩⟩
    · intro Z g a
      exact FinitaryPreExtensive.hasPullbacks_of_inclusions g a (hi := hi)
    · intro Z g
      infer_instance
    · intro Z g
      have := FinitaryPreExtensive.sigma_desc_iso (fun a ↦ Sigma.ι X₂ a) g hi
      infer_instance
    · refine ⟨id, fun b ↦ pullback.snd, ?_⟩
      intro b
      simp only [id_eq, Category.assoc, ← hg]
      rw [← Category.assoc, pullback.condition]
      simp
