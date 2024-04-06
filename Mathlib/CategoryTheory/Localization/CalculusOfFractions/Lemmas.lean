import Mathlib.CategoryTheory.Localization.CalculusOfFractions.Preadditive

namespace CategoryTheory

open Category

variable {C D E : Type*} [Category C] [Category D] [Category E]

-- should be moved
lemma Functor.full_of_precomp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    (h : ∀ ⦃X₁ X₂ : C⦄ (φ : (F.obj (L.obj X₁)) ⟶ F.obj (L.obj X₂)),
      ∃ (f : L.obj X₁ ⟶ L.obj X₂), φ = F.map f) :
    Full F := Functor.fullOfSurjective _ (by
  intro X₁ X₂ ψ
  obtain ⟨f, hf⟩ := h (F.map (L.objObjPreimageIso X₁).hom ≫ ψ ≫
    F.map (L.objObjPreimageIso X₂).inv)
  refine ⟨(L.objObjPreimageIso X₁).inv ≫ f ≫ (L.objObjPreimageIso X₂).hom, ?_⟩
  rw [F.map_comp, F.map_comp, ← hf, assoc, assoc, ← F.map_comp_assoc, ← F.map_comp,
    Iso.inv_hom_id, Iso.inv_hom_id, F.map_id, F.map_id, comp_id, id_comp])

-- should be moved
lemma Functor.faithful_of_precomp_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    (h : ∀ ⦃X₁ X₂ : C⦄ (f g : L.obj X₁ ⟶ L.obj X₂), F.map f = F.map g → f = g) :
    Faithful F where
  map_injective := by
    intro Y₁ Y₂ f g hfg
    rw [← cancel_mono (L.objObjPreimageIso Y₂).inv, ← cancel_epi (L.objObjPreimageIso Y₁).hom]
    apply h
    simp [hfg]

lemma Functor.faithful_of_precomp_cancel_zero_essSurj (F : D ⥤ E) (L : C ⥤ D) [EssSurj L]
    [Preadditive D] [Preadditive E] [F.Additive]
    (h : ∀ ⦃X₁ X₂ : C⦄ (f : L.obj X₁ ⟶ L.obj X₂), F.map f = 0 → f = 0) :
    Faithful F :=
  F.faithful_of_precomp_essSurj L (fun X₁ X₂ f g hfg => by
    rw [← sub_eq_zero]
    exact h _ (by rw [F.map_sub, hfg, sub_self]))

section

variable (F : D ⥤ E) (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
  [W.HasLeftCalculusOfFractions]

lemma Functor.faithful_of_precomp_of_hasLeftCalculusOfFractions
    (h : ∀ ⦃X₁ X₂ : C⦄ (f g : X₁ ⟶ X₂), F.map (L.map f) = F.map (L.map g) → L.map f = L.map g) :
    Faithful F := by
  have := Localization.essSurj L W
  apply F.faithful_of_precomp_essSurj L
  intro X₁ X₂ f g hfg
  obtain ⟨φ, rfl, rfl⟩ := Localization.exists_leftFraction₂ L W f g
  have := Localization.inverts L W φ.s φ.hs
  rw [← cancel_mono (L.map φ.s)]
  erw [φ.fst.map_comp_map_s L, φ.snd.map_comp_map_s L]
  apply h
  simpa only [← F.map_comp, φ.fst.map_comp_map_s, φ.snd.map_comp_map_s] using
    hfg =≫ F.map (L.map φ.s)

lemma Functor.faithful_of_precomp_cancel_zero_of_hasLeftCalculusOfFractions
    [Preadditive C] [Preadditive D] [Preadditive E] [L.Additive] [F.Additive]
    (h : ∀ ⦃X₁ X₂ : C⦄ (f : X₁ ⟶ X₂), F.map (L.map f) = 0 → L.map f = 0) :
    Faithful F :=
  Functor.faithful_of_precomp_of_hasLeftCalculusOfFractions F L W (fun X₁ X₂ f g hfg => by
    rw [← sub_eq_zero, ← L.map_sub]
    exact h _ (by rw [L.map_sub, F.map_sub, hfg, sub_self]))

end

end CategoryTheory
