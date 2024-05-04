import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

open CategoryTheory Category ComposableArrows Limits Abelian

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)} (φ : S₁ ⟶ S₂)
  (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)

namespace HomologicalComplex

section

variable {K L : HomologicalComplex C c} (φ : K ⟶ L)

attribute [local instance] epi_comp

instance [Epi φ] (i : ι) : Epi (opcyclesMap φ i) :=
  epi_of_epi_fac (p_opcyclesMap φ i)

lemma epi_homologyMap_of_epi_of_not_rel [Epi φ] (i : ι) (hi : ∀ j, ¬ c.Rel i j) :
    Epi (homologyMap φ i) := by
  let e : ∀ (M : HomologicalComplex C c), M.homology i ≅ M.opcycles i := fun M =>
    (M.isoHomologyι i _ rfl (shape _ _ _ (by tauto)))
  exact ((MorphismProperty.RespectsIso.epimorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (e _) (e _))).2 (inferInstance : Epi (opcyclesMap φ i))

lemma mono_homologyMap_of_mono_of_not_rel [Mono φ] (j : ι) (hj : ∀ i, ¬ c.Rel i j) :
    Mono (homologyMap φ j) := by
  let e : ∀ (M : HomologicalComplex C c), M.cycles j ≅ M.homology j := fun M =>
    (M.isoHomologyπ _ j rfl (shape _ _ _ (by tauto)))
  exact ((MorphismProperty.RespectsIso.monomorphisms C).arrow_mk_iso_iff
    (Arrow.isoMk (e _) (e _))).1 (inferInstance : Mono (cyclesMap φ j))

end

namespace HomologySequence

@[simps]
noncomputable def mapSnakeInput (i j : ι) (hij : c.Rel i j) :
    snakeInput hS₁ i j hij ⟶ snakeInput hS₂ i j hij where
  f₀ := (homologyFunctor C c i).mapShortComplex.map φ
  f₁ := (opcyclesFunctor C c i).mapShortComplex.map φ
  f₂ := (cyclesFunctor C c j).mapShortComplex.map φ
  f₃ := (homologyFunctor C c j).mapShortComplex.map φ

lemma δ_naturality (i j : ι) (hij : c.Rel i j) :
    hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ _ =
      HomologicalComplex.homologyMap φ.τ₃ _ ≫ hS₂.δ i j hij :=
  ShortComplex.SnakeInput.naturality_δ (mapSnakeInput φ hS₁ hS₂ i j hij)

variable (S₁) in
@[simp]
noncomputable def composableArrows₂ (i : ι) : ComposableArrows C 2 :=
  mk₂ (homologyMap S₁.f i) (homologyMap S₁.g i)

lemma composableArrows₂_exact (i : ι) :
    (composableArrows₂ S₁ i).Exact :=
  (hS₁.homology_exact₂ i).exact_toComposableArrows

@[simp]
noncomputable def composableArrows₅ (i j : ι) (hij : c.Rel i j) : ComposableArrows C 5 :=
  mk₅ (homologyMap S₁.f i) (homologyMap S₁.g i) (hS₁.δ i j hij)
    (homologyMap S₁.f j) (homologyMap S₁.g j)

lemma composableArrows₅_exact (i j : ι) (hij : c.Rel i j):
    (composableArrows₅ hS₁ i j hij).Exact :=
  exact_of_δ₀ (hS₁.homology_exact₂ i).exact_toComposableArrows
    (exact_of_δ₀ (hS₁.homology_exact₃ i j hij).exact_toComposableArrows
      (exact_of_δ₀ (hS₁.homology_exact₁ i j hij).exact_toComposableArrows
        (hS₁.homology_exact₂ j).exact_toComposableArrows))

@[simp]
noncomputable def mapComposableArrows₂ (i : ι) : composableArrows₂ S₁ i ⟶ composableArrows₂ S₂ i :=
  homMk₂ (homologyMap φ.τ₁ i) (homologyMap φ.τ₂ i) (homologyMap φ.τ₃ i) (by
    dsimp
    simp only [← homologyMap_comp, φ.comm₁₂]) (by
    dsimp
    simp only [← homologyMap_comp, φ.comm₂₃])

@[simp]
noncomputable def mapComposableArrows₅ (i j : ι) (hij : c.Rel i j) :
    composableArrows₅ hS₁ i j hij ⟶ composableArrows₅ hS₂ i j hij:=
  homMk₅ (homologyMap φ.τ₁ i) (homologyMap φ.τ₂ i) (homologyMap φ.τ₃ i)
    (homologyMap φ.τ₁ j) (homologyMap φ.τ₂ j) (homologyMap φ.τ₃ j)
    (naturality' (mapComposableArrows₂ φ i) 0 1)
    (naturality' (mapComposableArrows₂ φ i) 1 2)
    (δ_naturality φ hS₁ hS₂ i j hij)
    (naturality' (mapComposableArrows₂ φ j) 0 1)
    (naturality' (mapComposableArrows₂ φ j) 1 2)

attribute [local instance] epi_comp

lemma mono_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Mono (homologyMap φ.τ₂ i))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Mono (homologyMap φ.τ₃ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply mono_of_epi_of_mono_of_mono ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ _ hij
  · refine mono_of_epi_of_epi_of_mono (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₁ i) (composableArrows₂_exact hS₂ i) ?_ h₁ h₂
    have := hS₁.epi_g
    apply epi_homologyMap_of_epi_of_not_rel
    simpa using hi

lemma epi_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₂ i))
    (h₂ : ∀ j, c.Rel i j → Epi (homologyMap φ.τ₁ j))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₂ j)) :
    Epi (homologyMap φ.τ₃ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply epi_of_epi_of_epi_of_mono ((δ₀Functor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δlast
    · exact h₁
    · exact h₂ j hij
    · exact h₃ j hij
  · have := hS₂.epi_g
    have eq := (homologyFunctor C _ i).congr_map φ.comm₂₃
    dsimp at eq
    simp only [homologyMap_comp] at eq
    have := epi_homologyMap_of_epi_of_not_rel S₂.g i (by simpa using hi)
    exact epi_of_epi_fac eq.symm

lemma isIso_homologyMap_τ₃ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : IsIso (homologyMap φ.τ₂ i))
    (h₃ : ∀ j, c.Rel i j → IsIso (homologyMap φ.τ₁ j))
    (h₄ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₂ j)) :
    IsIso (homologyMap φ.τ₃ i) := by
  have := mono_homologyMap_τ₃ φ hS₁ hS₂ i h₁ inferInstance (fun j hij => by
    have := h₃ j hij
    infer_instance)
  have := epi_homologyMap_τ₃ φ hS₁ hS₂ i inferInstance (fun j hij => by
    have := h₃ j hij
    infer_instance) h₄
  apply isIso_of_mono_of_epi

lemma quasiIso_τ₃ (h₁ : QuasiIso φ.τ₁) (h₂ : QuasiIso φ.τ₂) :
    QuasiIso φ.τ₃ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₃ φ hS₁ hS₂
  all_goals infer_instance

lemma epi_homologyMap_τ₁ (j : ι)
    (h₁ : Epi (homologyMap φ.τ₂ j))
    (h₂ : Mono (homologyMap φ.τ₃ j))
    (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i)) :
    Epi (homologyMap φ.τ₁ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply epi_of_epi_of_epi_of_mono ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₃ i hij
    · exact h₁
    · exact h₂
  · refine epi_of_mono_of_epi_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j) (composableArrows₂_exact hS₂ j) ?_ h₁ h₂
    have := hS₂.mono_f
    apply HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    simpa using hj

lemma mono_homologyMap_τ₁ (j : ι)
    (h₁ : Mono (homologyMap φ.τ₂ j))
    (h₂ : ∀ i, c.Rel i j → Mono (homologyMap φ.τ₃ i))
    (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₂ i)) :
    Mono (homologyMap φ.τ₁ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply mono_of_epi_of_mono_of_mono ((δ₀Functor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δlast
    · exact h₃ i hij
    · exact h₂ i hij
    · exact h₁
  · have := hS₁.mono_f
    have eq := (homologyFunctor C _ j).congr_map φ.comm₁₂
    dsimp at eq
    simp only [homologyMap_comp] at eq
    have : Mono (homologyMap S₁.f j) :=
      HomologicalComplex.mono_homologyMap_of_mono_of_not_rel _ _ (by simpa using hj)
    exact mono_of_mono_fac eq

lemma isIso_homologyMap_τ₁ (j : ι)
    (h₁ : IsIso (homologyMap φ.τ₂ j))
    (h₂ : Mono (homologyMap φ.τ₃ j))
    (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₂ i))
    (h₄ : ∀ i, c.Rel i j → IsIso (homologyMap φ.τ₃ i)) :
    IsIso (homologyMap φ.τ₁ j) := by
  have := mono_homologyMap_τ₁ φ hS₁ hS₂ j inferInstance
    (fun i hij => by
      have := h₄ i hij
      infer_instance)
    (fun i hij => by
      have := h₃ i hij
      infer_instance)
  have := epi_homologyMap_τ₁ φ hS₁ hS₂ j inferInstance h₂
    (fun i hij => by
      have := h₄ i hij
      infer_instance)
  apply isIso_of_mono_of_epi

lemma quasiIso_τ₁ (h₂ : QuasiIso φ.τ₂) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₁ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₁ φ hS₁ hS₂
  all_goals infer_instance

lemma mono_homologyMap_τ₂ (j : ι)
    (h₁ : Mono (homologyMap φ.τ₁ j))
    (h₂ : Mono (homologyMap φ.τ₃ j))
    (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i)) :
    Mono (homologyMap φ.τ₂ j) := by
  by_cases hj : ∃ i, c.Rel i j
  · obtain ⟨i, hij⟩ := hj
    apply mono_of_epi_of_mono_of_mono ((δ₀Functor ⋙ δ₀Functor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δ₀.δ₀
    · exact (composableArrows₅_exact hS₂ i j hij).δ₀.δ₀
    · exact h₃ i hij
    · exact h₁
    · exact h₂
  · have := hS₂.mono_f
    exact mono_of_mono_of_mono_of_mono (mapComposableArrows₂ φ j)
      (composableArrows₂_exact hS₁ j)
      (mono_homologyMap_of_mono_of_not_rel S₂.f j (by simpa using hj)) h₁ h₂

lemma epi_homologyMap_τ₂ (i : ι)
    (h₁ : Epi (homologyMap φ.τ₁ i))
    (h₂ : Epi (homologyMap φ.τ₃ i))
    (h₃ : ∀ j, c.Rel i j → Mono (homologyMap φ.τ₁ j)) :
    Epi (homologyMap φ.τ₂ i) := by
  by_cases hi : ∃ j, c.Rel i j
  · obtain ⟨j, hij⟩ := hi
    apply epi_of_epi_of_epi_of_mono ((δlastFunctor ⋙ δlastFunctor).map (mapComposableArrows₅ φ hS₁ hS₂ i j hij))
    · exact (composableArrows₅_exact hS₁ i j hij).δlast.δlast
    · exact (composableArrows₅_exact hS₂ i j hij).δlast.δlast
    · exact h₁
    · exact h₂
    · exact h₃ j hij
  · have := hS₁.epi_g
    refine' epi_of_epi_of_epi_of_epi (mapComposableArrows₂ φ i)
      (composableArrows₂_exact hS₂ i)
      (epi_homologyMap_of_epi_of_not_rel S₁.g i (by simpa using hi)) h₁ h₂

lemma isIso_homologyMap_τ₂ (j : ι)
    (h₁ : IsIso (homologyMap φ.τ₁ j))
    (h₂ : IsIso (homologyMap φ.τ₃ j))
    (h₃ : ∀ i, c.Rel i j → Epi (homologyMap φ.τ₃ i))
    (h₄ : ∀ k, c.Rel j k → Mono (homologyMap φ.τ₁ k)) :
    IsIso (homologyMap φ.τ₂ j) := by
  have := mono_homologyMap_τ₂ φ hS₁ hS₂ j inferInstance inferInstance h₃
  have := epi_homologyMap_τ₂ φ hS₁ hS₂ j inferInstance inferInstance h₄
  apply isIso_of_mono_of_epi

lemma quasiIso_τ₂ (h₁ : QuasiIso φ.τ₁) (h₃ : QuasiIso φ.τ₃) :
    QuasiIso φ.τ₂ := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply isIso_homologyMap_τ₂ φ hS₁ hS₂
  all_goals infer_instance

end HomologySequence

end HomologicalComplex
