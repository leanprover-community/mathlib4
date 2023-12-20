import Mathlib.Algebra.Homology.SpectralObject.Misc

namespace CategoryTheory

open Category Limits

namespace Abelian

section

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

open ComposableArrows

structure SpectralObject where
  H (n : ℤ) : ComposableArrows ι 1 ⥤ C
  δ' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
  exact₁' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
  exact₂' (n : ℤ) (D : ComposableArrows ι 2) :
    (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
  exact₃' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact

namespace SpectralObject

variable {C ι}
variable (X : SpectralObject C ι)

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)

def δ : (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f) :=
  (X.δ' n₀ n₁ hn₁).app (mk₂ f g)

lemma δ_naturality {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g') (hαβ : α.app 1 = β.app 0):
    (X.H n₀).map β ≫ X.δ n₀ n₁ hn₁ f' g' = X.δ n₀ n₁ hn₁ f g ≫ (X.H n₁).map α := by
  let φ : mk₂ f g ⟶ mk₂ f' g' := homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
    (by simpa only [hαβ] using naturality' β 0 1)
  have h := (X.δ' n₀ n₁ hn₁).naturality φ
  dsimp at h
  convert h
  · ext
    · exact hαβ.symm
    · rfl
  · ext <;> rfl

section

variable (fg : i ⟶ k) (h : f ≫ g = fg)

@[simp]
noncomputable def iso₁ :
    mk₂ (X.δ n₀ n₁ hn₁ f g) ((X.H n₁).map (homMk₁ (𝟙 _) g (by simpa using h) : mk₁ f ⟶ mk₁ fg)) ≅
      mk₂ ((X.δ' n₀ n₁ hn₁).app (mk₂ f g)) (((X.H n₁).map
        ((mapFunctorArrows ι 0 1 0 2 2).app (mk₂ f g)))) :=
  isoMk₂ (Iso.refl _) (Iso.refl _) ((X.H n₁).mapIso
    (isoMk₁ (Iso.refl _) (Iso.refl _) (by simpa using h.symm)))
    (by aesop_cat) (by
      dsimp
      simp only [← Functor.map_comp, id_comp]
      congr 1
      ext <;> simp)

@[reassoc]
lemma zero₁ :
    X.δ n₀ n₁ hn₁ f g ≫
      (X.H n₁).map (homMk₁ (𝟙 _) g (by simpa using h) : mk₁ f ⟶ mk₁ fg) = 0 :=
  (exact_of_iso (X.iso₁ n₀ n₁ hn₁ f g fg h).symm (X.exact₁' n₀ n₁ hn₁ (mk₂ f g))).zero 0

@[simps]
def sc₁ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₁ n₀ n₁ hn₁ f g fg h)

lemma exact₁ : (X.sc₁ n₀ n₁ hn₁ f g fg h).Exact :=
  (exact_of_iso (X.iso₁ n₀ n₁ hn₁ f g fg h).symm (X.exact₁' n₀ n₁ hn₁ (mk₂ f g))).exact 0

@[simp]
noncomputable def iso₂ :
    mk₂ ((X.H n₀).map (homMk₁ (𝟙 _) g (by simpa using h) : mk₁ f ⟶ mk₁ fg))
      ((X.H n₀).map (homMk₁ f (𝟙 _) (by simpa using h.symm) : mk₁ fg ⟶ mk₁ g)) ≅
        (mk₂ ((X.H n₀).map ((mapFunctorArrows ι 0 1 0 2 2).app (mk₂ f g)))
      ((X.H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app (mk₂ f g)))) :=
  isoMk₂ (Iso.refl _) ((X.H n₀).mapIso
    (isoMk₁ (Iso.refl _) (Iso.refl _) (by simpa using h.symm))) (Iso.refl _) (by
      dsimp
      simp only [← Functor.map_comp, id_comp]
      congr 1
      ext <;> simp) (by
      dsimp
      simp only [← Functor.map_comp, comp_id]
      congr 1
      ext <;> simp)

@[reassoc]
lemma zero₂ :
    (X.H n₀).map (homMk₁ (𝟙 _) g (by simpa using h) : mk₁ f ⟶ mk₁ fg) ≫
    (X.H n₀).map (homMk₁ f (𝟙 _) (by simpa using h.symm) : mk₁ fg ⟶ mk₁ g) = 0 :=
  (exact_of_iso (X.iso₂ n₀ f g fg h).symm (X.exact₂' n₀ (mk₂ f g))).zero 0

@[simps]
def sc₂ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₂ n₀ f g fg h)

lemma exact₂ : (X.sc₂ n₀ f g fg h).Exact :=
  (exact_of_iso (X.iso₂ n₀ f g fg h).symm (X.exact₂' n₀ (mk₂ f g))).exact 0

@[simp]
noncomputable def iso₃ :
    mk₂ ((X.H n₀).map (homMk₁ f (𝟙 _) (by simpa using h.symm) : mk₁ fg ⟶ mk₁ g))
        (X.δ n₀ n₁ hn₁ f g) ≅
      mk₂ ((X.H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app (mk₂ f g)))
        ((X.δ' n₀ n₁ hn₁).app (mk₂ f g)) :=
  isoMk₂ ((X.H n₀).mapIso (isoMk₁ (Iso.refl _) (Iso.refl _) (by simpa using h.symm)))
    (Iso.refl _) (Iso.refl _) (by
      dsimp
      simp only [← Functor.map_comp, comp_id]
      congr 1
      ext <;> simp) (by aesop_cat)

@[reassoc]
lemma zero₃ :
    (X.H n₀).map (homMk₁ f (𝟙 _) (by simpa using h.symm) : mk₁ fg ⟶ mk₁ g) ≫
      X.δ n₀ n₁ hn₁ f g = 0 :=
  (exact_of_iso (X.iso₃ n₀ n₁ hn₁ f g fg h).symm (X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).zero 0

@[simps]
def sc₃ : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₃ n₀ n₁ hn₁ f g fg h)

lemma exact₃ : (X.sc₃ n₀ n₁ hn₁ f g fg h).Exact :=
  (exact_of_iso (X.iso₃ n₀ n₁ hn₁ f g fg h).symm (X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).exact 0

end

end

section

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)
    {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)

@[reassoc (attr := simp)]
lemma δ_δ : X.δ n₀ n₁ hn₁ g h ≫ X.δ n₁ n₂ hn₂ f g = 0 := by
  have eq := X.δ_naturality n₁ n₂ hn₂ f g f (g ≫ h) (𝟙 _) (homMk₁ (𝟙 _) h (by simp)) rfl
  rw [Functor.map_id, comp_id] at eq
  rw [← eq, X.zero₁_assoc n₀ n₁ hn₁ g h _ rfl, zero_comp]

end

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

@[simps]
def δFunctorArrows (i j k n : ℕ)
    (hij : i ≤ j := by linarith) (hjk : j ≤ k := by linarith) (hk : k ≤ n := by linarith) :
    functorArrows ι j k n ⋙ X.H n₀ ⟶ functorArrows ι i j n ⋙ X.H n₁ where
  app S := X.δ n₀ n₁ hn₁ _ _
  naturality {S S'} φ := by
    apply X.δ_naturality
    rfl

@[simp]
noncomputable def composableArrows₅ :
    ComposableArrows (ComposableArrows ι 2 ⥤ C) 5 :=
  mk₅ (whiskerRight (mapFunctorArrows ι 0 1 0 2 2) (X.H n₀))
    (whiskerRight (mapFunctorArrows ι 0 2 1 2 2) (X.H n₀))
    (X.δFunctorArrows n₀ n₁ hn₁ 0 1 2 2)
    (whiskerRight (mapFunctorArrows ι 0 1 0 2 2) (X.H n₁))
    (whiskerRight (mapFunctorArrows ι 0 2 1 2 2) (X.H n₁))

lemma composableArrows₅_apply_exact (D : ComposableArrows ι 2) :
    ((X.composableArrows₅ n₀ n₁ hn₁).apply ((evaluation _ _).obj D)).Exact := by
  obtain ⟨i, j, k, f, g, rfl⟩ := mk₂_surjective D
  exact exact_of_δ₀ (X.exact₂ n₀ f g _ rfl).exact_toComposableArrows
     (exact_of_δ₀ (X.exact₃ n₀ n₁ hn₁ f g _ rfl).exact_toComposableArrows
        (exact_of_δ₀ (X.exact₁ n₀ n₁ hn₁ f g _ rfl).exact_toComposableArrows
          (by
            refine' exact_of_iso _ (X.exact₂ n₁ f g _ rfl).exact_toComposableArrows
            refine' ComposableArrows.isoMk₂ (Iso.refl _) (Iso.refl _) (Iso.refl _) _ _
            all_goals
              dsimp
              rw [id_comp, comp_id]
              rfl)))


end

end SpectralObject

end

end Abelian

end CategoryTheory
