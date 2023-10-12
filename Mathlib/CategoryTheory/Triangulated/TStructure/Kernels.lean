import Mathlib.CategoryTheory.Triangulated.TStructure.Basic

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]
  {A : Set C} (hA : ∀ {X Y : C} {n : ℤ} (f : X ⟶ Y⟦n⟧), X ∈ A → Y ∈ A → n < 0 → f = 0)

namespace Triangulated

open Pretriangulated

variable (T : Triangle C) (hT : T ∈ distTriang C) (hT₁ : T.obj₁ ∈ A) (hT₂ : T.obj₂ ∈ A)
  {K Q : C} (α : K⟦(1 : ℤ)⟧ ⟶ T.obj₃) {β : T.obj₃ ⟶ Q} {γ : Q ⟶ K⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
  (hT' : Triangle.mk α β γ ∈ distTriang C) (hK : K ∈ A) (hQ : Q ∈ A)

section AbelianSubcategory

lemma vanishing_from_positive_shift {X Y : C} {n : ℤ} (f : X⟦n⟧ ⟶ Y)
    (hX : X ∈ A) (hY : Y ∈ A) (hn : 0 < n) : f = 0 := by
  apply (shiftFunctor C (-n)).map_injective
  rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app X), Functor.map_zero, comp_zero]
  exact hA _ hX hY (by linarith)

noncomputable def ιK : K ⟶ T.obj₁ := (shiftFunctor C (1 : ℤ)).preimage (α ≫ T.mor₃)

@[simp, reassoc]
lemma shift_ιK : (ιK T α)⟦(1 : ℤ)⟧' = α ≫ T.mor₃ := by
  simp [ιK]

variable {T}

lemma ιK_mor₁ : ιK T α ≫ T.mor₁ = 0 := by
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.map_comp, shift_ιK, assoc, Functor.map_zero]
  rw [comp_dist_triangle_mor_zero₃₁ T hT, comp_zero]

variable {α}

lemma ιK_cancel_zero
    {B : C} (k : B ⟶ K) (hB : B ∈ A) (hk : k ≫ ιK T α = 0) : k = 0 := by
  replace hk := (shiftFunctor C (1 : ℤ)).congr_map hk
  apply (shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.map_comp, Functor.map_zero, shift_ιK, ← assoc] at hk ⊢
  obtain ⟨l, hl⟩ := T.coyoneda_exact₃ hT _ hk
  obtain rfl : l = 0 := vanishing_from_positive_shift hA _ hB hT₂ (by linarith)
  rw [zero_comp] at hl
  obtain ⟨m, hm⟩ := Triangle.coyoneda_exact₁ _ hT' (k⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧') (by
    dsimp
    rw [← Functor.map_comp, hl, Functor.map_zero])
  dsimp at m
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by linarith)).hom.app B),
      comp_zero]
    exact vanishing_from_positive_shift hA _ hB hQ (by linarith)
  rw [zero_comp] at hm
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [hm, Functor.map_zero]

lemma ιK_lift
    {B : C} (x₁ : B ⟶ T.obj₁) (hB : B ∈ A) (hx₁ : x₁ ≫ T.mor₁ = 0) :
    ∃ (k : B ⟶ K), k ≫ ιK T α = x₁ := by
  suffices ∃ (k' : B⟦(1 : ℤ)⟧ ⟶ K⟦(1 : ℤ)⟧), x₁⟦(1 : ℤ)⟧' = k' ≫ α ≫ T.mor₃ by
    obtain ⟨k', hk'⟩ := this
    refine' ⟨(shiftFunctor C (1 : ℤ)).preimage k', _⟩
    apply (shiftFunctor C (1 : ℤ)).map_injective
    rw [Functor.map_comp, Functor.image_preimage, shift_ιK, hk']
  obtain ⟨x₃, hx₃⟩ := T.coyoneda_exact₁ hT (x₁⟦(1 : ℤ)⟧')
    (by rw [← Functor.map_comp, hx₁, Functor.map_zero])
  obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ _ hT' x₃
    (vanishing_from_positive_shift hA _ hB hQ (by linarith))
  refine' ⟨k', _⟩
  dsimp at hk'
  rw [hx₃, hk', assoc]

variable (α)

noncomputable abbrev kernelFork :=
  @KernelFork.ofι (FullSubcategory A) _ _ ⟨T.obj₁, hT₁⟩ ⟨T.obj₂, hT₂⟩ T.mor₁ ⟨K, hK⟩
    (ιK T α) (ιK_mor₁ hT α)

variable {α}

noncomputable def isLimitKernelFork : IsLimit (kernelFork hT hT₁ hT₂ α hK) :=
  KernelFork.IsLimit.ofι _ _ (fun {B} x₁ hx₁ => (ιK_lift hA hT hT' hQ x₁ B.2 hx₁).choose)
    (fun {B} x₁ hx₁ => (ιK_lift hA hT hT' hQ x₁ B.2 hx₁).choose_spec)
    (fun {B} x₁ hx₁ m hm => by
      rw [← sub_eq_zero]
      refine' ιK_cancel_zero hA hT hT₂ hT' hQ _ B.2 _
      rw [sub_comp, sub_eq_zero, (ιK_lift hA hT hT' hQ x₁ B.2 hx₁).choose_spec]
      exact hm)

-- BBD 1.2.1, p. 27
lemma hasKernel :
    HasKernel (show FullSubcategory.mk T.obj₁ hT₁ ⟶ FullSubcategory.mk T.obj₂ hT₂ from T.mor₁) :=
  ⟨_, isLimitKernelFork hA hT hT₁ hT₂ hT' hK hQ⟩

end AbelianSubcategory

end Triangulated

end CategoryTheory
