/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.Trunc
import Mathlib.CategoryTheory.Abelian.Constructor
import Mathlib.CategoryTheory.Shift.SingleFunctors

/-!
# Abelian subcategories of triangulated categories

-/

namespace CategoryTheory

open Category Limits Preadditive ZeroObject Pretriangulated ZeroObject

namespace Triangulated

variable {C A : Type*} [Category C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace AbelianSubcategory

variable [Category A] {ι : A ⥤ C}
  (hι : ∀ ⦃X Y : A⦄ ⦃n : ℤ⦄ (f : ι.obj X ⟶ (ι.obj Y)⟦n⟧), n < 0 → f = 0)

omit [HasZeroObject C] [Pretriangulated C] in
include hι in
lemma vanishing_from_positive_shift {X Y : A} {n : ℤ} (f : (ι.obj X)⟦n⟧ ⟶ ι.obj Y)
    (hn : 0 < n) : f = 0 := by
  apply (shiftFunctor C (-n)).map_injective
  rw [← cancel_epi ((shiftEquiv C n).unitIso.hom.app _), Functor.map_zero, comp_zero]
  exact hι _ (by linarith)

section

variable {X₁ X₂ : A} {f₁ : X₁ ⟶ X₂} {X₃ : C} (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
  (hT : Triangle.mk (ι.map f₁) f₂ f₃ ∈ distTriang C) {K Q : A}
  (α : (ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃) (β : X₃ ⟶ (ι.obj Q)) {γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧}
  (hT' : Triangle.mk α β γ ∈ distTriang C)

variable [ι.Full]

noncomputable def ιK : K ⟶ X₁ := (ι ⋙ shiftFunctor C (1 : ℤ)).preimage (α ≫ f₃)

noncomputable def πQ : X₂ ⟶ Q := ι.preimage (f₂ ≫ β)

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
@[simp, reassoc]
lemma shift_ι_map_ιK : (ι.map (ιK f₃ α))⟦(1 : ℤ)⟧' = α ≫ f₃ := by
  apply (ι ⋙ shiftFunctor C (1 : ℤ)).map_preimage

omit [Preadditive C] [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] [HasShift C ℤ] in
@[simp, reassoc]
lemma ι_map_πQ : ι.map (πQ f₂ β) = f₂ ≫ β := by
  apply ι.map_preimage

variable {f₂ f₃} [Preadditive A] [ι.Faithful]

include hT in
lemma ιK_mor₁ : ιK f₃ α ≫ f₁ = 0 := by
  apply (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.comp_map, Functor.map_comp, shift_ι_map_ιK,
    assoc, Functor.map_zero]
  erw [comp_distTriang_mor_zero₃₁ _ hT, comp_zero]

include hT in
lemma mor₁_πQ : f₁ ≫ πQ f₂ β = 0 := by
  apply ι.map_injective
  simp only [Functor.map_comp, Functor.map_zero, ι_map_πQ]
  erw [comp_distTriang_mor_zero₁₂_assoc _ hT, zero_comp]

variable {α β}

include hT hT' hι

lemma mono_ιK : Mono (ιK f₃ α) := by
  rw [mono_iff_cancel_zero]
  intro B k hk
  replace hk := (ι ⋙ shiftFunctor C (1 : ℤ)).congr_map hk
  apply (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    shift_ι_map_ιK, Functor.map_zero, ← assoc] at hk ⊢
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₃ _ hT _ hk
  obtain rfl : l = 0 := vanishing_from_positive_shift hι _ (by linarith)
  rw [zero_comp] at hl
  obtain ⟨m, hm⟩ := Triangle.coyoneda_exact₁ _ hT' ((ι.map k)⟦(1 : ℤ)⟧'⟦(1 : ℤ)⟧') (by
    dsimp
    rw [← Functor.map_comp, hl, Functor.map_zero])
  dsimp at m hm
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by linarith)).hom.app _), comp_zero]
    exact vanishing_from_positive_shift hι _ (by linarith)
  rw [zero_comp] at hm
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [hm, Functor.map_zero]

lemma epi_πQ : Epi (πQ f₂ β) := by
  rw [epi_iff_cancel_zero]
  intro B k hk
  replace hk := ι.congr_map hk
  simp only [Functor.map_comp, ι_map_πQ, assoc, Functor.map_zero] at hk
  obtain ⟨l, hl⟩ := Triangle.yoneda_exact₃ _ hT _ hk
  obtain rfl : l = 0 := vanishing_from_positive_shift hι _ (by linarith)
  rw [comp_zero] at hl
  obtain ⟨m, hm⟩ := Triangle.yoneda_exact₃ _ hT' (ι.map k) hl
  dsimp at m hm
  obtain rfl : m = 0 := by
    rw [← cancel_epi ((shiftFunctorAdd' C (1 : ℤ) 1 2 (by linarith)).hom.app _),
      comp_zero]
    exact vanishing_from_positive_shift hι _ (by linarith)
  apply ι.map_injective
  rw [hm, comp_zero, ι.map_zero]

lemma ιK_lift {B : A} (x₁ : B ⟶ X₁) (hx₁ : x₁ ≫ f₁ = 0) :
    ∃ (k : B ⟶ K), k ≫ ιK f₃ α = x₁ := by
  suffices ∃ (k' : (ι.obj B)⟦(1 : ℤ)⟧ ⟶ (ι.obj K)⟦(1 : ℤ)⟧), (ι.map x₁)⟦(1 : ℤ)⟧' = k' ≫ α ≫ f₃ by
    obtain ⟨k', hk'⟩ := this
    refine ⟨(ι ⋙ shiftFunctor C (1 : ℤ)).preimage k', ?_⟩
    apply (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
    rw [Functor.map_comp, Functor.map_preimage, Functor.comp_map, shift_ι_map_ιK,
      Functor.comp_map, hk']
  obtain ⟨x₃, hx₃⟩ := Triangle.coyoneda_exact₁ _ hT ((ι.map x₁)⟦(1 : ℤ)⟧')
    (by
      dsimp
      rw [← Functor.map_comp, ← Functor.map_comp, hx₁, Functor.map_zero, Functor.map_zero])
  obtain ⟨k', hk'⟩ := Triangle.coyoneda_exact₂ _ hT' x₃
    (vanishing_from_positive_shift hι _ (by linarith))
  refine ⟨k', ?_⟩
  dsimp at hk' hx₃
  rw [hx₃, hk', assoc]

noncomputable def isLimitKernelFork : IsLimit (KernelFork.ofι _ (ιK_mor₁ hT α)) :=
  KernelFork.IsLimit.ofι _ _  (fun {B} x₁ hx₁ => (ιK_lift hι hT hT' x₁ hx₁).choose)
    (fun {B} x₁ hx₁ => (ιK_lift hι hT hT' x₁ hx₁).choose_spec)
    (fun {B} x₁ hx₁ m hm => by
      have := mono_ιK hι hT hT'
      rw [← cancel_mono (ιK f₃ α), (ιK_lift hι hT hT' x₁ hx₁).choose_spec, hm])

lemma πQ_desc {B : A} (x₂ : X₂ ⟶ B) (hx₂ : f₁ ≫ x₂ = 0) :
    ∃ (k : Q ⟶ B), πQ f₂ β ≫ k = x₂ := by
  obtain ⟨x₁, hx₁⟩ := Triangle.yoneda_exact₂ _ hT (ι.map x₂) (by
    dsimp
    rw [← ι.map_comp, hx₂, ι.map_zero])
  obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT' x₁
    (vanishing_from_positive_shift hι _ (by linarith))
  dsimp at k hk hx₁
  refine ⟨ι.preimage k, ?_⟩
  apply ι.map_injective
  simp only [Functor.map_comp, ι_map_πQ, Functor.map_preimage, assoc, hx₁, hk]

noncomputable def isColimitCokernelCofork : IsColimit (CokernelCofork.ofπ _ (mor₁_πQ hT β)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {B} x₂ hx₂ => (πQ_desc hι hT hT' x₂ hx₂).choose)
    (fun {B} x₂ hx₂ => (πQ_desc hι hT hT' x₂ hx₂).choose_spec)
    (fun {B} x₂ hx₂ m hm => by
      have := epi_πQ hι hT hT'
      rw [← cancel_epi (πQ f₂ β), (πQ_desc hι hT hT' x₂ hx₂).choose_spec, hm])

-- BBD 1.2.1, p. 27
lemma hasKernel : HasKernel f₁ := ⟨_, isLimitKernelFork hι hT hT'⟩
lemma hasCokernel : HasCokernel f₁ := ⟨_, isColimitCokernelCofork hι hT hT'⟩

end

variable (ι)

def admissibleMorphism : MorphismProperty A := fun X₁ X₂ f₁ =>
  ∀ ⦃X₃ : C⦄ (f₂ : ι.obj X₂ ⟶ X₃) (f₃ : X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
    (_ : Triangle.mk (ι.map f₁) f₂ f₃ ∈ distTriang C),
  ∃ (K Q : A) (α : (ι.obj K)⟦(1 : ℤ)⟧ ⟶ X₃) (β : X₃ ⟶ (ι.obj Q))
    (γ : ι.obj Q ⟶ (ι.obj K)⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧), Triangle.mk α β γ ∈ distTriang C

variable {ι} [Preadditive A] [ι.Full] [ι.Faithful]

include hι in
lemma hasKernel_of_admissibleMorphism {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
    (hf₁ : admissibleMorphism ι f₁) :
    HasKernel f₁ := by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasKernel hι hT hT'

include hι in
lemma hasCokernel_of_admissibleMorphism {X₁ X₂ : A} (f₁ : X₁ ⟶ X₂)
    (hf₁ : admissibleMorphism ι f₁) :
    HasCokernel f₁ := by
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hf₁ f₂ f₃ hT
  exact hasCokernel hι hT hT'

section

-- should be moved somewhere
instance hasZeroObject [HasTerminal A] : HasZeroObject A :=
  ⟨⊤_ A, by
    rw [IsZero.iff_id_eq_zero]
    apply Subsingleton.elim⟩

variable [HasFiniteProducts A] [ι.Additive]

noncomputable def isLimitKernelForkOfDistTriang {X₁ X₂ X₃ : A}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : ι.obj X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ι.map f₁) (ι.map f₂) f₃ ∈ distTriang C) :
    IsLimit (KernelFork.ofι f₁ (show f₁ ≫ f₂ = 0 from ι.map_injective (by
        erw [Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, ι.map_zero]))) := by
  have hT' : Triangle.mk (𝟙 ((ι.obj X₁)⟦(1 : ℤ)⟧)) (0 : _ ⟶ ι.obj 0) 0 ∈ distTriang C := by
    refine isomorphic_distinguished _ (contractible_distinguished
      (((ι ⋙ shiftFunctor C (1 : ℤ)).obj X₁))) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (IsZero.iso (by
      dsimp
      rw [IsZero.iff_id_eq_zero, ← ι.map_id, id_zero, ι.map_zero]) (isZero_zero C))
      (by aesop_cat) (by aesop_cat) (by aesop_cat)
  refine IsLimit.ofIsoLimit (AbelianSubcategory.isLimitKernelFork hι
    (rot_of_distTriang _ hT) hT') ?_
  exact Fork.ext (-(Iso.refl _)) ((ι ⋙ shiftFunctor C (1 : ℤ)).map_injective
    (by simp))

noncomputable def isColimitCokernelCoforkOfDistTriang {X₁ X₂ X₃ : A}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : ι.obj X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (ι.map f₁) (ι.map f₂) f₃ ∈ distTriang C) :
    IsColimit (CokernelCofork.ofπ f₂ (show f₁ ≫ f₂ = 0 from ι.map_injective (by
        erw [Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, ι.map_zero]))) := by
  have hT' : Triangle.mk (0 : ((ι ⋙ shiftFunctor C (1 : ℤ)).obj 0) ⟶ _) (𝟙 (ι.obj X₃)) 0 ∈
      distTriang C := by
    refine isomorphic_distinguished _ (inv_rot_of_distTriang _
      (contractible_distinguished (ι.obj X₃))) _ ?_
    refine Triangle.isoMk _ _ (IsZero.iso ?_ ?_) (Iso.refl _) (Iso.refl _) (by
      dsimp
      simp only [comp_id, comp_neg, zero_eq_neg, IsIso.comp_left_eq_zero, IsIso.comp_right_eq_zero]
      rw [Functor.map_zero]) (by simp) (by simp)
    · dsimp
      rw [IsZero.iff_id_eq_zero, ← Functor.map_id, ← Functor.map_id, id_zero,
        Functor.map_zero, Functor.map_zero]
    · dsimp
      rw [IsZero.iff_id_eq_zero, ← Functor.map_id, id_zero, Functor.map_zero]
  refine IsColimit.ofIsoColimit (AbelianSubcategory.isColimitCokernelCofork hι
    hT hT') ?_
  exact Cofork.ext (Iso.refl _) (ι.map_injective (by simp))

variable (hA : ∀ ⦃X₁ X₂ : A⦄ (f₁ : X₁ ⟶ X₂), admissibleMorphism ι f₁) [IsTriangulated C]

omit [HasFiniteProducts A] [IsTriangulated C] in
include hι hA in
lemma exists_distinguished_triangle_of_epi {X₂ X₃ : A} (π : X₂ ⟶ X₃) [Epi π] :
    ∃ (X₁ : A) (i : X₁ ⟶ X₂) (δ : ι.obj X₃ ⟶ (ι.obj X₁)⟦(1 : ℤ)⟧),
      Triangle.mk (ι.map i) (ι.map π) δ ∈ distTriang C := by
  obtain ⟨X₁, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map π)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hA π f₂ f₃ hT
  have hQ : 𝟙 Q = 0 := by
    apply Cofork.IsColimit.hom_ext (isColimitCokernelCofork hι hT hT')
    dsimp
    rw [comp_id, comp_zero, ← cancel_epi π, comp_zero, mor₁_πQ hT β]
  have : IsIso α := (Triangle.isZero₃_iff_isIso₁ _ hT').1 (by
    dsimp
    rw [IsZero.iff_id_eq_zero, ← ι.map_id, hQ, ι.map_zero])
  refine ⟨K, -ιK f₃ α, f₂ ≫ inv α, ?_⟩
  rw [rotate_distinguished_triangle]
  refine isomorphic_distinguished _ hT _ ?_
  exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso α)

variable (ι)

noncomputable def abelian : Abelian A := by
  apply Abelian.mk'
  intro X₁ X₂ f₁
  obtain ⟨X₃, f₂, f₃, hT⟩ := distinguished_cocone_triangle (ι.map f₁)
  obtain ⟨K, Q, α, β, γ, hT'⟩ := hA f₁ f₂ f₃ hT
  have comm : f₂ ≫ β = ι.map (πQ f₂ β) := by simp
  have := epi_πQ hι hT hT'
  obtain ⟨I, i, δ, hI⟩ := exists_distinguished_triangle_of_epi hι hA (πQ f₂ β)
  have H := someOctahedron comm (rot_of_distTriang _ hT) (rot_of_distTriang _ hT')
    (rot_of_distTriang _ hI)
  obtain ⟨m₁, hm₁⟩ : ∃ (m₁ : X₁ ⟶ I), (shiftFunctor C (1 : ℤ)).map (ι.map m₁) = H.m₁ :=
    ⟨(ι ⋙ shiftFunctor C (1 : ℤ)).preimage H.m₁, Functor.map_preimage (ι ⋙ _) _⟩
  obtain ⟨m₃ : ι.obj I ⟶ (ι.obj K)⟦(1 : ℤ)⟧, hm₃⟩ :
      ∃ m₃, (shiftFunctor C (1 : ℤ)).map m₃ = H.m₃ :=
    ⟨(shiftFunctor C (1 : ℤ)).preimage H.m₃, Functor.map_preimage _ _⟩
  have Hmem' : Triangle.mk (ι.map (ιK f₃ α)) (ι.map m₁) (-m₃) ∈ distTriang C := by
    rw [rotate_distinguished_triangle, ← Triangle.shift_distinguished_iff _ 1]
    refine isomorphic_distinguished _ H.mem _ ?_
    refine Triangle.isoMk _ _ (-(Iso.refl _)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · dsimp
      simp [hm₁]
    · dsimp
      simp [hm₃]
    · dsimp
      simp
  exact ⟨K, _, _, isLimitKernelFork hι hT hT',
    Q, _, _, isColimitCokernelCofork hι hT hT',
    I, _, _, isColimitCokernelCoforkOfDistTriang hι _ _ _ Hmem',
    i, _, isLimitKernelForkOfDistTriang hι _ _ _ hI,
    (ι ⋙ shiftFunctor C (1 : ℤ)).map_injective (by simpa [hm₁] using H.comm₂.symm)⟩

end

end AbelianSubcategory

end Triangulated

end CategoryTheory
