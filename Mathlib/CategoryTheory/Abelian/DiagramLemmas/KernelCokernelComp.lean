/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Long exact sequence for the kernel and cokernel of a composition

If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms in an
abelian category, we construct a long exact sequence :
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`.

-/

universe v u

namespace CategoryTheory

open Limits Category

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace kernelCokernelCompSequence

@[simps (config := .lemmasOnly) L₁ L₂ v₁₂]
noncomputable def snakeInput : ShortComplex.SnakeInput C where
  L₁_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).exact
  L₂_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct Y Z).exact
  v₁₂ :=
    { τ₁ := f
      τ₂ := biprod.desc (f ≫ biprod.inl) (biprod.lift (-𝟙 Y) g)
      τ₃ := g }
  h₀ := kernelIsKernel _
  h₃ := cokernelIsCokernel _
  epi_L₁_g := by dsimp; infer_instance
  mono_L₂_f := by dsimp; infer_instance

@[simp]
lemma snakeInput_v₀₁ : (snakeInput f g).v₀₁ = kernel.ι ((snakeInput f g).v₁₂) := rfl

@[simp]
lemma snakeInput_v₂₃ : (snakeInput f g).v₂₃ = cokernel.π ((snakeInput f g).v₁₂) := rfl

attribute [simp] snakeInput_L₁ snakeInput_L₂

attribute [local simp] snakeInput_v₁₂ in
@[simps!]
noncomputable def kernelFork : KernelFork (snakeInput f g).v₁₂.τ₂ :=
  KernelFork.ofι (biprod.lift (kernel.ι (f ≫ g)) (kernel.ι _ ≫ f))
    (by aesop_cat)

def isLimitKernelFork : IsLimit (kernelFork f g) := sorry

@[simps!]
noncomputable def cokernelCofork : CokernelCofork (snakeInput f g).v₁₂.τ₂ :=
  CokernelCofork.ofπ (biprod.desc (g ≫ cokernel.π (f ≫ g)) (cokernel.π (f ≫ g)))
    (by
      dsimp [snakeInput_v₁₂]
      ext
      · simp only [biprod.inl_desc_assoc, assoc, biprod.inl_desc, comp_zero]
        rw [← assoc, cokernel.condition]
      · simp)

def isColimitCokernelCofork : IsColimit (cokernelCofork f g) := sorry

noncomputable def iso₀ : kernel f ≅ (snakeInput f g).L₀.X₁ :=
  (asIso (kernelComparison (snakeInput f g).v₁₂ ShortComplex.π₁)).symm

noncomputable def iso₁' : kernel (f ≫ g) ≅ kernel (snakeInput f g).v₁₂.τ₂ := by
  let e := IsLimit.conePointUniqueUpToIso (isLimitKernelFork f g)
    (kernelIsKernel ((snakeInput f g).v₁₂.τ₂))
  exact e

noncomputable def iso₁ : kernel (f ≫ g) ≅ (snakeInput f g).L₀.X₂ :=
  iso₁' f g ≪≫ (asIso (kernelComparison (snakeInput f g).v₁₂ ShortComplex.π₂)).symm

noncomputable def iso₂ : kernel g ≅ (snakeInput f g).L₀.X₃ :=
  (asIso (kernelComparison (snakeInput f g).v₁₂ ShortComplex.π₃)).symm

noncomputable def iso₃ : cokernel f ≅ (snakeInput f g).L₃.X₁ :=
  asIso (cokernelComparison (snakeInput f g).v₁₂ ShortComplex.π₁)

def iso₄ : cokernel (f ≫ g) ≅ (snakeInput f g).L₃.X₂ := sorry

noncomputable def iso₅ : cokernel g ≅ (snakeInput f g).L₃.X₃ :=
  asIso (cokernelComparison (snakeInput f g).v₁₂ ShortComplex.π₃)

noncomputable def δ : kernel g ⟶ cokernel f :=
  (iso₂ f g).hom ≫ (snakeInput f g).δ ≫ (iso₃ f g).inv

@[reassoc (attr := simp)]
lemma comm₀₁' :
    kernel.map f (f ≫ g) (𝟙 X) g (by simp) ≫ (iso₁' f g).hom =
      kernel.map _ _ biprod.inl biprod.inl (by simp [snakeInput_v₁₂]) := by
  have := IsLimit.conePointUniqueUpToIso_hom_comp (isLimitKernelFork f g)
    (kernelIsKernel ((snakeInput f g).v₁₂.τ₂)) .zero
  dsimp [kernelFork] at this ⊢
  rw [← cancel_mono (kernel.ι _), assoc, kernel.lift_ι, iso₁', this]
  aesop

@[reassoc (attr := simp)]
lemma comm₀₁ :
    kernel.map f (f ≫ g) (𝟙 X) g (by simp) ≫ (iso₁ f g).hom =
      (iso₀ f g).hom ≫ (snakeInput f g).L₀.f := by
  have h₁ := kernelComparison_comp_ι (snakeInput f g).v₁₂ ShortComplex.π₂
  have h₂ := (snakeInput f g).v₀₁.comm₁₂
  dsimp at h₁ h₂
  dsimp only [iso₁, Iso.trans, Iso.symm, asIso_inv]
  rw [← cancel_mono (kernelComparison (snakeInput f g).v₁₂ ShortComplex.π₂)]
  dsimp
  rw [comm₀₁'_assoc, assoc, assoc, IsIso.inv_hom_id, comp_id,
    ← cancel_mono (kernel.ι _), kernel.lift_ι, assoc, assoc, h₁, ← h₂]
  rw [← assoc]
  congr 1
  dsimp [iso₀]
  rw [IsIso.eq_inv_comp]
  apply kernelComparison_comp_ι

@[reassoc (attr := simp)]
lemma comm₁₂ :
    kernel.map (f ≫ g) g f (𝟙 _) (by simp) ≫ (iso₂ f g).hom =
      (iso₁ f g).hom ≫ (snakeInput f g).L₀.g := sorry

@[reassoc (attr := simp)]
lemma comm₂₃ :
    δ f g ≫ (iso₃ f g).hom =
      (iso₂ f g).hom ≫ (snakeInput f g).δ := by
  simp [δ]

@[reassoc (attr := simp)]
lemma comm₃₄ :
    cokernel.map f (f ≫ g) (𝟙 X) g (by simp) ≫ (iso₄ f g).hom =
      (iso₃ f g).hom ≫ (snakeInput f g).L₃.f := sorry

@[reassoc (attr := simp)]
lemma comm₄₅ :
    cokernel.map (f ≫ g) g f (𝟙 _) (by simp) ≫ (iso₅ f g).hom =
      (iso₄ f g).hom ≫ (snakeInput f g).L₃.g := sorry

end kernelCokernelCompSequence

open kernelCokernelCompSequence

noncomputable abbrev kernelCokernelCompSequence : ComposableArrows C 5 :=
  .mk₅ (kernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (kernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (δ f g)
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))

attribute [local simp] ComposableArrows.Precomp.map

noncomputable def kernelCokernelCompSequence.iso :
    kernelCokernelCompSequence f g ≅ (snakeInput f g).composableArrows :=
  ComposableArrows.isoMk₅ (iso₀ _ _) (iso₁ _ _) (iso₂ _ _) (iso₃ _ _) (iso₄ _ _) (iso₅ _ _)
    (by simp) (by simp) (by simp) (by simp) (by simp)

lemma kernelCokernelCompSequence_exact :
    (kernelCokernelCompSequence f g).Exact :=
  ComposableArrows.exact_of_iso (iso f g).symm (snakeInput f g).snake_lemma

end CategoryTheory
