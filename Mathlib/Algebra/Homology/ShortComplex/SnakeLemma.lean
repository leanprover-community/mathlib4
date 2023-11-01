/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# The snake lemma

The snake lemma is a standard tool in homological algebra. The basic situation
is when we have a diagram as follows in an abelian category `C`, with exact rows:

    L₁.X₁ ⟶ L₁.X₂ ⟶ L₁.X₃ ⟶ 0
      |       |       |
      |v₁₂.τ₁ |v₁₂.τ₂ |v₁₂.τ₃
      v       v       v
0 ⟶ L₂.X₁ ⟶ L₂.X₂ ⟶ L₂.X₃

We shall think of this diagram as the datum of a morphism `v₁₂ : L₁ ⟶ L₂` in the
category `ShortComplex C` such that both `L₁` and `L₂` are exact, and `L₁.g` is epi
and `L₂.f` is a mono (which is equivalent to saying that `L₁.X₃` is the cokernel
of `L₁.f` and `L₂.X₁` is the kernel of `L₂.g`). Then, we may introduce the kernels
and cokernels of the vertical maps. In other words, we may introduce short complexes
`L₀` and `L₃` that are respectively the kernel and the cokernel of `v₁₂`. All these
data constitute a `SnakeInput C`.

Given such a `S : SnakeInput C`, we shall define a connecting homomorphism
`S.δ : L₀.X₃ ⟶ L₃.X₁` and show that it is part of an exact sequence
`L₀.X₁ ⟶ L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂ ⟶ L₃.X₃` (TODO). This sequence can even
be extended with an extra `0` on the left if `L₁.X₁ ⟶ L₁.X₂` is a mono
(i.e. `L₁` is short exact), and similarly an extra `0` can be added
on the right if respectively `L₂.X₂ ⟶ L₂.X₃` is an epi.)

These results were also obtained in the Liquid Tensor Experiment. The code and the proof
here shall be slightly easier because of the use of the category `ShortComplex C`,
the use of duality (which allows to construct only half of the sequence, and deducing
the other half by arguing in the opposite category), and the use of "refinements"
(see `CategoryTheory.Abelian.Refinements`) instead of a weak form of pseudo-elements.

-/

namespace CategoryTheory

open Category Limits Preadditive

variable (C : Type*) [Category C] [Abelian C]

namespace ShortComplex

/-- A snake input in an abelian category `C` consists of morphisms
of short complexes `L₀ ⟶ L₁ ⟶ L₂ ⟶ L₃` (which should be visualized vertically) such
that `L₀` and `L₃` are respectively the kernel and the cokernel of `L₁ ⟶ L₂`,
`L₁` and `L₂` are exact, `L₁.g` is epi and `L₂.f` is mono. -/
structure SnakeInput where
  /-- the zeroth row -/
  L₀ : ShortComplex C
  /-- the first row -/
  L₁ : ShortComplex C
  /-- the second row -/
  L₂ : ShortComplex C
  /-- the third row -/
  L₃ : ShortComplex C
  /-- the morphism from the zeroth row to the first row -/
  v₀₁ : L₀ ⟶ L₁
  /-- the morphism from the first row to the second row -/
  v₁₂ : L₁ ⟶ L₂
  /-- the morphism from the second row to the third row -/
  v₂₃ : L₂ ⟶ L₃
  w₀₂ : v₀₁ ≫ v₁₂ = 0 := by aesop_cat
  w₁₃ : v₁₂ ≫ v₂₃ = 0 := by aesop_cat
  /-- `L₀` is the kernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₀ : IsLimit (KernelFork.ofι _ w₀₂)
  /-- `L₃` is the cokernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₃ : IsColimit (CokernelCofork.ofπ _ w₁₃)
  L₁_exact  : L₁.Exact
  epi_L₁_g : Epi L₁.g
  L₂_exact : L₂.Exact
  mono_L₂_f : Mono L₂.f

initialize_simps_projections SnakeInput (-h₀, -h₃)

namespace SnakeInput

attribute [reassoc (attr := simp)] w₀₂ w₁₃
attribute [instance] epi_L₁_g
attribute [instance] mono_L₂_f

variable {C}
variable (S : SnakeInput C)

/-- The snake input in the opposite category that is deduced from a snake input. -/
@[simps]
noncomputable def op : SnakeInput Cᵒᵖ where
  L₀ := S.L₃.op
  L₁ := S.L₂.op
  L₂ := S.L₁.op
  L₃ := S.L₀.op
  epi_L₁_g := by dsimp; infer_instance
  mono_L₂_f := by dsimp; infer_instance
  v₀₁ := opMap S.v₂₃
  v₁₂ := opMap S.v₁₂
  v₂₃ := opMap S.v₀₁
  w₀₂ := congr_arg opMap S.w₁₃
  w₁₃ := congr_arg opMap S.w₀₂
  h₀ := isLimitForkMapOfIsLimit' (ShortComplex.opEquiv C).functor _
      (CokernelCofork.IsColimit.ofπOp _ _ S.h₃)
  h₃ := isColimitCoforkMapOfIsColimit' (ShortComplex.opEquiv C).functor _
      (KernelFork.IsLimit.ofιOp _ _ S.h₀)
  L₁_exact := S.L₂_exact.op
  L₂_exact := S.L₁_exact.op

@[reassoc (attr := simp)] lemma w₀₂_τ₁ : S.v₀₁.τ₁ ≫ S.v₁₂.τ₁ = 0 := by
  rw [← comp_τ₁, S.w₀₂, zero_τ₁]
@[reassoc (attr := simp)] lemma w₀₂_τ₂ : S.v₀₁.τ₂ ≫ S.v₁₂.τ₂ = 0 := by
  rw [← comp_τ₂, S.w₀₂, zero_τ₂]
@[reassoc (attr := simp)] lemma w₀₂_τ₃ : S.v₀₁.τ₃ ≫ S.v₁₂.τ₃ = 0 := by
  rw [← comp_τ₃, S.w₀₂, zero_τ₃]
@[reassoc (attr := simp)] lemma w₁₃_τ₁ : S.v₁₂.τ₁ ≫ S.v₂₃.τ₁ = 0 := by
  rw [← comp_τ₁, S.w₁₃, zero_τ₁]
@[reassoc (attr := simp)] lemma w₁₃_τ₂ : S.v₁₂.τ₂ ≫ S.v₂₃.τ₂ = 0 := by
  rw [← comp_τ₂, S.w₁₃, zero_τ₂]
@[reassoc (attr := simp)] lemma w₁₃_τ₃ : S.v₁₂.τ₃ ≫ S.v₂₃.τ₃ = 0 := by
  rw [← comp_τ₃, S.w₁₃, zero_τ₃]

/-- `L₀.X₁` is the kernel of `v₁₂.τ₁ : L₁.X₁ ⟶ L₂.X₁`. -/
noncomputable def h₀τ₁ : IsLimit (KernelFork.ofι S.v₀₁.τ₁ S.w₀₂_τ₁) :=
  isLimitForkMapOfIsLimit' π₁ S.w₀₂ S.h₀

/-- `L₀.X₂` is the kernel of `v₁₂.τ₂ : L₁.X₂ ⟶ L₂.X₂`. -/
noncomputable def h₀τ₂ : IsLimit (KernelFork.ofι S.v₀₁.τ₂ S.w₀₂_τ₂) :=
  isLimitForkMapOfIsLimit' π₂ S.w₀₂ S.h₀

/-- `L₀.X₃` is the kernel of `v₁₂.τ₃ : L₁.X₃ ⟶ L₂.X₃`. -/
noncomputable def h₀τ₃ : IsLimit (KernelFork.ofι S.v₀₁.τ₃ S.w₀₂_τ₃) :=
  isLimitForkMapOfIsLimit' π₃ S.w₀₂ S.h₀

instance mono_v₀₁_τ₁ : Mono S.v₀₁.τ₁ := mono_of_isLimit_fork S.h₀τ₁
instance mono_v₀₁_τ₂ : Mono S.v₀₁.τ₂ := mono_of_isLimit_fork S.h₀τ₂
instance mono_v₀₁_τ₃ : Mono S.v₀₁.τ₃ := mono_of_isLimit_fork S.h₀τ₃

/-- The upper part of the first column of the snake diagram is exact. -/
lemma exact_C₁_up : (ShortComplex.mk S.v₀₁.τ₁ S.v₁₂.τ₁
    (by rw [← comp_τ₁, S.w₀₂, zero_τ₁])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₁

/-- The upper part of the second column of the snake diagram is exact. -/
lemma exact_C₂_up : (ShortComplex.mk S.v₀₁.τ₂ S.v₁₂.τ₂
    (by rw [← comp_τ₂, S.w₀₂, zero_τ₂])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₂

/-- The upper part of the third column of the snake diagram is exact. -/
lemma exact_C₃_up : (ShortComplex.mk S.v₀₁.τ₃ S.v₁₂.τ₃
    (by rw [← comp_τ₃, S.w₀₂, zero_τ₃])).Exact :=
  exact_of_f_is_kernel _ S.h₀τ₃

instance mono_L₀_f [Mono S.L₁.f] : Mono S.L₀.f := by
  have : Mono (S.L₀.f ≫ S.v₀₁.τ₂) := by
    rw [← S.v₀₁.comm₁₂]
    apply mono_comp
  exact mono_of_mono _ S.v₀₁.τ₂

/-- `L₃.X₁` is the cokernel of `v₁₂.τ₁ : L₁.X₁ ⟶ L₂.X₁`. -/
noncomputable def h₃τ₁ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₁ S.w₁₃_τ₁) :=
  isColimitCoforkMapOfIsColimit' π₁ S.w₁₃ S.h₃

/-- `L₃.X₂` is the cokernel of `v₁₂.τ₂ : L₁.X₂ ⟶ L₂.X₂`. -/
noncomputable def h₃τ₂ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₂ S.w₁₃_τ₂) :=
  isColimitCoforkMapOfIsColimit' π₂ S.w₁₃ S.h₃

/-- `L₃.X₃` is the cokernel of `v₁₂.τ₃ : L₁.X₃ ⟶ L₂.X₃`. -/
noncomputable def h₃τ₃ : IsColimit (CokernelCofork.ofπ S.v₂₃.τ₃ S.w₁₃_τ₃) :=
  isColimitCoforkMapOfIsColimit' π₃ S.w₁₃ S.h₃

instance epi_v₂₃_τ₁ : Epi S.v₂₃.τ₁ := epi_of_isColimit_cofork S.h₃τ₁
instance epi_v₂₃_τ₂ : Epi S.v₂₃.τ₂ := epi_of_isColimit_cofork S.h₃τ₂
instance epi_v₂₃_τ₃ : Epi S.v₂₃.τ₃ := epi_of_isColimit_cofork S.h₃τ₃

/-- The lower part of the first column of the snake diagram is exact. -/
lemma exact_C₁_down: (ShortComplex.mk S.v₁₂.τ₁ S.v₂₃.τ₁
    (by rw [← comp_τ₁, S.w₁₃, zero_τ₁])).Exact :=
  exact_of_g_is_cokernel _ S.h₃τ₁

/-- The lower part of the second column of the snake diagram is exact. -/
lemma exact_C₂_down : (ShortComplex.mk S.v₁₂.τ₂ S.v₂₃.τ₂
    (by rw [← comp_τ₂, S.w₁₃, zero_τ₂])).Exact :=
  exact_of_g_is_cokernel _ S.h₃τ₂

/-- The lower part of the third column of the snake diagram is exact. -/
lemma exact_C₃_down : (ShortComplex.mk S.v₁₂.τ₃ S.v₂₃.τ₃
    (by rw [← comp_τ₃, S.w₁₃, zero_τ₃])).Exact :=
  exact_of_g_is_cokernel _ S.h₃τ₃

instance epi_L₃_g [Epi S.L₂.g] : Epi S.L₃.g := by
  have : Epi (S.v₂₃.τ₂ ≫ S.L₃.g) := by
    rw [S.v₂₃.comm₂₃]
    apply epi_comp
  exact epi_of_epi S.v₂₃.τ₂ _

end SnakeInput

end ShortComplex

end CategoryTheory
