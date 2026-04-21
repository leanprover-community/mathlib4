/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.Refinements

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

Given such a `S : SnakeInput C`, we define a connecting homomorphism
`S.δ : L₀.X₃ ⟶ L₃.X₁` and show that it is part of an exact sequence
`L₀.X₁ ⟶ L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂ ⟶ L₃.X₃`. Each of the four exactness
statement is first stated separately as lemmas `L₀_exact`, `L₁'_exact`,
`L₂'_exact` and `L₃_exact` and the full 6-term exact sequence is stated
as `snake_lemma`. This sequence can even be extended with an extra `0`
on the left (see `mono_L₀_f`) if `L₁.X₁ ⟶ L₁.X₂` is a mono (i.e. `L₁` is short exact),
and similarly an extra `0` can be added on the right (`epi_L₃_g`)
if `L₂.X₂ ⟶ L₂.X₃` is an epi (i.e. `L₂` is short exact).

These results were also obtained in the Liquid Tensor Experiment. The code and the proof
here are slightly easier because of the use of the category `ShortComplex C`,
the use of duality (which allows to construct only half of the sequence, and deducing
the other half by arguing in the opposite category), and the use of "refinements"
(see `CategoryTheory.Abelian.Refinements`) instead of a weak form of pseudo-elements.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable (C : Type*) [Category* C] [Abelian C]

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
  w₀₂ : v₀₁ ≫ v₁₂ = 0 := by cat_disch
  w₁₃ : v₁₂ ≫ v₂₃ = 0 := by cat_disch
  /-- `L₀` is the kernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₀ : IsLimit (KernelFork.ofι _ w₀₂)
  /-- `L₃` is the cokernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₃ : IsColimit (CokernelCofork.ofπ _ w₁₃)
  L₁_exact : L₁.Exact
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
lemma exact_C₁_down : (ShortComplex.mk S.v₁₂.τ₁ S.v₂₃.τ₁
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

lemma L₀_exact : S.L₀.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ S.v₀₁.τ₂)
    (by rw [assoc, S.v₀₁.comm₂₃, reassoc_of% hx₂, zero_comp])
  have hy₁' : y₁ ≫ S.v₁₂.τ₁ = 0 := by
    simp only [← cancel_mono S.L₂.f, assoc, zero_comp, S.v₁₂.comm₁₂,
      ← reassoc_of% hy₁, w₀₂_τ₂, comp_zero]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ≫ S.v₀₁.τ₁ = y₁ := ⟨_, S.exact_C₁_up.lift_f y₁ hy₁'⟩
  refine ⟨A₁, π₁, hπ₁, x₁, ?_⟩
  simp only [← cancel_mono S.v₀₁.τ₂, assoc, ← S.v₀₁.comm₁₂, reassoc_of% hx₁, hy₁]

lemma L₃_exact : S.L₃.Exact := S.op.L₀_exact.unop

/-- The fiber product of `L₁.X₂` and `L₀.X₃` over `L₁.X₃`. This is an auxiliary
object in the construction of the morphism `δ : L₀.X₃ ⟶ L₃.X₁`. -/
noncomputable def P := pullback S.L₁.g S.v₀₁.τ₃

/-- The canonical map `P ⟶ L₂.X₂`. -/
noncomputable def φ₂ : S.P ⟶ S.L₂.X₂ := pullback.fst _ _ ≫ S.v₁₂.τ₂

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma lift_φ₂ {A : C} (a : A ⟶ S.L₁.X₂) (b : A ⟶ S.L₀.X₃) (h : a ≫ S.L₁.g = b ≫ S.v₀₁.τ₃) :
    pullback.lift a b h ≫ S.φ₂ = a ≫ S.v₁₂.τ₂ := by
  simp [φ₂]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map `P ⟶ L₂.X₁`. -/
noncomputable def φ₁ : S.P ⟶ S.L₂.X₁ :=
  S.L₂_exact.lift S.φ₂
    (by simp only [φ₂, assoc, S.v₁₂.comm₂₃, pullback.condition_assoc, w₀₂_τ₃, comp_zero])

@[reassoc (attr := simp)] lemma φ₁_L₂_f : S.φ₁ ≫ S.L₂.f = S.φ₂ := S.L₂_exact.lift_f _ _

set_option backward.isDefEq.respectTransparency false in
/-- The short complex that is part of an exact sequence `L₁.X₁ ⟶ P ⟶ L₀.X₃ ⟶ 0`. -/
noncomputable def L₀' : ShortComplex C where
  X₁ := S.L₁.X₁
  X₂ := S.P
  X₃ := S.L₀.X₃
  f := pullback.lift S.L₁.f 0 (by simp)
  g := pullback.snd _ _
  zero := by simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)] lemma L₁_f_φ₁ : S.L₀'.f ≫ S.φ₁ = S.v₁₂.τ₁ := by
  dsimp only [L₀']
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, φ₂, pullback.lift_fst_assoc,
    S.v₁₂.comm₁₂]

set_option backward.isDefEq.respectTransparency false in
instance : Epi S.L₀'.g := by dsimp only [L₀']; infer_instance

set_option backward.isDefEq.respectTransparency false in
instance [Mono S.L₁.f] : Mono S.L₀'.f :=
  mono_of_mono_fac (show S.L₀'.f ≫ pullback.fst _ _ = S.L₁.f by simp [L₀'])

set_option backward.isDefEq.respectTransparency false in
lemma L₀'_exact : S.L₀'.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp [L₀'] at x₂ hx₂
  obtain ⟨A', π, hπ, x₁, fac⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ pullback.fst _ _)
    (by rw [assoc, pullback.condition, reassoc_of% hx₂, zero_comp])
  exact ⟨A', π, hπ, x₁, pullback.hom_ext (by simpa [L₀'] using fac) (by simp [L₀', hx₂])⟩

set_option backward.isDefEq.respectTransparency false in
/-- The connecting homomorphism `δ : L₀.X₃ ⟶ L₃.X₁`. -/
noncomputable def δ : S.L₀.X₃ ⟶ S.L₃.X₁ :=
  S.L₀'_exact.desc (S.φ₁ ≫ S.v₂₃.τ₁) (by simp only [L₁_f_φ₁_assoc, w₁₃_τ₁])

set_option backward.isDefEq.respectTransparency false in -- This is needed below.
@[reassoc (attr := simp)]
lemma snd_δ : (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁ :=
  S.L₀'_exact.g_desc _ _

/-- The pushout of `L₂.X₂` and `L₃.X₁` along `L₂.X₁`. -/
noncomputable def P' := pushout S.L₂.f S.v₂₃.τ₁

set_option backward.isDefEq.respectTransparency false in
lemma snd_δ_inr : (pullback.snd _ _ : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr _ _ : _ ⟶ S.P') =
    pullback.fst _ _ ≫ S.v₁₂.τ₂ ≫ pushout.inl _ _ := by
  simp only [snd_δ_assoc, ← pushout.condition, φ₂, φ₁_L₂_f_assoc, assoc]

/-- The canonical morphism `L₀.X₂ ⟶ P`. -/
@[simp]
noncomputable def L₀X₂ToP : S.L₀.X₂ ⟶ S.P := pullback.lift S.v₀₁.τ₂ S.L₀.g S.v₀₁.comm₂₃

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma L₀X₂ToP_comp_pullback_snd : S.L₀X₂ToP ≫ pullback.snd _ _ = S.L₀.g := by simp

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma L₀X₂ToP_comp_φ₁ : S.L₀X₂ToP ≫ S.φ₁ = 0 := by
  simp only [← cancel_mono S.L₂.f, L₀X₂ToP, assoc, φ₂, φ₁_L₂_f,
    pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

set_option backward.isDefEq.respectTransparency false in
lemma L₀_g_δ : S.L₀.g ≫ S.δ = 0 := by
  rw [← L₀X₂ToP_comp_pullback_snd, assoc]
  erw [S.L₀'_exact.g_desc]
  rw [L₀X₂ToP_comp_φ₁_assoc, zero_comp]

set_option backward.isDefEq.respectTransparency false in
lemma δ_L₃_f : S.δ ≫ S.L₃.f = 0 := by
  rw [← cancel_epi S.L₀'.g]
  erw [S.L₀'_exact.g_desc_assoc]
  simp [S.v₂₃.comm₁₂, φ₂]

/-- The short complex `L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁`. -/
@[simps]
noncomputable def L₁' : ShortComplex C := ShortComplex.mk _ _ S.L₀_g_δ

/-- The short complex `L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂`. -/
@[simps]
noncomputable def L₂' : ShortComplex C := ShortComplex.mk _ _ S.δ_L₃_f

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of `L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁`. -/
lemma L₁'_exact : S.L₁'.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A₀ x₃ hx₃
  dsimp at x₃ hx₃
  obtain ⟨A₁, π₁, hπ₁, p, hp⟩ := surjective_up_to_refinements_of_epi S.L₀'.g x₃
  dsimp [L₀'] at p hp
  have hp' : (p ≫ S.φ₁) ≫ S.v₂₃.τ₁ = 0 := by
    rw [assoc, ← S.snd_δ, ← reassoc_of% hp, hx₃, comp_zero]
  obtain ⟨A₂, π₂, hπ₂, x₁, hx₁⟩ := S.exact_C₁_down.exact_up_to_refinements (p ≫ S.φ₁) hp'
  dsimp at x₁ hx₁
  let x₂' := x₁ ≫ S.L₁.f
  let x₂ := π₂ ≫ p ≫ pullback.fst _ _
  have hx₂' : (x₂ - x₂') ≫ S.v₁₂.τ₂ = 0 := by
    simp only [x₂, x₂', sub_comp, assoc, ← S.v₁₂.comm₁₂, ← reassoc_of% hx₁, φ₂, φ₁_L₂_f, sub_self]
  let k₂ : A₂ ⟶ S.L₀.X₂ := S.exact_C₂_up.lift _ hx₂'
  have hk₂ : k₂ ≫ S.v₀₁.τ₂ = x₂ - x₂' := S.exact_C₂_up.lift_f _ _
  have hk₂' : k₂ ≫ S.L₀.g = π₂ ≫ p ≫ pullback.snd _ _ := by
    simp only [x₂, x₂', ← cancel_mono S.v₀₁.τ₃, assoc, ← S.v₀₁.comm₂₃, reassoc_of% hk₂,
      sub_comp, S.L₁.zero, comp_zero, sub_zero, pullback.condition]
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, k₂, by simp only [assoc, L₁'_f, ← hk₂', hp]⟩

/-- The duality isomorphism `S.P ≅ Opposite.unop S.op.P'`. -/
noncomputable def PIsoUnopOpP' : S.P ≅ Opposite.unop S.op.P' := pullbackIsoUnopPushout _ _

/-- The duality isomorphism `S.P' ≅ Opposite.unop S.op.P`. -/
noncomputable def P'IsoUnopOpP : S.P' ≅ Opposite.unop S.op.P := pushoutIsoUnopPullback _ _

set_option backward.isDefEq.respectTransparency false in
lemma op_δ : S.op.δ = S.δ.op := Quiver.Hom.unop_inj (by
  rw [Quiver.Hom.unop_op, ← cancel_mono (pushout.inr _ _ : _ ⟶ S.P'),
    ← cancel_epi (pullback.snd _ _ : S.P ⟶ _), S.snd_δ_inr,
    ← cancel_mono S.P'IsoUnopOpP.hom, ← cancel_epi S.PIsoUnopOpP'.inv,
    P'IsoUnopOpP, PIsoUnopOpP', assoc, assoc, assoc, assoc,
    pushoutIsoUnopPullback_inr_hom, pullbackIsoUnopPushout_inv_snd_assoc,
    pushoutIsoUnopPullback_inl_hom, pullbackIsoUnopPushout_inv_fst_assoc]
  apply Quiver.Hom.op_inj
  simpa only [op_comp, Quiver.Hom.op_unop, assoc] using S.op.snd_δ_inr)

/-- The duality isomorphism `S.L₂'.op ≅ S.op.L₁'`. -/
noncomputable def L₂'OpIso : S.L₂'.op ≅ S.op.L₁' :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by dsimp; simp only [id_comp, comp_id, S.op_δ])

/-- Exactness of `L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂`. -/
lemma L₂'_exact : S.L₂'.Exact := by
  rw [← exact_op_iff, exact_iff_of_iso S.L₂'OpIso]
  exact S.op.L₁'_exact

/-- The diagram `S.L₀.X₁ ⟶ S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂ ⟶ S.L₃.X₃` for any
`S : SnakeInput C`. -/
noncomputable abbrev composableArrows : ComposableArrows C 5 :=
  ComposableArrows.mk₅ S.L₀.f S.L₀.g S.δ S.L₃.f S.L₃.g

open ComposableArrows in
/-- The diagram `S.L₀.X₁ ⟶ S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂ ⟶ S.L₃.X₃` is exact
for any `S : SnakeInput C`. -/
lemma snake_lemma : S.composableArrows.Exact :=
  exact_of_δ₀ S.L₀_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₁'_exact.exact_toComposableArrows
    (exact_of_δ₀ S.L₂'_exact.exact_toComposableArrows
    S.L₃_exact.exact_toComposableArrows))

set_option backward.isDefEq.respectTransparency false in
lemma δ_eq {A : C} (x₃ : A ⟶ S.L₀.X₃) (x₂ : A ⟶ S.L₁.X₂) (x₁ : A ⟶ S.L₂.X₁)
    (h₂ : x₂ ≫ S.L₁.g = x₃ ≫ S.v₀₁.τ₃) (h₁ : x₁ ≫ S.L₂.f = x₂ ≫ S.v₁₂.τ₂) :
    x₃ ≫ S.δ = x₁ ≫ S.v₂₃.τ₁ := by
  have H := (pullback.lift x₂ x₃ h₂) ≫= S.snd_δ
  rw [pullback.lift_snd_assoc] at H
  rw [H, ← assoc]
  congr 1
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, lift_φ₂, h₁]

theorem mono_δ (h₀ : IsZero S.L₀.X₂) : Mono S.δ :=
  (S.L₁'.exact_iff_mono (IsZero.eq_zero_of_src h₀ S.L₁'.f)).1 S.L₁'_exact

theorem epi_δ (h₃ : IsZero S.L₃.X₂) : Epi S.δ :=
  (S.L₂'.exact_iff_epi (IsZero.eq_zero_of_tgt h₃ S.L₂'.g)).1 S.L₂'_exact

theorem isIso_δ (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂) : IsIso S.δ :=
  @Balanced.isIso_of_mono_of_epi _ _ _ _ _ S.δ (S.mono_δ h₀) (S.epi_δ h₃)

/-- When `L₀₂` and `L₃₂` are trivial, `δ` defines an isomorphism `L₀₃ ≅ L₃₁`. -/
noncomputable def δIso (h₀ : IsZero S.L₀.X₂) (h₃ : IsZero S.L₃.X₂) :
    S.L₀.X₃ ≅ S.L₃.X₁ :=
  @asIso _ _ _ _ S.δ (SnakeInput.isIso_δ S h₀ h₃)

variable (S₁ S₂ S₃ : SnakeInput C)

/-- A morphism of snake inputs involve four morphisms of short complexes
which make the obvious diagram commute. -/
@[ext]
structure Hom where
  /-- a morphism between the zeroth lines -/
  f₀ : S₁.L₀ ⟶ S₂.L₀
  /-- a morphism between the first lines -/
  f₁ : S₁.L₁ ⟶ S₂.L₁
  /-- a morphism between the second lines -/
  f₂ : S₁.L₂ ⟶ S₂.L₂
  /-- a morphism between the third lines -/
  f₃ : S₁.L₃ ⟶ S₂.L₃
  comm₀₁ : f₀ ≫ S₂.v₀₁ = S₁.v₀₁ ≫ f₁ := by cat_disch
  comm₁₂ : f₁ ≫ S₂.v₁₂ = S₁.v₁₂ ≫ f₂ := by cat_disch
  comm₂₃ : f₂ ≫ S₂.v₂₃ = S₁.v₂₃ ≫ f₃ := by cat_disch

namespace Hom

attribute [reassoc] comm₀₁ comm₁₂ comm₂₃

/-- The identity morphism of a snake input. -/
@[simps]
def id : Hom S S where
  f₀ := 𝟙 _
  f₁ := 𝟙 _
  f₂ := 𝟙 _
  f₃ := 𝟙 _

variable {S₁ S₂ S₃}

/-- The composition of morphisms of snake inputs. -/
@[simps]
def comp (f : Hom S₁ S₂) (g : Hom S₂ S₃) : Hom S₁ S₃ where
  f₀ := f.f₀ ≫ g.f₀
  f₁ := f.f₁ ≫ g.f₁
  f₂ := f.f₂ ≫ g.f₂
  f₃ := f.f₃ ≫ g.f₃
  comm₀₁ := by simp only [assoc, comm₀₁, comm₀₁_assoc]
  comm₁₂ := by simp only [assoc, comm₁₂, comm₁₂_assoc]
  comm₂₃ := by simp only [assoc, comm₂₃, comm₂₃_assoc]

end Hom

instance : Category (SnakeInput C) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

variable {S₁ S₂ S₃}

@[simp] lemma id_f₀ : Hom.f₀ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_f₁ : Hom.f₁ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_f₂ : Hom.f₂ (𝟙 S) = 𝟙 _ := rfl
@[simp] lemma id_f₃ : Hom.f₃ (𝟙 S) = 𝟙 _ := rfl

section

variable (f : S₁ ⟶ S₂) (g : S₂ ⟶ S₃)

@[simp, reassoc] lemma comp_f₀ : (f ≫ g).f₀ = f.f₀ ≫ g.f₀ := rfl
@[simp, reassoc] lemma comp_f₁ : (f ≫ g).f₁ = f.f₁ ≫ g.f₁ := rfl
@[simp, reassoc] lemma comp_f₂ : (f ≫ g).f₂ = f.f₂ ≫ g.f₂ := rfl
@[simp, reassoc] lemma comp_f₃ : (f ≫ g).f₃ = f.f₃ ≫ g.f₃ := rfl

end

/-- The functor which sends `S : SnakeInput C` to its zeroth line `S.L₀`. -/
@[simps]
def functorL₀ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₀
  map f := f.f₀

/-- The functor which sends `S : SnakeInput C` to its zeroth line `S.L₁`. -/
@[simps]
def functorL₁ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₁
  map f := f.f₁

/-- The functor which sends `S : SnakeInput C` to its second line `S.L₂`. -/
@[simps]
def functorL₂ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₂
  map f := f.f₂

/-- The functor which sends `S : SnakeInput C` to its third line `S.L₃`. -/
@[simps]
def functorL₃ : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₃
  map f := f.f₃

set_option backward.isDefEq.respectTransparency false in
/-- The functor which sends `S : SnakeInput C` to the auxiliary object `S.P`,
which is `pullback S.L₁.g S.v₀₁.τ₃`. -/
@[simps]
noncomputable def functorP : SnakeInput C ⥤ C where
  obj S := S.P
  map f := pullback.map _ _ _ _ f.f₁.τ₂ f.f₀.τ₃ f.f₁.τ₃ f.f₁.comm₂₃.symm
      (congr_arg ShortComplex.Hom.τ₃ f.comm₀₁.symm)
  map_id _ := by dsimp [P]; simp
  map_comp _ _ := by dsimp [P]; cat_disch

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma naturality_φ₂ (f : S₁ ⟶ S₂) : S₁.φ₂ ≫ f.f₂.τ₂ = functorP.map f ≫ S₂.φ₂ := by
  dsimp [φ₂]
  simp only [assoc, pullback.lift_fst_assoc, ← comp_τ₂, f.comm₁₂]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma naturality_φ₁ (f : S₁ ⟶ S₂) : S₁.φ₁ ≫ f.f₂.τ₁ = functorP.map f ≫ S₂.φ₁ := by
  simp only [← cancel_mono S₂.L₂.f, assoc, φ₁_L₂_f, ← naturality_φ₂, f.f₂.comm₁₂, φ₁_L₂_f_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma naturality_δ (f : S₁ ⟶ S₂) : S₁.δ ≫ f.f₃.τ₁ = f.f₀.τ₃ ≫ S₂.δ := by
  rw [← cancel_epi (pullback.snd _ _ : S₁.P ⟶ _), S₁.snd_δ_assoc, ← comp_τ₁, ← f.comm₂₃,
    comp_τ₁, naturality_φ₁_assoc, ← S₂.snd_δ, functorP_map, pullback.lift_snd_assoc, assoc]

/-- The functor which sends `S : SnakeInput C` to `S.L₁'` which is
`S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁`. -/
@[simps]
noncomputable def functorL₁' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₁'
  map f :=
    { τ₁ := f.f₀.τ₂
      τ₂ := f.f₀.τ₃
      τ₃ := f.f₃.τ₁
      comm₁₂ := f.f₀.comm₂₃
      comm₂₃ := (naturality_δ f).symm }

/-- The functor which sends `S : SnakeInput C` to `S.L₂'` which is
`S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂`. -/
@[simps]
noncomputable def functorL₂' : SnakeInput C ⥤ ShortComplex C where
  obj S := S.L₂'
  map f :=
    { τ₁ := f.f₀.τ₃
      τ₂ := f.f₃.τ₁
      τ₃ := f.f₃.τ₂
      comm₁₂ := (naturality_δ f).symm
      comm₂₃ := f.f₃.comm₁₂ }

/-- The functor which maps `S : SnakeInput C` to the diagram
`S.L₀.X₁ ⟶ S.L₀.X₂ ⟶ S.L₀.X₃ ⟶ S.L₃.X₁ ⟶ S.L₃.X₂ ⟶ S.L₃.X₃`. -/
@[simps]
noncomputable def composableArrowsFunctor : SnakeInput C ⥤ ComposableArrows C 5 where
  obj S := S.composableArrows
  map f := ComposableArrows.homMk₅ f.f₀.τ₁ f.f₀.τ₂ f.f₀.τ₃ f.f₃.τ₁ f.f₃.τ₂ f.f₃.τ₃
    f.f₀.comm₁₂.symm f.f₀.comm₂₃.symm (naturality_δ f) f.f₃.comm₁₂.symm f.f₃.comm₂₃.symm

end SnakeInput

end ShortComplex

end CategoryTheory
