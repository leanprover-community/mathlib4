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
`L₀.X₁ ⟶ L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂ ⟶ L₃.X₃`. This is stated as lemmas
`L₀_exact`, `L₁'_exact`, `L₂'_exact` and `L₃_exact`. This sequence can even
be extended with an extra `0` on the left (see `mono_L₀_f`)
if `L₁.X₁ ⟶ L₁.X₂` is a mono (i.e. `L₁` is short exact),
and similarly an extra `0` can be added on the right (`epi_L₃_g`)
if `L₂.X₂ ⟶ L₂.X₃` is an epi (i.e. `L₂` is short exact).

These results were also obtained in the Liquid Tensor Experiment. The code and the proof
here are slightly easier because of the use of the category `ShortComplex C`,
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

lemma L₀_exact : S.L₀.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  obtain ⟨A₁, π₁, hπ₁, y₁, hy₁⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ S.v₀₁.τ₂)
    (by rw [assoc, S.v₀₁.comm₂₃, reassoc_of% hx₂, zero_comp])
  have hy₁' : y₁ ≫ S.v₁₂.τ₁ = 0 := by
    simp only [← cancel_mono S.L₂.f, assoc, zero_comp, S.v₁₂.comm₁₂,
      ← reassoc_of% hy₁, w₀₂_τ₂, comp_zero]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁, x₁ ≫ S.v₀₁.τ₁ = y₁ := ⟨_, S.exact_C₁_up.lift_f y₁ hy₁'⟩
  refine' ⟨A₁, π₁, hπ₁, x₁, _⟩
  simp only [← cancel_mono S.v₀₁.τ₂, assoc, ← S.v₀₁.comm₁₂, reassoc_of% hx₁, hy₁]

lemma L₃_exact : S.L₃.Exact := S.op.L₀_exact.unop

/-- The fiber product of `L₁.X₂` and `L₀.X₃` over `L₁.X₃`. This is an auxiliary
object in the construction of the morphism `δ : L₀.X₃ ⟶ L₃.X₁`. -/
noncomputable def P := pullback S.L₁.g S.v₀₁.τ₃

/-- The canonical map `P ⟶ L₂.X₂`. -/
noncomputable def φ₂ : S.P ⟶ S.L₂.X₂ := pullback.fst ≫ S.v₁₂.τ₂

/-- The canonical map `P ⟶ L₂.X₁`. -/
noncomputable def φ₁ : S.P ⟶ S.L₂.X₁ :=
  S.L₂_exact.lift S.φ₂
    (by simp only [φ₂, assoc, S.v₁₂.comm₂₃, pullback.condition_assoc, w₀₂_τ₃, comp_zero])

@[reassoc (attr := simp)] lemma φ₁_L₂_f : S.φ₁ ≫ S.L₂.f = S.φ₂ := S.L₂_exact.lift_f _ _

/-- The short complex that is part of an exact sequence `L₁.X₁ ⟶ P ⟶ L₀.X₃ ⟶ 0`. -/
noncomputable def L₀' : ShortComplex C where
  X₁ := S.L₁.X₁
  X₂ := S.P
  X₃ := S.L₀.X₃
  f := pullback.lift S.L₁.f 0 (by simp)
  g := pullback.snd
  zero := by simp

@[reassoc (attr := simp)] lemma L₁_f_φ₁ : S.L₀'.f ≫ S.φ₁ = S.v₁₂.τ₁ := by
  dsimp only [L₀']
  simp only [← cancel_mono S.L₂.f, assoc, φ₁_L₂_f, φ₂, pullback.lift_fst_assoc,
    S.v₁₂.comm₁₂]

instance : Epi S.L₀'.g := by dsimp only [L₀']; infer_instance

instance [Mono S.L₁.f] : Mono S.L₀'.f :=
  mono_of_mono_fac (show S.L₀'.f ≫ pullback.fst = S.L₁.f by simp [L₀'])

lemma L₀'_exact : S.L₀'.Exact := by
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x₂ hx₂
  dsimp [L₀'] at x₂ hx₂
  obtain ⟨A', π, hπ, x₁, fac⟩ := S.L₁_exact.exact_up_to_refinements (x₂ ≫ pullback.fst)
    (by rw [assoc, pullback.condition, reassoc_of% hx₂, zero_comp])
  exact ⟨A', π, hπ, x₁, pullback.hom_ext (by simpa [L₀'] using fac) (by simp [L₀', hx₂])⟩

/-- The connecting homomorphism `δ : L₀.X₃ ⟶ L₃.X₁`. -/
noncomputable def δ : S.L₀.X₃ ⟶ S.L₃.X₁ :=
  S.L₀'_exact.desc (S.φ₁ ≫ S.v₂₃.τ₁) (by simp only [L₁_f_φ₁_assoc, w₁₃_τ₁])

@[reassoc (attr := simp)]
lemma snd_δ : (pullback.snd : S.P ⟶ _) ≫ S.δ = S.φ₁ ≫ S.v₂₃.τ₁ :=
  S.L₀'_exact.g_desc _ _

/-- The pushout of `L₂.X₂` and `L₃.X₁` along `L₂.X₁`. -/
noncomputable def P' := pushout S.L₂.f S.v₂₃.τ₁

lemma snd_δ_inr : (pullback.snd : S.P ⟶ _) ≫ S.δ ≫ (pushout.inr : _ ⟶ S.P') =
    pullback.fst ≫ S.v₁₂.τ₂ ≫ pushout.inl := by
  simp only [snd_δ_assoc, ← pushout.condition, φ₂, φ₁_L₂_f_assoc, assoc]

/-- The canonical morphism `L₀.X₂ ⟶ P`. -/
@[simp]
noncomputable def L₀X₂ToP : S.L₀.X₂ ⟶ S.P := pullback.lift S.v₀₁.τ₂ S.L₀.g S.v₀₁.comm₂₃

@[reassoc]
lemma L₀X₂ToP_comp_pullback_snd : S.L₀X₂ToP ≫ pullback.snd = S.L₀.g := by simp

@[reassoc]
lemma L₀X₂ToP_comp_φ₁ : S.L₀X₂ToP ≫ S.φ₁ = 0 := by
  simp only [← cancel_mono S.L₂.f, L₀X₂ToP, assoc, φ₂, φ₁_L₂_f,
    pullback.lift_fst_assoc, w₀₂_τ₂, zero_comp]

lemma L₀_g_δ : S.L₀.g ≫ S.δ = 0 := by
  erw [← L₀X₂ToP_comp_pullback_snd, assoc, S.L₀'_exact.g_desc,
    L₀X₂ToP_comp_φ₁_assoc, zero_comp]

lemma δ_L₃_f : S.δ ≫ S.L₃.f = 0 := by
  erw [← cancel_epi S.L₀'.g, S.L₀'_exact.g_desc_assoc, assoc, S.v₂₃.comm₁₂, S.φ₁_L₂_f_assoc,
    φ₂, assoc, w₁₃_τ₂, comp_zero, comp_zero]

/-- The short complex `L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁`. -/
@[simps]
noncomputable def L₁' : ShortComplex C := ShortComplex.mk _ _ S.L₀_g_δ

/-- The short complex `L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂`. -/
@[simps]
noncomputable def L₂' : ShortComplex C := ShortComplex.mk _ _ S.δ_L₃_f

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
  let x₂ := π₂ ≫ p ≫ pullback.fst
  have hx₂' : (x₂ - x₂') ≫ S.v₁₂.τ₂ = 0 := by
    simp only [sub_comp, assoc, ← S.v₁₂.comm₁₂, ← reassoc_of% hx₁, φ₂, φ₁_L₂_f, sub_self]
  let k₂ : A₂ ⟶ S.L₀.X₂ := S.exact_C₂_up.lift _ hx₂'
  have hk₂ : k₂ ≫ S.v₀₁.τ₂ = x₂ - x₂' := S.exact_C₂_up.lift_f _ _
  have hk₂' : k₂ ≫ S.L₀.g = π₂ ≫ p ≫ pullback.snd := by
    simp only [← cancel_mono S.v₀₁.τ₃, assoc, ← S.v₀₁.comm₂₃, reassoc_of% hk₂,
      sub_comp, S.L₁.zero, comp_zero, sub_zero, pullback.condition]
  exact ⟨A₂, π₂ ≫ π₁, epi_comp _ _, k₂, by simp only [assoc, L₁'_f, ← hk₂', hp]⟩

/-- The duality isomorphism `S.P ≅ Opposite.unop S.op.P'`. -/
noncomputable def PIsoUnopOpP' : S.P ≅ Opposite.unop S.op.P' := pullbackIsoUnopPushout _ _

/-- The duality isomorphism `S.P' ≅ Opposite.unop S.op.P`. -/
noncomputable def P'IsoUnopOpP : S.P' ≅ Opposite.unop S.op.P := pushoutIsoUnopPullback _ _

lemma op_δ : S.op.δ = S.δ.op := Quiver.Hom.unop_inj (by
  rw [Quiver.Hom.unop_op, ← cancel_mono (pushout.inr : _ ⟶ S.P'),
    ← cancel_epi (pullback.snd : S.P ⟶ _), S.snd_δ_inr,
    ← cancel_mono S.P'IsoUnopOpP.hom, ← cancel_epi S.PIsoUnopOpP'.inv,
    P'IsoUnopOpP, PIsoUnopOpP', assoc, assoc, assoc, assoc,
    pushoutIsoUnopPullback_inr_hom, pullbackIsoUnopPushout_inv_snd_assoc,
    pushoutIsoUnopPullback_inl_hom, pullbackIsoUnopPushout_inv_fst_assoc]
  apply Quiver.Hom.op_inj
  simpa only [op_comp, Quiver.Hom.op_unop, assoc] using S.op.snd_δ_inr)

/-- The duality isomorphism `S.L₂'.op ≅ S.op.L₁'`. -/
noncomputable def L₂'OpIso : S.L₂'.op ≅ S.op.L₁' :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by aesop_cat)
    (by dsimp; simp only [id_comp, comp_id, S.op_δ])

/-- Exactness of `L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂`. -/
lemma L₂'_exact : S.L₂'.Exact := by
  rw [← exact_op_iff, exact_iff_of_iso S.L₂'OpIso]
  exact S.op.L₁'_exact

end SnakeInput

end ShortComplex

end CategoryTheory
