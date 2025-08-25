/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Sigmoid function

In this file we define the sigmoid function `x : ℝ ↦ (1 + exp (-x))⁻¹` and prove some of
its analytic properties.

We then show that the sigmoid function can be seen as an order embedding from `ℝ` to `I = [0, 1]`
and that this embedding is both a topological embedding and a measurable embedding. We also prove
that the composition of this embedding with the measurable embedding from a standard Borel space
`α` to `ℝ` is a measurable embedding from `α` to `I`.

## Main definitions and results

### Sigmoid as a function from `ℝ` to `ℝ`
* `sigmoid` : the sigmoid function from `ℝ` to `ℝ`.
* `sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `sigmoid_tendsto_nhds_1_atTop` : the sigmoid function tends to `1` at `+∞`.
* `sigmoid_tendsto_nhds_0_atBot` : the sigmoid function tends to `0` at `-∞`.
* `hasDerivAt_sigmoid` : the derivative of the sigmoid function.

### Sigmoid as an `OrderEmbedding` from `ℝ` to `I`
* `sigmoid_ord_embedding` : the sigmoid function as an `OrderEmbedding` from `ℝ` to `I`.
* `isEmbedding_sigmoid` : the sigmoid function is a topological embedding.
* `measurableEmbedding_sigmoid` : the sigmoid function is a measurable embedding.
* `measurableEmbedding_sigmoid_comp_embeddingReal` : the composition of `sigmoid_ord_embedding`
  with the measurable embedding from a standard Borel space `α` to `ℝ` is a measurable embedding
  from `α` to `I`.

## Tags
sigmoid, embedding, measurable embedding, topological embedding
-/


open unitInterval Real Set Function

/-- The Sigmoid function from `ℝ` to `ℝ`. -/
noncomputable def sigmoid (x : ℝ) := (1 + exp (-x))⁻¹

lemma sigmoid_def (x : ℝ) : sigmoid x = (1 + exp (-x))⁻¹ := rfl

@[simp]
lemma sigmoid_zero : sigmoid 0 = (2)⁻¹ := by
  refine inv_inj.mpr ?_
  rw [neg_zero, exp_zero]
  ring

@[bound]
lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  simp only [sigmoid]
  positivity

@[bound]
lemma sigmoid_nonneg (x : ℝ) : 0 ≤ sigmoid x := (sigmoid_pos x).le

@[bound]
lemma sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := by
  simp only [sigmoid]
  exact inv_lt_one_of_one_lt₀ <| (lt_add_iff_pos_right 1).mpr <| exp_pos _

@[bound]
lemma sigmoid_le_one (x : ℝ) : sigmoid x ≤ 1 := (sigmoid_lt_one x).le

lemma sigmoid_le_iff {a b : ℝ} : sigmoid a ≤ sigmoid b ↔ a ≤ b := by
  simp only [sigmoid]
  refine ⟨fun h ↦ ?_, fun h ↦ by gcongr⟩
  suffices -b ≤ -a from neg_le_neg_iff.mp this
  rwa [←exp_le_exp, ← add_le_add_iff_left 1, ← inv_le_inv₀ (by positivity) (by positivity)]

lemma sigmoid_lt_iff {a b : ℝ} : sigmoid a < sigmoid b ↔ a < b := by
  simp only [sigmoid]
  refine ⟨fun h ↦ ?_, fun h ↦ by gcongr⟩
  suffices -b < -a from neg_lt_neg_iff.mp this
  rwa [←exp_lt_exp, ← Real.add_lt_add_iff_left 1, ← inv_lt_inv₀ (by positivity) (by positivity)]

@[mono]
lemma sigmoid_strictMono : StrictMono sigmoid := fun a b hab ↦ by
  simp only [sigmoid]
  gcongr

@[mono]
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone

lemma sigmoid_injective : Injective sigmoid := sigmoid_strictMono.injective

@[simp]
lemma sigmoid_eq_sigmoid {a b : ℝ} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

@[continuity]
lemma continuous_sigmoid : Continuous sigmoid := by
  refine Continuous.inv₀ ?_ ?_
  · continuity
  · intro x
    positivity

open Topology Filter

lemma sigmoid_tendsto_nhds_1_atTop : Tendsto sigmoid atTop (𝓝 1) := by
  unfold sigmoid
  nth_rw 2 [← inv_one]
  rw [tendsto_inv_iff₀ (by simp)]
  nth_rw 2 [← AddMonoid.add_zero 1]
  exact tendsto_const_nhds.add tendsto_exp_neg_atTop_nhds_zero

lemma sigmoid_tendsto_nhds_0_atBot : Tendsto sigmoid atBot (𝓝 0) := by
  unfold sigmoid
  refine Tendsto.inv_tendsto_atTop <| tendsto_const_nhds.add_atTop ?_
  exact tendsto_exp_comp_atTop.mpr tendsto_neg_atBot_atTop

lemma hasDerivAt_sigmoid (x : ℝ) :
    HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  let g := fun x => 1 + exp (-x)
  suffices (exp (-x) / g x ^ 2) = (g⁻¹ x * (1 - g⁻¹ x)) by
    have g_inv_eq_sigmoid : sigmoid = g⁻¹ := by ext x; simp [sigmoid, g]
    rw [g_inv_eq_sigmoid, ← this, ← neg_neg (exp (-x))]
    refine HasDerivAt.inv ?_ (by simp only [g]; positivity)
    simp only [g]
    refine HasDerivAt.const_add 1 ?_
    simpa using (hasDerivAt_exp _).comp x (hasDerivAt_neg _)
  simp only [g]
  calc _ = 1 / (1 + exp (-x)) * (exp (-x) / (1 + exp (-x))) := by
        rw [mul_comm, mul_one_div, pow_two]
        exact div_mul_eq_div_div _ _ _
  _ = (1 + exp (-x))⁻¹ * (exp (-x) / (1 + exp (-x))) := by
    simp
  _ = (1 + exp (-x))⁻¹ * (((1 + exp (-x)) - 1) / (1 + exp (-x))) := by
    ring
  _ = (1 + exp (-x))⁻¹ * ((1 + exp (-x)) / (1 + exp (-x)) - 1 / (1 + exp (-x))) := by
    rw [div_sub_div_same]
  _ = _ := by
    rw [div_self (by positivity)]
    simp

lemma deriv_sigmoid : deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x) :=
    funext fun x => (hasDerivAt_sigmoid x).deriv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℝ]

@[simp]
theorem differentiable_sigmoid : Differentiable 𝕜 sigmoid := fun x =>
  (hasDerivAt_sigmoid x).differentiableAt.restrictScalars 𝕜

@[simp]
theorem differentiableAt_sigmoid {x : ℝ} : DifferentiableAt 𝕜 sigmoid x :=
  differentiable_sigmoid x

section OrderEmbedding

/-- The Sigmoid function as an `OrderEmbedding` from `ℝ` to `I`. -/
noncomputable def sigmoid_ord_embedding : ℝ ↪o I where
  toFun a := ⟨sigmoid a, by bound, by bound⟩
  inj' {a b} hab := by
    simp_all only [Subtype.mk.injEq, sigmoid_eq_sigmoid]
  map_rel_iff' {a b} := by
    simp_all only [Embedding.coeFn_mk, Subtype.mk_le_mk]
    exact sigmoid_le_iff

lemma range_sigmoid : range sigmoid_ord_embedding = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · change 0 < (1 + exp (-y))⁻¹
      positivity
    · exact inv_lt_one_of_one_lt₀ <| lt_add_of_pos_right 1 (exp_pos (-y))
  · intro hx
    use -(log (-1 + x.1⁻¹))
    suffices exp (log (-1 + x.1⁻¹)) = -1 + x.1⁻¹ by
      simp only [sigmoid_ord_embedding, sigmoid, RelEmbedding.coe_mk, Embedding.coeFn_mk, neg_neg,
        this, add_neg_cancel_left, inv_inv, Subtype.coe_eta]
    exact exp_log (lt_neg_add_iff_lt.mpr <| one_lt_inv_iff₀.mpr hx)

lemma isEmbedding_sigmoid : Topology.IsEmbedding sigmoid_ord_embedding :=
  sigmoid_ord_embedding.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => range_sigmoid ▸ Ioo_subset_Ioo a.2.1 b.2.2)

lemma measurableEmbedding_sigmoid : MeasurableEmbedding sigmoid_ord_embedding :=
  isEmbedding_sigmoid.measurableEmbedding <| range_sigmoid ▸ measurableSet_Ioo

variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

lemma measurableEmbedding_sigmoid_comp_embeddingReal :
    MeasurableEmbedding (sigmoid_ord_embedding ∘ MeasureTheory.embeddingReal α) :=
  measurableEmbedding_sigmoid.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

end OrderEmbedding
