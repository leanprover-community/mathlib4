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
* `Real.sigmoid` : the sigmoid function from `ℝ` to `ℝ`.
* `Real.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `Real.continuous_sigmoid` : the sigmoid function is continuous.
* `Real.sigmoid_tendsto_nhds_1_atTop` : the sigmoid function tends to `1` at `+∞`.
* `Real.sigmoid_tendsto_nhds_0_atBot` : the sigmoid function tends to `0` at `-∞`.
* `Real.hasDerivAt_sigmoid` : the derivative of the sigmoid function.
* `Real.analyticAt_sigmoid` : the sigmoid function is analytic at every point.

### Sigmoid as a function from `ℝ` to `I`
* `unitInterval.sigmoid` : the sigmoid function from `ℝ` to `I`.
* `unitInterval.sigmoid_strictMono` : the sigmoid function is strictly monotone.
* `unitInterval.continuous_sigmoid` : the sigmoid function is continuous.
* `unitInterval.sigmoid_tendsto_nhds_1_atTop` : the sigmoid function tends to `1` at `+∞`.
* `unitInterval.sigmoid_tendsto_nhds_0_atBot` : the sigmoid function tends to `0` at `-∞`.

### Sigmoid as an `OrderEmbedding` from `ℝ` to `I`
* `OrderEmbedding.sigmoid` : the sigmoid function as an `OrderEmbedding` from `ℝ` to `I`.
* `OrderEmbedding.isEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a topological
  embedding.
* `OrderEmbedding.measurableEmbedding_sigmoid` : the sigmoid function from `ℝ` to `I` is a
  measurable embedding.
* `OrderEmbedding.measurableEmbedding_sigmoid_comp_embeddingReal` : the composition of the
  sigmoid function from `ℝ` to `I` with the measurable embedding from a standard Borel
  space `α` to `ℝ` is a measurable embedding from `α` to `I`.

## Tags
sigmoid, embedding, measurable embedding, topological embedding
-/

namespace Real

/-- The sigmoid function from `ℝ` to `ℝ`. -/
noncomputable def sigmoid (x : ℝ) := (1 + exp (-x))⁻¹

lemma sigmoid_def (x : ℝ) : sigmoid x = (1 + exp (-x))⁻¹ := rfl

@[simp]
lemma sigmoid_zero : sigmoid 0 = (2)⁻¹ := by
  refine inv_inj.mpr ?_
  rw [neg_zero, exp_zero]
  ring

@[bound]
lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := by
  change 0 < (1 + exp (-x))⁻¹
  positivity

@[bound]
lemma sigmoid_nonneg (x : ℝ) : 0 ≤ sigmoid x := (sigmoid_pos x).le

@[bound]
lemma sigmoid_lt_one (x : ℝ) : sigmoid x < 1 :=
  inv_lt_one_of_one_lt₀ <| (lt_add_iff_pos_right 1).mpr <| exp_pos _

@[bound]
lemma sigmoid_le_one (x : ℝ) : sigmoid x ≤ 1 := (sigmoid_lt_one x).le

@[mono]
lemma sigmoid_strictMono : StrictMono sigmoid := fun a b hab ↦ by
  simp only [sigmoid]
  gcongr

lemma sigmoid_le_iff {a b : ℝ} : sigmoid a ≤ sigmoid b ↔ a ≤ b := sigmoid_strictMono.le_iff_le

@[gcongr]
lemma sigmoid_le {a b : ℝ} : a ≤ b → sigmoid a ≤ sigmoid b := sigmoid_le_iff.mpr

lemma sigmoid_lt_iff {a b : ℝ} : sigmoid a < sigmoid b ↔ a < b := sigmoid_strictMono.lt_iff_lt

@[gcongr]
lemma sigmoid_lt {a b : ℝ} : a < b → sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone

lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
lemma sigmoid_inj {a b : ℝ} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

@[fun_prop]
lemma continuous_sigmoid : Continuous sigmoid := by
  refine Continuous.inv₀ ?_ ?_
  · continuity
  · intro x
    positivity

lemma sigmoid_neg (x : ℝ) : sigmoid (-x) = 1 - sigmoid x := by
  simp only [sigmoid_def]
  field_simp
  simp [add_mul, ← Real.exp_add, add_comm (1 : ℝ)]

lemma sigmoid_mul_rexp_neg (x : ℝ) : sigmoid x * exp (-x) = sigmoid (-x) := by
  rw [sigmoid_neg, sigmoid_def]
  field_simp
  ring

open Set in
lemma range_sigmoid : range Real.sigmoid = Ioo 0 1 := by
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rintro - ⟨x, rfl⟩
    simp only [mem_Ioo]
    bound
  · replace hx : 0 < x⁻¹ - 1 := by rwa [sub_pos, one_lt_inv_iff₀]
    exact ⟨-(log (x⁻¹ - 1)), by simp [sigmoid_def, exp_log hx]⟩

open Topology Filter

lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) := by
  simpa using Real.tendsto_exp_comp_nhds_zero.mpr tendsto_neg_atTop_atBot |>.const_add 1 |>.inv₀ <|
    by norm_num

lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_const_nhds.add_atTop (tendsto_exp_comp_atTop.mpr tendsto_neg_atBot_atTop)
    |>.inv_tendsto_atTop

lemma hasDerivAt_sigmoid (x : ℝ) :
    HasDerivAt sigmoid (sigmoid x * (1 - sigmoid x)) x := by
  convert (hasDerivAt_neg' x |>.exp.const_add 1 |>.inv <| by positivity) using 1
  rw [← sigmoid_neg, ← sigmoid_mul_rexp_neg x, sigmoid_def]
  field_simp [sq]

lemma deriv_sigmoid : deriv sigmoid = fun x => sigmoid x * (1 - sigmoid x) :=
  funext fun x => (hasDerivAt_sigmoid x).deriv

open Set

variable {x : ℝ}

@[fun_prop]
lemma analyticAt_sigmoid : AnalyticAt ℝ sigmoid x :=
  AnalyticAt.fun_inv (by fun_prop) (by positivity)

theorem analyticOnNhd_sigmoid : AnalyticOnNhd ℝ sigmoid Set.univ :=
  fun _ _ ↦ analyticAt_sigmoid

lemma analyticOn_sigmoid : AnalyticOn ℝ sigmoid Set.univ :=
  analyticOnNhd_sigmoid.analyticOn

lemma analyticWithinAt_sigmoid {s : Set ℝ} : AnalyticWithinAt ℝ sigmoid s x :=
  analyticAt_sigmoid.analyticWithinAt

open ContDiff in
lemma contDiff_sigmoid : ContDiff ℝ ω sigmoid := analyticOn_sigmoid.contDiff

@[fun_prop]
theorem differentiable_sigmoid : Differentiable ℝ sigmoid :=
   contDiff_sigmoid.of_le le_top |>.differentiable_one

@[fun_prop]
theorem differentiableAt_sigmoid {x : ℝ} : DifferentiableAt ℝ sigmoid x :=
  differentiable_sigmoid x

end Real

namespace unitInterval

/-- The sigmoid function from `ℝ` to `I`. -/
noncomputable def sigmoid : ℝ → I := Subtype.coind Real.sigmoid (fun _ ↦ ⟨by bound, by bound⟩)

@[bound]
lemma sigmoid_pos (x : ℝ) : 0 < sigmoid x := Real.sigmoid_pos x

@[bound]
lemma sigmoid_lt_one (x : ℝ) : sigmoid x < 1 := Real.sigmoid_lt_one x

@[mono]
lemma sigmoid_strictMono : StrictMono sigmoid := Real.sigmoid_strictMono

lemma sigmoid_le_iff {a b : ℝ} : sigmoid a ≤ sigmoid b ↔ a ≤ b := Real.sigmoid_le_iff

@[gcongr]
lemma sigmoid_le {a b : ℝ} : a ≤ b → sigmoid a ≤ sigmoid b := sigmoid_le_iff.mpr

lemma sigmoid_lt_iff {a b : ℝ} : sigmoid a < sigmoid b ↔ a < b := Real.sigmoid_lt_iff

@[gcongr]
lemma sigmoid_lt {a b : ℝ} : a < b → sigmoid a < sigmoid b := sigmoid_lt_iff.mpr

@[mono]
lemma sigmoid_monotone : Monotone sigmoid := sigmoid_strictMono.monotone

lemma sigmoid_injective : Function.Injective sigmoid := sigmoid_strictMono.injective

@[simp]
lemma sigmoid_inj {a b : ℝ} : sigmoid a = sigmoid b ↔ a = b := sigmoid_injective.eq_iff

@[fun_prop]
lemma continuous_sigmoid : Continuous sigmoid := Real.continuous_sigmoid.subtype_mk _

lemma sigmoid_neg (x : ℝ) : sigmoid (-x) = σ (sigmoid x) := by
  ext
  exact Real.sigmoid_neg x

open Set Real in
lemma range_sigmoid : range unitInterval.sigmoid = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    constructor
    · change (0 : ℝ) < (1 + exp (-y))⁻¹
      positivity
    · exact inv_lt_one_of_one_lt₀ <| lt_add_of_pos_right 1 (exp_pos (-y))
  · intro hx
    use -(log (-1 + x.1⁻¹))
    suffices exp (log (-1 + x.1⁻¹)) = -1 + x.1⁻¹ by
      simp [sigmoid, Subtype.coind, Real.sigmoid, this]
    exact exp_log (lt_neg_add_iff_lt.mpr <| one_lt_inv_iff₀.mpr hx)

open Topology Filter

lemma tendsto_sigmoid_atTop : Tendsto sigmoid atTop (𝓝 1) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atTop

lemma tendsto_sigmoid_atBot : Tendsto sigmoid atBot (𝓝 0) :=
  tendsto_subtype_rng.mpr Real.tendsto_sigmoid_atBot

end unitInterval

section Embedding

open unitInterval Function Set

/-- The Sigmoid function as an `OrderEmbedding` from `ℝ` to `I`. -/
noncomputable def OrderEmbedding.sigmoid : ℝ ↪o I :=
  OrderEmbedding.ofStrictMono unitInterval.sigmoid sigmoid_strictMono

lemma Topology.isEmbedding_sigmoid : IsEmbedding unitInterval.sigmoid :=
  OrderEmbedding.sigmoid.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => range_sigmoid ▸ Ioo_subset_Ioo a.2.1 b.2.2)

lemma measurableEmbedding_sigmoid : MeasurableEmbedding unitInterval.sigmoid :=
  Topology.isEmbedding_sigmoid.measurableEmbedding <| range_sigmoid ▸ measurableSet_Ioo

variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

lemma measurableEmbedding_sigmoid_comp_embeddingReal :
    MeasurableEmbedding (unitInterval.sigmoid ∘ MeasureTheory.embeddingReal α) :=
  measurableEmbedding_sigmoid.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

end Embedding
