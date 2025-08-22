/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.Topology.UnitInterval

/-!
# Sigmoid function

In this file we define the sigmoid function `Sigmoid : ℝ ↪o I` as an order embedding from the real
line to the unit interval `I = [0, 1]`. We prove that it is a topological embedding and a measurable
embedding. We also prove that the composition of `Sigmoid` with the measurable embedding from a
standard Borel space `α` to `ℝ` is a measurable embedding from `α` to `I`.

## Main definitions and results

* `Sigmoid` : the sigmoid function as an order embedding from `ℝ` to `I`.
* `Sigmoid.is_embedding` : the sigmoid function is a topological embedding.
* `Sigmoid.measurable_real_embedding` : the sigmoid function is a measurable embedding.
* `Sigmoid.measurable_embedding` : the composition of `Sigmoid` with the measurable embedding from a
  standard Borel space `α` to `ℝ` is a measurable embedding from `α` to `I`.

## Tags
sigmoid, embedding, measurable embedding, topological embedding
-/


open unitInterval Real Set Function

/-- The Sigmoid function as an `OrderEmbedding` from `ℝ` to `I`. -/
noncomputable def sigmoid : ℝ ↪o I where
  toFun a := ⟨(1 + exp (-a))⁻¹, by positivity,
    inv_le_one_of_one_le₀ <| (le_add_iff_nonneg_right 1).mpr (exp_nonneg (-a))⟩
  inj' {a b} hab := by
    simp_all only [Subtype.mk.injEq, inv_inj, add_right_inj, exp_eq_exp, neg_inj]
  map_rel_iff' {a b} := by
    simp_all only [Embedding.coeFn_mk, Subtype.mk_le_mk]
    refine ⟨fun h ↦ ?_, fun h ↦ by gcongr⟩
    suffices -b ≤ -a from neg_le_neg_iff.mp this
    rwa [←exp_le_exp, ←add_le_add_iff_left 1, ←inv_le_inv₀ (by positivity) (by positivity)]

namespace Sigmoid

lemma range_sigmoid : range Sigmoid = Ioo 0 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := hx
    constructor
    · simp only [Sigmoid, RelEmbedding.coe_mk, Embedding.coeFn_mk]
      change 0 < (1 + exp (-y))⁻¹
      positivity
    · simp only [Sigmoid]
      change (1 + exp (-y))⁻¹ < 1
      refine inv_lt_one_of_one_lt₀ ?_
      exact lt_add_of_pos_right 1 (exp_pos (-y))
  · intro hx
    rw [mem_range]
    use -(log (-1 + x.1⁻¹))
    simp only [Sigmoid, RelEmbedding.coe_mk, Embedding.coeFn_mk, neg_neg]
    suffices exp (log (-1 + x.1⁻¹)) = -1 + x.1⁻¹ by
      simp only [this, add_neg_cancel_left, inv_inv]
    exact exp_log (lt_neg_add_iff_lt.mpr <| one_lt_inv_iff₀.mpr hx)

lemma isEmbedding_sigmoid : Topology.IsEmbedding Sigmoid :=
  Sigmoid.isEmbedding_of_ordConnected (ordConnected_of_Ioo <|
    fun a _ b _ _ => range_eq ▸ Ioo_subset_Ioo a.2.1 b.2.2)

lemma measurableEmbedding_sigmoid : MeasurableEmbedding Sigmoid :=
  is_embedding.measurableEmbedding <| range_eq ▸ measurableSet_Ioo

variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

lemma measurableEmbedding_sigmoid_comp_embeddingReal : MeasurableEmbedding (Sigmoid ∘ MeasureTheory.embeddingReal α) :=
  measurable_real_embedding.comp (MeasureTheory.measurableEmbedding_embeddingReal α)

end Sigmoid
