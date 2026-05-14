/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real
public import Mathlib.Topology.Algebra.Field
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Topological algebra properties of ℝ

This file defines topological field/(semi)ring structures on the
(extended) (nonnegative) reals and shows the algebraic operations are
(uniformly) continuous.

It also includes a bit of more general topological theory of the reals,
needed to define the structures and prove continuity.
-/

public section

assert_not_exists StarRing UniformContinuousConstSMul UniformOnFun

noncomputable section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

instance : NoncompactSpace ℝ := Int.isClosedEmbedding_coe_real.noncompactSpace

theorem Real.uniformContinuous_add : UniformContinuous fun p : ℝ × ℝ => p.1 + p.2 :=
  Metric.uniformContinuous_iff.2 fun _ε ε0 =>
    let ⟨δ, δ0, Hδ⟩ := rat_add_continuous_lemma abs ε0
    ⟨δ, δ0, fun _ _ h =>
      let ⟨h₁, h₂⟩ := max_lt_iff.1 h
      Hδ h₁ h₂⟩

theorem Real.uniformContinuous_neg : UniformContinuous (@Neg.neg ℝ _) :=
  Metric.uniformContinuous_iff.2 fun ε ε0 =>
    ⟨_, ε0, fun _ _ h => by simpa only [abs_sub_comm, Real.dist_eq, neg_sub_neg] using h⟩

instance : IsUniformAddGroup ℝ :=
  IsUniformAddGroup.mk' Real.uniformContinuous_add Real.uniformContinuous_neg

theorem Real.uniformContinuous_const_mul {x : ℝ} : UniformContinuous (x * ·) :=
  uniformContinuous_of_continuousAt_zero (DistribSMul.toAddMonoidHom ℝ x)
    (continuous_const_smul x).continuousAt

-- short-circuit type class inference
instance : IsTopologicalAddGroup ℝ := by infer_instance
instance : IsTopologicalRing ℝ := inferInstance
instance : IsTopologicalDivisionRing ℝ := inferInstance

namespace EReal

instance : ContinuousNeg EReal := ⟨negOrderIso.continuous⟩

end EReal

namespace NNReal

/-!
Instances for the following typeclasses are defined:

* `IsTopologicalSemiring ℝ≥0`
* `ContinuousSub ℝ≥0`
* `ContinuousInv₀ ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `ContinuousSMul ℝ≥0 α` (whenever `α` has a continuous `MulAction ℝ α`)

Everything is inherited from the corresponding structures on the reals.
-/
-- short-circuit type class inference
instance : IsTopologicalSemiring ℝ≥0 where
  toContinuousAdd := continuousAdd_induced toRealHom
  toContinuousMul := continuousMul_induced toRealHom

instance : ContinuousSub ℝ≥0 :=
  ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩

instance : ContinuousInv₀ ℝ≥0 := inferInstance

variable {α : Type*}

instance [TopologicalSpace α] [MulAction ℝ α] [ContinuousSMul ℝ α] :
    ContinuousSMul ℝ≥0 α where
  continuous_smul := continuous_induced_dom.fst'.smul continuous_snd

end NNReal

namespace ENNReal

open Filter NNReal Set Topology

theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe']; exact ordConnected_Iio

@[simp, norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {a : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ≥0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe.tendsto_nhds_iff.symm

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  ⟨isEmbedding_coe, by rw [range_coe']; exact isOpen_Iio⟩

theorem nhds_coe_coe {r p : ℝ≥0} :
    𝓝 ((r : ℝ≥0∞), (p : ℝ≥0∞)) = (𝓝 (r, p)).map fun p : ℝ≥0 × ℝ≥0 => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

instance : ContinuousAdd ℝ≥0∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff,
    Function.comp_def, tendsto_coe, tendsto_add]

instance : ContinuousInv ℝ≥0∞ := ⟨OrderIso.invENNReal.continuous⟩

end ENNReal
