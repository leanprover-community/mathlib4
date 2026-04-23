/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Closure
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UrysohnsLemma
/-!
# Urysohn's Metrization Theorem

In this file we prove Urysohn's Metrization Theorem:
a T₃ topological space with second countable topology `X` is metrizable.

First we prove that `X` can be embedded into `l^∞`, then use this embedding to pull back the metric
space structure.

## Implementation notes

We use `ℕ →ᵇ ℝ`, not `lpSpace` for `l^∞` to avoid heavy imports.
-/

@[expose] public section

open Filter Metric Set Topology
open scoped BoundedContinuousFunction

namespace TopologicalSpace

section RegularSpace

variable (X : Type*) [TopologicalSpace X] [RegularSpace X] [SecondCountableTopology X]

/-- For a regular topological space with second countable topology,
there exists an inducing map to `l^∞ = ℕ →ᵇ ℝ`. -/
theorem exists_isInducing_l_infty : ∃ f : X → ℕ →ᵇ ℝ, IsInducing f := by
  -- Choose a countable basis, and consider the set `s` of pairs of set `(U, V)` such that `U ∈ B`,
  -- `V ∈ B`, and `closure U ⊆ V`.
  rcases exists_countable_basis X with ⟨B, hBc, -, hB⟩
  let s : Set (Set X × Set X) := { UV ∈ B ×ˢ B | closure UV.1 ⊆ UV.2 }
  -- `s` is a countable set.
  haveI : Encodable s := ((hBc.prod hBc).mono (sep_subset _ _)).toEncodable
  -- We don't have the space of bounded (possibly discontinuous) functions, so we equip `s`
  -- with the discrete topology and deal with `s →ᵇ ℝ` instead.
  letI : TopologicalSpace s := ⊥
  haveI : DiscreteTopology s := ⟨rfl⟩
  rsuffices ⟨f, hf⟩ : ∃ f : X → s →ᵇ ℝ, IsInducing f
  · exact ⟨fun x => (f x).extend (Encodable.encode' s) 0,
      (BoundedContinuousFunction.isometry_extend (Encodable.encode' s)
        (0 : ℕ →ᵇ ℝ)).isEmbedding.isInducing.comp hf⟩
  have hd : ∀ UV : s, Disjoint (closure UV.1.1) UV.1.2ᶜ :=
    fun UV => disjoint_compl_right.mono_right (compl_subset_compl.2 UV.2.2)
  -- Choose a sequence of `εₙ > 0`, `n : s`, that is bounded above by `1` and tends to zero
  -- along the `cofinite` filter.
  obtain ⟨ε, ε01, hε⟩ : ∃ ε : s → ℝ, (∀ UV, ε UV ∈ Ioc (0 : ℝ) 1) ∧ Tendsto ε cofinite (𝓝 0) := by
    rcases posSumOfEncodable zero_lt_one s with ⟨ε, ε0, c, hεc, hc1⟩
    refine ⟨ε, fun UV => ⟨ε0 UV, ?_⟩, hεc.summable.tendsto_cofinite_zero⟩
    exact (le_hasSum hεc UV fun _ _ => (ε0 _).le).trans hc1
  /- For each `UV = (U, V) ∈ s` we use Urysohn's lemma to choose a function `f UV` that is equal to
    zero on `U` and is equal to `ε UV` on the complement to `V`. -/
  have : ∀ UV : s, ∃ f : C(X, ℝ),
      EqOn f 0 UV.1.1 ∧ EqOn f (fun _ => ε UV) UV.1.2ᶜ ∧ ∀ x, f x ∈ Icc 0 (ε UV) := by
    intro UV
    rcases exists_continuous_zero_one_of_isClosed isClosed_closure
        (hB.isOpen UV.2.1.2).isClosed_compl (hd UV) with
      ⟨f, hf₀, hf₁, hf01⟩
    exact ⟨ε UV • f, fun x hx => by simp [hf₀ (subset_closure hx)], fun x hx => by simp [hf₁ hx],
      fun x => ⟨mul_nonneg (ε01 _).1.le (hf01 _).1, mul_le_of_le_one_right (ε01 _).1.le (hf01 _).2⟩⟩
  choose f hf0 hfε hf0ε using this
  have hf01 : ∀ UV x, f UV x ∈ Icc (0 : ℝ) 1 :=
    fun UV x => Icc_subset_Icc_right (ε01 _).2 (hf0ε _ _)
  -- The embedding is given by `F x UV = f UV x`.
  set F : X → s →ᵇ ℝ := fun x =>
    ⟨⟨fun UV => f UV x, continuous_of_discreteTopology⟩, 1,
      fun UV₁ UV₂ => Real.dist_le_of_mem_Icc_01 (hf01 _ _) (hf01 _ _)⟩
  have hF : ∀ x UV, F x UV = f UV x := fun _ _ => rfl
  refine ⟨F, isInducing_iff_nhds.2 fun x => le_antisymm ?_ ?_⟩
  · /- First we prove that `F` is continuous. Given `δ > 0`, consider the set `T` of `(U, V) ∈ s`
    such that `ε (U, V) ≥ δ`. Since `ε` tends to zero, `T` is finite. Since each `f` is continuous,
    we can choose a neighborhood such that `dist (F y (U, V)) (F x (U, V)) ≤ δ` for any
    `(U, V) ∈ T`. For `(U, V) ∉ T`, the same inequality is true because both `F y (U, V)` and
    `F x (U, V)` belong to the interval `[0, ε (U, V)]`. -/
    refine (nhds_basis_closedBall.comap _).ge_iff.2 fun δ δ0 => ?_
    have h_fin : { UV : s | δ ≤ ε UV }.Finite := by simpa only [← not_lt] using hε (gt_mem_nhds δ0)
    have : ∀ᶠ y in 𝓝 x, ∀ UV, δ ≤ ε UV → dist (F y UV) (F x UV) ≤ δ := by
      refine (eventually_all_finite h_fin).2 fun UV _ => ?_
      exact (f UV).continuous.tendsto x (closedBall_mem_nhds _ δ0)
    refine this.mono fun y hy => (BoundedContinuousFunction.dist_le δ0.le).2 fun UV => ?_
    rcases le_total δ (ε UV) with hle | hle
    exacts [hy _ hle, (Real.dist_le_of_mem_Icc (hf0ε _ _) (hf0ε _ _)).trans (by rwa [sub_zero])]
  · /- Finally, we prove that each neighborhood `V` of `x : X`
    includes a preimage of a neighborhood of `F x` under `F`.
    Without loss of generality, `V` belongs to `B`.
    Choose `U ∈ B` such that `x ∈ V` and `closure V ⊆ U`.
    Then the preimage of the `(ε (U, V))`-neighborhood of `F x` is included by `V`. -/
    refine ((nhds_basis_ball.comap _).le_basis_iff hB.nhds_hasBasis).2 ?_
    rintro V ⟨hVB, hxV⟩
    rcases hB.exists_closure_subset (hB.mem_nhds hVB hxV) with ⟨U, hUB, hxU, hUV⟩
    set UV : ↥s := ⟨(U, V), ⟨hUB, hVB⟩, hUV⟩
    refine ⟨ε UV, (ε01 UV).1, fun y (hy : dist (F y) (F x) < ε UV) => ?_⟩
    replace hy : dist (F y UV) (F x UV) < ε UV :=
      (BoundedContinuousFunction.dist_coe_le_dist _).trans_lt hy
    contrapose! hy
    rw [hF, hF, hfε UV hy, hf0 UV hxU, Pi.zero_apply, dist_zero_right]
    exact le_abs_self _

/-- *Urysohn's metrization theorem* (Tychonoff's version):
a regular topological space with second countable topology `X` is metrizable,
i.e., there exists a pseudometric space structure that generates the same topology. -/
instance (priority := 90) PseudoMetrizableSpace.of_regularSpace_secondCountableTopology :
    PseudoMetrizableSpace X :=
  let ⟨_, hf⟩ := exists_isInducing_l_infty X
  hf.pseudoMetrizableSpace

end RegularSpace

variable (X : Type*) [TopologicalSpace X] [T3Space X] [SecondCountableTopology X]

/-- A T₃ topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`. -/
theorem exists_embedding_l_infty : ∃ f : X → ℕ →ᵇ ℝ, IsEmbedding f :=
  let ⟨f, hf⟩ := exists_isInducing_l_infty X; ⟨f, hf.isEmbedding⟩

/-- *Urysohn's metrization theorem* (Tychonoff's version): a T₃ topological space with second
countable topology `X` is metrizable, i.e., there exists a metric space structure that generates the
same topology. -/
instance (priority := 90) metrizableSpace_of_t3_secondCountable : MetrizableSpace X :=
  let ⟨_, hf⟩ := exists_embedding_l_infty X
  hf.metrizableSpace

end TopologicalSpace
