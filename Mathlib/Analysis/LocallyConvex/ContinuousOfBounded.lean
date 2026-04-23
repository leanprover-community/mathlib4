/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.GroupTheory.GroupAction.Pointwise
import Mathlib.Init
import Mathlib.Logic.Equiv.PartialEquiv
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.RingTheory.SimpleRing.Basic
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
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Continuity and Von Neumann boundedness

This file proves that for two topological vector spaces `E` and `F` over nontrivially normed fields,
if `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous
(this is `LinearMap.continuous_of_locally_bounded`).

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

@[expose] public section


open TopologicalSpace Bornology Filter Topology Pointwise

variable {𝕜 𝕜' E F : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
variable [AddCommGroup F] [TopologicalSpace F]

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [Module 𝕜 E] [ContinuousSMul 𝕜 E]
variable [NormedField 𝕜'] [Module 𝕜' F]
variable {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]

/-- Construct a continuous linear map from a linear map `f : E →ₛₗ[σ] F` and the existence of a
neighborhood of zero that gets mapped into a bounded set in `F`. -/
def LinearMap.clmOfExistsBoundedImage [IsTopologicalAddGroup F] (f : E →ₛₗ[σ] F)
    (h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)) : E →SL[σ] F :=
  ⟨f, by
    -- It suffices to show that `f` is continuous at `0`.
    refine continuous_of_continuousAt_zero f ?_
    rw [continuousAt_def, f.map_zero]
    intro U hU
    -- Continuity means that `U ∈ 𝓝 0` implies that `f ⁻¹' U ∈ 𝓝 0`.
    rcases h with ⟨V, hV, h⟩
    rcases (h hU).exists_pos with ⟨r, hr, h⟩
    rcases NormedField.exists_lt_norm 𝕜 r with ⟨x, hx⟩
    specialize h (σ x) (by simpa using hx.le)
    -- After unfolding all the definitions, we know that `f '' V ⊆ σ x • U`. We use this to show the
    -- inclusion `x⁻¹ • V ⊆ f⁻¹' U`.
    have x_ne := norm_pos_iff.mp (hr.trans hx)
    have : x⁻¹ • V ⊆ f ⁻¹' U :=
      calc
        x⁻¹ • V ⊆ x⁻¹ • f ⁻¹' (f '' V) := Set.smul_set_mono (Set.subset_preimage_image (⇑f) V)
        _ ⊆ x⁻¹ • f ⁻¹' (σ x • U) := Set.smul_set_mono (Set.preimage_mono h)
        _ = f ⁻¹' U := by rw [x_ne.isUnit.preimage_smul_setₛₗ _, inv_smul_smul₀ x_ne _]
    -- Using this inclusion, it suffices to show that `x⁻¹ • V` is in `𝓝 0`, which is trivial.
    grw [← this]
    rwa [set_smul_mem_nhds_zero_iff (inv_ne_zero x_ne)]⟩

theorem LinearMap.clmOfExistsBoundedImage_coe [IsTopologicalAddGroup F] {f : E →ₛₗ[σ] F}
    {h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)} :
    (f.clmOfExistsBoundedImage h : E →ₛₗ[σ] F) = f :=
  rfl

@[simp]
theorem LinearMap.clmOfExistsBoundedImage_apply [IsTopologicalAddGroup F] {f : E →ₛₗ[σ] F}
    {h : ∃ V ∈ 𝓝 (0 : E), Bornology.IsVonNBounded 𝕜' (f '' V)} {x : E} :
    f.clmOfExistsBoundedImage h x = f x :=
  rfl

variable [FirstCountableTopology E]

theorem LinearMap.continuousAt_zero_of_locally_bounded (f : E →ₛₗ[σ] F)
    (hf : ∀ s, IsVonNBounded 𝕜 s → IsVonNBounded 𝕜' (f '' s)) : ContinuousAt f 0 := by
  -- We pick `c : 𝕜` nonzero of norm `< 1`.
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one 𝕜
  have c_ne := norm_pos_iff.mp hc0
  -- We use a fast decreasing balanced basis for 0 : E, and reformulate continuity in terms of
  -- this basis
  rcases (nhds_basis_balanced 𝕜 E).exists_antitone_subbasis with ⟨b, bE1, bE⟩
  simp only [_root_.id] at bE
  have bE' : (𝓝 (0 : E)).HasBasis (fun _ ↦ True) (fun n : ℕ ↦ (c ^ n) • b n) := by
    refine bE.1.to_hasBasis' ?_ ?_
    · intro n _
      use n
      exact ⟨trivial, (bE1 n).2 _ (by grw [norm_pow, hc1, one_pow])⟩
    · intro n _
      simpa using smul_mem_nhds_smul₀ (pow_ne_zero n c_ne) (bE1 n).1
  simp_rw [ContinuousAt, map_zero, bE'.tendsto_left_iff, true_and, Set.MapsTo]
  -- Assume that f is not continuous at 0
  by_contra! h
  rcases h with ⟨V, hV, h⟩
  -- There exists `u : ℕ → E` such that for all `n : ℕ` we have `u n ∈ c ^ n • b n` and
  -- `f (u n) ∉ V`, with `V` some neighborhood of `0` in `F`.
  choose! u hu hu' using h
  -- The sequence `fun n ↦ c ^ (-n) • u n` converges to `0`
  have h_tendsto : Tendsto (fun n : ℕ => (c ^ n)⁻¹ • u n) atTop (𝓝 (0 : E)) := by
    apply bE.tendsto
    intro n
    simpa only [Set.mem_smul_set_iff_inv_smul_mem₀ (pow_ne_zero n c_ne)] using hu n
  -- The range of `fun n ↦ c ^ (-n) • u n` is von Neumann bounded
  have h_bounded : IsVonNBounded 𝕜 (Set.range fun n : ℕ => (c ^ n)⁻¹ • u n) :=
    h_tendsto.isVonNBounded_range 𝕜
  -- Hence, by assumption, the range of `fun n ↦ (σ c) ^ (-n) • f (u n)` is von Neumann bounded
  specialize hf _ h_bounded
  simp only [← Set.range_comp', LinearMap.map_smulₛₗ, map_inv₀, map_pow] at hf
  -- Since `fun n ↦ (σ c) ^ n` tends to zero, this implies that `f ∘ u` converges to zero.
  have : Tendsto (f ∘ u) atTop (𝓝 0) := by
    have : Tendsto (fun n ↦ σ c ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by simpa using hc1)
    have := hf.smul_tendsto_zero (.of_forall fun n ↦ Set.mem_range_self n) this
    exact this.congr fun n ↦ by simp [c_ne]
  -- But this is a contradiction.
  refine frequently_false (atTop : Filter ℕ) <| Eventually.frequently ?_
  filter_upwards [this.eventually_mem hV] using hu'

/-- If `E` is first countable, then every locally bounded linear map `E →ₛₗ[σ] F` is continuous. -/
theorem LinearMap.continuous_of_locally_bounded [IsTopologicalAddGroup F] (f : E →ₛₗ[σ] F)
    (hf : ∀ s, IsVonNBounded 𝕜 s → IsVonNBounded 𝕜' (f '' s)) : Continuous f :=
  continuous_of_continuousAt_zero f (f.continuousAt_zero_of_locally_bounded hf)

end NontriviallyNormedField
