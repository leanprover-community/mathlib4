/-
Copyright (c) 2023 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Order.Filter.Tendsto
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
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Closure
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Barrelled spaces and the Banach-Steinhaus theorem / Uniform Boundedness Principle

This file defines barrelled spaces over a `NontriviallyNormedField`, and proves the
Banach-Steinhaus theorem for maps from a barrelled space to a space equipped with a family
of seminorms generating the topology (i.e. `WithSeminorms q` for some family of seminorms `q`).

The more standard Banach-Steinhaus theorem for normed spaces is then deduced from that in
`Mathlib/Analysis/Normed/Operator/BanachSteinhaus.lean`.

## Main definitions

* `BarrelledSpace`: a topological vector space `E` is said to be **barrelled** if all lower
  semicontinuous seminorms on `E` are actually continuous. See the implementation details below for
  more comments on this definition.
* `continuousLinearMapOfTendsto`: fix `E` a barrelled space and `F` a `PolynormableSpace`.
  Given a sequence of continuous linear maps from `E` to `F` that converges pointwise to a
  function `f : E → F`, this bundles `f` as a continuous linear map using the
  Banach-Steinhaus theorem.

## Main theorems

* `BaireSpace.instBarrelledSpace`: any TVS that is also a `BaireSpace` is barrelled. In
  particular, this applies to Banach spaces and Fréchet spaces.
* `WithSeminorms.banach_steinhaus`: the **Banach-Steinhaus** theorem, also called
  **Uniform Boundedness Principle**. Fix `E` a barrelled space and `F` a TVS satisfying
  `WithSeminorms q` for some `q`. Any family `𝓕 : ι → E →L[𝕜] F` of continuous linear maps
  that is pointwise bounded is (uniformly) equicontinuous. Here, pointwise bounded means that
  for all `k` and `x`, the family of real numbers `i ↦ q k (𝓕 i x)` is bounded above.
* `PolynormableSpace.banach_steinhaus`: a version of the above which does not make reference
  to a fixed seminorm family. Fix `E` a barrelled space and `F` a `PolynormableSpace`.
  Any family `𝓕 : ι → E →L[𝕜] F` of continuous linear maps that is pointwise von Neumann bounded
  is (uniformly) equicontinuous.

## Implementation details

Barrelled spaces are defined in Bourbaki as locally convex spaces where barrels (aka closed
balanced absorbing convex sets) are neighborhoods of zero. One can then show that barrels in a
locally convex space are exactly closed unit balls of lower semicontinuous seminorms, hence that a
locally convex space is barrelled iff any lower semicontinuous seminorm is continuous.

The problem with this definition is the local convexity, which is essential to prove that the
barrel definition is equivalent to the seminorm definition, because we can essentially only
use `LocallyConvexSpace` over `ℝ` or `ℂ` (which is indeed the setup in which Bourbaki does most
of the theory). Since we can easily prove the normed space version over any
`NontriviallyNormedField`, this wouldn't make for a very satisfying "generalization".

Fortunately, it turns out that using the seminorm definition directly solves all problems,
since it is exactly what we need for the proof. One could then expect to need the barrel
characterization to prove that Baire TVS are barrelled, but the proof is actually easier to do
with the seminorm characterization!

## TODO

* define barrels and prove that a locally convex space is barrelled iff all barrels are
  neighborhoods of zero.

## References

* [N. Bourbaki, *Topological Vector Spaces*][bourbaki1987]

## Tags

banach-steinhaus, uniform boundedness, equicontinuity
-/

@[expose] public section

open Filter Topology Set ContinuousLinearMap

section defs

/-- A topological vector space `E` is said to be **barrelled** if all lower semicontinuous
seminorms on `E` are actually continuous. This is not the usual definition for TVS over `ℝ` or `ℂ`,
but this has the big advantage of working and giving sensible results over *any*
`NontriviallyNormedField`. In particular, the Banach-Steinhaus theorem holds for maps between such
a space and any space whose topology is generated by a family of seminorms. -/
class BarrelledSpace (𝕜 E : Type*) [SeminormedRing 𝕜] [AddGroup E] [SMul 𝕜 E]
    [TopologicalSpace E] : Prop where
  /-- In a barrelled space, all lower semicontinuous seminorms on `E` are actually continuous. -/
  continuous_of_lowerSemicontinuous : ∀ p : Seminorm 𝕜 E, LowerSemicontinuous p → Continuous p

theorem Seminorm.continuous_of_lowerSemicontinuous {𝕜 E : Type*} [AddGroup E] [SMul 𝕜 E]
    [SeminormedRing 𝕜] [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : Seminorm 𝕜 E)
    (hp : LowerSemicontinuous p) : Continuous p :=
  BarrelledSpace.continuous_of_lowerSemicontinuous p hp

theorem Seminorm.continuous_iSup
    {ι : Sort*} {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [BarrelledSpace 𝕜 E] (p : ι → Seminorm 𝕜 E)
    (hp : ∀ i, Continuous (p i)) (bdd : BddAbove (range p)) :
    Continuous (⨆ i, p i) := by
  rw [← Seminorm.coe_iSup_eq bdd]
  refine Seminorm.continuous_of_lowerSemicontinuous _ ?_
  rw [Seminorm.coe_iSup_eq bdd]
  rw [Seminorm.bddAbove_range_iff] at bdd
  convert lowerSemicontinuous_ciSup (f := fun i x ↦ p i x) bdd (fun i ↦ (hp i).lowerSemicontinuous)
  exact iSup_apply

end defs

section TVS_anyField

variable {α ι κ 𝕜₁ 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜₁]
    [NontriviallyNormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂]
    [AddCommGroup E] [AddCommGroup F] [Module 𝕜₁ E] [Module 𝕜₂ F]

/-- Any TVS over a `NontriviallyNormedField` that is also a Baire space is barrelled. In
particular, this applies to Banach spaces and Fréchet spaces. -/
instance BaireSpace.instBarrelledSpace [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜₁ E] [BaireSpace E] :
    BarrelledSpace 𝕜₁ E where
  continuous_of_lowerSemicontinuous := by
    -- Let `p` be a lower-semicontinuous seminorm on `E`.
    intro p hp
    -- Consider the family of all `p`-closed-balls with integer radius.
    -- By lower semicontinuity, each of these closed balls is indeed closed...
    have h₁ : ∀ n : ℕ, IsClosed (p.closedBall (0 : E) n) := fun n ↦ by
      simpa [p.closedBall_zero_eq] using hp.isClosed_preimage n
    -- ... and clearly they cover the whole space.
    have h₂ : (⋃ n : ℕ, p.closedBall (0 : E) n) = univ :=
      eq_univ_of_forall fun x ↦ mem_iUnion.mpr (exists_nat_ge <| p (x - 0))
    -- Hence, one of them has nonempty interior. Let `n : ℕ` be its radius, and fix `x` an
    -- interior point.
    rcases nonempty_interior_of_iUnion_of_closed h₁ h₂ with ⟨n, ⟨x, hxn⟩⟩
    -- To show that `p` is continuous, we will show that the `p`-closed-ball of
    -- radius `2*n` is a neighborhood of zero.
    refine Seminorm.continuous' (r := n + n) ?_
    rw [p.closedBall_zero_eq] at hxn ⊢
    have hxn' : p x ≤ n := by convert interior_subset hxn
    -- By definition, we have `p x' ≤ n` for `x'` sufficiently close to `x`.
    -- In other words, `p (x + y) ≤ n` for `y` sufficiently close to `0`.
    rw [mem_interior_iff_mem_nhds, ← map_add_left_nhds_zero] at hxn
    -- Hence, for `y` sufficiently close to `0`, we have
    -- `p y = p (x + y - x) ≤ p (x + y) + p x ≤ 2*n`
    filter_upwards [hxn] with y hy
    calc p y = p (x + y - x) := by rw [add_sub_cancel_left]
      _ ≤ p (x + y) + p x := map_sub_le_add _ _ _
      _ ≤ n + n := add_le_add hy hxn'

namespace WithSeminorms

variable [UniformSpace E] [UniformSpace F] [IsUniformAddGroup E] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E] {𝓕 : ι → E →SL[σ₁₂] F}
    {q : SeminormFamily 𝕜₂ F κ} (hq : WithSeminorms q)
include hq

/-- The **Banach-Steinhaus** theorem, or **Uniform Boundedness Principle**, for maps from a
barrelled space to any space whose topology is generated by a family of seminorms. Use
`WithSeminorms.equicontinuous_TFAE` and `Seminorm.bound_of_continuous` to get explicit bounds on
the seminorms from equicontinuity. -/
protected theorem banach_steinhaus (H : ∀ k x, BddAbove (range fun i ↦ q k (𝓕 i x))) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  -- We just have to prove that `⊔ i, (q k) ∘ (𝓕 i)` is a (well-defined) continuous seminorm
  -- for all `k`.
  refine (hq.uniformEquicontinuous_iff_bddAbove_and_continuous_iSup (toLinearMap ∘ 𝓕)).mpr ?_
  intro k
  -- By assumption the supremum `⊔ i, q k (𝓕 i x)` is well-defined for all `x`, hence the
  -- supremum `⊔ i, (q k) ∘ (𝓕 i)` is well defined in the lattice of seminorms.
  have : BddAbove (range fun i ↦ (q k).comp (𝓕 i).toLinearMap) := by
    rw [Seminorm.bddAbove_range_iff]
    exact H k
  -- By definition of the lattice structure on seminorms, `⊔ i, (q k) ∘ (𝓕 i)` is the *pointwise*
  -- supremum of the continuous seminorms `(q k) ∘ (𝓕 i)`. Since `E` is barrelled, this supremum
  -- is continuous.
  exact ⟨this, Seminorm.continuous_iSup _
    (fun i ↦ (hq.continuous_seminorm k).comp (𝓕 i).continuous) this⟩

end WithSeminorms

section PolynormableSpace

open Bornology

variable [UniformSpace E] [UniformSpace F] [IsUniformAddGroup E] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E] {𝓕 : ι → E →SL[σ₁₂] F} [PolynormableSpace 𝕜₂ F]

/-- The **Banach-Steinhaus** theorem, or **Uniform Boundedness Principle**, for maps from a
barrelled space to any polynormable space. -/
protected theorem PolynormableSpace.banach_steinhaus
    (H : ∀ x, IsVonNBounded 𝕜₂ (range fun i ↦ 𝓕 i x)) :
    UniformEquicontinuous ((↑) ∘ 𝓕) := by
  have hp := PolynormableSpace.withSeminorms 𝕜₂ F
  refine hp.banach_steinhaus ?_
  simp_rw [hp.isVonNBounded_iff_seminorm_bddAbove, ← range_comp] at H
  exact fun q x ↦ H x q

variable [ContinuousSMul 𝕜₂ F]

/-- Given a sequence of continuous linear maps which converges pointwise and for which the
domain is barrelled, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well.

This actually works for any *countably generated* filter instead of `atTop : Filter ℕ`,
but the proof ultimately goes back to sequences. -/
def continuousLinearMapOfTendsto
    [T2Space F] {l : Filter α} [l.IsCountablyGenerated]
    [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F} (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) :
    E →SL[σ₁₂] F where
  toLinearMap := linearMapOfTendsto _ _ h
  cont := by
    -- Since the filter `l` is countably generated and nontrivial, we can find a sequence
    -- `u : ℕ → α` that tends to `l`. By considering `g ∘ u` instead of `g`, we can thus assume
    -- that `α = ℕ` and `l = atTop`
    rcases l.exists_seq_tendsto with ⟨u, hu⟩
    -- We claim that the limit is continuous because it's a limit of an equicontinuous family.
    -- By the Banach-Steinhaus theorem, this equicontinuity will follow from pointwise boundedness.
    refine (h.comp hu).continuous_of_equicontinuous
      (PolynormableSpace.banach_steinhaus ?_).equicontinuous
    -- For `x` fixed, we need to show that the range of `(i : ℕ) ↦ g i x` is bounded.
    intro x
    -- This follows from the fact that this sequence converges (to `f x`) by hypothesis.
    rw [tendsto_pi_nhds] at h
    exact ((h x).comp hu).isVonNBounded_range 𝕜₂

end PolynormableSpace

section Deprecated

variable [UniformSpace E] [UniformSpace F] [IsUniformAddGroup E] [IsUniformAddGroup F]
    [ContinuousSMul 𝕜₁ E] [BarrelledSpace 𝕜₁ E] [ContinuousSMul 𝕜₂ F] {𝓕 : ι → E →SL[σ₁₂] F}
    {q : SeminormFamily 𝕜₂ F κ} (hq : WithSeminorms q)
include hq

/-- Given a sequence of continuous linear maps which converges pointwise and for which the
domain is barrelled, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well.

This actually works for any *countably generated* filter instead of `atTop : Filter ℕ`,
but the proof ultimately goes back to sequences. -/
@[deprecated continuousLinearMapOfTendsto (since := "2026-01-16")]
protected abbrev WithSeminorms.continuousLinearMapOfTendsto [T2Space F] {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F}
    (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) :
    E →SL[σ₁₂] F :=
  haveI : PolynormableSpace 𝕜₂ F := hq.toPolynormableSpace
  continuousLinearMapOfTendsto g h

end Deprecated

end TVS_anyField
