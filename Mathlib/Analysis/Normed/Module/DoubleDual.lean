/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Michał Świętek
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# The double dual of a normed space

In this file we define the inclusion of a normed space into its double strong dual,
prove that it is an isometry (for `𝕜 = ℝ` or `𝕜 = ℂ`), and use the corresponding weak-topology
embedding together with Banach–Alaoglu to transfer compactness from the weak-star bidual back to
the weak topology.

## Main definitions

* `NormedSpace.inclusionInDoubleDual` is the inclusion of a normed space in its double
  `StrongDual`, considered as a bounded linear map.
* `NormedSpace.inclusionInDoubleDualLi` is the same map as a linear isometry (for `𝕜 = ℝ` or
  `𝕜 = ℂ`).
* `NormedSpace.inclusionInDoubleDualWeak` is the map from the weak space into the weak-star bidual,
  as a continuous linear map.
* `NormedSpace.isEmbedding_inclusionInDoubleDualWeak` shows that `inclusionInDoubleDualWeak` is
  a topological embedding.
* `NormedSpace.isCompact_closure_of_isBounded` transfers compactness from the weak-star topology
  on the bidual back to the weak topology on `X`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

double dual, inclusion, isometry, embedding, weak-star topology
-/

@[expose] public section

noncomputable section

open Topology Bornology WeakDual

universe u v

namespace NormedSpace

section inclusionInDoubleDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The inclusion of a normed space in its double (topological) strong dual, considered
as a bounded linear map. -/
def inclusionInDoubleDual : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  ContinuousLinearMap.apply 𝕜 𝕜

@[simp]
theorem dual_def (x : E) (f : StrongDual 𝕜 E) : inclusionInDoubleDual 𝕜 E x f = f x :=
  rfl

theorem inclusionInDoubleDual_norm_eq :
    ‖inclusionInDoubleDual 𝕜 E‖ = ‖ContinuousLinearMap.id 𝕜 (StrongDual 𝕜 E)‖ :=
  ContinuousLinearMap.opNorm_flip _

theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ ≤ 1 := by
  rw [inclusionInDoubleDual_norm_eq]
  exact ContinuousLinearMap.norm_id_le

theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ ≤ ‖x‖ := by
  simpa using ContinuousLinearMap.le_of_opNorm_le _ (inclusionInDoubleDual_norm_le 𝕜 E) x

end inclusionInDoubleDual

section BidualIsometry

variable (𝕜 : Type v) [RCLike 𝕜] {E : Type u}

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The inclusion of a normed space in its double strong dual is an isometry onto its image. -/
def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E) :=
  { inclusionInDoubleDual 𝕜 E with
    norm_map' x := by
      apply le_antisymm (double_dual_bound 𝕜 E x)
      obtain ⟨g, hg⟩ := exists_dual_vector'' 𝕜 x
      grw [← (inclusionInDoubleDual 𝕜 E x).unit_le_opNorm g hg.left]
      simp [hg.right] }

/-- If one controls the norm of every `f x`, then one controls the norm of `x`.
Compare `ContinuousLinearMap.opNorm_le_bound`. -/
theorem norm_le_dual_bound (x : E) {M : ℝ} (hMp : 0 ≤ M)
    (hM : ∀ f : StrongDual 𝕜 E, ‖f x‖ ≤ M * ‖f‖) : ‖x‖ ≤ M := by
  rw [← (inclusionInDoubleDualLi (E := E) 𝕜).norm_map x]
  exact ContinuousLinearMap.opNorm_le_bound _ hMp hM

end Seminormed

end BidualIsometry

section Embedding

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (X : Type*) [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- The map from a normed space with the weak topology into the weak-star bidual, as a continuous
linear map. Built using `LinearEquiv.arrowCongr` to properly bundle the topology changes via
`toWeakSpace` and `StrongDual.toWeakDual`. -/
@[simps! -isSimp apply apply_apply]
def inclusionInDoubleDualWeak : WeakSpace 𝕜 X →L[𝕜] WeakDual 𝕜 (StrongDual 𝕜 X) where
  toLinearMap := (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual
    (inclusionInDoubleDual 𝕜 X).toLinearMap
  cont := Topology.IsInducing.continuous ⟨Eq.symm induced_compose⟩

attribute [simp] inclusionInDoubleDualWeak_apply_apply

@[simp]
lemma toLinearMap_inclusionInDoubleDualWeak :
    (inclusionInDoubleDualWeak 𝕜 X).toLinearMap =
      (toWeakSpace 𝕜 X).arrowCongr StrongDual.toWeakDual (inclusionInDoubleDual 𝕜 X).toLinearMap :=
  rfl

variable (𝕜 : Type*) [RCLike 𝕜] (X : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- `inclusionInDoubleDualWeak` is a topological embedding from the weak topology to the weak-star
topology. -/
theorem isEmbedding_inclusionInDoubleDualWeak :
    IsEmbedding (inclusionInDoubleDualWeak 𝕜 X) where
  eq_induced := Eq.symm induced_compose
  injective := StrongDual.toWeakDual.injective.comp
    (inclusionInDoubleDualLi (𝕜 := 𝕜) (E := X)).injective

/-- If `S` is bounded set in `WeakSpace X` and the weak-star closure of its image under
the embedding into the weak-star double dual lies in the range of that embedding,
then `closure S` is compact in the weak topology.

This combines Banach–Alaoglu (compactness of bounded weak-star–closed sets) with the topological
embedding `inclusionInDoubleDualWeak_isEmbedding` to transfer compactness back to the weak
topology on `X`. -/
theorem isCompact_closure_of_isBounded (S : Set (WeakSpace 𝕜 X))
    (hb : IsBounded ((toWeakSpace 𝕜 X) ⁻¹' S))
    (hrange : closure (inclusionInDoubleDualWeak 𝕜 X '' S) ⊆
      Set.range (inclusionInDoubleDualWeak 𝕜 X)) :
    IsCompact (closure S) := by
  rw [(isEmbedding_inclusionInDoubleDualWeak 𝕜 X).closure_eq_preimage_closure_image]
  apply (isEmbedding_inclusionInDoubleDualWeak 𝕜 X).isCompact_preimage' _ hrange
  exact WeakDual.isCompact_of_bounded_of_closed
    (WeakDual.isBounded_closure ((inclusionInDoubleDual 𝕜 X).lipschitz.isBounded_image hb))
    isClosed_closure

end Embedding

end NormedSpace
