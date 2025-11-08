/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.IsLUB

/-! ## Proper spaces

## Main definitions and results
* `ProperSpace α`: a `PseudoMetricSpace` where all closed balls are compact

* `isCompact_sphere`: any sphere in a proper space is compact.
* `proper_of_compact`: compact spaces are proper.
* `secondCountable_of_proper`: proper spaces are sigma-compact, hence second countable.
* `locallyCompact_of_proper`: proper spaces are locally compact.
* `pi_properSpace`: finite products of proper spaces are proper.

-/

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}

section ProperSpace

open Metric

/-- A pseudometric space is proper if all closed balls are compact. -/
class ProperSpace (α : Type u) [PseudoMetricSpace α] : Prop where
  isCompact_closedBall : ∀ x : α, ∀ r, IsCompact (closedBall x r)

export ProperSpace (isCompact_closedBall)

/-- In a proper pseudometric space, all spheres are compact. -/
theorem isCompact_sphere {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    IsCompact (sphere x r) :=
  (isCompact_closedBall x r).of_isClosed_subset isClosed_sphere sphere_subset_closedBall

/-- In a proper pseudometric space, any closed ball is a `CompactSpace` when considered as a
subtype. -/
instance {α : Type*} [PseudoMetricSpace α] [ProperSpace α] (x : α) (r : ℝ) :
    CompactSpace (closedBall x r) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

/-- In a proper pseudometric space, any sphere is a `CompactSpace` when considered as a subtype. -/
instance Metric.sphere.compactSpace {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    (x : α) (r : ℝ) : CompactSpace (sphere x r) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere _ _)

variable [PseudoMetricSpace α]

-- see Note [lower instance priority]
/-- A proper pseudo metric space is sigma compact, and therefore second countable. -/
instance (priority := 100) secondCountable_of_proper [ProperSpace α] :
    SecondCountableTopology α := by
  -- We already have `sigmaCompactSpace_of_locallyCompact_secondCountable`, so we don't
  -- add an instance for `SigmaCompactSpace`.
  suffices SigmaCompactSpace α from EMetric.secondCountable_of_sigmaCompact α
  rcases em (Nonempty α) with (⟨⟨x⟩⟩ | hn)
  · exact ⟨⟨fun n => closedBall x n, fun n => isCompact_closedBall _ _, iUnion_closedBall_nat _⟩⟩
  · exact ⟨⟨fun _ => ∅, fun _ => isCompact_empty, iUnion_eq_univ_iff.2 fun x => (hn ⟨x⟩).elim⟩⟩

/-- If all closed balls of large enough radius are compact, then the space is proper. Especially
useful when the lower bound for the radius is 0. -/
theorem ProperSpace.of_isCompact_closedBall_of_le (R : ℝ)
    (h : ∀ x : α, ∀ r, R ≤ r → IsCompact (closedBall x r)) : ProperSpace α :=
  ⟨fun x r => IsCompact.of_isClosed_subset (h x (max r R) (le_max_right _ _)) isClosed_closedBall
    (closedBall_subset_closedBall <| le_max_left _ _)⟩

/-- If there exists a sequence of compact closed balls with the same center
such that the radii tend to infinity, then the space is proper. -/
theorem ProperSpace.of_seq_closedBall {β : Type*} {l : Filter β} [NeBot l] {x : α} {r : β → ℝ}
    (hr : Tendsto r l atTop) (hc : ∀ᶠ i in l, IsCompact (closedBall x (r i))) :
    ProperSpace α where
  isCompact_closedBall a r :=
    let ⟨_i, hci, hir⟩ := (hc.and <| hr.eventually_ge_atTop <| r + dist a x).exists
    hci.of_isClosed_subset isClosed_closedBall <| closedBall_subset_closedBall' hir

-- A compact pseudometric space is proper
-- see Note [lower instance priority]
instance (priority := 100) proper_of_compact [CompactSpace α] : ProperSpace α :=
  ⟨fun _ _ => isClosed_closedBall.isCompact⟩

-- see Note [lower instance priority]
/-- A proper space is locally compact -/
instance (priority := 100) locallyCompact_of_proper [ProperSpace α] : LocallyCompactSpace α :=
  .of_hasBasis (fun _ => nhds_basis_closedBall) fun _ _ _ =>
    isCompact_closedBall _ _

-- see Note [lower instance priority]
/-- A proper space is complete -/
instance (priority := 100) complete_of_proper [ProperSpace α] : CompleteSpace α :=
  ⟨fun {f} hf => by
    /- We want to show that the Cauchy filter `f` is converging. It suffices to find a closed
      ball (therefore compact by properness) where it is nontrivial. -/
    obtain ⟨t, t_fset, ht⟩ : ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < 1 :=
      (Metric.cauchy_iff.1 hf).2 1 zero_lt_one
    rcases hf.1.nonempty_of_mem t_fset with ⟨x, xt⟩
    have : closedBall x 1 ∈ f := mem_of_superset t_fset fun y yt => (ht y yt x xt).le
    rcases (isCompact_iff_totallyBounded_isComplete.1 (isCompact_closedBall x 1)).2 f hf
        (le_principal_iff.2 this) with
      ⟨y, -, hy⟩
    exact ⟨y, hy⟩⟩

/-- A binary product of proper spaces is proper. -/
instance prod_properSpace {α : Type*} {β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [ProperSpace α] [ProperSpace β] : ProperSpace (α × β) where
  isCompact_closedBall := by
    rintro ⟨x, y⟩ r
    rw [← closedBall_prod_same x y]
    exact (isCompact_closedBall x r).prod (isCompact_closedBall y r)

/-- A finite product of proper spaces is proper. -/
instance pi_properSpace {X : β → Type*} [Fintype β] [∀ b, PseudoMetricSpace (X b)]
    [h : ∀ b, ProperSpace (X b)] : ProperSpace (∀ b, X b) := by
  refine .of_isCompact_closedBall_of_le 0 fun x r hr => ?_
  rw [closedBall_pi _ hr]
  exact isCompact_univ_pi fun _ => isCompact_closedBall _ _

/-- A closed subspace of a proper space is proper.
This is true for any proper lipschitz map. See `LipschitzWith.properSpace`. -/
lemma ProperSpace.of_isClosed {X : Type*} [PseudoMetricSpace X] [ProperSpace X]
    {s : Set X} (hs : IsClosed s) :
    ProperSpace s :=
  ⟨fun x r ↦ Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    ((isCompact_closedBall x.1 r).of_isClosed_subset
    (hs.isClosedMap_subtype_val _ isClosed_closedBall) (Set.image_subset_iff.mpr subset_rfl))⟩

end ProperSpace

instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Additive X) := ‹ProperSpace X›
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace (Multiplicative X) := ‹ProperSpace X›
instance [PseudoMetricSpace X] [ProperSpace X] : ProperSpace Xᵒᵈ := ‹ProperSpace X›
