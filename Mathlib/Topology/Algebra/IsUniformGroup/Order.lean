/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Topology.Algebra.IsUniformGroup.Defs
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# TendstoUniformlyOn on ordered spaces

We gather some results about `TendstoUniformlyOn f g K` on ordered spaces,
in particular bounding the values of `f` in terms of bounds on the limit `g`.

-/

open Filter Function Finset Topology

variable {α ι : Type*}

section order

variable {β : Type*} [UniformSpace β] [AddGroup β] [IsUniformAddGroup β] [PartialOrder β]
  [OrderTopology β] [AddLeftMono β] [AddRightMono β]

variable {f : ι → α → β} {g : α → β} {K : Set α} {p : Filter ι}

/-- If a sequence of functions converges uniformly on a set to a function `g` which is bounded above
by a value `u`, then the sequence is strictly bounded by any `v` such that `u < v`. -/
lemma TendstoUniformlyOn.eventually_forall_lt {u v : β} (huv : u < v)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x < v := by
  simp only [tendstoUniformlyOn_iff_tendsto, uniformity_eq_comap_neg_add_nhds_zero,
    tendsto_iff_eventually, eventually_comap, Prod.forall] at *
  conv at hf => enter [2]; rw [eventually_iff_exists_mem]
  have hf2 := hf (fun x ↦ -x.1 + x.2 < -u + v) ⟨_, (isOpen_gt' (-u + v)).mem_nhds (by simp [huv]),
    fun y hy a b hab ↦ (hab.symm ▸ hy :)⟩
  filter_upwards [eventually_prod_principal_iff.mp hf2] with i hi x hx
  simpa using add_lt_add_of_le_of_lt (hg x hx) (hi x hx)

lemma TendstoUniformlyOn.eventually_forall_le {u v : β} (huv : u < v)
    (hf : TendstoUniformlyOn f g p K) (hg : ∀ x ∈ K, g x ≤ u) :
    ∀ᶠ i in p, ∀ x ∈ K, f i x ≤ v := by
  filter_upwards [hf.eventually_forall_lt huv hg] with i hi x hx using (hi x hx).le

end order
