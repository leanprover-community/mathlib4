/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.Lift
import Mathlib.Order.Filter.Tendsto
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Neighborhoods

/-!
# Images of (von Neumann) bounded sets under continuous multilinear maps

In this file we prove that continuous multilinear maps
send von Neumann bounded sets to von Neumann bounded sets.

We prove 2 versions of the theorem:
one assumes that the index type is nonempty,
and the other assumes that the codomain is a topological vector space.

## Implementation notes

We do not assume the index type `ι` to be finite.
While for a nonzero continuous multilinear map
the family `∀ i, E i` has to be essentially finite
(more precisely, all but finitely many `E i` has to be trivial),
proving theorems without a `[Finite ι]` assumption saves us some typeclass searches here and there.
-/

public section

open Bornology Filter Set Function
open scoped Topology

namespace Bornology.IsVonNBounded

variable {ι 𝕜 F : Type*} {E : ι → Type*} [NormedField 𝕜]
  [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

/-- The image of a von Neumann bounded set under a continuous multilinear map
is von Neumann bounded.

This version does not assume that the topologies on the domain and on the codomain
agree with the vector space structure in any way
but it assumes that `ι` is nonempty.
-/
theorem image_multilinear' [Nonempty ι] {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s)
    (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s) := fun V hV ↦ by
  classical
  if h₁ : ∀ c : 𝕜, ‖c‖ ≤ 1 then
    exact absorbs_iff_norm.2 ⟨2, fun c hc ↦ by linarith [h₁ c]⟩
  else
    let _ : NontriviallyNormedField 𝕜 := ⟨by simpa using h₁⟩
    obtain ⟨I, t, ht₀, hft⟩ :
        ∃ (I : Finset ι) (t : ∀ i, Set (E i)), (∀ i, t i ∈ 𝓝 0) ∧ Set.pi I t ⊆ f ⁻¹' V := by
      have hfV : f ⁻¹' V ∈ 𝓝 0 := (map_continuous f).tendsto' _ _ f.map_zero hV
      rwa [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hfV
    have : ∀ i, ∃ c : 𝕜, c ≠ 0 ∧ ∀ c' : 𝕜, ‖c'‖ ≤ ‖c‖ → ∀ x ∈ s, c' • x i ∈ t i := fun i ↦ by
      rw [isVonNBounded_pi_iff] at hs
      have := (hs i).tendsto_smallSets_nhds.eventually (mem_lift' (ht₀ i))
      rcases NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff.1 this with ⟨r, hr₀, hr⟩
      rcases NormedField.exists_norm_lt 𝕜 hr₀ with ⟨c, hc₀, hc⟩
      refine ⟨c, norm_pos_iff.1 hc₀, fun c' hle x hx ↦ ?_⟩
      exact hr (hle.trans_lt hc) ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    choose c hc₀ hc using this
    rw [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV),
      NormedAddGroup.nhds_zero_basis_norm_lt.eventually_iff]
    have hc₀' : ∏ i ∈ I, c i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ hc₀ i
    refine ⟨‖∏ i ∈ I, c i‖, norm_pos_iff.2 hc₀', fun a ha ↦ mapsTo_image_iff.2 fun x hx ↦ ?_⟩
    let ⟨i₀⟩ := ‹Nonempty ι›
    set y := I.piecewise (fun i ↦ c i • x i) x
    calc
      f (update y i₀ ((a / ∏ i ∈ I, c i) • y i₀)) ∈ V := hft fun i hi => by
        rcases eq_or_ne i i₀ with rfl | hne
        · simp_rw [update_self, y, I.piecewise_eq_of_mem _ _ hi, smul_smul]
          refine hc _ _ ?_ _ hx
          calc
            ‖(a / ∏ i ∈ I, c i) * c i‖ ≤ (‖∏ i ∈ I, c i‖ / ‖∏ i ∈ I, c i‖) * ‖c i‖ := by
              rw [norm_mul, norm_div]; gcongr; exact ha.out.le
            _ ≤ 1 * ‖c i‖ := by gcongr; apply div_self_le_one
            _ = ‖c i‖ := one_mul _
        · simp_rw [update_of_ne hne, y, I.piecewise_eq_of_mem _ _ hi]
          exact hc _ _ le_rfl _ hx
      _ = a • f x := by
        rw [f.map_update_smul, update_eq_self, f.map_piecewise_smul, div_eq_mul_inv, mul_smul,
          inv_smul_smul₀ hc₀']

/-- The image of a von Neumann bounded set under a continuous multilinear map
is von Neumann bounded.

This version assumes that the codomain is a topological vector space.
-/
theorem image_multilinear [ContinuousSMul 𝕜 F] {s : Set (∀ i, E i)} (hs : IsVonNBounded 𝕜 s)
    (f : ContinuousMultilinearMap 𝕜 E F) : IsVonNBounded 𝕜 (f '' s) := by
  cases isEmpty_or_nonempty ι with
  | inl h =>
    exact (isBounded_iff_isVonNBounded _).1 <|
      @Set.Finite.isBounded _ (vonNBornology 𝕜 F) _ (s.toFinite.image _)
  | inr h => exact hs.image_multilinear' f

end IsVonNBounded

end Bornology
