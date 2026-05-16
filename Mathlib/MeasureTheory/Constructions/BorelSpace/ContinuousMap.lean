/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion, Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Topology.CompactOpen

import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# A measurable space structure on the type of continuous maps

In this file we endow the type `C(X, Y)` of continuous maps from `X` to `Y` with the Borel
sigma-algebra coming from the compact-open topology. We show that, under some assumptions on
`X` and `Y`, this is equal to the restriction of the product sigma-algebra over `X → Y`. This
means that a function `g : Z → C(X, Y)` is measurable if and only if, for all `x : X`,
`z ↦ g z x` is measurable. We then use this to build a measurable equivalence between
`{f : X → Y // Continuous f}` and `C(X, Y)`.

## Main definition

* `MeasurableEquiv.continuousMap X Y`: A measurable equivalence between
  `{f : X → Y // Continuous f}` and `C(X, Y)`.

## Main statements

* `borel_eq_iSup_comap_eval`: The sigma-algebra over `C(X, Y)` is the coarsest that makes
  the maps `f ↦ f x` measurable for all `x : X`.
* `measurable_iff_eval`: A function `g : Z → C(X, Y)` is measurable if and only if,
  for all `x : X`, `z ↦ g z x` is measurable.

## References

* <https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr>

## Tags

continuous map, sigma-algebra
-/

@[expose] public section

open MeasurableSpace TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

instance ContinuousMap.measurableSpace : MeasurableSpace C(X, Y) := borel _

instance ContinuousMap.borelSpace : BorelSpace C(X, Y) where
  measurable_eq := rfl

/-- The coarsest sigma-algebra over `C(X, Y)` making the evaluation maps `f ↦ f x` is
smaller than the Borel sigma-algebra coming from the compact-open topology. -/
lemma ContinuousMap.iSup_comap_le_borel [MeasurableSpace Y] [BorelSpace Y] :
    ⨆ x : X, (borel Y).comap (fun f ↦ f x) ≤ borel C(X, Y) := by
  refine iSup_le fun x ↦ ?_
  rw [← measurable_iff_comap_le, ← BorelSpace.measurable_eq, ← BorelSpace.measurable_eq]
  exact Continuous.measurable (by fun_prop)

lemma ContinuousMap.measurable_eval [MeasurableSpace Y] [BorelSpace Y] (x : X) :
    Measurable (fun f : C(X, Y) ↦ f x) := by
  refine .le iSup_comap_le_borel <| .le (le_iSup _ x) ?_
  rw [← BorelSpace.measurable_eq]
  exact comap_measurable _

variable [SecondCountableTopology X] [SecondCountableTopology Y]
  [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]

namespace ContinuousMap

/-- The sigma-algebra over `C(X, Y)` is the coarsest that makes the maps `f ↦ f x` measurable
for all `x : X`.

The proof follows the one presented on <https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr>. -/
theorem borel_eq_iSup_comap_eval :
    borel C(X, Y) = ⨆ x : X, (borel Y).comap fun f ↦ f x := by
  refine le_antisymm ?_ iSup_comap_le_borel
  -- Denote `M(K, U)` the set of functions `f` such that `Set.MapsTo f K U`. These form a
  -- basis for the compact-open topology when `K` is compact and `U` is open.
  -- Because `C(X, Y)` is second-countable, it suffices to prove that those sets are measurable.
  -- Let therefore `K` be a compact set of `X` and `U` an open set of `Y`.
  rw [borel_eq_generateFrom_of_subbasis compactOpen_eq]
  apply generateFrom_le
  rintro - ⟨K, hK, U, hU, rfl⟩
  obtain rfl | ⟨x, hx⟩ := U.eq_empty_or_nonempty
  · simp
  -- Consider `V` a countable basis of the topology on `Y` obtained by taking the finite unions
  -- of sets of `countableBasis Y`.
  let V := Set.sUnion '' {f : Set (Set Y) | f.Finite ∧ f ⊆ countableBasis Y}
  have hV : IsTopologicalBasis V := (isBasis_countableBasis Y).finite_sUnion
  have cV : V.Countable :=
    (Set.countable_setOf_finite_subset (countable_countableBasis Y)).image _
  -- Because `Y` is regular, we have `U = ⋃_{v ∈ V, closure v ⊆ U} v`.
  -- For any continuous `f` such that `f '' K ⊆ U`, because `K` is compact, `f '' K` is compact.
  -- Because the set `{v ∈ V, closure v ⊆ U}` is a directed set of open sets that covers `f '' K`,
  -- we deduce that there exists `v ∈ V` such that `f '' K ⊆ closure v`.
  have (f : C(X, Y)) (hf : K.MapsTo f U) : ∃ v ∈ V, closure v ⊆ U ∧ K.MapsTo f (closure v) := by
    simp_rw [Set.mapsTo_iff_image_subset] at hf ⊢
    rw [hV.open_eq_sUnion_of_closure_subset hU] at hf
    obtain ⟨b, ⟨hb1, hb2⟩, hb3⟩ : ∃ b ∈ {v | v ∈ V ∧ closure v ⊆ U}, f '' K ⊆ b := by
      refine (hK.image f.continuous).elim_directedOn_cover _
        (fun v hv ↦ hV.isOpen hv.1) hf ?_ ?_
      · rintro - ⟨⟨f, ⟨hf1, hf2⟩, rfl⟩, hf3⟩ - ⟨⟨g, ⟨hg1, hg2⟩, rfl⟩, hg3⟩
        exact ⟨⋃₀ (f ∪ g), ⟨⟨f ∪ g, ⟨hf1.union hg1, by grind⟩, rfl⟩,
          by simp_all [Set.sUnion_union]⟩, by grind, by grind⟩
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
      exact ⟨v, hv2, hv3⟩
    exact ⟨b, hb1, hb2, hb3.trans subset_closure⟩
  -- Therefore, we obtain that
  -- `M(K, U) = ⋃_{u ∈ V, closure u ⊆ U}, M(K, closure u)`.
  have : {f : C(X, Y) | K.MapsTo f U} =
      ⋃ u ∈ V, ⋃ (_ : closure u ⊆ U), {f : C(X, Y) | K.MapsTo f (closure u)} := by
    ext f
    simpa using ⟨by grind, fun ⟨u, hu1, hu2, hu3⟩ ↦ hu3.mono_right hu1⟩
  simp_rw [this]
  -- In particular, because `V` is countable, this is a countable union.
  -- To show measurability it is therefore enough to show the measurability of each term.
  refine .biUnion cV (fun v hv1 ↦ .iUnion (fun hv2 ↦ ?_))
  -- Consider now `v ∈ V` such that `closure v ⊆ U`.
  -- Consider `Q` a countable dense subset of `K`, which exists by second-countability assumption.
  obtain ⟨Q, cQ, hQ, dQ⟩ := exists_countable_dense_subset K
  -- Because `f` is continuous and `closure v` is closed and `Q` is dense in `K`, having
  -- `f '' K ⊆ closure v` is the same as `f '' Q ⊆ closure v`.
  have : {f : C(X, Y) | K.MapsTo f (closure v)} = {f : C(X, Y) | Q.MapsTo f (closure v)} := by
    ext f
    refine ⟨fun h ↦ h.mono_left hQ, fun h x hx ↦ ?_⟩
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff_seq_limit.1 <| dQ hx
    exact isClosed_closure.mem_of_tendsto ((f.continuous.tendsto x).comp hu2)
      (.of_forall fun n ↦ h (hu1 n))
  -- We can write `M(Q, closure v) = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (closure v)`.
  have : {f : C(X, Y) | K.MapsTo f (closure v)} = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (closure v) := by
    ext f
    rw [this, Set.mem_iInter₂]
    exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h x hx⟩
  rw [this]
  -- This is a countable intersection, so it suffices to prove that each term is measurable.
  -- Because `closure v` is closed, it is measurable, so it suffices to prove that
  -- for any `q ∈ Q`, `fun f ↦ f q` is measurable for the product σ-algebra.
  -- The latter is the coarsest σ-algebra which makes the maps `fun f ↦ f x` measurable,
  -- so we are done.
  refine .biInter cQ fun q hq ↦ .preimage measurableSet_closure (.le (le_iSup _ q) ?_)
  rw [BorelSpace.measurable_eq (α := Y)]
  exact comap_measurable _

lemma measurableSpace_eq_iSup_comap_eval :
    measurableSpace = ⨆ a : X, (inferInstance : MeasurableSpace Y).comap fun b ↦ b a := by
  simp_rw [BorelSpace.measurable_eq, borel_eq_iSup_comap_eval]

/-- A function `g : Z → C(X, Y)` is measurable if and only if,
for all `x : X`, `z ↦ g z x` is measurable. -/
lemma measurable_iff_eval {Z : Type*} [MeasurableSpace Z] {g : Z → C(X, Y)} :
    Measurable g ↔ ∀ (x : X), Measurable fun a ↦ g a x := by
  rw [measurableSpace_eq_iSup_comap_eval]
  simp_rw [measurable_iff_comap_le, comap_iSup, iSup_le_iff, comap_comp, Function.comp_def]

end ContinuousMap

namespace MeasurableEquiv

variable (X Y) in
/-- A measurable equivalence between `{f : X → Y // Continuous f}` and `C(X, Y)`. -/
def continuousMap : {f : X → Y // Continuous f} ≃ᵐ C(X, Y) where
  toFun f := ⟨f.1, f.2⟩
  invFun f := ⟨f, f.continuous⟩
  left_inv f := rfl
  right_inv f := rfl
  measurable_toFun :=
    ContinuousMap.measurable_iff_eval.2 fun x ↦ by simpa using measurable_subtype_coe.eval
  measurable_invFun :=
    .subtype_mk (measurable_pi_lambda _ fun _ ↦ Continuous.measurable (by fun_prop))

@[simp]
lemma continuousMap_apply (f : {g : X → Y // Continuous g}) :
    continuousMap X Y f = ⟨f.1, f.2⟩ := rfl

@[simp]
lemma symm_continuousMap_apply (f : C(X, Y)) :
    (continuousMap X Y).symm f = ⟨f, f.continuous⟩ := rfl

lemma continuousMap_apply_apply (f : {g : X → Y // Continuous g}) (x : X) :
    continuousMap X Y f x = f.1 x := rfl

lemma symm_continuousMap_apply_apply (f : C(X, Y)) (x : X) :
    ((continuousMap X Y).symm f).1 x = f x := rfl

end MeasurableEquiv
