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

variable [SecondCountableTopology X] [SecondCountableTopology Y]
  [LocallyCompactSpace X] [RegularSpace Y] [MeasurableSpace Y] [BorelSpace Y]

namespace ContinuousMap

/-- The sigma-algebra over `C(X, Y)` is the coarsest that makes the maps `f ↦ f x` measurable
for all `x : X`.

The proof follows the one presented on <https://math.stackexchange.com/questions/4789531/when-does-the-borel-sigma-algebra-of-compact-convergence-coincide-with-the-pr>. -/
theorem borel_eq_iSup_comap_eval :
    borel C(X, Y) = ⨆ a : X, (borel Y).comap fun b ↦ b a := by
  apply le_antisymm
  swap
  · refine iSup_le fun x ↦ ?_
    simp_rw [← measurable_iff_comap_le]
    rw [← BorelSpace.measurable_eq, ← BorelSpace.measurable_eq]
    exact Continuous.measurable (by fun_prop)
  -- Denote `M(K, U)` the set of functions `f` such that `Set.MapsTo f K U`. These form a
  -- basis for the compact-open topology when `K` is compact and `U` is open.
  -- Because `C(X, Y)` is second-countable, it suffices to prove that those sets are measurable.
  -- Let therefore `K` be a compact set of `X` and `U` an open set of `Y`.
  rw [borel_eq_generateFrom_of_subbasis compactOpen_eq]
  refine generateFrom_le fun s hs ↦ ?_
  obtain ⟨K, hK, U, hU, rfl⟩ := hs
  -- Consider `V` a countable basis of the topology on Y.
  let V := countableBasis Y
  have hV : IsTopologicalBasis V := isBasis_countableBasis Y
  have cV : V.Countable := countable_countableBasis Y
  let W₁ := {v | v ∈ V ∧ closure v ⊆ U}
  -- Consider `W` the set of `closure v`, where `v ∈ V` and `closure v ⊆ U`.
  let W := {v | ∃ u ∈ V, v ⊆ U ∧ v = closure u}
  -- Because `V` is countable, so is `W`.
  have cW : W.Countable := by
    apply (cV.image closure).mono
    rintro - ⟨u, hu, -, rfl⟩
    exact ⟨u, hu, rfl⟩
  -- Because `Y` is regular, we can write that `U = ⋃_{v ∈ W} v`.
  have U_eq_sUnion_W : U = ⋃₀ W := by
    ext x
    rw [Set.mem_sUnion]
    constructor
    · intro hx
      obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ : ∃ v, (x ∈ v ∧ v ∈ V) ∧ closure v ⊆ U :=
        hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
      exact ⟨closure v, ⟨v, hv2, hv3, rfl⟩, subset_closure hv1⟩
    · rintro ⟨-, ⟨t, ht1, ht2, rfl⟩, hx⟩
      exact ht2 hx
  -- Similarly, we can write that `U = ⋃_{v ∈ V, closure v ⊆ U} v`.
  have U_eq_sUnion_W₁ : U = ⋃₀ W₁ := by
    ext x
    rw [Set.mem_sUnion]
    refine ⟨fun hx ↦ ?_, fun ⟨t, ⟨ht1, ht2⟩, hx⟩ ↦ ht2 <| subset_closure hx⟩
    obtain ⟨v, ⟨hv1, hv2⟩, hv3⟩ := hV.nhds_basis_closure x |>.mem_iff.1 <| hU.mem_nhds hx
    exact ⟨v, ⟨hv2, hv3⟩, hv1⟩
  -- For any continuous `f` such that `f '' K ⊆ U`, because `K` is compact, `f '' K` is compact.
  -- But we just proved that `U = ⋃_{v ∈ V, closure v ⊆ U} v`, and each `v ∈ V` is open,
  -- so there exists `J` a finite set of `v ∈ V` such that `closure v ⊆ U` and
  -- `f '' K ⊆ ⋃ v ∈ J, v`. We thus have `f '' K ⊆ ⋃ v ∈ J, closure v`. This is equivalent to
  -- having `I` a finite subset of `W` such that `f '' K ⊆ ⋃ v ∈ I, v`.
  have (f : C(X, Y)) (hf : K.MapsTo f U) : ∃ I, I.Finite ∧ I ⊆ W ∧ K.MapsTo f (⋃₀ I) := by
    simp_rw [Set.mapsTo_iff_image_subset] at hf ⊢
    rw [U_eq_sUnion_W₁, Set.sUnion_eq_biUnion] at hf
    have : ∀ i ∈ W₁, IsOpen i := fun x ⟨hx, _⟩ ↦ hV.isOpen hx
    obtain ⟨b, hb1, hb2, hb3⟩ := (hK.image f.continuous).elim_finite_subcover_image this hf
    refine ⟨closure '' b, hb2.image _, ?_, ?_⟩
    · rintro - ⟨v, hv, rfl⟩
      exact ⟨v, (hb1 hv).1, (hb1 hv).2, rfl⟩
    rw [← Set.sUnion_eq_biUnion] at hb3
    exact hb3.trans <| Set.sUnion_mono_subsets fun _ ↦ subset_closure
  -- Therefore, we obtain that
  -- `M(K, U) = ⋃_{I ⊆ W, I finite}, M(K, ⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f U} =
      ⋃₀ {v | ∃ I, I.Finite ∧ I ⊆ W ∧ v = {f : C(X, Y) | K.MapsTo f (⋃₀ I)}} := by
    ext f
    rw [Set.mem_sUnion]
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain ⟨I, hI1, hI2, hI3⟩ := this f h
      exact ⟨{f : C(X, Y) | K.MapsTo f (⋃₀ I)}, ⟨I, hI1, hI2, rfl⟩, hI3⟩
    · rintro ⟨-, ⟨I, hI1, hI2, rfl⟩, h⟩
      simp only [Set.mapsTo_iff_image_subset] at h ⊢
      rw [U_eq_sUnion_W]
      exact h.trans <| Set.sUnion_subset_sUnion hI2
  simp only
  rw [this]
  -- In particular, because `W` is countable, this is a countable union.
  -- To show measurability it is therefore enough to show the measurability of each term.
  apply MeasurableSet.sUnion
  · let f : Set (Set Y) → Set C(X, Y) := fun I ↦ {f : C(X, Y) | Set.MapsTo (⇑f) K (⋃₀ I)}
    refine ((Set.countable_setOf_finite_subset cW).image f).mono ?_
    rintro - ⟨I, hI1, hI2, rfl⟩
    exact ⟨I, ⟨hI1, hI2⟩, rfl⟩
  -- Consider now `I` a finite subset of `W`.
  rintro - ⟨I, hI1, hI2, rfl⟩
  -- First, `⋃ v ∈ I, v` is closed as a finite union of closed sets.
  have hI : IsClosed (⋃₀ I) := by
    refine hI1.isClosed_sUnion fun x hx ↦ ?_
    obtain ⟨u, -, -, rfl⟩ := hI2 hx
    exact isClosed_closure
  -- Consider `Q` a countable dense subset of `K`, which exists by second-countability assumption.
  obtain ⟨Q, cQ, dQ⟩ := exists_countable_dense K
  -- Because `f` is continuous and `⋃ v ∈ I, v` is closed and `Q` is dense in `K`, having
  -- `f '' K ⊆ ⋃ v ∈ I, v` is the same as `f '' Q ⊆ ⋃ v ∈ I, v`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      {f : C(X, Y) | (Subtype.val '' Q).MapsTo f (⋃₀ I)} := by
    ext f
    refine ⟨fun h x hx ↦ h (Subtype.coe_image_subset K Q hx), fun h x hx ↦ ?_⟩
    obtain ⟨u, hu1, hu2⟩ := mem_closure_iff_seq_limit.1 <| Subtype.dense_iff.1 dQ hx
    exact hI.mem_of_tendsto ((f.continuous.tendsto x).comp hu2)
      (Filter.Eventually.of_forall fun n ↦ h (hu1 n))
  -- We can write `M(Q, ⋃ v ∈ I, v) = ⋂ q ∈ Q, (fun f ↦ f q) ⁻¹' (⋃ v ∈ I, v)`.
  have : {f : C(X, Y) | K.MapsTo f (⋃₀ I)} =
      ⋂ q ∈ Subtype.val '' Q, (fun f ↦ f q) ⁻¹' (⋃₀ I) := by
    ext f
    rw [this, Set.mem_iInter₂]
    exact ⟨fun h x hx ↦ h hx, fun h x hx ↦ h x hx⟩
  rw [this]
  -- This is a countable intersection, so it suffices to prove that each term is measurable.
  -- Because `⋃ v ∈ I, v` is closed, it is measurable, so it suffices to prove that
  -- for any `q ∈ Q`, `fun f ↦ f q` is measurable for the product σ-algebra.
  -- The latter is the coarsest σ-algebra which makes the maps `fun f ↦ f x` measurable,
  -- so we are done.
  refine MeasurableSet.biInter (cQ.image _)
    fun q hq ↦ MeasurableSet.preimage hI.measurableSet (Measurable.le (le_iSup _ q) ?_)
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
