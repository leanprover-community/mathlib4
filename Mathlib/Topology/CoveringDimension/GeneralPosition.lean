/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-! # Finite families in affine general position -/

public section

open MeasureTheory

/-- Every positive-radius ball contains a point outside
the affine spans of all small subfamilies of a fixed finite family. -/
lemma exists_mem_ball_avoiding_small_affineSpans
    {ι : Type*} {N : ℕ} (z : ι → EuclideanSpace ℝ (Fin N))
    (s : Finset ι) (c : EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ Metric.ball c ε, ∀ u : Finset ι, u ⊆ s → u.card ≤ N → p ∉ affineSpan ℝ (u.image z) := by
  let candidates := s.powerset.filter fun u ↦ u.card ≤ N
  let forbidden : Set (EuclideanSpace ℝ (Fin N)) :=
    ⋃ u : candidates, (affineSpan ℝ (u.1.image z : Set (EuclideanSpace ℝ (Fin N))) : Set _)
  let μ : Measure (EuclideanSpace ℝ (Fin N)) :=
    (Module.finBasis ℝ (EuclideanSpace ℝ (Fin N))).addHaar
  -- Each candidate affine span is proper, hence Haar-null; the finite union is null.
  have hforbidden_zero : μ forbidden = 0 := by
    apply measure_iUnion_null
    intro u
    exact Measure.addHaar_affineSubspace μ _ <| by
      simpa only [Finset.coe_image] using
        affineSpan_image_ne_top_of_encard_le_finrank (p := z) ℝ u.1.finite_toSet
          (by simpa only [Set.encard_coe_eq_coe_finsetCard, finrank_euclideanSpace_fin,
            ENat.natCast_le_natCast] using (Finset.mem_filter.mp u.2).2)
  -- A positive-measure ball cannot be contained in the null forbidden union.
  have hnot_subset : ¬ Metric.ball c ε ⊆ forbidden := by
    intro hsubset
    have : μ (Metric.ball c ε) ≤ μ forbidden := measure_mono hsubset
    have := Metric.measure_ball_pos μ c hε
    grind
  obtain ⟨p, hp_ball, hp_forbidden⟩ := Set.not_subset.mp hnot_subset
  refine ⟨p, hp_ball, ?_⟩
  intro u hus hcard hp_span
  -- The candidate subtype witnesses that membership in this span implies
  -- membership in the whole forbidden union.
  apply hp_forbidden
  apply Set.mem_iUnion.mpr
  refine ⟨⟨u, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hus, hcard⟩⟩, hp_span⟩

open scoped Classical in
/-- Adjoining a fresh updated point outside the old
affine span preserves affine independence on the enlarged finset. -/
lemma affineIndependent_insert_update
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {z : ι → E} {s : Finset ι} {i : ι} {p : E}
    (hi : i ∉ s)
    (hs : AffineIndependent ℝ (fun j : {j // j ∈ s} ↦ z j.1))
    (hp : p ∉ affineSpan ℝ (Set.image z (s : Set ι))) :
    AffineIndependent ℝ
      (fun j : {j // j ∈ insert i s} ↦ Function.update z i p j.1) := by
  let inserted : {j // j ∈ insert i s} := ⟨i, Finset.mem_insert_self i s⟩
  have hmem (j : {j : {j // j ∈ insert i s} // j ≠ inserted}) : j.1.1 ∈ s :=
    (Finset.mem_insert.mp j.1.2).resolve_left fun h ↦ j.2 (Subtype.ext h)
  let old : {j : {j // j ∈ insert i s} // j ≠ inserted} ↪ {j // j ∈ s} :=
    ⟨fun j ↦ ⟨j.1.1, hmem j⟩, by grind [Function.Injective]⟩
  have hold : AffineIndependent ℝ
      (fun j : {j : {j // j ∈ insert i s} // j ≠ inserted} ↦
        Function.update z i p j.1.1) := by
    convert hs.comp_embedding old using 1
    ext j
    exact Function.update_of_ne (fun h : j.1.1 = i ↦ hi (h ▸ hmem j)) _ _
  apply hold.affineIndependent_of_notMem_span
  simp only [inserted, Function.update_self]
  exact fun h ↦ hp (affineSpan_mono ℝ (by grind [Function.update_of_ne]) h)

open scoped Classical in
/-- A finite Euclidean family admits a pointwise small
perturbation whose subfamilies of size at most the ambient dimension plus one
are affinely independent. -/
lemma existsNearbyBoundedAffineIndependentFamily
    {ι : Type*} [Finite ι] {N : ℕ}
    (v : ι → EuclideanSpace ℝ (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ z : ι → EuclideanSpace ℝ (Fin N),
      (∀ i, dist (z i) (v i) < ε) ∧
      ∀ t : Finset ι, t.card ≤ N + 1 →
        AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1) := by
  let _ := Fintype.ofFinite ι
  -- Induct over processed indices while retaining a total family, pointwise
  -- closeness on the processed set, and general position for every subfinset.
  have invariant : ∀ s : Finset ι,
      ∃ z : ι → EuclideanSpace ℝ (Fin N),
        (∀ i ∈ s, dist (z i) (v i) < ε) ∧
        ∀ t : Finset ι, t ⊆ s → t.card ≤ N + 1 →
          AffineIndependent ℝ (fun i : {i // i ∈ t} ↦ z i.1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        refine ⟨v, by simp, ?_⟩
        intro t ht _
        obtain rfl := Finset.subset_empty.mp ht
        exact affineIndependent_of_subsingleton ℝ _
    | @insert i s hi ih =>
        obtain ⟨z, hz_close, hz_independent⟩ := ih
        obtain ⟨p, hp_ball, hp_avoid⟩ :=
          exists_mem_ball_avoiding_small_affineSpans z s (v i) hε
        let z' : ι → EuclideanSpace ℝ (Fin N) := Function.update z i p
        refine ⟨z', ?_, ?_⟩
        · intro j hj
          grind [Function.update_apply, Metric.mem_ball]
        · intro t ht hcard
          by_cases hit : i ∈ t
          · let u := t.erase i
            have hu_subset : u ⊆ s := by grind
            have hu_card_add_one : u.card + 1 = t.card := Finset.card_erase_add_one hit
            have hu_card : u.card ≤ N := by omega
            have hu_independent := hz_independent u hu_subset (by omega)
            have hp_span : p ∉ affineSpan ℝ (Set.image z (u : Set ι)) := by
              simpa only [Finset.coe_image] using hp_avoid u hu_subset hu_card
            have hinsert := affineIndependent_insert_update
              (Finset.notMem_erase i t) hu_independent hp_span
            have ht_eq : insert i u = t := Finset.insert_erase hit
            rw [← ht_eq]
            simpa [z', u] using hinsert
          · have ht_subset : t ⊆ s := by grind
            have ht_independent := hz_independent t ht_subset hcard
            convert ht_independent using 1
            ext j
            simp only [z']
            rw [Function.update_of_ne]
            exact fun h ↦ hit (h ▸ j.2)
  obtain ⟨z, hz_close, hz_independent⟩ := invariant Finset.univ
  refine ⟨z, ?_, ?_⟩
  · intro i
    exact hz_close i (Finset.mem_univ i)
  · intro t hcard
    exact hz_independent t (Finset.subset_univ t) hcard

end
