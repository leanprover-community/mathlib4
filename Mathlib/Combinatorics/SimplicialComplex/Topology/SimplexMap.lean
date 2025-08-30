/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Combinatorics.SimplicialComplex.FacePoset
import Mathlib.Combinatorics.SimplicialComplex.Topology.Simplex
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Maps on standard simplices

Given a simplicial map `φ : X ⟶ Y` and a face `s` of `X`, we define a continuous map
`Simplex.map φ s : Simplex s.1 → Simplex (s.1.image φ.toFun)`. Concretely, the weights are
pushed forward along `φ` by summing the barycentric coordinates over the fibres `φ ⁻¹ {y}`.

This construction is the simplex-level ingredient for the induced map on geometric
realisations, and serves as the component of the natural transformation between the face
diagrams used to build `|X|` as a colimit.

## Main definitions

* `Simplex.map` : the continuous map between standard simplices induced by a simplicial map.

## Main results

* `Simplex.map_continuous` : the map `Simplex.map φ s` is continuous.
* `Simplex.map_naturality` : `Simplex.map` is natural with respect to face inclusions.
* `Simplex.supportFinset_map` : the support of `Simplex.map φ s p` is the image of the support
  of `p` under `φ`.

## Implementation notes

* Continuity is proved using `continuous_finset_sum` together with `continuous_apply`,
  after expressing each output coordinate as a finite sum of input coordinates.
* We index the push-forward by `s.1.filter (fun x ↦ φ.toFun x = y)`.
* Basic summation lemmas (`sum_congr`, `single_le_sum`, etc.) verify that the weights
  remain in `Set.Icc 0 1` and still sum to `1`.

## Tags

simplex, simplicial map, barycentric coordinates
-/

open Simplex SimplicialComplex Finset

variable {U V W : Type*} [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable {X : SimplicialComplex U} {Y : SimplicialComplex V} {Z : SimplicialComplex W}

namespace Simplex

omit [DecidableEq U] in
/-- A helper for continuity: for a fixed vertex `x : U`, the evaluation map
`p ↦ (p : U → ℝ) x` on `Simplex A` is continuous. -/
private lemma continuous_weight_eval {A : Finset U} (x : U) :
  Continuous (fun p : Simplex A => (p : U → ℝ) x) := by
  apply (continuous_apply x).comp
  exact continuous_induced_dom

/-- The continuous map on standard simplices induced by a simplicial map.

Given `φ : X ⟶ Y` and a face `s : X.faces`, `map φ s : Simplex s.1 → Simplex (s.1.image φ.toFun)`
pushes barycentric weights forward along the fibres of `φ.toFun`. -/
noncomputable def map (φ : Hom X Y) (s : X.faces) : Simplex s.1 → Simplex (s.1.image φ.toFun) := by
  intro p
  set B : Finset V := s.1.image φ.toFun with hB
  set w : V → ℝ :=
    fun y ↦ ∑ x ∈ s.1.filter (fun x ↦ φ.toFun x = y), p.weight x
    with hw

  /- `∑ y ∈ B, w y = 1` -/
  have h_sum : ∑ y ∈ B, w y = 1 := by
    calc
      _ = ∑ y ∈ B,
            ∑ x ∈ s.1.filter (fun x ↦ φ.toFun x = y), p.weight x := by
              simp [hw]
      _ = ∑ y ∈ B,
            ∑ x ∈ s.1, if φ.toFun x = y then p.weight x else 0 := by
              refine Finset.sum_congr rfl ?_
              intro y _
              simp [Finset.sum_filter]
      _ = ∑ x ∈ s.1,
            ∑ y ∈ B, if φ.toFun x = y then p.weight x else 0 := by
              simpa using
                Finset.sum_comm
                  (f := fun y (x : U) =>
                    if _ : φ.toFun x = y then p.weight x else 0)
                  (s := B) (t := s.1)
      _ = ∑ x ∈ s.1, p.weight x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              have : φ.toFun x ∈ B := by
                have : φ.toFun x ∈ s.1.image φ.toFun :=
                  Finset.mem_image_of_mem _ hx
                simpa [hB] using this
              simp [this]
      _ = 1 := p.sum_eq_one

  /- Support zero outside `B`. -/
  have h_support_zero : ∀ {y}, y ∉ B → w y = 0 := by
    intro y hyB
    have h_empty :
        (s.1.filter fun x : U ↦ φ.toFun x = y) = (∅ : Finset U) := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro x hx
      rcases Finset.mem_filter.1 hx with ⟨hx₁, hxy⟩
      have : (φ.toFun x) ∈ B := by
        have : φ.toFun x ∈ s.1.image φ.toFun :=
          Finset.mem_image_of_mem _ hx₁
        simpa [hB] using this
      have : y ∈ B := by simpa [hxy] using this
      exact (hyB this).elim
    dsimp [w] at *
    simp [h_empty] at *

  /- `w y ∈ [0,1]` for all `y`. -/
  have h_Icc : ∀ y, w y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    have h₀ : (0 : ℝ) ≤ w y := by
      dsimp [w]
      exact Finset.sum_nonneg fun _ _ ↦ (p.range_mem_Icc _).1
    have h₁ : w y ≤ 1 := by
      by_cases hy : y ∈ B
      · have h_nonneg : ∀ z ∈ B, (0 : ℝ) ≤ w z := by
          intro z hz
          dsimp [w]
          exact Finset.sum_nonneg fun _ _ ↦ (p.range_mem_Icc _).1
        have : w y ≤ ∑ z ∈ B, w z :=
          Finset.single_le_sum h_nonneg hy
        simpa [h_sum] using this
      · have : w y = 0 := h_support_zero hy
        simp [this]
    exact ⟨h₀, h₁⟩

  exact
    { weight         := w
      support_subset := by
        intro y hy
        have hyB : y ∉ B := by simpa [hB] using hy
        simpa using h_support_zero hyB
      sum_eq_one     := by simpa [hB] using h_sum
      range_mem_Icc  := by simpa [hB] using h_Icc }

omit [DecidableEq U] in
/-- Continuity of `Simplex.map`. -/
@[simp] lemma map_continuous (φ : Hom X Y) (s : X.faces) :
    Continuous (map (U := U) (V := V) φ s) := by
  have h_prod :
      Continuous (fun p : Simplex (U := U) s.1 ↦
        (map (U := U) (V := V) φ s p : V → ℝ)) := by
    refine continuous_pi ?_
    intro y
    have :
        Continuous (fun p : Simplex (U := U) s.1 ↦
          ∑ x ∈ s.1.filter (fun x : U ↦ φ.toFun x = y), (p : U → ℝ) x) := by
      apply continuous_finset_sum
      intro x hx
      exact continuous_weight_eval x
    simpa [map] using this
  simpa using (continuous_induced_rng.2 h_prod)

omit [DecidableEq U] in
/-- **Naturality of `Simplex.map` with respect to face inclusions.**

For a morphism `f : A ⟶ B` in the face poset, the diagram

Simplex A       ⟶      Simplex B
    |                      |
    |                      |
    v                      v
Simplex (φ(A))  ⟶     Simplex (φ(B))

commutes, where the horizontal arrows are the `simplexEmbedding`s and the vertical arrows
are `Simplex.map`. -/
lemma map_naturality (φ : Hom X Y) {A B : X.faces} (f : A ⟶ B)
  (p : Simplex (U := U) A.1) :
  map φ B (simplexEmbedding (hAB := f.down) p)
    =
  simplexEmbedding (hAB := ((φ.face_functor).map f).down) (map φ A p) := by
  ext y
  unfold map
  simp only [simplexEmbedding_apply]
  let P : U → Prop := fun x' => φ.toFun x' = y
  let s_A := A.1.filter P
  let s_B := B.1.filter P
  apply Eq.symm
  apply Finset.sum_subset
  · exact Finset.filter_subset_filter _ f.down
  · intro x hx_in_sB hx_not_in_sA
    have hx_not_in_A : x ∉ A.1 := by
      intro hx_in_A
      have Px_true : P x := (Finset.mem_filter.1 hx_in_sB).2
      have hx_in_sA : x ∈ s_A := Finset.mem_filter.2 ⟨hx_in_A, Px_true⟩
      exact hx_not_in_sA hx_in_sA
    exact p.support_subset hx_not_in_A

/-- The support of the image of a point under `Simplex.map` equals the image of the support. -/
@[simp] lemma supportFinset_map
  (φ : Hom X Y) (s : X.faces) (p : Simplex (U := U) s.1) :
  Simplex.supportFinset (Simplex.map (X := X) (Y := Y) φ s p)
    = (Simplex.supportFinset p).image φ.toFun := by
  ext y
  constructor
  · intro hy
    have hy0 :
        (Simplex.map (X := X) (Y := Y) φ s p : V → ℝ) y ≠ 0 := by
      simpa [Simplex.mem_supportFinset] using hy
    set S := s.1.filter (fun x : U => φ.toFun x = y)
    have hexists : ∃ x ∈ S, p.weight x ≠ 0 := by
      by_contra hnone
      have hzero : ∀ x ∈ S, p.weight x = 0 := by
        intro x hx; by_contra hxne; exact hnone ⟨x, hx, hxne⟩
      have hsum : (∑ x ∈ S, p.weight x) = 0 := Finset.sum_eq_zero hzero
      have : (Simplex.map (X := X) (Y := Y) φ s p : V → ℝ) y = 0 := by
        simpa [Simplex.map, S] using hsum
      exact hy0 this
    rcases hexists with ⟨x, hxS, hxne⟩
    exact Finset.mem_image.mpr
      ⟨x, (Simplex.mem_supportFinset p).2 hxne, (Finset.mem_filter.1 hxS).2⟩
  · intro hy
    rcases Finset.mem_image.1 hy with ⟨x, hxSupp, hxy⟩
    set S := s.1.filter (fun z : U => φ.toFun z = y)
    have hxA : x ∈ s.1 := (Finset.mem_filter.1 hxSupp).1
    have hxS : x ∈ S := by exact Finset.mem_filter.2 ⟨hxA, by simp [hxy]⟩
    have hxne : p.weight x ≠ 0 := (Simplex.mem_supportFinset p).1 hxSupp
    have hxpos : (0 : ℝ) < p.weight x := by
      have hx0 : (0 : ℝ) ≤ p.weight x := (p.range_mem_Icc x).1
      exact lt_of_le_of_ne' hx0 hxne
    have h_le :
        p.weight x ≤ ∑ z ∈ S, p.weight z :=
      Finset.single_le_sum (fun z _ => (p.range_mem_Icc z).1) hxS
    have hw_pos :
        (0 : ℝ) < (Simplex.map (X := X) (Y := Y) φ s p : V → ℝ) y :=
      lt_of_lt_of_le hxpos (by simpa [Simplex.map, S])
    exact (Simplex.mem_supportFinset _).2 (ne_of_gt hw_pos)

end Simplex
