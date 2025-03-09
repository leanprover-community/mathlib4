/-
Copyright (c) 2024 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Newell Jensen
-/
import Mathlib.Topology.MetricSpace.Congruence

/-!
# Similarities

This file defines `Similarity`, i.e., the equivalence between sets of points in a metric space
where all corresponding pairwise distances have the same ratio. The motivating example are
triangles in the plane.

## Implementation notes

For more details see the [Zulip discussion](https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Euclidean.20Geometry).

## Notation

* `(v₁ ∼ v₂ : Prop)` represents that `(v₁ : ι → P₁)` and `(v₂ : ι → P₂)` are similar.
-/

variable {ι ι' : Type*} {P₁ P₂ P₃ : Type*} {v₁ : ι → P₁} {v₂ : ι → P₂} {v₃ : ι → P₃}

noncomputable section

/-- Similarity between indexed sets of vertices v₁ and v₂.
Use `open scoped Similarity` to access the `v₁ ∼ v₂` notation. -/

def Similarity (v₁ : ι → P₁) (v₂ : ι → P₂)
    [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] : Prop :=
  ∃ r : NNReal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) = r * edist (v₂ i₁) (v₂ i₂))

@[inherit_doc]
scoped[Similarity] infixl:25 " ∼ " => Similarity

/-- Similarity holds if and only if and only if all extended distances are proportional. -/
lemma similarity_iff_exists_edist_eq [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] :
    Similarity v₁ v₂ ↔ (∃ r : NNReal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂))) :=
  refl _

/-- Similarity holds if and only if all non-negative distances are proportional. -/
lemma similarity_iff_exists_nndist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂] :
    Similarity v₁ v₂ ↔ (∃ r : NNReal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (nndist (v₁ i₁) (v₁ i₂) =
      r * nndist (v₂ i₁) (v₂ i₂))) :=
  exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
  fun _ _ => by { rw [edist_nndist, edist_nndist]; norm_cast }

/-- Similarity holds if and only if all distances are proportional. -/
lemma similarity_iff_exists_dist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂] :
    Similarity v₁ v₂ ↔ (∃ r : NNReal, r ≠ 0 ∧ ∀ (i₁ i₂ : ι), (dist (v₁ i₁) (v₁ i₂) =
      r * dist (v₂ i₁) (v₂ i₂))) :=
  similarity_iff_exists_nndist_eq.trans
  (exists_congr <| fun _ => and_congr Iff.rfl <| forall₂_congr <|
    fun _ _ => by { rw [dist_nndist, dist_nndist]; norm_cast })

lemma Congruent.similarity [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] {v₁ : ι → P₁}
    {v₂ : ι → P₂} (h : Congruent v₁ v₂) : Similarity v₁ v₂ :=
  ⟨1, one_ne_zero, fun i₁ i₂ ↦ by simpa using h i₁ i₂⟩

namespace Similarity

/-- Similarity preserves extended distance. -/
alias ⟨exists_edist_eq, _⟩ := similarity_iff_exists_edist_eq

/-- Similarity follows from preserved extended distance. -/
alias ⟨_, of_exists_edist_eq⟩ := similarity_iff_exists_edist_eq

/-- Similarity preserves non-negative distance. -/
alias ⟨exists_nndist_eq, _⟩ := similarity_iff_exists_nndist_eq

/-- Similarity follows from preserved non-negative distance. -/
alias ⟨_, of_exists_nndist_eq⟩ := similarity_iff_exists_nndist_eq

/-- Similarity preserves distance. -/
alias ⟨exists_dist_eq, _⟩ := similarity_iff_exists_dist_eq

/-- Similarity follows from preserved distance. -/
alias ⟨_, of_exists_dist_eq⟩ := similarity_iff_exists_dist_eq

/-- Similarity follows from pairwise preserved extended distance. -/
lemma of_pairwise_exists_edist_eq [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [DecidableEq ι]
    {r : NNReal} (hr : r ≠ 0) (h : Pairwise (fun i₁ i₂ => (edist (v₁ i₁) (v₁ i₂) =
      r * edist (v₂ i₁) (v₂ i₂)))) :
    v₁ ∼ v₂ :=
  ⟨r, hr, fun i₁ i₂ => if g : i₁ = i₂ then by { rw [g]; simp } else h g⟩

/-- Similarity follows from pairwise preserved non-negative distance. -/
lemma of_pairwise_exists_nndist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]
    [DecidableEq ι] {r : NNReal} (hr : r ≠ 0)
    (h : Pairwise (fun i₁ i₂ => (nndist (v₁ i₁) (v₁ i₂) = r * nndist (v₂ i₁) (v₂ i₂)))) :
    v₁ ∼ v₂ :=
  of_pairwise_exists_edist_eq hr (fun i₁ i₂ hn => by
    simp_rw [edist_nndist, h hn]
    norm_cast)

/-- Similarity follows from pairwise preserved distance. -/
lemma of_pairwise_exists_dist_eq [PseudoMetricSpace P₁] [PseudoMetricSpace P₂]
    [DecidableEq ι] {r : NNReal} (hr : r ≠ 0)
    (h : Pairwise (fun i₁ i₂ => dist (v₁ i₁) (v₁ i₂) = r * dist (v₂ i₁) (v₂ i₂))) :
    v₁ ∼ v₂ :=
  of_pairwise_exists_nndist_eq hr (fun i₁ i₂ hn => by
    have := h hn
    simp_rw [dist_nndist] at this
    norm_cast at this)


section PseudoEMetricSpace

variable [PseudoEMetricSpace P₁] [PseudoEMetricSpace P₂] [PseudoEMetricSpace P₃]

@[refl] protected lemma refl (v₁ : ι → P₁): v₁ ∼ v₁ :=
  ⟨1, one_ne_zero, fun _ _ => by {norm_cast; rw [one_mul]}⟩

@[symm] protected lemma symm (h : v₁ ∼ v₂) : v₂ ∼ v₁ := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r⁻¹, inv_ne_zero hr, fun _ _ => ?_⟩
  rw [ENNReal.coe_inv hr, ← ENNReal.div_eq_inv_mul, ENNReal.eq_div_iff _ ENNReal.coe_ne_top, h]
  norm_cast

lemma _root_.similarity_comm : v₁ ∼ v₂ ↔ v₂ ∼ v₁ := ⟨Similarity.symm, Similarity.symm⟩

@[trans] protected lemma trans (h₁ : v₁ ∼ v₂) (h₂ : v₂ ∼ v₃) : v₁ ∼ v₃ := by
  rcases h₁ with ⟨r₁, hr₁, h₁⟩; rcases h₂ with ⟨r₂, hr₂, h₂⟩
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, fun _ _ => ?_⟩
  rw [ENNReal.coe_mul, mul_assoc, h₁, h₂]

lemma index_map (h : v₁ ∼ v₂) (f : ι' → ι) : (v₁ ∘ f) ∼ (v₂ ∘ f) := by
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun _ _ => ?_⟩
  apply h

@[simp]
lemma index_equiv (f : ι' ≃ ι) (v₁ : ι → P₁) (v₂ : ι → P₂) :
    v₁ ∘ f ∼ v₂ ∘ f ↔ v₁ ∼ v₂ := by
  refine ⟨fun h => ?_, fun h => Similarity.index_map h f⟩
  rcases h with ⟨r, hr, h⟩
  refine ⟨r, hr, fun i₁ i₂ => ?_⟩
  simpa [f.right_inv i₁, f.right_inv i₂] using h (f.symm i₁) (f.symm i₂)

end PseudoEMetricSpace

end Similarity
