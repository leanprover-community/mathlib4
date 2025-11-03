/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Mario Carneiro, Yury Kudryashov, Heather Macbeth
-/
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# The Arzelà–Ascoli theorem for bounded continuous functions

Arzelà–Ascoli asserts that, on a compact space, a set of functions sharing a common modulus of
continuity and taking values in a compact set forms a compact subset for the topology of
uniform convergence. This file proves the theorem and several useful variations around it.
-/

open Set Metric

universe u v

namespace BoundedContinuousFunction

variable {α : Type u} {β : Type v} [TopologicalSpace α] [CompactSpace α] [PseudoMetricSpace β]

/-- First version, with pointwise equicontinuity and range in a compact space. -/
theorem arzela_ascoli₁ [CompactSpace β] (A : Set (α →ᵇ β)) (closed : IsClosed A)
    (H : Equicontinuous ((↑) : A → α → β)) : IsCompact A := by
  simp_rw [Equicontinuous, Metric.equicontinuousAt_iff_pair] at H
  refine TotallyBounded.isCompact_of_isClosed ?_ closed
  refine totallyBounded_of_finite_discretization fun ε ε0 => ?_
  rcases exists_between ε0 with ⟨ε₁, ε₁0, εε₁⟩
  let ε₂ := ε₁ / 2 / 2
  /- We have to find a finite discretization of `u`, i.e., finite information
    that is sufficient to reconstruct `u` up to `ε`. This information will be
    provided by the values of `u` on a sufficiently dense set `tα`,
    slightly translated to fit in a finite `ε₂`-dense set `tβ` in the image. Such
    sets exist by compactness of the source and range. Then, to check that these
    data determine the function up to `ε`, one uses the control on the modulus of
    continuity to extend the closeness on tα to closeness everywhere. -/
  have ε₂0 : ε₂ > 0 := half_pos (half_pos ε₁0)
  have : ∀ x : α, ∃ U, x ∈ U ∧ IsOpen U ∧
      ∀ y ∈ U, ∀ z ∈ U, ∀ {f : α →ᵇ β}, f ∈ A → dist (f y) (f z) < ε₂ := fun x =>
    let ⟨U, nhdsU, hU⟩ := H x _ ε₂0
    let ⟨V, VU, openV, xV⟩ := _root_.mem_nhds_iff.1 nhdsU
    ⟨V, xV, openV, fun y hy z hz f hf => hU y (VU hy) z (VU hz) ⟨f, hf⟩⟩
  choose U hU using this
  /- For all `x`, the set `hU x` is an open set containing `x` on which the elements of `A`
    fluctuate by at most `ε₂`.
    We extract finitely many of these sets that cover the whole space, by compactness. -/
  obtain ⟨tα : Set α, _, hfin, htα : univ ⊆ ⋃ x ∈ tα, U x⟩ :=
    isCompact_univ.elim_finite_subcover_image (fun x _ => (hU x).2.1) fun x _ =>
      mem_biUnion (mem_univ _) (hU x).1
  rcases hfin.nonempty_fintype with ⟨_⟩
  obtain ⟨tβ : Set β, _, hfin, htβ : univ ⊆ ⋃ y ∈ tβ, ball y ε₂⟩ :=
    @finite_cover_balls_of_compact β _ _ isCompact_univ _ ε₂0
  rcases hfin.nonempty_fintype with ⟨_⟩
  -- Associate to every point `y` in the space a nearby point `F y` in `tβ`
  choose F hF using fun y => show ∃ z ∈ tβ, dist y z < ε₂ by simpa using htβ (mem_univ y)
  -- `F : β → β`, `hF : ∀ (y : β), F y ∈ tβ ∧ dist y (F y) < ε₂`
  /- Associate to every function a discrete approximation, mapping each point in `tα`
    to a point in `tβ` close to its true image by the function. -/
  classical
  refine ⟨tα → tβ, by infer_instance, fun f a => ⟨F (f.1 a), (hF (f.1 a)).1⟩, ?_⟩
  rintro ⟨f, hf⟩ ⟨g, hg⟩ f_eq_g
  -- If two functions have the same approximation, then they are within distance `ε`
  refine lt_of_le_of_lt ((dist_le <| le_of_lt ε₁0).2 fun x => ?_) εε₁
  obtain ⟨x', x'tα, hx'⟩ := mem_iUnion₂.1 (htα (mem_univ x))
  calc
    dist (f x) (g x) ≤ dist (f x) (f x') + dist (g x) (g x') + dist (f x') (g x') :=
      dist_triangle4_right _ _ _ _
    _ ≤ ε₂ + ε₂ + ε₁ / 2 := by
      refine le_of_lt (add_lt_add (add_lt_add ?_ ?_) ?_)
      · exact (hU x').2.2 _ hx' _ (hU x').1 hf
      · exact (hU x').2.2 _ hx' _ (hU x').1 hg
      · have F_f_g : F (f x') = F (g x') :=
          (congr_arg (fun f : tα → tβ => (f ⟨x', x'tα⟩ : β)) f_eq_g :)
        calc
          dist (f x') (g x') ≤ dist (f x') (F (f x')) + dist (g x') (F (f x')) :=
            dist_triangle_right _ _ _
          _ = dist (f x') (F (f x')) + dist (g x') (F (g x')) := by rw [F_f_g]
          _ < ε₂ + ε₂ := (add_lt_add (hF (f x')).2 (hF (g x')).2)
          _ = ε₁ / 2 := add_halves _
    _ = ε₁ := by rw [add_halves, add_halves]

/-- Second version, with pointwise equicontinuity and range in a compact subset. -/
theorem arzela_ascoli₂ (s : Set β) (hs : IsCompact s) (A : Set (α →ᵇ β)) (closed : IsClosed A)
    (in_s : ∀ (f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s) (H : Equicontinuous ((↑) : A → α → β)) :
    IsCompact A := by
  /- This version is deduced from the previous one by restricting to the compact type in the target,
  using compactness there and then lifting everything to the original space. -/
  have M : LipschitzWith 1 Subtype.val := LipschitzWith.subtype_val s
  let F : (α →ᵇ s) → α →ᵇ β := comp (↑) M
  refine IsCompact.of_isClosed_subset ((?_ : IsCompact (F ⁻¹' A)).image (continuous_comp M)) closed
      fun f hf => ?_
  · haveI : CompactSpace s := isCompact_iff_compactSpace.1 hs
    refine arzela_ascoli₁ _ (continuous_iff_isClosed.1 (continuous_comp M) _ closed) ?_
    rw [isUniformEmbedding_subtype_val.isUniformInducing.equicontinuous_iff]
    exact H.comp (A.restrictPreimage F)
  · let g := codRestrict s f fun x => in_s f x hf
    rw [show f = F g by ext; rfl] at hf ⊢
    exact ⟨g, hf, rfl⟩

/-- Third (main) version, with pointwise equicontinuity and range in a compact subset, but
without closedness. The closure is then compact. -/
theorem arzela_ascoli [T2Space β] (s : Set β) (hs : IsCompact s) (A : Set (α →ᵇ β))
    (in_s : ∀ (f : α →ᵇ β) (x : α), f ∈ A → f x ∈ s) (H : Equicontinuous ((↑) : A → α → β)) :
    IsCompact (closure A) :=
  /- This version is deduced from the previous one by checking that the closure of `A`, in
  addition to being closed, still satisfies the properties of compact range and equicontinuity. -/
  arzela_ascoli₂ s hs (closure A) isClosed_closure
    (fun _ x hf =>
      (mem_of_closed' hs.isClosed).2 fun ε ε0 =>
        let ⟨g, gA, dist_fg⟩ := Metric.mem_closure_iff.1 hf ε ε0
        ⟨g x, in_s g x gA, lt_of_le_of_lt (dist_coe_le_dist _) dist_fg⟩)
    (H.closure' continuous_coe)

end BoundedContinuousFunction
