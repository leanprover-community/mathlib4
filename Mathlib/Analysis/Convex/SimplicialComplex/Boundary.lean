import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.StdSimplex

/-!
# Boundary of simplicial complexes

This file defines the boundary of a simplicial complex restricted to a coordinate hyperplane.

## Main definitions

* `SimplicialComplex.boundary`: The boundary of a simplicial complex on the k-th coordinate hyperplane
-/

open Set Finset Function

namespace Geometry.SimplicialComplex

variable {m : ℕ}

/-- The projection that removes the k-th coordinate. -/
def proj (k : Fin (m + 1)) (x : Fin (m + 1) → ℝ) : Fin m → ℝ := x ∘ k.succAbove

/-- `proj k` as a linear map. -/
def proj_linear (k : Fin (m + 1)) : (Fin (m + 1) → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun := proj k
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

theorem proj_injective_on_hyperplane (k : Fin (m + 1)) :
    Set.InjOn (proj k) {x | x k = 0} := by
  intro x hx y hy h
  ext i
  by_cases hi : i = k
  · rw [hi]
    exact (hx.trans hy.symm)
  · have : (k.succAbove (k.predAbove i hi)) = i := Fin.succAbove_predAbove hi
    rw [← this]
    exact congr_fun h (k.predAbove i hi)

/-- The boundary of a simplicial complex on a coordinate hyperplane. -/
def boundary (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1)) :
    SimplicialComplex ℝ (Fin m → ℝ) where
  faces := {s' | ∃ s ∈ S.faces, (∀ x ∈ s, x k = 0) ∧ s' = s.image (proj k)}
  empty_notMem := by
    rintro _ ⟨s, hs, -, rfl⟩
    simp only [Finset.image_eq_empty]
    exact S.empty_notMem hs
  indep := by
    rintro s' ⟨s, hs, hk, rfl⟩
    let f : {x // x k = 0} ≃ₗ[ℝ] (Fin m → ℝ) :=
      LinearEquiv.ofBijective (LinearMap.codRestrict {x | x k = 0} (LinearMap.comp (proj_linear k) (Submodule.subtype _)) (fun x => x.2))
        (by
          constructor
          · intro x y h
            ext i
            have := proj_injective_on_hyperplane k x.2 y.2 (bysimpa using h)
            exact this i
          · intro y
            let x : Fin (m + 1) → ℝ := fun i => if h : i = k then 0 else y (k.predAbove i h)
            have hxk : x k = 0 := by simp [x]
            refine ⟨⟨x, hxk⟩, ?_⟩
            ext i
            simp [proj_linear, proj, x, Fin.succAbove_ne]
        )
    have : AffineIndependent ℝ (Subtype.val : s → (Fin (m + 1) → ℝ)) := S.indep hs
    -- The set s is a subset of the hyperplane.
    -- The subspace injection preserves independence
    have h_sub : AffineIndependent ℝ (Subtype.val : (s : Set {x | x k = 0}) → {x | x k = 0}) :=
      AffineIndependent.subtype_iff_val.mpr (by
        convert this
        ext x
        rfl
      )
    -- The isomorphism preserves independence
    have h_map := h_sub.map' f
    convert h_map
    ext x
    simp [f]
  down_closed := by
    rintro s' ⟨s, hs, hk, rfl⟩ t' ht'
    let t := s.filter (fun x => proj k x ∈ t')
    refine ⟨t, S.down_closed hs (Finset.filter_subset _ _), ?_, ?_⟩
    · intro x hx; exact hk x (Finset.mem_of_mem_filter hx)
    · change t' = t.image (proj k)
      ext y
      simp only [t, Finset.mem_image, Finset.mem_filter]
      constructor
      · intro hy
        rcases ht' hy with ⟨x, hx_s, rfl⟩
        refine ⟨x, ⟨hx_s, hy⟩, rfl⟩
      · rintro ⟨x, ⟨_, hx_in_t'⟩, rfl⟩
        exact hx_in_t'
  inter_subset_convexHull := by
    rintro s' t' ⟨s, hs, hsk, rfl⟩ ⟨t, ht, htk, rfl⟩
    use s ∩ t
    refine ⟨S.down_closed hs (Finset.inter_subset_left _ _), ?_, ?_⟩
    · intro x hx; exact hsk x (Finset.mem_of_mem_inter_left hx)
    · ext y
      simp only [Finset.mem_image, Finset.mem_inter]
      constructor
      · rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
        exact ⟨⟨x, hxs, rfl⟩, ⟨x, hxt, rfl⟩⟩
      · rintro ⟨⟨x1, hx1s, rfl⟩, ⟨x2, hx2t, heq⟩⟩
        have : x1 = x2 := proj_injective_on_hyperplane k (hsk x1 hx1s) (htk x2 hx2t) heq
        subst this
        exact ⟨x1, ⟨hx1s, hx2t⟩, rfl⟩
    · rw [← convexHull_image (proj_linear k), ← convexHull_image (proj_linear k)]
      rw [← Set.image_inter]
      · refine Set.image_subset _ (S.inter_subset_convexHull hs ht)
      · apply proj_injective_on_hyperplane k
        -- Need to show convex Hulls are in the hyperplane
        rw [Set.union_subset_iff]
        constructor <;> apply convexHull_subset <;> assumption

/-- Vertices of the boundary are vertices of the original complex lying in the hyperplane. -/
theorem boundary_vertices_subset (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1)) :
    (S.boundary k).vertices ⊆ (S.vertices.image (proj k)) := by
  intro v hv
  rcases hv with ⟨s', hs', hv⟩
  rcases hs' with ⟨s, hs, hk, rfl⟩
  simp at hv
  rcases hv with ⟨x, hx, rfl⟩
  exact mem_image_of_mem _ (S.mem_vertices_of_mem_faces hs hx)

/-- A boundary vertex is the projection of a vertex in the hyperplane. -/
theorem boundary_vertex_preimage (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1))
    (v : Fin m → ℝ) (hv : v ∈ (S.boundary k).vertices) :
    ∃ x ∈ S.vertices, x k = 0 ∧ proj k x = v := by
  rcases hv with ⟨s', hs', hv_mem⟩
  rcases hs' with ⟨s, hs, hk, rfl⟩
  simp at hv_mem
  rcases hv_mem with ⟨x, hx, rfl⟩
  exact ⟨x, S.mem_vertices_of_mem_faces hs hx, hk x hx, rfl⟩

/-- The space of the boundary complex is (isomorphic to) the standard simplex of lower dimension. -/
theorem space_boundary (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1))
    (hS : S.space = stdSimplex ℝ (Fin (m + 1))) :
    (S.boundary k).space = stdSimplex ℝ (Fin m) := by
  simp only [SimplicialComplex.space, boundary]
  rw [← Set.image_iUnion]
  -- Set of indices restricted to those in hyperplane
  let I := {s ∈ S.faces | ∀ x ∈ s, x k = 0}
  have h_proj : ⋃ s ∈ I, convexHull ℝ (s.image (proj k) : Set (Fin m → ℝ)) =
                ⋃ s ∈ I, (proj_linear k) '' (convexHull ℝ (s : Set (Fin (m + 1) → ℝ))) := by
    apply iUnion₂_congr
    intro s _
    rw [convexHull_image (proj_linear k)]
    rfl
  rw [h_proj, ← Set.image_iUnion]
  -- Now we identify the union: it is space S ∩ {x | x k = 0}
  -- We need to prove ⋃ s ∈ I, cH s = (⋃ s ∈ S.faces, cH s) ∩ {x | x k = 0}
  have h_union : (⋃ s ∈ I, convexHull ℝ (s : Set (Fin (m + 1) → ℝ))) =
                 S.space ∩ {x | x k = 0} := by
    apply subset_antisymm
    · refine Set.iUnion₂_subset ?_
      intro s hs
      have h_subset_S : convexHull ℝ (s : Set _) ⊆ S.space :=
        S.convexHull_subset_space hs.1
      have h_subset_H : convexHull ℝ (s : Set _) ⊆ {x | x k = 0} :=
        convexHull_subset _ hs.2
      exact Set.subset_inter h_subset_S h_subset_H
    · intro x ⟨hx_space, hx_k⟩
      rw [hS] at hx_space
      -- x is in stdSimplex and x k = 0
      -- We need to show x is in some face s that lies in the hyperplane.
      -- x ∈ face of S.
      -- Since S covers stdSimplex, x is in some s ∈ S.faces.
      obtain ⟨s, hs, hxs⟩ := S.mem_space_iff.mp hx_space -- Wait, S.mem_space_iff is x ∈ space S ↔ ∃ s, ...
      -- We need to show that IF x ∈ cH s AND x k = 0 (and S is triangulation of stdSimplex)
      -- THEN there exists s' ⊆ s (so s' ∈ S.faces) such that s' ⊆ H and x ∈ cH s'.
      -- Actually, for stdSimplex with vertices V, the face corresponding to H is cH (V \ {v_k}).
      -- Since S is a triangulation, the restriction to a face is a triangulation of the face.
      -- This implies x is in the space of the restricted complex.
      -- The restricted complex consists of faces contained in H.
      -- This is exactly what we need.
      -- However, proving this from scratch might be long.
      -- Is there a lemma?
      -- SimplicialComplex.space_inter_eq_union_convexHull_inter might be useful?
      -- No, we need to know that s ∩ {x | x k = 0} is the convex hull of a face.
      -- stdSimplex face property: {x ∈ stdSimplex | x k = 0} = convexHull {e_i | i ≠ k}.
      -- The vertices of S must lie in stdSimplex.
      -- If x ∈ cH s and x k = 0, then x is a convex comb of vertices of s.
      -- Since all vertices v of s satisfy v k ≥ 0 (as they are in stdSimplex),
      -- and ∑ w_v * v k = 0 with w_v > 0 (for x in relative interior),
      -- this implies v k = 0 for all v in s involved in the convex combination.
      -- Let s' = {v ∈ s | v k = 0}.
      -- Then x ∈ cH s'.
      -- s' is a face of s (down_closed).
      -- So s' ∈ S.faces.
      -- And s' ⊆ {x | x k = 0}.
      -- So s' ∈ I.
      -- So x ∈ ⋃ s ∈ I, cH s.
      obtain ⟨s, hs_face, hx_mem_cH⟩ := S.mem_space_iff.mp hx_space
      let s' := s.filter (fun v => v k = 0)
      have h_subset : s' ⊆ s := Finset.filter_subset _ _
      have hs'_face : s' ∈ S.faces := S.down_closed hs_face h_subset
      have : x ∈ convexHull ℝ (s' : Set (Fin (m + 1) → ℝ)) := by
         rw [Finset.convexHull_eq] at hx_mem_cH ⊢
         rcases hx_mem_cH with ⟨w, hw_nonneg, hw_supp, hw_sum, rfl⟩
         refine ⟨w, hw_nonneg, ?_, hw_sum, ?_⟩
         · intro v hv
           have hv_in_s : v ∈ s := hw_supp hv
           have h_vk_zero : v k = 0 := by
             -- Weighted sum is 0. All terms nonneg. So all terms 0.
             have h_sum_zero : (s.centerMass w id) k = 0 := hx_k
             rw [Finset.centerMass, Finset.sum_div] at h_sum_zero
             simp only [Pi.smul_apply, id_eq, smul_eq_mul] at h_sum_zero
             -- Denominator is 1.
             rw [hw_sum, div_one] at h_sum_zero
             -- Sum w_i * v_i_k = 0.
             have h_term_nonneg : ∀ y ∈ s, 0 ≤ w y * y k := by
               intro y hy
               have : y ∈ stdSimplex ℝ (Fin (m + 1)) := by
                 rw [← hS]; exact S.subset_space hs_face hy
               exact mul_nonneg (hw_nonneg y) (this.2 k)
             have h_all_zero : ∀ y ∈ s, w y * y k = 0 :=
               Finset.sum_eq_zero_iff_of_nonneg h_term_nonneg |>.mp h_sum_zero _
             specialize h_all_zero v hv_in_s
             -- if w v > 0, then v k = 0
             by_contra h_vk_ne_zero
             have : w v = 0 := by
               by_contra h_w_ne
               have := mul_pos (lt_of_le_of_ne (hw_nonneg v) (Ne.symm h_w_ne))
                 (lt_of_le_of_ne ((hS ▸ S.subset_space hs_face hv_in_s : _).2 k) (Ne.symm h_vk_ne_zero))
               linarith
             exact (this ▸ hv)
           rw [Finset.mem_coe, s', Finset.mem_filter]
           exact ⟨hv_in_s, h_vk_zero⟩
         · apply Finset.centerMass_eq_of_sum_1 _ hw_sum
      refine Set.mem_iUnion₂.mpr ⟨s', ⟨hs'_face, ?_⟩, this⟩
      intro v hv
      exact (Finset.mem_filter.mp hv).2
  rw [h_union, hS]
  -- P maps stdSimplex ∩ H to stdSimplex
  ext y
  constructor
  · rintro ⟨x, ⟨hx_std, hx_k⟩, rfl⟩
    -- x is in stdSimplex, so x i ≥ 0 and sum x = 1.
    -- y = x ∘ k.succAbove.
    -- sum y = sum_{j} x (k.succAbove j) = sum_{l ≠ k} x l.
    -- Since x k = 0, sum_{l ≠ k} x l = sum_{all} x l = 1.
    -- Also y j = x (...) ≥ 0.
    rw [mem_stdSimplex_iff] at hx_std ⊢
    refine ⟨fun j => hx_std.2 _, ?_⟩
    skip
    rw [Fin.sum_univ_eq_sum_univ_succAbove x k] at hx_std
    rw [hx_k, add_zero] at hx_std
    exact hx_std.1
  · intro hy
    -- Lift y to x
    let x : Fin (m + 1) → ℝ := fun i => if h : i = k then 0 else y (k.predAbove i h)
    have hxk : x k = 0 := by simp [x]
    have hy_eq_Px : y = proj k x := by
      ext j
      simp [proj, x, Fin.succAbove_ne]
    rw [hy_eq_Px]
    refine ⟨x, ⟨?_, hxk⟩, rfl⟩
    rw [mem_stdSimplex_iff]
    constructor
    · rw [Fin.sum_univ_eq_sum_univ_succAbove x k]
      simp only [hxk, add_zero]
      convert hy.1 using 1
      apply Finset.sum_congr rfl
      intro j _
      simp [x, Fin.succAbove_ne]
    · intro i
      by_cases hi : i = k
      · rw [hi, hxk]; rfl
      · simp [x, hi, hy.2]

/-- The boundary of a finite complex is finite. -/
theorem boundary_finite (S : SimplicialComplex ℝ (Fin (m + 1) → ℝ)) (k : Fin (m + 1))
    (h : S.faces.Finite) : (S.boundary k).faces.Finite := by
  let f : Finset (Fin (m + 1) → ℝ) → Finset (Fin m → ℝ) := fun s => s.image (proj k)
  have : (S.boundary k).faces ⊆ f '' S.faces := by
    rintro s' ⟨s, _, _, rfl⟩
    exact Set.mem_image_of_mem f ‹_›
  exact Set.Finite.subset (Set.Finite.image f h) this

end Geometry.SimplicialComplex
