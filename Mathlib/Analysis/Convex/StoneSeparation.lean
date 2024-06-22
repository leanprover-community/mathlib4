/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Join

#align_import analysis.convex.stone_separation from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!
# Stone's separation theorem

This file proves Stone's separation theorem. This tells us that any two disjoint convex sets can be
separated by a convex set whose complement is also convex.

In locally convex real topological vector spaces, the Hahn-Banach separation theorems provide
stronger statements: one may find a separating hyperplane, instead of merely a convex set whose
complement is convex.
-/


open Set

variable {𝕜 E ι : Type*} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

/-- In a tetrahedron with vertices `x`, `y`, `p`, `q`, any segment `[u, v]` joining the opposite
edges `[x, p]` and `[y, q]` passes through any triangle of vertices `p`, `q`, `z` where
`z ∈ [x, y]`. -/
theorem not_disjoint_segment_convexHull_triple {p q u v x y z : E} (hz : z ∈ segment 𝕜 x y)
    (hu : u ∈ segment 𝕜 x p) (hv : v ∈ segment 𝕜 y q) :
    ¬Disjoint (segment 𝕜 u v) (convexHull 𝕜 {p, q, z}) := by
  rw [not_disjoint_iff]
  obtain ⟨az, bz, haz, hbz, habz, rfl⟩ := hz
  obtain rfl | haz' := haz.eq_or_lt
  · rw [zero_add] at habz
    rw [zero_smul, zero_add, habz, one_smul]
    refine ⟨v, by apply right_mem_segment, segment_subset_convexHull ?_ ?_ hv⟩ <;> simp
  obtain ⟨av, bv, hav, hbv, habv, rfl⟩ := hv
  obtain rfl | hav' := hav.eq_or_lt
  · rw [zero_add] at habv
    rw [zero_smul, zero_add, habv, one_smul]
    exact ⟨q, right_mem_segment _ _ _, subset_convexHull _ _ <| by simp⟩
  obtain ⟨au, bu, hau, hbu, habu, rfl⟩ := hu
  have hab : 0 < az * av + bz * au := by positivity
  refine ⟨(az * av / (az * av + bz * au)) • (au • x + bu • p) +
    (bz * au / (az * av + bz * au)) • (av • y + bv • q), ⟨_, _, ?_, ?_, ?_, rfl⟩, ?_⟩
  · positivity
  · positivity
  · rw [← add_div, div_self]; positivity
  rw [smul_add, smul_add, add_add_add_comm, add_comm, ← mul_smul, ← mul_smul]
  classical
    let w : Fin 3 → 𝕜 := ![az * av * bu, bz * au * bv, au * av]
    let z : Fin 3 → E := ![p, q, az • x + bz • y]
    have hw₀ : ∀ i, 0 ≤ w i := by
      rintro i
      fin_cases i
      · exact mul_nonneg (mul_nonneg haz hav) hbu
      · exact mul_nonneg (mul_nonneg hbz hau) hbv
      · exact mul_nonneg hau hav
    have hw : ∑ i, w i = az * av + bz * au := by
      trans az * av * bu + (bz * au * bv + au * av)
      · simp [w, Fin.sum_univ_succ, Fin.sum_univ_zero]
      rw [← one_mul (au * av), ← habz, add_mul, ← add_assoc, add_add_add_comm, mul_assoc, ← mul_add,
        mul_assoc, ← mul_add, mul_comm av, ← add_mul, ← mul_add, add_comm bu, add_comm bv, habu,
        habv, one_mul, mul_one]
    have hz : ∀ i, z i ∈ ({p, q, az • x + bz • y} : Set E) := fun i => by fin_cases i <;> simp [z]
    convert Finset.centerMass_mem_convexHull (Finset.univ : Finset (Fin 3)) (fun i _ => hw₀ i)
        (by rwa [hw]) fun i _ => hz i
    rw [Finset.centerMass]
    simp_rw [div_eq_inv_mul, hw, mul_assoc, mul_smul (az * av + bz * au)⁻¹, ← smul_add, add_assoc, ←
      mul_assoc]
    congr 3
    rw [← mul_smul, ← mul_rotate, mul_right_comm, mul_smul, ← mul_smul _ av, mul_rotate,
      mul_smul _ bz, ← smul_add]
    simp only [w, z, smul_add, List.foldr, Matrix.cons_val_succ', Fin.mk_one,
      Matrix.cons_val_one, Matrix.head_cons, add_zero]
#align not_disjoint_segment_convex_hull_triple not_disjoint_segment_convexHull_triple

/-- **Stone's Separation Theorem** -/
theorem exists_convex_convex_compl_subset (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst : Disjoint s t) :
    ∃ C : Set E, Convex 𝕜 C ∧ Convex 𝕜 Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ := by
  let S : Set (Set E) := { C | Convex 𝕜 C ∧ Disjoint C t }
  obtain ⟨C, hC, hsC, hCmax⟩ :=
    zorn_subset_nonempty S
      (fun c hcS hc ⟨_, _⟩ =>
        ⟨⋃₀ c,
          ⟨hc.directedOn.convex_sUnion fun s hs => (hcS hs).1,
            disjoint_sUnion_left.2 fun c hc => (hcS hc).2⟩,
          fun s => subset_sUnion_of_mem⟩)
      s ⟨hs, hst⟩
  refine
    ⟨C, hC.1, convex_iff_segment_subset.2 fun x hx y hy z hz hzC => ?_, hsC, hC.2.subset_compl_left⟩
  suffices h : ∀ c ∈ Cᶜ, ∃ a ∈ C, (segment 𝕜 c a ∩ t).Nonempty by
    obtain ⟨p, hp, u, hu, hut⟩ := h x hx
    obtain ⟨q, hq, v, hv, hvt⟩ := h y hy
    refine
      not_disjoint_segment_convexHull_triple hz hu hv
        (hC.2.symm.mono (ht.segment_subset hut hvt) <| convexHull_min ?_ hC.1)
    simp [insert_subset_iff, hp, hq, singleton_subset_iff.2 hzC]
  rintro c hc
  by_contra! h
  suffices h : Disjoint (convexHull 𝕜 (insert c C)) t by
    rw [←
      hCmax _ ⟨convex_convexHull _ _, h⟩ ((subset_insert _ _).trans <| subset_convexHull _ _)] at hc
    exact hc (subset_convexHull _ _ <| mem_insert _ _)
  rw [convexHull_insert ⟨z, hzC⟩, convexJoin_singleton_left]
  refine disjoint_iUnion₂_left.2 fun a ha => disjoint_iff_inter_eq_empty.2 (h a ?_)
  rwa [← hC.1.convexHull_eq]
#align exists_convex_convex_compl_subset exists_convex_convex_compl_subset
