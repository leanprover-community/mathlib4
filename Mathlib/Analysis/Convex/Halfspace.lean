/-
Copyright (c) 2024 Hyeokjun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeokjun Kwon
-/
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.NormedSpace.AddTorsorBases

open LinearMap Set

open scoped BigOperators Convex Pointwise


/-- Halfspace is a set of points that lie on one side of a hyperplane. -/
structure Halfspace (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  carrier : Set E
  direction : {p : E // ‖p‖ = 1}
  bound : ℝ
  inner_le : ∀ x, x ∈ carrier ↔ ⟪direction.1, x⟫_ℝ ≤ bound

namespace Halfspace
variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

instance SetLike : SetLike (Halfspace E) E where
  coe := Halfspace.carrier
  coe_injective' := by
    intro ⟨S1, d1, b1, h1⟩ ⟨S2, d2, b2, h2⟩ hS
    simp only at hS
    have hd : d1 = d2 := by
      by_contra! hne
      rw [Subtype.ext_iff_val.ne] at hne
      let v' := d1.1 - d2.1
      obtain hv'ne0 : v' ≠ 0 := sub_ne_zero.mpr hne
      let v := ‖v'‖⁻¹ • v'
      have hv'1 : 0 < ⟪d1.1, v⟫_ℝ := by
        rwa [inner_smul_right, mul_pos_iff_of_pos_left (by simp [hv'ne0]), inner_sub_right,
          real_inner_self_eq_norm_sq, d1.prop, one_pow, sub_pos,
          inner_lt_one_iff_real_of_norm_one d1.prop d2.prop]
      have hv'2 : ⟪d2.1, v⟫_ℝ < 0 := by
        rw [inner_smul_right]
        refine mul_neg_of_pos_of_neg (by simp [hv'ne0]) ?_
        rwa [inner_sub_right, real_inner_self_eq_norm_sq, d2.prop, one_pow, sub_neg,
          inner_lt_one_iff_real_of_norm_one d2.prop d1.prop, ne_comm]
      have hv1out (m) (hm : b1 / ⟪d1.1, v⟫_ℝ < m) : (m • v) ∉ S1 := by
        rw [h1, inner_smul_right, ← le_div_iff hv'1]
        exact not_le_of_gt hm
      have hv2in (m) (hm : b2 / ⟪d2.1, v⟫_ℝ < m) : (m • v) ∈ S2 := by
        rw [h2, inner_smul_right]
        exact le_of_lt <| (div_lt_iff_of_neg hv'2).mp hm
      let M := 1 + max (b1 / ⟪d1.1, v⟫_ℝ) (b2 / ⟪d2.1, v⟫_ℝ)
      obtain hlt1 : b1 / ⟪d1.1, v⟫_ℝ < M := by
        linarith [le_max_left (b1 / ⟪d1.1, v⟫_ℝ) (b2 / ⟪d2.1, v⟫_ℝ)]
      obtain hlt2: b2 / ⟪d2.1, v⟫_ℝ < M := by
        linarith [le_max_right (b1 / ⟪d1.1, v⟫_ℝ) (b2 / ⟪d2.1, v⟫_ℝ)]
      exact (hv1out M hlt1) <| hS ▸ (hv2in M hlt2)

    congr
    contrapose! hS
    rw [← Set.symmDiff_nonempty, Set.nonempty_def]
    use (max b1 b2) • d1
    rw [Set.mem_symmDiff]
    apply Or.imp (fun hmax => ?_) (fun hmax => ?_) <| max_choice b1 b2 <;>
    rw [hmax, h1, h2, inner_smul_right, inner_smul_right, hd, real_inner_self_eq_norm_sq, d2.prop]
    simp [lt_of_le_of_ne (max_eq_left_iff.mp hmax) hS.symm]
    simp [lt_of_le_of_ne (max_eq_right_iff.mp hmax) hS]
    done

variable (h : Halfspace E)

lemma carrier_eq : h.carrier = {x | ⟪h.direction.1, x⟫_ℝ ≤ h.bound} := by
  ext x
  exact h.inner_le x

noncomputable def linearIsom : NormedSpace.Dual ℝ E := InnerProductSpace.toDualMap ℝ E h.direction

lemma linearIsom_ne_zero : h.linearIsom ≠ 0 := by
  apply_fun (‖·‖)
  beta_reduce
  rw [Halfspace.linearIsom, norm_zero, LinearIsometry.norm_map]
  linarith [h.direction.2]

lemma mem_of_linearIsom (x : E) : x ∈ h.carrier ↔ h.linearIsom x ≤ h.bound := by
  rw [h.carrier_eq, Halfspace.linearIsom, InnerProductSpace.toDualMap_apply]
  exact mem_setOf

lemma convex : Convex ℝ h.carrier := by
  rw [h.carrier_eq]
  exact convex_halfspace_le h.linearIsom.isLinear h.bound

lemma closed : IsClosed h.carrier := by
  rw [h.carrier_eq]
  exact IsClosed.preimage h.linearIsom.cont isClosed_Iic

lemma affineSpan_eq_top : affineSpan ℝ h.carrier = ⊤ := by
  refine affineSpan_eq_top_of_nonempty_interior ?_
  apply Set.Nonempty.mono (?_ : h.linearIsom ⁻¹' (Metric.ball (h.bound -1) 1) ⊆ _)
  · -- preimage of ball is not empty as f is surjective
    refine Nonempty.preimage (by simp) <| h.linearIsom.surjective_of_ne_zero ?_
    norm_cast
    exact h.linearIsom_ne_zero
  -- this open set is subset of the halfspace
  rw [IsOpen.subset_interior_iff (IsOpen.preimage (by exact h.linearIsom.cont) Metric.isOpen_ball)]
  refine subset_trans (fun x hx => ?_) (subset_convexHull ℝ h.carrier)
  rw [Real.ball_eq_Ioo, sub_add_cancel, mem_preimage, mem_Ioo] at hx
  rw [h.mem_of_linearIsom]
  exact hx.2.le

end Halfspace
