import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Order.CompletePartialOrder

open Set Bornology
open scoped NNReal

variable {ι : Type*} {s : Set ι} {E : Type*} [SeminormedAddCommGroup E]

namespace ENNReal

lemma exists_biSup_le_enorm_add_eps
    {f : ι → E} {ε : ℝ≥0} (εpos : 0 < ε) (hs : s.Nonempty) (hf : IsBounded (range f)) :
    ∃ x ∈ s, ⨆ z ∈ s, ‖f z‖ₑ ≤ ‖f x‖ₑ + ε := by
  obtain ⟨i₀, mi₀⟩ := hs; set A := ⨆ z ∈ s, ‖f z‖ₑ
  have lub : IsLUB ((‖f ·‖ₑ) '' s) A := isLUB_biSup
  rw [isLUB_iff_le_iff] at lub
  by_contra! h
  specialize lub (A - ε)
  have key : A - ε ∈ upperBounds ((‖f ·‖ₑ) '' s) := fun i mi ↦ by
    rw [mem_image] at mi; obtain ⟨x, mx, hx⟩ := mi
    specialize h x mx; rw [hx] at h; exact ENNReal.le_sub_of_add_le_right (by simp) h.le
  rw [← lub] at key
  have Ant : A ≠ ⊤ := by -- boundedness of `f` used here
    by_contra! h; simp_rw [A, iSup₂_eq_top] at h; apply absurd h; push_neg
    rw [isBounded_iff_forall_norm_le] at hf; obtain ⟨C, hC⟩ := hf
    simp_rw [mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hC
    lift C to ℝ≥0 using (norm_nonneg _).trans (hC i₀)
    use C, by simp, fun i mi ↦ by exact_mod_cast hC i
  obtain ⟨B, eB⟩ : ∃ B : ℝ≥0, A = B := Option.ne_none_iff_exists'.mp Ant
  have εlA : ε < A := le_add_self.trans_lt (h i₀ mi₀)
  rw [eB, coe_lt_coe] at εlA
  rw [eB, ← ENNReal.coe_sub, coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_sub εlA.le,
    le_sub_self_iff] at key
  rw [← NNReal.coe_pos] at εpos; linarith only [εpos, key]

lemma exists_enorm_sub_eps_le_biInf
    {f : ι → E} {ε : ℝ≥0} (εpos : 0 < ε) (hs : s.Nonempty) :
    ∃ x ∈ s, ‖f x‖ₑ - ε ≤ ⨅ z ∈ s, ‖f z‖ₑ := by
  obtain ⟨i₀, mi₀⟩ := hs; set A := ⨅ z ∈ s, ‖f z‖ₑ
  have glb : IsGLB ((‖f ·‖ₑ) '' s) A := isGLB_biInf
  rw [isGLB_iff_le_iff] at glb
  by_contra! h
  specialize glb (A + ε)
  have key : A + ε ∈ lowerBounds ((‖f ·‖ₑ) '' s) := fun i mi ↦ by
    rw [mem_image] at mi; obtain ⟨x, mx, hx⟩ := mi
    specialize h x mx; rw [hx] at h; exact (lt_tsub_iff_right.mp h).le
  rw [← glb] at key
  have Ant : A ≠ ⊤ := (h i₀ mi₀).ne_top
  obtain ⟨B, eB⟩ : ∃ B : ℝ≥0, A = B := Option.ne_none_iff_exists'.mp Ant
  rw [eB, ← ENNReal.coe_add, coe_le_coe, ← NNReal.coe_le_coe, NNReal.coe_add,
    add_le_iff_nonpos_right] at key
  rw [← NNReal.coe_pos] at εpos; linarith only [εpos, key]

end ENNReal
