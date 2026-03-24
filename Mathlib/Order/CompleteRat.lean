import Mathlib.Data.EReal.Basic
import Mathlib.Order.Completion
import Mathlib.Tactic.Order

open DedekindCut
open Concept
open Order

noncomputable def ratEmbedEReal : ℚ ↪o EReal := Rat.castOrderEmbedding.trans Real.coeOrderEmbedding

theorem ratEmbedEReal_apply (x : ℚ) : ratEmbedEReal x = ((x : ℝ) : EReal) := rfl

/-- The order embedding from the completion of `ℚ` to `EReal` -/
noncomputable def factorEmbeddingRat : DedekindCut ℚ ↪o EReal := factorEmbedding ratEmbedEReal

theorem factorEmbeddingRat_apply (x : DedekindCut ℚ) :
  factorEmbeddingRat x = sSup ((fun (a : ℚ) ↦ ((a : ℝ) : EReal)) '' x.extent) := rfl

/-- The set of rational numbers less than the extended real `x` -/
def ratLowerBounds (x : EReal) : Set ℚ := ratEmbedEReal ⁻¹' (lowerBounds {x})

theorem ratLowerBounds_apply (x : EReal) :
    ratLowerBounds x = (fun (a : ℚ) ↦ ((a : ℝ) : EReal)) ⁻¹' (Set.Iic x) := by
  simp [ratLowerBounds]
  rfl

theorem mem_ratLowerBounds_iff (x : EReal) (q : ℚ) :
  q ∈ ratLowerBounds x ↔ ratEmbedEReal q ≤ x := by simp [ratLowerBounds]

theorem ratLowerBounds_eq_lowerBoundsUpperBounds (x : EReal) :
    lowerBounds (upperBounds (ratLowerBounds x)) = ratLowerBounds x := by
  refine Set.Subset.antisymm_iff.mpr ⟨?_, ?_⟩
  · intro q hq
    by_contra h
    simp only [mem_ratLowerBounds_iff, not_le] at h
    obtain ⟨r, x_lt_r, r_lt_q⟩ := EReal.exists_rat_btwn_of_lt h
    have : r < q := by simpa [ratEmbedEReal_apply] using r_lt_q
    simp only [mem_lowerBounds, mem_upperBounds, mem_ratLowerBounds_iff] at hq
    have : q ≤ r := hq r (by
      intro h le
      simp only [ratEmbedEReal_apply] at le
      have : ((h : ℝ) : EReal) ≤ ((r : ℝ) : EReal) := by order
      norm_cast at this)
    order
  · exact subset_lowerBounds_upperBounds (ratLowerBounds x)

def isExtent_ratLowerBounds (x : EReal) : IsExtent (· ≤ ·) (ratLowerBounds x) := by
  simp only [isExtent_iff, upperPolar_le, lowerPolar_le]
  exact ratLowerBounds_eq_lowerBoundsUpperBounds x

def eRealEmbedDedekindCut (x : EReal) : DedekindCut ℚ := ofIsExtent (· ≤ ·) (ratLowerBounds x)
  (isExtent_ratLowerBounds x)

theorem left_eRealEmbedDedekindCut_apply (x : EReal) :
    (eRealEmbedDedekindCut x).left = (fun (a : ℚ) ↦ ((a : ℝ) : EReal)) ⁻¹' (Set.Iic x) := by
  simp [eRealEmbedDedekindCut, ratLowerBounds_apply]

theorem factorEmbeddingRat_leftInv_eRealEmbedDedekindCut :
    Function.LeftInverse eRealEmbedDedekindCut factorEmbeddingRat := by
  intro x
  ext z
  simp only [factorEmbeddingRat_apply, left_eRealEmbedDedekindCut_apply, Set.mem_preimage,
    Set.mem_Iic]
  simp only [sSup_image]
  constructor
  · intro z_le_sup
    simp_rw [← x.lowerBounds_right, ← x.upperBounds_left, mem_lowerBounds, mem_upperBounds]
    intro r hr
    simp only [le_iSup_iff, iSup_le_iff] at z_le_sup
    exact_mod_cast (z_le_sup ((r : ℝ) : EReal) (fun t ht => by exact_mod_cast hr t ht))
  · exact fun z_mem_extent ↦ le_iSup₂_of_le z z_mem_extent le_rfl

theorem factorEmbeddingRat_rightInv_eRealEmbedDedekindCut :
    Function.RightInverse eRealEmbedDedekindCut factorEmbeddingRat := by
  intro x
  simp only [factorEmbeddingRat_apply, left_eRealEmbedDedekindCut_apply]
  apply sSup_eq_of_forall_le_of_forall_lt_exists_gt
  · simp
  · simp only [Set.mem_image, Set.mem_preimage, Set.mem_Iic, exists_exists_and_eq_and]
    intro w w_lt_x
    obtain ⟨r, w_lt_r, r_lt_x⟩ := EReal.exists_rat_btwn_of_lt w_lt_x
    use r
    exact ⟨r_lt_x.le, w_lt_r⟩

noncomputable def completeRat_iso_EReal : DedekindCut ℚ ≃o EReal where
  toFun := factorEmbeddingRat
  invFun := eRealEmbedDedekindCut
  left_inv := factorEmbeddingRat_leftInv_eRealEmbedDedekindCut
  right_inv := factorEmbeddingRat_rightInv_eRealEmbedDedekindCut
  map_rel_iff' := by simp
