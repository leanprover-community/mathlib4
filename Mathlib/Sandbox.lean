import Mathlib.Algebra.Module.ZLattice.Covolume


section

variable {K ι : Type*} [DivisionRing K] [Fintype ι]

noncomputable def basisOfPiSpaceOfLinearIndependent {b : ι → (ι → K)} (hb : LinearIndependent K b) :
    Basis ι K (ι → K) := by
  by_cases hι : Nonempty ι
  · refine basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm
  · rw [not_nonempty_iff] at hι
    exact Basis.empty _

@[simp]
theorem coe_basisOfPiSpaceOfLinearIndependent {b : ι → (ι → K)} (hb : LinearIndependent K b) :
    ⇑(basisOfPiSpaceOfLinearIndependent hb) = b := by
  by_cases hι : Nonempty ι
  · rw [basisOfPiSpaceOfLinearIndependent, dif_pos hι]
    exact coe_basisOfLinearIndependentOfCardEqFinrank hb _
  · rw [basisOfPiSpaceOfLinearIndependent, dif_neg hι]
    ext i
    exact ((not_nonempty_iff.mp hι).false i).elim

end

section

theorem Matrix.det_ne_zero_iff {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] [Fintype ι]
    {v : ι → (ι → K)} :
    (Matrix.of fun i ↦ v i).det ≠ 0 ↔ LinearIndependent K v := by
  by_cases hι : Nonempty ι
  · rw [← isUnit_iff_ne_zero, ← Pi.basisFun_det_apply, ← is_basis_iff_det, and_iff_left_iff_imp]
    exact fun h ↦ h.span_eq_top_of_card_eq_finrank (Module.finrank_fintype_fun_eq_card K).symm
  · rw [not_nonempty_iff] at hι
    simp

theorem Matrix.det_eq_zero_iff {K : Type*} [Field K] {ι : Type*} [DecidableEq ι] [Fintype ι]
    {v : ι → (ι → K)} :
    (Matrix.of fun i ↦ v i).det = 0 ↔ ¬ LinearIndependent K v := by
  simpa using (Matrix.det_ne_zero_iff (v := v)).not

end
