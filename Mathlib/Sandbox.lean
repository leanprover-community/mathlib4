import Mathlib.LinearAlgebra.FiniteDimensional

variable {K ι : Type*} [DivisionRing K] [Fintype ι]

noncomputable def basisOfPiSpaceOfLinearIndependent {b : ι → (ι → K)} (hb : LinearIndependent K b) :
    Basis ι K (ι → K) := by
  by_cases hι : Nonempty ι
  · refine basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm
  · rw [not_nonempty_iff] at hι
    exact Basis.empty _

theorem coe_basisOfPiSpaceOfLinearIndependent {b : ι → (ι → K)} (hb : LinearIndependent K b) :
    ⇑(basisOfPiSpaceOfLinearIndependent hb) = b := by
  by_cases hι : Nonempty ι
  · rw [basisOfPiSpaceOfLinearIndependent, dif_pos hι]
    exact coe_basisOfLinearIndependentOfCardEqFinrank hb _
  · rw [basisOfPiSpaceOfLinearIndependent, dif_neg hι]
    ext i
    exact ((not_nonempty_iff.mp hι).false i).elim
