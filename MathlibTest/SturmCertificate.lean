import Mathlib.Analysis.Polynomial.SturmCertificate

open Polynomial

#check Polynomial.CertifiedSturmChain
#check Polynomial.CertifiedSturmChain.toIsSturmSequence
#check Polynomial.positive_scaled_recurrence_sign_reversal
#check Polynomial.bezout_nonzero_constant_no_common_real_root
#check Polynomial.simple_root_derivative_punctured_sign

namespace Polynomial

private noncomputable def sturmTestP : ℝ[X] := X ^ 2 - 2
private noncomputable def sturmTestChain : List ℝ[X] := [sturmTestP, sturmTestP.derivative, 4]

/-- Small exact smoke certificate exercising the generic PRS-to-Sturm constructor. -/
private theorem sturmTestCertified : CertifiedSturmChain sturmTestP sturmTestChain := by
  refine
    { ne_nil := by simp [sturmTestChain]
      length_ge_two := by simp [sturmTestChain]
      second_mem := by simp [sturmTestChain]
      head_eq_p := by simp [sturmTestChain]
      second_eq_derivative := by simp [sturmTestChain]
      recurrence := ?_
      terminal_constant := ?_
      bezout := ?_ }
  · intro i hi
    simp [sturmTestChain] at hi
    have hi0 : i = 0 := by omega
    subst hi0
    refine ⟨2, X, by norm_num, ?_⟩
    have hC : (C 2 : ℝ[X]) * C 2 = C 4 := by rw [← map_mul]; norm_num
    simp only [sturmTestChain, sturmTestP, List.getElem_cons_zero, List.getElem_cons_succ,
      derivative_sub, derivative_X_pow, derivative_C, sub_zero, ← Polynomial.C_ofNat]
    linear_combination -hC
  · refine ⟨4, by norm_num, ?_⟩
    simp [sturmTestChain, ← Polynomial.C_ofNat]
  · refine ⟨2, -X, -4, by norm_num, ?_⟩
    have hC : (C 2 : ℝ[X]) * C 2 = C 4 := by rw [← map_mul]; norm_num
    simp only [sturmTestChain, sturmTestP, List.getElem_cons_zero, List.getElem_cons_succ,
      derivative_sub, derivative_X_pow, derivative_C, sub_zero, ← Polynomial.C_ofNat, Polynomial.C_neg]
    linear_combination -hC

example : CertifiedSturmChain sturmTestP sturmTestChain := sturmTestCertified

example : IsSturmSequence sturmTestP sturmTestChain :=
  sturmTestCertified.toIsSturmSequence

end Polynomial
#check Polynomial.CertifiedSturmChain.count_roots_between
