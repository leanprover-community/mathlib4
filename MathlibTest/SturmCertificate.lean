import Mathlib.Analysis.Polynomial.SturmCertificate

open Polynomial

/-- info: Polynomial.CertifiedSturmChain (p : ℝ[X]) (ps : List ℝ[X]) : Prop -/
#guard_msgs in
#check Polynomial.CertifiedSturmChain

/--
info: Polynomial.CertifiedSturmChain.toIsSturmSequence {p : ℝ[X]} {ps : List ℝ[X]} (h : p.CertifiedSturmChain ps) :
  p.IsSturmSequence ps
-/
#guard_msgs in
#check Polynomial.CertifiedSturmChain.toIsSturmSequence

/--
info: Polynomial.positive_scaled_recurrence_sign_reversal {a x : ℝ} {p q r s : ℝ[X]} (ha : 0 < a) (hrec : C a * p = q * r - s)
  (hr : eval x r = 0) : SignType.sign (eval x s) = -SignType.sign (eval x p)
-/
#guard_msgs in
#check Polynomial.positive_scaled_recurrence_sign_reversal

/--
info: Polynomial.bezout_nonzero_constant_no_common_real_root {p q u v : ℝ[X]} {c : ℝ} (hbez : u * p + v * q = C c)
  (hc : c ≠ 0) (x : ℝ) : ¬(eval x p = 0 ∧ eval x q = 0)
-/
#guard_msgs in
#check Polynomial.bezout_nonzero_constant_no_common_real_root

/--
info: Polynomial.simple_root_derivative_punctured_sign (p : ℝ[X]) {x0 : ℝ} (hp0 : eval x0 p = 0)
  (hd0 : eval x0 (derivative p) ≠ 0) :
  ∀ᶠ (x : ℝ) in nhdsWithin x0 {x0}ᶜ, SignType.sign (eval x (p * derivative p)) = if x > x0 then 1 else -1
-/
#guard_msgs in
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

/--
info: Polynomial.CertifiedSturmChain.count_roots_between {p : ℝ[X]} {ps : List ℝ[X]} (h : p.CertifiedSturmChain ps)
  (hpne : p ≠ 0) (a b : ℝ) :
  a ≤ b → ↑(sturmVariations ps a) - ↑(sturmVariations ps b) = ↑{x | a < x ∧ x ≤ b ∧ eval x p = 0}.ncard
-/
#guard_msgs in
#check Polynomial.CertifiedSturmChain.count_roots_between
