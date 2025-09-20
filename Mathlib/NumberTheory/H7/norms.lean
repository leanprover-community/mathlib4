import Mathlib.Analysis.Matrix

variable {R l m n α β ι : Type*} [Fintype l] [Fintype m] [Fintype n] [Unique ι]

attribute [local instance] Matrix.linftyOpSeminormedAddCommGroup

open Finset
namespace Matrix

theorem matrix_norm_etc [SeminormedAddCommGroup α] (A : Matrix m n α) :
   ‖A‖ ≤ Fintype.card n * (haveI := Matrix.seminormedAddCommGroup (m := m) (n := n) (α := α) ; ‖A‖)  := by
  rw [norm_eq_sup_sup_nnnorm]
  rw [linfty_opNorm_def]
  norm_cast
  rw [NNReal.mul_finset_sup]
  apply sup_mono_fun
  intros b hb
  rw [← card_univ]
  rw [← nsmul_eq_mul]
  rw [← sum_const]
  apply sum_le_sum
  intros i hi
  apply le_sup hi

end Matrix
