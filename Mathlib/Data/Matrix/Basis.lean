/-
Copyright (c) 2020 Jalex Stark. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jalex Stark, Kim Morrison, Eric Wieser, Oliver Nash, Wen Yang
-/
import Mathlib.Data.Matrix.Basic

/-!
# Matrices with a single non-zero element.

This file provides `Matrix.single`. The matrix `Matrix.single i j c` has `c`
at position `(i, j)`, and zeroes elsewhere.
-/

assert_not_exists Matrix.trace

variable {l m n o : Type*}
variable {R S α β γ : Type*}

namespace Matrix

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq o]

section Zero
variable [Zero α]

/-- `single i j a` is the matrix with `a` in the `i`-th row, `j`-th column,
and zeroes elsewhere.
-/
def single (i : m) (j : n) (a : α) : Matrix m n α :=
  of <| fun i' j' => if i = i' ∧ j = j' then a else 0

@[deprecated (since := "2025-05-05")] alias stdBasisMatrix := single

/-- See also `single_eq_updateRow_zero` and `single_eq_updateCol_zero`. -/
theorem single_eq_of_single_single (i : m) (j : n) (a : α) :
    single i j a = Matrix.of (Pi.single i (Pi.single j a)) := by
  ext a b
  unfold single
  by_cases hi : i = a <;> by_cases hj : j = b <;> simp [*]

@[deprecated (since := "2025-05-05")]
alias stdBasisMatrix_eq_of_single_single := single_eq_of_single_single

@[simp]
theorem of_symm_single (i : m) (j : n) (a : α) :
    of.symm (single i j a) = Pi.single i (Pi.single j a) :=
  congr_arg of.symm <| single_eq_of_single_single i j a

@[deprecated (since := "2025-05-05")] alias of_symm_stdBasisMatrix := of_symm_single

@[simp]
theorem smul_single [SMulZeroClass R α] (r : R) (i : m) (j : n) (a : α) :
    r • single i j a = single i j (r • a) := by
  unfold single
  ext
  simp [smul_ite]

@[deprecated (since := "2025-05-05")] alias smul_stdBasisMatrix := smul_single

@[simp]
theorem single_zero (i : m) (j : n) : single i j (0 : α) = 0 := by
  unfold single
  ext
  simp

@[deprecated (since := "2025-05-05")] alias stdBasisMatrix_zero := single_zero

@[simp]
lemma transpose_single (i : m) (j : n) (a : α) :
    (single i j a)ᵀ = single j i a := by
  aesop (add unsafe unfold single)

@[deprecated (since := "2025-05-05")] alias transpose_stdBasisMatrix := transpose_single

@[simp]
lemma map_single (i : m) (j : n) (a : α) {β : Type*} [Zero β]
    {F : Type*} [FunLike F α β] [ZeroHomClass F α β] (f : F) :
    (single i j a).map f = single i j (f a) := by
  aesop (add unsafe unfold single)

@[deprecated (since := "2025-05-05")] alias map_stdBasisMatrix := map_single

theorem single_mem_matrix {S : Set α} (hS : 0 ∈ S) {i : m} {j : n} {a : α} :
    Matrix.single i j a ∈ S.matrix ↔ a ∈ S := by
  simp only [Set.mem_matrix, single, of_apply]
  conv_lhs => intro _ _; rw [ite_mem]
  simp [hS]

end Zero

theorem single_add [AddZeroClass α] (i : m) (j : n) (a b : α) :
    single i j (a + b) = single i j a + single i j b := by
  ext
  simp only [single, of_apply]
  split_ifs with h <;> simp [h]

@[deprecated (since := "2025-05-05")] alias stdBasisMatrix_add := single_add

theorem single_mulVec [NonUnitalNonAssocSemiring α] [Fintype m]
    (i : n) (j : m) (c : α) (x : m → α) :
    mulVec (single i j c) x = Function.update (0 : n → α) i (c * x j) := by
  ext i'
  simp [single, mulVec, dotProduct]
  rcases eq_or_ne i i' with rfl | h
  · simp
  simp [h, h.symm]

@[deprecated (since := "2025-05-05")] alias mulVec_stdBasisMatrix := single_mulVec

theorem matrix_eq_sum_single [AddCommMonoid α] [Fintype m] [Fintype n] (x : Matrix m n α) :
    x = ∑ i : m, ∑ j : n, single i j (x i j) := by
  ext i j
  rw [← Fintype.sum_prod_type']
  simp [single, Matrix.sum_apply, Matrix.of_apply, ← Prod.mk_inj]

@[deprecated (since := "2025-05-05")] alias matrix_eq_sum_stdBasisMatrix := matrix_eq_sum_single

theorem single_eq_single_vecMulVec_single [MulZeroOneClass α] (i : m) (j : n) :
    single i j (1 : α) = vecMulVec (Pi.single i 1) (Pi.single j 1) := by
  ext i' j'
  simp [-mul_ite, single, vecMulVec, ite_and, Pi.single_apply, eq_comm]

@[deprecated (since := "2025-05-05")]
alias stdBasisMatrix_eq_single_vecMulVec_single := single_eq_single_vecMulVec_single

-- todo: the old proof used fintypes, I don't know `Finsupp` but this feels generalizable
@[elab_as_elim]
protected theorem induction_on'
    [AddCommMonoid α] [Finite m] [Finite n] {P : Matrix m n α → Prop} (M : Matrix m n α)
    (h_zero : P 0) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ (i : m) (j : n) (x : α), P (single i j x)) : P M := by
  cases nonempty_fintype m; cases nonempty_fintype n
  rw [matrix_eq_sum_single M, ← Finset.sum_product']
  apply Finset.sum_induction _ _ h_add h_zero
  · intros
    apply h_std_basis

@[elab_as_elim]
protected theorem induction_on
    [AddCommMonoid α] [Finite m] [Finite n] [Nonempty m] [Nonempty n]
    {P : Matrix m n α → Prop} (M : Matrix m n α) (h_add : ∀ p q, P p → P q → P (p + q))
    (h_std_basis : ∀ i j x, P (single i j x)) : P M :=
  Matrix.induction_on' M
    (by
      inhabit m
      inhabit n
      simpa using h_std_basis default default 0)
    h_add h_std_basis

/-- `Matrix.single` as a bundled additive map. -/
@[simps]
def singleAddMonoidHom [AddCommMonoid α] (i : m) (j : n) : α →+ Matrix m n α where
  toFun := single i j
  map_zero' := single_zero _ _
  map_add' _ _ := single_add _ _ _ _

@[deprecated (since := "2025-05-05")] alias stdBasisMatrixAddMonoidHom := singleAddMonoidHom

variable (R)
/-- `Matrix.single` as a bundled linear map. -/
@[simps!]
def singleLinearMap [Semiring R] [AddCommMonoid α] [Module R α] (i : m) (j : n) :
    α →ₗ[R] Matrix m n α where
  __ := singleAddMonoidHom i j
  map_smul' _ _:= smul_single _ _ _ _ |>.symm

@[deprecated (since := "2025-05-05")] alias stdBasisMatrixLinearMap := singleLinearMap

section ext

/-- Additive maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
theorem ext_addMonoidHom
    [Finite m] [Finite n] [AddCommMonoid α] [AddCommMonoid β] ⦃f g : Matrix m n α →+ β⦄
    (h : ∀ i j, f.comp (singleAddMonoidHom i j) = g.comp (singleAddMonoidHom i j)) :
    f = g := by
  cases nonempty_fintype m
  cases nonempty_fintype n
  ext x
  rw [matrix_eq_sum_single x]
  simp_rw [map_sum]
  congr! 2
  exact DFunLike.congr_fun (h _ _) _

/-- Linear maps from finite matrices are equal if they agree on the standard basis.

See note [partially-applied ext lemmas]. -/
@[local ext]
theorem ext_linearMap
    [Finite m] [Finite n] [Semiring R] [AddCommMonoid α] [AddCommMonoid β] [Module R α] [Module R β]
    ⦃f g : Matrix m n α →ₗ[R] β⦄
    (h : ∀ i j, f ∘ₗ singleLinearMap R i j = g ∘ₗ singleLinearMap R i j) :
    f = g :=
  LinearMap.toAddMonoidHom_injective <| ext_addMonoidHom fun i j =>
    congrArg LinearMap.toAddMonoidHom <| h i j

section liftLinear
variable {R} (S)
variable [Fintype m] [Fintype n] [Semiring R] [Semiring S] [AddCommMonoid α] [AddCommMonoid β]
variable [Module R α] [Module R β] [Module S β] [SMulCommClass R S β]

/-- Families of linear maps acting on each element are equivalent to linear maps from a matrix.

This can be thought of as the matrix version of `LinearMap.lsum`. -/
def liftLinear : (m → n → α →ₗ[R] β) ≃ₗ[S] (Matrix m n α →ₗ[R] β) :=
  LinearEquiv.piCongrRight (fun _ => LinearMap.lsum R _ S) ≪≫ₗ LinearMap.lsum R _ S ≪≫ₗ
    LinearEquiv.congrLeft _ _ (ofLinearEquiv _)

-- not `simp` to let `liftLinear_single` fire instead
theorem liftLinear_apply (f : m → n → α →ₗ[R] β) (M : Matrix m n α) :
    liftLinear S f M = ∑ i, ∑ j, f i j (M i j) := by
  simp [liftLinear, map_sum, LinearEquiv.congrLeft]

@[simp]
theorem liftLinear_single (f : m → n → α →ₗ[R] β) (i : m) (j : n) (a : α) :
    liftLinear S f (Matrix.single i j a) = f i j a := by
  dsimp [liftLinear, -LinearMap.lsum_apply, LinearEquiv.congrLeft, LinearEquiv.piCongrRight]
  simp_rw [of_symm_single, LinearMap.lsum_piSingle]

@[deprecated (since := "2025-08-13")] alias liftLinear_piSingle := liftLinear_single

@[simp]
theorem liftLinear_comp_singleLinearMap (f : m → n → α →ₗ[R] β) (i : m) (j : n) :
    liftLinear S f ∘ₗ Matrix.singleLinearMap _ i j = f i j :=
  LinearMap.ext <| liftLinear_single S f i j

@[simp]
theorem liftLinear_singleLinearMap [Module S α] [SMulCommClass R S α] :
    liftLinear S (Matrix.singleLinearMap R) = .id (M := Matrix m n α) :=
  ext_linearMap _ <| liftLinear_comp_singleLinearMap _ _

end liftLinear

end ext

section

variable [Zero α] (i : m) (j : n) (c : α) (i' : m) (j' : n)

@[simp]
theorem single_apply_same : single i j c i j = c :=
  if_pos (And.intro rfl rfl)

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.apply_same := single_apply_same

@[simp]
theorem single_apply_of_ne (h : ¬(i = i' ∧ j = j')) : single i j c i' j' = 0 := by
  simp only [single, and_imp, ite_eq_right_iff, of_apply]
  tauto

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.apply_of_ne := single_apply_of_ne

theorem single_apply_of_row_ne {i i' : m} (hi : i ≠ i') (j j' : n) (a : α) :
    single i j a i' j' = 0 := by simp [hi]

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.apply_of_row_ne := single_apply_of_row_ne

theorem single_apply_of_col_ne (i i' : m) {j j' : n} (hj : j ≠ j') (a : α) :
    single i j a i' j' = 0 := by simp [hj]

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.apply_of_col_ne := single_apply_of_col_ne

end

section
variable [Zero α] (i j : n) (c : α)

-- This simp lemma should take priority over `diag_apply`
@[simp 1050]
theorem diag_single_of_ne (h : i ≠ j) : diag (single i j c) = 0 :=
  funext fun _ => if_neg fun ⟨e₁, e₂⟩ => h (e₁.trans e₂.symm)

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.diag_zero := diag_single_of_ne

-- This simp lemma should take priority over `diag_apply`
@[simp 1050]
theorem diag_single_same : diag (single i i c) = Pi.single i c := by
  ext j
  by_cases hij : i = j <;> (try rw [hij]) <;> simp [hij]

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.diag_same := diag_single_same

end

section mul
variable [Fintype m] [NonUnitalNonAssocSemiring α] (c : α)

omit [DecidableEq n] in
@[simp]
theorem single_mul_apply_same (i : l) (j : m) (b : n) (M : Matrix m n α) :
    (single i j c * M) i b = c * M j b := by simp [mul_apply, single]

@[deprecated (since := "2025-05-05")]
alias StdBasisMatrix.mul_left_apply_same := single_mul_apply_same

omit [DecidableEq l] in
@[simp]
theorem mul_single_apply_same (i : m) (j : n) (a : l) (M : Matrix l m α) :
    (M * single i j c) a j = M a i * c := by simp [mul_apply, single]

@[deprecated (since := "2025-05-05")]
alias StdBasisMatrix.mul_right_apply_same := mul_single_apply_same

omit [DecidableEq n] in
@[simp]
theorem single_mul_apply_of_ne (i : l) (j : m) (a : l) (b : n) (h : a ≠ i) (M : Matrix m n α) :
    (single i j c * M) a b = 0 := by simp [mul_apply, h.symm]

@[deprecated (since := "2025-05-05")]
alias StdBasisMatrix.mul_left_apply_of_ne := single_mul_apply_of_ne

omit [DecidableEq l] in
@[simp]
theorem mul_single_apply_of_ne (i : m) (j : n) (a : l) (b : n) (hbj : b ≠ j) (M : Matrix l m α) :
    (M * single i j c) a b = 0 := by simp [mul_apply, hbj.symm]

@[deprecated (since := "2025-05-05")]
alias StdBasisMatrix.mul_right_apply_of_ne := mul_single_apply_of_ne

@[simp]
theorem single_mul_single_same (i : l) (j : m) (k : n) (d : α) :
    single i j c * single j k d = single i k (c * d) := by
  ext a b
  simp only [mul_apply, single]
  by_cases h₁ : i = a <;> by_cases h₂ : k = b <;> simp [h₁, h₂]

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.mul_same := single_mul_single_same

@[simp]
theorem single_mul_mul_single [Fintype n]
    (i : l) (i' : m) (j' : n) (j : o) (a : α) (x : Matrix m n α) (b : α) :
    single i i' a * x * single j' j b = single i j (a * x i' j' * b) := by
  ext i'' j''
  simp only [mul_apply, single]
  by_cases h₁ : i = i'' <;> by_cases h₂ : j = j'' <;> simp [h₁, h₂]

@[deprecated (since := "2025-05-05")]
alias StdBasisMatrix.stdBasisMatrix_mul_mul_stdBasisMatrix := single_mul_mul_single

@[simp]
theorem single_mul_single_of_ne (i : l) (j k : m) {l : n} (h : j ≠ k) (d : α) :
    single i j c * single k l d = 0 := by
  ext a b
  simp only [mul_apply, single, of_apply]
  by_cases h₁ : i = a
  · simp [h₁, h, Finset.sum_eq_zero]
  · simp [h₁]

@[deprecated (since := "2025-05-05")] alias StdBasisMatrix.mul_of_ne := single_mul_single_of_ne

end mul

section Commute

variable [Fintype n] [Semiring α]

theorem row_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) (hkj : k ≠ j) : M j k = 0 := by
  have := ext_iff.mpr hM i k
  aesop

@[deprecated (since := "2025-05-05")]
alias row_eq_zero_of_commute_stdBasisMatrix := row_eq_zero_of_commute_single

theorem col_eq_zero_of_commute_single {i j k : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) (hki : k ≠ i) : M k i = 0 := by
  have := ext_iff.mpr hM k j
  aesop

@[deprecated (since := "2025-05-05")]
alias col_eq_zero_of_commute_stdBasisMatrix := col_eq_zero_of_commute_single

theorem diag_eq_of_commute_single {i j : n} {M : Matrix n n α}
    (hM : Commute (single i j 1) M) : M i i = M j j := by
  have := ext_iff.mpr hM i j
  aesop

@[deprecated (since := "2025-05-05")]
alias diag_eq_of_commute_stdBasisMatrix := diag_eq_of_commute_single

/-- `M` is a scalar matrix if it commutes with every non-diagonal `single`. -/
theorem mem_range_scalar_of_commute_single {M : Matrix n n α}
    (hM : Pairwise fun i j => Commute (single i j 1) M) :
    M ∈ Set.range (Matrix.scalar n) := by
  cases isEmpty_or_nonempty n
  · exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨i⟩ := ‹Nonempty n›
  refine ⟨M i i, Matrix.ext fun j k => ?_⟩
  simp only [scalar_apply]
  obtain rfl | hkl := Decidable.eq_or_ne j k
  · rw [diagonal_apply_eq]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rfl
    · exact diag_eq_of_commute_single (hM hij)
  · rw [diagonal_apply_ne _ hkl]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [col_eq_zero_of_commute_single (hM hkl.symm) hkl]
    · rw [row_eq_zero_of_commute_single (hM hij) hkl.symm]

@[deprecated (since := "2025-05-05")]
alias mem_range_scalar_of_commute_stdBasisMatrix := mem_range_scalar_of_commute_single

theorem mem_range_scalar_iff_commute_single {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), i ≠ j → Commute (single i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j _ => hr ▸ Commute.symm ?_, mem_range_scalar_of_commute_single⟩
  rw [scalar_commute_iff]
  simp

@[deprecated (since := "2025-05-05")]
alias mem_range_scalar_iff_commute_stdBasisMatrix := mem_range_scalar_iff_commute_single

/-- `M` is a scalar matrix if and only if it commutes with every `single`. -/
theorem mem_range_scalar_iff_commute_single' {M : Matrix n n α} :
    M ∈ Set.range (Matrix.scalar n) ↔ ∀ (i j : n), Commute (single i j 1) M := by
  refine ⟨fun ⟨r, hr⟩ i j => hr ▸ Commute.symm ?_,
    fun hM => mem_range_scalar_iff_commute_single.mpr <| fun i j _ => hM i j⟩
  rw [scalar_commute_iff]
  simp

@[deprecated (since := "2025-05-05")]
alias mem_range_scalar_iff_commute_stdBasisMatrix' := mem_range_scalar_iff_commute_single'

end Commute

end Matrix
