/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Algebra.Star.Pi
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Matrices associated with non-degenerate bilinear forms

## Main definitions

* `Matrix.Nondegenerate A`: the proposition that when interpreted as a bilinear form, the matrix `A`
  is nondegenerate.
-/

@[expose] public section


namespace Matrix

section Finite

variable {m n R A : Type*} [NonUnitalSemiring R] [Finite m] [Finite n] (M : Matrix m n R)

attribute [local instance] Fintype.ofFinite

/-- A matrix `M` is right-separating if for all `w ≠ 0`, there is a `v` with `v * M * w ≠ 0`. -/
def SeparatingRight : Prop :=
  (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0)

/-- A matrix `M` is right-separating if for all `v ≠ 0`, there is a `w` with `v * M * w ≠ 0`. -/
def SeparatingLeft : Prop :=
  (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0)

/-- A matrix `M` is nondegenerate if it is both left-separating and right-separating.

See also `Matrix.Nonsingular`. -/
@[mk_iff]
structure Nondegenerate (M : Matrix m n R) : Prop where
  separatingLeft : SeparatingLeft M
  separatingRight : SeparatingRight M

end Finite

section NonUnitalSemiring

section Fintype
variable {m n R : Type*} [Fintype m] [Fintype n] [NonUnitalSemiring R]
variable {M : Matrix m n R}

lemma separatingRight_def : M.SeparatingRight ↔ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  refine forall_congr' fun w ↦ ⟨fun hM hw ↦ hM ?_, fun hM hw ↦ hM ?_⟩ <;>
  convert hw

lemma separatingLeft_def : M.SeparatingLeft ↔ (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) := by
  refine forall_congr' fun v ↦ ⟨fun hM hv ↦ hM ?_, fun hM hv ↦ hM ?_⟩ <;>
  convert hv

lemma nondegenerate_def :
    M.Nondegenerate ↔
      (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) ∧ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  rw [nondegenerate_iff, separatingLeft_def, separatingRight_def]

/-- If `M` is nondegenerate and `w * M * v = 0` for all `w`, then `v = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho (hM : Nondegenerate M) {v : m → R}
    (hv : ∀ w, v ⬝ᵥ M *ᵥ w = 0) : v = 0 :=
  (nondegenerate_def.mp hM).1 v hv

/-- If `M` is nondegenerate and `v ≠ 0`, then there is some `w` such that `w * M * v ≠ 0`. -/
theorem Nondegenerate.exists_not_ortho_of_ne_zero (hM : Nondegenerate M)
    {v : m → R} (hv : v ≠ 0) : ∃ w, v ⬝ᵥ M *ᵥ w ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho hv)

/-- If `M` is nondegenerate and `w * M * v = 0` for all `v`, then `w = 0`. -/
theorem Nondegenerate.eq_zero_of_ortho' (hM : Nondegenerate M) {w : n → R}
    (hw : ∀ v, v ⬝ᵥ M *ᵥ w = 0) : w = 0 :=
  (nondegenerate_def.mp hM).2 w hw

/-- If `M` is nondegenerate and `w ≠ 0`, then there is some `v` such that `v * M * w ≠ 0`. -/
theorem Nondegenerate.exists_not_ortho_of_ne_zero' (hM : Nondegenerate M) {w : n → R} (hw : w ≠ 0) :
    ∃ v, v ⬝ᵥ M *ᵥ w ≠ 0 :=
  not_forall.mp (mt hM.eq_zero_of_ortho' hw)

end Fintype

section Finite
variable {k l m n R : Type*} [Finite k] [Finite l] [Finite m] [Finite n] [NonUnitalSemiring R]
variable {M : Matrix m n R} {r : k → m} {c : l → n}

@[simp]
theorem separatingLeft_conjTranspose_iff [StarRing R] :
    Mᴴ.SeparatingLeft ↔ M.SeparatingRight := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingLeft_def, separatingRight_def]
  rw [star_involutive.surjective.forall]
  congr! 1 with v
  rw [star_involutive.surjective.forall]
  simp [star_eq_zero, ← star_vecMul, star_dotProduct_star, dotProduct_mulVec]

alias ⟨_, SeparatingRight.separatingLeft_conTranspose⟩ := separatingLeft_conjTranspose_iff

@[simp]
theorem separatingRight_conjTranspose_iff [StarRing R] :
    Mᴴ.SeparatingRight ↔ M.SeparatingLeft := by
  rw [← separatingLeft_conjTranspose_iff, conjTranspose_conjTranspose]

alias ⟨_, SeparatingLeft.separatingRight_conjTranspose⟩ := separatingRight_conjTranspose_iff

@[simp]
theorem nondegenerate_conjTranspose_iff [StarRing R] :
    Mᴴ.Nondegenerate ↔ M.Nondegenerate := by
  simp [nondegenerate_iff, and_comm]

alias ⟨_, Nondegenerate.conjTranspose⟩ := nondegenerate_conjTranspose_iff

theorem separatingLeft_map_op_iff :
    (M.map MulOpposite.op).SeparatingLeft ↔ Mᵀ.SeparatingRight := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  rw [separatingLeft_def, separatingRight_def]
  let em : (m → Rᵐᵒᵖ) ≃ (m → R) := Equiv.piCongrRight fun _ ↦ MulOpposite.opEquiv.symm
  let en : (n → Rᵐᵒᵖ) ≃ (n → R) := Equiv.piCongrRight fun _ ↦ MulOpposite.opEquiv.symm
  refine em.forall_congr_left.trans <| forall_congr' fun w ↦ ?_
  rw [en.forall_congr_left]
  refine imp_congr (forall_congr' fun v ↦ ?_) (by simp [em, funext_iff])
  rw [← MulOpposite.op_eq_zero_iff (a := v ⬝ᵥ Mᵀ *ᵥ w), dotProduct_mulVec]
  simp [em, en, dotProduct, mulVec, vecMul]

theorem separatingRight_map_op_iff :
    (M.map MulOpposite.op).SeparatingRight ↔ Mᵀ.SeparatingLeft := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  rw [separatingRight_def, separatingLeft_def]
  let em : (m → Rᵐᵒᵖ) ≃ (m → R) := Equiv.piCongrRight fun _ ↦ MulOpposite.opEquiv.symm
  let en : (n → Rᵐᵒᵖ) ≃ (n → R) := Equiv.piCongrRight fun _ ↦ MulOpposite.opEquiv.symm
  refine en.forall_congr_left.trans <| forall_congr' fun w ↦ ?_
  rw [em.forall_congr_left]
  refine imp_congr (forall_congr' fun v ↦ ?_) (by simp [en, funext_iff])
  rw [← MulOpposite.op_eq_zero_iff (a := w ⬝ᵥ Mᵀ *ᵥ v), dotProduct_mulVec]
  simp [em, en, dotProduct, mulVec, vecMul]

theorem nondegenerate_map_op_iff :
    (M.map MulOpposite.op).Nondegenerate ↔ Mᵀ.Nondegenerate := by
  simp [nondegenerate_iff, separatingLeft_map_op_iff, separatingRight_map_op_iff, and_comm]

/-- Auxiliary transfer lemma unifying `SeparatingRight.of_submatrix` and
`SeparatingRight.submatrix`: if `A.submatrix id s = B.submatrix r id` with `s` injective, then
`A.SeparatingRight` implies `B.SeparatingRight`. -/
private lemma SeparatingRight.of_submatrix_eq {A : Matrix k l R} {B : Matrix m n R}
    (r : k → m) {s : n → l} (hs : Function.Injective s) (hAB : A.submatrix id s = B.submatrix r id)
    (hA : A.SeparatingRight) : B.SeparatingRight := by
  classical
  have := Fintype.ofFinite k
  have := Fintype.ofFinite l
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  rw [separatingRight_def] at hA ⊢
  intro w hw
  suffices Function.extend s w 0 = 0 by
    ext y
    simpa [hs.extend_apply] using congr($this (s y))
  refine hA _ fun v ↦ ?_
  have hmul : A *ᵥ Function.extend s w 0 = (B *ᵥ w) ∘ r :=
    funext fun i ↦ (Fintype.sum_of_injective s hs _ _
      (fun j hj ↦ by simp [Function.extend_apply' _ _ _ hj])
      (fun y ↦ by simpa [hs.extend_apply] using congr(($hAB.symm i y) * w y))).symm
  have hv : (fun x ↦ ∑ i with r i = x, v i) ⬝ᵥ (B *ᵥ w) = v ⬝ᵥ (A *ᵥ Function.extend s w 0) := by
    rw [hmul]
    simp only [dotProduct, Finset.sum_mul, Function.comp_apply]
    refine (Finset.sum_congr rfl fun x _ ↦ Finset.sum_congr rfl fun i hi ↦ ?_).trans
      (Finset.univ.sum_fiberwise r fun i ↦ v i * (B *ᵥ w) (r i))
    rw [(Finset.mem_filter.mp hi).2]
  exact hv.symm.trans (hw _)

theorem SeparatingRight.of_submatrix (hc : Function.Surjective c)
    (h : (M.submatrix r c).SeparatingRight) : M.SeparatingRight :=
  h.of_submatrix_eq r (Function.injective_surjInv hc) (by ext; simp [Function.surjInv_eq hc])

theorem SeparatingRight.submatrix (hr : Function.Surjective r) (hc : Function.Injective c)
    (h : M.SeparatingRight) : (M.submatrix r c).SeparatingRight :=
  h.of_submatrix_eq (Function.surjInv hr) hc (by ext; simp [Function.surjInv_eq hr])

theorem separatingRight_submatrix_iff (hr : Function.Surjective r) (hc : Function.Bijective c) :
    (M.submatrix r c).SeparatingRight ↔ M.SeparatingRight :=
  ⟨.of_submatrix hc.surjective, .submatrix hr hc.injective⟩

theorem SeparatingLeft.of_submatrix (hr : Function.Surjective r)
    (h : (M.submatrix r c).SeparatingLeft) : M.SeparatingLeft :=
  separatingRight_map_op_iff.mp <|
    SeparatingRight.of_submatrix (M := Mᵀ.map MulOpposite.op) (r := c) (c := r) hr
      (separatingRight_map_op_iff.mpr h)

theorem SeparatingLeft.submatrix (hr : Function.Injective r) (hc : Function.Surjective c)
    (h : M.SeparatingLeft) : (M.submatrix r c).SeparatingLeft :=
  separatingRight_map_op_iff.mp <|
    SeparatingRight.submatrix (M := Mᵀ.map MulOpposite.op) (r := c) (c := r) hc hr
      (separatingRight_map_op_iff.mpr h)

theorem separatingLeft_submatrix_iff (hr : Function.Bijective r) (hc : Function.Surjective c) :
    (M.submatrix r c).SeparatingLeft ↔ M.SeparatingLeft :=
  ⟨.of_submatrix hr.surjective, .submatrix hr.injective hc⟩

theorem Nondegenerate.of_submatrix (hr : Function.Surjective r) (hc : Function.Surjective c)
    (h : (M.submatrix r c).Nondegenerate) : M.Nondegenerate :=
  ⟨h.1.of_submatrix hr, h.2.of_submatrix hc⟩

theorem Nondegenerate.submatrix (hr : Function.Bijective r) (hc : Function.Bijective c)
    (h : M.Nondegenerate) : (M.submatrix r c).Nondegenerate :=
  ⟨h.1.submatrix hr.injective hc.surjective, h.2.submatrix hr.surjective hc.injective⟩

theorem nondegenerate_submatrix_iff (hr : Function.Bijective r) (hc : Function.Bijective c) :
    (M.submatrix r c).Nondegenerate ↔ M.Nondegenerate :=
  ⟨.of_submatrix hr.surjective hc.surjective, .submatrix hr hc⟩

end Finite

end NonUnitalSemiring

section Semiring
variable {m n R : Type*} [Semiring R] {M : Matrix m n R}

theorem separatingLeft_iff_forall_vecMul_eq_zero [Fintype m] [Finite n] :
    M.SeparatingLeft ↔ ∀ v, v ᵥ* M = 0 → v = 0 := by
  have := Fintype.ofFinite n
  rw [separatingLeft_def]
  refine ⟨fun h v hv ↦ h v fun w ↦ ?_, fun h w hw ↦ h w <| funext fun i ↦ ?_⟩
  · simp [dotProduct_mulVec, hv]
  · classical simpa using! hw <| Pi.single i 1

theorem separatingRight_iff_forall_mulVec_eq_zero [Finite m] [Fintype n] :
    M.SeparatingRight ↔ ∀ v, M *ᵥ v = 0 → v = 0 := by
  have := Fintype.ofFinite m
  rw [separatingRight_def]
  refine ⟨fun h v hv ↦ h v fun w ↦ ?_, fun h w hw ↦ h w <| funext fun i ↦ ?_⟩
  · simp [hv]
  · classical simpa using hw <| Pi.single i 1

theorem SeparatingLeft.eq_zero_of_vecMul_eq_zero [Fintype m] [Finite n] (hM : M.SeparatingLeft)
    {v : m → R} (hv : v ᵥ* M = 0) : v = 0 :=
  separatingLeft_iff_forall_vecMul_eq_zero.mp hM v hv

theorem SeparatingRight.eq_zero_of_mulVec_eq_zero [Finite m] [Fintype n] (hM : M.SeparatingRight)
    {v : n → R} (hv : M *ᵥ v = 0) : v = 0 :=
  separatingRight_iff_forall_mulVec_eq_zero.mp hM v hv

theorem nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero [Fintype m] [Fintype n] :
    M.Nondegenerate ↔ (∀ v, v ᵥ* M = 0 → v = 0) ∧ (∀ v, M *ᵥ v = 0 → v = 0) := by
  rw [nondegenerate_iff, separatingLeft_iff_forall_vecMul_eq_zero,
    separatingRight_iff_forall_mulVec_eq_zero]

end Semiring

section NonUnitalCommSemiring
variable {m n R : Type*} [NonUnitalCommSemiring R] {M : Matrix m n R}

@[simp]
theorem separatingLeft_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingLeft ↔ M.SeparatingRight := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingLeft_def, separatingRight_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingRight.separatingLeft_transpose⟩ := separatingLeft_transpose_iff

@[simp]
theorem separatingRight_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingRight ↔ M.SeparatingLeft := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingRight_def, separatingLeft_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingLeft.separatingRight_transpose⟩ := separatingRight_transpose_iff

@[simp]
theorem nondegenerate_transpose_iff [Finite m] [Finite n] : Mᵀ.Nondegenerate ↔ M.Nondegenerate := by
  simp [nondegenerate_iff, and_comm]

alias ⟨_, Nondegenerate.transpose⟩ := nondegenerate_transpose_iff

end NonUnitalCommSemiring

section Determinant
variable {m R : Type*} [CommRing R] [Fintype m] [DecidableEq m] {M : Matrix m m R}

open scoped nonZeroDivisors

private theorem SeparatingLeft.of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰) : M.SeparatingLeft := by
  refine separatingLeft_def.mpr fun v h ↦ funext fun i ↦ mem_nonZeroDivisors_iff_left.mp hM _ ?_
  simpa using h <| M.cramer <| Pi.single i 1

theorem Nondegenerate.of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰) : M.Nondegenerate where
  separatingLeft := .of_det_mem_nonZeroDivisors hM
  separatingRight := separatingLeft_transpose_iff.mp <| .of_det_mem_nonZeroDivisors <| by simpa

/-- If `M` is square and has nonzero determinant, then `M` as a bilinear form on `n → R` is
nondegenerate. The "iff" implication, `nondegenerate_iff_det_ne_zero`, is proved in a later file.

See also `BilinForm.nondegenerateOfDetNeZero'` and `BilinForm.nondegenerateOfDetNeZero`.
-/
theorem Nondegenerate.of_det_ne_zero [NoZeroDivisors R] (hM : M.det ≠ 0) : M.Nondegenerate :=
  .of_det_mem_nonZeroDivisors <| mem_nonZeroDivisors_of_ne_zero hM

@[deprecated (since := "2026-11-13")] alias nondegenerate_of_det_ne_zero :=
  Nondegenerate.of_det_ne_zero

theorem eq_zero_of_det_mem_nonZeroDivisors_of_vecMul_eq_zero (hM : M.det ∈ R⁰)
    {v : m → R} (hv : v ᵥ* M = 0) : v = 0 :=
  Nondegenerate.of_det_mem_nonZeroDivisors hM |>.separatingLeft.eq_zero_of_vecMul_eq_zero hv

theorem eq_zero_of_vecMul_eq_zero [NoZeroDivisors R] (hM : M.det ≠ 0) {v : m → R}
    (hv : v ᵥ* M = 0) : v = 0 :=
  Nondegenerate.of_det_ne_zero hM |>.separatingLeft.eq_zero_of_vecMul_eq_zero hv

theorem eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero (hM : M.det ∈ R⁰)
    {v : m → R} (hv : M *ᵥ v = 0) : v = 0 :=
  Nondegenerate.of_det_mem_nonZeroDivisors hM |>.separatingRight.eq_zero_of_mulVec_eq_zero hv

theorem eq_zero_of_mulVec_eq_zero [NoZeroDivisors R] (hM : M.det ≠ 0) {v : m → R}
    (hv : M *ᵥ v = 0) : v = 0 :=
  Nondegenerate.of_det_ne_zero hM |>.separatingRight.eq_zero_of_mulVec_eq_zero hv

/-- See also `Matrix.mulVec_injective_iff_isUnit` when working over a field. -/
theorem mulVec_injective_of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰) :
    Function.Injective M.mulVec :=
  fun _ _ hxy => sub_eq_zero.mp
    (eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hM (by rw [mulVec_sub, hxy, sub_self]))

theorem mulVec_injective_of_det_ne_zero [NoZeroDivisors R] (hM : M.det ≠ 0) :
    Function.Injective M.mulVec :=
  mulVec_injective_of_det_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hM)

end Determinant

end Matrix

open scoped Matrix in
lemma LinearIndependent.sum_smul_of_nondegenerate
    {ι κ R M : Type*} [Fintype ι] [Finite κ] [CommRing R] [AddCommGroup M] [Module R M]
    {v : ι → M} (hv : LinearIndependent R v)
    {A : Matrix κ ι R} (hA : A.Nondegenerate) :
    LinearIndependent R fun i ↦ ∑ j, A i j • v j := by
  have : Fintype κ := Fintype.ofFinite _
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro w hw
  suffices w = 0 by aesop
  simp_rw [Finset.smul_sum, ← smul_assoc] at hw
  rw [Finset.sum_comm] at hw
  simp_rw [← Finset.sum_smul] at hw
  replace hv : w ᵥ* A = 0 := funext <| hv _ hw
  replace hv (w' : ι → R) : w ⬝ᵥ A *ᵥ w' = 0 := by
    simpa [Matrix.dotProduct_mulVec] using congr(dotProduct $hv w')
  exact hA.eq_zero_of_ortho hv
