/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

variable {m n R A : Type*} [NonUnitalNonAssocSemiring R] [Finite m] [Finite n] (M : Matrix m n R)

attribute [local instance] Fintype.ofFinite

/-- A matrix `M` is right-separating if for all `w ≠ 0`, there is a `v` with `v * M * w ≠ 0`. -/
def SeparatingRight : Prop :=
  (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0)

/-- A matrix `M` is right-separating if for all `v ≠ 0`, there is a `w` with `v * M * w ≠ 0`. -/
def SeparatingLeft : Prop :=
  (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0)

/-- A matrix `M` is nondegenerate if it is both left-separating and right-separating. -/
@[mk_iff]
structure Nondegenerate (M : Matrix m n R) : Prop where
  separatingLeft : SeparatingLeft M
  separatingRight : SeparatingRight M

end Finite

variable {m n R : Type*} [CommRing R] {M : Matrix m n R}

lemma separatingRight_def [Fintype m] [Fintype n] :
    M.SeparatingRight ↔ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  refine forall_congr' fun w ↦ ⟨fun hM hw ↦ hM ?_, fun hM hw ↦ hM ?_⟩ <;>
  convert! hw

lemma separatingLeft_def [Fintype m] [Fintype n] :
    M.SeparatingLeft ↔ (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) := by
  refine forall_congr' fun v ↦ ⟨fun hM hv ↦ hM ?_, fun hM hv ↦ hM ?_⟩ <;>
  convert! hv

lemma nondegenerate_def [Fintype m] [Fintype n] :
    M.Nondegenerate ↔
      (∀ v, (∀ w, v ⬝ᵥ M *ᵥ w = 0) → v = 0) ∧ (∀ w, (∀ v, v ⬝ᵥ M *ᵥ w = 0) → w = 0) := by
  constructor
  · exact fun h ↦ ⟨separatingLeft_def.mp h.1, separatingRight_def.mp h.2⟩
  · exact fun h ↦ ⟨separatingLeft_def.mpr h.1, separatingRight_def.mpr h.2⟩

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

@[simp]
theorem separatingLeft_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingLeft ↔ M.SeparatingRight := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingLeft_def, separatingRight_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingRight.transpose⟩ := separatingLeft_transpose_iff

@[simp]
theorem separatingRight_transpose_iff [Finite m] [Finite n] :
    Mᵀ.SeparatingRight ↔ M.SeparatingLeft := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  simp_rw [separatingRight_def, separatingLeft_def, dotProduct_transpose_mulVec]

alias ⟨_, SeparatingLeft.transpose⟩ := separatingRight_transpose_iff

@[simp]
theorem nondegenerate_transpose_iff [Finite m] [Finite n] : Mᵀ.Nondegenerate ↔ M.Nondegenerate := by
  rw [nondegenerate_iff, nondegenerate_iff, separatingLeft_transpose_iff,
    separatingRight_transpose_iff, and_comm]

alias ⟨_, Nondegenerate.transpose⟩ := nondegenerate_transpose_iff

variable [Fintype m] [Fintype n]

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

section Determinant
open scoped nonZeroDivisors
variable [DecidableEq m] {M : Matrix m m R}

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
theorem nondegenerate_of_det_ne_zero [NoZeroDivisors R] (hM : M.det ≠ 0) : M.Nondegenerate :=
  .of_det_mem_nonZeroDivisors <| mem_nonZeroDivisors_of_ne_zero hM

theorem eq_zero_of_vecMul_eq_zero_of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰)
    {v : m → R} (hv : v ᵥ* M = 0) : v = 0 :=
  Nondegenerate.of_det_mem_nonZeroDivisors hM |>.separatingLeft.eq_zero_of_vecMul_eq_zero hv

theorem eq_zero_of_vecMul_eq_zero [NoZeroDivisors R] (hM : M.det ≠ 0) {v : m → R}
    (hv : v ᵥ* M = 0) : v = 0 :=
  nondegenerate_of_det_ne_zero hM |>.separatingLeft.eq_zero_of_vecMul_eq_zero hv

theorem eq_zero_of_mulVec_eq_zero_of_det_mem_nonZeroDivisors (hM : M.det ∈ R⁰)
    {v : m → R} (hv : M *ᵥ v = 0) : v = 0 :=
  Nondegenerate.of_det_mem_nonZeroDivisors hM |>.separatingRight.eq_zero_of_mulVec_eq_zero hv

theorem eq_zero_of_mulVec_eq_zero [NoZeroDivisors R] (hM : M.det ≠ 0) {v : m → R}
    (hv : M *ᵥ v = 0) : v = 0 :=
  nondegenerate_of_det_ne_zero hM |>.separatingRight.eq_zero_of_mulVec_eq_zero hv

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
    simpa [Matrix.dotProduct_mulVec] using congr_arg (fun x ↦ dotProduct x w') hv
  exact hA.eq_zero_of_ortho hv
