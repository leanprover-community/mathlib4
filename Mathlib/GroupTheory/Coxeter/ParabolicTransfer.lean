/-
Copyright (c) 2026 Johnathon Kyle Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johnathon Kyle Armstrong
-/
module

public import Mathlib.GroupTheory.Coxeter.ReflectionSystem
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Subdiagram relation transfer for reflection systems

Let `B : Matrix ι ι K` be a matrix over a field `K` and let `f : κ → ι` select a subset of
indices, giving the induced submatrix `B.submatrix f f : Matrix κ κ K`.

For any word `w : List κ`, the product of the reflections `reflectionMatrix B (f a)` in the
ambient space has the form `1 + E * C * R`, while the product of the reflections
`reflectionMatrix (B.submatrix f f) a` in the subdiagram has the form `1 + C * B.submatrix f f`
with the *same* coefficient matrix `C : Matrix κ κ K` (where `E` is the coordinate embedding
`K^κ → K^ι` and `R = B.submatrix f id`).

This yields two relation-transfer theorems between a reflection system and its induced
subdiagrams:
* `ReflectionSystem.prod_map_reflectionMatrix_eq_of_submatrix`: if `(B.submatrix f f).det ≠ 0`,
  then every relation holding in the subdiagram holds in the ambient reflection system.
* `ReflectionSystem.prod_map_reflectionMatrix_submatrix_eq_of_map`: if `f` is injective (with no
  nondegeneracy hypothesis on `B.submatrix f f`), then every relation among the ambient
  reflections `s_{f a}` already holds in the subdiagram.
* `ReflectionSystem.prod_map_reflectionMatrix_eq_iff_submatrix`: when `f` is injective and
  `(B.submatrix f f).det ≠ 0`, the relations among the ambient reflections `s_{f a}` coincide
  precisely with the relations of the induced subdiagram.

## Main definitions
* `ReflectionSystem.submatrix`: the induced `ReflectionSystem κ K` on a subdiagram `f : κ → ι`.

## Main results
* `ReflectionSystem.prod_map_reflectionMatrix_eq_of_submatrix`
* `ReflectionSystem.prod_map_reflectionMatrix_submatrix_eq_of_map`
* `ReflectionSystem.prod_map_reflectionMatrix_eq_iff_submatrix`

## References
* J. K. Armstrong, *Principal Elements of Mixed-Sign Coxeter Systems*, PhD thesis,
  Florida State University (2012), Section 3.3.
-/

open Matrix

@[expose] public section

namespace ReflectionSystem

variable {ι κ K : Type*} [Field K]

/-- The induced reflection system on a subdiagram selected by `f : κ → ι`. -/
def submatrix (S : ReflectionSystem ι K) (f : κ → ι) : ReflectionSystem κ K where
  B := S.B.submatrix f f
  B_symm := S.B_symm.submatrix f
  B_diag_ne_zero a := S.B_diag_ne_zero (f a)

@[simp]
lemma submatrix_B (S : ReflectionSystem ι K) (f : κ → ι) :
    (S.submatrix f).B = S.B.submatrix f f := rfl

section Transfer

variable [DecidableEq ι] [DecidableEq κ]

private def embedMat (f : κ → ι) : Matrix ι κ K :=
  Matrix.of fun r a ↦ if r = f a then 1 else 0

private def reflCoeff (B : Matrix ι ι K) (f : κ → ι) (a : κ) : Matrix κ κ K :=
  Matrix.of fun x y ↦ if x = a ∧ y = a then 2 / B (f a) (f a) else 0

variable [Fintype ι] [Fintype κ]

omit [DecidableEq κ] [Fintype κ] in
private lemma rows_mul_embedMat (B : Matrix ι ι K) (f : κ → ι) :
    B.submatrix f id * embedMat (K := K) f = B.submatrix f f := by
  ext b a
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id_eq, embedMat, Matrix.of_apply, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp

omit [Fintype κ] in
private lemma embedMat_transpose_mul (f : κ → ι) (hf : Function.Injective f) :
    (embedMat (K := K) f)ᵀ * embedMat (K := K) f = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, embedMat, Matrix.of_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  by_cases hab : a = b
  · simp [hab]
  · have : f b ≠ f a := fun h ↦ hab (hf h).symm
    simp [hab, this]

omit [Fintype ι] in
private lemma reflectionMatrix_comp_eq (B : Matrix ι ι K) (f : κ → ι) (a : κ) :
    reflectionMatrix B (f a) = 1 - embedMat f * reflCoeff B f a * B.submatrix f id := by
  ext r c
  simp only [reflectionMatrix_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    embedMat, reflCoeff, Matrix.of_apply, Matrix.submatrix_apply, id_eq]
  congr 1
  have hinner : ∀ y : κ,
      (∑ x : κ, (if r = f x then (1 : K) else 0) *
          (if x = a ∧ y = a then 2 / B (f a) (f a) else 0)) =
        if y = a then (if r = f a then 2 / B (f a) (f a) else 0) else 0 := by
    intro y
    rw [Finset.sum_eq_single a]
    · by_cases hy : y = a <;> by_cases hr : r = f a <;> simp [hy, hr]
    · intro x _ hx; simp [hx]
    · simp
  simp_rw [hinner]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hr : r = f a
  · simp [hr]; ring
  · simp [hr]

omit [DecidableEq ι] [Fintype ι] in
private lemma reflectionMatrix_sub_eq (B : Matrix ι ι K) (f : κ → ι) (a : κ) :
    reflectionMatrix (B.submatrix f f) a = 1 - reflCoeff B f a * B.submatrix f f := by
  ext x c
  simp only [reflectionMatrix_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    reflCoeff, Matrix.of_apply, Matrix.submatrix_apply]
  congr 1
  have hterm : ∀ y : κ,
      (if x = a ∧ y = a then 2 / B (f a) (f a) else 0) * B (f y) (f c) =
        if y = a then (if x = a then 2 / B (f a) (f a) * B (f a) (f c) else 0) else 0 := by
    intro y
    by_cases hy : y = a <;> by_cases hx : x = a <;> simp [hy, hx]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hx : x = a
  · simp [hx]; ring
  · simp [hx]

private lemma prod_map_reflectionMatrix_eq_one_add (B : Matrix ι ι K) (f : κ → ι) (w : List κ) :
    ∃ C : Matrix κ κ K,
      ((w.map f).map (reflectionMatrix B)).prod = 1 + embedMat f * C * B.submatrix f id ∧
      (w.map (reflectionMatrix (B.submatrix f f))).prod = 1 + C * B.submatrix f f := by
  induction w with
  | nil => exact ⟨0, by simp, by simp⟩
  | cons a t ih =>
    obtain ⟨C, h₁, h₂⟩ := ih
    refine ⟨C - reflCoeff B f a - reflCoeff B f a * B.submatrix f f * C, ?_, ?_⟩
    · simp only [List.map_cons, List.prod_cons, h₁, reflectionMatrix_comp_eq B f a]
      rw [← rows_mul_embedMat B f]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel
    · simp only [List.map_cons, List.prod_cons, h₂, reflectionMatrix_sub_eq B f a]
      simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
      abel

/-- If the induced submatrix `B.submatrix f f` is nonsingular (`det ≠ 0`), then every relation
among the generating reflections of `B.submatrix f f` also holds among the corresponding ambient
reflections `reflectionMatrix B (f a)`. -/
theorem prod_map_reflectionMatrix_eq_of_submatrix (B : Matrix ι ι K) (f : κ → ι)
    (hdet : (B.submatrix f f).det ≠ 0) (w w' : List κ)
    (h : (w.map (reflectionMatrix (B.submatrix f f))).prod =
      (w'.map (reflectionMatrix (B.submatrix f f))).prod) :
    ((w.map f).map (reflectionMatrix B)).prod = ((w'.map f).map (reflectionMatrix B)).prod := by
  obtain ⟨C, h₁, h₂⟩ := prod_map_reflectionMatrix_eq_one_add B f w
  obtain ⟨C', h₁', h₂'⟩ := prod_map_reflectionMatrix_eq_one_add B f w'
  rw [h₂, h₂'] at h
  have hCB : C * B.submatrix f f = C' * B.submatrix f f := add_left_cancel h
  have hunit : IsUnit (B.submatrix f f).det := isUnit_iff_ne_zero.mpr hdet
  have hCC : C = C' := by
    have := congr_arg (· * (B.submatrix f f)⁻¹) hCB
    simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit] using this
  rw [h₁, h₁', hCC]

/-- If `f : κ → ι` is injective (with no nondegeneracy hypothesis on `B.submatrix f f`), then
every relation among the ambient reflections `reflectionMatrix B (f a)` already holds among the
generating reflections of `B.submatrix f f`. -/
theorem prod_map_reflectionMatrix_submatrix_eq_of_map (B : Matrix ι ι K) (f : κ → ι)
    (hf : Function.Injective f) (w w' : List κ)
    (h : ((w.map f).map (reflectionMatrix B)).prod = ((w'.map f).map (reflectionMatrix B)).prod) :
    (w.map (reflectionMatrix (B.submatrix f f))).prod =
      (w'.map (reflectionMatrix (B.submatrix f f))).prod := by
  obtain ⟨C, h₁, h₂⟩ := prod_map_reflectionMatrix_eq_one_add B f w
  obtain ⟨C', h₁', h₂'⟩ := prod_map_reflectionMatrix_eq_one_add B f w'
  rw [h₁, h₁'] at h
  have hECR : embedMat f * C * B.submatrix f id = embedMat f * C' * B.submatrix f id :=
    add_left_cancel h
  have hE := embedMat_transpose_mul (K := K) f hf
  have hCR : C * B.submatrix f id = C' * B.submatrix f id := by
    have := congr_arg ((embedMat f)ᵀ * ·) hECR
    simpa [← Matrix.mul_assoc, hE] using this
  have hCB : C * B.submatrix f f = C' * B.submatrix f f := by
    rw [← rows_mul_embedMat B f, ← Matrix.mul_assoc, hCR, Matrix.mul_assoc]
  rw [h₂, h₂', hCB]

/-- For an injective `f : κ → ι` selecting a nonsingular submatrix `B.submatrix f f`, two words
define the same element in the ambient reflection group if and only if they define the same
element in the induced subdiagram reflection group. -/
theorem prod_map_reflectionMatrix_eq_iff_submatrix (B : Matrix ι ι K) (f : κ → ι)
    (hf : Function.Injective f) (hdet : (B.submatrix f f).det ≠ 0) (w w' : List κ) :
    ((w.map f).map (reflectionMatrix B)).prod = ((w'.map f).map (reflectionMatrix B)).prod ↔
      (w.map (reflectionMatrix (B.submatrix f f))).prod =
        (w'.map (reflectionMatrix (B.submatrix f f))).prod :=
  ⟨prod_map_reflectionMatrix_submatrix_eq_of_map B f hf w w',
    prod_map_reflectionMatrix_eq_of_submatrix B f hdet w w'⟩

end Transfer

end ReflectionSystem
