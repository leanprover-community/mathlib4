/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef

/-!
# TODO

-/

@[expose] public noncomputable section

namespace exteriorPower

open RealInnerProductSpace Matrix

def bilinForm (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) :
    ⋀[ℝ]^n E →ₗ[ℝ] ⋀[ℝ]^n E →ₗ[ℝ] ℝ :=
  pairingDual ℝ E n ∘ₗ map n (innerₗ E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

@[simp]
lemma bilinForm_ιMulti_ιMulti (x y : Fin n → E) :
    bilinForm E n (ιMulti ℝ n x) (ιMulti ℝ n y) = det (of fun i j ↦ ⟪x j, y i⟫) := by
  simp [bilinForm]

@[simp]
lemma bilinForm_ιMulti_self (x : Fin n → E) :
    bilinForm E n (ιMulti ℝ n x) (ιMulti ℝ n x) = det (gram ℝ x) := by
  simp_rw [bilinForm_ιMulti_ιMulti, gram, real_inner_comm]


lemma bilinForm_flip : LinearMap.flip (bilinForm E n) = bilinForm E n := by
  apply linearMap_ext
  ext
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.flip_apply, bilinForm_ιMulti_ιMulti]
  rw [← Matrix.det_transpose]
  congr 1
  ext
  exact real_inner_comm _ _

lemma bilinForm_symm (x y : ⋀[ℝ]^n E) : bilinForm E n x y = bilinForm E n y x :=
  congr($(bilinForm_flip) y x)

variable (ι : Type*) [Fintype ι] [LinearOrder ι] (b : OrthonormalBasis ι ℝ E)
variable (σ τ : Set.powersetCard ι n)

#check pairingDual_ιMulti_ιMulti
#check ιMulti_family_apply_coe
#check ExteriorAlgebra.ιMulti_family
#check gram
lemma bilinForm_basis_orthonormal (s t : Set.powersetCard ι n) :
    bilinForm E n (b.toBasis.exteriorPower n s) (b.toBasis.exteriorPower n t) =
      if s = t then 1 else 0 := by
  simp [bilinForm, ιMulti_family]
  #check b.orthonormal
  sorry

#check b.toBasis.exteriorPower n σ

variable (v : Fin n → E)
#check (Matrix.posSemidef_gram ℝ v).det_nonneg
#check Matrix.PosSemidef.det_nonneg
#check OrthonormalBasis

noncomputable instance : InnerProductSpace.Core ℝ (⋀[ℝ]^n E) where
  inner x y := bilinForm E n x y
  conj_inner_symm x y := bilinForm_symm y x
  add_left := by simp
  smul_left := by simp
  re_inner_nonneg x := by
    simp
    sorry
  definite x h := by
    sorry


#check innerₗ

