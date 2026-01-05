/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Standard subspaces of a Hilbert space

This files defines standard subspaces of a complex Hilbert space: a standard subspace `S` of `H` is
a closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`. For a standard subspace, one
can define a closable operator `x + i y ↦ x - i y` and develop an analogue of the Tomita-Takesaki
modular theory for von Neumann algebras. By considering inclusions of standard subspaces, one can
obtain unitary representations of various Lie groups.

## Main definitions and results

* `instance : InnerProductSpace ℝ H` for `InnerProductSpace ℂ H`, by restricting the scalar product
to its real part

* `StandardSubspace` as a structure with a `ClosedSubmodule` for `InnerProductSpace ℝ H` satisfying
`IsCyclic` and `IsSeparating`. Actually the interesting cases need `CompleteSpace H`, but the
definition is given for a general case.

* `symplComp` as a `StandardSubspace` of the symplectic complement of a standard subspace with
respect to `⟪⬝, ⬝⟫.im`

* `symplComp_symplComp_eq` the double symplectic complement is equal to itself

## References

* [Chap. 2 of Lecture notes by R. Longo](https://www.mat.uniroma2.it/longo/Lecture-Notes_files/LN-Part1.pdf)

* [Oberwolfach report](https://ems.press/content/serial-article-files/48171)

## TODO

Define the Tomita conjugation, prove Tomita's theorem, prove the KMS condition.
-/

@[expose] public section

open ContinuousLinearMap
open scoped ComplexInnerProductSpace

local instance : NeZero Complex.I := neZero_iff.mpr Complex.I_ne_zero

section ScalarSMulCLE

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- the scalar product by a non-zero complex number as a continuous real-linear equivalence. -/
noncomputable def scalarSMulCLE (c : ℂ) [h : NeZero c] : H ≃L[ℝ] H where
  toFun := lsmul ℂ ℂ c
  continuous_toFun := by
    have : Continuous (fun (x : H) => c • x) := continuous_const_smul c
    congr
  map_add' x y := by simp
  map_smul' a x := by
    exact smul_comm c a x
  invFun := lsmul ℂ ℂ c⁻¹
  left_inv := by
    exact fun x => inv_smul_smul₀ h.out x
  right_inv := by
    exact fun x => smul_inv_smul₀ h.out x
  continuous_invFun := by
    have : Continuous (fun (x : H) => c⁻¹ • x) := continuous_const_smul c⁻¹
    congr

@[simp]
lemma scalarSMulCLE_apply (c : ℂ) [NeZero c] (x : H) : scalarSMulCLE H c x = c • x := rfl

@[simp]
lemma scalarSMulCLE_symm_apply (c : ℂ) [NeZero c] (x : H) :
    (scalarSMulCLE H c).symm x = c⁻¹ • x := rfl

end ScalarSMulCLE

section RestrictScalar

variable {H : Type*} [NormedAddCommGroup H] [ipc : InnerProductSpace ℂ H]

noncomputable instance : InnerProductSpace ℝ H where
  inner x y := ⟪x, y⟫.re
  norm_sq_eq_re_inner x := by
    simp only [RCLike.re_to_real, ipc.norm_sq_eq_re_inner]
    exact rfl
  conj_inner_symm x y := by
    simp only [← ipc.conj_inner_symm x y, conj_trivial]
    rfl
  add_left x y z := by simp
  smul_left c x y := by simp

lemma inner_real_eq_re_inner (x y : H) : inner ℝ x y = ⟪x, y⟫.re := rfl

end RestrictScalar

namespace ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The image of a closed submodule by the multiplication by `Complex.I`. -/
noncomputable abbrev mulI (S : ClosedSubmodule ℝ H) := S.mapEquiv (scalarSMulCLE H Complex.I)

/-- The symplectic complement of a closed submodule with respect to `⟪⬝, ⬝⟫.im`, defined as the
image of `mulI` and `orthogonal`. The proof that this is the symplectic complement is given by
`mem_symplComp`. -/
noncomputable abbrev symplComp (S : ClosedSubmodule ℝ H) := (S.mulI)ᗮ

lemma mem_iff (S : ClosedSubmodule ℝ H) {x : H} : x ∈ S ↔ x ∈ S.toSubmodule.carrier := by
  exact Eq.to_iff rfl

lemma mem_symplComp_iff {x : H} {S : ClosedSubmodule ℝ H} :
    x ∈ S.symplComp ↔ ∀ y ∈ S, ⟪y, x⟫.im = 0 := by
  rw [symplComp, mem_orthogonal]
  simp only [mem_mapEquiv_iff', scalarSMulCLE_symm_apply, Complex.inv_I, neg_smul]
  constructor
  · intro h y hy
    have hiy := h (Complex.I • y)
    simp only [← smul_assoc, smul_eq_mul, Complex.I_mul_I, neg_smul, one_smul, neg_neg] at hiy
    have hxy := hiy hy
    rw [inner_real_eq_re_inner] at hxy
    simp only [CStarModule.inner_op_smul_left, RCLike.star_def, Complex.conj_I, mul_neg,
      Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub,
      neg_neg] at hxy
    exact hxy
  · intro h y hy
    rw [inner_real_eq_re_inner]
    have hiy := h _ hy
    simp only [inner_neg_left, Complex.neg_im, neg_eq_zero] at hiy
    rw [inner_smul_left] at hiy
    simp only [Complex.conj_I, neg_mul, Complex.neg_im, Complex.mul_im, Complex.I_re, zero_mul,
      Complex.I_im, one_mul, zero_add, neg_eq_zero] at hiy
    exact hiy

lemma orthogonal_mulI_eq_symplComp (S : ClosedSubmodule ℝ H) : Sᗮ.mulI = S.symplComp := by
  ext x
  rw [← mem_iff, ← mem_iff, mem_symplComp_iff]
  simp only [mem_mapEquiv_iff', scalarSMulCLE_symm_apply, Complex.inv_I, neg_smul]
  simp_rw [mem_orthogonal, inner_real_eq_re_inner]
  constructor
  · intro h y hy
    have hxy := h y hy
    simp only [inner_neg_right, Complex.neg_re, neg_eq_zero] at hxy
    rw [inner_smul_right_eq_smul] at hxy
    simp only [smul_eq_mul, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub,
      neg_eq_zero] at hxy
    exact hxy
  · intro h y hy
    simp only [inner_neg_right, Complex.neg_re, neg_eq_zero]
    rw [inner_smul_right_eq_smul]
    simp only [smul_eq_mul, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub,
      neg_eq_zero]
    exact h y hy

lemma mulI_symplComp_eq_symplComp_mulI {S : ClosedSubmodule ℝ H} :
    S.mulI.symplComp = S.symplComp.mulI := by
  rw [symplComp, symplComp, orthogonal_mulI_eq_symplComp]

@[simp]
lemma mulI_mulI_eq (S : ClosedSubmodule ℝ H) : S.mulI.mulI = S := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe]
  constructor
  · intro h
    rw [mem_mapEquiv_iff' (scalarSMulCLE H Complex.I)] at h
    simp only [scalarSMulCLE_symm_apply, Complex.inv_I, neg_smul, mem_mapEquiv_iff', smul_neg,
      neg_neg, ← smul_assoc] at h
    simp only [smul_eq_mul, Complex.I_mul_I] at h
    rw [← SetLike.forall_smul_mem_iff] at h
    have := h (-1 : ℝ)
    simp only [neg_smul, one_smul, smul_neg, neg_neg] at this
    exact this
  · intro h
    rw [mem_mapEquiv_iff' (scalarSMulCLE H Complex.I)]
    simp only [scalarSMulCLE_symm_apply, Complex.inv_I, neg_smul, mem_mapEquiv_iff', smul_neg,
      neg_neg, ← smul_assoc]
    simp only [smul_eq_mul, Complex.I_mul_I, neg_smul, one_smul]
    rw [← SetLike.forall_smul_mem_iff] at h
    have hx := h (-1 : ℝ)
    simp only [neg_smul, one_smul] at hx
    exact hx

@[simp]
lemma symplComp_symplComp_eq [CompleteSpace H] {S : ClosedSubmodule ℝ H} :
    S.symplComp.symplComp = S := by
  rw [symplComp, ← mulI_symplComp_eq_symplComp_mulI, symplComp]
  simp only [eq_orthogonal_orthogonal, mulI_mulI_eq]

lemma sup_mulI_eq_mulI_sup (S T : ClosedSubmodule ℝ H) :
    (S ⊔ T).mulI = S.mulI ⊔ T.mulI := by
  rw [mulI, ← mapEquiv_sup_eq_sup_mapEquiv]

lemma inf_mulI_eq_mulI_inf (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).mulI = S.mulI ⊓ T.mulI := by
  rw [mulI, ← mapEquiv_inf_eq_inf_mapEquiv]

lemma inf_symplComp_eq_symplcomp_sup (S T : ClosedSubmodule ℝ H) :
    (S ⊔ T).symplComp = S.symplComp ⊓ T.symplComp := by
  rw [symplComp, symplComp, symplComp, sup_mulI_eq_mulI_sup]
  exact Eq.symm (inf_orthogonal S.mulI T.mulI)

lemma sup_symplComp_eq_symplcomp_inf [CompleteSpace H] (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).symplComp = S.symplComp ⊔ T.symplComp := by
  rw [symplComp, symplComp, symplComp, inf_mulI_eq_mulI_inf]
  exact Eq.symm (sup_orthogonal S.mulI T.mulI)

end ClosedSubmodule

section Def

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A standard subspace `S` of a complex Hilbert space (or just an inner product space) `H` is a
closed real subspace `S` such that `S ⊓ i S = ⊥` and `S ⊔ i S = ⊤`. -/
@[ext]
structure StandardSubspace where
  /-- A real closed subspace `S`. -/
  toClosedSubmodule : ClosedSubmodule ℝ H
  /-- `S` is separating, that is, `S ⊓ i S` is the trivial subspace. -/
  IsSeparating : toClosedSubmodule ⊓ toClosedSubmodule.mulI = ⊥
  /-- `S` is cyclic, that is, `S ⊔ i S` is the whole space. -/
  IsCyclic : toClosedSubmodule ⊔ toClosedSubmodule.mulI = ⊤

end Def

namespace StandardSubspace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma standardSubspace_eq_iff {S T : StandardSubspace H} :
    S = T ↔ S.toClosedSubmodule = T.toClosedSubmodule := by
  constructor
  · intro h
    exact congrArg StandardSubspace.toClosedSubmodule h
  · intro h
    ext x
    simp only [Submodule.carrier_eq_coe, ClosedSubmodule.coe_toSubmodule, SetLike.mem_coe]
    exact Eq.to_iff (congrFun (congrArg Membership.mem h) x)

/-- The image of a standard subspace by the multiplication by `Complex.I`, bundled as a
`StandardSubspace`. -/
noncomputable def mulI (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.mulI
  IsSeparating := by
    simp only [ClosedSubmodule.mulI_mulI_eq]
    rw [inf_comm]
    exact S.IsSeparating
  IsCyclic := by
    simp only [ClosedSubmodule.mulI_mulI_eq]
    rw [sup_comm]
    exact S.IsCyclic

/-- The symplectic complement of a standard subspace, bundled as a `StandardSubspace`. -/
noncomputable def symplComp [CompleteSpace H] (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.symplComp
  IsSeparating := by
    rw [← ClosedSubmodule.mulI_symplComp_eq_symplComp_mulI,
      ← ClosedSubmodule.inf_symplComp_eq_symplcomp_sup, S.IsCyclic, ClosedSubmodule.symplComp,
      ClosedSubmodule.mulI]
    simp
  IsCyclic := by
    rw [← ClosedSubmodule.mulI_symplComp_eq_symplComp_mulI,
      ← ClosedSubmodule.sup_symplComp_eq_symplcomp_inf, S.IsSeparating, ClosedSubmodule.symplComp,
      ClosedSubmodule.mulI]
    simp

@[simp]
theorem symplComp_symplComp_eq [CompleteSpace H] (S : StandardSubspace H) :
    S.symplComp.symplComp = S := by
  apply standardSubspace_eq_iff.mpr
  simp only [symplComp]
  exact ClosedSubmodule.symplComp_symplComp_eq

end StandardSubspace
