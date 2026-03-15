/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

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

open Complex ContinuousLinearMap
open scoped ComplexInnerProductSpace

section ScalarSMulCLE

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- the scalar product by a non-zero complex number as a continuous real-linear equivalence. -/
noncomputable def scalarSMulCLE (c : ℂˣ) : H ≃L[ℝ] H := ContinuousLinearEquiv.smulLeft c

@[simp]
lemma scalarSMulCLE_apply (c : ℂˣ) (x : H) : scalarSMulCLE H c x = c • x := rfl

@[simp]
lemma scalarSMulCLE_symm_apply (c : ℂˣ) (x : H) : (scalarSMulCLE H c).symm x = c⁻¹ • x := rfl

end ScalarSMulCLE

namespace ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [ipc : InnerProductSpace ℂ H]

/-- `H` as a real Hilbert space. This instance is declared inside `ClosedSubmodule` namespace. If
one needs this structure (for example when considering standard subspaces), one should just `open
ClosedSubmodule` and not declare another instance. -/
noncomputable scoped instance : InnerProductSpace ℝ H where
  inner x y := ⟪x, y⟫.re
  norm_sq_eq_re_inner := by simp [RCLike.re_to_real, ipc.norm_sq_eq_re_inner]
  conj_inner_symm x y := by
    simp only [← ipc.conj_inner_symm x y, conj_trivial]
    rfl
  add_left := by simp
  smul_left := by simp

lemma inner_real_eq_re_inner (x y : H) : inner ℝ x y = ⟪x, y⟫.re := rfl

/-- The imaginary unit as an invertible element. -/
abbrev _root_.Complex.UnitI : ℂˣ where
  val := I
  inv := -I
  val_inv := by simp
  inv_val := by simp

/-- The image of a closed submodule by the multiplication by `Complex.I`. -/
noncomputable abbrev mulI (S : ClosedSubmodule ℝ H) := S.mapEquiv (scalarSMulCLE H UnitI)

/-- The symplectic complement of a closed submodule with respect to `⟪⬝, ⬝⟫.im`, defined as the
image of `mulI` and `orthogonal`. The proof that this is the symplectic complement is given by
`mem_symplComp_iff`. -/
noncomputable abbrev symplComp (S : ClosedSubmodule ℝ H) := (S.mulI)ᗮ

lemma mem_iff (S : ClosedSubmodule ℝ H) {x : H} : x ∈ S ↔ x ∈ S.toSubmodule.carrier := by
  exact Eq.to_iff rfl

lemma mem_symplComp_iff {x : H} {S : ClosedSubmodule ℝ H} :
    x ∈ S.symplComp ↔ ∀ y ∈ S, ⟪y, x⟫.im = 0 := by
  simp only [mem_orthogonal, mem_mapEquiv_iff, scalarSMulCLE_symm_apply, Units.inv_mk,
    Units.smul_mk_apply, neg_smul]
  constructor
  · intro h y hy
    have hiy := h (I • y)
    simp only [← smul_assoc, smul_eq_mul, I_mul_I, neg_smul, one_smul, neg_neg] at hiy
    simpa [inner_real_eq_re_inner] using hiy hy
  · intro h _ hy
    have hiy := h _ hy
    simpa [inner_smul_left] using hiy

lemma mulI_orthogonal_eq_symplComp (S : ClosedSubmodule ℝ H) : Sᗮ.mulI = S.symplComp := by
  ext x
  rw [← mem_iff, ← mem_iff, mem_symplComp_iff, mem_mapEquiv_iff, scalarSMulCLE_symm_apply,
    Units.inv_mk, Units.smul_mk_apply, neg_smul, mem_orthogonal]
  simp [inner_real_eq_re_inner]

lemma mulI_orthogonal (S : ClosedSubmodule ℝ H) : Sᗮ.mulI = S.mulIᗮ := by
  rw [mulI_orthogonal_eq_symplComp]

@[simp]
lemma mulI_symplComp {S : ClosedSubmodule ℝ H} :
    S.symplComp.mulI = S.mulI.symplComp := by
  rw [symplComp, symplComp, mulI_orthogonal_eq_symplComp]

@[simp]
lemma mulI_mulI_eq (S : ClosedSubmodule ℝ H) : S.mulI.mulI = S := by
  ext x
  simp only [Submodule.carrier_eq_coe, coe_toSubmodule, SetLike.mem_coe]
  constructor
  · intro h
    rw [mem_mapEquiv_iff (scalarSMulCLE H UnitI), ← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc] using (h (-1 : ℝ))
  · intro h
    rw [← SetLike.forall_smul_mem_iff] at h
    simpa [← smul_assoc] using (h (-1 : ℝ))

lemma involutive_mulI :
    Function.Involutive (mulI : ClosedSubmodule ℝ H → ClosedSubmodule ℝ H) := mulI_mulI_eq

@[simp]
lemma symplComp_symplComp_eq [CompleteSpace H] {S : ClosedSubmodule ℝ H} :
    S.symplComp.symplComp = S := by simp [symplComp]

lemma mulI_sup (S T : ClosedSubmodule ℝ H) :
    (S ⊔ T).mulI = S.mulI ⊔ T.mulI := by
  rw [mulI, ← mapEquiv_sup_eq]

lemma mulI_inf (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).mulI = S.mulI ⊓ T.mulI := by
  rw [mulI, ← mapEquiv_inf_eq]

@[simp]
lemma symplComp_sup (S T : ClosedSubmodule ℝ H) :
    (S ⊔ T).symplComp = S.symplComp ⊓ T.symplComp := by
  rw [symplComp, symplComp, symplComp, mulI_sup]
  exact Eq.symm (inf_orthogonal S.mulI T.mulI)

@[simp]
lemma symplComp_inf [CompleteSpace H] (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).symplComp = S.symplComp ⊔ T.symplComp := by
  rw [symplComp, symplComp, symplComp, mulI_inf]
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

open ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

@[simp]
lemma toClosedSubmodule_inj {S T : StandardSubspace H} :
    S.toClosedSubmodule = T.toClosedSubmodule ↔ S = T :=
  StandardSubspace.ext_iff.symm

lemma toClosedSubmodule_injective : Function.Injective (toClosedSubmodule (H := H)) :=
  fun _ _ ↦ toClosedSubmodule_inj.mp

/-- The image of a standard subspace by the multiplication by `Complex.I`, bundled as a
`StandardSubspace`. -/
noncomputable def mulI (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.mulI
  IsSeparating := by simpa [mulI_mulI_eq, inf_comm] using S.IsSeparating
  IsCyclic := by simpa [mulI_mulI_eq, sup_comm] using S.IsCyclic

/-- The symplectic complement of a standard subspace, bundled as a `StandardSubspace`. -/
noncomputable def symplComp [CompleteSpace H] (S : StandardSubspace H) : StandardSubspace H where
  toClosedSubmodule := S.toClosedSubmodule.symplComp
  IsSeparating := by
    simp [mulI_symplComp, ClosedSubmodule.inf_orthogonal, sup_comm, S.IsCyclic]
  IsCyclic := by
    simp [mulI_symplComp, ClosedSubmodule.sup_orthogonal, inf_comm, S.IsSeparating]

@[simp]
theorem symplComp_symplComp_eq [CompleteSpace H] (S : StandardSubspace H) :
    S.symplComp.symplComp = S := toClosedSubmodule_inj.mp ClosedSubmodule.symplComp_symplComp_eq

lemma involutive_symplComp [CompleteSpace H] :
    Function.Involutive (symplComp : StandardSubspace H → StandardSubspace H)
  := symplComp_symplComp_eq

end StandardSubspace
