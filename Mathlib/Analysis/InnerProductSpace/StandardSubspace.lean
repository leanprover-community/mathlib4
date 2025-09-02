import Mathlib.Analysis.CStarAlgebra.Module.Constructions

open Set ContinuousLinearMap
open scoped ComplexInnerProductSpace

instance : NeZero Complex.I := neZero_iff.mpr Complex.I_ne_zero

section ScalarSMulCLM

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def scalarSMulCLM : ℂ →L[ℂ] H →L[ℝ] H where
  toFun c := c • (id ℝ H)
  map_add' _ _ := Module.add_smul _ _ (id ℝ H)
  map_smul' _ _ := IsScalarTower.smul_assoc _ _ (id ℝ H)

@[simp]
lemma scalarSMulCLM_apply (c : ℂ) (x : H) : scalarSMulCLM H c x = c • x := rfl

noncomputable def scalarSMulCLE (c : ℂ) [h : NeZero c] : H ≃L[ℝ] H where
  toFun := c • (id ℝ H)
  continuous_toFun := by
    have : Continuous (fun (x : H) => c • x) := continuous_const_smul c
    congr
  map_add' x y := by simp
  map_smul' a x := by
    simp only [coe_id', Pi.smul_apply, id_eq, RingHom.id_apply]
    exact smul_comm c a x
  invFun := c⁻¹ • (id ℝ H)
  left_inv := by
    intro x
    simp only [coe_id', Pi.smul_apply, id_eq]
    exact inv_smul_smul₀ h.out x
  right_inv := by
    intro x
    simp only [coe_id', Pi.smul_apply, id_eq]
    refine smul_inv_smul₀ h.out x
  continuous_invFun := by
    have : Continuous (fun (x : H) => c⁻¹ • x) := continuous_const_smul c⁻¹
    congr

@[simp]
lemma scalarSMulCLE_apply (c : ℂ) [NeZero c] (x : H) : scalarSMulCLE H c x = c • x := rfl

@[simp]
lemma scalarSMulCLE_symm_apply (c : ℂ) [NeZero c] (x : H) :
    (scalarSMulCLE H c).symm x = c⁻¹ • x := rfl

lemma IsInvertible_scalarSMulCLM_of_neZero (c : ℂ) [NeZero c] :
    IsInvertible (scalarSMulCLM H c) := by
  use scalarSMulCLE H c
  ext x
  simp

end ScalarSMulCLM

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

lemma aaa (x y : H) : inner ℝ x y = ⟪x, y⟫.re := rfl

end RestrictScalar

namespace Submodule

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Submodule

namespace ClosedSubmodule

variable {H : Type*} [NormedAddCommGroup H] [ipc : InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable abbrev mulI (S : ClosedSubmodule ℝ H) := S.mapEquiv (scalarSMulCLE H Complex.I)

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
    simp [← smul_assoc] at hiy
    have hxy := hiy hy
    rw [aaa] at hxy
    simp only [CStarModule.inner_op_smul_left, RCLike.star_def, Complex.conj_I, mul_neg,
      Complex.neg_re, Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_sub,
      neg_neg] at hxy
    exact hxy
  · intro h y hy
    rw [aaa]
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
  simp_rw [mem_orthogonal, aaa]
  constructor
  · intro h y hy
    have hxy := h y hy
    simp only [inner_neg_right, Complex.neg_re, neg_eq_zero] at hxy
    rw [inner_smul_right_eq_smul] at hxy
    simp only [smul_eq_mul, Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub,
      neg_eq_zero] at hxy
    exact hxy
  · intro h
    intro y hy
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
lemma symplComp_symplComp_eq {S : ClosedSubmodule ℝ H} : S.symplComp.symplComp = S := by
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

lemma sup_symplComp_eq_symplcomp_inf (S T : ClosedSubmodule ℝ H) :
    (S ⊓ T).symplComp = S.symplComp ⊔ T.symplComp := by
  rw [symplComp, symplComp, symplComp, inf_mulI_eq_mulI_inf]
  exact Eq.symm (sup_orthogonal S.mulI T.mulI)

end ClosedSubmodule

section StandardSubspace

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

@[ext]
structure StandardSubspace where
  toSubspace : ClosedSubmodule ℝ H
  separating : toSubspace ⊓ toSubspace.mulI = ⊥
  cyclic : toSubspace ⊔ toSubspace.mulI = ⊤

namespace StandardSubspace

lemma standardSubspace_eq_iff {S T : StandardSubspace H} : S = T ↔ S.toSubspace = T.toSubspace := by
  constructor
  · intro h
    exact congrArg StandardSubspace.toSubspace h
  · intro h
    ext x
    simp only [Submodule.carrier_eq_coe, ClosedSubmodule.coe_toSubmodule, SetLike.mem_coe]
    exact Eq.to_iff (congrFun (congrArg Membership.mem h) x)

noncomputable def mulI (S : StandardSubspace H) : StandardSubspace H where
  toSubspace := S.toSubspace.mulI
  separating := by
    simp only [ClosedSubmodule.mulI_mulI_eq]
    rw [inf_comm]
    exact S.separating
  cyclic := by
    simp only [ClosedSubmodule.mulI_mulI_eq]
    rw [sup_comm]
    exact S.cyclic

noncomputable def symplComp (S : StandardSubspace H) : StandardSubspace H where
  toSubspace := S.toSubspace.symplComp
  separating := by
    rw [← ClosedSubmodule.mulI_symplComp_eq_symplComp_mulI,
      ← ClosedSubmodule.inf_symplComp_eq_symplcomp_sup, S.cyclic, ClosedSubmodule.symplComp,
      ClosedSubmodule.mulI]
    simp
  cyclic := by
    rw [← ClosedSubmodule.mulI_symplComp_eq_symplComp_mulI,
      ← ClosedSubmodule.sup_symplComp_eq_symplcomp_inf, S.separating, ClosedSubmodule.symplComp,
      ClosedSubmodule.mulI]
    simp

@[simp]
theorem symplComp_symplComp_eq (S : StandardSubspace H) : S.symplComp.symplComp = S := by
  refine (standardSubspace_eq_iff H).mpr ?_
  simp only [symplComp]
  exact ClosedSubmodule.symplComp_symplComp_eq

end StandardSubspace

end StandardSubspace
