/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# TODO: not needed anymore
-/

open NormedSpace UniformSpace
open scoped ENNReal InnerProductSpace


namespace LinearMap.BilinForm

variable {𝕜 E : Type*} [RCLike 𝕜] [AddCommMonoid E] [Module 𝕜 E]

structure IsPosSemidef (B : LinearMap.BilinForm 𝕜 E) : Prop where
  isSymm : B.IsSymm
  nonneg_re_apply_self : ∀ x, 0 ≤ RCLike.re (B x x)

structure IsPosDef (B : LinearMap.BilinForm 𝕜 E) : Prop extends B.IsPosSemidef where
  definite : ∀ x, RCLike.re (B x x) = 0 → x = 0

lemma isSymm_bilinFormOfRealInner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    LinearMap.BilinForm.IsSymm (bilinFormOfRealInner (F := F)) := by
  intro x y
  simp only [bilinFormOfRealInner_apply_apply, RingHom.id_apply]
  rw [real_inner_comm]

lemma isPosSemidef_bilinFormOfRealInner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    LinearMap.BilinForm.IsPosSemidef (bilinFormOfRealInner (F := F)) where
  isSymm := isSymm_bilinFormOfRealInner
  nonneg_re_apply_self x := by
    simp only [bilinFormOfRealInner_apply_apply, RCLike.re_to_real]
    exact real_inner_self_nonneg

lemma isPosDef_bilinFormOfRealInner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] :
    LinearMap.BilinForm.IsPosDef (bilinFormOfRealInner (F := F)) where
  isSymm := isPosSemidef_bilinFormOfRealInner.isSymm
  nonneg_re_apply_self := isPosSemidef_bilinFormOfRealInner.nonneg_re_apply_self
  definite x hx := by simpa using hx

end LinearMap.BilinForm


namespace ProbabilityTheory

section MooreAronszajn

variable {E : Type*} [AddCommMonoid E] [Module ℝ E] {B : LinearMap.BilinForm ℝ E}
  {hB : B.IsPosDef}

set_option linter.unusedVariables false in
noncomputable
def H (hB : B.IsPosDef) : Submodule ℝ (E →ₗ[ℝ] ℝ) := Submodule.map B ⊤

variable (hB) in
noncomputable
def innerH : H hB → H hB → ℝ :=
  fun x y ↦ B (Submodule.mem_map.mp x.2).choose (Submodule.mem_map.mp y.2).choose

lemma innerH_self_eq' (hB : B.IsSymm) {y z : E} (h : B y = B z) :
    B y y = B z z := by
  calc B y y
  _ = B y (y + z) - B y z := by simp
  _ = B z (y + z) - B y z := by rw [h]
  _ = B z (y + z) - B z y := by rw [hB.eq y]
  _ = B z z := by simp

lemma todo (hB : B.IsSymm) {x x' y y' : E} (hx : B x = B x') (hy : B y = B y') :
    B x y = B x' y' := by
  rw [hx, hB.eq, hy, hB.eq]

lemma innerH_self_eq {y : E} {x : H hB} (hy : B y = x) :
    innerH hB x x = B y y := by
  refine innerH_self_eq' hB.isSymm ?_
  rw [hy]
  exact (Submodule.mem_map.mp x.2).choose_spec.2

lemma innerH_zero_zero : innerH hB 0 0 = 0 := by
  rw [innerH_self_eq (y := 0)] <;> simp

lemma innerH_eq {x y : H hB} {x' y' : E} (hx : B x' = x) (hy : B y' = y) :
    innerH hB x y = B x' y' := by
  refine todo hB.isSymm ?_ ?_
  · rw [hx]
    exact (Submodule.mem_map.mp x.2).choose_spec.2
  · rw [hy]
    exact (Submodule.mem_map.mp y.2).choose_spec.2

lemma innerH_add_left (x y z : H hB) :
    innerH hB (x + y) z = innerH hB x z + innerH hB y z := by
  obtain ⟨x', -, hx'⟩ := Submodule.mem_map.mp x.2
  obtain ⟨y', -, hy'⟩ := Submodule.mem_map.mp y.2
  obtain ⟨z', -, hz'⟩ := Submodule.mem_map.mp z.2
  calc innerH hB (x + y) z
  _ = B (x' + y') z' := by
    refine innerH_eq ?_ ?_
    · simp [hx', hy']
    · simp [hz']
  _ = B x' z' + B y' z' := by simp
  _ = innerH hB x z + innerH hB y z := by
    rw [innerH_eq hy' hz', innerH_eq hx' hz']

lemma innerH_symm (x y : H hB) : innerH hB x y = innerH hB y x := by
  obtain ⟨x', -, hx'⟩ := Submodule.mem_map.mp x.2
  obtain ⟨y', -, hy'⟩ := Submodule.mem_map.mp y.2
  rw [innerH_eq hx' hy', hB.isSymm.eq, ← innerH_eq hy' hx']

lemma innerH_smul_left (x y : H hB) (r : ℝ) :
    innerH hB (r • x) y = r * innerH hB x y := by
  obtain ⟨x', -, hx'⟩ := Submodule.mem_map.mp x.2
  obtain ⟨y', -, hy'⟩ := Submodule.mem_map.mp y.2
  rw [innerH_eq hx' hy', innerH_eq (x' := r • x') _ hy']
  · simp
  · simp [hx']

lemma re_innerH_self_nonneg (x : H hB) :
    0 ≤ RCLike.re (innerH hB x x) := by
  obtain ⟨x', -, hx'⟩ := Submodule.mem_map.mp x.2
  rw [innerH_self_eq hx']
  exact hB.nonneg_re_apply_self x'

lemma re_innerH_self_pos (x : H hB) (hx : RCLike.re (innerH hB x x) = 0) :
    x = 0 := by
  obtain ⟨x', -, hx'⟩ := Submodule.mem_map.mp x.2
  simp only [innerH_self_eq hx'] at hx
  simp only [hB.definite x' hx, map_zero] at hx'
  norm_cast at hx'
  exact hx'.symm

noncomputable
instance : Inner ℝ (H hB) where
  inner := innerH hB

noncomputable
instance coreH : InnerProductSpace.Core ℝ (H hB) where
  conj_inner_symm x y := by
    simp only [conj_trivial]
    exact innerH_symm y x
  add_left := innerH_add_left
  smul_left x y r := by
    simp only [conj_trivial]
    exact innerH_smul_left x y r
  re_inner_nonneg := re_innerH_self_nonneg
  definite := re_innerH_self_pos

noncomputable
instance : NormedAddCommGroup (H hB) := coreH.toNormedAddCommGroup

noncomputable
instance : InnerProductSpace ℝ (H hB) := InnerProductSpace.ofCore coreH

variable (hB) in
def rkhs : Type _ := Completion (H hB)

noncomputable
instance : NormedAddCommGroup (rkhs hB) := by unfold rkhs; infer_instance

noncomputable
instance : InnerProductSpace ℝ (rkhs hB) := by unfold rkhs; infer_instance

lemma eval_eq_inner (x : H hB) (y : E) :
    (x : E →ₗ[ℝ] ℝ) y = ⟪x, ⟨B y, Submodule.mem_map.mpr ⟨y, by simp, rfl⟩⟩⟫_ℝ := by
  change _ = innerH hB x ⟨B y, Submodule.mem_map.mpr ⟨y, by simp, rfl⟩⟩
  obtain ⟨x', -, hx'⟩ := Submodule.mem_map.mp x.2
  rw [innerH_eq hx' rfl, ← hx']

lemma eval_eq_innerSL (x : H hB) (y : E) :
    (x : E →ₗ[ℝ] ℝ) y
      = (innerSL ℝ ⟨B y, Submodule.mem_map.mpr ⟨y, by simp, rfl⟩⟩) x := by
  simp only [innerSL_apply]
  rw [real_inner_comm]
  exact eval_eq_inner x y

lemma uniformContinuous_eval {y : E} : UniformContinuous (fun x : H hB ↦ (x : E →ₗ[ℝ] ℝ) y) := by
  suffices (fun x : H hB ↦ (x : E →ₗ[ℝ] ℝ) y)
      = (innerSL ℝ ⟨B y, Submodule.mem_map.mpr ⟨y, by simp, rfl⟩⟩) by
    rw [this]
    exact ContinuousLinearMap.uniformContinuous _
  ext x
  exact eval_eq_innerSL _ _

noncomputable
def Rkhs.evalMap (y : E) : rkhs hB → ℝ :=
  Completion.extension (fun x : H hB ↦ (x : E →ₗ[ℝ] ℝ) y)

-- todo: why do I need to specify the coercion?
noncomputable
def rkhsPure (y : E) : rkhs hB :=
  ((↑) : H hB → Completion (H hB))
    ⟨B y, Submodule.mem_map.mpr ⟨y, by simp, rfl⟩⟩

lemma evalMap_apply (y : E) (x : rkhs hB) :
    Rkhs.evalMap y x = ⟪x, rkhsPure y⟫_ℝ := by
  revert x
  rw [← funext_iff]
  refine Completion.ext Completion.continuous_extension (by fun_prop) fun x ↦ ?_
  unfold rkhsPure Rkhs.evalMap
  rw [Completion.extension_coe, eval_eq_inner, Completion.inner_coe]
  exact uniformContinuous_eval

end MooreAronszajn

end ProbabilityTheory
