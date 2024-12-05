/-
Copyright (c) 2024 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# GNS construction
-/

open scoped TensorProduct
open scoped ComplexOrder

section Unital

section GNS

open Complex in
lemma yet_another_polarization {E F : Type*} [AddCommGroup E] [AddCommGroup F] [Module ℂ E]
    [Module ℂ F] {f : E →ₗ⋆[ℂ] E →ₗ[ℂ] F}
    {x y : E} : f x y = (4⁻¹ : ℂ) • (f (x+y) (x+y) - f (x-y) (x-y) +
      I • f (x - I•y) (x - I•y) - I • f (x + I•y) (x + I•y)) := by
  simp_rw [map_add, map_sub, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, conj_I, smul_add, smul_sub, ← mul_smul, mul_neg, I_mul_I]
  module

open Complex in
lemma hermitian_of_sesquilinear {E F : Type*} [AddCommGroup E] [AddCommGroup F] [Module ℂ E]
    [Module ℂ F] [StarAddMonoid F] [StarModule ℂ F] {f : E →ₗ⋆[ℂ] E →ₗ[ℂ] F}
    (hf : ∀ x, f x x = star (f x x)) (x y : E) : f x y = star (f y x) := by
  have a : y + I • x = I • (x - I • y) := by
    rw [smul_sub, ← mul_smul, I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]
  have b : y - I • x = -I • (x + I • y) := by
    rw [smul_add, ← mul_smul, neg_mul, I_mul_I, neg_neg, one_smul, sub_eq_add_neg, add_comm,
        neg_smul]
  have c : y + x = x + y := add_comm _ _
  have d : y - x = -(x - y) := by rw [neg_sub]
  simp_rw [yet_another_polarization (x := x) (y := y), yet_another_polarization (x := y) (y := x),
    c, d, a, b, map_smul, map_smulₛₗ, map_neg, LinearMap.smul_apply, LinearMap.neg_apply,
    conj_I, ← mul_smul, mul_neg, neg_mul, I_mul_I, neg_neg, mul_one, mul_neg_one, neg_neg,
    star_smul, star_sub, star_add, star_sub, star_smul, ← hf, ← starRingEnd_apply, conj_inv, conj_I,
    conj_ofNat]
  module

variable {A : Type*} [SeminormedRing A] [StarAddMonoid A] [NormedAlgebra ℂ A] [StarModule ℂ A]

structure ContinuousLinearMap.IsGNSRepr (φ : A →L[ℂ] ℂ) {H : Type*}
    [NormedAddCommGroup H] [CompleteSpace H] [InnerProductSpace ℂ H]
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) where
  eq : ∀ a, φ a = inner ξ (π a ξ)

set_option linter.unusedVariables false in
def ContinuousLinearMap.gnsPreSpace (φ : A →L[ℂ] ℂ) : Type _ := A

noncomputable instance {φ : A →L[ℂ] ℂ} : AddCommGroup (φ.gnsPreSpace) :=
  inferInstanceAs <| AddCommGroup A

noncomputable instance {φ : A →L[ℂ] ℂ} : Module ℂ (φ.gnsPreSpace) :=
  inferInstanceAs <| Module ℂ A

def ContinuousLinearMap.ofGnsPreSpace (φ : A →L[ℂ] ℂ) : φ.gnsPreSpace →ₗ[ℂ] A := .id

noncomputable def ContinuousLinearMap.innerGnsPreSpaceₛₗ (φ : A →L[ℂ] ℂ) :
    φ.gnsPreSpace →ₗ⋆[ℂ] φ.gnsPreSpace →ₗ[ℂ] ℂ :=
  .mk₂'ₛₗ _ _ (fun a b ↦ φ (star (φ.ofGnsPreSpace a) * (φ.ofGnsPreSpace b)))
    (fun _ _ _ ↦ by simp [star_add, add_mul])
    (fun _ _ _ ↦ by simp [star_smul])
    (fun _ _ _ ↦ by simp [mul_add])
    (fun _ _ _ ↦ by simp)

noncomputable instance {φ : A →L[ℂ] ℂ} : Inner ℂ (φ.gnsPreSpace) :=
  letI := Classical.propDecidable
  if ∀ a, 0 ≤ φ (star a * a)
  then {inner := fun a b ↦ φ.innerGnsPreSpaceₛₗ a b}
  else {inner := fun _ _ ↦ 0}

lemma ContinuousLinearMap.inner_gnsPreSpace_eq {φ : A →L[ℂ] ℂ} {a b : φ.gnsPreSpace} :
    letI := Classical.propDecidable
    inner a b =
      if ∀ a, 0 ≤ φ (star a * a)
      then φ (star (φ.ofGnsPreSpace a) * (φ.ofGnsPreSpace b))
      else 0 := by
  rw [instInnerComplexGnsPreSpace]
  split_ifs <;> rfl

noncomputable def ContinuousLinearMap.coreGnsPreSpace {φ : A →L[ℂ] ℂ} :
    PreInnerProductSpace.Core ℂ (φ.gnsPreSpace) where
  nonneg_re x := by
    rw [inner_gnsPreSpace_eq]
    split_ifs with hφ
    · exact Complex.nonneg_iff.mp (hφ x) |>.1
    · simp
  conj_symm := fun x y ↦ by
    rw [inner_gnsPreSpace_eq, inner_gnsPreSpace_eq]
    split_ifs with hφ
    · have : ∀ a : φ.gnsPreSpace, φ.innerGnsPreSpaceₛₗ a a = star (φ.innerGnsPreSpaceₛₗ a a) := by
        change ∀ a : A, φ (star a * a) = star (φ (star a * a))
        intro a
        rw [(hφ a).isSelfAdjoint]
      exact hermitian_of_sesquilinear this x y |>.symm
    · simp
  add_left := fun x y ↦ LinearMap.congr_fun (map_add φ.innerGnsPreSpaceₛₗ x y)
  smul_left := fun x y c ↦ LinearMap.congr_fun (map_smulₛₗ φ.innerGnsPreSpaceₛₗ c x) y

noncomputable instance

end GNS

section Stinespring

variable {𝕜 A K : Type*} [RCLike 𝕜] [Star A] [SeminormedRing A] [NormedAlgebra 𝕜 A]
  [NormedAddCommGroup K] [CompleteSpace K] [InnerProductSpace 𝕜 K]

structure ContinuousLinearMap.IsStinespringRepr (φ : A →L[𝕜] K →L[𝕜] K) {H : Type*}
    [NormedAddCommGroup H] [CompleteSpace H] [InnerProductSpace 𝕜 H]
    (π : A →⋆ₐ[𝕜] (H →L[𝕜] H)) (V : K →L[𝕜] H) where
  eq : ∀ a, φ a = (adjoint V) ∘L (π a) ∘L V

set_option linter.unusedVariables false in
def ContinuousLinearMap.stinespringPreSpace (φ : A →L[𝕜] K →L[𝕜] K) : Type _ :=
  A ⊗[𝕜] K

noncomputable instance {φ : A →L[𝕜] K →L[𝕜] K} : AddCommGroup (φ.stinespringPreSpace) :=
  inferInstanceAs <| AddCommGroup (A ⊗[𝕜] K)

noncomputable instance {φ : A →L[𝕜] K →L[𝕜] K} : Module 𝕜 (φ.stinespringPreSpace) :=
  inferInstanceAs <| Module 𝕜 (A ⊗[𝕜] K)

-- Defining the inner product is painful because of lack of API for semilinear things and tensor
-- products

end Stinespring

end Unital
