/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Geometry.Manifold.RegularValueTheorem
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-! # Analytification of a standard smooth algebra as a manifold

to be written!
-/

public section

open scoped ContDiff
open Manifold Topology Function Set

section

lemma Function.Injective.extend_single_zero {α β γ : Type*} [DecidableEq α] [DecidableEq β] [Zero γ]
    (f : α → β) (hf : Function.Injective f) (a : α) (x : γ) :
    Function.extend f (Pi.single a x) 0 = Pi.single (f a) x := by
  ext j
  by_cases h : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := h
    simp [hf.extend_apply, Pi.single_apply, hf.eq_iff]
  · rw [Function.extend_apply' _ _ _ h, Pi.single_apply]
    simp
    grind

-- less universe restrictions
@[expose, simps]
noncomputable def Function.ExtendByZero.linearMap' (R : Type*) [Semiring R]
    {ι η : Type*} (s : ι → η) :
    (ι → R) →ₗ[R] η → R :=
  { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }

end

@[simp]
lemma fderiv_apply {ι : Type*} [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (x : ι → 𝕜) (i : ι) :
    fderiv 𝕜 (fun x : ι → 𝕜 => x i) x = ContinuousLinearMap.proj i :=
  (ContinuousLinearMap.proj (R := 𝕜) i).fderiv (x := x)

@[fun_prop]
lemma MvPolynomial.contDiff {ι : Type*} [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : MvPolynomial ι 𝕜) :
    ContDiff 𝕜 ω (p.eval ·) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p j hp => simpa using hp.mul (contDiff_apply 𝕜 𝕜 j)

@[fun_prop]
lemma MvPolynomial.differentiable {ι : Type*} [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : MvPolynomial ι 𝕜) :
    Differentiable 𝕜 (p.eval ·) :=
  p.contDiff.differentiable (by simp)

lemma MvPolynomial.eval_pderiv_eq_fderiv_aeval {ι : Type*} [DecidableEq ι] [Fintype ι]
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] (p : MvPolynomial ι 𝕜) (i : ι) (x : ι → 𝕜) :
    (p.pderiv i).eval x = fderiv 𝕜 (p.eval ·) x (Pi.single i 1) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add]
    rw [fderiv_fun_add (by fun_prop) (by fun_prop)]
    simp [hp, hq]
  | mul_X p j hp =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, eval_X]
    rw [fderiv_fun_mul (by fun_prop) (by fun_prop)]
    simp [hp, Pi.single_apply]

namespace Algebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {R : Type*} [CommRing R] [Algebra 𝕜 R]
variable {S : Type*} [CommRing S] [Algebra R S]
variable {T : Type*} [CommRing T] [Algebra R T]
variable {ι σ : Type*}

namespace Presentation

section Algebra

variable (P : Presentation R S ι σ)

/--
The polynomial function `(ι → R) → (σ → R)` given by evaluating the relations:
`x = (xᵢ)ᵢ ↦ ((P.relation r)(x))ᵣ`
-/
def evaluation (P : Presentation R S ι σ) (x : (ι → R)) (r : σ) : R :=
  (P.relation r).eval x

def evaluation' (P : Presentation R S ι σ) (x : (ι → R)) : σ → R :=
  fun r ↦ (P.relation r).eval x

end Algebra
end Presentation

namespace PreSubmersivePresentation

section Algebra

variable [Finite σ]
variable (P : PreSubmersivePresentation R S ι σ)

noncomputable
def aevalDifferential' (x : ι → T) : (σ → T) →ₗ[T] (σ → T) :=
  (Pi.basisFun T σ).constr T fun i j ↦
    MvPolynomial.aeval x (MvPolynomial.pderiv (P.map i) (P.relation j))

end Algebra

section Analysis

variable (P : PreSubmersivePresentation 𝕜 R ι σ) [Fintype ι] [Fintype σ]

lemma fderiv_evaluation (x : ι → 𝕜) :
     (fderiv 𝕜 P.evaluation x).toLinearMap ∘ₗ Function.ExtendByZero.linearMap' _ P.map =
      P.aevalDifferential' x := by
  classical
  apply (Pi.basisFun 𝕜 σ).ext fun i ↦ ?_
  dsimp [ExtendByZero.linearMap']
  simp only [Pi.basisFun_apply, aevalDifferential', MvPolynomial.aeval_eq_eval,
    MvPolynomial.eval_pderiv_eq_fderiv_aeval, Module.Basis.constr_apply_fintype,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply, Fintype.sum_single_smul, one_smul,
    P.map_inj.extend_single_zero]
  unfold Presentation.evaluation
  ext a
  rw [← ContinuousLinearMap.proj_apply (R := 𝕜)
    (b := (fderiv 𝕜 (fun x r ↦ (MvPolynomial.eval x) (P.relation r)) x) (Pi.single (P.map i) 1))]
  rw [← (ContinuousLinearMap.proj (φ := fun _ ↦ 𝕜) (R := 𝕜) a).fderiv,
    ← ContinuousLinearMap.comp_apply, ← fderiv_comp _ (by fun_prop) (by fun_prop),
    Function.comp_def]
  dsimp

lemma contMDiff_evaluation : ContMDiff 𝓘(𝕜, ι → 𝕜) 𝓘(𝕜, σ → 𝕜) ω P.evaluation := by
  rw [contMDiff_iff_contDiff]
  unfold Presentation.evaluation
  fun_prop

end Analysis

end PreSubmersivePresentation

namespace SubmersivePresentation

section Analysis

variable [Fintype ι] [Fintype σ] (P : SubmersivePresentation 𝕜 R ι σ)

variable [CompleteSpace 𝕜]

lemma isRegularValue_zero :
    IsRegularValue 𝓘(𝕜, ι → 𝕜) 𝓘(𝕜, σ → 𝕜) P.evaluation 0 := by
  intro x hx
  unfold IsRegularPoint
  refine .of_surjective_of_finiteDimensional ?_
  dsimp
  have := P.fderiv_evaluation x
  suffices h : Function.Surjective (P.aevalDifferential' x) by
    rw [← P.fderiv_evaluation x] at h
    apply Function.Surjective.of_comp
    exact h
  sorry

end Analysis


end SubmersivePresentation

end Algebra
