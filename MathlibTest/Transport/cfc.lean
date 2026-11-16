module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Tactic.Transport.Test

open Complex TransportTest

@[transport fun f : ℂ → ℂ ↦ cfc f a, fun f : ℝ → ℝ ↦ cfc f a]
lemma cfc_real_eq_complex_comp'
    {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
    [ContinuousFunctionalCalculus ℂ A IsStarNormal] [T2Space A]
    [ContinuousMap.UniqueHom ℝ A] (g f : ℝ → ℝ) (a : A)
    (hg : ContinuousOn g (f '' spectrum ℝ a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc (fun x ↦ (g (f x.re) : ℂ)) a = cfc g (cfc f a) := by
  rw [← cfc_comp' g f a hg hf ha , ← cfc_real_eq_complex (fun x ↦ g (f x)) ha]

attribute [transport fun f : R → R ↦ cfc f a]
  cfc_add cfc_mul cfc_pow cfc_sum cfc_smul cfc_sub cfc_neg cfc_const_one cfc_const_zero
  cfc_id' cfc_comp'

theorem foo {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    a + I • cfcₙ (√·) (1 - a ^ 2) = cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  rw [cfcₙ_eq_cfc]
  transport [MapRel fun f : ℂ → ℂ ↦ cfc f a] <;> try infer_param
  rfl
