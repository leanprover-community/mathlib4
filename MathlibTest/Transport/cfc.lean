module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Tactic.Transport.Test

open Complex Transport

theorem cfc_transport (R : Type*) {A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R A p] (a : A) {f g : R → R} {x y : A}
    (hx : MapRel (cfc · a) f x) (hy : MapRel (cfc · a) g y) :
    (∀ x ∈ spectrum R a, f x = g x) → x = y := by
  subst hx hy
  apply cfc_congr

@[transport (cfc (R := ℂ) · a), (cfc (R := ℝ) · a)]
lemma cfc_real_eq_complex_comp'
    {A : Type*} [TopologicalSpace A] [Ring A] [StarRing A] [Algebra ℂ A]
    [ContinuousFunctionalCalculus ℂ A IsStarNormal] [T2Space A]
    [ContinuousMap.UniqueHom ℝ A] (g f : ℝ → ℝ) (a : A)
    (hg : ContinuousOn g (f '' spectrum ℝ a) := by cfc_cont_tac)
    (hf : ContinuousOn f (spectrum ℝ a) := by cfc_cont_tac)
    (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc (fun x ↦ (g (f x.re) : ℂ)) a = cfc g (cfc f a) := by
  rw [← cfc_comp' g f a hg hf ha , ← cfc_real_eq_complex (g <| f ·) ha]

attribute [transport (cfc (R := R) · a)]
  cfc_id' cfc_comp' cfc_add cfc_mul cfc_pow cfc_smul cfc_const_mul cfc_star cfc_sub cfc_neg cfc_sum
  cfc_const_one cfc_const_zero

/--
trace: A : Type u_1
inst✝ : CStarAlgebra A
a : A
ha : IsSelfAdjoint a
⊢ ∀ x ∈ spectrum ℂ a, x + I * ↑√(1 - x.re ^ 2) = x + I * ↑√(1 - x.re ^ 2)
-/
#guard_msgs in
theorem foo {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    a + I • cfcₙ (√·) (1 - a ^ 2) = cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  rw [cfcₙ_eq_cfc]
  transport [cfc_transport ℂ a]
  trace_state
  intro x hx
  rfl
