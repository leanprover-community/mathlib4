module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Tactic.Transport.Test

open Complex TransportTest

section
variable
  {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
  [IsTopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
  [Algebra R A] [ContinuousFunctionalCalculus R A p]

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

set_option trace.transport true
@[transport]
lemma cfc_eq_transport (a x y : A) (f g : R → R)
    (hf : MapRel (cfc · a) f x) (hg : MapRel (cfc · a) g y) (h : ∀ x, f x = g x) :
    x = y := by
  subst hf hg
  cases funext h
  rfl

end

attribute [transport fun f : R → R ↦ cfc f a] cfc_id'
attribute [transport fun f : R → R ↦ cfc f a]
  cfc_add cfc_const_mul cfc_comp' cfc_sub cfc_const_one cfc_pow_id
-- attribute [transport fun f : ℂ → ℂ ↦ cfc f a, fun f : ℝ → ℝ ↦ cfc f a] cfc_real_eq_complex


set_option trace.transport true
set_option trace.Meta.synthInstance true
set_option trace.Meta.isDefEq true
theorem foo {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) :
    a + I • cfcₙ (√·) (1 - a ^ 2) = cfc (fun x : ℂ ↦ x + I * ↑√(1 - x.re ^ 2)) a := by
  rw [cfcₙ_eq_cfc]
  transport [A to ℂ, @cfc_id'.transport_1 (a := a)] <;> try infer_param
  intro x; rfl
