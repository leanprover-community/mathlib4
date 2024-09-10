import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

/-- Synthesize algebra instance from ring hom. -/
example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra A B := inferInstance
  algebraize f
  rename_i h₀
  guard_hyp h₀ := f.toAlgebra
  trivial

/-- Synthesize algebra instance from a composition -/
example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra A C := inferInstance
  algebraize (g.comp f)
  rename_i h₀
  guard_hyp h₀ := (g.comp f).toAlgebra
  trivial

/-- Synthesize algebra instance and scalar tower instance from a composition -/
example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    True := by
  fail_if_success -- Check that this instance is not available by default
    have h : IsScalarTower A B C := inferInstance
  algebraize f g (g.comp f)
  rename_i hT
  guard_hyp hT := IsScalarTower.of_algebraMap_eq' rfl
  trivial

/-- Synthesize `Module.Finite` from morphism property. -/
example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Finite) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Module.Finite A B := inferInstance
  algebraize f
  rename_i h
  guard_hyp h : Module.Finite A B
  trivial

/-- Synthesize `Algebra.FiniteType` from morphism property. -/
example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FiniteType) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra.FiniteType A B := inferInstance
  algebraize f
  rename_i h
  guard_hyp h : Algebra.FiniteType A B
  trivial

/-- Synthesize `Algebra.Flat` from morphism property. -/
example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra.Flat A B := inferInstance
  algebraize f
  rename_i h
  guard_hyp h : Algebra.Flat A B
  trivial

/-- Synthesize `Algebra.Integral` from morphism property. -/
example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.IsIntegral) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra.IsIntegral A B := inferInstance
  algebraize f
  rename_i h
  guard_hyp h : Algebra.IsIntegral A B
  trivial

/-- Synthesize from morphism property of a composition (and check that tower is also synthesized). -/
example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (hfg : (g.comp f).Flat) : True := by
  fail_if_success -- Check that this instance is not available by default
    have h : Algebra.Flat A C := inferInstance
  fail_if_success
    have h : IsScalarTower A B C := inferInstance
  algebraize f g (g.comp f)
  rename_i h₂ h₁
  guard_hyp h₁ : Algebra.Flat A C
  guard_hyp h₂ := IsScalarTower.of_algebraMap_eq' rfl
  trivial
