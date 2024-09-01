import Mathlib.RingTheory.Flat.Algebra
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs

example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) : True := by
  algebraize f
  have h : Algebra A B := inferInstance
  guard_hyp h : Algebra A B
  trivial

example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    True := by
  algebraize f g (g.comp f)
  have h₁ : Algebra A C := inferInstance
  guard_hyp h₁ : Algebra A C
  clear h₁
  have h₂ : IsScalarTower A B C := inferInstance
  guard_hyp h₂ : IsScalarTower A B C
  trivial

example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Finite) : True := by
  algebraize f
  have h : Module.Finite A B := inferInstance
  guard_hyp h : Module.Finite A B
  trivial

example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.FiniteType) : True := by
  algebraize f
  have h : Algebra.FiniteType A B := inferInstance
  guard_hyp h : Algebra.FiniteType A B
  trivial

example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.Flat) : True := by
  algebraize f
  have h : Algebra.Flat A B := inferInstance
  guard_hyp h : Algebra.Flat A B
  trivial

example (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (hf : f.IsIntegral) : True := by
  algebraize f
  have h : Algebra.IsIntegral A B := inferInstance
  guard_hyp h : Algebra.IsIntegral A B
  trivial

example (A B C : Type*) [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (hfg : (g.comp f).Flat) : True := by
  algebraize f g (g.comp f)
  have h₁ : Algebra.Flat A C := inferInstance
  guard_hyp h₁ : Algebra.Flat A C
  trivial
