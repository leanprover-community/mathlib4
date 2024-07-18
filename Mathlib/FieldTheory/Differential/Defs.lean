import Mathlib.RingTheory.Derivation.DifferentialRing

class DifferentialField (R : Type*) extends Field R, CommDifferentialRing R

def DifferentialField.equiv {R R2 : Type*} [Field R] [CommDifferentialRing R2] (h : R ≃+* R2) :
    DifferentialField R :=
  letI := CommDifferentialRing.equiv h
  DifferentialField.mk this.deriv
