import Mathlib.Algebra.Module.Defs
import Mathlib.RingTheory.Flat.Basic

/-!
# Setup of Almost Ring Theory

In this file we define the basic setup of almost ring theory, and basic notations in almost
-/

open scoped TensorProduct

open Module

variable (V : Type*) [CommRing V] (m : Ideal V)

class AlmostPair : Prop where
  isIdempotent : IsIdempotentElem m
  flat_tensor : Flat V (m ⊗[V] m)
