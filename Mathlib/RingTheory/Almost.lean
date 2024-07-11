import Mathlib.Algebra.Module.Defs
import Mathlib.RingTheory.Flat.Basic

/-!
# Setup of Almost Ring Theory

In this file we define the basic setup of almost ring theory, and basic notations in almost

AlmostZero

AlmostInjective

AlmostSurjective

AlmostIsom

AlmostFree

AlmostFree module over V = Almost Free module over V/m

Goal: Lemma 4.1. Let M be an A-module which is π-adically complete and without π-torsion; let d ≥ 0. Then the A-module M is almost free of rank d if and only if the A/πA-module M/πM is almost free of rank d.
Let K be a perfectoid field of characteristic p, and L/K a finite field exten- sion. Then the OK-module OL (= the integral closure of OK inside L) is almost free of rank |L : K|.
-/

open scoped TensorProduct

open Module

variable {V : Type*} [CommRing V] (m : Ideal V)

class AlmostBasicSetup : Prop where
  isIdempotent : IsIdempotentElem m
  flat_tensor : Flat V (m ⊗[V] m)

def IsAlmostFreeOfRank {M : Type*} [Module V M] (d : ℕ) :
  ∀ e > 0, ∃
