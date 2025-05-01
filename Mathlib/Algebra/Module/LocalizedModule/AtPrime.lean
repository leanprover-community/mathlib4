/-
Copyright (c) 2025 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Prime

/-!
# Localizations of modules at the complement of a prime ideal
-/

/-- Given a prime ideal `P` and `f : M →ₗ[R] M'`, `IsLocalizedModule.AtPrime P f` states that `M'`
  is isomorphic to the localization of `M` at the complement of `P`. -/
protected abbrev IsLocalizedModule.AtPrime {R M M' : Type*} [CommSemiring R] (P : Ideal R)
    [P.IsPrime] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M'] (f : M →ₗ[R] M') :=
  IsLocalizedModule P.primeCompl f

/-- Given a prime ideal `P`, `LocalizedModule.AtPrime P M` is a localization of `M`
  at the complement of `P`. -/
protected abbrev LocalizedModule.AtPrime {R : Type*} [CommSemiring R] (P : Ideal R) [P.IsPrime]
    (M : Type*) [AddCommMonoid M] [Module R M] :=
  LocalizedModule P.primeCompl M
