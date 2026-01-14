/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
# Integral algebras

## Main definitions

Let `R` be a `CommRing` and let `A` be an R-algebra.

* `Algebra.IsIntegral R A` : An algebra is integral if every element of the extension is integral
  over the base ring.
-/


open Polynomial Submodule

section Ring

variable {R S A : Type*}
variable [CommRing R] [Ring A] [Ring S] (f : R →+* S)

variable [Algebra R A] (R)

variable (A)

/-- An algebra is integral if every element of the extension is integral over the base ring. -/
@[mk_iff] protected class Algebra.IsIntegral : Prop where
  isIntegral : ∀ x : A, IsIntegral R x

variable {R A}

lemma Algebra.isIntegral_def : Algebra.IsIntegral R A ↔ ∀ x : A, IsIntegral R x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

lemma algebraMap_isIntegral_iff : (algebraMap R A).IsIntegral ↔ Algebra.IsIntegral R A :=
  (Algebra.isIntegral_iff ..).symm

end Ring
