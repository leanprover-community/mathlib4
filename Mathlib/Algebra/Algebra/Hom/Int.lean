/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import Mathlib.Algebra.Algebra.Hom.Basic

/-!
# Homomorphisms of `ℤ`-algebras

-/


namespace RingHom

variable {R S : Type*}

/-- Reinterpret a `RingHom` as a `ℤ`-algebra homomorphism. -/
def toIntAlgHom [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] (f : R →+* S) : R →ₐ[ℤ] S :=
  { f with commutes' := fun n => by simp }
#align ring_hom.to_int_alg_hom RingHom.toIntAlgHom

lemma toIntAlgHom_injective [Ring R] [Ring S] [Algebra ℤ R] [Algebra ℤ S] :
    Function.Injective (RingHom.toIntAlgHom : (R →+* S) → _) :=
  fun _ _ e ↦ DFunLike.ext _ _ (fun x ↦ DFunLike.congr_fun e x)

