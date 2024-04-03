/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

#align_import linear_algebra.multilinear.finite_dimensional from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

/-! # Multilinear maps over finite dimensional spaces

The main results are that multilinear maps over finitely-generated, free modules are
finitely-generated and free.

* `Module.Finite.multilinearMap`
* `Module.Free.multilinearMap`

We do not put this in `LinearAlgebra.Multilinear.Basic` to avoid making the imports too large
there.
-/


namespace MultilinearMap

variable {ι R M₂ : Type*} {M₁ : ι → Type*}
variable [Finite ι]
variable [CommRing R] [AddCommGroup M₂] [Module R M₂]
variable [Module.Finite R M₂] [Module.Free R M₂]

-- Porting note: split out from `free_and_finite` because of inscrutable typeclass errors
private theorem free_and_finite_fin (n : ℕ) (N : Fin n → Type*) [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] [∀ i, Module.Finite R (N i)] [∀ i, Module.Free R (N i)] :
    Module.Free R (MultilinearMap R N M₂) ∧ Module.Finite R (MultilinearMap R N M₂) := by
  induction' n with n ih
  · haveI : IsEmpty (Fin Nat.zero) := inferInstanceAs (IsEmpty (Fin 0))
    exact
      ⟨Module.Free.of_equiv (constLinearEquivOfIsEmpty R R N M₂),
        Module.Finite.equiv (constLinearEquivOfIsEmpty R R N M₂)⟩
  · suffices
      Module.Free R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂) ∧
        Module.Finite R (N 0 →ₗ[R] MultilinearMap R (fun i : Fin n => N i.succ) M₂) by
      cases this
      exact
        ⟨Module.Free.of_equiv (multilinearCurryLeftEquiv R N M₂),
          Module.Finite.equiv (multilinearCurryLeftEquiv R N M₂)⟩
    cases ih fun i => N i.succ
    exact ⟨Module.Free.linearMap _ _ _ _, Module.Finite.linearMap _ _ _ _⟩

variable [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)]
variable [∀ i, Module.Finite R (M₁ i)] [∀ i, Module.Free R (M₁ i)]

-- the induction requires us to show both at once
private theorem free_and_finite :
    Module.Free R (MultilinearMap R M₁ M₂) ∧ Module.Finite R (MultilinearMap R M₁ M₂) := by
  cases nonempty_fintype ι
  have := @free_and_finite_fin R M₂ _ _ _ _ _ (Fintype.card ι)
    (fun x => M₁ ((Fintype.equivFin ι).symm x))
  cases' this with l r
  have e := domDomCongrLinearEquiv' R R M₁ M₂ (Fintype.equivFin ι)
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

instance _root_.Module.Finite.multilinearMap : Module.Finite R (MultilinearMap R M₁ M₂) :=
  free_and_finite.2
#align module.finite.multilinear_map Module.Finite.multilinearMap

instance _root_.Module.Free.multilinearMap : Module.Free R (MultilinearMap R M₁ M₂) :=
  free_and_finite.1
#align module.free.multilinear_map Module.Free.multilinearMap

end MultilinearMap
