/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of the symmetric algebra

In this file we prove that a derivation of `SymmetricAlgebra R M` is determined by its values on
the generators. We also provide a constructor `SymmetricAlgebra.mkDerivation` that builds a
derivation from its values on the generators and a linear equivalence
`SymmetricAlgebra.mkDerivationEquiv` between `M →ₗ[R] N` and
`Derivation R (SymmetricAlgebra R M) N`.
-/

@[expose] public section

namespace SymmetricAlgebra

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Module (SymmetricAlgebra R M) N]

@[ext]
theorem derivation_ext {D₁ D₂ : Derivation R (SymmetricAlgebra R M) N}
    (h : ∀ x, D₁ (ι R M x) = D₂ (ι R M x)) : D₁ = D₂ :=
  Derivation.ext_of_adjoin_eq_top _ adjoin_range_ι (Set.forall_mem_range.2 h)

variable [IsScalarTower R (SymmetricAlgebra R M) N]

section

open TrivSqZeroExt

/-- The right action of the commutative algebra `SymmetricAlgebra R M` on `N` needed by
`TrivSqZeroExt`; it agrees with the left action. -/
local instance : Module (SymmetricAlgebra R M)ᵐᵒᵖ N :=
  Module.compHom N ((RingHom.id (SymmetricAlgebra R M)).fromOpposite mul_comm)

local instance : IsCentralScalar (SymmetricAlgebra R M) N := ⟨fun _ _ => rfl⟩

/-- The algebra homomorphism into the trivial square-zero extension lifting
`x ↦ (ι R M x, f x)`. Its first component is the identity and its second component is
`mkDerivation f`; use `SymmetricAlgebra.mkDerivation` instead. -/
def liftTrivSqZeroExt (f : M →ₗ[R] N) :
    SymmetricAlgebra R M →ₐ[R] TrivSqZeroExt (SymmetricAlgebra R M) N :=
  lift <| (inlAlgHom R (SymmetricAlgebra R M) N).toLinearMap ∘ₗ ι R M +
    (inrHom (SymmetricAlgebra R M) N).restrictScalars R ∘ₗ f

theorem fst_liftTrivSqZeroExt (f : M →ₗ[R] N) (a : SymmetricAlgebra R M) :
    (liftTrivSqZeroExt f a).fst = a := by
  have : (fstHom R (SymmetricAlgebra R M) N).comp (liftTrivSqZeroExt f) = .id R _ :=
    algHom_ext <| LinearMap.ext fun x => by simp [liftTrivSqZeroExt]
  exact AlgHom.congr_fun this a

/-- The derivation on `SymmetricAlgebra R M` that takes the value `f x` on `ι R M x`. -/
def mkDerivation (f : M →ₗ[R] N) : Derivation R (SymmetricAlgebra R M) N where
  toLinearMap :=
    (sndHom (SymmetricAlgebra R M) N).restrictScalars R ∘ₗ (liftTrivSqZeroExt f).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' a b := by simp [snd_mul, fst_liftTrivSqZeroExt]

@[simp]
theorem mkDerivation_ι (f : M →ₗ[R] N) (x : M) : mkDerivation f (ι R M x) = f x := by
  simp [mkDerivation, liftTrivSqZeroExt]

end

/-- `SymmetricAlgebra.mkDerivation` as a linear equivalence. -/
def mkDerivationEquiv : (M →ₗ[R] N) ≃ₗ[R] Derivation R (SymmetricAlgebra R M) N :=
  LinearEquiv.symm
    { toFun := fun D => (D : SymmetricAlgebra R M →ₗ[R] N) ∘ₗ ι R M
      invFun := mkDerivation
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => derivation_ext <| mkDerivation_ι _
      right_inv := fun _ => LinearMap.ext <| mkDerivation_ι _ }

@[simp]
theorem mkDerivationEquiv_apply (f : M →ₗ[R] N) : mkDerivationEquiv f = mkDerivation f :=
  rfl

@[simp]
theorem mkDerivationEquiv_symm_apply (D : Derivation R (SymmetricAlgebra R M) N) :
    mkDerivationEquiv.symm D = (D : SymmetricAlgebra R M →ₗ[R] N) ∘ₗ ι R M :=
  rfl

end SymmetricAlgebra

end
