/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Anne Baanen
-/
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Algebra.Tower

/-!
# Subalgebras in towers of algebras

In this file we prove facts about subalgebras in towers of algebra.

An algebra tower A/S/R is expressed by having instances of `Algebra A S`,
`Algebra R S`, `Algebra R A` and `IsScalarTower R S A`, the later asserting the
compatibility condition `(r • s) • a = r • (s • a)`.

## Main results

* `IsScalarTower.Subalgebra`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S/S₀` is a tower
* `IsScalarTower.Subalgebra'`: if `A/S/R` is a tower and `S₀` is a subalgebra
  between `S` and `R`, then `A/S₀/R` is a tower
* `Subalgebra.restrictScalars`: turn an `S`-subalgebra of `A` into an `R`-subalgebra of `A`,
  given that `A/S/R` is a tower

-/


open Pointwise

universe u v w u₁ v₁

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

namespace Algebra

variable [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {A}

theorem lmul_algebraMap (x : R) : Algebra.lmul R A (algebraMap R A x) = Algebra.lsmul R R A x :=
  Eq.symm <| LinearMap.ext <| smul_def x

end Algebra

namespace IsScalarTower

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A]
variable [Algebra R S] [Algebra S A]

instance subalgebra (S₀ : Subalgebra R S) : IsScalarTower S₀ S A :=
  of_algebraMap_eq fun _ ↦ rfl

variable [Algebra R A] [IsScalarTower R S A]

instance subalgebra' (S₀ : Subalgebra R S) : IsScalarTower R S₀ A :=
  @IsScalarTower.of_algebraMap_eq R S₀ A _ _ _ _ _ _ fun _ ↦
    (IsScalarTower.algebraMap_apply R S A _ :)

end Semiring

end IsScalarTower

namespace Subalgebra

open IsScalarTower

section Semiring

variable {S A B} [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra R A] [Algebra S B] [Algebra R B]
variable [IsScalarTower R S A] [IsScalarTower R S B]

/-- Given a tower `A / ↥U / S / R` of algebras, where `U` is an `S`-subalgebra of `A`, reinterpret
`U` as an `R`-subalgebra of `A`. -/
def restrictScalars (U : Subalgebra S A) : Subalgebra R A :=
  { U with
    algebraMap_mem' := fun x ↦ by
      rw [algebraMap_apply R S A]
      exact U.algebraMap_mem _ }

@[simp]
theorem coe_restrictScalars {U : Subalgebra S A} : (restrictScalars R U : Set A) = (U : Set A) :=
  rfl

@[simp]
theorem restrictScalars_top : restrictScalars R (⊤ : Subalgebra S A) = ⊤ :=
  SetLike.coe_injective <| by dsimp -- Porting note: why does `rfl` not work instead of `by dsimp`?

@[simp]
theorem restrictScalars_toSubmodule {U : Subalgebra S A} :
    Subalgebra.toSubmodule (U.restrictScalars R) = U.toSubmodule.restrictScalars R :=
  SetLike.coe_injective rfl

@[simp]
theorem mem_restrictScalars {U : Subalgebra S A} {x : A} : x ∈ restrictScalars R U ↔ x ∈ U :=
  Iff.rfl

theorem restrictScalars_injective :
    Function.Injective (restrictScalars R : Subalgebra S A → Subalgebra R A) := fun U V H ↦
  ext fun x ↦ by rw [← mem_restrictScalars R, H, mem_restrictScalars]

/-- Produces an `R`-algebra map from `U.restrictScalars R` given an `S`-algebra map from `U`.

This is a special case of `AlgHom.restrictScalars` that can be helpful in elaboration. -/
@[simp]
def ofRestrictScalars (U : Subalgebra S A) (f : U →ₐ[S] B) : U.restrictScalars R →ₐ[R] B :=
  f.restrictScalars R

end Semiring

section CommSemiring

@[simp]
lemma range_isScalarTower_toAlgHom [CommSemiring R] [CommSemiring A]
    [Algebra R A] (S : Subalgebra R A) :
    LinearMap.range (IsScalarTower.toAlgHom R S A) = Subalgebra.toSubmodule S := by
  ext
  simp only [← Submodule.range_subtype (Subalgebra.toSubmodule S), LinearMap.mem_range,
    IsScalarTower.coe_toAlgHom', Subalgebra.mem_toSubmodule]
  rfl

end CommSemiring

end Subalgebra

namespace IsScalarTower

open Subalgebra

variable [CommSemiring R] [CommSemiring S] [CommSemiring A]
variable [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

theorem adjoin_range_toAlgHom (t : Set A) :
    (Algebra.adjoin (toAlgHom R S A).range t).restrictScalars R =
      (Algebra.adjoin S t).restrictScalars R :=
  Subalgebra.ext fun z ↦
    show z ∈ Subsemiring.closure (Set.range (algebraMap (toAlgHom R S A).range A) ∪ t : Set A) ↔
         z ∈ Subsemiring.closure (Set.range (algebraMap S A) ∪ t : Set A) by
      suffices Set.range (algebraMap (toAlgHom R S A).range A) = Set.range (algebraMap S A) by
        rw [this]
      ext z
      exact ⟨fun ⟨⟨_, y, h1⟩, h2⟩ ↦ ⟨y, h2 ▸ h1⟩, fun ⟨y, hy⟩ ↦ ⟨⟨z, y, hy⟩, rfl⟩⟩

end IsScalarTower
