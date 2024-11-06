/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# WithValuation

`WithValuation v` is a type synonym for a ring `R` which depends on an discrete valuation.

## Main definitions
 - `WithValuation` : type synonym for a semiring which depends on a discrete valuation. This is
  a function that takes a valuation on a ring and returns the ring. This can be used
  to assign and infer instances on a ring that depend on valuations.
 - `WithValuation.equiv v` : the canonical (type) equivalence between `WithValuation v` and `R`.
 - `WithValuation.ringEquiv v` : The canonical ring equivalence between `WithValuation v` and `R`.
 - `Valuation.completion` : the uniform space completion of a field `K` according to the
  uniform structure defined by the specified discrete valuation.
-/

noncomputable section

variable {R : Type*} {Γ₀ : outParam (Type*)} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

def WithValuation : Valuation R Γ₀ → Type _ := fun _ => R

namespace WithValuation

variable (v : Valuation R Γ₀)

/-- Canonical equivalence between `WithValuation v` and `R`. -/
def equiv : WithValuation v ≃ R := Equiv.refl (WithValuation v)

instance [Nontrivial R] : Nontrivial (WithValuation v) :=
  inferInstanceAs (Nontrivial R)

instance [Unique R] : Unique (WithValuation v) := inferInstanceAs (Unique R)

instance : Ring (WithValuation v) := inferInstanceAs (Ring R)

instance [CommRing R] : CommRing (WithValuation v) := inferInstanceAs (CommRing R)

instance [Field R] : Field (WithValuation v) := inferInstanceAs (Field R)

instance : Inhabited (WithValuation v) := ⟨0⟩

instance {S : Type*} [CommSemiring S] [CommRing R] [Algebra S R] : Algebra S (WithValuation v) :=
  inferInstanceAs (Algebra S R)

instance {S : Type*} [CommRing S] [CommRing R] [Algebra S R] [IsFractionRing S R] :
    IsFractionRing S (WithValuation v) :=
  inferInstanceAs (IsFractionRing S R)

instance valued (v : Valuation R Γ₀) : Valued (WithValuation v) Γ₀ :=
  Valued.mk' v

/-! `WithValuation.equiv` preserves the ring structure. -/

variable (x y : WithValuation v) (r s : R)
@[simp]
theorem equiv_zero : WithValuation.equiv v 0 = 0 := rfl

@[simp]
theorem equiv_symm_zero : (WithValuation.equiv v).symm 0 = 0 := rfl

@[simp]
theorem equiv_add : WithValuation.equiv v (x + y) =
    WithValuation.equiv v x + WithValuation.equiv v y := rfl

@[simp]
theorem equiv_symm_add :
    (WithValuation.equiv v).symm (r + s) =
      (WithValuation.equiv v).symm r + (WithValuation.equiv v).symm s :=
  rfl

@[simp]
theorem equiv_sub : WithValuation.equiv v (x - y) =
    WithValuation.equiv v x - WithValuation.equiv v y := rfl

@[simp]
theorem equiv_symm_sub :
    (WithValuation.equiv v).symm (r - s) =
      (WithValuation.equiv v).symm r - (WithValuation.equiv v).symm s :=
  rfl

@[simp]
theorem equiv_neg : WithValuation.equiv v (-x) = - WithValuation.equiv v x := rfl

@[simp]
theorem equiv_symm_neg : (WithValuation.equiv v).symm (-r) = - (WithValuation.equiv v).symm r := rfl

@[simp]
theorem equiv_mul : WithValuation.equiv v (x * y) =
    WithValuation.equiv v x * WithValuation.equiv v y := rfl

@[simp]
theorem equiv_symm_mul :
    (WithValuation.equiv v).symm (x * y) =
      (WithValuation.equiv v).symm x * (WithValuation.equiv v).symm y :=
  rfl

/-- `WithValuation.equiv` as a ring equivalence. -/
def ringEquiv : WithValuation v ≃+* R := RingEquiv.refl _

/-! The completion of a field at an absolute value. -/

end WithValuation

namespace Valuation

open WithValuation

variable {K : Type*} [Field K] (v : Valuation K Γ₀)

/-- The completion of a field with respect to a real absolute value. -/
abbrev completion := UniformSpace.Completion (WithValuation v)

instance : Coe K v.completion :=
  inferInstanceAs <| Coe (WithValuation v) (UniformSpace.Completion (WithValuation v))

end Valuation
