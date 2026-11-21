/-
Copyright (c) 2026 Viviana del Barco, Gustavo Infanti, Exequiel Rivas and Paul Schwahn.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Viviana del Barco, Gustavo Infanti, Exequiel Rivas, Paul Schwahn
-/
module

public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Quotient
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import Mathlib.RingTheory.TwoSidedIdeal.Basic


/-!
# Two-sided ideals in non-unital, non-associative algebras.

For a semiring `R` and a non-unital, non-associative semiring `A`
equipped with an `R`-module structure,
`NonUnitalNonAssocAlgebra.TwoSidedIdeal R A` consists of the
`R`-submodules of `A` that absorb multiplication on both sides.

When `R` is a ring and `A` is a non-unital, non-associative ring,
the quotient `A ⧸ I` inherits a non-unital, non-associative ring
structure and an `R`-module structure.

## Implementation notes

The quotient is defined as the quotient by `I.toSubmodule`.
Compatibility between scalar multiplication and multiplication
is not required for the ideal definition. The conditions
`SMulCommClass R A A` and `IsScalarTower R A A`, when available,
descend to the quotient.

-/

@[expose] public section

namespace NonUnitalNonAssocAlgebra

section definitions

variable (R : Type*) [Semiring R]
variable (A : Type*) [NonUnitalNonAssocSemiring A]
variable [Module R A]

/-- A two-sided ideal is an `R`-submodule closed under multiplication by arbitrary elements of `A`
on both sides. No compatibility between scalar multiplication and multiplication is required. -/
structure TwoSidedIdeal extends Submodule R A where
  left_mul_mem' (a : A) {x : A} : x ∈ carrier → a * x ∈ carrier
  right_mul_mem' (a : A) {x : A} : x ∈ carrier → x * a ∈ carrier

end definitions

namespace TwoSidedIdeal

variable (R : Type*) [Semiring R]
variable (A : Type*) [NonUnitalNonAssocSemiring A]
variable [Module R A]

instance : Coe (TwoSidedIdeal R A) (Submodule R A) where
  coe := TwoSidedIdeal.toSubmodule

attribute [coe] TwoSidedIdeal.toSubmodule

variable {R A}

instance : SetLike (TwoSidedIdeal R A) A where
  coe := fun I ↦ I.carrier
  coe_injective I J h := by
    cases I; cases J; congr;
    exact SetLike.coe_injective h

instance : PartialOrder (TwoSidedIdeal R A) := .ofSetLike (TwoSidedIdeal R A)

theorem left_mul_mem {I : TwoSidedIdeal R A} (a : A) (x : A) (hx : x ∈ I) : a * x ∈ I :=
  left_mul_mem' _ a hx

theorem right_mul_mem {I : TwoSidedIdeal R A} (a : A) (x : A) (hx : x ∈ I) : x * a ∈ I :=
  right_mul_mem' _ a hx

instance : Bot (TwoSidedIdeal R A) :=
  ⟨{ (⊥ : Submodule R A) with
    left_mul_mem' := by simp
    right_mul_mem' := by simp }⟩

instance : Top (TwoSidedIdeal R A) :=
  ⟨{ carrier := ⊤
     zero_mem' := by simp
     add_mem' := by simp
     smul_mem' := by simp
     left_mul_mem' := by simp
     right_mul_mem' := by simp }⟩

@[simp]
theorem mem_toSubmodule (I : TwoSidedIdeal R A) {x : A} :
    x ∈ I.toSubmodule ↔ x ∈ I :=
  Iff.rfl

@[simp]
theorem mem_top {x : A} :
    x ∈ (⊤ : TwoSidedIdeal R A) :=
  trivial

@[ext]
theorem ext {I J : TwoSidedIdeal R A} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  SetLike.ext h

@[simp]
theorem coe_toSubmodule (I : TwoSidedIdeal R A) : (toSubmodule I : Set A) = I := rfl

@[simp]
theorem bot_toSubmodule : (⊥ : TwoSidedIdeal R A).toSubmodule = ⊥ := rfl

@[simp]
theorem top_toSubmodule : (⊤ : TwoSidedIdeal R A).toSubmodule = ⊤ := rfl

@[simp]
theorem coe_top : ((⊤ : TwoSidedIdeal R A) : Set A) = Set.univ := rfl

instance : OrderTop (TwoSidedIdeal R A) where
  le_top _ _ _ := trivial

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : TwoSidedIdeal R A → Submodule R A) := fun x y h ↦ by
  cases x; cases y; congr

variable {R : Type*} [Ring R]
variable {A : Type*} [NonUnitalNonAssocRing A]
variable [Module R A]

instance instHasQuotient :
    HasQuotient A (TwoSidedIdeal R A) :=
  ⟨fun I ↦ A ⧸ I.toSubmodule⟩

namespace Quotient

variable {I : TwoSidedIdeal R A}

/-- The quotient map as a funtion. -/
def mk : A → A ⧸ I :=
  Quotient.mk''

theorem eq_submodule_quotient :
    (A ⧸ I) = (A ⧸ I.toSubmodule) :=
  rfl

instance : AddCommGroup (A ⧸ I) :=
  inferInstanceAs <| AddCommGroup (A ⧸ I.toSubmodule)

instance : Module R (A ⧸ I) :=
  inferInstanceAs <| Module R (A ⧸ I.toSubmodule)

instance : Mul (A ⧸ I) where
  mul := Quotient.map₂' (fun x y : A ↦ x * y) (by
    simp_rw [Submodule.quotientRel_def, mem_toSubmodule]
    intro a₁ a₂ ha b₁ b₂ hb
    have : a₁ * b₁ - a₂ * b₂ = a₁ * (b₁ - b₂) + (a₁ - a₂) * b₂ := by
      rw [mul_sub, sub_mul]
      exact (sub_add_sub_cancel _ _ _).symm
    rw [this]
    apply I.add_mem <;> rw [mem_toSubmodule]
    · exact left_mul_mem _ _ hb
    · exact right_mul_mem _ _ ha
  )


@[simp]
theorem mk_add {x y : A} : (mk (x + y) : A ⧸ I) = mk x + mk y :=
  rfl

@[simp]
theorem mk_neg {x : A} : (mk (-x) : A ⧸ I) = -(mk x) :=
  rfl

@[simp]
theorem mk_sub {x y : A} : (mk (x - y) : A ⧸ I) = mk x - mk y :=
  rfl

@[simp]
theorem mk_mul {x y : A} : (mk (x * y) : A ⧸ I) = mk x * mk y :=
  rfl

@[simp]
theorem mk_smul {r : R} {x : A} : (mk (r • x) : A ⧸ I) = r • mk x :=
  rfl

theorem eq {x y : A} : (mk x : A ⧸ I) = mk y ↔ x - y ∈ I :=
  Submodule.Quotient.eq I.toSubmodule

@[simp]
theorem mk_eq_zero {x : A} : (mk x : A ⧸ I) = 0 ↔ x ∈ I :=
  Submodule.Quotient.mk_eq_zero I.toSubmodule

@[simp]
theorem mk_zero : mk (0 : A) = (0 : A ⧸ I) := by rfl

instance : NonUnitalNonAssocRing (A ⧸ I) := fast_instance%
  Function.Surjective.nonUnitalNonAssocRing (R := A) (S := A ⧸ I) _ Quotient.mk''_surjective rfl
  (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

theorem induction_on {C : A ⧸ I → Prop} (x : A ⧸ I) (H : ∀ z, C (mk z)) :
    C x := Quotient.inductionOn' x H

/-- The quotient map as a morphism of non-unital algebras -/
def mkHom : A →ₙₐ[R] A ⧸ I where
    toFun := mk
    map_smul' := fun {_ _} ↦ mk_smul
    map_zero' := mk_zero
    map_add' := fun {_ _} ↦ mk_add
    map_mul' := fun {_ _} ↦ mk_mul

instance [SMulCommClass R A A] : SMulCommClass R (A ⧸ I) (A ⧸ I) where
  smul_comm := by
    intro r x
    apply induction_on x
    intro x y
    apply induction_on y
    intro y
    simp only [smul_eq_mul, ← mk_mul, ← mk_smul]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_comm]

instance [IsScalarTower R A A] : IsScalarTower R (A ⧸ I) (A ⧸ I) where
  smul_assoc := by
    intro r x
    apply induction_on x
    intro x y
    apply induction_on y
    intro y
    simp only [smul_eq_mul, ← mk_mul, ← mk_smul]
    rw [← smul_eq_mul, ← smul_eq_mul, smul_assoc]

end Quotient

end TwoSidedIdeal

end NonUnitalNonAssocAlgebra

namespace NonUnitalNonAssocAlgebra.TwoSidedIdeal

variable {R A : Type*} [Ring R] [NonUnitalNonAssocRing A] [Module R A]

/-- Forgetting the scalar multiplication, `TwoSidedIdeal R A` is a two-sided ring ideal of `A`. -/
def toTwoSidedIdeal (I : TwoSidedIdeal R A) : _root_.TwoSidedIdeal A
  :=
  _root_.TwoSidedIdeal.mk' (I : Set A) I.toSubmodule.zero_mem I.toSubmodule.add_mem
    I.toSubmodule.neg_mem (fun {x y} hy ↦ I.left_mul_mem x y hy)
      (fun {x y} hx ↦ I.right_mul_mem y x hx)

@[simp]
theorem mem_toTwoSidedIdeal (I : TwoSidedIdeal R A) {x : A} :
    x ∈ I.toTwoSidedIdeal ↔ x ∈ I := by
  simp [toTwoSidedIdeal]

end NonUnitalNonAssocAlgebra.TwoSidedIdeal
