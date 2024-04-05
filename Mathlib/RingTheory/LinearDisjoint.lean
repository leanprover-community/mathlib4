/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.LinearAlgebra.LinearDisjoint

/-!

# Linearly disjoint of subalgebras

This file contains basics about the linearly disjoint of subalgebras.

## Main definitions

- ...

## Main results

- ...

## Tags

linearly disjoint, linearly independent, tensor product

## TODO

- ...

-/

open scoped Classical TensorProduct

noncomputable section

universe u v w

namespace Subalgebra

variable {R : Type u} {S : Type v}

section Semiring

variable [CommSemiring R] [Semiring S] [Algebra R S]

variable (A B : Subalgebra R S)

/-- If `A` and `B` are subalgebras of `S / R`,
then `A` and `B` are linearly disjoint, if they are linearly disjoint as submodules of `S`. -/
protected def LinearDisjoint : Prop :=
  (Subalgebra.toSubmodule A).LinearDisjoint (Subalgebra.toSubmodule B)

variable {A B}

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem LinearDisjoint.symm_of_commute (H : A.LinearDisjoint B)
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : B.LinearDisjoint A :=
  Submodule.LinearDisjoint.symm_of_commute H hc

/-- Linearly disjoint is symmetric if elements in the module commute. -/
theorem linearDisjoint_symm_of_commute
    (hc : ∀ (a : A) (b : B), Commute a.1 b.1) : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨fun H ↦ H.symm_of_commute hc, fun H ↦ H.symm_of_commute fun _ _ ↦ (hc _ _).symm⟩

namespace LinearDisjoint

variable (A B)

-- skip of_map_linearIndependent_left' ??

-- skip of_map_linearIndependent_right' ??

-- skip of_map_linearIndependent_mul' ??

theorem of_bot_left : (⊥ : Subalgebra R S).LinearDisjoint B :=
  Submodule.LinearDisjoint.of_self_left _

theorem of_bot_right : A.LinearDisjoint ⊥ :=
  Submodule.LinearDisjoint.of_self_right _

-- skip of_linearDisjoint_finite_left ?? (not correct ??)

-- skip of_linearDisjoint_finite_right ?? (not correct ??)

-- skip of_linearDisjoint_finite ?? (not correct ??)

end LinearDisjoint

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S] [Algebra R S]

variable {A B : Subalgebra R S}

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem LinearDisjoint.symm (H : A.LinearDisjoint B) : B.LinearDisjoint A :=
  H.symm_of_commute fun _ _ ↦ mul_comm _ _

/-- Linearly disjoint is symmetric in a commutative ring. -/
theorem linearDisjoint_symm : A.LinearDisjoint B ↔ B.LinearDisjoint A :=
  ⟨LinearDisjoint.symm, LinearDisjoint.symm⟩

end CommSemiring

end Subalgebra
