/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
import Mathlib.LinearAlgebra.Basis.Mk

/-!
# Bases

Further results on bases in modules and vector spaces.

-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

namespace Basis

instance uniqueBasis [Subsingleton R] : Unique (Basis ι R M) :=
  ⟨⟨⟨default⟩⟩, fun ⟨b⟩ => by rw [Subsingleton.elim b]⟩

variable (b : Basis ι R M)

section Singleton

/-- `Basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`. -/
protected def singleton (ι R : Type*) [Unique ι] [Semiring R] : Basis ι R R :=
  ofRepr
    { toFun := fun x => Finsupp.single default x
      invFun := fun f => f default
      left_inv := fun x => by simp
      right_inv := fun f => Finsupp.unique_ext (by simp)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }

@[simp]
theorem singleton_apply (ι R : Type*) [Unique ι] [Semiring R] (i) : Basis.singleton ι R i = 1 :=
  apply_eq_iff.mpr (by simp [Basis.singleton])

@[simp]
theorem singleton_repr (ι R : Type*) [Unique ι] [Semiring R] (x i) :
    (Basis.singleton ι R).repr x i = x := by simp [Basis.singleton, Unique.eq_default i]

end Singleton

section Empty

variable (M)

/-- If `M` is a subsingleton and `ι` is empty, this is the unique `ι`-indexed basis for `M`. -/
protected def empty [Subsingleton M] [IsEmpty ι] : Basis ι R M :=
  ofRepr 0

instance emptyUnique [Subsingleton M] [IsEmpty ι] : Unique (Basis ι R M) where
  default := Basis.empty M
  uniq := fun _ => congr_arg ofRepr <| Subsingleton.elim _ _

end Empty

section NoZeroSMulDivisors

end NoZeroSMulDivisors

section Singleton

theorem basis_singleton_iff {R M : Type*} [Ring R] [Nontrivial R] [AddCommGroup M] [Module R M]
    [NoZeroSMulDivisors R M] (ι : Type*) [Unique ι] :
    Nonempty (Basis ι R M) ↔ ∃ x ≠ 0, ∀ y : M, ∃ r : R, r • x = y := by
  constructor
  · rintro ⟨b⟩
    refine ⟨b default, b.linearIndependent.ne_zero _, ?_⟩
    simpa [span_singleton_eq_top_iff, Set.range_unique] using b.span_eq
  · rintro ⟨x, nz, w⟩
    refine ⟨ofRepr <| LinearEquiv.symm
      { toFun := fun f => f default • x
        invFun := fun y => Finsupp.single default (w y).choose
        left_inv := fun f => Finsupp.unique_ext ?_
        right_inv := fun y => ?_
        map_add' := fun y z => ?_
        map_smul' := fun c y => ?_ }⟩
    · simp [Finsupp.add_apply, add_smul]
    · simp only [Finsupp.coe_smul, Pi.smul_apply, RingHom.id_apply]
      rw [← smul_assoc]
    · refine smul_left_injective _ nz ?_
      simp only [Finsupp.single_eq_same]
      exact (w (f default • x)).choose_spec
    · simp only [Finsupp.single_eq_same]
      exact (w y).choose_spec

end Singleton

end Basis

end Module
