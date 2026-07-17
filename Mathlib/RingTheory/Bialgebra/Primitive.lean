/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv

/-!
# Primitive elements in a bialgebra

This file defines primitive elements in a bialgebra, i.e. elements `a` such that
`Δ a = a ⊗ₜ 1 + 1 ⊗ₜ a` and `ε a = 0`.

## Main declarations

* `IsPrimitiveElem R a`: `a` is a primitive element of the `R`-bialgebra.
* `primitiveSubmodule R A`: The submodule of primitive elements of `A`.

## TODO

* `primitiveSubmodule` is a `LieSubalgebra` with bracket `[a, b] = a * b - b * a`.
  (`IsPrimitiveElem.commutator` is stated with `a * b - b * a` rather than `⁅a, b⁆` to avoid
  importing Lie theory into this file.)
* In characteristic 0 over a field, the primitive elements of a cocommutative connected
  bialgebra generate it as the universal enveloping of a Lie algebra.
* Generalize to `(g, h)`-skew-primitive elements `Δ a = a ⊗ₜ g + h ⊗ₜ a` for group-like `g`, `h`
  over a plain coalgebra, of which primitivity is the `(1, 1)` case over a bialgebra.
-/

public section

open Coalgebra TensorProduct

variable {F R A B : Type*}

section Semiring
variable [CommSemiring R] [Semiring A] [Bialgebra R A] [Semiring B] [Bialgebra R B] {a b : A}

variable (R) in
/-- An element `a` of a bialgebra is *primitive* if `Δ a = a ⊗ₜ 1 + 1 ⊗ₜ a` and `ε a = 0`,
where `ε` and `Δ` are the counit and comultiplication respectively. -/
@[mk_iff]
structure IsPrimitiveElem (a : A) : Prop where
  /-- A primitive element `a` satisfies `ε(a) = 0`. -/
  counit_eq_zero : counit (R := R) a = 0
  /-- A primitive element `a` satisfies `Δ(a) = a ⊗ₜ 1 + 1 ⊗ₜ a`. -/
  comul_eq_tmul_add_tmul : comul a = a ⊗ₜ[R] 1 + 1 ⊗ₜ[R] a

attribute [simp] IsPrimitiveElem.counit_eq_zero IsPrimitiveElem.comul_eq_tmul_add_tmul

/-- In a bialgebra, `0` is a primitive element. -/
lemma IsPrimitiveElem.zero : IsPrimitiveElem R (0 : A) := by simp [isPrimitiveElem_iff]

/-- In a bialgebra over a nontrivial semiring, primitive elements are not `1`. -/
lemma IsPrimitiveElem.ne_one [Nontrivial R] (ha : IsPrimitiveElem R a) : a ≠ 1 :=
  ne_of_apply_ne (counit (R := R)) (by simp [ha])

/-- Primitive elements in a bialgebra are stable under addition. -/
lemma IsPrimitiveElem.add (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a + b) := ⟨by simp [ha, hb], by simp [ha, hb, add_tmul, tmul_add]; abel⟩

/-- Primitive elements in a bialgebra are stable under scalar multiplication. -/
lemma IsPrimitiveElem.smul (ha : IsPrimitiveElem R a) (r : R) : IsPrimitiveElem R (r • a) :=
  ⟨by simp [ha], by simp [ha, smul_add, smul_tmul']⟩

/-- A bialgebra homomorphism sends primitive elements to primitive elements. -/
lemma IsPrimitiveElem.map [FunLike F A B] [BialgHomClass F R A B] (f : F)
    (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (f a) :=
  ⟨by simp [ha], by simp [ha, ← CoalgHomClass.map_comp_comul_apply]⟩

/-- A bialgebra isomorphism preserves primitive elements. -/
@[simp] lemma isPrimitiveElem_map_equiv [EquivLike F A B] [BialgEquivClass F R A B] (f : F) :
    IsPrimitiveElem R (f a) ↔ IsPrimitiveElem R a where
  mp ha := (BialgEquivClass.toBialgEquiv f).symm_apply_apply a ▸ ha.map _
  mpr := .map f

variable (R A) in
/-- The primitive elements form a submodule. -/
def primitiveSubmodule : Submodule R A where
  carrier := {a | IsPrimitiveElem R a}
  add_mem' := .add
  zero_mem' := .zero
  smul_mem' r _ ha := ha.smul r

@[simp] lemma mem_primitiveSubmodule : a ∈ primitiveSubmodule R A ↔ IsPrimitiveElem R a := Iff.rfl

end Semiring

section Ring
variable [CommSemiring R] [Ring A] [Bialgebra R A] {a b : A}

/-- Primitive elements in a bialgebra are stable under negation. -/
lemma IsPrimitiveElem.neg (ha : IsPrimitiveElem R a) : IsPrimitiveElem R (-a) :=
  ⟨by simpa [ha] using (map_add (counit (R := R)) (-a) a).symm,
    by simp [ha, neg_tmul, tmul_neg, add_comm]⟩

/-- Primitive elements in a bialgebra are stable under subtraction. -/
lemma IsPrimitiveElem.sub (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a - b) := sub_eq_add_neg a b ▸ ha.add hb.neg

/-- The commutator `[a, b] = a * b - b * a` of two primitive elements is primitive. -/
lemma IsPrimitiveElem.commutator (ha : IsPrimitiveElem R a) (hb : IsPrimitiveElem R b) :
    IsPrimitiveElem R (a * b - b * a) :=
  ⟨by simpa [ha] using (map_add (counit (R := R)) (a * b - b * a) (b * a)).symm,
    by simp [ha, hb, add_mul, mul_add, sub_tmul, tmul_sub]; abel⟩

end Ring
