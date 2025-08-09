/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.Notation.Defs
import Mathlib.Logic.Function.Defs

/-!
# Regular elements

We introduce left-regular, right-regular and regular elements, along with their `to_additive`
analogues add-left-regular, add-right-regular and add-regular elements.

For monoids where _every_ element is regular, see `IsCancelMul` and nearby typeclasses.
-/

variable {R : Type*} [Mul R]

/-- A left-regular element is an element `c` such that multiplication on the left by `c`
is injective. -/
@[to_additive /-- An add-left-regular element is an element `c` such that addition
    on the left by `c` is injective. -/]
def IsLeftRegular (c : R) :=
  (c * ·).Injective

/-- A right-regular element is an element `c` such that multiplication on the right by `c`
is injective. -/
@[to_additive /-- An add-right-regular element is an element `c` such that addition
    on the right by `c` is injective. -/]
def IsRightRegular (c : R) :=
  (· * c).Injective

/-- An add-regular element is an element `c` such that addition by `c` both on the left and
on the right is injective. -/
structure IsAddRegular {R : Type*} [Add R] (c : R) : Prop where
  /-- An add-regular element `c` is left-regular -/
  left : IsAddLeftRegular c -- Porting note: It seems like to_additive is misbehaving
  /-- An add-regular element `c` is right-regular -/
  right : IsAddRightRegular c

/-- A regular element is an element `c` such that multiplication by `c` both on the left and
on the right is injective. -/
structure IsRegular (c : R) : Prop where
  /-- A regular element `c` is left-regular -/
  left : IsLeftRegular c
  /-- A regular element `c` is right-regular -/
  right : IsRightRegular c

attribute [simp] IsRegular.left IsRegular.right

attribute [to_additive] IsRegular

@[to_additive]
theorem isRegular_iff {c : R} : IsRegular c ↔ IsLeftRegular c ∧ IsRightRegular c :=
  ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩
