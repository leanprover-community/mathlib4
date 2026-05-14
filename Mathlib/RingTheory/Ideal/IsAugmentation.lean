/-
Copyright (c) 2026 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.SetLike

/-! # Augmentation ideals

* `Ideal.IsAugmentation` :  An ideal `I` of an `A`-algebra `S` is an augmentation ideal
  if its underlying submodule is a complement of `1 : Submodule A S`.

* `Ideal.isAugmentation_subalgebra_iff` : If `S` is a subalgebra of an `R`-algebra `A`,
  then an ideal `I`of `A` is an augmentation ideal for the `R`-algebra structure if and only if
  it is an augmentation ideal for the `S`-algebra structure.

-/

@[expose] public section

namespace Ideal

variable (R : Type*) [CommSemiring R] {A : Type*}

open Submodule Subalgebra

/-- An ideal `I` of an `R`-algebra `A` is an augmentation ideal
if its underlying module is a complement to `1 : Submodule R A`. -/
def IsAugmentation [Semiring A] [Algebra R A] (I : Ideal A) : Prop :=
  IsCompl 1 (I.restrictScalars R)

lemma isAugmentation_iff [Semiring A] [Algebra R A] (I : Ideal A) :
    I.IsAugmentation R ↔ IsCompl 1 (I.restrictScalars R) := Iff.rfl

/-- If `S` is a subalgebra of an `R`-algebra `A`, then an ideal `I`of `A` is an augmentation ideal
for the `R`-algebra structure
if and only if it is an augmentation ideal for the `S`-algebra structure. -/
theorem isAugmentation_subalgebra_iff [CommSemiring A] [Algebra R A]
    {S : Subalgebra R A} {I : Ideal A} :
    I.IsAugmentation S ↔ IsCompl S.toSubmodule (I.restrictScalars R) := by
  simp [Ideal.IsAugmentation, ← Submodule.isCompl_restrictScalars_iff R]

end Ideal

end
