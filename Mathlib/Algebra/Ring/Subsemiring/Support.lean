/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Subsemiring.Defs
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Supports of subsemirings

Let `R` be a ring, and let `S` be a subsemiring of `R`.
If `S` generates `R` as a subring, then the support of `S` forms an ideal.

## Main definitions

* `Subsemiring.supportIdeal`: the support of a subsemiring, as an ideal.

-/

public section

variable {R : Type*} [Ring R]

namespace Subsemiring

variable {S : Subsemiring R}

theorem mem_support {x : R} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := by simp

theorem isPointed_def : S.IsPointed ↔ ∀ {x}, x ∈ S → -x ∈ S → x = 0 := by
  simp [AddSubmonoid.IsPointed]

theorem isSpanning_def : S.IsSpanning ↔ ∀ a, a ∈ S ∨ -a ∈ S := by simp [AddSubmonoid.IsSpanning]

theorem _root_.AddSubmonoid.IsPointed.neg_one_notMem [Nontrivial R] (hS : S.IsPointed) :
    -1 ∉ S := by grind [isPointed_def, one_mem, zero_ne_one']

@[expose, simps!]
def supportIdeal (hS : S.IsSpanning) : Ideal R where
  __ : AddSubgroup R := S.toAddSubmonoid.support
  smul_mem' x a ha := by
    have : ∀ {x y}, -x ∈ S → -y ∈ S → x * y ∈ S := fun hx hy ↦ by simpa using mul_mem hx hy
    simp_all [isSpanning_def]
    grind [mul_mem, neg_mul_mem, mul_neg_mem]

@[simp] theorem mem_supportIdeal {S : Subsemiring R} (hS : S.IsSpanning) {x : R} :
    x ∈ S.supportIdeal hS ↔ x ∈ S.support := .rfl

@[simp] theorem supportIdeal_toAddSubgroup {S : Subsemiring R} (hS : S.IsSpanning) :
    (S.supportIdeal hS).toAddSubgroup = S.support := rfl

variable {R R' : Type*} [Ring R] [Ring R'] {f : R →+* R'}
         {S T : Subsemiring R} {S' : Subsemiring R'} {s : Set (Subsemiring R)}

variable (f) in
theorem isSpanning_comap (hS' : S'.IsSpanning) : (S'.comap f).IsSpanning :=
  hS'.comap f.toAddMonoidHom

theorem isSpanning_map (hS : S.IsSpanning) (hf : Function.Surjective f) : (S.map f).IsSpanning :=
  hS.map (f := f.toAddMonoidHom) hf

end Subsemiring
