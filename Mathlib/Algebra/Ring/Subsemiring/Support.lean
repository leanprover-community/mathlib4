/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Support
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Ring.Subsemiring.Basic
public import Mathlib.Algebra.Ring.SumsOfSquares
public import Mathlib.RingTheory.Ideal.Defs

/-!
# Supports of subsemirings

Let `R` be a ring, and let `S` be a subsemiring of `R`.
If `S` generates `R` as a subring, then the support of `S` forms an ideal.

## Main definitions

* `Subsemiring.supportIdeal`: the support of a subsemiring, as an ideal.
-/

public section

section Ring

variable {R : Type*} [Ring R] {S : Subsemiring R}

namespace Subsemiring

theorem mem_support {x : R} : x ∈ S.support ↔ x ∈ S ∧ -x ∈ S := by simp

theorem isPointed_def : S.IsPointed ↔ ∀ {x}, x ∈ S → -x ∈ S → x = 0 := by
  simp [AddSubmonoid.IsPointed]

theorem isSpanning_def : S.IsSpanning ↔ ∀ a, a ∈ S ∨ -a ∈ S := by simp [AddSubmonoid.IsSpanning]

/--
The support `S ∩ -S` of a subsemiring `S`, as an ideal.
We restrict to subsemirings that span the whole ring as subrings
because the support of a subsemiring does not form an ideal in general.
-/
@[expose, simps!]
def supportIdeal (hS : S.IsSpanning) : Ideal R where
  __ : AddSubgroup R := S.toAddSubmonoid.support
  smul_mem' x a ha := by
    have {x y} (hx : -x ∈ S) (hy : -y ∈ S) : x * y ∈ S := by simpa using mul_mem hx hy
    simp_all [isSpanning_def]
    grind [mul_mem, neg_mul_mem, mul_neg_mem]

@[simp] theorem mem_supportIdeal {S : Subsemiring R} (hS : S.IsSpanning) {x : R} :
    x ∈ S.supportIdeal hS ↔ x ∈ S.support := .rfl

@[simp] theorem supportIdeal_toAddSubgroup {S : Subsemiring R} (hS : S.IsSpanning) :
    (S.supportIdeal hS).toAddSubgroup = S.support := rfl

variable {R' : Type*} [Ring R'] {f : R →+* R'} {S' : Subsemiring R'}

variable (f) in
protected theorem IsSpanning.comap (hS' : S'.IsSpanning) : (S'.comap f).IsSpanning :=
  hS'.comap f.toAddMonoidHom

protected theorem IsSpanning.map (hS : S.IsSpanning) (hf : Function.Surjective f) :
    (S.map f).IsSpanning :=
  hS.map (f := f.toAddMonoidHom) hf

end Subsemiring

theorem AddSubmonoid.IsPointed.neg_one_notMem [Nontrivial R] (hS : S.IsPointed) :
    -1 ∉ S := by grind [Subsemiring.isPointed_def, one_mem, zero_ne_one']

end Ring

section CommRing

variable {R : Type*} [CommRing R] (S : Subsemiring R)

theorem AddSubmonoid.IsSpanning.mem_of_isSquare (hS : S.IsSpanning) {x : R} :
    IsSquare x → x ∈ S := by
  rintro ⟨y, rfl⟩
  rcases (Subsemiring.isSpanning_def.mp hS) y with hy | hy
  · exact mul_mem hy hy
  · simpa using mul_mem hy hy

grind_pattern [membership] AddSubmonoid.IsSpanning.mem_of_isSquare => S.IsSpanning, x ∈ S

theorem AddSubmonoid.IsSpanning.sumSq_le (hS : S.IsSpanning) : .sumSq R ≤ S := by
  rw [← Subsemiring.closure_isSquare, Subsemiring.closure_le]
  exact fun _ ↦ hS.mem_of_isSquare

theorem AddSubmonoid.IsSpanning.mem_of_isSumSq (hS : S.IsSpanning)
    {x : R} (hx : IsSumSq x) : x ∈ S := by
  grind [membership, hS.sumSq_le, Subsemiring.mem_sumSq]

grind_pattern [membership] AddSubmonoid.IsSpanning.mem_of_isSumSq => S.IsSpanning, x ∈ S

end CommRing
