/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.Ring.Defs
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.Data.Finset.Sym

/-!
# Finitely Supported Commutative multiplication

-/

section

variable {α R}

/-- A commutative magma with multiplicative zero. -/
class CommMagmaMulZeroClass (R : Type*) extends CommMagma R, MulZeroClass R

instance [CommSemiring R] : CommMagmaMulZeroClass R where
  zero_mul _ := zero_mul _
  mul_zero _ := mul_zero _

variable [CommMagmaMulZeroClass R]

lemma Sym2.mem_support_sym2_of_mul_ne_zero {f : α →₀ R} (p : Sym2 α) (hp : mul f p ≠ 0) :
    p ∈ f.support.sym2 := by
  obtain ⟨a,b⟩ := p
  simp only [Finset.mem_sym2_iff, mem_iff, Finsupp.mem_support_iff, ne_eq, forall_eq_or_imp,
    forall_eq]
  simp only [mul_sym2Mk, ne_eq] at hp
  aesop

/--
`Sym2.mul` as a `Finsupp`
-/
noncomputable def Sym2.mul_finsupp (f : α →₀ R) :
    Sym2 α →₀ R := Finsupp.onFinset
      f.support.sym2
    (Sym2.mul f) Sym2.mem_support_sym2_of_mul_ne_zero

lemma Sym2.mul_finsupp_support (f : α →₀ R) :
    (Sym2.mul_finsupp f).support ⊆ f.support.sym2 := fun p hp => by
  apply Sym2.mem_support_sym2_of_mul_ne_zero
  simp_all only [Finsupp.mem_support_iff, ne_eq]
  exact hp

end
