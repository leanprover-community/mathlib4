/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Sym.Sym2

/-!
# Finitely Supported Commutative multiplication

-/

section

variable {α R}

variable [CommMonoidWithZero R]

namespace Sym2

lemma sym2_support_eq_preimage_support_mul [NoZeroDivisors R] (f : α →₀ R) :
    f.support.sym2 = map f ⁻¹' mul.support := by
  ext ⟨a,b⟩
  simp_all

lemma mem_sym2_support_of_mul_ne_zero {f : α →₀ R} (p : Sym2 α) (hp : mul (p.map f) ≠ 0) :
    p ∈ f.support.sym2 := by
  obtain ⟨a,b⟩ := p
  simp only [Finset.mem_sym2_iff, mem_iff, Finsupp.mem_support_iff, ne_eq, forall_eq_or_imp,
    forall_eq]
  simp only [map_pair_eq, mul_mk, ne_eq] at hp
  aesop

/--
The composition of a `Finsupp` with `Sym2.mul` as a `Finsupp`
-/
noncomputable def mulFinsupp (f : α →₀ R) :
    Sym2 α →₀ R := Finsupp.onFinset
      f.support.sym2
    (fun p => mul (p.map f)) mem_sym2_support_of_mul_ne_zero

lemma support_mulFinsupp_subset (f : α →₀ R) :
    (mulFinsupp f).support ⊆ f.support.sym2 := fun p hp => by
  apply mem_sym2_support_of_mul_ne_zero
  simp_all only [Finsupp.mem_support_iff, ne_eq]
  exact hp

lemma mulFinsupp_eq_mul_comp_map (l : α →₀ R) : (mulFinsupp l) = mul ∘ map l := rfl

end Sym2

end
