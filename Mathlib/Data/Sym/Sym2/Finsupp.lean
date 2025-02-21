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

section

variable [DecidableEq R]

/--
Off-diagonal multiplication
-/
def mulOffDiag : R → R → R := fun a b => if a = b then (0 : R) else a * b

/--
Off-diagonal multiplication as a function from `Sym2`.
-/
def Sym2.mulOffDiag : Sym2 R → R := lift ⟨_root_.mulOffDiag, fun a b => by
  rw [_root_.mulOffDiag, _root_.mulOffDiag, mul_comm]
  simp_rw [eq_comm]⟩

@[simp]
lemma Sym2.mulOffDiag_mk (xy : R × R) :
    mulOffDiag (.mk xy) = if xy.1 = xy.2 then (0 : R) else xy.1 * xy.2 := rfl

lemma mem_sym2_support_of_mulOffDiag_ne_zero {f : α →₀ R} (p : Sym2 α)
    (hp : Sym2.mulOffDiag (p.map f) ≠ (0 : R)) : p ∈ f.support.sym2 := by
  obtain ⟨_, _⟩ := p
  aesop

/--
The composition of a `Finsupp` with `Sym2.mul` as a `Finsupp`
-/
noncomputable def Finsupp.mulOffDiag (f : α →₀ R) :
    Sym2 α →₀ R := Finsupp.onFinset
      f.support.sym2
    (fun p => Sym2.mulOffDiag (p.map f)) mem_sym2_support_of_mulOffDiag_ne_zero

end

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
noncomputable def _root_.Finsupp.sym2_mul (f : α →₀ R) :
    Sym2 α →₀ R := Finsupp.onFinset
      f.support.sym2
    (fun p => mul (p.map f)) mem_sym2_support_of_mul_ne_zero

lemma support_mulFinsupp_subset (f : α →₀ R) :
    f.sym2_mul.support ⊆ f.support.sym2 := fun p hp => by
  apply mem_sym2_support_of_mul_ne_zero
  simp_all only [Finsupp.mem_support_iff, ne_eq]
  exact hp

lemma mulFinsupp_eq_mul_comp_map (l : α →₀ R) : l.sym2_mul = mul ∘ map l := rfl

end Sym2

end
