/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# Isomorphism between `FreeAddCommGroup X` and `X →₀ ℤ`

In this file we construct the canonical isomorphism between `FreeAddCommGroup X` and `X →₀ ℤ`.
We use this to transport the notion of `support` from `Finsupp` to `FreeAddCommGroup`.

## Main declarations

- `FreeAddCommGroup.equivFinsupp`: group isomorphism between `FreeAddCommGroup X` and `X →₀ ℤ`
- `FreeAddCommGroup.coeff`: the multiplicity of `x : X` in `a : FreeAddCommGroup X`
- `FreeAddCommGroup.support`: the finset of `x : X` that occur in `a : FreeAddCommGroup X`
-/

@[expose] public section

assert_not_exists Cardinal Module.Basis

noncomputable section

variable {X : Type*}

/-- The group homomorphism `FreeAddCommGroup X →+ (X →₀ ℤ)`. -/
def FreeAddCommGroup.toFinsupp : FreeAddCommGroup X →+ X →₀ ℤ :=
  FreeAddCommGroup.lift fun x => Finsupp.single x (1 : ℤ)

/-- The group homomorphism `(X →₀ ℤ) →+ FreeAddCommGroup X`. -/
def Finsupp.toFreeAddCommGroup : (X →₀ ℤ) →+ FreeAddCommGroup X :=
  Finsupp.liftAddHom fun x => (smulAddHom ℤ (FreeAddCommGroup X)).flip (FreeAddCommGroup.of x)

@[simp] lemma FreeAddCommGroup.toFinsupp_of (x : X) : toFinsupp (of x) = .single x 1 := by
  simp [toFinsupp]

@[simp] lemma Finsupp.toFreeAddCommGroup_single (x : X) (n : ℤ) :
    toFreeAddCommGroup (single x n) = n • .of x := by simp [toFreeAddCommGroup]

open Finsupp FreeAddCommGroup

@[simp]
theorem Finsupp.toFreeAddCommGroup_comp_singleAddHom (x : X) :
    Finsupp.toFreeAddCommGroup.comp (Finsupp.singleAddHom x) =
      (smulAddHom ℤ (FreeAddCommGroup X)).flip (of x) :=
  AddMonoidHom.ext <| toFreeAddCommGroup_single _

@[simp]
theorem FreeAddCommGroup.toFinsupp_comp_toFreeAddCommGroup :
    toFinsupp.comp toFreeAddCommGroup = AddMonoidHom.id (X →₀ ℤ) := by
  ext
  simp

@[simp]
theorem Finsupp.toFreeAddCommGroup_comp_toFinsupp :
    toFreeAddCommGroup.comp toFinsupp = AddMonoidHom.id (FreeAddCommGroup X) := by
  ext
  rw [toFreeAddCommGroup, toFinsupp, AddMonoidHom.comp_apply, lift_apply_of,
    liftAddHom_apply_single, AddMonoidHom.flip_apply, smulAddHom_apply, one_smul,
    AddMonoidHom.id_apply]

@[simp]
theorem Finsupp.toFreeAddCommGroup_toFinsupp {X} (x : FreeAddCommGroup X) :
    Finsupp.toFreeAddCommGroup (FreeAddCommGroup.toFinsupp x) = x := by
  rw [← AddMonoidHom.comp_apply, Finsupp.toFreeAddCommGroup_comp_toFinsupp, AddMonoidHom.id_apply]

namespace FreeAddCommGroup

open Finsupp

@[simp]
theorem toFinsupp_toFreeAddCommGroup (f : X →₀ ℤ) :
    FreeAddCommGroup.toFinsupp (Finsupp.toFreeAddCommGroup f) = f := by
  rw [← AddMonoidHom.comp_apply, toFinsupp_comp_toFreeAddCommGroup, AddMonoidHom.id_apply]

variable (X)

/-- The additive equivalence between `FreeAddCommGroup X` and `(X →₀ ℤ)`. -/
@[simps!]
def equivFinsupp : FreeAddCommGroup X ≃+ (X →₀ ℤ) where
  toFun := toFinsupp
  invFun := toFreeAddCommGroup
  left_inv := toFreeAddCommGroup_toFinsupp
  right_inv := toFinsupp_toFreeAddCommGroup
  map_add' := toFinsupp.map_add

variable {X}

/-- `coeff x` is the additive group homomorphism `FreeAddCommGroup X →+ ℤ`
that sends `a` to the multiplicity of `x : X` in `a`. -/
def coeff (x : X) : FreeAddCommGroup X →+ ℤ :=
  (Finsupp.applyAddHom x).comp toFinsupp

/-- `support a` for `a : FreeAddCommGroup X` is the finite set of `x : X`
that occur in the formal sum `a`. -/
def support (a : FreeAddCommGroup X) : Finset X :=
  a.toFinsupp.support

@[simp]
theorem mem_support_iff (x : X) (a : FreeAddCommGroup X) : x ∈ a.support ↔ coeff x a ≠ 0 := by
  rw [support, Finsupp.mem_support_iff]
  exact Iff.rfl

theorem notMem_support_iff (x : X) (a : FreeAddCommGroup X) : x ∉ a.support ↔ coeff x a = 0 := by
  rw [support, Finsupp.notMem_support_iff]
  exact Iff.rfl

@[simp]
theorem support_zero : support (0 : FreeAddCommGroup X) = ∅ := by
  simp only [support, Finsupp.support_zero, map_zero]

@[simp]
theorem support_of (x : X) : support (of x) = {x} := by
  rw [support, toFinsupp_of, Finsupp.support_single _ one_ne_zero]

@[simp]
theorem support_neg (a : FreeAddCommGroup X) : support (-a) = support a := by
  simp only [support, map_neg, Finsupp.support_neg]

@[simp]
theorem support_zsmul (k : ℤ) (h : k ≠ 0) (a : FreeAddCommGroup X) :
    support (k • a) = support a := by
  ext x
  simp [h]

@[simp]
theorem support_nsmul (k : ℕ) (h : k ≠ 0) (a : FreeAddCommGroup X) :
    support (k • a) = support a := by
  apply support_zsmul k _ a
  exact mod_cast h

open scoped Classical in
theorem support_add (a b : FreeAddCommGroup X) : support (a + b) ⊆ a.support ∪ b.support := by
  simp only [support, map_add]
  apply Finsupp.support_add

@[simp] theorem support_eq_empty {a : FreeAddCommGroup X} : a.support = ∅ ↔ a = 0 :=
  Finsupp.support_eq_empty.trans (equivFinsupp X).map_eq_zero_iff

@[simp] theorem nonempty_support_iff {a : FreeAddCommGroup X} :
    a.support.Nonempty ↔ a ≠ 0 := by
  contrapose!; exact support_eq_empty

theorem card_support_eq_zero {a : FreeAddCommGroup X} : a.support.card = 0 ↔ a = 0 := by
  simp

theorem eq_sum_support_coeff_smul_of (a : FreeAddCommGroup X) :
    a = ∑ x ∈ a.support, coeff x a • of x := by
  conv_lhs => rw [← toFreeAddCommGroup_toFinsupp a, ← sum_single a.toFinsupp]
  simp [sum, support, coeff]

@[simp] lemma coeff_of_self (x : X) : coeff x (of x) = 1 := by simp [coeff]

@[simp] lemma coeff_of_of_ne {x y : X} (h : x ≠ y) : coeff x (of y) = 0 := by simp [coeff, h]

lemma coeff_of (x y : X) [Decidable (x = y)] : coeff x (of y) = if x = y then 1 else 0 := by
  aesop

end FreeAddCommGroup
