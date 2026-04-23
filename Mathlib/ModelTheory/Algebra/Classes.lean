/-
Copyright (c) 2025 Dexin Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dexin Zhang
-/
module

public import Mathlib.ModelTheory.Definability

/-!
# Typeclasses for first-order languages

This file defines typeclasses for first-order languages contaning certain algebraic symbols, as well
as instances of `Add`, `Mul`, etc. on terms in the language.

## Main definitions

* `FirstOrder.Language.ZeroContants` etc.: typeclasses for first-order languages that have certain
  symbols.
* `FirstOrder.Language.Structure.CompatibleZero` etc.: typeclasses stating that a first-order
  structure `M` interprets first-order language symbols the same as its algebraic structure
  instance.
-/

@[expose] public section

namespace FirstOrder.Language

attribute [to_additive_ignore_args 2] Term

variable {L : Language} {α : Type*} {t t₁ t₂ : L.Term α}

/-- Type class for first-order langauges that have a constant symbol `0` for zero. -/
class ZeroConstant (L : Language) where
  zero : L.Constants

/-- Type class for first-order langauges that have a constant symbol `1` for one. -/
@[to_additive]
class OneConstant (L : Language) where
  one : L.Constants

/-- Constant `1`. -/
@[to_additive /-- Constant `0`. -/]
def Constants.one [OneConstant L] : L.Constants := OneConstant.one

/-- Type class for first-order languages that have a binary function symbol `+` for addition. -/
class AddFunction (L : Language) where
  add : L.Functions 2

/-- Type class for first-order languages that have a binary function symbol `*` for
multiplication. -/
@[to_additive]
class MulFunction (L : Language) where
  mul : L.Functions 2

/-- Binary function `*`. -/
@[to_additive /-- Binary function `+`. -/]
def Functions.mul [MulFunction L] : L.Functions 2 := MulFunction.mul

/-- Type class for first-order languages that have a unary function symbol `-` for negation. -/
class NegFunction (L : Language) where
  neg : L.Functions 1

/-- Type class for first-order languages that have a unary function symbol `⁻¹` for inverse. -/
@[to_additive]
class InvFunction (L : Language) where
  inv : L.Functions 1

/-- Unary function `⁻¹`. -/
@[to_additive /-- Unary function `-`. -/]
def Functions.inv [InvFunction L] : L.Functions 1 := InvFunction.inv

namespace Term

@[to_additive]
instance [OneConstant L] : One (L.Term α) where
  one := Constants.one.term

@[to_additive]
theorem one_def [OneConstant L] : (1 : L.Term α) = Constants.one.term := rfl

@[to_additive]
instance [MulFunction L] : Mul (L.Term α) where
  mul := Functions.mul.apply₂

@[to_additive]
theorem mul_def [MulFunction L] : t₁ * t₂ = Functions.mul.apply₂ t₁ t₂ := rfl

@[to_additive]
instance [InvFunction L] : Inv (L.Term α) where
  inv := Functions.inv.apply₁

@[to_additive]
theorem inv_def [InvFunction L] : t⁻¹ = Functions.inv.apply₁ t := rfl

section

variable [ZeroConstant L] [OneConstant L] [AddFunction L]

instance : NatCast (L.Term α) where
  natCast := Nat.unaryCast

@[simp, norm_cast] theorem natCast_zero : (0 : ℕ) = (0 : L.Term α) := rfl

@[simp, norm_cast] theorem natCast_succ (n : ℕ) : (n + 1 : ℕ) = (n : L.Term α) + 1 := rfl

end

section

variable [OneConstant L] [MulFunction L]

@[to_additive]
instance : Pow (L.Term α) ℕ where
  pow t n := npowRec n t

@[to_additive (attr := simp)]
theorem pow_zero : t ^ 0 = 1 := rfl

@[to_additive (attr := simp)]
theorem pow_succ {n : ℕ} : t ^ (n + 1) = t ^ n * t := rfl

/-- Product over a finite set of terms.

It is defined via choice, so the result only makes sense when the structure satisfies commutativity
(see `realize_prod`). -/
@[to_additive /-- Summation over a finite set of terms.

It is defined via choice, so the result only makes sense when the structure satisfies commutativity
(see `realize_sum`). -/]
noncomputable def prod {β : Type*} (s : Finset β) (f : β → L.Term α) : L.Term α :=
  (s.toList.map f).prod

end

end Term

namespace Structure

variable (L) (M : Type*) [L.Structure M]

/-- Type class stating that a first-order structure `M` interprets symbol `0` the same as its `Zero`
instance. -/
class CompatibleZero [ZeroConstant L] [Zero M] where
  funMap_zero : ∀ x, funMap (L := L) (M := M) Constants.zero x = 0

/-- Type class stating that a first-order structure `M` interprets symbol `1` the same as its `One`
instance. -/
@[to_additive]
class CompatibleOne [OneConstant L] [One M] where
  funMap_one : ∀ x, funMap (L := L) (M := M) Constants.one x = 1

/-- Type class stating that a first-order structure `M` interprets symbol `+` the same as its `Add`
instance. -/
class CompatibleAdd [AddFunction L] [Add M] where
  funMap_add : ∀ x, funMap (L := L) (M := M) Functions.add x = x 0 + x 1

/-- Type class stating that a first-order structure `M` interprets symbol `1` the same as its `One`
instance. -/
@[to_additive]
class CompatibleMul [MulFunction L] [Mul M] where
  funMap_mul : ∀ x, funMap (L := L) (M := M) Functions.mul x = x 0 * x 1

/-- Type class stating that a first-order structure `M` interprets symbol `-` the same as its `Neg`
instance. -/
class CompatibleNeg [NegFunction L] [Neg M] where
  funMap_neg : ∀ x, funMap (L := L) (M := M) Functions.neg x = -x 0

/-- Type class stating that a first-order structure `M` interprets symbol `⁻¹` the same as its `Inv`
instance. -/
@[to_additive]
class CompatibleInv [InvFunction L] [Inv M] where
  funMap_inv : ∀ x, funMap (L := L) (M := M) Functions.inv x = (x 0)⁻¹

attribute [simp] CompatibleZero.funMap_zero CompatibleOne.funMap_one CompatibleAdd.funMap_add
  CompatibleMul.funMap_mul CompatibleNeg.funMap_neg CompatibleInv.funMap_inv

variable {L M} {v : α → M}

@[to_additive (attr := simp)]
theorem realize_one [OneConstant L] [One M] [CompatibleOne L M] :
    Term.realize v (1 : L.Term α) = 1 := by
  simp [Term.one_def, constantMap]

@[to_additive (attr := simp)]
theorem realize_mul [MulFunction L] [Mul M] [CompatibleMul L M] :
    Term.realize v (t₁ * t₂) = Term.realize v t₁ * Term.realize v t₂ := by
  simp [Term.mul_def]

@[to_additive (attr := simp)]
theorem realize_inv [InvFunction L] [Inv M] [CompatibleInv L M] :
    Term.realize v t⁻¹ = (Term.realize v t)⁻¹ := by
  simp [Term.inv_def]

@[simp]
theorem realize_natCast [ZeroConstant L] [OneConstant L] [AddFunction L] [AddMonoidWithOne M]
    [CompatibleZero L M] [CompatibleOne L M] [CompatibleAdd L M] {n : ℕ} :
    Term.realize v (n : L.Term α) = n := by
  induction n <;> simp [*]

@[to_additive (attr := simp)]
theorem realize_npow [OneConstant L] [MulFunction L] [Monoid M] [CompatibleOne L M]
    [CompatibleMul L M] {n : ℕ} :
    Term.realize v (t ^ n) = Term.realize v t ^ n := by
  induction n <;> simp [pow_add, *]

@[to_additive (attr := simp)]
theorem realize_prod [OneConstant L] [MulFunction L] [CommMonoid M] [CompatibleOne L M]
    [CompatibleMul L M] {ι : Type*} {s : Finset ι} {f : ι → L.Term α} :
    Term.realize v (Term.prod s f) = ∏ i ∈ s, Term.realize v (f i) := by
  classical
  simp only [Term.prod]
  conv => rhs; rw [← s.toList_toFinset, List.prod_toFinset _ s.nodup_toList]
  generalize s.toList = l
  induction l with simp [*]

end FirstOrder.Language.Structure

open FirstOrder Language Structure

namespace Set

variable {L : Language} {M : Type*} [L.Structure M] {A : Set M} {α : Type*} {f g : (α → M) → M}

@[to_additive (attr := fun_prop)]
theorem DefinableFun.one [OneConstant L] [One M] [CompatibleOne L M] :
    A.DefinableFun L fun _ : α → M => 1 := by
  convert (1 : Term L α).definableFun_realize.of_empty
  simp

@[to_additive (attr := fun_prop)]
theorem DefinableFun.mul [MulFunction L] [Mul M] [CompatibleMul L M]
    (hf : A.DefinableFun L f) (hg : A.DefinableFun L g) :
    A.DefinableFun L fun v => f v * g v := by
  apply comp (g := fun v => ![f v, g v]) (f := fun v => v 0 * v 1)
  · simp [DefinableMap, *]
  · convert (DefinableFun.fun_symbol (L := L) Functions.mul).of_empty
    simp

@[to_additive (attr := fun_prop)]
theorem DefinableFun.inv [InvFunction L] [Inv M] [CompatibleInv L M] (hf : A.DefinableFun L f) :
    A.DefinableFun L fun v => (f v)⁻¹ := by
  apply comp (g := fun v => ![f v]) (f := fun v => (v 0)⁻¹)
  · simp [DefinableMap, *]
  · convert (DefinableFun.fun_symbol (L := L) Functions.inv).of_empty
    simp

@[fun_prop]
theorem DefinableFun.natCast [ZeroConstant L] [OneConstant L] [AddFunction L] [AddMonoidWithOne M]
    [CompatibleZero L M] [CompatibleOne L M] [CompatibleAdd L M] {n : ℕ} :
    A.DefinableFun L fun _ : α → M => n := by
  convert (n : Term L α).definableFun_realize.of_empty
  simp

@[to_additive (attr := fun_prop)]
theorem DefinableFun.npow [OneConstant L] [MulFunction L] [Monoid M] [CompatibleOne L M]
    [CompatibleMul L M] {n : ℕ} (hf : A.DefinableFun L f) :
    A.DefinableFun L fun v => (f v) ^ n := by
  apply comp (g := fun v => ![f v]) (f := fun v => v 0 ^ n)
  · simp [DefinableMap, *]
  · convert (Term.var 0 ^ n : Term L (Fin 1)).definableFun_realize.of_empty
    simp only [Fin.isValue, realize_npow, Term.realize_var]

@[to_additive (attr := fun_prop)]
theorem DefinableFun.finsetProd [OneConstant L] [MulFunction L] [CommMonoid M] [CompatibleOne L M]
    [CompatibleMul L M] {ι : Type*} {s : Finset ι} {f : ι → (α → M) → M}
    (hf : ∀ i ∈ s, A.DefinableFun L (f i)) :
    A.DefinableFun L fun v => ∏ i ∈ s, f i v := by
  conv in Finset.prod _ _ => rw [← Finset.prod_coe_sort]
  apply comp
  · simp [DefinableMap, *]
  · convert (Term.prod .univ (L := L) fun i : s => Term.var i).definableFun_realize.of_empty
    simp

end Set
