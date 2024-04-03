/-
Copyright (c) 2024 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/

import Mathlib.Algebra.Group.Defs

/-!
# Monoid, group etc structures on families indexed by sum types

Given 2 families of e.g. groups `αᵢ, βᵢ` indexed by `ια, ιβ` respectively, the components
of the resulting family of types indexed by `ια ⊕ ιβ` each have a group structure.

## Implementation notes

A little care is required to avoid non-defeq diamonds - e.g. `instElimMulOneClass` can't just be
defined with a match expression, since the resulting `One` and `Mul` instances won't be defeq to
`instElimOne` and `instElimMul`.

## Todo

Missing some of the algebraic hierarchy compared to e.g. `Mathlib.Algebra.Group.Prod`.

-/
universe v u

namespace Sum

variable {ια ιβ : Type*} {α : (i : ια) → Type u} {β : (i : ιβ) → Type u}

@[to_additive] instance instElimOne [∀ (i : ια), One (α i)] [∀ i : ιβ, One (β i)]
    (i : ια ⊕ ιβ) : One (Sum.elim α β i) :=
  { one := match i with
    | Sum.inl i => (1 : α i)
    | Sum.inr i => (1 : β i) }

@[to_additive] instance instElimMul [∀ (i : ια), Mul (α i)]
    [∀ i : ιβ, Mul (β i)] (i : ια ⊕ ιβ) : Mul (Sum.elim α β i) :=
  { mul := match i with
    | Sum.inl i => (· * · : α i → α i → α i)
    | Sum.inr i => (· * · : β i → β i → β i) }

@[to_additive] instance instElimMulOneClass [∀ (i : ια), MulOneClass (α i)]
    [∀ i : ιβ, MulOneClass (β i)] (i : ια ⊕ ιβ) : MulOneClass (Sum.elim α β i) :=
  { one_mul := fun _ => match i with
    | Sum.inl i => one_mul (M := α i) _
    | Sum.inr i => one_mul (M := β i) _
    mul_one := fun _ => match i with
    | Sum.inl i => mul_one (M := α i) _
    | Sum.inr i => mul_one (M := β i) _ }

@[to_additive] instance instElimSemigroup [∀ (i : ια), Semigroup (α i)]
    [∀ i : ιβ, Semigroup (β i)] (i : ια ⊕ ιβ) : Semigroup (Sum.elim α β i) :=
  { mul_assoc := fun _ _ _ => match i with
    | Sum.inl i => mul_assoc (G := α i) _ _ _
    | Sum.inr i => mul_assoc (G := β i) _ _ _ }

@[to_additive] instance instElimCommSemigroup [∀ (i : ια), CommSemigroup (α i)]
    [∀ i : ιβ, CommSemigroup (β i)] (i : ια ⊕ ιβ) : CommSemigroup (Sum.elim α β i) :=
  { mul_comm := fun _ _ => match i with
    | Sum.inl i => mul_comm (G := α i) _ _
    | Sum.inr i => mul_comm (G := β i) _ _ }

instance instElimPow {γ : Type*} [∀ i : ια, Pow (α i) γ]
    [∀ i : ιβ, Pow (β i) γ] (i : ια ⊕ ιβ) :
    Pow (Sum.elim α β i) γ :=
  { pow := match i with
    | Sum.inl i => (· ^ · : α i → γ → α i)
    | Sum.inr i => (· ^ · : β i → γ → β i) }

instance instElimSMul {γ : Type*} [∀ i : ια, SMul γ (α i)]
    [∀ i : ιβ, SMul γ (β i)] (i : ια ⊕ ιβ) :
    SMul γ (Sum.elim α β i) :=
  { smul := match i with
    | Sum.inl i => (· • · : γ → α i → α i)
    | Sum.inr i => (· • · : γ → β i → β i) }

attribute [to_additive existing instElimSMul] instElimPow

instance instElimMonoid [∀ (i : ια), Monoid (α i)]
    [∀ i : ιβ, Monoid (β i)] (i : ια ⊕ ιβ) : Monoid (Sum.elim α β i) :=
  { one_mul := one_mul
    mul_one := mul_one
    npow := fun n x => x ^ n
    npow_zero := match i with
    | Sum.inl i => Monoid.npow_zero (M := α i)
    | Sum.inr i => Monoid.npow_zero (M := β i)
    npow_succ := match i with
    | Sum.inl i => Monoid.npow_succ (M := α i)
    | Sum.inr i => Monoid.npow_succ (M := β i) }

instance instElimAddMonoid  [∀ (i : ια), AddMonoid (α i)]
    [∀ i : ιβ, AddMonoid (β i)] (i : ια ⊕ ιβ) : AddMonoid (Sum.elim α β i) :=
  { zero_add := zero_add
    add_zero := add_zero
    nsmul := fun n x => n • x
    nsmul_zero := match i with
    | Sum.inl i => AddMonoid.nsmul_zero (M := α i)
    | Sum.inr i => AddMonoid.nsmul_zero (M := β i)
    nsmul_succ := match i with
    | Sum.inl i => AddMonoid.nsmul_succ (M := α i)
    | Sum.inr i => AddMonoid.nsmul_succ (M := β i) }

attribute [to_additive existing] instElimMonoid

@[to_additive] instance instElimCommMonoid [∀ (i : ια), CommMonoid (α i)]
    [∀ i : ιβ, CommMonoid (β i)] (i : ια ⊕ ιβ) : CommMonoid (Sum.elim α β i) :=
  { mul_comm := CommSemigroup.mul_comm }

@[to_additive] instance instElimInv [∀ (i : ια), Inv (α i)]
    [∀ i : ιβ, Inv (β i)] (i : ια ⊕ ιβ) : Inv (Sum.elim α β i) :=
  { inv := match i with
    | Sum.inl i => (· ⁻¹ : α i → α i)
    | Sum.inr i => (· ⁻¹ : β i → β i) }

@[to_additive] instance instElimDiv [∀ (i : ια), Div (α i)]
    [∀ i : ιβ, Div (β i)] (i : ια ⊕ ιβ) : Div (Sum.elim α β i) :=
  { div := match i with
    | Sum.inl i => (· / · : α i → α i → α i)
    | Sum.inr i => (· / · : β i → β i → β i) }

instance instElimDivInvMonoid [∀ (i : ια), DivInvMonoid (α i)]
    [∀ i : ιβ, DivInvMonoid (β i)] (i : ια ⊕ ιβ) : DivInvMonoid (Sum.elim α β i) :=
  { div_eq_mul_inv := fun _ _ => match i with
    | Sum.inl i => div_eq_mul_inv (G := α i) _ _
    | Sum.inr i => div_eq_mul_inv (G := β i) _ _
    zpow := fun i x => x ^ i
    zpow_zero' := fun _ => match i with
    | Sum.inl i => zpow_zero (G := α i) _
    | Sum.inr i => zpow_zero (G := β i) _
    zpow_succ' := fun _ _ => match i with
    | Sum.inl i => DivInvMonoid.zpow_succ' (G := α i) _ _
    | Sum.inr i => DivInvMonoid.zpow_succ' (G := β i) _ _
    zpow_neg' := fun _ _ => match i with
    | Sum.inl i => DivInvMonoid.zpow_neg' (G := α i) _ _
    | Sum.inr i => DivInvMonoid.zpow_neg' (G := β i) _ _ }

instance instElimSubNegMonoid [∀ (i : ια), SubNegMonoid (α i)]
    [∀ i : ιβ, SubNegMonoid (β i)] (i : ια ⊕ ιβ) : SubNegMonoid (Sum.elim α β i) :=
  { sub_eq_add_neg := fun _ _ => match i with
    | Sum.inl i => sub_eq_add_neg (G := α i) _ _
    | Sum.inr i => sub_eq_add_neg (G := β i) _ _
    zsmul := fun i x => i • x
    zsmul_zero' := fun _ => match i with
    | Sum.inl i => SubNegMonoid.zsmul_zero' (G := α i) _
    | Sum.inr i => SubNegMonoid.zsmul_zero' (G := β i) _
    zsmul_succ' := fun _ _ => match i with
    | Sum.inl i => SubNegMonoid.zsmul_succ' (G := α i) _ _
    | Sum.inr i => SubNegMonoid.zsmul_succ' (G := β i) _ _
    zsmul_neg' := fun _ _ => match i with
    | Sum.inl i => SubNegMonoid.zsmul_neg' (G := α i) _ _
    | Sum.inr i => SubNegMonoid.zsmul_neg' (G := β i) _ _ }

attribute [to_additive existing instElimSubNegMonoid] instElimDivInvMonoid

@[to_additive] instance instElimGroup [∀ (i : ια), Group (α i)]
    [∀ i : ιβ, Group (β i)] (i : ια ⊕ ιβ) : Group (Sum.elim α β i) :=
  { mul_left_inv := fun _ => match i with
    | Sum.inl i => mul_left_inv (G := α i) _
    | Sum.inr i => mul_left_inv (G := β i) _ }

@[to_additive] instance instElimCommGroup [∀ (i : ια), CommGroup (α i)]
    [∀ i : ιβ, CommGroup (β i)] (i : ια ⊕ ιβ) : CommGroup (Sum.elim α β i) :=
  { mul_comm := CommMonoid.mul_comm }

end Sum
