/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Data.FunLike.IsApply

/-!
# Relation isomorphisms form a group

This file contains `Monoid` instances for `RelHom` and `OrderHom`, where multiplication is
given by composition. Likewise there is a `Group` instance for `RelIso`. Because `OrderIso`
is an abbreviation for `RelIso`, there is no need for an additional instance.

## TODO

+ Rename the `mul_def`/`one_def` lemmas to `mul_eq_comp`/`one_eq_id`.
+ Use the `IsMulApplyEqComp` and `IsOneApplyEqSelf` classes for `RelHom` and `RelIso`.
-/

@[expose] public section

assert_not_exists MulAction MonoidWithZero

variable {α : Type*} {r : α → α → Prop}

namespace RelHom

instance : One (r →r r) where one := .id r
instance : Mul (r →r r) where mul := .comp
instance : Pow (r →r r) Nat where
  pow f n :=
    { toFun := f^[n]
      map_rel' {a b} := Nat.rec (fun _ _ h => h)
        (fun _ ih a b h => ih (f a) (f b) (f.map_rel h)) n a b }

instance : Monoid (r →r r) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  npow n f := f ^ n

lemma one_def : (1 : r →r r) = .id r := rfl
lemma mul_def (f g : r →r r) : (f * g) = f.comp g := rfl

@[simp] lemma coe_one : ⇑(1 : r →r r) = id := rfl
@[simp] lemma coe_mul (f g : r →r r) : ⇑(f * g) = f ∘ g := rfl

lemma one_apply (a : α) : (1 : r →r r) a = a := rfl
lemma mul_apply (e₁ e₂ : r →r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelHom

namespace RelEmbedding

instance : One (r ↪r r) where one := .refl r
instance : Mul (r ↪r r) where mul f g := g.trans f
instance : Pow (r ↪r r) ℕ where
  pow f n :=
    { toFun := f^[n]
      inj' := f.injective.iterate n
      map_rel_iff' {a b} := Nat.rec (fun _ _ => Iff.rfl)
        (fun _ ih a b => (ih (f a) (f b)).trans f.map_rel_iff) n a b }

instance : Monoid (r ↪r r) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  npow n f := f ^ n

lemma one_def : (1 : r ↪r r) = .refl r := rfl
lemma mul_def (f g : r ↪r r) : (f * g) = g.trans f := rfl

@[simp] lemma coe_one : ⇑(1 : r ↪r r) = id := rfl
@[simp] lemma coe_mul (f g : r ↪r r) : ⇑(f * g) = f ∘ g := rfl

lemma one_apply (a : α) : (1 : r ↪r r) a = a := rfl
lemma mul_apply (e₁ e₂ : r ↪r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

end RelEmbedding

namespace RelIso

instance : One (r ≃r r) where one := .refl r
instance : Mul (r ≃r r) where mul f₁ f₂ := f₂.trans f₁
instance : Inv (r ≃r r) where inv := .symm
instance : Pow (r ≃r r) ℕ where
  pow f n :=
    { __ := f.toEquiv ^ n
      map_rel_iff' {a b} := Nat.rec (fun _ _ => Iff.rfl)
        (fun _ ih a b => (ih (f a) (f b)).trans f.map_rel_iff) n a b }
instance : Pow (r ≃r r) ℤ where
  pow f n :=
    { __ := f.toEquiv ^ n
      map_rel_iff' := n.casesOn (fun n => (f ^ n).map_rel_iff)
        (fun n => ((f ^ (n + 1))⁻¹).map_rel_iff) }

instance : Group (r ≃r r) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel f := ext f.symm_apply_apply
  npow n f := f ^ n
  zpow n f := f ^ n

lemma one_def : (1 : r ≃r r) = .refl r := rfl
lemma mul_def (f g : r ≃r r) : (f * g) = g.trans f := rfl

@[simp] lemma coe_one : ((1 : r ≃r r) : α → α) = id := rfl
@[simp] lemma coe_mul (e₁ e₂ : r ≃r r) : ((e₁ * e₂) : α → α) = e₁ ∘ e₂ := rfl

lemma one_apply (x : α) : (1 : r ≃r r) x = x := rfl
lemma mul_apply (e₁ e₂ : r ≃r r) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl

@[simp]
theorem inv_apply_self (e : r ≃r r) (x) : e⁻¹ (e x) = x :=
  e.symm_apply_apply x

@[simp]
theorem apply_inv_self (e : r ≃r r) (x) : e (e⁻¹ x) = x :=
  e.apply_symm_apply x

end RelIso

namespace OrderHom

variable [Preorder α]

instance : Mul (α →o α) where mul f g := f.comp g
instance : One (α →o α) where one := .id
instance : IsMulApplyEqComp (α →o α) α where mul_apply_eq_comp _ _ _ := rfl
instance : IsOneApplyEqSelf (α →o α) α where one_apply_eq_self _ := rfl

lemma mul_eq_comp (f g : α →o α) : (f * g : α →o α) = f.comp g := rfl
lemma one_eq_id : (1 : α →o α) = .id := rfl

instance : Monoid (α →o α) where
  mul_assoc f g h := by simp [DFunLike.ext_iff]
  one_mul f := by simp [DFunLike.ext_iff]
  mul_one f := by simp [DFunLike.ext_iff]

end OrderHom
