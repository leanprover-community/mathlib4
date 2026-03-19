/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.RelIso.Basic

/-!
# Relation isomorphisms form a group
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
    { toFun := f^[n]
      invFun := Nat.repeat f.symm n
      left_inv := Nat.rec Eq.refl
        (fun _ ih x => (congrArg f.symm (ih (f x))).trans (f.left_inv x)) n
      right_inv := Nat.rec Eq.refl
        (fun n ih x => (congrArg f^[n] (f.right_inv (Nat.repeat f.symm n x))).trans (ih x)) n
      map_rel_iff' {a b} := Nat.rec (fun _ _ => Iff.rfl)
        (fun _ ih a b => (ih (f a) (f b)).trans f.map_rel_iff) n a b }

instance : Group (r ≃r r) where
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl
  inv_mul_cancel f := ext f.symm_apply_apply
  npow n f := f ^ n
  zpow := zpowRec fun n f => f ^ n

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
