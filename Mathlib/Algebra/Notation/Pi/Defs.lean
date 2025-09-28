/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Notation.Defs
import Mathlib.Util.AssertExists

/-!
# Notation for algebraic operators on pi types

This file provides only the notation for (pointwise) `0`, `1`, `+`, `*`, `•`, `^`, `⁻¹` on pi types.
See `Mathlib/Algebra/Group/Pi/Basic.lean` for the `Monoid` and `Group` instances. There is also
an instance of the `Star` notation typeclass, but no default notation is included.
-/

assert_not_exists Set.range Monoid Preorder

open Function

variable {ι α β : Type*} {G M R : ι → Type*}

namespace Pi

-- TODO: Do we really need this definition? If so, where to put it?
/-- The mapping into a product type built from maps into each component. -/
@[simp]
protected def prod {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) (i : ι) : α i × β i := (f i, g i)

lemma prod_fst_snd : Pi.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id := rfl
lemma prod_snd_fst : Pi.prod (Prod.snd : α × β → β) (Prod.fst : α × β → α) = .swap := rfl

/-! `1`, `0`, `+`, `*`, `+ᵥ`, `•`, `^`, `-`, `⁻¹`, and `/` are defined pointwise. -/

section One
variable [∀ i, One (M i)]

@[to_additive]
instance instOne : One (∀ i, M i) where one _ := 1

@[to_additive (attr := simp high)]
lemma one_apply (i : ι) : (1 : ∀ i, M i) i = 1 := rfl

@[to_additive]
lemma one_def : (1 : ∀ i, M i) = fun _ ↦ 1 := rfl

variable {M : Type*} [One M]

@[to_additive (attr := simp)] lemma _root_.Function.const_one : const α (1 : M) = 1 := rfl

@[to_additive (attr := simp)] lemma one_comp (f : α → β) : (1 : β → M) ∘ f = 1 := rfl
@[to_additive (attr := simp)] lemma comp_one (f : M → β) : f ∘ (1 : α → M) = const α (f 1) := rfl

end One

section Mul
variable [∀ i, Mul (M i)]

@[to_additive]
instance instMul : Mul (∀ i, M i) where mul f g i := f i * g i

@[to_additive (attr := simp)]
lemma mul_apply (f g : ∀ i, M i) (i : ι) : (f * g) i = f i * g i := rfl

@[to_additive]
lemma mul_def (f g : ∀ i, M i) : f * g = fun i ↦ f i * g i := rfl

variable {M : Type*} [Mul M]

@[to_additive (attr := simp)]
lemma _root_.Function.const_mul (a b : M) : const ι a * const ι b = const ι (a * b) := rfl

@[to_additive]
lemma mul_comp (f g : β → M) (z : α → β) : (f * g) ∘ z = f ∘ z * g ∘ z := rfl

end Mul

section Inv
variable [∀ i, Inv (G i)]

@[to_additive]
instance instInv : Inv (∀ i, G i) where inv f i := (f i)⁻¹

@[to_additive (attr := simp)]
lemma inv_apply (f : ∀ i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹ := rfl

@[to_additive]
lemma inv_def (f : ∀ i, G i) : f⁻¹ = fun i ↦ (f i)⁻¹ := rfl

variable {G : Type*} [Inv G]

@[to_additive]
lemma _root_.Function.const_inv (a : G) : (const ι a)⁻¹ = const ι a⁻¹ := rfl

@[to_additive]
lemma inv_comp (f : β → G) (g : α → β) : f⁻¹ ∘ g = (f ∘ g)⁻¹ := rfl
end Inv

section Div
variable [∀ i, Div (G i)]

@[to_additive]
instance instDiv : Div (∀ i, G i) where div f g i := f i / g i

@[to_additive (attr := simp)]
lemma div_apply (f g : ∀ i, G i) (i : ι) : (f / g) i = f i / g i :=rfl

@[to_additive]
lemma div_def (f g : ∀ i, G i) : f / g = fun i ↦ f i / g i := rfl

variable {G : Type*} [Div G]

@[to_additive]
lemma div_comp (f g : β → G) (z : α → β) : (f / g) ∘ z = f ∘ z / g ∘ z := rfl

@[to_additive (attr := simp)]
lemma _root_.Function.const_div (a b : G) : const ι a / const ι b = const ι (a / b) := rfl

end Div

section Pow

@[to_additive]
instance instSMul [∀ i, SMul α (M i)] : SMul α (∀ i, M i) where smul a f i := a • f i

variable [∀ i, Pow (M i) α]

@[to_additive existing instSMul]
instance instPow : Pow (∀ i, M i) α where pow f a i := f i ^ a

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
lemma pow_apply (f : ∀ i, M i) (a : α) (i : ι) : (f ^ a) i = f i ^ a := rfl

@[to_additive (attr := to_additive) (reorder := 5 6) smul_def]
lemma pow_def (f : ∀ i, M i) (a : α) : f ^ a = fun i ↦ f i ^ a := rfl

variable {M : Type*} [Pow M α]

@[to_additive (attr := simp, to_additive) (reorder := 2 3, 5 6) smul_const]
lemma _root_.Function.const_pow (a : M) (b : α) : const ι a ^ b = const ι (a ^ b) := rfl

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]
lemma pow_comp (f : β → M) (a : α) (g : ι → β) : (f ^ a) ∘ g = f ∘ g ^ a := rfl

end Pow

section Star

variable [∀ i, Star (R i)]

instance : Star (∀ i, R i) where star x i := star (x i)

@[simp]
theorem star_apply (x : ∀ i, R i) (i : ι) : star x i = star (x i) := rfl

theorem star_def (x : ∀ i, R i) : star x = fun i => star (x i) := rfl

end Star


end Pi
