/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Yury Kudryashov
-/
import Mathlib.Util.AssertExists
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Prod.Basic

/-!
# Arithmetic operators on (pairwise) product types

This file provides only the notation for (componentwise) `0`, `1`, `+`, `*`, `•`, `^`, `⁻¹` on
(pairwise) product types. See `Mathlib/Algebra/Group/Prod.lean` for the `Monoid` and `Group`
instances. There is also an instance of the `Star` notation typeclass, but no default notation is
included.

-/

assert_not_exists Monoid DenselyOrdered

variable {G H M N P R S : Type*}

namespace Prod

section One

variable [One M] [One N]

@[to_additive]
instance instOne : One (M × N) :=
  ⟨(1, 1)⟩

@[to_additive (attr := simp)]
theorem fst_one : (1 : M × N).1 = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem snd_one : (1 : M × N).2 = 1 :=
  rfl

@[to_additive]
theorem one_eq_mk : (1 : M × N) = (1, 1) :=
  rfl

@[to_additive]
theorem mk_one_one : ((1 : M), (1 : N)) = 1 := rfl

@[to_additive (attr := simp)]
theorem mk_eq_one {x : M} {y : N} : (x, y) = 1 ↔ x = 1 ∧ y = 1 := mk_inj

@[to_additive (attr := simp)]
theorem swap_one : (1 : M × N).swap = 1 :=
  rfl

end One

section Mul

variable {M N : Type*} [Mul M] [Mul N]

@[to_additive]
instance instMul : Mul (M × N) :=
  ⟨fun p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

@[to_additive (attr := simp)]
theorem fst_mul (p q : M × N) : (p * q).1 = p.1 * q.1 := rfl

@[to_additive (attr := simp)]
theorem snd_mul (p q : M × N) : (p * q).2 = p.2 * q.2 := rfl

@[to_additive (attr := simp)]
theorem mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) = (a₁ * a₂, b₁ * b₂) := rfl

@[to_additive (attr := simp)]
theorem swap_mul (p q : M × N) : (p * q).swap = p.swap * q.swap := rfl

@[to_additive]
theorem mul_def (p q : M × N) : p * q = (p.1 * q.1, p.2 * q.2) := rfl

end Mul

section Inv

variable {G H : Type*} [Inv G] [Inv H]

@[to_additive]
instance instInv : Inv (G × H) :=
  ⟨fun p => (p.1⁻¹, p.2⁻¹)⟩

@[to_additive (attr := simp)]
theorem fst_inv (p : G × H) : p⁻¹.1 = p.1⁻¹ := rfl

@[to_additive (attr := simp)]
theorem snd_inv (p : G × H) : p⁻¹.2 = p.2⁻¹ := rfl

@[to_additive (attr := simp)]
theorem inv_mk (a : G) (b : H) : (a, b)⁻¹ = (a⁻¹, b⁻¹) := rfl

@[to_additive (attr := simp)]
theorem swap_inv (p : G × H) : p⁻¹.swap = p.swap⁻¹ := rfl

end Inv

section Div

variable {G H : Type*} [Div G] [Div H]

@[to_additive]
instance instDiv : Div (G × H) :=
  ⟨fun p q => ⟨p.1 / q.1, p.2 / q.2⟩⟩

@[to_additive (attr := simp)]
theorem fst_div (a b : G × H) : (a / b).1 = a.1 / b.1 := rfl

@[to_additive (attr := simp)]
theorem snd_div (a b : G × H) : (a / b).2 = a.2 / b.2 := rfl

@[to_additive (attr := simp)]
theorem mk_div_mk (x₁ x₂ : G) (y₁ y₂ : H) : (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) := rfl

@[to_additive (attr := simp)]
theorem swap_div (a b : G × H) : (a / b).swap = a.swap / b.swap := rfl

@[to_additive] lemma div_def (a b : G × H) : a / b = (a.1 / b.1, a.2 / b.2) := rfl

end Div

section SMul

variable {M α β : Type*} [SMul M α] [SMul M β]

@[to_additive]
instance instSMul : SMul M (α × β) where smul a p := (a • p.1, a • p.2)

@[to_additive (attr := simp)] lemma smul_fst (a : M) (x : α × β) : (a • x).1 = a • x.1 := rfl

@[to_additive (attr := simp)] lemma smul_snd (a : M) (x : α × β) : (a • x).2 = a • x.2 := rfl

@[to_additive (attr := simp)]
lemma smul_mk (a : M) (b : α) (c : β) : a • (b, c) = (a • b, a • c) := rfl

@[to_additive]
lemma smul_def (a : M) (x : α × β) : a • x = (a • x.1, a • x.2) := rfl

@[to_additive (attr := simp)] lemma smul_swap (a : M) (x : α × β) : (a • x).swap = a • x.swap := rfl

end SMul

section Pow

variable {E α β : Type*} [Pow α E] [Pow β E]

@[to_additive existing instSMul]
instance instPow : Pow (α × β) E where pow p c := (p.1 ^ c, p.2 ^ c)

@[to_additive existing (attr := simp) (reorder := 6 7) smul_fst]
lemma pow_fst (p : α × β) (c : E) : (p ^ c).fst = p.fst ^ c := rfl

@[to_additive existing (attr := simp) (reorder := 6 7) smul_snd]
lemma pow_snd (p : α × β) (c : E) : (p ^ c).snd = p.snd ^ c := rfl

@[to_additive existing (attr := simp) (reorder := 6 7 8) smul_mk]
lemma pow_mk (a : α) (b : β) (c : E) : Prod.mk a b ^ c = Prod.mk (a ^ c) (b ^ c) := rfl

@[to_additive existing (reorder := 6 7) smul_def]
lemma pow_def (p : α × β) (c : E) : p ^ c = (p.1 ^ c, p.2 ^ c) := rfl

@[to_additive existing (attr := simp) (reorder := 6 7) smul_swap]
lemma pow_swap (p : α × β) (c : E) : (p ^ c).swap = p.swap ^ c := rfl

end Pow

section Star

variable [Star R] [Star S]

instance : Star (R × S) where star x := (star x.1, star x.2)

@[simp]
theorem fst_star (x : R × S) : (star x).1 = star x.1 := rfl

@[simp]
theorem snd_star (x : R × S) : (star x).2 = star x.2 := rfl

theorem star_def (x : R × S) : star x = (star x.1, star x.2) := rfl

end Star


end Prod
