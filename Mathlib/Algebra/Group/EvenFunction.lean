/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Module.Defs

/-!
# Even and odd functions

We define even functions `α → β` assuming `α` has a negation, and odd functions assuming both `α`
and `β` have negation.

These definitions are `Function.Even` and `Function.Odd`; and they are `protected`, to avoid
conflicting with the root-level definitions `Even` and `Odd` (which, for functions, mean that the
function takes even resp. odd _values_, a wholly different concept).
-/

assert_not_exists Module.IsTorsionFree NoZeroSMulDivisors

namespace Function

variable {α β : Type*} [Neg α]

/-- A function `f` is _even_ if it satisfies `f (-x) = f x` for all `x`. -/
protected def Even (f : α → β) : Prop := ∀ a, f (-a) = f a

/-- A function `f` is _odd_ if it satisfies `f (-x) = -f x` for all `x`. -/
protected def Odd [Neg β] (f : α → β) : Prop := ∀ a, f (-a) = -(f a)

/-- Any constant function is even. -/
lemma Even.const (b : β) : Function.Even (fun _ : α ↦ b) := fun _ ↦ rfl

/-- The zero function is even. -/
lemma Even.zero [Zero β] : Function.Even (fun (_ : α) ↦ (0 : β)) := Even.const 0

/-- The zero function is odd. -/
lemma Odd.zero [NegZeroClass β] : Function.Odd (fun (_ : α) ↦ (0 : β)) := fun _ ↦ neg_zero.symm

section composition

variable {γ : Type*}

/-- If `f` is arbitrary and `g` is even, then `f ∘ g` is even. -/
lemma Even.left_comp {g : α → β} (hg : g.Even) (f : β → γ) : (f ∘ g).Even :=
  (congr_arg f <| hg ·)

/-- If `f` is even and `g` is odd, then `f ∘ g` is even. -/
lemma Even.comp_odd [Neg β] {f : β → γ} (hf : f.Even) {g : α → β} (hg : g.Odd) :
    (f ∘ g).Even := by
  intro a
  simp only [comp_apply, hg a, hf _]

/-- If `f` and `g` are odd, then `f ∘ g` is odd. -/
lemma Odd.comp_odd [Neg β] [Neg γ] {f : β → γ} (hf : f.Odd) {g : α → β} (hg : g.Odd) :
    (f ∘ g).Odd := by
  intro a
  simp only [comp_apply, hg a, hf _]

end composition

lemma Even.add [Add β] {f g : α → β} (hf : f.Even) (hg : g.Even) : (f + g).Even := by
  intro a
  simp only [hf a, hg a, Pi.add_apply]

lemma Odd.add [SubtractionCommMonoid β] {f g : α → β} (hf : f.Odd) (hg : g.Odd) : (f + g).Odd := by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

section smul

variable {γ : Type*} {f : α → β} {g : α → γ}

lemma Even.smul_even [SMul β γ] (hf : f.Even) (hg : g.Even) : (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

lemma Even.smul_odd [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hf : f.Even) (hg : g.Odd) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

lemma Odd.smul_even [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Even) :
    (f • g).Odd := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

lemma Odd.smul_odd [Ring β] [AddCommGroup γ] [Module β γ] (hf : f.Odd) (hg : g.Odd) :
    (f • g).Even := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

lemma Even.const_smul [SMul β γ] (hg : g.Even) (r : β) : (r • g).Even := by
  intro a
  simp only [Pi.smul_apply, hg a]

lemma Odd.const_smul [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hg : g.Odd) (r : β) :
    (r • g).Odd := by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

end smul

section mul

variable {R : Type*} [Mul R] {f g : α → R}

lemma Even.mul_even (hf : f.Even) (hg : g.Even) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

lemma Even.mul_odd [HasDistribNeg R] (hf : f.Even) (hg : g.Odd) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

lemma Odd.mul_even [HasDistribNeg R] (hf : f.Odd) (hg : g.Even) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

lemma Odd.mul_odd [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

end mul

section torsionfree

-- need to redeclare variables since `InvolutiveNeg α` conflicts with `Neg α`
variable {α β : Type*} [AddCommGroup β] [IsAddTorsionFree β] {f : α → β}

/--
If `f` is both even and odd, and its target is a torsion-free commutative additive group,
then `f = 0`.
-/
lemma zero_of_even_and_odd [Neg α] (he : f.Even) (ho : f.Odd) : f = 0 := by
  ext r
  rw [Pi.zero_apply, ← neg_eq_self, ← ho, he]

/-- The sum of the values of an odd function is 0. -/
lemma Odd.sum_eq_zero [Fintype α] [InvolutiveNeg α] {f : α → β} (hf : f.Odd) : ∑ a, f a = 0 := by
  simpa [neg_eq_self, Finset.sum_neg_distrib, funext hf] using Equiv.sum_comp (.neg α) f

/-- An odd function vanishes at zero. -/
lemma Odd.map_zero [NegZeroClass α] (hf : f.Odd) : f 0 = 0 := by simp [← neg_eq_self, ← hf 0]

end torsionfree

end Function
