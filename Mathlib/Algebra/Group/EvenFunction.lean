/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.Algebra.Module.Defs

/-!
# Even and odd functions

We define even functions `α → β` assuming `α` has a negation, and odd functions assuming both `α`
and `β` have negation.

These definitions are called `EvenFun` and `OddFun` to avoid conflicting with the root-level
definitions `Even` and `Odd` (which, for functions, mean that the function takes even resp. odd
_values_, a wholly different concept).
-/

namespace Function

variable {α β : Type*} [Neg α]

/-- A function `f` is _even_ if it satisfies `f (-x) = f x` for all `x`. -/
def EvenFun (f : α → β) : Prop := ∀ a, f (-a) = f a

/-- A function `f` is _odd_ if it satisfies `f (-x) = -f x` for all `x`. -/
def OddFun [Neg β] (f : α → β) : Prop := ∀ a, f (-a) = -(f a)

/-- Any constant function is even. -/
lemma EvenFun.const (b : β) : EvenFun (fun _ : α ↦ b) := fun _ ↦ rfl

/-- The zero function is odd. -/
lemma OddFun.zero [NegZeroClass β] : OddFun (fun (_ : α) ↦ (0 : β)) := fun _ ↦ neg_zero.symm

section composition

variable {γ : Type*}

/-- If `f` is arbitrary and `g` is even, then `f ∘ g` is even. -/
lemma EvenFun.left_comp {g : α → β} (hg : EvenFun g) (f : β → γ) : EvenFun (f ∘ g) :=
  (congr_arg f <| hg ·)

/-- If `f` is even and `g` is odd, then `f ∘ g` is even. -/
lemma EvenFun.comp_oddFun [Neg β] {f : β → γ} (hf : EvenFun f) {g : α → β} (hg : OddFun g) :
    EvenFun (f ∘ g) :=
  fun r ↦ by rw [comp_apply, hg, hf, comp_apply]

/-- If `f` and `g` are odd, then `f ∘ g` is odd. -/
lemma OddFun.comp_oddFun [Neg β] [Neg γ] {f : β → γ} (hf : OddFun f) {g : α → β} (hg : OddFun g) :
    OddFun (f ∘ g) :=
  fun r ↦ by rw [comp_apply, hg, hf, comp_apply]

end composition

lemma EvenFun.add [Add β] {f g : α → β} (hf : EvenFun f) (hg : EvenFun g) : EvenFun (f + g) := by
  intro a
  simp only [hf a, hg a, Pi.add_apply]

lemma OddFun.add [SubtractionCommMonoid β] {f g : α → β} (hf : OddFun f) (hg : OddFun g) :
    OddFun (f + g) := by
  intro a
  simp only [hf a, hg a, Pi.add_apply, neg_add]

section smul

variable {γ : Type*} {f : α → β} {g : α → γ}

lemma EvenFun.smul_evenFun [SMul β γ] (hf : EvenFun f) (hg : EvenFun g) : EvenFun (f • g) := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a]

lemma EvenFun.smul_oddFun [Monoid β] [AddGroup γ] [DistribMulAction β γ]
    (hf : EvenFun f) (hg : OddFun g) :
    OddFun (f • g) := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg]

lemma OddFun.smul_evenFun [Ring β] [AddCommGroup γ] [Module β γ] (hf : OddFun f) (hg : EvenFun g) :
    OddFun (f • g) := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, neg_smul]

lemma OddFun.smul_oddFun [Ring β] [AddCommGroup γ] [Module β γ] (hf : OddFun f) (hg : OddFun g) :
    EvenFun (f • g) := by
  intro a
  simp only [Pi.smul_apply', hf a, hg a, smul_neg, neg_smul, neg_neg]

lemma EvenFun.const_smul [SMul β γ] (hg : EvenFun g) (r : β) : EvenFun (r • g) := by
  intro a
  simp only [Pi.smul_apply, hg a]

lemma OddFun.const_smul [Monoid β] [AddGroup γ] [DistribMulAction β γ] (hg : OddFun g) (r : β) :
    OddFun (r • g) := by
  intro a
  simp only [Pi.smul_apply, hg a, smul_neg]

end smul

section mul

variable {R : Type*} [Mul R] {f g : α → R}

lemma EvenFun.mul_evenFun (hf : EvenFun f) (hg : EvenFun g) : EvenFun (f * g) := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

lemma EvenFun.mul_oddFun [HasDistribNeg R] (hf : EvenFun f) (hg : OddFun g) : OddFun (f * g) := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

lemma OddFun.mul_evenFun [HasDistribNeg R] (hf : OddFun f) (hg : EvenFun g) : OddFun (f * g) := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

lemma OddFun.mul_oddFun [HasDistribNeg R] (hf : OddFun f) (hg : OddFun g) : EvenFun (f * g) := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

end mul

/--
If `f` is both even and odd, and its target is a torsion-free commutative additive group,
then `f = 0`.
-/
lemma zero_of_evenFun_and_oddFun [AddCommGroup β] [NoZeroSMulDivisors ℕ β]
    {f : α → β} (he : EvenFun f) (ho : OddFun f) :
    f = 0 := by
  ext r
  rw [Pi.zero_apply, ← neg_eq_self ℕ, ← ho, he]

end Function
