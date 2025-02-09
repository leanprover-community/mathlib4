/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.SetTheory.Nimber.Basic
import Mathlib.Tactic.Abel

/-!
# Nimber multiplication

The nim product `a * b` is recursively defined as the least nimber not equal to any
`a' * b + a * b' + a' * b'` for `a' < a` and `b' < b`. When endowed with this operation, the nimbers
form a field.

## Todo

- Define nim division and prove nimbers are a field.
- Show the nimbers are algebraically closed.
-/

universe u v

open Function Order

noncomputable section

namespace Nimber

/-! ### Nimber multiplication -/

variable {a b c : Nimber.{u}}

instance : CharP Nimber 2 := by
  apply CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero
  rw [← one_add_one_eq_two, add_self]

private theorem two_zsmul (x : Nimber) : (2 : ℤ) • x = 0 := by
  rw [_root_.two_zsmul]
  exact add_self x

private theorem add_eq_iff_eq_add : a + b = c ↔ a = c + b :=
  sub_eq_iff_eq_add

/-- Nimber multiplication is recursively defined so that `a * b` is the smallest nimber not equal to
`a' * b + a * b' + a' * b'` for `a' < a` and `b' < b`. -/
-- We write the binders like this so that the termination checker works.
protected def mul (a b : Nimber.{u}) : Nimber.{u} :=
  sInf {x | ∃ a', ∃ (_ : a' < a), ∃ b', ∃ (_ : b' < b),
    Nimber.mul a' b + Nimber.mul a b' + Nimber.mul a' b' = x}ᶜ
termination_by (a, b)

instance : Mul Nimber :=
  ⟨Nimber.mul⟩

theorem mul_def (a b : Nimber) :
    a * b = sInf {x | ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = x}ᶜ := by
  change Nimber.mul a b = _
  rw [Nimber.mul]
  simp_rw [exists_prop]
  rfl

/-- The set in the definition of `Nimber.mul` is nonempty. -/
private theorem mul_nonempty (a b : Nimber.{u}) :
    {x | ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = x}ᶜ.Nonempty := by
  convert nonempty_of_not_bddAbove <| not_bddAbove_compl_of_small
    ((fun x ↦ x.1 * b + a * x.2 + x.1 * x.2) '' Set.Iio a ×ˢ Set.Iio b)
  ext
  simp_rw [Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Set.mem_Iio, Prod.exists]
  tauto

theorem exists_of_lt_mul (h : c < a * b) : ∃ a' < a, ∃ b' < b, a' * b + a * b' + a' * b' = c := by
  rw [mul_def] at h
  have := not_mem_of_lt_csInf' h
  rwa [Set.not_mem_compl_iff] at this

theorem mul_le_of_forall_ne (h : ∀ a' < a, ∀ b' < b, a' * b + a * b' + a' * b' ≠ c) :
    a * b ≤ c := by
  by_contra! h'
  have := exists_of_lt_mul h'
  tauto

instance : MulZeroClass Nimber where
  mul_zero a := by
    rw [← Nimber.le_zero]
    exact mul_le_of_forall_ne fun _ _ _ h ↦ (Nimber.not_lt_zero _ h).elim
  zero_mul a := by
    rw [← Nimber.le_zero]
    exact mul_le_of_forall_ne fun _ h ↦ (Nimber.not_lt_zero _ h).elim

private theorem mul_ne_of_lt : ∀ a' < a, ∀ b' < b, a' * b + a * b' + a' * b' ≠ a * b := by
  have H := csInf_mem (mul_nonempty a b)
  rw [← mul_def] at H
  simpa using H

instance : NoZeroDivisors Nimber where
  eq_zero_or_eq_zero_of_mul_eq_zero {a b} h := by
    by_contra! hab
    iterate 2 rw [← Nimber.pos_iff_ne_zero] at hab
    apply (mul_ne_of_lt _ hab.1 _ hab.2).symm
    simpa only [zero_add, mul_zero, zero_mul]

protected theorem mul_comm (a b : Nimber) : a * b = b * a := by
  apply le_antisymm <;> refine mul_le_of_forall_ne fun x hx y hy ↦ ?_
  on_goal 1 => rw [add_comm (x * _), Nimber.mul_comm a, Nimber.mul_comm x, Nimber.mul_comm x]
  on_goal 2 => rw [add_comm (x * _), ← Nimber.mul_comm y, ← Nimber.mul_comm a, ← Nimber.mul_comm y]
  all_goals exact mul_ne_of_lt y hy x hx
termination_by (a, b)

protected theorem mul_add (a b c : Nimber) : a * (b + c) = a * b + a * c := by
  apply le_antisymm
  · refine mul_le_of_forall_ne fun a' ha x hx ↦ ?_
    obtain (⟨b', h, rfl⟩ | ⟨c', h, rfl⟩) := exists_of_lt_add hx <;>
      rw [Nimber.mul_add a', Nimber.mul_add a, Nimber.mul_add a']
    on_goal 1 => rw [← add_ne_add_left (a * c)]
    on_goal 2 => rw [← add_ne_add_left (a * b)]
    all_goals
      abel_nf
      simp only [two_zsmul, zero_add]
      rw [← add_assoc]
      exact mul_ne_of_lt _ ha _ h
  · apply add_le_of_forall_ne <;>
      (intro x' hx'; obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_lt_mul hx')
    · obtain h | h | h := lt_trichotomy (y + c) (b + c)
      · have H := mul_ne_of_lt _ hx _ h
        rw [Nimber.mul_add x, Nimber.mul_add a, Nimber.mul_add x] at H
        abel_nf at H ⊢
        simpa only [two_zsmul, zero_add] using H
      · exact (hy.ne <| add_left_injective _ h).elim
      · obtain ⟨z, hz, hz'⟩ | ⟨c', hc, hc'⟩ := exists_of_lt_add h
        · exact ((hz.trans hy).ne <| add_left_injective _ hz').elim
        · have := add_eq_iff_eq_add.1 hc'
          have H := mul_ne_of_lt _ hx _ hc
          rw [← hc', Nimber.mul_add a y c', ← add_ne_add_left (a * y), ← add_ne_add_left (a * c),
            ← add_ne_add_left (a * c'), ← add_eq_iff_eq_add.2 hc', Nimber.mul_add x,
            Nimber.mul_add x]
          abel_nf at H ⊢
          simpa only [two_zsmul, add_zero, zero_add] using H
    · obtain h | h | h := lt_trichotomy (b + y) (b + c)
      · have H := mul_ne_of_lt _ hx _ h
        rw [Nimber.mul_add x, Nimber.mul_add a, Nimber.mul_add x] at H
        abel_nf at H ⊢
        simpa only [two_zsmul, zero_add] using H
      · exact (hy.ne <| add_right_injective _ h).elim
      · obtain ⟨b', hb, hb'⟩ | ⟨z, hz, hz'⟩ := exists_of_lt_add h
        · have H := mul_ne_of_lt _ hx _ hb
          have hb'' := add_eq_iff_eq_add.2 (add_comm b c ▸ hb')
          rw [← hb', Nimber.mul_add a b', ← add_ne_add_left (a * y), ← add_ne_add_left (a * b),
            ← add_ne_add_left (a * b'), ← hb'', Nimber.mul_add x, Nimber.mul_add x]
          abel_nf at H ⊢
          simpa only [two_zsmul, add_zero, zero_add] using H
        · exact ((hz.trans hy).ne <| add_right_injective _ hz').elim
termination_by (a, b, c)

protected theorem add_mul (a b c : Nimber) : (a + b) * c = a * c + b * c := by
  rw [Nimber.mul_comm, Nimber.mul_add, Nimber.mul_comm, Nimber.mul_comm b]

private theorem add_ne_zero_of_lt {a b : Nimber} (h : b < a) : a + b ≠ 0 := by
  rw [add_ne_zero_iff]
  exact h.ne'

protected theorem mul_assoc (a b c : Nimber) : a * b * c = a * (b * c) := by
  apply le_antisymm <;> refine mul_le_of_forall_ne fun x hx y hy ↦ ?_
  · obtain ⟨a', ha, b', hb, rfl⟩ := exists_of_lt_mul hx
    have H : (a + a') * ((b + b') * (c + y)) ≠ 0 := by
      apply mul_ne_zero _ (mul_ne_zero _ _) <;> apply add_ne_zero_of_lt
      assumption'
    simp only [Nimber.add_mul, Nimber.mul_add] at H ⊢
    iterate 7 rw [Nimber.mul_assoc]
    rw [← add_ne_add_left (a * (b * c))]
    abel_nf at H ⊢
    simpa only [two_zsmul, zero_add] using H
  · obtain ⟨b', hb, c', hc, rfl⟩ := exists_of_lt_mul hy
    have H : (a + x) * (b + b') * (c + c') ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero _ _) <;> apply add_ne_zero_of_lt
      assumption'
    simp only [Nimber.add_mul, Nimber.mul_add] at H ⊢
    iterate 7 rw [← Nimber.mul_assoc]
    rw [← add_ne_add_left (a * b * c)]
    abel_nf at H ⊢
    simpa only [two_zsmul, zero_add] using H
termination_by (a, b, c)

instance : IsCancelMulZero Nimber where
  mul_left_cancel_of_ne_zero ha h := by
    rw [← add_eq_zero, ← Nimber.mul_add, mul_eq_zero] at h
    exact add_eq_zero.1 (h.resolve_left ha)
  mul_right_cancel_of_ne_zero ha h := by
    rw [← add_eq_zero, ← Nimber.add_mul, mul_eq_zero] at h
    exact add_eq_zero.1 (h.resolve_right ha)

protected theorem one_mul (a : Nimber) : 1 * a = a := by
  apply le_antisymm
  · refine mul_le_of_forall_ne fun x hx y hy ↦ ?_
    rw [Nimber.lt_one_iff_zero] at hx
    rw [hx, Nimber.one_mul, zero_mul, zero_mul, add_zero, zero_add]
    exact hy.ne
  · by_contra! h
    replace h := h -- needed to remind `termination_by`
    exact (mul_left_cancel₀ one_ne_zero <| Nimber.one_mul _).not_lt h
termination_by a

protected theorem mul_one (a : Nimber) : a * 1 = a := by
  rw [Nimber.mul_comm, Nimber.one_mul]

instance : CommRing Nimber where
  left_distrib := Nimber.mul_add
  right_distrib := Nimber.add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := Nimber.mul_assoc
  mul_comm := Nimber.mul_comm
  one_mul := Nimber.one_mul
  mul_one := Nimber.mul_one
  __ : AddCommGroupWithOne Nimber := inferInstance

instance : IsDomain Nimber where
instance : CancelMonoidWithZero Nimber where

end Nimber
