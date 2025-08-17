/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.SetTheory.Nimber.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linter.DeprecatedModule

deprecated_module
  "This module is now at `CombinatorialGames.Nimber.Field` in the CGT repo <https://github.com/vihdzp/combinatorial-games>"
  (since := "2025-08-06")

/-!
# Nimber multiplication and division

The nim product `a * b` is recursively defined as the least nimber not equal to any
`a' * b + a * b' + a' * b'` for `a' < a` and `b' < b`. When endowed with this operation, the nimbers
form a field.

It's possible to show the existence of the nimber inverse implicitly via the simplicity theorem.
Instead, we employ the explicit formula given in [On Numbers And Games][conway2001] (p. 56), which
uses mutual induction and mimics the definition for the surreal inverse. This definition `invAux`
"accidentally" gives the inverse of `0` as `1`, which the real inverse corrects.

## Todo

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
  have := notMem_of_lt_csInf' h
  rwa [Set.notMem_compl_iff] at this

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
  mul_left_cancel_of_ne_zero ha _ _ h := by
    rw [← add_eq_zero, ← Nimber.mul_add, mul_eq_zero] at h
    exact add_eq_zero.1 (h.resolve_left ha)
  mul_right_cancel_of_ne_zero ha _ _ h := by
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

/-! ### Nimber division -/

mutual

/-- The nimber inverse `a⁻¹` is mutually recursively defined as the smallest nimber not in the set
`s = invSet a`, which itself is defined as the smallest set with `0 ∈ s` and
`(1 + (a + a') * b) / a' ∈ s` for `0 < a' < a` and `b ∈ s`.

This preliminary definition "accidentally" satisfies `invAux 0 = 1`, which the real inverse
corrects. The lemma `inv_eq_invAux` can be used to transfer between the two. -/
def invAux (a : Nimber) : Nimber :=
  sInf (invSet a)ᶜ
termination_by (a, 1)

/-- The set in the definition of `invAux a`. -/
def invSet (a : Nimber) : Set Nimber :=
  ⋂₀ {s | 0 ∈ s ∧ ∀ a' < a, a' ≠ 0 → ∀ b ∈ s, invAux a' * (1 + (a + a') * b) ∈ s}
termination_by (a, 0)

end

theorem zero_mem_invSet (a : Nimber) : 0 ∈ invSet a := by
  rw [invSet]
  exact Set.mem_sInter.2 fun _ hs => hs.1

/-- "cons" is our operation `(1 + (a + a') * b) / a'` in the definition of the inverse. -/
theorem cons_mem_invSet {a' : Nimber} (ha₀ : a' ≠ 0) (ha : a' < a) (hb : b ∈ invSet a) :
    invAux a' * (1 + (a + a') * b) ∈ invSet a := by
  rw [invSet] at hb ⊢
  exact Set.mem_sInter.2 fun _ hs => hs.2 _ ha ha₀ _ (Set.mem_sInter.1 hb _ hs)

/-- A recursion principle for `invSet`. -/
@[elab_as_elim]
theorem invSet_recOn {p : Nimber → Prop} (a : Nimber) (h0 : p 0)
    (hi : ∀ a' < a, a' ≠ 0 → ∀ b, p b → p (invAux a' * (1 + (a + a') * b))) (x : Nimber)
    (hx : x ∈ invSet a) : p x := by
  revert x
  rw [invSet]
  exact Set.sInter_subset_of_mem ⟨h0, hi⟩

/-- An enumeration of elements in `invSet` by a type in the same universe. -/
private def List.toNimber {a : Nimber} : List a.toOrdinal.toType → Nimber
  | [] => 0
  | x :: l =>
    let a' := ∗((Ordinal.enumIsoToType a.toOrdinal).symm x)
    invAux a' * (1 + (a + a') * toNimber l)

instance (a : Nimber.{u}) : Small.{u} (invSet a) := by
  refine @small_subset.{u, u + 1} _ _ _ ?_ (small_range (@List.toNimber a))
  refine fun x hx ↦ invSet_recOn a ⟨[], rfl⟩ ?_ x hx
  rintro a' ha _ _ ⟨l, rfl⟩
  use Ordinal.enumIsoToType _ ⟨toOrdinal a', ha⟩ :: l
  rw [List.toNimber]
  simp

/-- The complement of `invSet a` is nonempty. -/
private theorem invSet_nonempty (a : Nimber) : (invSet a)ᶜ.Nonempty :=
  have := instSmallElemInvSet a -- why is this needed?
  nonempty_of_not_bddAbove (Ordinal.not_bddAbove_compl_of_small _)

theorem invAux_ne_zero (a : Nimber) : invAux a ≠ 0 := by
  rw [invAux]
  exact fun h ↦ h ▸ csInf_mem (invSet_nonempty a) <| zero_mem_invSet a

theorem mem_invSet_of_lt_invAux (h : b < invAux a) : b ∈ invSet a := by
  rw [invAux] at h
  have := notMem_of_lt_csInf h ⟨_, bot_mem_lowerBounds _⟩
  rwa [Set.notMem_compl_iff] at this

theorem invAux_notMem_invSet (a : Nimber) : invAux a ∉ invSet a := by
  rw [invAux]
  exact csInf_mem (invSet_nonempty a)

@[deprecated (since := "2025-05-23")] alias invAux_not_mem_invSet := invAux_notMem_invSet

theorem invAux_mem_invSet_of_lt (ha : a ≠ 0) (hb : a < b) : invAux a ∈ invSet b := by
  have H := cons_mem_invSet ha hb (zero_mem_invSet b)
  rwa [mul_zero, add_zero, mul_one] at H

/-- We set up a simultaneous induction to prove that `invAux a` is the inverse of `a`, and no
element in its defining set `invSet a` is. -/
private theorem mul_inv_cancel_aux (a : Nimber) :
    (∀ b ∈ invSet a, a * b ≠ 1) ∧ (a ≠ 0 → a * invAux a = 1) := by
  have H₁ : ∀ b ∈ invSet a, a * b ≠ 1 := by
    refine fun b hb ↦ invSet_recOn a ?_ ?_ b hb
    · rw [mul_zero]
      exact zero_ne_one
    · intro a' ha ha' b hb
      rw [ne_eq, mul_comm, ← mul_right_inj' ha', ← mul_assoc, ← mul_assoc,
        (mul_inv_cancel_aux a').2 ha', one_mul, mul_one, add_mul, one_mul, ← add_left_inj a',
        add_self, mul_assoc, mul_comm b, add_assoc, add_comm _ a', ← add_assoc, ← mul_one_add,
        ← ne_eq, mul_ne_zero_iff, add_ne_zero_iff, add_ne_zero_iff]
      exact ⟨ha.ne', hb.symm⟩
  refine ⟨H₁, fun ha₀ => le_antisymm ?_ ?_⟩
  · apply mul_le_of_forall_ne fun a' ha b hb H ↦ ?_
    replace hb := mem_invSet_of_lt_invAux hb
    rw [add_assoc, ← add_mul, ← CharTwo.eq_add_iff_add_eq] at H
    obtain rfl | ha' := eq_or_ne a' 0
    · rw [zero_mul, add_zero, ← add_eq_iff_eq_add, zero_add] at H
      exact H₁ _ hb H
    · rw [← mul_right_inj' (invAux_ne_zero a'), ← mul_assoc, mul_comm _ a',
        (mul_inv_cancel_aux a').2 ha', one_mul] at H
      exact invAux_notMem_invSet a (H ▸ cons_mem_invSet ha' ha hb)
  · rw [one_le_iff_ne_zero, mul_ne_zero_iff]
    exact ⟨ha₀, invAux_ne_zero a⟩
termination_by a

theorem mul_invAux_cancel (h : a ≠ 0) : a * invAux a = 1 :=
  (mul_inv_cancel_aux a).2 h

instance : Inv Nimber where
  inv a := if a = 0 then 0 else invAux a

theorem inv_eq_invAux (ha : a ≠ 0) : a⁻¹ = invAux a :=
  dif_neg ha

instance : Field Nimber where
  mul_inv_cancel a ha := by rw [inv_eq_invAux ha, mul_invAux_cancel ha]
  inv_zero := dif_pos rfl
  nnqsmul := _
  qsmul := _

end Nimber
