/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Algebra.CharP.Two
import Mathlib.SetTheory.Nimber.Basic
import Mathlib.Tactic.Abel

/-!
# Nimber multiplication and division

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
  apply le_antisymm <;>
    apply mul_le_of_forall_ne <;>
    intro x hx y hy
  on_goal 1 => rw [add_comm (x * _), Nimber.mul_comm a, Nimber.mul_comm x, Nimber.mul_comm x]
  on_goal 2 => rw [add_comm (x * _), ← Nimber.mul_comm y, ← Nimber.mul_comm a, ← Nimber.mul_comm y]
  all_goals exact mul_ne_of_lt y hy x hx
termination_by (a, b)

protected theorem mul_add (a b c : Nimber) : a * (b + c) = a * b + a * c := by
  apply le_antisymm
  · apply mul_le_of_forall_ne
    intro a' ha x hx
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
      intro x' hx' <;>
      obtain ⟨x, hx, y, hy, rfl⟩ := exists_of_lt_mul hx'
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

protected theorem mul_assoc (a b c : Nimber) : a * b * c = a * (b * c) := by
  apply le_antisymm <;>
    apply mul_le_of_forall_ne <;>
    intro x hx y hy
  · obtain ⟨a', ha, b', hb, rfl⟩ := exists_of_lt_mul hx
    have H : (a + a') * ((b + b') * (c + y)) ≠ 0 := by
      apply mul_ne_zero _ (mul_ne_zero _ _)
      all_goals
        rw [add_ne_zero_iff]
        apply ne_of_gt
        assumption
    simp only [Nimber.add_mul, Nimber.mul_add] at H ⊢
    iterate 7 rw [Nimber.mul_assoc]
    rw [← add_ne_add_left (a * (b * c))]
    abel_nf at H ⊢
    simpa only [two_zsmul, zero_add] using H
  · obtain ⟨b', hb, c', hc, rfl⟩ := exists_of_lt_mul hy
    have H : (a + x) * (b + b') * (c + c') ≠ 0 := by
      apply mul_ne_zero (mul_ne_zero _ _)
      all_goals
        rw [add_ne_zero_iff]
        apply ne_of_gt
        assumption
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
  · apply mul_le_of_forall_ne
    intro x hx y hy
    rw [Nimber.lt_one_iff_zero] at hx
    rw [hx, Nimber.one_mul, zero_mul, zero_mul, add_zero, zero_add]
    exact hy.ne
  · -- by_contra! doesn't work for whatever reason.
    by_contra h
    replace h := lt_of_not_le h
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

/-- The nimber inverse `a⁻¹` is recursively defined as the smallest nimber not in the set `s`, which
itself is recursively defined as the smallest set with `0 ∈ s` and `(1 + (a + a') * b) / a' ∈ s`
for `0 < a' < a` and `b ∈ s`.

This preliminary definition "accidentally" satisfies `inv 0 = 1`, which the real inverse corrects.
-/
def inv (a : Nimber) : Nimber :=
  sInf (⋂₀ {s | 0 ∈ s ∧ ∀ a' < a, a' ≠ 0 → ∀ b ∈ s, inv a' * (1 + (a + a') * b) ∈ s})ᶜ
termination_by a

/-- The (complement of the) set in the definition of `inv a`. -/
def inv_set (a : Nimber) : Set Nimber :=
  ⋂₀ {s | 0 ∈ s ∧ ∀ a' < a, a' ≠ 0 → ∀ b ∈ s, inv a' * (1 + (a + a') * b) ∈ s}

theorem inv_def (a : Nimber) : inv a = sInf (inv_set a)ᶜ := by
  rw [inv]
  rfl

theorem zero_mem_inv_set (a : Nimber) : 0 ∈ inv_set a :=
  Set.mem_sInter.2 fun _ hs => hs.1

/-- "cons" is our operation `(1 + (a + a') * b) / a'` in the definition of the inverse. -/
theorem cons_mem_inv_set {a' : Nimber} (ha₀ : a' ≠ 0) (ha : a' < a) (hb : b ∈ inv_set a) :
    inv a' * (1 + (a + a') * b) ∈ inv_set a :=
  Set.mem_sInter.2 fun _ hs => hs.2 _ ha ha₀ _ (Set.mem_sInter.1 hb _ hs)

/-- A recursion principle for `inv_set`. -/
@[elab_as_elim]
theorem inv_recOn {p : Nimber → Prop} (a : Nimber) (h0 : p 0)
    (hi : ∀ a' < a, a' ≠ 0 → ∀ b, p b → p (inv a' * (1 + (a + a') * b))) (x : Nimber)
    (hx : x ∈ inv_set a) : p x := by
  revert x
  exact Set.sInter_subset_of_mem ⟨h0, hi⟩

/--- An auxiliary type for enumerating the elements of `inv_set`, and proving that its complement
is nonempty. -/
private inductive InvTy (a : Nimber.{u}) : Type u
  | zero : InvTy a
  | cons : (toOrdinal a).toType → InvTy a → InvTy a

/-- An enumeration of elements in the complement of `inv_set` by a type in the same universe. -/
private def InvTy.toNimber {a : Nimber} : InvTy a → Nimber
  | zero => 0
  | cons x b => let a' := Ordinal.toNimber ((Ordinal.enumIsoToType (toOrdinal a)).symm x)
      inv a' * (1 + (a + a') * (toNimber b))

/-- The complement of `inv_set a` is nonempty. -/
private theorem inv_set_nonempty (a : Nimber.{u}) : (inv_set a)ᶜ.Nonempty := by
  refine nonempty_of_not_bddAbove <| @Ordinal.not_bddAbove_compl_of_small _ <|
    @small_subset.{u, u + 1} _ _ _ ?_ (small_range (@InvTy.toNimber.{u} a))
  refine fun x hx ↦ inv_recOn a ⟨InvTy.zero, rfl⟩ ?_ x hx
  rintro a' ha _ _ ⟨b, rfl⟩
  use InvTy.cons (Ordinal.enumIsoToType _ ⟨toOrdinal a', ha⟩) b
  rw [InvTy.toNimber]
  simp

theorem inv_ne_zero (a : Nimber) : inv a ≠ 0 := by
  rw [inv_def]
  intro h
  exact h ▸ csInf_mem (inv_set_nonempty a) <| zero_mem_inv_set a

theorem mem_inv_set_of_lt_inv (h : b < inv a) : b ∈ inv_set a := by
  rw [inv_def] at h
  have := not_mem_of_lt_csInf h ⟨_, bot_mem_lowerBounds _⟩
  rwa [Set.not_mem_compl_iff] at this

theorem inv_not_mem_inv_set (a : Nimber) : inv a ∉ inv_set a := by
  rw [inv_def]
  exact csInf_mem (inv_set_nonempty a)

theorem mem_inv_set_of_inv_lt (ha : a ≠ 0) (hb : a < b) : inv a ∈ inv_set b := by
  have H := cons_mem_inv_set ha hb (zero_mem_inv_set b)
  rwa [mul_zero, add_zero, mul_one] at H

private theorem inv_ne_of_lt (ha : a ≠ 0) (hb : a < b) : inv a ≠ inv b :=
  fun h => inv_not_mem_inv_set b (h ▸ mem_inv_set_of_inv_lt ha hb)

theorem inv_injective : Set.InjOn inv {0}ᶜ := by
  intro a ha b hb h
  obtain hab | rfl | hab := lt_trichotomy a b
  · cases inv_ne_of_lt ha hab h
  · rfl
  · cases inv_ne_of_lt hb hab h.symm

theorem inv_inj (ha : a ≠ 0) (hb : b ≠ 0) : inv a = inv b ↔ a = b :=
  inv_injective.eq_iff ha hb

/-- We set up a simultaneous induction to prove that `inv a` is the inverse of `a`, and no element
in its defining set `inv_set a` is. -/
private theorem main (a : Nimber) : (∀ b ∈ inv_set a, a * b ≠ 1) ∧ (a ≠ 0 → a * inv a = 1) := by
  have H₁ : ∀ b ∈ inv_set a, a * b ≠ 1 := by
    intro b hb
    refine inv_recOn a ?_ ?_ b hb
    · rw [mul_zero]
      exact zero_ne_one
    · intro a' ha ha' b hb
      rw [ne_eq, mul_comm, ← mul_right_inj' ha', ← mul_assoc, ← mul_assoc, (main a').2 ha',
        one_mul, mul_one, add_mul, one_mul, ← add_left_inj a', add_self, mul_assoc, mul_comm b,
        add_assoc, add_comm _ a', ← add_assoc, ← mul_one_add, ← ne_eq, mul_ne_zero_iff,
        add_ne_zero_iff, add_ne_zero_iff]
      use ha.ne', hb.symm
  refine ⟨H₁, fun ha₀ => le_antisymm ?_ ?_⟩
  · apply mul_le_of_forall_ne
    intro a' ha b hb H
    replace hb := mem_inv_set_of_lt_inv hb
    rw [add_assoc, ← add_mul, ← CharTwo.eq_add_iff_add_eq] at H
    obtain rfl | ha' := eq_or_ne a' 0
    · rw [zero_mul, add_zero, ← add_eq_iff_eq_add, zero_add] at H
      exact H₁ _ hb H
    · rw [← mul_right_inj' (inv_ne_zero a'), ← mul_assoc, mul_comm _ a', (main a').2 ha',
        one_mul] at H
      exact inv_not_mem_inv_set a (H ▸ cons_mem_inv_set ha' ha hb)
  · rw [one_le_iff_ne_zero, mul_ne_zero_iff]
    use ha₀, inv_ne_zero a
termination_by a

/-- This proves that `inv a` is the multiplicative inverse of `a`. -/
theorem mul_inv_cancel' (h : a ≠ 0) : a * inv a = 1 :=
  (main a).2 h

instance : Inv Nimber :=
  ⟨fun a => if a = 0 then 0 else inv a⟩

theorem inv_eq_inv (ha : a ≠ 0) : a⁻¹ = inv a :=
  dif_neg ha

protected theorem mul_inv_cancel (ha : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [inv_eq_inv ha, mul_inv_cancel' ha]

instance : Field Nimber where
  mul_inv_cancel := @Nimber.mul_inv_cancel
  inv_zero := dif_pos rfl
  nnqsmul := _
  qsmul := _

end Nimber
