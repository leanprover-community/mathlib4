/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Group.Subgroup.ZPowers
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Order.Archimedean
import Mathlib.GroupTheory.Coset

/-!
# Periodicity

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `Function.Periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `Function.Antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2 • c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/


variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

open Set

namespace Function

/-! ### Periodicity -/


/-- A function `f` is said to be `Periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp]
def Periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x

protected theorem Periodic.funext [Add α] (h : Periodic f c) : (fun x => f (x + c)) = f :=
  funext h

protected theorem Periodic.comp [Add α] (h : Periodic f c) (g : β → γ) : Periodic (g ∘ f) c := by
  simp_all

theorem Periodic.comp_addHom [Add α] [Add γ] (h : Periodic f c) (g : AddHom γ α) (g_inv : α → γ)
    (hg : RightInverse g_inv g) : Periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]

@[to_additive]
protected theorem Periodic.mul [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f * g) c := by simp_all

@[to_additive]
protected theorem Periodic.div [Add α] [Div β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f / g) c := by simp_all

@[to_additive]
theorem _root_.List.periodic_prod [Add α] [Monoid β] (l : List (α → β))
    (hl : ∀ f ∈ l, Periodic f c) : Periodic l.prod c := by
  induction' l with g l ih hl
  · simp
  · rw [List.forall_mem_cons] at hl
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)

@[to_additive]
theorem _root_.Multiset.periodic_prod [Add α] [CommMonoid β] (s : Multiset (α → β))
    (hs : ∀ f ∈ s, Periodic f c) : Periodic s.prod c :=
  (s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f <| Multiset.mem_toList.mp hf

@[to_additive]
theorem _root_.Finset.periodic_prod [Add α] [CommMonoid β] {ι : Type*} {f : ι → α → β}
    (s : Finset ι) (hs : ∀ i ∈ s, Periodic (f i) c) : Periodic (∏ i ∈ s, f i) c :=
  s.prod_to_list f ▸ (s.toList.map f).periodic_prod (by simpa [-Periodic] )

@[to_additive]
protected theorem Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
    Periodic (a • f) c := by simp_all

protected theorem Periodic.const_smul [AddMonoid α] [Group γ] [DistribMulAction γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

protected theorem Periodic.const_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

protected theorem Periodic.const_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  Periodic.const_smul₀ h a

theorem Periodic.const_inv_smul [AddMonoid α] [Group γ] [DistribMulAction γ α] (h : Periodic f c)
    (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹

theorem Periodic.const_inv_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ a⁻¹

theorem Periodic.const_inv_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a

theorem Periodic.mul_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ (MulOpposite.op a)

theorem Periodic.mul_const' [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c / a) := by simpa only [div_eq_mul_inv] using h.mul_const a

theorem Periodic.mul_const_inv [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ (MulOpposite.op a)

theorem Periodic.div_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x / a)) (c * a) := by simpa only [div_eq_mul_inv] using h.mul_const_inv a

theorem Periodic.add_period [AddSemigroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ + c₂) := by simp_all [← add_assoc]

theorem Periodic.sub_eq [AddGroup α] (h : Periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [sub_add_cancel] using (h (x - c)).symm

theorem Periodic.sub_eq' [AddCommGroup α] (h : Periodic f c) : f (c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)

protected theorem Periodic.neg [AddGroup α] (h : Periodic f c) : Periodic f (-c) := by
  simpa only [sub_eq_add_neg, Periodic] using h.sub_eq

theorem Periodic.sub_period [AddGroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ - c₂) := fun x => by
  rw [sub_eq_add_neg, ← add_assoc, h2.neg, h1]

theorem Periodic.const_add [AddSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)

theorem Periodic.add_const [AddCommSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)

theorem Periodic.const_sub [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]

theorem Periodic.sub_const [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

theorem Periodic.nsmul [AddMonoid α] (h : Periodic f c) (n : ℕ) : Periodic f (n • c) := by
  induction n <;> simp_all [add_nsmul, ← add_assoc, zero_nsmul]

theorem Periodic.nat_mul [Semiring α] (h : Periodic f c) (n : ℕ) : Periodic f (n * c) := by
  simpa only [nsmul_eq_mul] using h.nsmul n

theorem Periodic.neg_nsmul [AddGroup α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n • c)) :=
  (h.nsmul n).neg

theorem Periodic.neg_nat_mul [Ring α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n * c)) :=
  (h.nat_mul n).neg

theorem Periodic.sub_nsmul_eq [AddGroup α] (h : Periodic f c) (n : ℕ) : f (x - n • c) = f x := by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x

theorem Periodic.sub_nat_mul_eq [Ring α] (h : Periodic f c) (n : ℕ) : f (x - n * c) = f x := by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

theorem Periodic.nsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : ℕ) :
    f (n • c - x) = f (-x) :=
  (h.nsmul n).sub_eq'

theorem Periodic.nat_mul_sub_eq [Ring α] (h : Periodic f c) (n : ℕ) : f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

protected theorem Periodic.zsmul [AddGroup α] (h : Periodic f c) (n : ℤ) : Periodic f (n • c) := by
  cases' n with n n
  · simpa only [Int.ofNat_eq_coe, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg

protected theorem Periodic.int_mul [Ring α] (h : Periodic f c) (n : ℤ) : Periodic f (n * c) := by
  simpa only [zsmul_eq_mul] using h.zsmul n

theorem Periodic.sub_zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (x - n • c) = f x :=
  (h.zsmul n).sub_eq x

theorem Periodic.sub_int_mul_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (x - n * c) = f x :=
  (h.int_mul n).sub_eq x

theorem Periodic.zsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : ℤ) :
    f (n • c - x) = f (-x) :=
  (h.zsmul _).sub_eq'

theorem Periodic.int_mul_sub_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (n * c - x) = f (-x) :=
  (h.int_mul _).sub_eq'

protected theorem Periodic.eq [AddZeroClass α] (h : Periodic f c) : f c = f 0 := by
  simpa only [zero_add] using h 0

protected theorem Periodic.neg_eq [AddGroup α] (h : Periodic f c) : f (-c) = f 0 :=
  h.neg.eq

protected theorem Periodic.nsmul_eq [AddMonoid α] (h : Periodic f c) (n : ℕ) : f (n • c) = f 0 :=
  (h.nsmul n).eq

theorem Periodic.nat_mul_eq [Semiring α] (h : Periodic f c) (n : ℕ) : f (n * c) = f 0 :=
  (h.nat_mul n).eq

theorem Periodic.zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (n • c) = f 0 :=
  (h.zsmul n).eq

theorem Periodic.int_mul_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (n * c) = f 0 :=
  (h.int_mul n).eq

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico₀ [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x) : ∃ y ∈ Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩

theorem Periodic.image_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Ioc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩

theorem Periodic.image_Icc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Icc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| h.image_Ioc hc a ▸ image_subset _ Ioc_subset_Icc_self

theorem Periodic.image_uIcc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : c ≠ 0) (a : α) : f '' uIcc a (a + c) = range f := by
  cases hc.lt_or_lt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le), ← h.neg.image_Icc (neg_pos.2 hc) (a + c),
      add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]

theorem periodic_with_period_zero [AddZeroClass α] (f : α → β) : Periodic f 0 := fun x => by
  rw [add_zero]

theorem Periodic.map_vadd_zmultiples [AddCommGroup α] (hf : Periodic f c)
    (a : AddSubgroup.zmultiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubgroup.vadd_def, add_comm _ x, hf.zsmul m x]

theorem Periodic.map_vadd_multiples [AddCommMonoid α] (hf : Periodic f c)
    (a : AddSubmonoid.multiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]

/-- Lift a periodic function to a function from the quotient group. -/
def Periodic.lift [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))

@[simp]
theorem Periodic.lift_coe [AddGroup α] (h : Periodic f c) (a : α) :
    h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a :=
  rfl

/-- A periodic function `f : R → X` on a semiring (or, more generally, `AddZeroClass`)
of non-zero period is not injective. -/
lemma Periodic.not_injective {R X : Type*} [AddZeroClass R] {f : R → X} {c : R}
    (hf : Periodic f c) (hc : c ≠ 0) : ¬ Injective f := fun h ↦ hc <| h hf.eq

/-! ### Antiperiodicity -/

/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp]
def Antiperiodic [Add α] [Neg β] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = -f x

protected theorem Antiperiodic.funext [Add α] [Neg β] (h : Antiperiodic f c) :
    (fun x => f (x + c)) = -f :=
  funext h

protected theorem Antiperiodic.funext' [Add α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    (fun x => -f (x + c)) = f :=
  neg_eq_iff_eq_neg.mpr h.funext

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` with period
`2 • c`. -/
protected theorem Antiperiodic.periodic [AddMonoid α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 • c) := by simp [two_nsmul, ← add_assoc, h _]

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` with period
  `2 * c`. -/
protected theorem Antiperiodic.periodic_two_mul [Semiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 * c) := nsmul_eq_mul 2 c ▸ h.periodic

protected theorem Antiperiodic.eq [AddZeroClass α] [Neg β] (h : Antiperiodic f c) : f c = -f 0 := by
  simpa only [zero_add] using h 0

theorem Antiperiodic.even_nsmul_periodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Periodic f ((2 * n) • c) := mul_nsmul c 2 n ▸ h.periodic.nsmul n

theorem Antiperiodic.nat_even_mul_periodic [Semiring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.nat_mul n

theorem Antiperiodic.odd_nsmul_antiperiodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Antiperiodic f ((2 * n + 1) • c) := fun x => by
  rw [add_nsmul, one_nsmul, ← add_assoc, h, h.even_nsmul_periodic]

theorem Antiperiodic.nat_odd_mul_antiperiodic [Semiring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.nat_even_mul_periodic]

theorem Antiperiodic.even_zsmul_periodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Periodic f ((2 * n) • c) := by
  rw [mul_comm, mul_zsmul, two_zsmul, ← two_nsmul]
  exact h.periodic.zsmul n

theorem Antiperiodic.int_even_mul_periodic [Ring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.int_mul n

theorem Antiperiodic.odd_zsmul_antiperiodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Antiperiodic f ((2 * n + 1) • c) := by
  intro x
  rw [add_zsmul, one_zsmul, ← add_assoc, h, h.even_zsmul_periodic]

theorem Antiperiodic.int_odd_mul_antiperiodic [Ring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.int_even_mul_periodic]

theorem Antiperiodic.sub_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (x : α) :
    f (x - c) = -f x := by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]

theorem Antiperiodic.sub_eq' [AddCommGroup α] [Neg β] (h : Antiperiodic f c) :
    f (c - x) = -f (-x) := by simpa only [sub_eq_neg_add] using h (-x)

protected theorem Antiperiodic.neg [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    Antiperiodic f (-c) := by simpa only [sub_eq_add_neg, Antiperiodic] using h.sub_eq

theorem Antiperiodic.neg_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    f (-c) = -f 0 := by
  simpa only [zero_add] using h.neg 0

theorem Antiperiodic.nat_mul_eq_of_eq_zero [Semiring α] [NegZeroClass β] (h : Antiperiodic f c)
    (hi : f 0 = 0) : ∀ n : ℕ, f (n * c) = 0
  | 0 => by rwa [Nat.cast_zero, zero_mul]
  | n + 1 => by simp [add_mul, h _, Antiperiodic.nat_mul_eq_of_eq_zero h hi n]

theorem Antiperiodic.int_mul_eq_of_eq_zero [Ring α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (hi : f 0 = 0) : ∀ n : ℤ, f (n * c) = 0
  | (n : ℕ) => by rw [Int.cast_natCast, h.nat_mul_eq_of_eq_zero hi n]
  | .negSucc n => by rw [Int.cast_negSucc, neg_mul, ← mul_neg, h.neg.nat_mul_eq_of_eq_zero hi]

theorem Antiperiodic.add_zsmul_eq [AddGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℤ) :
    f (x + n • c) = (n.negOnePow : ℤ) • f x := by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_zsmul_periodic, Int.negOnePow_two_mul, Units.val_one, one_zsmul]
  · rw [h.odd_zsmul_antiperiodic, Int.negOnePow_two_mul_add_one, Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul]

theorem Antiperiodic.sub_zsmul_eq [AddGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℤ) :
    f (x - n • c) = (n.negOnePow : ℤ) • f x := by
  simpa only [sub_eq_add_neg, neg_zsmul, Int.negOnePow_neg] using h.add_zsmul_eq (-n)

theorem Antiperiodic.zsmul_sub_eq [AddCommGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℤ) :
    f (n • c - x) = (n.negOnePow : ℤ) • f (-x) := by
  rw [sub_eq_add_neg, add_comm]
  exact h.add_zsmul_eq n

theorem Antiperiodic.add_int_mul_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℤ) :
    f (x + n * c) = (n.negOnePow : ℤ) * f x := by simpa only [zsmul_eq_mul] using h.add_zsmul_eq n

theorem Antiperiodic.sub_int_mul_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℤ) :
    f (x - n * c) = (n.negOnePow : ℤ) * f x := by simpa only [zsmul_eq_mul] using h.sub_zsmul_eq n

theorem Antiperiodic.int_mul_sub_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℤ) :
    f (n * c - x) = (n.negOnePow : ℤ) * f (-x) := by
  simpa only [zsmul_eq_mul] using h.zsmul_sub_eq n

theorem Antiperiodic.add_nsmul_eq [AddMonoid α] [AddGroup β] (h : Antiperiodic f c) (n : ℕ) :
    f (x + n • c) = (-1) ^ n • f x := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_nsmul_periodic, pow_mul, (by norm_num : (-1) ^ 2 = 1), one_pow, one_zsmul]
  · rw [h.odd_nsmul_antiperiodic, pow_add, pow_mul, (by norm_num : (-1) ^ 2 = 1), one_pow,
      pow_one, one_mul, neg_zsmul, one_zsmul]

theorem Antiperiodic.sub_nsmul_eq [AddGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℕ) :
    f (x - n • c) = (-1) ^ n • f x := by
  simpa only [Int.reduceNeg, natCast_zsmul] using h.sub_zsmul_eq n

theorem Antiperiodic.nsmul_sub_eq [AddCommGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℕ) :
    f (n • c - x) = (-1) ^ n • f (-x) := by
  simpa only [Int.reduceNeg, natCast_zsmul] using h.zsmul_sub_eq n

theorem Antiperiodic.add_nat_mul_eq [Semiring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x + n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n

theorem Antiperiodic.sub_nat_mul_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x - n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.sub_nsmul_eq n

theorem Antiperiodic.nat_mul_sub_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (n * c - x) = (-1) ^ n * f (-x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n

theorem Antiperiodic.const_add [AddSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)

theorem Antiperiodic.add_const [AddCommSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)

theorem Antiperiodic.const_sub [AddCommGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]

theorem Antiperiodic.sub_const [AddCommGroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)

theorem Antiperiodic.smul [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (a • f) c := by simp_all

theorem Antiperiodic.const_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)

theorem Antiperiodic.const_smul₀ [AddCommMonoid α] [Neg β] [DivisionSemiring γ] [Module γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) :=
  fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

theorem Antiperiodic.const_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ ha

theorem Antiperiodic.const_inv_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹

theorem Antiperiodic.const_inv_smul₀ [AddCommMonoid α] [Neg β] [DivisionSemiring γ] [Module γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)

theorem Antiperiodic.const_inv_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ ha

theorem Antiperiodic.mul_const [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

theorem Antiperiodic.mul_const' [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c / a) := by
  simpa only [div_eq_mul_inv] using h.mul_const ha

theorem Antiperiodic.mul_const_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha

theorem Antiperiodic.div_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha

theorem Antiperiodic.add [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ + c₂) := by simp_all [← add_assoc]

theorem Antiperiodic.sub [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add h2.neg

theorem Periodic.add_antiperiod [AddGroup α] [Neg β] (h1 : Periodic f c₁) (h2 : Antiperiodic f c₂) :
    Antiperiodic f (c₁ + c₂) := by simp_all [← add_assoc]

theorem Periodic.sub_antiperiod [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : Antiperiodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg

theorem Periodic.add_antiperiod_eq [AddGroup α] [Neg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ + c₂) = -f 0 :=
  (h1.add_antiperiod h2).eq

theorem Periodic.sub_antiperiod_eq [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ - c₂) = -f 0 :=
  (h1.sub_antiperiod h2).eq

theorem Antiperiodic.mul [Add α] [Mul β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f * g) c := by simp_all

theorem Antiperiodic.div [Add α] [DivisionMonoid β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f / g) c := by simp_all [neg_div_neg_eq]

end Function

theorem Int.fract_periodic (α) [LinearOrderedRing α] [FloorRing α] :
    Function.Periodic Int.fract (1 : α) := fun a => mod_cast Int.fract_add_int a 1
