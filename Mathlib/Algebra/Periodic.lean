/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Group.Subgroup.ZPowers
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupPower.NegOnePow
import Mathlib.Algebra.Order.Archimedean
import Mathlib.GroupTheory.Coset

#align_import algebra.periodic from "leanprover-community/mathlib"@"30413fc89f202a090a54d78e540963ed3de0056e"

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

open Set BigOperators

namespace Function

/-! ### Periodicity -/


/-- A function `f` is said to be `Periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp]
def Periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x
#align function.periodic Function.Periodic

protected lemma Periodic.funext [Add α] (h : Periodic f c) : (fun x => f (x + c)) = f :=
  funext h
#align function.periodic.funext Function.Periodic.funext

protected lemma Periodic.comp [Add α] (h : Periodic f c) (g : β → γ) : Periodic (g ∘ f) c := by
  simp_all
#align function.periodic.comp Function.Periodic.comp

lemma Periodic.comp_addHom [Add α] [Add γ] (h : Periodic f c) (g : AddHom γ α) (g_inv : α → γ)
    (hg : RightInverse g_inv g) : Periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]
#align function.periodic.comp_add_hom Function.Periodic.comp_addHom

@[to_additive]
protected lemma Periodic.mul [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f * g) c := by simp_all
#align function.periodic.mul Function.Periodic.mul
#align function.periodic.add Function.Periodic.add

@[to_additive]
protected lemma Periodic.div [Add α] [Div β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f / g) c := by simp_all
#align function.periodic.div Function.Periodic.div
#align function.periodic.sub Function.Periodic.sub

@[to_additive]
lemma _root_.List.periodic_prod [Add α] [Monoid β] (l : List (α → β))
    (hl : ∀ f ∈ l, Periodic f c) : Periodic l.prod c := by
  induction' l with g l ih hl
  · simp
  · rw [List.forall_mem_cons] at hl
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)
#align list.periodic_prod List.periodic_prod
#align list.periodic_sum List.periodic_sum

@[to_additive]
lemma _root_.Multiset.periodic_prod [Add α] [CommMonoid β] (s : Multiset (α → β))
    (hs : ∀ f ∈ s, Periodic f c) : Periodic s.prod c :=
  (s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f <| Multiset.mem_toList.mp hf
#align multiset.periodic_prod Multiset.periodic_prod
#align multiset.periodic_sum Multiset.periodic_sum

@[to_additive]
lemma _root_.Finset.periodic_prod [Add α] [CommMonoid β] {ι : Type*} {f : ι → α → β}
    (s : Finset ι) (hs : ∀ i ∈ s, Periodic (f i) c) : Periodic (∏ i in s, f i) c :=
  s.prod_to_list f ▸ (s.toList.map f).periodic_prod (by simpa [-Periodic] )
#align finset.periodic_prod Finset.periodic_prod
#align finset.periodic_sum Finset.periodic_sum

@[to_additive]
protected lemma Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
    Periodic (a • f) c := by simp_all
#align function.periodic.smul Function.Periodic.smul
#align function.periodic.vadd Function.Periodic.vadd

protected lemma Periodic.const_smul [AddMonoid α] [Group γ] [DistribMulAction γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)
#align function.periodic.const_smul Function.Periodic.const_smul

protected lemma Periodic.const_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  by_cases ha : a = 0
  · simp only [ha, zero_smul]
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)
#align function.periodic.const_smul₀ Function.Periodic.const_smul₀

protected lemma Periodic.const_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  Periodic.const_smul₀ h a
#align function.periodic.const_mul Function.Periodic.const_mul

lemma Periodic.const_inv_smul [AddMonoid α] [Group γ] [DistribMulAction γ α] (h : Periodic f c)
    (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹
#align function.periodic.const_inv_smul Function.Periodic.const_inv_smul

lemma Periodic.const_inv_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ a⁻¹
#align function.periodic.const_inv_smul₀ Function.Periodic.const_inv_smul₀

lemma Periodic.const_inv_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a
#align function.periodic.const_inv_mul Function.Periodic.const_inv_mul

lemma Periodic.mul_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ (MulOpposite.op a)
#align function.periodic.mul_const Function.Periodic.mul_const

lemma Periodic.mul_const' [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c / a) := by simpa only [div_eq_mul_inv] using h.mul_const a
#align function.periodic.mul_const' Function.Periodic.mul_const'

lemma Periodic.mul_const_inv [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ (MulOpposite.op a)
#align function.periodic.mul_const_inv Function.Periodic.mul_const_inv

lemma Periodic.div_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x / a)) (c * a) := by simpa only [div_eq_mul_inv] using h.mul_const_inv a
#align function.periodic.div_const Function.Periodic.div_const

lemma Periodic.add_period [AddSemigroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ + c₂) := by simp_all [← add_assoc]
#align function.periodic.add_period Function.Periodic.add_period

lemma Periodic.sub_eq [AddGroup α] (h : Periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [sub_add_cancel] using (h (x - c)).symm
#align function.periodic.sub_eq Function.Periodic.sub_eq

lemma Periodic.sub_eq' [AddCommGroup α] (h : Periodic f c) : f (c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)
#align function.periodic.sub_eq' Function.Periodic.sub_eq'

protected lemma Periodic.neg [AddGroup α] (h : Periodic f c) : Periodic f (-c) := by
  simpa only [sub_eq_add_neg, Periodic] using h.sub_eq
#align function.periodic.neg Function.Periodic.neg

lemma Periodic.sub_period [AddGroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ - c₂) := fun x => by
  rw [sub_eq_add_neg, ← add_assoc, h2.neg, h1]
#align function.periodic.sub_period Function.Periodic.sub_period

lemma Periodic.const_add [AddSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)
#align function.periodic.const_add Function.Periodic.const_add

lemma Periodic.add_const [AddCommSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)
#align function.periodic.add_const Function.Periodic.add_const

lemma Periodic.const_sub [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]
#align function.periodic.const_sub Function.Periodic.const_sub

lemma Periodic.sub_const [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)
#align function.periodic.sub_const Function.Periodic.sub_const

lemma Periodic.nsmul [AddMonoid α] (h : Periodic f c) (n : ℕ) : Periodic f (n • c) := by
  induction n <;> simp_all [Nat.succ_eq_add_one, add_nsmul, ← add_assoc, zero_nsmul]
#align function.periodic.nsmul Function.Periodic.nsmul

lemma Periodic.nat_mul [Semiring α] (h : Periodic f c) (n : ℕ) : Periodic f (n * c) := by
  simpa only [nsmul_eq_mul] using h.nsmul n
#align function.periodic.nat_mul Function.Periodic.nat_mul

lemma Periodic.neg_nsmul [AddGroup α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n • c)) :=
  (h.nsmul n).neg
#align function.periodic.neg_nsmul Function.Periodic.neg_nsmul

lemma Periodic.neg_nat_mul [Ring α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n * c)) :=
  (h.nat_mul n).neg
#align function.periodic.neg_nat_mul Function.Periodic.neg_nat_mul

lemma Periodic.sub_nsmul_eq [AddGroup α] (h : Periodic f c) (n : ℕ) : f (x - n • c) = f x := by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x
#align function.periodic.sub_nsmul_eq Function.Periodic.sub_nsmul_eq

lemma Periodic.sub_nat_mul_eq [Ring α] (h : Periodic f c) (n : ℕ) : f (x - n * c) = f x := by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n
#align function.periodic.sub_nat_mul_eq Function.Periodic.sub_nat_mul_eq

lemma Periodic.nsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : ℕ) :
    f (n • c - x) = f (-x) :=
  (h.nsmul n).sub_eq'
#align function.periodic.nsmul_sub_eq Function.Periodic.nsmul_sub_eq

lemma Periodic.nat_mul_sub_eq [Ring α] (h : Periodic f c) (n : ℕ) : f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)
#align function.periodic.nat_mul_sub_eq Function.Periodic.nat_mul_sub_eq

protected lemma Periodic.zsmul [AddGroup α] (h : Periodic f c) (n : ℤ) : Periodic f (n • c) := by
  cases' n with n n
  · simpa only [Int.ofNat_eq_coe, natCast_zsmul] using h.nsmul n
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg
#align function.periodic.zsmul Function.Periodic.zsmul

protected lemma Periodic.int_mul [Ring α] (h : Periodic f c) (n : ℤ) : Periodic f (n * c) := by
  simpa only [zsmul_eq_mul] using h.zsmul n
#align function.periodic.int_mul Function.Periodic.int_mul

lemma Periodic.sub_zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (x - n • c) = f x :=
  (h.zsmul n).sub_eq x
#align function.periodic.sub_zsmul_eq Function.Periodic.sub_zsmul_eq

lemma Periodic.sub_int_mul_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (x - n * c) = f x :=
  (h.int_mul n).sub_eq x
#align function.periodic.sub_int_mul_eq Function.Periodic.sub_int_mul_eq

lemma Periodic.zsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : ℤ) :
    f (n • c - x) = f (-x) :=
  (h.zsmul _).sub_eq'
#align function.periodic.zsmul_sub_eq Function.Periodic.zsmul_sub_eq

lemma Periodic.int_mul_sub_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (n * c - x) = f (-x) :=
  (h.int_mul _).sub_eq'
#align function.periodic.int_mul_sub_eq Function.Periodic.int_mul_sub_eq

protected lemma Periodic.eq [AddZeroClass α] (h : Periodic f c) : f c = f 0 := by
  simpa only [zero_add] using h 0
#align function.periodic.eq Function.Periodic.eq

protected lemma Periodic.neg_eq [AddGroup α] (h : Periodic f c) : f (-c) = f 0 :=
  h.neg.eq
#align function.periodic.neg_eq Function.Periodic.neg_eq

protected lemma Periodic.nsmul_eq [AddMonoid α] (h : Periodic f c) (n : ℕ) : f (n • c) = f 0 :=
  (h.nsmul n).eq
#align function.periodic.nsmul_eq Function.Periodic.nsmul_eq

lemma Periodic.nat_mul_eq [Semiring α] (h : Periodic f c) (n : ℕ) : f (n * c) = f 0 :=
  (h.nat_mul n).eq
#align function.periodic.nat_mul_eq Function.Periodic.nat_mul_eq

lemma Periodic.zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (n • c) = f 0 :=
  (h.zsmul n).eq
#align function.periodic.zsmul_eq Function.Periodic.zsmul_eq

lemma Periodic.int_mul_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (n * c) = f 0 :=
  (h.int_mul n).eq
#align function.periodic.int_mul_eq Function.Periodic.int_mul_eq

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico₀ [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x) : ∃ y ∈ Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩
#align function.periodic.exists_mem_Ico₀ Function.Periodic.exists_mem_Ico₀

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩
#align function.periodic.exists_mem_Ico Function.Periodic.exists_mem_Ico

/-- If a function `f` is `Periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩
#align function.periodic.exists_mem_Ioc Function.Periodic.exists_mem_Ioc

lemma Periodic.image_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Ioc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩
#align function.periodic.image_Ioc Function.Periodic.image_Ioc

lemma Periodic.image_Icc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Icc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| h.image_Ioc hc a ▸ image_subset _ Ioc_subset_Icc_self

lemma Periodic.image_uIcc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : c ≠ 0) (a : α) : f '' uIcc a (a + c) = range f := by
  cases hc.lt_or_lt with
  | inl hc =>
    rw [uIcc_of_ge (add_le_of_nonpos_right hc.le), ← h.neg.image_Icc (neg_pos.2 hc) (a + c),
      add_neg_cancel_right]
  | inr hc => rw [uIcc_of_le (le_add_of_nonneg_right hc.le), h.image_Icc hc]

lemma periodic_with_period_zero [AddZeroClass α] (f : α → β) : Periodic f 0 := fun x => by
  rw [add_zero]
#align function.periodic_with_period_zero Function.periodic_with_period_zero

lemma Periodic.map_vadd_zmultiples [AddCommGroup α] (hf : Periodic f c)
    (a : AddSubgroup.zmultiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubgroup.vadd_def, add_comm _ x, hf.zsmul m x]
#align function.periodic.map_vadd_zmultiples Function.Periodic.map_vadd_zmultiples

lemma Periodic.map_vadd_multiples [AddCommMonoid α] (hf : Periodic f c)
    (a : AddSubmonoid.multiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]
#align function.periodic.map_vadd_multiples Function.Periodic.map_vadd_multiples

/-- Lift a periodic function to a function from the quotient group. -/
def Periodic.lift [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    obtain ⟨k, hk⟩ := h'
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))
#align function.periodic.lift Function.Periodic.lift

@[simp]
lemma Periodic.lift_coe [AddGroup α] (h : Periodic f c) (a : α) :
    h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a :=
  rfl
#align function.periodic.lift_coe Function.Periodic.lift_coe

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
#align function.antiperiodic Function.Antiperiodic

protected lemma Antiperiodic.funext [Add α] [Neg β] (h : Antiperiodic f c) :
    (fun x => f (x + c)) = -f :=
  funext h
#align function.antiperiodic.funext Function.Antiperiodic.funext

protected lemma Antiperiodic.funext' [Add α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    (fun x => -f (x + c)) = f :=
  neg_eq_iff_eq_neg.mpr h.funext
#align function.antiperiodic.funext' Function.Antiperiodic.funext'

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` with period
`2 • c`. -/
protected theorem Antiperiodic.periodic [AddMonoid α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 • c) := by simp [two_nsmul, ← add_assoc, h _]

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `Periodic` with period
  `2 * c`. -/
protected theorem Antiperiodic.periodic_two_mul [Semiring α] [InvolutiveNeg β]
    (h : Antiperiodic f c) : Periodic f (2 * c) := nsmul_eq_mul 2 c ▸ h.periodic
#align function.antiperiodic.periodic Function.Antiperiodic.periodic_two_mul

protected lemma Antiperiodic.eq [AddZeroClass α] [Neg β] (h : Antiperiodic f c) : f c = -f 0 := by
  simpa only [zero_add] using h 0
#align function.antiperiodic.eq Function.Antiperiodic.eq

lemma Antiperiodic.even_nsmul_periodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Periodic f ((2 * n) • c) := mul_nsmul c 2 n ▸ h.periodic.nsmul n

lemma Antiperiodic.nat_even_mul_periodic [Semiring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.nat_mul n
#align function.antiperiodic.nat_even_mul_periodic Function.Antiperiodic.nat_even_mul_periodic

lemma Antiperiodic.odd_nsmul_antiperiodic [AddMonoid α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Antiperiodic f ((2 * n + 1) • c) := fun x => by
  rw [add_nsmul, one_nsmul, ← add_assoc, h, h.even_nsmul_periodic]

lemma Antiperiodic.nat_odd_mul_antiperiodic [Semiring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.nat_even_mul_periodic]
#align function.antiperiodic.nat_odd_mul_antiperiodic Function.Antiperiodic.nat_odd_mul_antiperiodic

lemma Antiperiodic.even_zsmul_periodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Periodic f ((2 * n) • c) := by
  rw [mul_comm, mul_zsmul, two_zsmul, ← two_nsmul]
  exact h.periodic.zsmul n

lemma Antiperiodic.int_even_mul_periodic [Ring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Periodic f (n * (2 * c)) :=
  h.periodic_two_mul.int_mul n
#align function.antiperiodic.int_even_mul_periodic Function.Antiperiodic.int_even_mul_periodic

lemma Antiperiodic.odd_zsmul_antiperiodic [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Antiperiodic f ((2 * n + 1) • c) := by
  intro x
  rw [add_zsmul, one_zsmul, ← add_assoc, h, h.even_zsmul_periodic]

lemma Antiperiodic.int_odd_mul_antiperiodic [Ring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.int_even_mul_periodic]
#align function.antiperiodic.int_odd_mul_antiperiodic Function.Antiperiodic.int_odd_mul_antiperiodic

lemma Antiperiodic.sub_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (x : α) :
    f (x - c) = -f x := by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]
#align function.antiperiodic.sub_eq Function.Antiperiodic.sub_eq

lemma Antiperiodic.sub_eq' [AddCommGroup α] [Neg β] (h : Antiperiodic f c) :
    f (c - x) = -f (-x) := by simpa only [sub_eq_neg_add] using h (-x)
#align function.antiperiodic.sub_eq' Function.Antiperiodic.sub_eq'

protected lemma Antiperiodic.neg [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    Antiperiodic f (-c) := by simpa only [sub_eq_add_neg, Antiperiodic] using h.sub_eq
#align function.antiperiodic.neg Function.Antiperiodic.neg

lemma Antiperiodic.neg_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    f (-c) = -f 0 := by
  simpa only [zero_add] using h.neg 0
#align function.antiperiodic.neg_eq Function.Antiperiodic.neg_eq

lemma Antiperiodic.nat_mul_eq_of_eq_zero [Semiring α] [NegZeroClass β] (h : Antiperiodic f c)
    (hi : f 0 = 0) : ∀ n : ℕ, f (n * c) = 0
  | 0 => by rwa [Nat.cast_zero, zero_mul]
  | n + 1 => by simp [add_mul, h _, Antiperiodic.nat_mul_eq_of_eq_zero h hi n]
#align function.antiperiodic.nat_mul_eq_of_eq_zero Function.Antiperiodic.nat_mul_eq_of_eq_zero

lemma Antiperiodic.int_mul_eq_of_eq_zero [Ring α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (hi : f 0 = 0) : ∀ n : ℤ, f (n * c) = 0
  | (n : ℕ) => by rw [Int.cast_natCast, h.nat_mul_eq_of_eq_zero hi n]
  | .negSucc n => by rw [Int.cast_negSucc, neg_mul, ← mul_neg, h.neg.nat_mul_eq_of_eq_zero hi]
#align function.antiperiodic.int_mul_eq_of_eq_zero Function.Antiperiodic.int_mul_eq_of_eq_zero

lemma Antiperiodic.add_zsmul_eq [AddGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℤ) :
    f (x + n • c) = (n.negOnePow : ℤ) • f x := by
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_zsmul_periodic, Int.negOnePow_two_mul, Units.val_one, one_zsmul]
  · rw [h.odd_zsmul_antiperiodic, Int.negOnePow_two_mul_add_one, Units.val_neg,
      Units.val_one, neg_zsmul, one_zsmul]

lemma Antiperiodic.sub_zsmul_eq [AddGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℤ) :
    f (x - n • c) = (n.negOnePow : ℤ) • f x := by
  simpa only [sub_eq_add_neg, neg_zsmul, Int.negOnePow_neg] using h.add_zsmul_eq (-n)

lemma Antiperiodic.zsmul_sub_eq [AddCommGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℤ) :
    f (n • c - x) = (n.negOnePow : ℤ) • f (-x) := by
  rw [sub_eq_add_neg, add_comm]
  exact h.add_zsmul_eq n

lemma Antiperiodic.add_int_mul_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℤ) :
    f (x + n * c) = (n.negOnePow : ℤ) * f x := by simpa only [zsmul_eq_mul] using h.add_zsmul_eq n

lemma Antiperiodic.sub_int_mul_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℤ) :
    f (x - n * c) = (n.negOnePow : ℤ) * f x := by simpa only [zsmul_eq_mul] using h.sub_zsmul_eq n

lemma Antiperiodic.int_mul_sub_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℤ) :
    f (n * c - x) = (n.negOnePow : ℤ) * f (-x) := by
  simpa only [zsmul_eq_mul] using h.zsmul_sub_eq n

lemma Antiperiodic.add_nsmul_eq [AddMonoid α] [AddGroup β] (h : Antiperiodic f c) (n : ℕ) :
    f (x + n • c) = (-1) ^ n • f x := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [h.even_nsmul_periodic, pow_mul, (by norm_num : (-1) ^ 2 = 1), one_pow, one_zsmul]
  · rw [h.odd_nsmul_antiperiodic, pow_add, pow_mul, (by norm_num : (-1) ^ 2 = 1), one_pow,
      pow_one, one_mul, neg_zsmul, one_zsmul]

lemma Antiperiodic.sub_nsmul_eq [AddGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℕ) :
    f (x - n • c) = (-1) ^ n • f x := by
  simpa only [Int.reduceNeg, natCast_zsmul] using h.sub_zsmul_eq n

lemma Antiperiodic.nsmul_sub_eq [AddCommGroup α] [AddGroup β] (h : Antiperiodic f c) (n : ℕ) :
    f (n • c - x) = (-1) ^ n • f (-x) := by
  simpa only [Int.reduceNeg, natCast_zsmul] using h.zsmul_sub_eq n

lemma Antiperiodic.add_nat_mul_eq [Semiring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x + n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.add_nsmul_eq n

lemma Antiperiodic.sub_nat_mul_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (x - n * c) = (-1) ^ n * f x := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.sub_nsmul_eq n

lemma Antiperiodic.nat_mul_sub_eq [Ring α] [Ring β] (h : Antiperiodic f c) (n : ℕ) :
    f (n * c - x) = (-1) ^ n * f (-x) := by
  simpa only [nsmul_eq_mul, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one] using h.nsmul_sub_eq n

lemma Antiperiodic.const_add [AddSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)
#align function.antiperiodic.const_add Function.Antiperiodic.const_add

lemma Antiperiodic.add_const [AddCommSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)
#align function.antiperiodic.add_const Function.Antiperiodic.add_const

lemma Antiperiodic.const_sub [AddCommGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]
#align function.antiperiodic.const_sub Function.Antiperiodic.const_sub

lemma Antiperiodic.sub_const [AddCommGroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)
#align function.antiperiodic.sub_const Function.Antiperiodic.sub_const

lemma Antiperiodic.smul [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (a • f) c := by simp_all
#align function.antiperiodic.smul Function.Antiperiodic.smul

lemma Antiperiodic.const_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)
#align function.antiperiodic.const_smul Function.Antiperiodic.const_smul

lemma Antiperiodic.const_smul₀ [AddCommMonoid α] [Neg β] [DivisionSemiring γ] [Module γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) :=
  fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)
#align function.antiperiodic.const_smul₀ Function.Antiperiodic.const_smul₀

lemma Antiperiodic.const_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ ha
#align function.antiperiodic.const_mul Function.Antiperiodic.const_mul

lemma Antiperiodic.const_inv_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹
#align function.antiperiodic.const_inv_smul Function.Antiperiodic.const_inv_smul

lemma Antiperiodic.const_inv_smul₀ [AddCommMonoid α] [Neg β] [DivisionSemiring γ] [Module γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)
#align function.antiperiodic.const_inv_smul₀ Function.Antiperiodic.const_inv_smul₀

lemma Antiperiodic.const_inv_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ ha
#align function.antiperiodic.const_inv_mul Function.Antiperiodic.const_inv_mul

lemma Antiperiodic.mul_const [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha
#align function.antiperiodic.mul_const Function.Antiperiodic.mul_const

lemma Antiperiodic.mul_const' [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c / a) := by
  simpa only [div_eq_mul_inv] using h.mul_const ha
#align function.antiperiodic.mul_const' Function.Antiperiodic.mul_const'

lemma Antiperiodic.mul_const_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha
#align function.antiperiodic.mul_const_inv Function.Antiperiodic.mul_const_inv

lemma Antiperiodic.div_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha
#align function.antiperiodic.div_inv Function.Antiperiodic.div_inv

lemma Antiperiodic.add [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ + c₂) := by simp_all [← add_assoc]
#align function.antiperiodic.add Function.Antiperiodic.add

lemma Antiperiodic.sub [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add h2.neg
#align function.antiperiodic.sub Function.Antiperiodic.sub

lemma Periodic.add_antiperiod [AddGroup α] [Neg β] (h1 : Periodic f c₁) (h2 : Antiperiodic f c₂) :
    Antiperiodic f (c₁ + c₂) := by simp_all [← add_assoc]
#align function.periodic.add_antiperiod Function.Periodic.add_antiperiod

lemma Periodic.sub_antiperiod [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : Antiperiodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg
#align function.periodic.sub_antiperiod Function.Periodic.sub_antiperiod

lemma Periodic.add_antiperiod_eq [AddGroup α] [Neg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ + c₂) = -f 0 :=
  (h1.add_antiperiod h2).eq
#align function.periodic.add_antiperiod_eq Function.Periodic.add_antiperiod_eq

lemma Periodic.sub_antiperiod_eq [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ - c₂) = -f 0 :=
  (h1.sub_antiperiod h2).eq
#align function.periodic.sub_antiperiod_eq Function.Periodic.sub_antiperiod_eq

lemma Antiperiodic.mul [Add α] [Mul β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f * g) c := by simp_all
#align function.antiperiodic.mul Function.Antiperiodic.mul

lemma Antiperiodic.div [Add α] [DivisionMonoid β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f / g) c := by simp_all [neg_div_neg_eq]
#align function.antiperiodic.div Function.Antiperiodic.div

end Function

lemma Int.fract_periodic (α) [LinearOrderedRing α] [FloorRing α] :
    Function.Periodic Int.fract (1 : α) := fun a => mod_cast Int.fract_add_int a 1
#align int.fract_periodic Int.fract_periodic
