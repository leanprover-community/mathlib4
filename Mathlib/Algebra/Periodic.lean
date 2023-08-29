/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Field.Opposite
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.Archimedean
import Mathlib.Data.Int.Parity
import Mathlib.GroupTheory.Coset
import Mathlib.GroupTheory.Subgroup.ZPowers
import Mathlib.GroupTheory.Submonoid.Membership

#align_import algebra.periodic from "leanprover-community/mathlib"@"30413fc89f202a090a54d78e540963ed3de0056e"

/-!
# Periodicity

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `Function.Periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `Function.Antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2*c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/


variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

open Set BigOperators

namespace Function

/-! ### Periodicity -/


/-- A function `f` is said to be `periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp]
def Periodic [Add α] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = f x
#align function.periodic Function.Periodic

protected theorem Periodic.funext [Add α] (h : Periodic f c) : (fun x => f (x + c)) = f :=
  funext h
#align function.periodic.funext Function.Periodic.funext

protected theorem Periodic.comp [Add α] (h : Periodic f c) (g : β → γ) : Periodic (g ∘ f) c := by
  simp_all
  -- 🎉 no goals
#align function.periodic.comp Function.Periodic.comp

theorem Periodic.comp_addHom [Add α] [Add γ] (h : Periodic f c) (g : AddHom γ α) (g_inv : α → γ)
    (hg : RightInverse g_inv g) : Periodic (f ∘ g) (g_inv c) := fun x => by
  simp only [hg c, h (g x), map_add, comp_apply]
  -- 🎉 no goals
#align function.periodic.comp_add_hom Function.Periodic.comp_addHom

@[to_additive]
protected theorem Periodic.mul [Add α] [Mul β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f * g) c := by simp_all
                             -- 🎉 no goals
#align function.periodic.mul Function.Periodic.mul
#align function.periodic.add Function.Periodic.add

@[to_additive]
protected theorem Periodic.div [Add α] [Div β] (hf : Periodic f c) (hg : Periodic g c) :
    Periodic (f / g) c := by simp_all
                             -- 🎉 no goals
#align function.periodic.div Function.Periodic.div
#align function.periodic.sub Function.Periodic.sub

@[to_additive]
theorem _root_.List.periodic_prod [Add α] [Monoid β] (l : List (α → β))
    (hl : ∀ f ∈ l, Periodic f c) : Periodic l.prod c := by
  induction' l with g l ih hl
  -- ⊢ Periodic (List.prod []) c
  · simp
    -- 🎉 no goals
  · rw [List.forall_mem_cons] at hl
    -- ⊢ Periodic (List.prod (g :: l)) c
    simpa only [List.prod_cons] using hl.1.mul (ih hl.2)
    -- 🎉 no goals
#align list.periodic_prod List.periodic_prod
#align list.periodic_sum List.periodic_sum

@[to_additive]
theorem _root_.Multiset.periodic_prod [Add α] [CommMonoid β] (s : Multiset (α → β))
    (hs : ∀ f ∈ s, Periodic f c) : Periodic s.prod c :=
  (s.prod_toList ▸ s.toList.periodic_prod) fun f hf => hs f <| Multiset.mem_toList.mp hf
#align multiset.periodic_prod Multiset.periodic_prod
#align multiset.periodic_sum Multiset.periodic_sum

@[to_additive]
theorem _root_.Finset.periodic_prod [Add α] [CommMonoid β] {ι : Type*} {f : ι → α → β}
    (s : Finset ι) (hs : ∀ i ∈ s, Periodic (f i) c) : Periodic (∏ i in s, f i) c :=
  s.prod_to_list f ▸ (s.toList.map f).periodic_prod (by simpa [-Periodic] )
                                                        -- 🎉 no goals
#align finset.periodic_prod Finset.periodic_prod
#align finset.periodic_sum Finset.periodic_sum

@[to_additive]
protected theorem Periodic.smul [Add α] [SMul γ β] (h : Periodic f c) (a : γ) :
    Periodic (a • f) c := by simp_all
                             -- 🎉 no goals
#align function.periodic.smul Function.Periodic.smul
#align function.periodic.vadd Function.Periodic.vadd

protected theorem Periodic.const_smul [AddMonoid α] [Group γ] [DistribMulAction γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)
  -- 🎉 no goals
#align function.periodic.const_smul Function.Periodic.const_smul

protected theorem Periodic.const_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  by_cases ha : a = 0
  -- ⊢ (fun x => f (a • x)) (x + a⁻¹ • c) = (fun x => f (a • x)) x
  · simp only [ha, zero_smul]
    -- 🎉 no goals
  · simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)
    -- 🎉 no goals
#align function.periodic.const_smul₀ Function.Periodic.const_smul₀

protected theorem Periodic.const_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a * x)) (a⁻¹ * c) :=
  Periodic.const_smul₀ h a
#align function.periodic.const_mul Function.Periodic.const_mul

theorem Periodic.const_inv_smul [AddMonoid α] [Group γ] [DistribMulAction γ α] (h : Periodic f c)
    (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹
  -- 🎉 no goals
#align function.periodic.const_inv_smul Function.Periodic.const_inv_smul

theorem Periodic.const_inv_smul₀ [AddCommMonoid α] [DivisionSemiring γ] [Module γ α]
    (h : Periodic f c) (a : γ) : Periodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ a⁻¹
  -- 🎉 no goals
#align function.periodic.const_inv_smul₀ Function.Periodic.const_inv_smul₀

theorem Periodic.const_inv_mul [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ a
#align function.periodic.const_inv_mul Function.Periodic.const_inv_mul

theorem Periodic.mul_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ (MulOpposite.op a)
#align function.periodic.mul_const Function.Periodic.mul_const

theorem Periodic.mul_const' [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a)) (c / a) := by simpa only [div_eq_mul_inv] using h.mul_const a
                                                -- 🎉 no goals
#align function.periodic.mul_const' Function.Periodic.mul_const'

theorem Periodic.mul_const_inv [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ (MulOpposite.op a)
#align function.periodic.mul_const_inv Function.Periodic.mul_const_inv

theorem Periodic.div_const [DivisionSemiring α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x / a)) (c * a) := by simpa only [div_eq_mul_inv] using h.mul_const_inv a
                                                -- 🎉 no goals
#align function.periodic.div_const Function.Periodic.div_const

theorem Periodic.add_period [AddSemigroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ + c₂) := by simp_all [← add_assoc]
                               -- 🎉 no goals
#align function.periodic.add_period Function.Periodic.add_period

theorem Periodic.sub_eq [AddGroup α] (h : Periodic f c) (x : α) : f (x - c) = f x := by
  simpa only [sub_add_cancel] using (h (x - c)).symm
  -- 🎉 no goals
#align function.periodic.sub_eq Function.Periodic.sub_eq

theorem Periodic.sub_eq' [AddCommGroup α] (h : Periodic f c) : f (c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h (-x)
  -- 🎉 no goals
#align function.periodic.sub_eq' Function.Periodic.sub_eq'

protected theorem Periodic.neg [AddGroup α] (h : Periodic f c) : Periodic f (-c) := by
  simpa only [sub_eq_add_neg, Periodic] using h.sub_eq
  -- 🎉 no goals
#align function.periodic.neg Function.Periodic.neg

theorem Periodic.sub_period [AddGroup α] (h1 : Periodic f c₁) (h2 : Periodic f c₂) :
    Periodic f (c₁ - c₂) := fun x => by
  rw [sub_eq_add_neg, ← add_assoc, h2.neg, h1]
  -- 🎉 no goals
#align function.periodic.sub_period Function.Periodic.sub_period

theorem Periodic.const_add [AddSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)
                                                   -- 🎉 no goals
#align function.periodic.const_add Function.Periodic.const_add

theorem Periodic.add_const [AddCommSemigroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)
  -- 🎉 no goals
#align function.periodic.add_const Function.Periodic.add_const

theorem Periodic.const_sub [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]
  -- 🎉 no goals
#align function.periodic.const_sub Function.Periodic.const_sub

theorem Periodic.sub_const [AddCommGroup α] (h : Periodic f c) (a : α) :
    Periodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)
  -- 🎉 no goals
#align function.periodic.sub_const Function.Periodic.sub_const

theorem Periodic.nsmul [AddMonoid α] (h : Periodic f c) (n : ℕ) : Periodic f (n • c) := by
  induction n <;> simp_all [Nat.succ_eq_add_one, add_nsmul, ← add_assoc, zero_nsmul]
  -- ⊢ Periodic f (Nat.zero • c)
                  -- 🎉 no goals
                  -- 🎉 no goals
#align function.periodic.nsmul Function.Periodic.nsmul

theorem Periodic.nat_mul [Semiring α] (h : Periodic f c) (n : ℕ) : Periodic f (n * c) := by
  simpa only [nsmul_eq_mul] using h.nsmul n
  -- 🎉 no goals
#align function.periodic.nat_mul Function.Periodic.nat_mul

theorem Periodic.neg_nsmul [AddGroup α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n • c)) :=
  (h.nsmul n).neg
#align function.periodic.neg_nsmul Function.Periodic.neg_nsmul

theorem Periodic.neg_nat_mul [Ring α] (h : Periodic f c) (n : ℕ) : Periodic f (-(n * c)) :=
  (h.nat_mul n).neg
#align function.periodic.neg_nat_mul Function.Periodic.neg_nat_mul

theorem Periodic.sub_nsmul_eq [AddGroup α] (h : Periodic f c) (n : ℕ) : f (x - n • c) = f x := by
  simpa only [sub_eq_add_neg] using h.neg_nsmul n x
  -- 🎉 no goals
#align function.periodic.sub_nsmul_eq Function.Periodic.sub_nsmul_eq

theorem Periodic.sub_nat_mul_eq [Ring α] (h : Periodic f c) (n : ℕ) : f (x - n * c) = f x := by
  simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n
  -- 🎉 no goals
#align function.periodic.sub_nat_mul_eq Function.Periodic.sub_nat_mul_eq

theorem Periodic.nsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : ℕ) :
    f (n • c - x) = f (-x) :=
  (h.nsmul n).sub_eq'
#align function.periodic.nsmul_sub_eq Function.Periodic.nsmul_sub_eq

theorem Periodic.nat_mul_sub_eq [Ring α] (h : Periodic f c) (n : ℕ) : f (n * c - x) = f (-x) := by
  simpa only [sub_eq_neg_add] using h.nat_mul n (-x)
  -- 🎉 no goals
#align function.periodic.nat_mul_sub_eq Function.Periodic.nat_mul_sub_eq

protected theorem Periodic.zsmul [AddGroup α] (h : Periodic f c) (n : ℤ) : Periodic f (n • c) := by
  cases' n with n n
  -- ⊢ Periodic f (Int.ofNat n • c)
  · simpa only [Int.ofNat_eq_coe, coe_nat_zsmul] using h.nsmul n
    -- 🎉 no goals
  · simpa only [negSucc_zsmul] using (h.nsmul (n + 1)).neg
    -- 🎉 no goals
#align function.periodic.zsmul Function.Periodic.zsmul

protected theorem Periodic.int_mul [Ring α] (h : Periodic f c) (n : ℤ) : Periodic f (n * c) := by
  simpa only [zsmul_eq_mul] using h.zsmul n
  -- 🎉 no goals
#align function.periodic.int_mul Function.Periodic.int_mul

theorem Periodic.sub_zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (x - n • c) = f x :=
  (h.zsmul n).sub_eq x
#align function.periodic.sub_zsmul_eq Function.Periodic.sub_zsmul_eq

theorem Periodic.sub_int_mul_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (x - n * c) = f x :=
  (h.int_mul n).sub_eq x
#align function.periodic.sub_int_mul_eq Function.Periodic.sub_int_mul_eq

theorem Periodic.zsmul_sub_eq [AddCommGroup α] (h : Periodic f c) (n : ℤ) :
    f (n • c - x) = f (-x) :=
  (h.zsmul _).sub_eq'
#align function.periodic.zsmul_sub_eq Function.Periodic.zsmul_sub_eq

theorem Periodic.int_mul_sub_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (n * c - x) = f (-x) :=
  (h.int_mul _).sub_eq'
#align function.periodic.int_mul_sub_eq Function.Periodic.int_mul_sub_eq

protected theorem Periodic.eq [AddZeroClass α] (h : Periodic f c) : f c = f 0 := by
  simpa only [zero_add] using h 0
  -- 🎉 no goals
#align function.periodic.eq Function.Periodic.eq

protected theorem Periodic.neg_eq [AddGroup α] (h : Periodic f c) : f (-c) = f 0 :=
  h.neg.eq
#align function.periodic.neg_eq Function.Periodic.neg_eq

protected theorem Periodic.nsmul_eq [AddMonoid α] (h : Periodic f c) (n : ℕ) : f (n • c) = f 0 :=
  (h.nsmul n).eq
#align function.periodic.nsmul_eq Function.Periodic.nsmul_eq

theorem Periodic.nat_mul_eq [Semiring α] (h : Periodic f c) (n : ℕ) : f (n * c) = f 0 :=
  (h.nat_mul n).eq
#align function.periodic.nat_mul_eq Function.Periodic.nat_mul_eq

theorem Periodic.zsmul_eq [AddGroup α] (h : Periodic f c) (n : ℤ) : f (n • c) = f 0 :=
  (h.zsmul n).eq
#align function.periodic.zsmul_eq Function.Periodic.zsmul_eq

theorem Periodic.int_mul_eq [Ring α] (h : Periodic f c) (n : ℤ) : f (n * c) = f 0 :=
  (h.int_mul n).eq
#align function.periodic.int_mul_eq Function.Periodic.int_mul_eq

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico₀ [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x) : ∃ y ∈ Ico 0 c, f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_zsmul_near_of_pos' hc x
  ⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩
#align function.periodic.exists_mem_Ico₀ Function.Periodic.exists_mem_Ico₀

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ico [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ico a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ico hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩
#align function.periodic.exists_mem_Ico Function.Periodic.exists_mem_Ico

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
theorem Periodic.exists_mem_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (x a) : ∃ y ∈ Ioc a (a + c), f x = f y :=
  let ⟨n, H, _⟩ := existsUnique_add_zsmul_mem_Ioc hc x a
  ⟨x + n • c, H, (h.zsmul n x).symm⟩
#align function.periodic.exists_mem_Ioc Function.Periodic.exists_mem_Ioc

theorem Periodic.image_Ioc [LinearOrderedAddCommGroup α] [Archimedean α] (h : Periodic f c)
    (hc : 0 < c) (a : α) : f '' Ioc a (a + c) = range f :=
  (image_subset_range _ _).antisymm <| range_subset_iff.2 fun x =>
    let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a
    ⟨y, hy, hyx.symm⟩
#align function.periodic.image_Ioc Function.Periodic.image_Ioc

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
  -- 🎉 no goals
#align function.periodic_with_period_zero Function.periodic_with_period_zero

theorem Periodic.map_vadd_zmultiples [AddCommGroup α] (hf : Periodic f c)
    (a : AddSubgroup.zmultiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  -- ⊢ f ({ val := (fun x => x • c) m, property := (_ : ∃ y, (fun x => x • c) y = ( …
  simp [AddSubgroup.vadd_def, add_comm _ x, hf.zsmul m x]
  -- 🎉 no goals
#align function.periodic.map_vadd_zmultiples Function.Periodic.map_vadd_zmultiples

theorem Periodic.map_vadd_multiples [AddCommMonoid α] (hf : Periodic f c)
    (a : AddSubmonoid.multiples c) (x : α) : f (a +ᵥ x) = f x := by
  rcases a with ⟨_, m, rfl⟩
  -- ⊢ f ({ val := (fun i => i • c) m, property := (_ : ∃ y, (fun i => i • c) y = ( …
  simp [AddSubmonoid.vadd_def, add_comm _ x, hf.nsmul m x]
  -- 🎉 no goals
#align function.periodic.map_vadd_multiples Function.Periodic.map_vadd_multiples

/-- Lift a periodic function to a function from the quotient group. -/
def Periodic.lift [AddGroup α] (h : Periodic f c) (x : α ⧸ AddSubgroup.zmultiples c) : β :=
  Quotient.liftOn' x f fun a b h' => by
    rw [QuotientAddGroup.leftRel_apply] at h'
    -- ⊢ f a = f b
    obtain ⟨k, hk⟩ := h'
    -- ⊢ f a = f b
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk))
    -- 🎉 no goals
#align function.periodic.lift Function.Periodic.lift

@[simp]
theorem Periodic.lift_coe [AddGroup α] (h : Periodic f c) (a : α) :
    h.lift (a : α ⧸ AddSubgroup.zmultiples c) = f a :=
  rfl
#align function.periodic.lift_coe Function.Periodic.lift_coe

/-! ### Antiperiodicity -/

/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp]
def Antiperiodic [Add α] [Neg β] (f : α → β) (c : α) : Prop :=
  ∀ x : α, f (x + c) = -f x
#align function.antiperiodic Function.Antiperiodic

protected theorem Antiperiodic.funext [Add α] [Neg β] (h : Antiperiodic f c) :
    (fun x => f (x + c)) = -f :=
  funext h
#align function.antiperiodic.funext Function.Antiperiodic.funext

protected theorem Antiperiodic.funext' [Add α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    (fun x => -f (x + c)) = f :=
  neg_eq_iff_eq_neg.mpr h.funext
#align function.antiperiodic.funext' Function.Antiperiodic.funext'

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `periodic` with period
  `2 * c`. -/
protected theorem Antiperiodic.periodic [Semiring α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    Periodic f (2 * c) := by simp [two_mul, ← add_assoc, h _]
                             -- 🎉 no goals
#align function.antiperiodic.periodic Function.Antiperiodic.periodic

protected theorem Antiperiodic.eq [AddZeroClass α] [Neg β] (h : Antiperiodic f c) : f c = -f 0 := by
  simpa only [zero_add] using h 0
  -- 🎉 no goals
#align function.antiperiodic.eq Function.Antiperiodic.eq

theorem Antiperiodic.nat_even_mul_periodic [Semiring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Periodic f (n * (2 * c)) :=
  h.periodic.nat_mul n
#align function.antiperiodic.nat_even_mul_periodic Function.Antiperiodic.nat_even_mul_periodic

theorem Antiperiodic.nat_odd_mul_antiperiodic [Semiring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℕ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.periodic.nat_mul]
  -- 🎉 no goals
#align function.antiperiodic.nat_odd_mul_antiperiodic Function.Antiperiodic.nat_odd_mul_antiperiodic

theorem Antiperiodic.int_even_mul_periodic [Ring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Periodic f (n * (2 * c)) :=
  h.periodic.int_mul n
#align function.antiperiodic.int_even_mul_periodic Function.Antiperiodic.int_even_mul_periodic

theorem Antiperiodic.int_odd_mul_antiperiodic [Ring α] [InvolutiveNeg β] (h : Antiperiodic f c)
    (n : ℤ) : Antiperiodic f (n * (2 * c) + c) := fun x => by
  rw [← add_assoc, h, h.periodic.int_mul]
  -- 🎉 no goals
#align function.antiperiodic.int_odd_mul_antiperiodic Function.Antiperiodic.int_odd_mul_antiperiodic

theorem Antiperiodic.sub_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (x : α) :
    f (x - c) = -f x := by simp only [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]
                           -- 🎉 no goals
#align function.antiperiodic.sub_eq Function.Antiperiodic.sub_eq

theorem Antiperiodic.sub_eq' [AddCommGroup α] [Neg β] (h : Antiperiodic f c) :
    f (c - x) = -f (-x) := by simpa only [sub_eq_neg_add] using h (-x)
                              -- 🎉 no goals
#align function.antiperiodic.sub_eq' Function.Antiperiodic.sub_eq'

protected theorem Antiperiodic.neg [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) :
    Antiperiodic f (-c) := by simpa only [sub_eq_add_neg, Antiperiodic] using h.sub_eq
                              -- 🎉 no goals
#align function.antiperiodic.neg Function.Antiperiodic.neg

theorem Antiperiodic.neg_eq [AddGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) : f (-c) = -f 0 :=
  by simpa only [zero_add] using h.neg 0
     -- 🎉 no goals
#align function.antiperiodic.neg_eq Function.Antiperiodic.neg_eq

theorem Antiperiodic.nat_mul_eq_of_eq_zero [Semiring α] [NegZeroClass β] (h : Antiperiodic f c)
    (hi : f 0 = 0) : ∀ n : ℕ, f (n * c) = 0
  | 0 => by rwa [Nat.cast_zero, zero_mul]
            -- 🎉 no goals
  | n + 1 => by simp [add_mul, h _, Antiperiodic.nat_mul_eq_of_eq_zero h hi n]
                -- 🎉 no goals
#align function.antiperiodic.nat_mul_eq_of_eq_zero Function.Antiperiodic.nat_mul_eq_of_eq_zero

theorem Antiperiodic.int_mul_eq_of_eq_zero [Ring α] [SubtractionMonoid β] (h : Antiperiodic f c)
    (hi : f 0 = 0) : ∀ n : ℤ, f (n * c) = 0
  | (n : ℕ) => by rw [Int.cast_ofNat, h.nat_mul_eq_of_eq_zero hi n]
                  -- 🎉 no goals
  | .negSucc n => by rw [Int.cast_negSucc, neg_mul, ← mul_neg, h.neg.nat_mul_eq_of_eq_zero hi]
                     -- 🎉 no goals
#align function.antiperiodic.int_mul_eq_of_eq_zero Function.Antiperiodic.int_mul_eq_of_eq_zero

theorem Antiperiodic.const_add [AddSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a + x)) c := fun x => by simpa [add_assoc] using h (a + x)
                                                       -- 🎉 no goals
#align function.antiperiodic.const_add Function.Antiperiodic.const_add

theorem Antiperiodic.add_const [AddCommSemigroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x + a)) c := fun x => by
  simpa only [add_right_comm] using h (x + a)
  -- 🎉 no goals
#align function.antiperiodic.add_const Function.Antiperiodic.add_const

theorem Antiperiodic.const_sub [AddCommGroup α] [InvolutiveNeg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (a - x)) c := fun x => by
  simp only [← sub_sub, h.sub_eq]
  -- 🎉 no goals
#align function.antiperiodic.const_sub Function.Antiperiodic.const_sub

theorem Antiperiodic.sub_const [AddCommGroup α] [Neg β] (h : Antiperiodic f c) (a : α) :
    Antiperiodic (fun x => f (x - a)) c := by
  simpa only [sub_eq_add_neg] using h.add_const (-a)
  -- 🎉 no goals
#align function.antiperiodic.sub_const Function.Antiperiodic.sub_const

theorem Antiperiodic.smul [Add α] [Monoid γ] [AddGroup β] [DistribMulAction γ β]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (a • f) c := by simp_all
                                                                  -- 🎉 no goals
#align function.antiperiodic.smul Function.Antiperiodic.smul

theorem Antiperiodic.const_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) := fun x => by
  simpa only [smul_add, smul_inv_smul] using h (a • x)
  -- 🎉 no goals
#align function.antiperiodic.const_smul Function.Antiperiodic.const_smul

theorem Antiperiodic.const_smul₀ [AddCommMonoid α] [Neg β] [DivisionSemiring γ] [Module γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a • x)) (a⁻¹ • c) :=
  fun x => by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)
              -- 🎉 no goals
#align function.antiperiodic.const_smul₀ Function.Antiperiodic.const_smul₀

theorem Antiperiodic.const_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a * x)) (a⁻¹ * c) :=
  h.const_smul₀ ha
#align function.antiperiodic.const_mul Function.Antiperiodic.const_mul

theorem Antiperiodic.const_inv_smul [AddMonoid α] [Neg β] [Group γ] [DistribMulAction γ α]
    (h : Antiperiodic f c) (a : γ) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul a⁻¹
  -- 🎉 no goals
#align function.antiperiodic.const_inv_smul Function.Antiperiodic.const_inv_smul

theorem Antiperiodic.const_inv_smul₀ [AddCommMonoid α] [Neg β] [DivisionSemiring γ] [Module γ α]
    (h : Antiperiodic f c) {a : γ} (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ • x)) (a • c) := by
  simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)
  -- 🎉 no goals
#align function.antiperiodic.const_inv_smul₀ Function.Antiperiodic.const_inv_smul₀

theorem Antiperiodic.const_inv_mul [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (a⁻¹ * x)) (a * c) :=
  h.const_inv_smul₀ ha
#align function.antiperiodic.const_inv_mul Function.Antiperiodic.const_inv_mul

theorem Antiperiodic.mul_const [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c * a⁻¹) :=
  h.const_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha
#align function.antiperiodic.mul_const Function.Antiperiodic.mul_const

theorem Antiperiodic.mul_const' [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a)) (c / a) := by
  simpa only [div_eq_mul_inv] using h.mul_const ha
  -- 🎉 no goals
#align function.antiperiodic.mul_const' Function.Antiperiodic.mul_const'

theorem Antiperiodic.mul_const_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x * a⁻¹)) (c * a) :=
  h.const_inv_smul₀ <| (MulOpposite.op_ne_zero_iff a).mpr ha
#align function.antiperiodic.mul_const_inv Function.Antiperiodic.mul_const_inv

theorem Antiperiodic.div_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha
  -- 🎉 no goals
#align function.antiperiodic.div_inv Function.Antiperiodic.div_inv

theorem Antiperiodic.add [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ + c₂) := by simp_all [← add_assoc]
                                                          -- 🎉 no goals
#align function.antiperiodic.add Function.Antiperiodic.add

theorem Antiperiodic.sub [AddGroup α] [InvolutiveNeg β] (h1 : Antiperiodic f c₁)
    (h2 : Antiperiodic f c₂) : Periodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add h2.neg
  -- 🎉 no goals
#align function.antiperiodic.sub Function.Antiperiodic.sub

theorem Periodic.add_antiperiod [AddGroup α] [Neg β] (h1 : Periodic f c₁) (h2 : Antiperiodic f c₂) :
    Antiperiodic f (c₁ + c₂) := by simp_all [← add_assoc]
                                   -- 🎉 no goals
#align function.periodic.add_antiperiod Function.Periodic.add_antiperiod

theorem Periodic.sub_antiperiod [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : Antiperiodic f (c₁ - c₂) := by
  simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg
  -- 🎉 no goals
#align function.periodic.sub_antiperiod Function.Periodic.sub_antiperiod

theorem Periodic.add_antiperiod_eq [AddGroup α] [Neg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ + c₂) = -f 0 :=
  (h1.add_antiperiod h2).eq
#align function.periodic.add_antiperiod_eq Function.Periodic.add_antiperiod_eq

theorem Periodic.sub_antiperiod_eq [AddGroup α] [InvolutiveNeg β] (h1 : Periodic f c₁)
    (h2 : Antiperiodic f c₂) : f (c₁ - c₂) = -f 0 :=
  (h1.sub_antiperiod h2).eq
#align function.periodic.sub_antiperiod_eq Function.Periodic.sub_antiperiod_eq

theorem Antiperiodic.mul [Add α] [Mul β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f * g) c := by simp_all
                                                       -- 🎉 no goals
#align function.antiperiodic.mul Function.Antiperiodic.mul

theorem Antiperiodic.div [Add α] [DivisionMonoid β] [HasDistribNeg β] (hf : Antiperiodic f c)
    (hg : Antiperiodic g c) : Periodic (f / g) c := by simp_all [neg_div_neg_eq]
                                                       -- 🎉 no goals
#align function.antiperiodic.div Function.Antiperiodic.div

end Function

theorem Int.fract_periodic (α) [LinearOrderedRing α] [FloorRing α] :
    Function.Periodic Int.fract (1 : α) := fun a => by
  exact_mod_cast Int.fract_add_int a 1
  -- 🎉 no goals
#align int.fract_periodic Int.fract_periodic
