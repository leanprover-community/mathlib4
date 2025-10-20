/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/

import Mathlib.Algebra.Module.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Sign

/-!
# Cycles of a permutation

This file starts the theory of cycles in permutations.

## Main definitions

In the following, `f : Equiv.Perm β`.

* `Equiv.Perm.SameCycle`: `f.SameCycle x y` when `x` and `y` are in the same cycle of `f`.
* `Equiv.Perm.IsCycle`: `f` is a cycle if any two nonfixed points of `f` are related by repeated
  applications of `f`, and `f` is not the identity.
* `Equiv.Perm.IsCycleOn`: `f` is a cycle on a set `s` when any two points of `s` are related by
  repeated applications of `f`.

## Notes

`Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn` are different in three ways:
* `IsCycle` is about the entire type while `IsCycleOn` is restricted to a set.
* `IsCycle` forbids the identity while `IsCycleOn` allows it (if `s` is a subsingleton).
* `IsCycleOn` forbids fixed points on `s` (if `s` is nontrivial), while `IsCycle` allows them.
-/


open Equiv Function Finset

variable {ι α β : Type*}

namespace Equiv.Perm

/-! ### `SameCycle` -/

section SameCycle

variable {f g : Perm α} {p : α → Prop} {x y z : α}

/-- The equivalence relation indicating that two points are in the same cycle of a permutation. -/
def SameCycle (f : Perm α) (x y : α) : Prop :=
  ∃ i : ℤ, (f ^ i) x = y

@[refl]
theorem SameCycle.refl (f : Perm α) (x : α) : SameCycle f x x :=
  ⟨0, rfl⟩

theorem SameCycle.rfl : SameCycle f x x :=
  SameCycle.refl _ _

protected theorem _root_.Eq.sameCycle (h : x = y) (f : Perm α) : f.SameCycle x y := by rw [h]

@[symm]
theorem SameCycle.symm : SameCycle f x y → SameCycle f y x := fun ⟨i, hi⟩ =>
  ⟨-i, by rw [zpow_neg, ← hi, inv_apply_self]⟩

theorem sameCycle_comm : SameCycle f x y ↔ SameCycle f y x :=
  ⟨SameCycle.symm, SameCycle.symm⟩

@[trans]
theorem SameCycle.trans : SameCycle f x y → SameCycle f y z → SameCycle f x z :=
  fun ⟨i, hi⟩ ⟨j, hj⟩ => ⟨j + i, by rw [zpow_add, mul_apply, hi, hj]⟩

variable (f) in
theorem SameCycle.equivalence : Equivalence (SameCycle f) :=
  ⟨SameCycle.refl f, SameCycle.symm, SameCycle.trans⟩

/-- The setoid defined by the `SameCycle` relation. -/
def SameCycle.setoid (f : Perm α) : Setoid α where
  r := f.SameCycle
  iseqv := SameCycle.equivalence f

@[simp]
theorem sameCycle_one : SameCycle 1 x y ↔ x = y := by simp [SameCycle]

@[simp]
theorem sameCycle_inv : SameCycle f⁻¹ x y ↔ SameCycle f x y :=
  (Equiv.neg _).exists_congr_left.trans <| by simp [SameCycle]

alias ⟨SameCycle.of_inv, SameCycle.inv⟩ := sameCycle_inv

@[simp]
theorem sameCycle_conj : SameCycle (g * f * g⁻¹) x y ↔ SameCycle f (g⁻¹ x) (g⁻¹ y) :=
  exists_congr fun i => by simp [conj_zpow, eq_inv_iff_eq]

theorem SameCycle.conj : SameCycle f x y → SameCycle (g * f * g⁻¹) (g x) (g y) := by
  simp [sameCycle_conj]

theorem SameCycle.apply_eq_self_iff : SameCycle f x y → (f x = x ↔ f y = y) := fun ⟨i, hi⟩ => by
  rw [← hi, ← mul_apply, ← zpow_one_add, add_comm, zpow_add_one, mul_apply,
    (f ^ i).injective.eq_iff]

theorem SameCycle.eq_of_left (h : SameCycle f x y) (hx : IsFixedPt f x) : x = y :=
  let ⟨_, hn⟩ := h
  (hx.perm_zpow _).eq.symm.trans hn

theorem SameCycle.eq_of_right (h : SameCycle f x y) (hy : IsFixedPt f y) : x = y :=
  h.eq_of_left <| h.apply_eq_self_iff.2 hy

@[simp]
theorem sameCycle_apply_left : SameCycle f (f x) y ↔ SameCycle f x y :=
  (Equiv.addRight 1).exists_congr_left.trans <| by
    simp [zpow_sub, SameCycle, Int.add_neg_one, Function.comp]

@[simp]
theorem sameCycle_apply_right : SameCycle f x (f y) ↔ SameCycle f x y := by
  rw [sameCycle_comm, sameCycle_apply_left, sameCycle_comm]

@[simp]
theorem sameCycle_inv_apply_left : SameCycle f (f⁻¹ x) y ↔ SameCycle f x y := by
  rw [← sameCycle_apply_left, apply_inv_self]

@[simp]
theorem sameCycle_inv_apply_right : SameCycle f x (f⁻¹ y) ↔ SameCycle f x y := by
  rw [← sameCycle_apply_right, apply_inv_self]

@[simp]
theorem sameCycle_zpow_left {n : ℤ} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y :=
  (Equiv.addRight (n : ℤ)).exists_congr_left.trans <| by simp [SameCycle, zpow_add]

@[simp]
theorem sameCycle_zpow_right {n : ℤ} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [sameCycle_comm, sameCycle_zpow_left, sameCycle_comm]

@[simp]
theorem sameCycle_pow_left {n : ℕ} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y := by
  rw [← zpow_natCast, sameCycle_zpow_left]

@[simp]
theorem sameCycle_pow_right {n : ℕ} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [← zpow_natCast, sameCycle_zpow_right]

alias ⟨SameCycle.of_apply_left, SameCycle.apply_left⟩ := sameCycle_apply_left

alias ⟨SameCycle.of_apply_right, SameCycle.apply_right⟩ := sameCycle_apply_right

alias ⟨SameCycle.of_inv_apply_left, SameCycle.inv_apply_left⟩ := sameCycle_inv_apply_left

alias ⟨SameCycle.of_inv_apply_right, SameCycle.inv_apply_right⟩ := sameCycle_inv_apply_right

alias ⟨SameCycle.of_pow_left, SameCycle.pow_left⟩ := sameCycle_pow_left

alias ⟨SameCycle.of_pow_right, SameCycle.pow_right⟩ := sameCycle_pow_right

alias ⟨SameCycle.of_zpow_left, SameCycle.zpow_left⟩ := sameCycle_zpow_left

alias ⟨SameCycle.of_zpow_right, SameCycle.zpow_right⟩ := sameCycle_zpow_right

theorem SameCycle.of_pow {n : ℕ} : SameCycle (f ^ n) x y → SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

theorem SameCycle.of_zpow {n : ℤ} : SameCycle (f ^ n) x y → SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩

@[simp]
theorem sameCycle_subtypePerm {h} {x y : { x // p x }} :
    (f.subtypePerm h).SameCycle x y ↔ f.SameCycle x y :=
  exists_congr fun n => by simp [Subtype.ext_iff]

alias ⟨_, SameCycle.subtypePerm⟩ := sameCycle_subtypePerm

@[simp]
theorem sameCycle_extendDomain {p : β → Prop} [DecidablePred p] {f : α ≃ Subtype p} :
    SameCycle (g.extendDomain f) (f x) (f y) ↔ g.SameCycle x y :=
  exists_congr fun n => by
    rw [← extendDomain_zpow, extendDomain_apply_image, Subtype.coe_inj, f.injective.eq_iff]

alias ⟨_, SameCycle.extendDomain⟩ := sameCycle_extendDomain

theorem SameCycle.exists_pow_eq' [Finite α] : SameCycle f x y → ∃ i < orderOf f, (f ^ i) x = y := by
  rintro ⟨k, rfl⟩
  use (k % orderOf f).natAbs
  have h₀ := Int.natCast_pos.mpr (orderOf_pos f)
  have h₁ := Int.emod_nonneg k h₀.ne'
  rw [← zpow_natCast, Int.natAbs_of_nonneg h₁, zpow_mod_orderOf]
  refine ⟨?_, by rfl⟩
  rw [← Int.ofNat_lt, Int.natAbs_of_nonneg h₁]
  exact Int.emod_lt_of_pos _ h₀

theorem SameCycle.exists_pow_eq'' [Finite α] (h : SameCycle f x y) :
    ∃ i : ℕ, 0 < i ∧ i ≤ orderOf f ∧ (f ^ i) x = y := by
  obtain ⟨_ | i, hi, rfl⟩ := h.exists_pow_eq'
  · refine ⟨orderOf f, orderOf_pos f, le_rfl, ?_⟩
    rw [pow_orderOf_eq_one, pow_zero]
  · exact ⟨i.succ, i.zero_lt_succ, hi.le, by rfl⟩

theorem SameCycle.exists_fin_pow_eq [Finite α] (h : SameCycle f x y) :
    ∃ i : Fin (orderOf f), (f ^ (i : ℕ)) x = y := by
  obtain ⟨i, hi, hx⟩ := SameCycle.exists_pow_eq' h
  exact ⟨⟨i, hi⟩, hx⟩

theorem SameCycle.exists_nat_pow_eq [Finite α] (h : SameCycle f x y) :
    ∃ i : ℕ, (f ^ i) x = y := by
  obtain ⟨i, _, hi⟩ := h.exists_pow_eq'
  exact ⟨i, hi⟩

instance (f : Perm α) [DecidableRel (SameCycle f)] :
    DecidableRel (SameCycle f⁻¹) := fun x y =>
  decidable_of_iff (f.SameCycle x y) (sameCycle_inv).symm

instance (priority := 100) [DecidableEq α] : DecidableRel (SameCycle (1 : Perm α)) := fun x y =>
  decidable_of_iff (x = y) sameCycle_one.symm

end SameCycle

/-!
### `IsCycle`
-/

section IsCycle

variable {f g : Perm α} {x y : α}

/-- A cycle is a non-identity permutation where any two nonfixed points of the permutation are
related by repeated application of the permutation. -/
def IsCycle (f : Perm α) : Prop :=
  ∃ x, f x ≠ x ∧ ∀ ⦃y⦄, f y ≠ y → SameCycle f x y

theorem IsCycle.ne_one (h : IsCycle f) : f ≠ 1 := fun hf => by simp [hf, IsCycle] at h

@[simp]
theorem not_isCycle_one : ¬(1 : Perm α).IsCycle := fun H => H.ne_one rfl

protected theorem IsCycle.sameCycle (hf : IsCycle f) (hx : f x ≠ x) (hy : f y ≠ y) :
    SameCycle f x y :=
  let ⟨g, hg⟩ := hf
  let ⟨a, ha⟩ := hg.2 hx
  let ⟨b, hb⟩ := hg.2 hy
  ⟨b - a, by rw [← ha, ← mul_apply, ← zpow_add, sub_add_cancel, hb]⟩

theorem IsCycle.exists_zpow_eq : IsCycle f → f x ≠ x → f y ≠ y → ∃ i : ℤ, (f ^ i) x = y :=
  IsCycle.sameCycle

theorem IsCycle.inv (hf : IsCycle f) : IsCycle f⁻¹ :=
  hf.imp fun _ ⟨hx, h⟩ =>
    ⟨inv_eq_iff_eq.not.2 hx.symm, fun _ hy => (h <| inv_eq_iff_eq.not.2 hy.symm).inv⟩

@[simp]
theorem isCycle_inv : IsCycle f⁻¹ ↔ IsCycle f :=
  ⟨fun h => h.inv, IsCycle.inv⟩

theorem IsCycle.conj : IsCycle f → IsCycle (g * f * g⁻¹) := by
  rintro ⟨x, hx, h⟩
  refine ⟨g x, by simp [coe_mul, inv_apply_self, hx], fun y hy => ?_⟩
  rw [← apply_inv_self g y]
  exact (h <| eq_inv_iff_eq.not.2 hy).conj

protected theorem IsCycle.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    IsCycle g → IsCycle (g.extendDomain f) := by
  rintro ⟨a, ha, ha'⟩
  refine ⟨f a, ?_, fun b hb => ?_⟩
  · rw [extendDomain_apply_image]
    exact Subtype.coe_injective.ne (f.injective.ne ha)
  have h : b = f (f.symm ⟨b, of_not_not <| hb ∘ extendDomain_apply_not_subtype _ _⟩) := by
    rw [apply_symm_apply, Subtype.coe_mk]
  rw [h] at hb ⊢
  simp only [extendDomain_apply_image, Subtype.coe_injective.ne_iff, f.injective.ne_iff] at hb
  exact (ha' hb).extendDomain

theorem isCycle_iff_sameCycle (hx : f x ≠ x) : IsCycle f ↔ ∀ {y}, SameCycle f x y ↔ f y ≠ y :=
  ⟨fun hf y =>
    ⟨fun ⟨i, hi⟩ hy =>
      hx <| by
        rw [← zpow_apply_eq_self_of_apply_eq_self hy i, (f ^ i).injective.eq_iff] at hi
        rw [hi, hy],
      hf.exists_zpow_eq hx⟩,
    fun h => ⟨x, hx, fun _ hy => h.2 hy⟩⟩

section Finite

variable [Finite α]

theorem IsCycle.exists_pow_eq (hf : IsCycle f) (hx : f x ≠ x) (hy : f y ≠ y) :
    ∃ i : ℕ, (f ^ i) x = y := by
  let ⟨n, hn⟩ := hf.exists_zpow_eq hx hy
  classical exact
      ⟨(n % orderOf f).toNat, by
        {have := n.emod_nonneg (Int.natCast_ne_zero.mpr (ne_of_gt (orderOf_pos f)))
         rwa [← zpow_natCast, Int.toNat_of_nonneg this, zpow_mod_orderOf]}⟩

end Finite

variable [DecidableEq α]

theorem isCycle_swap (hxy : x ≠ y) : IsCycle (swap x y) :=
  ⟨y, by rwa [swap_apply_right], fun a (ha : ite (a = x) y (ite (a = y) x a) ≠ a) =>
    if hya : y = a then ⟨0, hya⟩
    else
      ⟨1, by
        rw [zpow_one, swap_apply_def]
        split_ifs at * <;> tauto⟩⟩

protected theorem IsSwap.isCycle : IsSwap f → IsCycle f := by
  rintro ⟨x, y, hxy, rfl⟩
  exact isCycle_swap hxy

variable [Fintype α]

theorem IsCycle.two_le_card_support (h : IsCycle f) : 2 ≤ #f.support :=
  two_le_card_support_of_ne_one h.ne_one

/-- The subgroup generated by a cycle is in bijection with its support -/
noncomputable def IsCycle.zpowersEquivSupport {σ : Perm α} (hσ : IsCycle σ) :
    (Subgroup.zpowers σ) ≃ σ.support :=
  Equiv.ofBijective
    (fun (τ : ↥((Subgroup.zpowers σ) : Set (Perm α))) =>
      ⟨(τ : Perm α) (Classical.choose hσ), by
        obtain ⟨τ, n, rfl⟩ := τ
        rw [Subtype.coe_mk, zpow_apply_mem_support, mem_support]
        exact (Classical.choose_spec hσ).1⟩)
    (by
      constructor
      · rintro ⟨a, m, rfl⟩ ⟨b, n, rfl⟩ h
        ext y
        by_cases hy : σ y = y
        · simp_rw [zpow_apply_eq_self_of_apply_eq_self hy]
        · obtain ⟨i, rfl⟩ := (Classical.choose_spec hσ).2 hy
          rw [Subtype.coe_mk, Subtype.coe_mk, zpow_apply_comm σ m i, zpow_apply_comm σ n i]
          exact congr_arg _ (Subtype.ext_iff.mp h)
      · rintro ⟨y, hy⟩
        rw [mem_support] at hy
        obtain ⟨n, rfl⟩ := (Classical.choose_spec hσ).2 hy
        exact ⟨⟨σ ^ n, n, rfl⟩, rfl⟩)

@[simp]
theorem IsCycle.zpowersEquivSupport_apply {σ : Perm α} (hσ : IsCycle σ) {n : ℕ} :
    hσ.zpowersEquivSupport ⟨σ ^ n, n, rfl⟩ =
      ⟨(σ ^ n) (Classical.choose hσ),
        pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ :=
  rfl

@[simp]
theorem IsCycle.zpowersEquivSupport_symm_apply {σ : Perm α} (hσ : IsCycle σ) (n : ℕ) :
    hσ.zpowersEquivSupport.symm
        ⟨(σ ^ n) (Classical.choose hσ),
          pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ =
      ⟨σ ^ n, n, rfl⟩ :=
  (Equiv.symm_apply_eq _).2 hσ.zpowersEquivSupport_apply

protected theorem IsCycle.orderOf (hf : IsCycle f) : orderOf f = #f.support := by
  rw [← Fintype.card_zpowers, ← Fintype.card_coe]
  convert Fintype.card_congr (IsCycle.zpowersEquivSupport hf)

theorem isCycle_swap_mul_aux₁ {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) {b x : α} {f : Perm α} (_ : (swap x (f x) * f) b ≠ b) (_ : (f ^ n) (f x) = b),
      ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b := by
  intro n
  induction n with
  | zero => exact fun _ h => ⟨0, h⟩
  | succ n hn =>
    intro b x f hb h
    exact if hfbx : f x = b then ⟨0, hfbx⟩
      else
        have : f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb
        have hb' : (swap x (f x) * f) (f⁻¹ b) ≠ f⁻¹ b := by
          rw [mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (Ne.symm hfbx), Ne, ←
            f.injective.eq_iff, apply_inv_self]
          exact this.1
        let ⟨i, hi⟩ := hn hb' (f.injective <| by
          rw [apply_inv_self]; rwa [pow_succ', mul_apply] at h)
        ⟨i + 1, by
          rw [add_comm, zpow_add, mul_apply, hi, zpow_one, mul_apply, apply_inv_self,
            swap_apply_of_ne_of_ne (ne_and_ne_of_swap_mul_apply_ne_self hb).2 (Ne.symm hfbx)]⟩

theorem isCycle_swap_mul_aux₂ {α : Type*} [DecidableEq α] :
    ∀ (n : ℤ) {b x : α} {f : Perm α} (_ : (swap x (f x) * f) b ≠ b) (_ : (f ^ n) (f x) = b),
      ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b := by
  intro n
  cases n with
  | ofNat n => exact isCycle_swap_mul_aux₁ n
  | negSucc n =>
    intro b x f hb h
    exact if hfbx' : f x = b then ⟨0, hfbx'⟩
      else
        have : f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb
        have hb : (swap x (f⁻¹ x) * f⁻¹) (f⁻¹ b) ≠ f⁻¹ b := by
          rw [mul_apply, swap_apply_def]
          split_ifs <;>
            simp only [inv_eq_iff_eq, Perm.mul_apply, zpow_negSucc, Ne, Perm.apply_inv_self] at *
              <;> tauto
        let ⟨i, hi⟩ :=
          isCycle_swap_mul_aux₁ n hb
            (show (f⁻¹ ^ n) (f⁻¹ x) = f⁻¹ b by
              rw [← zpow_natCast, ← h, ← mul_apply, ← mul_apply, ← mul_apply, zpow_negSucc,
                ← inv_pow, pow_succ, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, zpow_natCast,
                ← pow_succ', ← pow_succ])
        have h : (swap x (f⁻¹ x) * f⁻¹) (f x) = f⁻¹ x := by
          rw [mul_apply, inv_apply_self, swap_apply_left]
        ⟨-i, by
          rw [← add_sub_cancel_right i 1, neg_sub, sub_eq_add_neg, zpow_add, zpow_one, zpow_neg,
            ← inv_zpow, mul_inv_rev, swap_inv, mul_swap_eq_swap_mul, inv_apply_self, swap_comm _ x,
            zpow_add, zpow_one, mul_apply, mul_apply (_ ^ i), h, hi, mul_apply, apply_inv_self,
            swap_apply_of_ne_of_ne this.2 (Ne.symm hfbx')]⟩

theorem IsCycle.eq_swap_of_apply_apply_eq_self {α : Type*} [DecidableEq α] {f : Perm α}
    (hf : IsCycle f) {x : α} (hfx : f x ≠ x) (hffx : f (f x) = x) : f = swap x (f x) :=
  Equiv.ext fun y =>
    let ⟨z, hz⟩ := hf
    let ⟨i, hi⟩ := hz.2 hfx
    if hyx : y = x then by simp [hyx]
    else
      if hfyx : y = f x then by simp [hfyx, hffx]
      else by
        rw [swap_apply_of_ne_of_ne hyx hfyx]
        refine by_contradiction fun hy => ?_
        obtain ⟨j, hj⟩ := hz.2 hy
        rw [← sub_add_cancel j i, zpow_add, mul_apply, hi] at hj
        rcases zpow_apply_eq_of_apply_apply_eq_self hffx (j - i) with hji | hji
        · rw [← hj, hji] at hyx
          tauto
        · rw [← hj, hji] at hfyx
          tauto

theorem IsCycle.swap_mul {α : Type*} [DecidableEq α] {f : Perm α} (hf : IsCycle f) {x : α}
    (hx : f x ≠ x) (hffx : f (f x) ≠ x) : IsCycle (swap x (f x) * f) :=
  ⟨f x, by simp [swap_apply_def, mul_apply, if_neg hffx, f.injective.eq_iff, hx],
    fun y hy =>
    let ⟨i, hi⟩ := hf.exists_zpow_eq hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1
    have hi : (f ^ (i - 1)) (f x) = y :=
      calc
        (f ^ (i - 1) : Perm α) (f x) = (f ^ (i - 1) * f ^ (1 : ℤ) : Perm α) x := by simp
        _ = y := by rwa [← zpow_add, sub_add_cancel]
    isCycle_swap_mul_aux₂ (i - 1) hy hi⟩

theorem IsCycle.sign {f : Perm α} (hf : IsCycle f) : sign f = -(-1) ^ #f.support :=
  let ⟨x, hx⟩ := hf
  calc
    Perm.sign f = Perm.sign (swap x (f x) * (swap x (f x) * f)) := by
      {rw [← mul_assoc, mul_def, mul_def, swap_swap, trans_refl]}
    _ = -(-1) ^ #f.support :=
      if h1 : f (f x) = x then by
        have h : swap x (f x) * f = 1 := by
          simp only [mul_def, one_def]
          rw [hf.eq_swap_of_apply_apply_eq_self hx.1 h1, swap_apply_left, swap_swap]
        rw [sign_mul, sign_swap hx.1.symm, h, sign_one,
          hf.eq_swap_of_apply_apply_eq_self hx.1 h1, card_support_swap hx.1.symm]
        rfl
      else by
        have h : #(swap x (f x) * f).support + 1 = #f.support := by
          rw [← insert_erase (mem_support.2 hx.1), support_swap_mul_eq _ _ h1,
            card_insert_of_notMem (notMem_erase _ _), sdiff_singleton_eq_erase]
        rw [sign_mul, sign_swap hx.1.symm, (hf.swap_mul hx.1 h1).sign, ← h]
        simp only [mul_neg, neg_mul, one_mul, neg_neg, pow_add, pow_one, mul_one]
termination_by #f.support

theorem IsCycle.of_pow {n : ℕ} (h1 : IsCycle (f ^ n)) (h2 : f.support ⊆ (f ^ n).support) :
    IsCycle f := by
  have key : ∀ x : α, (f ^ n) x ≠ x ↔ f x ≠ x := by
    simp_rw [← mem_support, ← Finset.ext_iff]
    exact (support_pow_le _ n).antisymm h2
  obtain ⟨x, hx1, hx2⟩ := h1
  refine ⟨x, (key x).mp hx1, fun y hy => ?_⟩
  obtain ⟨i, _⟩ := hx2 ((key y).mpr hy)
  exact ⟨n * i, by rwa [zpow_mul]⟩

-- The lemma `support_zpow_le` is relevant. It means that `h2` is equivalent to
-- `σ.support = (σ ^ n).support`, as well as to `#σ.support ≤ #(σ ^ n).support`.
theorem IsCycle.of_zpow {n : ℤ} (h1 : IsCycle (f ^ n)) (h2 : f.support ⊆ (f ^ n).support) :
    IsCycle f := by
  cases n
  · exact h1.of_pow h2
  · simp only [zpow_negSucc, Perm.support_inv] at h1 h2
    exact (inv_inv (f ^ _) ▸ h1.inv).of_pow h2

theorem nodup_of_pairwise_disjoint_cycles {l : List (Perm β)} (h1 : ∀ f ∈ l, IsCycle f)
    (h2 : l.Pairwise Disjoint) : l.Nodup :=
  nodup_of_pairwise_disjoint (fun h => (h1 1 h).ne_one rfl) h2

/-- Unlike `support_congr`, which assumes that `∀ (x ∈ g.support), f x = g x)`, here
we have the weaker assumption that `∀ (x ∈ f.support), f x = g x`. -/
theorem IsCycle.support_congr (hf : IsCycle f) (hg : IsCycle g) (h : f.support ⊆ g.support)
    (h' : ∀ x ∈ f.support, f x = g x) : f = g := by
  have : f.support = g.support := by
    refine le_antisymm h ?_
    intro z hz
    obtain ⟨x, hx, _⟩ := id hf
    have hx' : g x ≠ x := by rwa [← h' x (mem_support.mpr hx)]
    obtain ⟨m, hm⟩ := hg.exists_pow_eq hx' (mem_support.mp hz)
    have h'' : ∀ x ∈ f.support ∩ g.support, f x = g x := by
      intro x hx
      exact h' x (mem_of_mem_inter_left hx)
    rwa [← hm, ←
      pow_eq_on_of_mem_support h'' _ x
        (mem_inter_of_mem (mem_support.mpr hx) (mem_support.mpr hx')),
      pow_apply_mem_support, mem_support]
  refine Equiv.Perm.support_congr h ?_
  simpa [← this] using h'

/-- If two cyclic permutations agree on all terms in their intersection,
and that intersection is not empty, then the two cyclic permutations must be equal. -/
theorem IsCycle.eq_on_support_inter_nonempty_congr (hf : IsCycle f) (hg : IsCycle g)
    (h : ∀ x ∈ f.support ∩ g.support, f x = g x)
    (hx : f x = g x) (hx' : x ∈ f.support) : f = g := by
  have hx'' : x ∈ g.support := by rwa [mem_support, ← hx, ← mem_support]
  have : f.support ⊆ g.support := by
    intro y hy
    obtain ⟨k, rfl⟩ := hf.exists_pow_eq (mem_support.mp hx') (mem_support.mp hy)
    rwa [pow_eq_on_of_mem_support h _ _ (mem_inter_of_mem hx' hx''), pow_apply_mem_support]
  rw [inter_eq_left.mpr this] at h
  exact hf.support_congr hg this h

theorem IsCycle.support_pow_eq_iff (hf : IsCycle f) {n : ℕ} :
    support (f ^ n) = support f ↔ ¬orderOf f ∣ n := by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h H
    refine hf.ne_one ?_
    rw [← support_eq_empty_iff, ← h, H, support_one]
  · intro H
    apply le_antisymm (support_pow_le _ n) _
    intro x hx
    contrapose! H
    ext z
    by_cases hz : f z = z
    · rw [pow_apply_eq_self_of_apply_eq_self hz, one_apply]
    · obtain ⟨k, rfl⟩ := hf.exists_pow_eq hz (mem_support.mp hx)
      apply (f ^ k).injective
      rw [← mul_apply, (Commute.pow_pow_self _ _ _).eq, mul_apply]
      simpa using H

theorem IsCycle.support_pow_of_pos_of_lt_orderOf (hf : IsCycle f) {n : ℕ} (npos : 0 < n)
    (hn : n < orderOf f) : (f ^ n).support = f.support :=
  hf.support_pow_eq_iff.2 <| Nat.not_dvd_of_pos_of_lt npos hn

theorem IsCycle.pow_iff [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    IsCycle (f ^ n) ↔ n.Coprime (orderOf f) := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      have hr : support (f ^ n) = support f := by
        rw [hf.support_pow_eq_iff]
        rintro ⟨k, rfl⟩
        refine h.ne_one ?_
        simp [pow_mul, pow_orderOf_eq_one]
      have : orderOf (f ^ n) = orderOf f := by rw [h.orderOf, hr, hf.orderOf]
      rw [orderOf_pow, Nat.div_eq_self] at this
      rcases this with h | _
      · exact absurd h (orderOf_pos _).ne'
      · rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    · intro h
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
      have hf' : IsCycle ((f ^ n) ^ m) := by rwa [hm]
      refine hf'.of_pow fun x hx => ?_
      rw [hm]
      exact support_pow_le _ n hx

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
theorem IsCycle.pow_eq_one_iff [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    f ^ n = 1 ↔ ∃ x, f x ≠ x ∧ (f ^ n) x = x := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      by_cases h : support (f ^ n) = support f
      · rw [← mem_support, ← h, mem_support] at hx
        contradiction
      · rw [hf.support_pow_eq_iff, Classical.not_not] at h
        obtain ⟨k, rfl⟩ := h
        rw [pow_mul, pow_orderOf_eq_one, one_pow]

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
theorem IsCycle.pow_eq_one_iff' [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} {x : β}
    (hx : f x ≠ x) : f ^ n = 1 ↔ (f ^ n) x = x :=
  ⟨fun h => DFunLike.congr_fun h x, fun h => hf.pow_eq_one_iff.2 ⟨x, hx, h⟩⟩

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
theorem IsCycle.pow_eq_one_iff'' [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    f ^ n = 1 ↔ ∀ x, f x ≠ x → (f ^ n) x = x :=
  ⟨fun h _ hx => (hf.pow_eq_one_iff' hx).1 h, fun h =>
    let ⟨_, hx, _⟩ := id hf
    (hf.pow_eq_one_iff' hx).2 (h _ hx)⟩

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
theorem IsCycle.pow_eq_pow_iff [Finite β] {f : Perm β} (hf : IsCycle f) {a b : ℕ} :
    f ^ a = f ^ b ↔ ∃ x, f x ≠ x ∧ (f ^ a) x = (f ^ b) x := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      obtain ⟨x, hx, -⟩ := id hf
      exact ⟨x, hx, by simp [h]⟩
    · rintro ⟨x, hx, hx'⟩
      wlog hab : a ≤ b generalizing a b
      · exact (this hx'.symm (le_of_not_ge hab)).symm
      suffices f ^ (b - a) = 1 by
        rw [pow_sub _ hab, mul_inv_eq_one] at this
        rw [this]
      rw [hf.pow_eq_one_iff]
      by_cases hfa : (f ^ a) x ∈ f.support
      · refine ⟨(f ^ a) x, mem_support.mp hfa, ?_⟩
        simp only [pow_sub _ hab, Equiv.Perm.coe_mul, Function.comp_apply, inv_apply_self, ← hx']
      · have h := @Equiv.Perm.zpow_apply_comm _ f 1 a x
        simp only [zpow_one, zpow_natCast] at h
        rw [notMem_support, h, Function.Injective.eq_iff (f ^ a).injective] at hfa
        contradiction

theorem IsCycle.isCycle_pow_pos_of_lt_prime_order [Finite β] {f : Perm β} (hf : IsCycle f)
    (hf' : (orderOf f).Prime) (n : ℕ) (hn : 0 < n) (hn' : n < orderOf f) : IsCycle (f ^ n) := by
  classical
    cases nonempty_fintype β
    have : n.Coprime (orderOf f) := by
      refine Nat.Coprime.symm ?_
      rw [Nat.Prime.coprime_iff_not_dvd hf']
      exact Nat.not_dvd_of_pos_of_lt hn hn'
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime this
    have hf'' := hf
    rw [← hm] at hf''
    refine hf''.of_pow ?_
    rw [hm]
    exact support_pow_le f n

end IsCycle

open Equiv

theorem _root_.Int.addLeft_one_isCycle : (Equiv.addLeft 1 : Perm ℤ).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

theorem _root_.Int.addRight_one_isCycle : (Equiv.addRight 1 : Perm ℤ).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

theorem IsCycle.isConj (hσ : IsCycle σ) (hτ : IsCycle τ) (h : #σ.support = #τ.support) :
    IsConj σ τ := by
  refine
    isConj_of_support_equiv
      (hσ.zpowersEquivSupport.symm.trans <|
        (zpowersEquivZPowers <| by rw [hσ.orderOf, h, hτ.orderOf]).trans hτ.zpowersEquivSupport)
      ?_
  intro x hx
  simp only [Equiv.trans_apply]
  obtain ⟨n, rfl⟩ := hσ.exists_pow_eq (Classical.choose_spec hσ).1 (mem_support.1 hx)
  simp [← Perm.mul_apply, ← pow_succ']

theorem IsCycle.isConj_iff (hσ : IsCycle σ) (hτ : IsCycle τ) :
    IsConj σ τ ↔ #σ.support = #τ.support where
  mp h := by
    obtain ⟨π, rfl⟩ := (_root_.isConj_iff).1 h
    refine Finset.card_bij (fun a _ => π a) (fun _ ha => ?_) (fun _ _ _ _ ab => π.injective ab)
        fun b hb ↦ ⟨π⁻¹ b, ?_, π.apply_inv_self b⟩
    · simp [mem_support.1 ha]
    contrapose! hb
    rw [mem_support, Classical.not_not] at hb
    rw [mem_support, Classical.not_not, Perm.mul_apply, Perm.mul_apply, hb, Perm.apply_inv_self]
  mpr := hσ.isConj hτ

end Conjugation

/-! ### `IsCycleOn` -/

section IsCycleOn

variable {f g : Perm α} {s t : Set α} {a b x y : α}

/-- A permutation is a cycle on `s` when any two points of `s` are related by repeated application
of the permutation. Note that this means the identity is a cycle of subsingleton sets. -/
def IsCycleOn (f : Perm α) (s : Set α) : Prop :=
  Set.BijOn f s s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → f.SameCycle x y

@[simp]
theorem isCycleOn_empty : f.IsCycleOn ∅ := by simp [IsCycleOn]

@[simp]
theorem isCycleOn_one : (1 : Perm α).IsCycleOn s ↔ s.Subsingleton := by
  simp [IsCycleOn, Set.bijOn_id, Set.Subsingleton]

alias ⟨IsCycleOn.subsingleton, _root_.Set.Subsingleton.isCycleOn_one⟩ := isCycleOn_one

@[simp]
theorem isCycleOn_singleton : f.IsCycleOn {a} ↔ f a = a := by simp [IsCycleOn, SameCycle.rfl]

theorem isCycleOn_of_subsingleton [Subsingleton α] (f : Perm α) (s : Set α) : f.IsCycleOn s :=
  ⟨s.bijOn_of_subsingleton _, fun x _ y _ => (Subsingleton.elim x y).sameCycle _⟩

@[simp]
theorem isCycleOn_inv : f⁻¹.IsCycleOn s ↔ f.IsCycleOn s := by
  simp only [IsCycleOn, sameCycle_inv, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ Set.BijOn.perm_inv h, fun h ↦ Set.BijOn.perm_inv h⟩

alias ⟨IsCycleOn.of_inv, IsCycleOn.inv⟩ := isCycleOn_inv

theorem IsCycleOn.conj (h : f.IsCycleOn s) : (g * f * g⁻¹).IsCycleOn ((g : Perm α) '' s) :=
  ⟨(g.bijOn_image.comp h.1).comp g.bijOn_symm_image, fun x hx y hy => by
    rw [← preimage_inv] at hx hy
    convert Equiv.Perm.SameCycle.conj (h.2 hx hy) (g := g) <;> rw [apply_inv_self]⟩

theorem isCycleOn_swap [DecidableEq α] (hab : a ≠ b) : (swap a b).IsCycleOn {a, b} :=
  ⟨bijOn_swap (by simp) (by simp), fun x hx y hy => by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    obtain rfl | rfl := hx <;> obtain rfl | rfl := hy
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_left]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_right]⟩
    · exact ⟨0, by rw [zpow_zero, coe_one, id]⟩⟩

protected theorem IsCycleOn.apply_ne (hf : f.IsCycleOn s) (hs : s.Nontrivial) (ha : a ∈ s) :
    f a ≠ a := by
  obtain ⟨b, hb, hba⟩ := hs.exists_ne a
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  exact fun h => hba (IsFixedPt.perm_zpow h n)

protected theorem IsCycle.isCycleOn (hf : f.IsCycle) : f.IsCycleOn { x | f x ≠ x } :=
  ⟨f.bijOn fun _ => f.apply_eq_iff_eq.not, fun _ ha _ => hf.sameCycle ha⟩

/-- This lemma demonstrates the relation between `Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn`
in non-degenerate cases. -/
theorem isCycle_iff_exists_isCycleOn :
    f.IsCycle ↔ ∃ s : Set α, s.Nontrivial ∧ f.IsCycleOn s ∧ ∀ ⦃x⦄, ¬IsFixedPt f x → x ∈ s := by
  refine ⟨fun hf => ⟨{ x | f x ≠ x }, ?_, hf.isCycleOn, fun _ => id⟩, ?_⟩
  · obtain ⟨a, ha⟩ := hf
    exact ⟨f a, f.injective.ne ha.1, a, ha.1, ha.1⟩
  · rintro ⟨s, hs, hf, hsf⟩
    obtain ⟨a, ha⟩ := hs.nonempty
    exact ⟨a, hf.apply_ne hs ha, fun b hb => hf.2 ha <| hsf hb⟩

theorem IsCycleOn.apply_mem_iff (hf : f.IsCycleOn s) : f x ∈ s ↔ x ∈ s :=
  ⟨fun hx => by
    convert hf.1.perm_inv.1 hx
    rw [inv_apply_self], fun hx => hf.1.mapsTo hx⟩

/-- Note that the identity satisfies `IsCycleOn` for any subsingleton set, but not `IsCycle`. -/
theorem IsCycleOn.isCycle_subtypePerm (hf : f.IsCycleOn s) (hs : s.Nontrivial) :
    (f.subtypePerm fun _ => hf.apply_mem_iff : Perm s).IsCycle := by
  obtain ⟨a, ha⟩ := hs.nonempty
  exact
    ⟨⟨a, ha⟩, ne_of_apply_ne ((↑) : s → α) (hf.apply_ne hs ha), fun b _ =>
      (hf.2 (⟨a, ha⟩ : s).2 b.2).subtypePerm⟩

/-- Note that the identity is a cycle on any subsingleton set, but not a cycle. -/
protected theorem IsCycleOn.subtypePerm (hf : f.IsCycleOn s) :
    (f.subtypePerm fun _ => hf.apply_mem_iff : Perm s).IsCycleOn _root_.Set.univ := by
  obtain hs | hs := s.subsingleton_or_nontrivial
  · haveI := hs.coe_sort
    exact isCycleOn_of_subsingleton _ _
  convert (hf.isCycle_subtypePerm hs).isCycleOn
  rw [eq_comm, Set.eq_univ_iff_forall]
  exact fun x => ne_of_apply_ne ((↑) : s → α) (hf.apply_ne hs x.2)

-- TODO: Theory of order of an element under an action
theorem IsCycleOn.pow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) {n : ℕ} :
    (f ^ n) a = a ↔ #s ∣ n := by
  obtain rfl | hs := Finset.eq_singleton_or_nontrivial ha
  · rw [coe_singleton, isCycleOn_singleton] at hf
    simpa using IsFixedPt.iterate hf n
  classical
    have h (x : s) : ¬f x = x := hf.apply_ne hs x.2
    have := (hf.isCycle_subtypePerm hs).orderOf
    simp only [coe_sort_coe, support_subtypePerm, ne_eq, h, not_false_eq_true, univ_eq_attach,
      mem_attach, imp_self, implies_true, filter_true_of_mem, card_attach] at this
    rw [← this, orderOf_dvd_iff_pow_eq_one,
      (hf.isCycle_subtypePerm hs).pow_eq_one_iff'
        (ne_of_apply_ne ((↑) : s → α) <| hf.apply_ne hs (⟨a, ha⟩ : s).2)]
    simp [-coe_sort_coe]

theorem IsCycleOn.zpow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) :
    ∀ {n : ℤ}, (f ^ n) a = a ↔ (#s : ℤ) ∣ n
  | Int.ofNat _ => (hf.pow_apply_eq ha).trans Int.natCast_dvd_natCast.symm
  | Int.negSucc n => by
    rw [zpow_negSucc, ← inv_pow]
    exact (hf.inv.pow_apply_eq ha).trans (dvd_neg.trans Int.natCast_dvd_natCast).symm

theorem IsCycleOn.pow_apply_eq_pow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s)
    {m n : ℕ} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [MOD #s] := by
  rw [Nat.modEq_iff_dvd, ← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_inv_iff_eq, eq_comm]

theorem IsCycleOn.zpow_apply_eq_zpow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s)
    {m n : ℤ} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [ZMOD #s] := by
  rw [Int.modEq_iff_dvd, ← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_inv_iff_eq, eq_comm]

theorem IsCycleOn.pow_card_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) :
    (f ^ #s) a = a :=
  (hf.pow_apply_eq ha).2 dvd_rfl

theorem IsCycleOn.exists_pow_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ n < #s, (f ^ n) a = b := by
  classical
    obtain ⟨n, rfl⟩ := hf.2 ha hb
    obtain ⟨k, hk⟩ := (Int.mod_modEq n #s).symm.dvd
    refine ⟨n.natMod #s, Int.natMod_lt (Nonempty.card_pos ⟨a, ha⟩).ne', ?_⟩
    rw [← zpow_natCast, Int.natMod,
      Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.2
        (Nonempty.card_pos ⟨a, ha⟩).ne'), sub_eq_iff_eq_add'.1 hk, zpow_add, zpow_mul]
    simp only [zpow_natCast, coe_mul, comp_apply, EmbeddingLike.apply_eq_iff_eq]
    exact IsFixedPt.perm_zpow (hf.pow_card_apply ha) _

theorem IsCycleOn.exists_pow_eq' (hs : s.Finite) (hf : f.IsCycleOn s) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ n : ℕ, (f ^ n) a = b := by
  lift s to Finset α using id hs
  obtain ⟨n, -, hn⟩ := hf.exists_pow_eq ha hb
  exact ⟨n, hn⟩

theorem IsCycleOn.range_pow (hs : s.Finite) (h : f.IsCycleOn s) (ha : a ∈ s) :
    Set.range (fun n => (f ^ n) a : ℕ → α) = s :=
  Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => h.1.mapsTo.perm_pow _ ha) fun _ =>
    h.exists_pow_eq' hs ha

theorem IsCycleOn.range_zpow (h : f.IsCycleOn s) (ha : a ∈ s) :
    Set.range (fun n => (f ^ n) a : ℤ → α) = s :=
  Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => (h.1.perm_zpow _).mapsTo ha) <| h.2 ha

theorem IsCycleOn.of_pow {n : ℕ} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) : f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_pow⟩

theorem IsCycleOn.of_zpow {n : ℤ} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) :
    f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_zpow⟩

theorem IsCycleOn.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)
    (h : g.IsCycleOn s) : (g.extendDomain f).IsCycleOn ((↑) ∘ f '' s) :=
  ⟨h.1.extendDomain, by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h.2 ha hb).extendDomain⟩

protected theorem IsCycleOn.countable (hs : f.IsCycleOn s) : s.Countable := by
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · exact Set.countable_empty
  · exact (Set.countable_range fun n : ℤ => (⇑(f ^ n) : α → α) a).mono (hs.2 ha)


end IsCycleOn

end Equiv.Perm

namespace List

section

variable [DecidableEq α] {l : List α}

theorem Nodup.isCycleOn_formPerm (h : l.Nodup) :
    l.formPerm.IsCycleOn { a | a ∈ l } := by
  refine ⟨l.formPerm.bijOn fun _ => List.formPerm_mem_iff_mem, fun a ha b hb => ?_⟩
  rw [Set.mem_setOf, ← List.idxOf_lt_length_iff] at ha hb
  rw [← List.getElem_idxOf ha, ← List.getElem_idxOf hb]
  refine ⟨l.idxOf b - l.idxOf a, ?_⟩
  simp only [sub_eq_neg_add, zpow_add, zpow_neg, Equiv.Perm.inv_eq_iff_eq, zpow_natCast,
    Equiv.Perm.coe_mul, List.formPerm_pow_apply_getElem _ h, Function.comp]
  rw [add_comm]

end

end List

namespace Finset

variable [DecidableEq α] [Fintype α]

theorem exists_cycleOn (s : Finset α) :
    ∃ f : Perm α, f.IsCycleOn s ∧ f.support ⊆ s := by
  refine ⟨s.toList.formPerm, ?_, fun x hx => by
    simpa using List.mem_of_formPerm_apply_ne (Perm.mem_support.1 hx)⟩
  convert s.nodup_toList.isCycleOn_formPerm
  simp

end Finset

namespace Set

variable {f : Perm α} {s : Set α}

theorem Countable.exists_cycleOn (hs : s.Countable) :
    ∃ f : Perm α, f.IsCycleOn s ∧ { x | f x ≠ x } ⊆ s := by
  classical
  obtain hs' | hs' := s.finite_or_infinite
  · refine ⟨hs'.toFinset.toList.formPerm, ?_, fun x hx => by
      simpa using List.mem_of_formPerm_apply_ne hx⟩
    convert hs'.toFinset.nodup_toList.isCycleOn_formPerm
    simp
  · haveI := hs.to_subtype
    haveI := hs'.to_subtype
    obtain ⟨f⟩ : Nonempty (ℤ ≃ s) := inferInstance
    refine ⟨(Equiv.addRight 1).extendDomain f, ?_, fun x hx =>
      of_not_not fun h => hx <| Perm.extendDomain_apply_not_subtype _ _ h⟩
    convert Int.addRight_one_isCycle.isCycleOn.extendDomain f
    rw [Set.image_comp, Equiv.image_eq_preimage]
    ext
    simp

theorem prod_self_eq_iUnion_perm (hf : f.IsCycleOn s) :
    s ×ˢ s = ⋃ n : ℤ, (fun a => (a, (f ^ n) a)) '' s := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_image]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, rfl⟩ := hf.2 hx.1 hx.2
    exact ⟨_, _, hx.1, rfl⟩
  · rintro ⟨n, a, ha, ⟨⟩⟩
    exact ⟨ha, (hf.1.perm_zpow _).mapsTo ha⟩

end Set

namespace Finset

variable {f : Perm α} {s : Finset α}

theorem product_self_eq_disjiUnion_perm_aux (hf : f.IsCycleOn s) :
    (range #s : Set ℕ).PairwiseDisjoint fun k =>
      s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr_arg Prod.fst⟩ := by
  obtain hs | _ := (s : Set α).subsingleton_or_nontrivial
  · refine Set.Subsingleton.pairwise ?_ _
    simp_rw [Set.Subsingleton, mem_coe, ← card_le_one] at hs ⊢
    rwa [card_range]
  classical
    rintro m hm n hn hmn
    simp only [disjoint_left, Function.onFun, mem_map, Function.Embedding.coeFn_mk,
      not_exists, not_and, forall_exists_index, and_imp, Prod.forall, Prod.mk_inj]
    rintro _ _ _ - rfl rfl a ha rfl h
    rw [hf.pow_apply_eq_pow_apply ha] at h
    rw [mem_coe, mem_range] at hm hn
    exact hmn.symm (h.eq_of_lt_of_lt hn hm)

/-- We can partition the square `s ×ˢ s` into shifted diagonals as such:
```
01234
40123
34012
23401
12340
```

The diagonals are given by the cycle `f`.
-/
theorem product_self_eq_disjiUnion_perm (hf : f.IsCycleOn s) :
    s ×ˢ s =
      (range #s).disjiUnion
        (fun k => s.map ⟨fun i => (i, (f ^ k) i), fun _ _ => congr_arg Prod.fst⟩)
        (product_self_eq_disjiUnion_perm_aux hf) := by
  ext ⟨a, b⟩
  simp only [mem_product, Equiv.Perm.coe_pow, mem_disjiUnion, mem_range, mem_map,
    Function.Embedding.coeFn_mk, Prod.mk_inj]
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨n, hn, rfl⟩ := hf.exists_pow_eq hx.1 hx.2
    exact ⟨n, hn, a, hx.1, rfl, by rw [f.iterate_eq_pow]⟩
  · rintro ⟨n, -, a, ha, rfl, rfl⟩
    exact ⟨ha, (hf.1.iterate _).mapsTo ha⟩

end Finset

namespace Finset

variable [Semiring α] [AddCommMonoid β] [Module α β] {s : Finset ι} {σ : Perm ι}

theorem sum_smul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f : ι → α) (g : ι → β) :
    (∑ i ∈ s, f i) • ∑ i ∈ s, g i = ∑ k ∈ range #s, ∑ i ∈ s, f i • g ((σ ^ k) i) := by
  rw [sum_smul_sum, ← sum_product']
  simp_rw [product_self_eq_disjiUnion_perm hσ, sum_disjiUnion, sum_map, Embedding.coeFn_mk]

theorem sum_mul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f g : ι → α) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, g i) = ∑ k ∈ range #s, ∑ i ∈ s, f i * g ((σ ^ k) i) :=
  sum_smul_sum_eq_sum_perm hσ f g

end Finset

namespace Equiv.Perm

theorem subtypePerm_apply_pow_of_mem {g : Perm α} {s : Finset α}
    (hs : ∀ x : α, g x ∈ s ↔ x ∈ s) {n : ℕ} {x : α} (hx : x ∈ s) :
    ((g.subtypePerm hs ^ n) (⟨x, hx⟩ : s) : α) = (g ^ n) x := by
  simp only [subtypePerm_pow, subtypePerm_apply]

theorem subtypePerm_apply_zpow_of_mem {g : Perm α} {s : Finset α}
    (hs : ∀ x : α, g x ∈ s ↔ x ∈ s) {i : ℤ} {x : α} (hx : x ∈ s) :
    ((g.subtypePerm hs ^ i) (⟨x, hx⟩ : s) : α) = (g ^ i) x := by
  simp only [subtypePerm_zpow, subtypePerm_apply]

variable [Fintype α] [DecidableEq α]

/-- Restrict a permutation to its support -/
def subtypePermOfSupport (c : Perm α) : Perm c.support :=
  subtypePerm c fun _ : α => apply_mem_support

/-- Restrict a permutation to a Finset containing its support -/
def subtypePerm_of_support_le (c : Perm α) {s : Finset α}
    (hcs : c.support ⊆ s) : Equiv.Perm s :=
  subtypePerm c (isInvariant_of_support_le hcs)

/-- Support of a cycle is nonempty -/
theorem IsCycle.nonempty_support {g : Perm α} (hg : g.IsCycle) :
    g.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty, ne_eq, support_eq_empty_iff]
  exact IsCycle.ne_one hg

/-- Centralizer of a cycle is a power of that cycle on the cycle -/
theorem IsCycle.commute_iff' {g c : Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, g x ∈ c.support ↔ x ∈ c.support,
        subtypePerm g hc' ∈ Subgroup.zpowers c.subtypePermOfSupport := by
  constructor
  · intro hgc
    have hgc' := mem_support_iff_of_commute hgc
    use hgc'
    obtain ⟨a, ha⟩ := IsCycle.nonempty_support hc
    obtain ⟨i, hi⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp ((hgc' a).mpr ha))
    use i
    ext ⟨x, hx⟩
    simp only [subtypePermOfSupport, Subtype.coe_mk, subtypePerm_apply]
    rw [subtypePerm_apply_zpow_of_mem]
    obtain ⟨j, rfl⟩ := hc.sameCycle (mem_support.mp ha) (mem_support.mp hx)
    simp only [← mul_apply, Commute.eq (Commute.zpow_right hgc j)]
    rw [← zpow_add, add_comm i j, zpow_add]
    simp only [mul_apply, EmbeddingLike.apply_eq_iff_eq]
    exact hi
  · rintro ⟨hc', ⟨i, hi⟩⟩
    ext x
    simp only [coe_mul, Function.comp_apply]
    by_cases hx : x ∈ c.support
    · suffices hi' : ∀ x ∈ c.support, g x = (c ^ i) x by
        rw [hi' x hx, hi' (c x) (apply_mem_support.mpr hx)]
        simp only [← mul_apply, ← zpow_add_one, ← zpow_one_add, add_comm]
      intro x hx
      have hix := Perm.congr_fun hi ⟨x, hx⟩
      simp only [← Subtype.coe_inj, subtypePermOfSupport, subtypePerm_apply,
        subtypePerm_apply_zpow_of_mem] at hix
      exact hix.symm
    · rw [notMem_support.mp hx, eq_comm, ← notMem_support]
      contrapose! hx
      exact (hc' x).mp hx

/-- A permutation `g` commutes with a cycle `c` if and only if
  `c.support` is invariant under `g`, and `g` acts on it as a power of `c`. -/
theorem IsCycle.commute_iff {g c : Perm α} (hc : c.IsCycle) :
    Commute g c ↔
      ∃ hc' : ∀ x : α, g x ∈ c.support ↔ x ∈ c.support,
        ofSubtype (subtypePerm g hc') ∈ Subgroup.zpowers c := by
  simp_rw [hc.commute_iff', Subgroup.mem_zpowers_iff]
  refine exists_congr fun hc' => exists_congr fun k => ?_
  rw [subtypePermOfSupport, subtypePerm_zpow c k]
  simp only [Perm.ext_iff, subtypePerm_apply, Subtype.mk.injEq, Subtype.forall]
  apply forall_congr'
  intro a
  by_cases ha : a ∈ c.support
  · rw [imp_iff_right ha, ofSubtype_subtypePerm_of_mem hc' ha]
  · rw [iff_true_left (fun b ↦ (ha b).elim), ofSubtype_apply_of_not_mem, ← notMem_support]
    · exact Finset.notMem_mono (support_zpow_le c k) ha
    · exact ha

theorem zpow_eq_ofSubtype_subtypePerm_iff
    {g c : Equiv.Perm α} {s : Finset α}
    (hg : ∀ x, g x ∈ s ↔ x ∈ s) (hc : c.support ⊆ s) (n : ℤ) :
    c ^ n = ofSubtype (g.subtypePerm hg) ↔
      c.subtypePerm (isInvariant_of_support_le hc) ^ n = g.subtypePerm hg := by
  constructor
  · intro h
    ext ⟨x, hx⟩
    simp only [Perm.congr_fun h x, subtypePerm_apply_zpow_of_mem, Subtype.coe_mk, subtypePerm_apply]
    rw [ofSubtype_apply_of_mem]
    · simp only [Subtype.coe_mk, subtypePerm_apply]
    · exact hx
  · intro h; ext x
    rw [← h]
    by_cases hx : x ∈ s
    · rw [ofSubtype_apply_of_mem (subtypePerm c _ ^ n) hx,
        subtypePerm_zpow, subtypePerm_apply]
    · rw [ofSubtype_apply_of_not_mem (subtypePerm c _ ^ n) hx,
        ← notMem_support]
      exact fun hx' ↦ hx (hc (support_zpow_le _ _ hx'))

theorem cycle_zpow_mem_support_iff {g : Perm α}
    (hg : g.IsCycle) {n : ℤ} {x : α} (hx : g x ≠ x) :
    (g ^ n) x = x ↔ n % #g.support = 0 := by
  set q := n / #g.support
  set r := n % #g.support
  have div_euc : r + #g.support * q = n ∧ 0 ≤ r ∧ r < #g.support := by
    rw [← Int.ediv_emod_unique _]
    · exact ⟨rfl, rfl⟩
    simp only [Int.natCast_pos]
    apply lt_of_lt_of_le _ (IsCycle.two_le_card_support hg); simp
  simp only [← hg.orderOf] at div_euc
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le div_euc.2.1
  simp only [hm, Nat.cast_nonneg, Nat.cast_lt, true_and] at div_euc
  rw [← div_euc.1, zpow_add g]
  simp only [hm, Nat.cast_eq_zero, zpow_natCast, coe_mul, comp_apply, zpow_mul,
    pow_orderOf_eq_one, one_zpow, coe_one, id_eq]
  have : (g ^ m) x = x ↔ g ^ m = 1 := by
    constructor
    · intro hgm
      simp only [IsCycle.pow_eq_one_iff hg]
      use x
    · intro hgm
      simp only [hgm, coe_one, id_eq]
  rw [this]
  by_cases hm0 : m = 0
  · simp only [hm0, pow_zero]
  · simp only [hm0, iff_false]
    exact pow_ne_one_of_lt_orderOf hm0 div_euc.2

end Perm

end Equiv
