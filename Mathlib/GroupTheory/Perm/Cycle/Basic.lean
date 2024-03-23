/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yaël Dillies
-/

import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Finite
import Mathlib.GroupTheory.Perm.List

#align_import group_theory.perm.cycle.basic from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

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

open BigOperators

variable {ι α β : Type*}

namespace Equiv.Perm

/-! ### `SameCycle` -/

section SameCycle

variable {f g : Perm α} {p : α → Prop} {x y z : α}

/-- The equivalence relation indicating that two points are in the same cycle of a permutation. -/
def SameCycle (f : Perm α) (x y : α) : Prop :=
  ∃ i : ℤ, (f ^ i) x = y
#align equiv.perm.same_cycle Equiv.Perm.SameCycle

@[refl]
theorem SameCycle.refl (f : Perm α) (x : α) : SameCycle f x x :=
  ⟨0, rfl⟩
#align equiv.perm.same_cycle.refl Equiv.Perm.SameCycle.refl

theorem SameCycle.rfl : SameCycle f x x :=
  SameCycle.refl _ _
#align equiv.perm.same_cycle.rfl Equiv.Perm.SameCycle.rfl

protected theorem _root_.Eq.sameCycle (h : x = y) (f : Perm α) : f.SameCycle x y := by rw [h]
#align eq.same_cycle Eq.sameCycle

@[symm]
theorem SameCycle.symm : SameCycle f x y → SameCycle f y x := fun ⟨i, hi⟩ =>
  ⟨-i, by rw [zpow_neg, ← hi, inv_apply_self]⟩
#align equiv.perm.same_cycle.symm Equiv.Perm.SameCycle.symm

theorem sameCycle_comm : SameCycle f x y ↔ SameCycle f y x :=
  ⟨SameCycle.symm, SameCycle.symm⟩
#align equiv.perm.same_cycle_comm Equiv.Perm.sameCycle_comm

@[trans]
theorem SameCycle.trans : SameCycle f x y → SameCycle f y z → SameCycle f x z :=
  fun ⟨i, hi⟩ ⟨j, hj⟩ => ⟨j + i, by rw [zpow_add, mul_apply, hi, hj]⟩
#align equiv.perm.same_cycle.trans Equiv.Perm.SameCycle.trans

variable (f) in
theorem SameCycle.equivalence : Equivalence (SameCycle f) :=
  ⟨SameCycle.refl f, SameCycle.symm, SameCycle.trans⟩

/-- The setoid defined by the `SameCycle` relation. -/
def SameCycle.setoid (f : Perm α) : Setoid α where
  iseqv := SameCycle.equivalence f

@[simp]
theorem sameCycle_one : SameCycle 1 x y ↔ x = y := by simp [SameCycle]
#align equiv.perm.same_cycle_one Equiv.Perm.sameCycle_one

@[simp]
theorem sameCycle_inv : SameCycle f⁻¹ x y ↔ SameCycle f x y :=
  (Equiv.neg _).exists_congr_left.trans <| by simp [SameCycle]
#align equiv.perm.same_cycle_inv Equiv.Perm.sameCycle_inv

alias ⟨SameCycle.of_inv, SameCycle.inv⟩ := sameCycle_inv
#align equiv.perm.same_cycle.of_inv Equiv.Perm.SameCycle.of_inv
#align equiv.perm.same_cycle.inv Equiv.Perm.SameCycle.inv

@[simp]
theorem sameCycle_conj : SameCycle (g * f * g⁻¹) x y ↔ SameCycle f (g⁻¹ x) (g⁻¹ y) :=
  exists_congr fun i => by simp [conj_zpow, eq_inv_iff_eq]
#align equiv.perm.same_cycle_conj Equiv.Perm.sameCycle_conj

theorem SameCycle.conj : SameCycle f x y → SameCycle (g * f * g⁻¹) (g x) (g y) := by
  simp [sameCycle_conj]
#align equiv.perm.same_cycle.conj Equiv.Perm.SameCycle.conj

theorem SameCycle.apply_eq_self_iff : SameCycle f x y → (f x = x ↔ f y = y) := fun ⟨i, hi⟩ => by
  rw [← hi, ← mul_apply, ← zpow_one_add, add_comm, zpow_add_one, mul_apply,
    (f ^ i).injective.eq_iff]
#align equiv.perm.same_cycle.apply_eq_self_iff Equiv.Perm.SameCycle.apply_eq_self_iff

theorem SameCycle.eq_of_left (h : SameCycle f x y) (hx : IsFixedPt f x) : x = y :=
  let ⟨_, hn⟩ := h
  (hx.perm_zpow _).eq.symm.trans hn
#align equiv.perm.same_cycle.eq_of_left Equiv.Perm.SameCycle.eq_of_left

theorem SameCycle.eq_of_right (h : SameCycle f x y) (hy : IsFixedPt f y) : x = y :=
  h.eq_of_left <| h.apply_eq_self_iff.2 hy
#align equiv.perm.same_cycle.eq_of_right Equiv.Perm.SameCycle.eq_of_right

@[simp]
theorem sameCycle_apply_left : SameCycle f (f x) y ↔ SameCycle f x y :=
  (Equiv.addRight 1).exists_congr_left.trans <| by
    simp [zpow_sub, SameCycle, Int.add_neg_one, Function.comp]
#align equiv.perm.same_cycle_apply_left Equiv.Perm.sameCycle_apply_left

@[simp]
theorem sameCycle_apply_right : SameCycle f x (f y) ↔ SameCycle f x y := by
  rw [sameCycle_comm, sameCycle_apply_left, sameCycle_comm]
#align equiv.perm.same_cycle_apply_right Equiv.Perm.sameCycle_apply_right

@[simp]
theorem sameCycle_inv_apply_left : SameCycle f (f⁻¹ x) y ↔ SameCycle f x y := by
  rw [← sameCycle_apply_left, apply_inv_self]
#align equiv.perm.same_cycle_inv_apply_left Equiv.Perm.sameCycle_inv_apply_left

@[simp]
theorem sameCycle_inv_apply_right : SameCycle f x (f⁻¹ y) ↔ SameCycle f x y := by
  rw [← sameCycle_apply_right, apply_inv_self]
#align equiv.perm.same_cycle_inv_apply_right Equiv.Perm.sameCycle_inv_apply_right

@[simp]
theorem sameCycle_zpow_left {n : ℤ} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y :=
  (Equiv.addRight (n : ℤ)).exists_congr_left.trans <| by simp [SameCycle, zpow_add]
#align equiv.perm.same_cycle_zpow_left Equiv.Perm.sameCycle_zpow_left

@[simp]
theorem sameCycle_zpow_right {n : ℤ} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [sameCycle_comm, sameCycle_zpow_left, sameCycle_comm]
#align equiv.perm.same_cycle_zpow_right Equiv.Perm.sameCycle_zpow_right

@[simp]
theorem sameCycle_pow_left {n : ℕ} : SameCycle f ((f ^ n) x) y ↔ SameCycle f x y := by
  rw [← zpow_natCast, sameCycle_zpow_left]
#align equiv.perm.same_cycle_pow_left Equiv.Perm.sameCycle_pow_left

@[simp]
theorem sameCycle_pow_right {n : ℕ} : SameCycle f x ((f ^ n) y) ↔ SameCycle f x y := by
  rw [← zpow_natCast, sameCycle_zpow_right]
#align equiv.perm.same_cycle_pow_right Equiv.Perm.sameCycle_pow_right

alias ⟨SameCycle.of_apply_left, SameCycle.apply_left⟩ := sameCycle_apply_left
#align equiv.perm.same_cycle.of_apply_left Equiv.Perm.SameCycle.of_apply_left
#align equiv.perm.same_cycle.apply_left Equiv.Perm.SameCycle.apply_left

alias ⟨SameCycle.of_apply_right, SameCycle.apply_right⟩ := sameCycle_apply_right
#align equiv.perm.same_cycle.of_apply_right Equiv.Perm.SameCycle.of_apply_right
#align equiv.perm.same_cycle.apply_right Equiv.Perm.SameCycle.apply_right

alias ⟨SameCycle.of_inv_apply_left, SameCycle.inv_apply_left⟩ := sameCycle_inv_apply_left
#align equiv.perm.same_cycle.of_inv_apply_left Equiv.Perm.SameCycle.of_inv_apply_left
#align equiv.perm.same_cycle.inv_apply_left Equiv.Perm.SameCycle.inv_apply_left

alias ⟨SameCycle.of_inv_apply_right, SameCycle.inv_apply_right⟩ := sameCycle_inv_apply_right
#align equiv.perm.same_cycle.of_inv_apply_right Equiv.Perm.SameCycle.of_inv_apply_right
#align equiv.perm.same_cycle.inv_apply_right Equiv.Perm.SameCycle.inv_apply_right

alias ⟨SameCycle.of_pow_left, SameCycle.pow_left⟩ := sameCycle_pow_left
#align equiv.perm.same_cycle.of_pow_left Equiv.Perm.SameCycle.of_pow_left
#align equiv.perm.same_cycle.pow_left Equiv.Perm.SameCycle.pow_left

alias ⟨SameCycle.of_pow_right, SameCycle.pow_right⟩ := sameCycle_pow_right
#align equiv.perm.same_cycle.of_pow_right Equiv.Perm.SameCycle.of_pow_right
#align equiv.perm.same_cycle.pow_right Equiv.Perm.SameCycle.pow_right

alias ⟨SameCycle.of_zpow_left, SameCycle.zpow_left⟩ := sameCycle_zpow_left
#align equiv.perm.same_cycle.of_zpow_left Equiv.Perm.SameCycle.of_zpow_left
#align equiv.perm.same_cycle.zpow_left Equiv.Perm.SameCycle.zpow_left

alias ⟨SameCycle.of_zpow_right, SameCycle.zpow_right⟩ := sameCycle_zpow_right
#align equiv.perm.same_cycle.of_zpow_right Equiv.Perm.SameCycle.of_zpow_right
#align equiv.perm.same_cycle.zpow_right Equiv.Perm.SameCycle.zpow_right

theorem SameCycle.of_pow {n : ℕ} : SameCycle (f ^ n) x y → SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩
#align equiv.perm.same_cycle.of_pow Equiv.Perm.SameCycle.of_pow

theorem SameCycle.of_zpow {n : ℤ} : SameCycle (f ^ n) x y → SameCycle f x y := fun ⟨m, h⟩ =>
  ⟨n * m, by simp [zpow_mul, h]⟩
#align equiv.perm.same_cycle.of_zpow Equiv.Perm.SameCycle.of_zpow

@[simp]
theorem sameCycle_subtypePerm {h} {x y : { x // p x }} :
    (f.subtypePerm h).SameCycle x y ↔ f.SameCycle x y :=
  exists_congr fun n => by simp [Subtype.ext_iff]
#align equiv.perm.same_cycle_subtype_perm Equiv.Perm.sameCycle_subtypePerm

alias ⟨_, SameCycle.subtypePerm⟩ := sameCycle_subtypePerm
#align equiv.perm.same_cycle.subtype_perm Equiv.Perm.SameCycle.subtypePerm

@[simp]
theorem sameCycle_extendDomain {p : β → Prop} [DecidablePred p] {f : α ≃ Subtype p} :
    SameCycle (g.extendDomain f) (f x) (f y) ↔ g.SameCycle x y :=
  exists_congr fun n => by
    rw [← extendDomain_zpow, extendDomain_apply_image, Subtype.coe_inj, f.injective.eq_iff]
#align equiv.perm.same_cycle_extend_domain Equiv.Perm.sameCycle_extendDomain

alias ⟨_, SameCycle.extendDomain⟩ := sameCycle_extendDomain
#align equiv.perm.same_cycle.extend_domain Equiv.Perm.SameCycle.extendDomain

theorem SameCycle.exists_pow_eq' [Finite α] : SameCycle f x y → ∃ i < orderOf f, (f ^ i) x = y := by
  classical
    rintro ⟨k, rfl⟩
    use (k % orderOf f).natAbs
    have h₀ := Int.coe_nat_pos.mpr (orderOf_pos f)
    have h₁ := Int.emod_nonneg k h₀.ne'
    rw [← zpow_natCast, Int.natAbs_of_nonneg h₁, zpow_mod_orderOf]
    refine' ⟨_, by rfl⟩
    rw [← Int.ofNat_lt, Int.natAbs_of_nonneg h₁]
    exact Int.emod_lt_of_pos _ h₀
#align equiv.perm.same_cycle.exists_pow_eq' Equiv.Perm.SameCycle.exists_pow_eq'

theorem SameCycle.exists_pow_eq'' [Finite α] (h : SameCycle f x y) :
    ∃ i : ℕ, 0 < i ∧ i ≤ orderOf f ∧ (f ^ i) x = y := by
  classical
    obtain ⟨_ | i, hi, rfl⟩ := h.exists_pow_eq'
    · refine' ⟨orderOf f, orderOf_pos f, le_rfl, _⟩
      rw [pow_orderOf_eq_one, pow_zero]
    · exact ⟨i.succ, i.zero_lt_succ, hi.le, by rfl⟩
#align equiv.perm.same_cycle.exists_pow_eq'' Equiv.Perm.SameCycle.exists_pow_eq''

instance [Fintype α] [DecidableEq α] (f : Perm α) : DecidableRel (SameCycle f) := fun x y =>
  decidable_of_iff (∃ n ∈ List.range (Fintype.card (Perm α)), (f ^ n) x = y)
    ⟨fun ⟨n, _, hn⟩ => ⟨n, hn⟩, fun ⟨i, hi⟩ => ⟨(i % orderOf f).natAbs,
      List.mem_range.2 (Int.ofNat_lt.1 <| by
        rw [Int.natAbs_of_nonneg (Int.emod_nonneg _ <| Int.coe_nat_ne_zero.2 (orderOf_pos _).ne')]
        · refine' (Int.emod_lt _ <| Int.coe_nat_ne_zero_iff_pos.2 <| orderOf_pos _).trans_le _
          simp [orderOf_le_card_univ]),
      by
        rw [← zpow_natCast, Int.natAbs_of_nonneg (Int.emod_nonneg _ <|
          Int.coe_nat_ne_zero_iff_pos.2 <| orderOf_pos _), zpow_mod_orderOf, hi]⟩⟩

end SameCycle

/-!
### `IsCycle`
-/

section IsCycle

variable {f g : Perm α} {x y : α}

/-- A cycle is a non identity permutation where any two nonfixed points of the permutation are
related by repeated application of the permutation. -/
def IsCycle (f : Perm α) : Prop :=
  ∃ x, f x ≠ x ∧ ∀ ⦃y⦄, f y ≠ y → SameCycle f x y
#align equiv.perm.is_cycle Equiv.Perm.IsCycle

theorem IsCycle.ne_one (h : IsCycle f) : f ≠ 1 := fun hf => by simp [hf, IsCycle] at h
#align equiv.perm.is_cycle.ne_one Equiv.Perm.IsCycle.ne_one

@[simp]
theorem not_isCycle_one : ¬(1 : Perm α).IsCycle := fun H => H.ne_one rfl
#align equiv.perm.not_is_cycle_one Equiv.Perm.not_isCycle_one

protected theorem IsCycle.sameCycle (hf : IsCycle f) (hx : f x ≠ x) (hy : f y ≠ y) :
    SameCycle f x y :=
  let ⟨g, hg⟩ := hf
  let ⟨a, ha⟩ := hg.2 hx
  let ⟨b, hb⟩ := hg.2 hy
  ⟨b - a, by rw [← ha, ← mul_apply, ← zpow_add, sub_add_cancel, hb]⟩
#align equiv.perm.is_cycle.same_cycle Equiv.Perm.IsCycle.sameCycle

theorem IsCycle.exists_zpow_eq : IsCycle f → f x ≠ x → f y ≠ y → ∃ i : ℤ, (f ^ i) x = y :=
  IsCycle.sameCycle
#align equiv.perm.is_cycle.exists_zpow_eq Equiv.Perm.IsCycle.exists_zpow_eq

theorem IsCycle.inv (hf : IsCycle f) : IsCycle f⁻¹ :=
  hf.imp fun _ ⟨hx, h⟩ =>
    ⟨inv_eq_iff_eq.not.2 hx.symm, fun _ hy => (h <| inv_eq_iff_eq.not.2 hy.symm).inv⟩
#align equiv.perm.is_cycle.inv Equiv.Perm.IsCycle.inv

@[simp]
theorem isCycle_inv : IsCycle f⁻¹ ↔ IsCycle f :=
  ⟨fun h => h.inv, IsCycle.inv⟩
#align equiv.perm.is_cycle_inv Equiv.Perm.isCycle_inv

theorem IsCycle.conj : IsCycle f → IsCycle (g * f * g⁻¹) := by
  rintro ⟨x, hx, h⟩
  refine' ⟨g x, by simp [coe_mul, inv_apply_self, hx], fun y hy => _⟩
  rw [← apply_inv_self g y]
  exact (h <| eq_inv_iff_eq.not.2 hy).conj
#align equiv.perm.is_cycle.conj Equiv.Perm.IsCycle.conj

protected theorem IsCycle.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p) :
    IsCycle g → IsCycle (g.extendDomain f) := by
  rintro ⟨a, ha, ha'⟩
  refine' ⟨f a, _, fun b hb => _⟩
  · rw [extendDomain_apply_image]
    exact Subtype.coe_injective.ne (f.injective.ne ha)
  have h : b = f (f.symm ⟨b, of_not_not <| hb ∘ extendDomain_apply_not_subtype _ _⟩) := by
    rw [apply_symm_apply, Subtype.coe_mk]
  rw [h] at hb ⊢
  simp only [extendDomain_apply_image, Subtype.coe_injective.ne_iff, f.injective.ne_iff] at hb
  exact (ha' hb).extendDomain
#align equiv.perm.is_cycle.extend_domain Equiv.Perm.IsCycle.extendDomain

theorem isCycle_iff_sameCycle (hx : f x ≠ x) : IsCycle f ↔ ∀ {y}, SameCycle f x y ↔ f y ≠ y :=
  ⟨fun hf y =>
    ⟨fun ⟨i, hi⟩ hy =>
      hx <| by
        rw [← zpow_apply_eq_self_of_apply_eq_self hy i, (f ^ i).injective.eq_iff] at hi
        rw [hi, hy],
      hf.exists_zpow_eq hx⟩,
    fun h => ⟨x, hx, fun y hy => h.2 hy⟩⟩
#align equiv.perm.is_cycle_iff_same_cycle Equiv.Perm.isCycle_iff_sameCycle

section Finite

variable [Finite α]

theorem IsCycle.exists_pow_eq (hf : IsCycle f) (hx : f x ≠ x) (hy : f y ≠ y) :
    ∃ i : ℕ, (f ^ i) x = y := by
  let ⟨n, hn⟩ := hf.exists_zpow_eq hx hy
  classical exact
      ⟨(n % orderOf f).toNat, by
        {have := n.emod_nonneg (Int.coe_nat_ne_zero.mpr (ne_of_gt (orderOf_pos f)))
         rwa [← zpow_natCast, Int.toNat_of_nonneg this, zpow_mod_orderOf]}⟩
#align equiv.perm.is_cycle.exists_pow_eq Equiv.Perm.IsCycle.exists_pow_eq

end Finite

variable [DecidableEq α]

theorem isCycle_swap (hxy : x ≠ y) : IsCycle (swap x y) :=
  ⟨y, by rwa [swap_apply_right], fun a (ha : ite (a = x) y (ite (a = y) x a) ≠ a) =>
    if hya : y = a then ⟨0, hya⟩
    else
      ⟨1, by
        rw [zpow_one, swap_apply_def]
        split_ifs at * <;> tauto⟩⟩
#align equiv.perm.is_cycle_swap Equiv.Perm.isCycle_swap

protected theorem IsSwap.isCycle : IsSwap f → IsCycle f := by
  rintro ⟨x, y, hxy, rfl⟩
  exact isCycle_swap hxy
#align equiv.perm.is_swap.is_cycle Equiv.Perm.IsSwap.isCycle

variable [Fintype α]

theorem IsCycle.two_le_card_support (h : IsCycle f) : 2 ≤ f.support.card :=
  two_le_card_support_of_ne_one h.ne_one
#align equiv.perm.is_cycle.two_le_card_support Equiv.Perm.IsCycle.two_le_card_support

#noalign equiv.perm.is_cycle.exists_pow_eq_one

/-- The subgroup generated by a cycle is in bijection with its support -/
noncomputable def IsCycle.zpowersEquivSupport {σ : Perm α} (hσ : IsCycle σ) :
    (Subgroup.zpowers σ) ≃ σ.support :=
  Equiv.ofBijective
    (fun (τ : ↥ ((Subgroup.zpowers σ) : Set (Perm α))) =>
      ⟨(τ : Perm α) (Classical.choose hσ), by
        obtain ⟨τ, n, rfl⟩ := τ
        erw [Finset.mem_coe, Subtype.coe_mk, zpow_apply_mem_support, mem_support]
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
        erw [Finset.mem_coe, mem_support] at hy
        obtain ⟨n, rfl⟩ := (Classical.choose_spec hσ).2 hy
        exact ⟨⟨σ ^ n, n, rfl⟩, rfl⟩)
#align equiv.perm.is_cycle.zpowers_equiv_support Equiv.Perm.IsCycle.zpowersEquivSupport

@[simp]
theorem IsCycle.zpowersEquivSupport_apply {σ : Perm α} (hσ : IsCycle σ) {n : ℕ} :
    hσ.zpowersEquivSupport ⟨σ ^ n, n, rfl⟩ =
      ⟨(σ ^ n) (Classical.choose hσ),
        pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ :=
  rfl
#align equiv.perm.is_cycle.zpowers_equiv_support_apply Equiv.Perm.IsCycle.zpowersEquivSupport_apply

@[simp]
theorem IsCycle.zpowersEquivSupport_symm_apply {σ : Perm α} (hσ : IsCycle σ) (n : ℕ) :
    hσ.zpowersEquivSupport.symm
        ⟨(σ ^ n) (Classical.choose hσ),
          pow_apply_mem_support.2 (mem_support.2 (Classical.choose_spec hσ).1)⟩ =
      ⟨σ ^ n, n, rfl⟩ :=
  (Equiv.symm_apply_eq _).2 hσ.zpowersEquivSupport_apply
#align equiv.perm.is_cycle.zpowers_equiv_support_symm_apply Equiv.Perm.IsCycle.zpowersEquivSupport_symm_apply

protected theorem IsCycle.orderOf (hf : IsCycle f) : orderOf f = f.support.card := by
  rw [← Fintype.card_zpowers, ← Fintype.card_coe]
  convert Fintype.card_congr (IsCycle.zpowersEquivSupport hf)
#align equiv.perm.is_cycle.order_of Equiv.Perm.IsCycle.orderOf

theorem isCycle_swap_mul_aux₁ {α : Type*} [DecidableEq α] :
    ∀ (n : ℕ) {b x : α} {f : Perm α} (_ : (swap x (f x) * f) b ≠ b) (_ : (f ^ n) (f x) = b),
      ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b := by
  intro n
  induction' n with n hn
  · exact fun _ h => ⟨0, h⟩
  · intro b x f hb h
    exact if hfbx : f x = b then ⟨0, hfbx⟩
      else
        have : f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb
        have hb' : (swap x (f x) * f) (f⁻¹ b) ≠ f⁻¹ b := by
          rw [mul_apply, apply_inv_self, swap_apply_of_ne_of_ne this.2 (Ne.symm hfbx), Ne.def, ←
            f.injective.eq_iff, apply_inv_self]
          exact this.1
        let ⟨i, hi⟩ := hn hb' (f.injective <| by
          rw [apply_inv_self]; rwa [pow_succ, mul_apply] at h)
        ⟨i + 1, by
          rw [add_comm, zpow_add, mul_apply, hi, zpow_one, mul_apply, apply_inv_self,
            swap_apply_of_ne_of_ne (ne_and_ne_of_swap_mul_apply_ne_self hb).2 (Ne.symm hfbx)]⟩
#align equiv.perm.is_cycle_swap_mul_aux₁ Equiv.Perm.isCycle_swap_mul_aux₁

theorem isCycle_swap_mul_aux₂ {α : Type*} [DecidableEq α] :
    ∀ (n : ℤ) {b x : α} {f : Perm α} (_ : (swap x (f x) * f) b ≠ b) (_ : (f ^ n) (f x) = b),
      ∃ i : ℤ, ((swap x (f x) * f) ^ i) (f x) = b := by
  intro n
  induction' n with n n
  · exact isCycle_swap_mul_aux₁ n
  · intro b x f hb h
    exact if hfbx' : f x = b then ⟨0, hfbx'⟩
      else
        have : f b ≠ b ∧ b ≠ x := ne_and_ne_of_swap_mul_apply_ne_self hb
        have hb : (swap x (f⁻¹ x) * f⁻¹) (f⁻¹ b) ≠ f⁻¹ b := by
          rw [mul_apply, swap_apply_def]
          split_ifs <;>
              simp only [inv_eq_iff_eq, Perm.mul_apply, zpow_negSucc,
                Ne.def, Perm.apply_inv_self] at
                * <;> tauto
        let ⟨i, hi⟩ :=
          isCycle_swap_mul_aux₁ n hb
            (show (f⁻¹ ^ n) (f⁻¹ x) = f⁻¹ b by
              rw [← zpow_natCast, ← h, ← mul_apply, ← mul_apply, ← mul_apply, zpow_negSucc,
                ← inv_pow, pow_succ', mul_assoc, mul_assoc, inv_mul_self, mul_one, zpow_natCast,
                ← pow_succ', ← pow_succ])
        have h : (swap x (f⁻¹ x) * f⁻¹) (f x) = f⁻¹ x := by
          rw [mul_apply, inv_apply_self, swap_apply_left]
        ⟨-i, by
          rw [← add_sub_cancel_right i 1, neg_sub, sub_eq_add_neg, zpow_add, zpow_one, zpow_neg,
            ← inv_zpow, mul_inv_rev, swap_inv, mul_swap_eq_swap_mul, inv_apply_self, swap_comm _ x,
            zpow_add, zpow_one, mul_apply, mul_apply (_ ^ i), h, hi, mul_apply, apply_inv_self,
            swap_apply_of_ne_of_ne this.2 (Ne.symm hfbx')]⟩
#align equiv.perm.is_cycle_swap_mul_aux₂ Equiv.Perm.isCycle_swap_mul_aux₂

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
        refine' by_contradiction fun hy => _
        cases' hz.2 hy with j hj
        rw [← sub_add_cancel j i, zpow_add, mul_apply, hi] at hj
        cases' zpow_apply_eq_of_apply_apply_eq_self hffx (j - i) with hji hji
        · rw [← hj, hji] at hyx
          tauto
        · rw [← hj, hji] at hfyx
          tauto
#align equiv.perm.is_cycle.eq_swap_of_apply_apply_eq_self Equiv.Perm.IsCycle.eq_swap_of_apply_apply_eq_self

theorem IsCycle.swap_mul {α : Type*} [DecidableEq α] {f : Perm α} (hf : IsCycle f) {x : α}
    (hx : f x ≠ x) (hffx : f (f x) ≠ x) : IsCycle (swap x (f x) * f) :=
  ⟨f x, by simp [swap_apply_def, mul_apply, if_neg hffx, f.injective.eq_iff, if_neg hx, hx],
    fun y hy =>
    let ⟨i, hi⟩ := hf.exists_zpow_eq hx (ne_and_ne_of_swap_mul_apply_ne_self hy).1
    -- Porting note: Needed to add Perm α typehint, otherwise does not know how to coerce to fun
    have hi : (f ^ (i - 1) : Perm α) (f x) = y :=
      calc
        (f ^ (i - 1) : Perm α) (f x) = (f ^ (i - 1) * f ^ (1 : ℤ) : Perm α) x := by simp
        _ = y := by rwa [← zpow_add, sub_add_cancel]

    isCycle_swap_mul_aux₂ (i - 1) hy hi⟩
#align equiv.perm.is_cycle.swap_mul Equiv.Perm.IsCycle.swap_mul

theorem IsCycle.sign {f : Perm α} (hf : IsCycle f) : sign f = -(-1) ^ f.support.card :=
  let ⟨x, hx⟩ := hf
  calc
    Perm.sign f = Perm.sign (swap x (f x) * (swap x (f x) * f)) := by
      {rw [← mul_assoc, mul_def, mul_def, swap_swap, trans_refl]}
    _ = -(-1) ^ f.support.card :=
      if h1 : f (f x) = x then by
        have h : swap x (f x) * f = 1 := by
          simp only [mul_def, one_def]
          rw [hf.eq_swap_of_apply_apply_eq_self hx.1 h1, swap_apply_left, swap_swap]
        rw [sign_mul, sign_swap hx.1.symm, h, sign_one,
          hf.eq_swap_of_apply_apply_eq_self hx.1 h1, card_support_swap hx.1.symm]
        rfl
      else by
        have h : card (support (swap x (f x) * f)) + 1 = card (support f) := by
          rw [← insert_erase (mem_support.2 hx.1), support_swap_mul_eq _ _ h1,
            card_insert_of_not_mem (not_mem_erase _ _), sdiff_singleton_eq_erase]
        have : card (support (swap x (f x) * f)) < card (support f) :=
          card_support_swap_mul hx.1
        rw [sign_mul, sign_swap hx.1.symm, (hf.swap_mul hx.1 h1).sign, ← h]
        simp only [mul_neg, neg_mul, one_mul, neg_neg, pow_add, pow_one, mul_one]
termination_by f.support.card
#align equiv.perm.is_cycle.sign Equiv.Perm.IsCycle.sign

theorem IsCycle.of_pow {n : ℕ} (h1 : IsCycle (f ^ n)) (h2 : f.support ⊆ (f ^ n).support) :
    IsCycle f := by
  have key : ∀ x : α, (f ^ n) x ≠ x ↔ f x ≠ x := by
    simp_rw [← mem_support, ← Finset.ext_iff]
    exact (support_pow_le _ n).antisymm h2
  obtain ⟨x, hx1, hx2⟩ := h1
  refine' ⟨x, (key x).mp hx1, fun y hy => _⟩
  cases' hx2 ((key y).mpr hy) with i _
  exact ⟨n * i, by rwa [zpow_mul]⟩
#align equiv.perm.is_cycle.of_pow Equiv.Perm.IsCycle.of_pow

-- The lemma `support_zpow_le` is relevant. It means that `h2` is equivalent to
-- `σ.support = (σ ^ n).support`, as well as to `σ.support.card ≤ (σ ^ n).support.card`.
theorem IsCycle.of_zpow {n : ℤ} (h1 : IsCycle (f ^ n)) (h2 : f.support ⊆ (f ^ n).support) :
    IsCycle f := by
  cases n
  · exact h1.of_pow h2
  · simp only [le_eq_subset, zpow_negSucc, Perm.support_inv] at h1 h2
    exact (inv_inv (f ^ _) ▸ h1.inv).of_pow h2
#align equiv.perm.is_cycle.of_zpow Equiv.Perm.IsCycle.of_zpow

theorem nodup_of_pairwise_disjoint_cycles {l : List (Perm β)} (h1 : ∀ f ∈ l, IsCycle f)
    (h2 : l.Pairwise Disjoint) : l.Nodup :=
  nodup_of_pairwise_disjoint (fun h => (h1 1 h).ne_one rfl) h2
#align equiv.perm.nodup_of_pairwise_disjoint_cycles Equiv.Perm.nodup_of_pairwise_disjoint_cycles

/-- Unlike `support_congr`, which assumes that `∀ (x ∈ g.support), f x = g x)`, here
we have the weaker assumption that `∀ (x ∈ f.support), f x = g x`. -/
theorem IsCycle.support_congr (hf : IsCycle f) (hg : IsCycle g) (h : f.support ⊆ g.support)
    (h' : ∀ x ∈ f.support, f x = g x) : f = g := by
  have : f.support = g.support := by
    refine' le_antisymm h _
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
  refine' Equiv.Perm.support_congr h _
  simpa [← this] using h'
#align equiv.perm.is_cycle.support_congr Equiv.Perm.IsCycle.support_congr

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
#align equiv.perm.is_cycle.eq_on_support_inter_nonempty_congr Equiv.Perm.IsCycle.eq_on_support_inter_nonempty_congr

theorem IsCycle.support_pow_eq_iff (hf : IsCycle f) {n : ℕ} :
    support (f ^ n) = support f ↔ ¬orderOf f ∣ n := by
  rw [orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h H
    refine' hf.ne_one _
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
#align equiv.perm.is_cycle.support_pow_eq_iff Equiv.Perm.IsCycle.support_pow_eq_iff

theorem IsCycle.support_pow_of_pos_of_lt_orderOf (hf : IsCycle f) {n : ℕ} (npos : 0 < n)
    (hn : n < orderOf f) : (f ^ n).support = f.support :=
  hf.support_pow_eq_iff.2 <| Nat.not_dvd_of_pos_of_lt npos hn
#align equiv.perm.is_cycle.support_pow_of_pos_of_lt_order_of Equiv.Perm.IsCycle.support_pow_of_pos_of_lt_orderOf

theorem IsCycle.pow_iff [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    IsCycle (f ^ n) ↔ n.Coprime (orderOf f) := by
  classical
    cases nonempty_fintype β
    constructor
    · intro h
      have hr : support (f ^ n) = support f := by
        rw [hf.support_pow_eq_iff]
        rintro ⟨k, rfl⟩
        refine' h.ne_one _
        simp [pow_mul, pow_orderOf_eq_one]
      have : orderOf (f ^ n) = orderOf f := by rw [h.orderOf, hr, hf.orderOf]
      rw [orderOf_pow, Nat.div_eq_self] at this
      cases' this with h
      · exact absurd h (orderOf_pos _).ne'
      · rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
    · intro h
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime h
      have hf' : IsCycle ((f ^ n) ^ m) := by rwa [hm]
      refine' hf'.of_pow fun x hx => _
      rw [hm]
      exact support_pow_le _ n hx
#align equiv.perm.is_cycle.pow_iff Equiv.Perm.IsCycle.pow_iff

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
#align equiv.perm.is_cycle.pow_eq_one_iff Equiv.Perm.IsCycle.pow_eq_one_iff

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
theorem IsCycle.pow_eq_one_iff' [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} {x : β}
    (hx : f x ≠ x) : f ^ n = 1 ↔ (f ^ n) x = x :=
  ⟨fun h => DFunLike.congr_fun h x, fun h => hf.pow_eq_one_iff.2 ⟨x, hx, h⟩⟩
#align equiv.perm.is_cycle.pow_eq_one_iff' Equiv.Perm.IsCycle.pow_eq_one_iff'

-- TODO: Define a `Set`-valued support to get rid of the `Finite β` assumption
theorem IsCycle.pow_eq_one_iff'' [Finite β] {f : Perm β} (hf : IsCycle f) {n : ℕ} :
    f ^ n = 1 ↔ ∀ x, f x ≠ x → (f ^ n) x = x :=
  ⟨fun h _ hx => (hf.pow_eq_one_iff' hx).1 h, fun h =>
    let ⟨_, hx, _⟩ := id hf
    (hf.pow_eq_one_iff' hx).2 (h _ hx)⟩
#align equiv.perm.is_cycle.pow_eq_one_iff'' Equiv.Perm.IsCycle.pow_eq_one_iff''

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
      · exact (this hx'.symm (le_of_not_le hab)).symm
      suffices f ^ (b - a) = 1 by
        rw [pow_sub _ hab, mul_inv_eq_one] at this
        rw [this]
      rw [hf.pow_eq_one_iff]
      by_cases hfa : (f ^ a) x ∈ f.support
      · refine' ⟨(f ^ a) x, mem_support.mp hfa, _⟩
        simp only [pow_sub _ hab, Equiv.Perm.coe_mul, Function.comp_apply, inv_apply_self, ← hx']
      · have h := @Equiv.Perm.zpow_apply_comm _ f 1 a x
        simp only [zpow_one, zpow_natCast] at h
        rw [not_mem_support, h, Function.Injective.eq_iff (f ^ a).injective] at hfa
        contradiction
#align equiv.perm.is_cycle.pow_eq_pow_iff Equiv.Perm.IsCycle.pow_eq_pow_iff

theorem IsCycle.isCycle_pow_pos_of_lt_prime_order [Finite β] {f : Perm β} (hf : IsCycle f)
    (hf' : (orderOf f).Prime) (n : ℕ) (hn : 0 < n) (hn' : n < orderOf f) : IsCycle (f ^ n) := by
  classical
    cases nonempty_fintype β
    have : n.Coprime (orderOf f) := by
      refine' Nat.Coprime.symm _
      rw [Nat.Prime.coprime_iff_not_dvd hf']
      exact Nat.not_dvd_of_pos_of_lt hn hn'
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime this
    have hf'' := hf
    rw [← hm] at hf''
    refine' hf''.of_pow _
    rw [hm]
    exact support_pow_le f n
#align equiv.perm.is_cycle.is_cycle_pow_pos_of_lt_prime_order Equiv.Perm.IsCycle.isCycle_pow_pos_of_lt_prime_order

end IsCycle

open Equiv

theorem _root_.Int.addLeft_one_isCycle : (Equiv.addLeft 1 : Perm ℤ).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩
#align int.add_left_one_is_cycle Int.addLeft_one_isCycle

theorem _root_.Int.addRight_one_isCycle : (Equiv.addRight 1 : Perm ℤ).IsCycle :=
  ⟨0, one_ne_zero, fun n _ => ⟨n, by simp⟩⟩
#align int.add_right_one_is_cycle Int.addRight_one_isCycle

section Conjugation

variable [Fintype α] [DecidableEq α] {σ τ : Perm α}

theorem IsCycle.isConj (hσ : IsCycle σ) (hτ : IsCycle τ) (h : σ.support.card = τ.support.card) :
    IsConj σ τ := by
  refine'
    isConj_of_support_equiv
      (hσ.zpowersEquivSupport.symm.trans <|
        (zpowersEquivZPowers <| by rw [hσ.orderOf, h, hτ.orderOf]).trans hτ.zpowersEquivSupport)
      _
  intro x hx
  simp only [Perm.mul_apply, Equiv.trans_apply, Equiv.sumCongr_apply]
  obtain ⟨n, rfl⟩ := hσ.exists_pow_eq (Classical.choose_spec hσ).1 (mem_support.1 hx)
  apply
    Eq.trans _
      (congr rfl (congr rfl (congr rfl (congr rfl (hσ.zpowersEquivSupport_symm_apply n).symm))))
  apply (congr rfl (congr rfl (congr rfl (hσ.zpowersEquivSupport_symm_apply (n + 1))))).trans _
  -- This used to be a `simp only` before leanprover/lean4#2644
  erw [zpowersEquivZPowers_apply, zpowersEquivZPowers_apply]
  dsimp
    -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [pow_succ, Perm.mul_apply]
#align equiv.perm.is_cycle.is_conj Equiv.Perm.IsCycle.isConj

theorem IsCycle.isConj_iff (hσ : IsCycle σ) (hτ : IsCycle τ) :
    IsConj σ τ ↔ σ.support.card = τ.support.card :=
  ⟨by
    intro h
    obtain ⟨π, rfl⟩ := (_root_.isConj_iff).1 h
    refine' Finset.card_congr (fun a _ => π a) (fun _ ha => _) (fun _ _ _ _ ab => π.injective ab)
        fun b hb => _
    · simp [mem_support.1 ha]
    · refine' ⟨π⁻¹ b, ⟨_, π.apply_inv_self b⟩⟩
      contrapose! hb
      rw [mem_support, Classical.not_not] at hb
      rw [mem_support, Classical.not_not, Perm.mul_apply, Perm.mul_apply, hb, Perm.apply_inv_self],
    hσ.isConj hτ⟩
#align equiv.perm.is_cycle.is_conj_iff Equiv.Perm.IsCycle.isConj_iff

end Conjugation

/-! ### `IsCycleOn` -/

section IsCycleOn

variable {f g : Perm α} {s t : Set α} {a b x y : α}

/-- A permutation is a cycle on `s` when any two points of `s` are related by repeated application
of the permutation. Note that this means the identity is a cycle of subsingleton sets. -/
def IsCycleOn (f : Perm α) (s : Set α) : Prop :=
  Set.BijOn f s s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → f.SameCycle x y
#align equiv.perm.is_cycle_on Equiv.Perm.IsCycleOn

@[simp]
theorem isCycleOn_empty : f.IsCycleOn ∅ := by simp [IsCycleOn, Set.bijOn_empty]
#align equiv.perm.is_cycle_on_empty Equiv.Perm.isCycleOn_empty

@[simp]
theorem isCycleOn_one : (1 : Perm α).IsCycleOn s ↔ s.Subsingleton := by
  simp [IsCycleOn, Set.bijOn_id, Set.Subsingleton]
#align equiv.perm.is_cycle_on_one Equiv.Perm.isCycleOn_one

alias ⟨IsCycleOn.subsingleton, _root_.Set.Subsingleton.isCycleOn_one⟩ := isCycleOn_one
#align equiv.perm.is_cycle_on.subsingleton Equiv.Perm.IsCycleOn.subsingleton
#align set.subsingleton.is_cycle_on_one Set.Subsingleton.isCycleOn_one

@[simp]
theorem isCycleOn_singleton : f.IsCycleOn {a} ↔ f a = a := by simp [IsCycleOn, SameCycle.rfl]
#align equiv.perm.is_cycle_on_singleton Equiv.Perm.isCycleOn_singleton

theorem isCycleOn_of_subsingleton [Subsingleton α] (f : Perm α) (s : Set α) : f.IsCycleOn s :=
  ⟨s.bijOn_of_subsingleton _, fun x _ y _ => (Subsingleton.elim x y).sameCycle _⟩
#align equiv.perm.is_cycle_on_of_subsingleton Equiv.Perm.isCycleOn_of_subsingleton

@[simp]
theorem isCycleOn_inv : f⁻¹.IsCycleOn s ↔ f.IsCycleOn s := by
  simp only [IsCycleOn, sameCycle_inv, and_congr_left_iff]
  exact fun _ ↦ ⟨fun h ↦ Set.BijOn.perm_inv h, fun h ↦ Set.BijOn.perm_inv h⟩
#align equiv.perm.is_cycle_on_inv Equiv.Perm.isCycleOn_inv

alias ⟨IsCycleOn.of_inv, IsCycleOn.inv⟩ := isCycleOn_inv
#align equiv.perm.is_cycle_on.of_inv Equiv.Perm.IsCycleOn.of_inv
#align equiv.perm.is_cycle_on.inv Equiv.Perm.IsCycleOn.inv

theorem IsCycleOn.conj (h : f.IsCycleOn s) : (g * f * g⁻¹).IsCycleOn ((g : Perm α) '' s) :=
  ⟨(g.bijOn_image.comp h.1).comp g.bijOn_symm_image, fun x hx y hy => by
    rw [← preimage_inv] at hx hy
    convert Equiv.Perm.SameCycle.conj (h.2 hx hy) (g := g) <;> rw [apply_inv_self]⟩
#align equiv.perm.is_cycle_on.conj Equiv.Perm.IsCycleOn.conj

theorem isCycleOn_swap [DecidableEq α] (hab : a ≠ b) : (swap a b).IsCycleOn {a, b} :=
  ⟨bijOn_swap (by simp) (by simp), fun x hx y hy => by
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    obtain rfl | rfl := hx <;> obtain rfl | rfl := hy
    · exact ⟨0, by rw [zpow_zero, coe_one, id.def]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_left]⟩
    · exact ⟨1, by rw [zpow_one, swap_apply_right]⟩
    · exact ⟨0, by rw [zpow_zero, coe_one, id.def]⟩⟩
#align equiv.perm.is_cycle_on_swap Equiv.Perm.isCycleOn_swap

protected theorem IsCycleOn.apply_ne (hf : f.IsCycleOn s) (hs : s.Nontrivial) (ha : a ∈ s) :
    f a ≠ a := by
  obtain ⟨b, hb, hba⟩ := hs.exists_ne a
  obtain ⟨n, rfl⟩ := hf.2 ha hb
  exact fun h => hba (IsFixedPt.perm_zpow h n)
#align equiv.perm.is_cycle_on.apply_ne Equiv.Perm.IsCycleOn.apply_ne

protected theorem IsCycle.isCycleOn (hf : f.IsCycle) : f.IsCycleOn { x | f x ≠ x } :=
  ⟨f.bijOn fun _ => f.apply_eq_iff_eq.not, fun _ ha _ => hf.sameCycle ha⟩
#align equiv.perm.is_cycle.is_cycle_on Equiv.Perm.IsCycle.isCycleOn

/-- This lemma demonstrates the relation between `Equiv.Perm.IsCycle` and `Equiv.Perm.IsCycleOn`
in non-degenerate cases. -/
theorem isCycle_iff_exists_isCycleOn :
    f.IsCycle ↔ ∃ s : Set α, s.Nontrivial ∧ f.IsCycleOn s ∧ ∀ ⦃x⦄, ¬IsFixedPt f x → x ∈ s := by
  refine' ⟨fun hf => ⟨{ x | f x ≠ x }, _, hf.isCycleOn, fun _ => id⟩, _⟩
  · obtain ⟨a, ha⟩ := hf
    exact ⟨f a, f.injective.ne ha.1, a, ha.1, ha.1⟩
  · rintro ⟨s, hs, hf, hsf⟩
    obtain ⟨a, ha⟩ := hs.nonempty
    exact ⟨a, hf.apply_ne hs ha, fun b hb => hf.2 ha <| hsf hb⟩
#align equiv.perm.is_cycle_iff_exists_is_cycle_on Equiv.Perm.isCycle_iff_exists_isCycleOn

theorem IsCycleOn.apply_mem_iff (hf : f.IsCycleOn s) : f x ∈ s ↔ x ∈ s :=
  ⟨fun hx => by
    convert hf.1.perm_inv.1 hx
    rw [inv_apply_self], fun hx => hf.1.mapsTo hx⟩
#align equiv.perm.is_cycle_on.apply_mem_iff Equiv.Perm.IsCycleOn.apply_mem_iff

/-- Note that the identity satisfies `IsCycleOn` for any subsingleton set, but not `IsCycle`. -/
theorem IsCycleOn.isCycle_subtypePerm (hf : f.IsCycleOn s) (hs : s.Nontrivial) :
    (f.subtypePerm fun _ => hf.apply_mem_iff.symm : Perm s).IsCycle := by
  obtain ⟨a, ha⟩ := hs.nonempty
  exact
    ⟨⟨a, ha⟩, ne_of_apply_ne ((↑) : s → α) (hf.apply_ne hs ha), fun b _ =>
      (hf.2 (⟨a, ha⟩ : s).2 b.2).subtypePerm⟩
#align equiv.perm.is_cycle_on.is_cycle_subtype_perm Equiv.Perm.IsCycleOn.isCycle_subtypePerm

/-- Note that the identity is a cycle on any subsingleton set, but not a cycle. -/
protected theorem IsCycleOn.subtypePerm (hf : f.IsCycleOn s) :
    (f.subtypePerm fun _ => hf.apply_mem_iff.symm : Perm s).IsCycleOn _root_.Set.univ := by
  obtain hs | hs := s.subsingleton_or_nontrivial
  · haveI := hs.coe_sort
    exact isCycleOn_of_subsingleton _ _
  convert (hf.isCycle_subtypePerm hs).isCycleOn
  rw [eq_comm, Set.eq_univ_iff_forall]
  exact fun x => ne_of_apply_ne ((↑) : s → α) (hf.apply_ne hs x.2)
#align equiv.perm.is_cycle_on.subtype_perm Equiv.Perm.IsCycleOn.subtypePerm

-- TODO: Theory of order of an element under an action
theorem IsCycleOn.pow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) {n : ℕ} :
    (f ^ n) a = a ↔ s.card ∣ n := by
  obtain rfl | hs := Finset.eq_singleton_or_nontrivial ha
  · rw [coe_singleton, isCycleOn_singleton] at hf
    simpa using IsFixedPt.iterate hf n
  classical
    have h : ∀ x ∈ s.attach, ¬f ↑x = ↑x := fun x _ => hf.apply_ne hs x.2
    have := (hf.isCycle_subtypePerm hs).orderOf
    simp only [coe_sort_coe, support_subtype_perm, ne_eq, decide_not, Bool.not_eq_true',
      decide_eq_false_iff_not, mem_attach, forall_true_left, Subtype.forall, filter_true_of_mem h,
      card_attach] at this
    rw [← this, orderOf_dvd_iff_pow_eq_one,
      (hf.isCycle_subtypePerm hs).pow_eq_one_iff'
        (ne_of_apply_ne ((↑) : s → α) <| hf.apply_ne hs (⟨a, ha⟩ : s).2)]
    simp_rw [coe_sort_coe, subtypePerm_pow]
    -- This used to be the end of the proof before leanprover/lean4#2644
    erw [subtypePerm_apply]
    simp
#align equiv.perm.is_cycle_on.pow_apply_eq Equiv.Perm.IsCycleOn.pow_apply_eq

theorem IsCycleOn.zpow_apply_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) :
    ∀ {n : ℤ}, (f ^ n) a = a ↔ (s.card : ℤ) ∣ n
  | Int.ofNat n => (hf.pow_apply_eq ha).trans Int.coe_nat_dvd.symm
  | Int.negSucc n => by
    rw [zpow_negSucc, ← inv_pow]
    exact (hf.inv.pow_apply_eq ha).trans (dvd_neg.trans Int.coe_nat_dvd).symm
#align equiv.perm.is_cycle_on.zpow_apply_eq Equiv.Perm.IsCycleOn.zpow_apply_eq

theorem IsCycleOn.pow_apply_eq_pow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s)
    {m n : ℕ} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [MOD s.card] := by
  rw [Nat.modEq_iff_dvd, ← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_inv_iff_eq, eq_comm]
#align equiv.perm.is_cycle_on.pow_apply_eq_pow_apply Equiv.Perm.IsCycleOn.pow_apply_eq_pow_apply

theorem IsCycleOn.zpow_apply_eq_zpow_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s)
    {m n : ℤ} : (f ^ m) a = (f ^ n) a ↔ m ≡ n [ZMOD s.card] := by
  rw [Int.modEq_iff_dvd, ← hf.zpow_apply_eq ha]
  simp [sub_eq_neg_add, zpow_add, eq_inv_iff_eq, eq_comm]
#align equiv.perm.is_cycle_on.zpow_apply_eq_zpow_apply Equiv.Perm.IsCycleOn.zpow_apply_eq_zpow_apply

theorem IsCycleOn.pow_card_apply {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) :
    (f ^ s.card) a = a :=
  (hf.pow_apply_eq ha).2 dvd_rfl
#align equiv.perm.is_cycle_on.pow_card_apply Equiv.Perm.IsCycleOn.pow_card_apply

theorem IsCycleOn.exists_pow_eq {s : Finset α} (hf : f.IsCycleOn s) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ n < s.card, (f ^ n) a = b := by
  classical
    obtain ⟨n, rfl⟩ := hf.2 ha hb
    obtain ⟨k, hk⟩ := (Int.mod_modEq n s.card).symm.dvd
    refine' ⟨n.natMod s.card, Int.natMod_lt (Nonempty.card_pos ⟨a, ha⟩).ne', _⟩
    rw [← zpow_natCast, Int.natMod,
      Int.toNat_of_nonneg (Int.emod_nonneg _ <| Nat.cast_ne_zero.2
        (Nonempty.card_pos ⟨a, ha⟩).ne'), sub_eq_iff_eq_add'.1 hk, zpow_add, zpow_mul]
    simp only [zpow_natCast, coe_mul, comp_apply, EmbeddingLike.apply_eq_iff_eq]
    exact IsFixedPt.perm_zpow (hf.pow_card_apply ha) _
#align equiv.perm.is_cycle_on.exists_pow_eq Equiv.Perm.IsCycleOn.exists_pow_eq

theorem IsCycleOn.exists_pow_eq' (hs : s.Finite) (hf : f.IsCycleOn s) (ha : a ∈ s) (hb : b ∈ s) :
    ∃ n : ℕ, (f ^ n) a = b := by
  lift s to Finset α using id hs
  obtain ⟨n, -, hn⟩ := hf.exists_pow_eq ha hb
  exact ⟨n, hn⟩
#align equiv.perm.is_cycle_on.exists_pow_eq' Equiv.Perm.IsCycleOn.exists_pow_eq'

theorem IsCycleOn.range_pow (hs : s.Finite) (h : f.IsCycleOn s) (ha : a ∈ s) :
    Set.range (fun n => (f ^ n) a : ℕ → α) = s :=
  Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => h.1.mapsTo.perm_pow _ ha) fun _ =>
    h.exists_pow_eq' hs ha
#align equiv.perm.is_cycle_on.range_pow Equiv.Perm.IsCycleOn.range_pow

theorem IsCycleOn.range_zpow (h : f.IsCycleOn s) (ha : a ∈ s) :
    Set.range (fun n => (f ^ n) a : ℤ → α) = s :=
  Set.Subset.antisymm (Set.range_subset_iff.2 fun _ => (h.1.perm_zpow _).mapsTo ha) <| h.2 ha
#align equiv.perm.is_cycle_on.range_zpow Equiv.Perm.IsCycleOn.range_zpow

theorem IsCycleOn.of_pow {n : ℕ} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) : f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_pow⟩
#align equiv.perm.is_cycle_on.of_pow Equiv.Perm.IsCycleOn.of_pow

theorem IsCycleOn.of_zpow {n : ℤ} (hf : (f ^ n).IsCycleOn s) (h : Set.BijOn f s s) :
    f.IsCycleOn s :=
  ⟨h, fun _ hx _ hy => (hf.2 hx hy).of_zpow⟩
#align equiv.perm.is_cycle_on.of_zpow Equiv.Perm.IsCycleOn.of_zpow

theorem IsCycleOn.extendDomain {p : β → Prop} [DecidablePred p] (f : α ≃ Subtype p)
    (h : g.IsCycleOn s) : (g.extendDomain f).IsCycleOn ((↑) ∘ f '' s) :=
  ⟨h.1.extendDomain, by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (h.2 ha hb).extendDomain⟩
#align equiv.perm.is_cycle_on.extend_domain Equiv.Perm.IsCycleOn.extendDomain

protected theorem IsCycleOn.countable (hs : f.IsCycleOn s) : s.Countable := by
  obtain rfl | ⟨a, ha⟩ := s.eq_empty_or_nonempty
  · exact Set.countable_empty
  · exact (Set.countable_range fun n : ℤ => (⇑(f ^ n) : α → α) a).mono (hs.2 ha)
#align equiv.perm.is_cycle_on.countable Equiv.Perm.IsCycleOn.countable


end IsCycleOn

end Equiv.Perm

namespace List

section

variable [DecidableEq α] {l : List α}

set_option linter.deprecated false in -- nthLe
theorem Nodup.isCycleOn_formPerm (h : l.Nodup) :
    l.formPerm.IsCycleOn { a | a ∈ l } := by
  refine' ⟨l.formPerm.bijOn fun _ => List.formPerm_mem_iff_mem, fun a ha b hb => _⟩
  rw [Set.mem_setOf, ← List.indexOf_lt_length] at ha hb
  rw [← List.indexOf_get ha, ← List.indexOf_get hb]
  refine' ⟨l.indexOf b - l.indexOf a, _⟩
  simp only [sub_eq_neg_add, zpow_add, zpow_neg, Equiv.Perm.inv_eq_iff_eq, zpow_natCast,
    Equiv.Perm.coe_mul, ← List.nthLe_eq, List.formPerm_pow_apply_nthLe _ h, Function.comp]
  rw [add_comm]
#align list.nodup.is_cycle_on_form_perm List.Nodup.isCycleOn_formPerm

end

end List

namespace Finset

variable [DecidableEq α] [Fintype α]

theorem exists_cycleOn (s : Finset α) :
    ∃ f : Perm α, f.IsCycleOn s ∧ f.support ⊆ s := by
  refine ⟨s.toList.formPerm, ?_, fun x hx => by
    simpa using List.mem_of_formPerm_apply_ne _ _ (Perm.mem_support.1 hx)⟩
  convert s.nodup_toList.isCycleOn_formPerm
  simp
#align finset.exists_cycle_on Finset.exists_cycleOn

end Finset

namespace Set

variable {f : Perm α} {s : Set α}

theorem Countable.exists_cycleOn (hs : s.Countable) :
    ∃ f : Perm α, f.IsCycleOn s ∧ { x | f x ≠ x } ⊆ s := by
  classical
  obtain hs' | hs' := s.finite_or_infinite
  · refine ⟨hs'.toFinset.toList.formPerm, ?_, fun x hx => by
      simpa using List.mem_of_formPerm_apply_ne _ _ hx⟩
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
#align set.countable.exists_cycle_on Set.Countable.exists_cycleOn

theorem prod_self_eq_iUnion_perm (hf : f.IsCycleOn s) :
    s ×ˢ s = ⋃ n : ℤ, (fun a => (a, (f ^ n) a)) '' s := by
  ext ⟨a, b⟩
  simp only [Set.mem_prod, Set.mem_iUnion, Set.mem_image]
  refine' ⟨fun hx => _, _⟩
  · obtain ⟨n, rfl⟩ := hf.2 hx.1 hx.2
    exact ⟨_, _, hx.1, rfl⟩
  · rintro ⟨n, a, ha, ⟨⟩⟩
    exact ⟨ha, (hf.1.perm_zpow _).mapsTo ha⟩
#align set.prod_self_eq_Union_perm Set.prod_self_eq_iUnion_perm

end Set

namespace Finset

variable {f : Perm α} {s : Finset α}

theorem product_self_eq_disjiUnion_perm_aux (hf : f.IsCycleOn s) :
    (range s.card : Set ℕ).PairwiseDisjoint fun k =>
      s.map ⟨fun i => (i, (f ^ k) i), fun i j => congr_arg Prod.fst⟩ := by
  obtain hs | _ := (s : Set α).subsingleton_or_nontrivial
  · refine' Set.Subsingleton.pairwise _ _
    simp_rw [Set.Subsingleton, mem_coe, ← card_le_one] at hs ⊢
    rwa [card_range]
  classical
    rintro m hm n hn hmn
    simp only [disjoint_left, Function.onFun, mem_map, Function.Embedding.coeFn_mk, exists_prop,
      not_exists, not_and, forall_exists_index, and_imp, Prod.forall, Prod.mk.inj_iff]
    rintro _ _ _ - rfl rfl a ha rfl h
    rw [hf.pow_apply_eq_pow_apply ha] at h
    rw [mem_coe, mem_range] at hm hn
    exact hmn.symm (h.eq_of_lt_of_lt hn hm)
#align finset.product_self_eq_disj_Union_perm_aux Finset.product_self_eq_disjiUnion_perm_aux

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
      (range s.card).disjiUnion
        (fun k => s.map ⟨fun i => (i, (f ^ k) i), fun i j => congr_arg Prod.fst⟩)
        (product_self_eq_disjiUnion_perm_aux hf) := by
  ext ⟨a, b⟩
  simp only [mem_product, Equiv.Perm.coe_pow, mem_disjiUnion, mem_range, mem_map,
    Function.Embedding.coeFn_mk, Prod.mk.inj_iff, exists_prop]
  refine' ⟨fun hx => _, _⟩
  · obtain ⟨n, hn, rfl⟩ := hf.exists_pow_eq hx.1 hx.2
    exact ⟨n, hn, a, hx.1, rfl, by rw [f.iterate_eq_pow]⟩
  · rintro ⟨n, -, a, ha, rfl, rfl⟩
    exact ⟨ha, (hf.1.iterate _).mapsTo ha⟩
#align finset.product_self_eq_disj_Union_perm Finset.product_self_eq_disjiUnion_permₓ

end Finset

namespace Finset

variable [Semiring α] [AddCommMonoid β] [Module α β] {s : Finset ι} {σ : Perm ι}

theorem sum_smul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f : ι → α) (g : ι → β) :
    ((∑ i in s, f i) • ∑ i in s, g i) = ∑ k in range s.card, ∑ i in s, f i • g ((σ ^ k) i) := by
  simp_rw [sum_smul_sum, product_self_eq_disjiUnion_perm hσ, sum_disjiUnion, sum_map]
  rfl
#align finset.sum_smul_sum_eq_sum_perm Finset.sum_smul_sum_eq_sum_perm

theorem sum_mul_sum_eq_sum_perm (hσ : σ.IsCycleOn s) (f g : ι → α) :
    ((∑ i in s, f i) * ∑ i in s, g i) = ∑ k in range s.card, ∑ i in s, f i * g ((σ ^ k) i) :=
  sum_smul_sum_eq_sum_perm hσ f g
#align finset.sum_mul_sum_eq_sum_perm Finset.sum_mul_sum_eq_sum_perm

end Finset
