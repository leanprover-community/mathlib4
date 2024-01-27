/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/

import Mathlib.Dynamics.PeriodicPts
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Int.Lemmas

/-!
# Period of a group action

This module defines some helpful lemmas around [`MulAction.period`] and [`AddAction.period`].
The period of a point `a` by a group element `g` is the smallest `m` such that `g ^ m • a = a`
(resp. `(m • g) +ᵥ a = a`) for a given `g : G` and `a : α`.

If such an `m` does not exist,
then by convention `MulAction.period` and `AddAction.period` return 0.
-/

namespace MulAction

universe u v
variable {α : Type v}
variable {G : Type u} [Group G] [MulAction G α]
variable {M : Type u} [Monoid M] [MulAction M α]

@[to_additive period_zero_eq_one]
theorem period_one_eq_one (a : α) : period (1 : M) a = 1 := by
  simp_rw [period, one_smul]
  exact Function.minimalPeriod_id

@[to_additive (attr := simp)]
theorem period_subgroup_mk {H : Subgroup G} {g : G} (gh : g ∈ H) (a : α) :
    period (⟨g, gh⟩ : H) a = period g a := by
  simp only [period, Submonoid.mk_smul]

theorem period_eq_zero_iff_forall_pow {m : M} {a : α} :
    period m a = 0 ↔ ∀ n > 0, m ^ n • a ≠ a := by
  simp_rw [period, ← smul_iterate, Function.minimalPeriod_eq_zero_iff_nmem_periodicPts,
    Function.mem_periodicPts, Function.IsPeriodicPt, Function.IsFixedPt, not_exists, not_and]

theorem period_eq_zero_iff_forall_zpow {g : G} {a : α} :
    period g a = 0 ↔ ∀ j : ℤ, j ≠ 0 → g ^ j • a ≠ a := by
  rw [period_eq_zero_iff_forall_pow]
  constructor
  · intro h₁ j j_ne_zero
    specialize h₁ j.natAbs (Int.natAbs_pos.mpr j_ne_zero)
    rw [← zpow_ofNat] at h₁
    cases Int.natAbs_eq j with
    | inl h₂ =>
      rwa [← h₂] at h₁
    | inr h₂ =>
      rw [← neg_eq_iff_eq_neg] at h₂
      rwa [← h₂, ne_eq, zpow_neg, smul_eq_iff_eq_inv_smul, inv_inv, eq_comm] at h₁
  · intro h n n_pos
    specialize h n (Int.coe_nat_ne_zero_iff_pos.mpr n_pos)
    rwa [zpow_ofNat] at h

/-- If the action is periodic, then a lower bound for its period can be computed. -/
@[to_additive "If the action is periodic, then a lower bound for its period can be computed."]
theorem le_period {m : M} {a : α} {n : ℕ} (period_pos : 0 < period m a)
    (moved : ∀ k, 0 < k → k < n → m ^ k • a ≠ a) : n ≤ period m a :=
  le_of_not_gt fun period_lt_n =>
    moved _ period_pos period_lt_n <| pow_period_smul m a

/-- If for some `n`, `m ^ n • a = a`, then `period m a ≤ n`. -/
@[to_additive "If for some `n`, `(n • m) +ᵥ a = a`, then `period m a ≤ n`."]
theorem period_le_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    period m a ≤ n :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_le n_pos

theorem period_le_natAbs_of_fixed {g : G} {a : α} {j : ℤ} (j_ne_zero : j ≠ 0)
    (fixed : g ^ j • a = a) : period g a ≤ j.natAbs := by
  apply period_le_of_fixed (Int.natAbs_pos.mpr j_ne_zero)
  cases Int.natAbs_eq j with
  | inl h_eq =>
    rwa [← zpow_ofNat, ← h_eq]
  | inr h_eq =>
    rw [← neg_eq_iff_eq_neg] at h_eq
    rwa [← zpow_ofNat, ← h_eq, zpow_neg, smul_eq_iff_eq_inv_smul, inv_inv, eq_comm]

/-- If for some `n`, `m ^ n • a = a`, then `0 < period m a`. -/
@[to_additive "If for some `n`, `(n • m) +ᵥ a = a`, then `0 < period m a`."]
theorem period_pos_of_fixed {m : M} {a : α} {n : ℕ} (n_pos : 0 < n) (fixed : m ^ n • a = a) :
    0 < period m a :=
  (isPeriodicPt_smul_iff.mpr fixed).minimalPeriod_pos n_pos

@[to_additive]
theorem period_eq_one_iff {m : M} {a : α} : period m a = 1 ↔ m • a = a :=
  ⟨fun eq_one => pow_one m ▸ eq_one ▸ pow_period_smul m a,
   fun fixed => le_antisymm
    (period_le_of_fixed one_pos (by simpa))
    (period_pos_of_fixed one_pos (by simpa))⟩

/-- For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `m ^ n`. -/
@[to_additive "For any non-zero `n` less than the period of `m` on `a`, `a` is moved by `n • m`."]
theorem pow_smul_ne_of_lt_period {m : M} {a : α} {n : ℕ} (n_pos : 0 < n)
    (n_lt_period : n < period m a) : m ^ n • a ≠ a := fun a_fixed =>
  not_le_of_gt n_lt_period <| period_le_of_fixed n_pos a_fixed

section Identities

/-! ### `MulAction.period` for common group elements
-/

variable (M) in
@[to_additive (attr := simp)]
theorem period_one (a : α) : period (1 : M) a = 1 := period_eq_one_iff.mpr (one_smul M a)

@[to_additive (attr := simp)]
theorem period_inv (g : G) (a : α) : period g⁻¹ a = period g a := by
  simp only [period_eq_minimalPeriod, Function.minimalPeriod_eq_minimalPeriod_iff,
    isPeriodicPt_smul_iff]
  intro n
  rw [smul_eq_iff_eq_inv_smul, eq_comm, ← zpow_ofNat, inv_zpow, inv_inv, zpow_ofNat]

end Identities

/-!
If `g ^ i • x = g ^ j • x` (resp. `(i • g) +ᵥ x = (j • g) +ᵥ x`), then `period g x` divides `i - j`.
If the action of `g` on `x` is aperiodic, then this is equivalent to say that `i = j`.
-/

@[to_additive]
theorem smul_zpow_eq_of_period_dvd {g : G} {x : α} {i j : ℤ} :
    g ^ i • x = g ^ j • x ↔ (period g x : ℤ) ∣ i - j := by
  rw [eq_comm, smul_eq_iff_eq_inv_smul, eq_comm, ← mul_smul, ← zpow_neg, ← zpow_add, add_comm,
    ← sub_eq_add_neg, zpow_smul_eq_iff_period_dvd]

@[to_additive]
theorem smul_pow_eq_of_period_dvd {g : G} {x : α} {n m : ℕ} :
    g ^ n • x = g ^ m • x ↔ period g x ∣ Int.natAbs (↑n - ↑m) := by
  rw [← zpow_ofNat, ← zpow_ofNat, smul_zpow_eq_of_period_dvd, ← dvd_abs, ← Int.coe_natAbs,
    Int.ofNat_dvd]

section MonoidExponent

/-! ### `MulAction.period` and group exponents

The period of a given element `m : M` can be bounded by the `Monoid.exponent M` or `orderOf m`.
-/

@[to_additive]
theorem period_dvd_orderOf (m : M) (a : α) : period m a ∣ orderOf m := by
  rw [← pow_smul_eq_iff_period_dvd, pow_orderOf_eq_one, one_smul]

@[to_additive]
theorem period_pos_of_orderOf_pos {m : M} (order_pos : 0 < orderOf m) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_orderOf m a) order_pos

@[to_additive]
theorem period_le_orderOf {m : M} (order_pos : 0 < orderOf m) (a : α) :
    period m a ≤ orderOf m :=
  Nat.le_of_dvd order_pos (period_dvd_orderOf m a)

@[to_additive]
theorem period_dvd_exponent (m : M) (a : α) : period m a ∣ Monoid.exponent M := by
  rw [← pow_smul_eq_iff_period_dvd, Monoid.pow_exponent_eq_one, one_smul]

@[to_additive]
theorem period_pos_of_exponent_pos (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    0 < period m a :=
  Nat.pos_of_dvd_of_pos (period_dvd_exponent m a) exp_pos

@[to_additive]
theorem period_le_exponent (exp_pos : 0 < Monoid.exponent M) (m : M) (a : α) :
    period m a ≤ Monoid.exponent M :=
  Nat.le_of_dvd exp_pos (period_dvd_exponent m a)

variable (α) in
@[to_additive]
theorem periods_bounded_of_exponent_pos (exp_pos : Monoid.exponent M ≠ 0) :
    BddAbove { period m a | (m : M) (a : α)} := by
  use Monoid.exponent M
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index]
  intro _ m a period_eq
  rw [← period_eq]
  exact period_le_exponent exp_pos _ _

variable (α) in
@[to_additive]
theorem period_bounded_of_exponent_pos (exp_pos : Monoid.exponent M ≠ 0) (m : M) :
    BddAbove (Set.range (fun a : α => period m a)) := by
  use Monoid.exponent M
  simpa [upperBounds] using period_le_exponent exp_pos _

@[to_additive]
theorem periods_in_set_bounded_of_exponent_pos (exp_pos : Monoid.exponent M ≠ 0) (s : Set α) :
    BddAbove { period m a | (m : M) (a ∈ s) } := by
  apply BddAbove.mono _ (periods_bounded_of_exponent_pos α exp_pos)
  exact fun _ ⟨m, a, _, eq⟩ => ⟨m, a, eq⟩

@[to_additive]
theorem exists_maximal_period_of_exponent_pos (exp_pos : Monoid.exponent G ≠ 0)
    {s : Set α} (s_nonempty : s.Nonempty) : ∃ (g : G) (x : α), x ∈ s ∧ 0 < period g x ∧
      ∀ h : G, ∀ y ∈ s, period h y ≤ period g x := by
  have bounded := periods_in_set_bounded_of_exponent_pos exp_pos s
  have nonempty : Set.Nonempty { period g a | (g : G) (a ∈ s) } := by
    refine ⟨1, 1, s_nonempty.choose, s_nonempty.choose_spec, ?eq⟩
    exact period_one_eq_one _
  let ⟨g, x, x_in_s, period_eq_sSup⟩ := Nat.sSup_mem nonempty bounded

  exact ⟨g, x, x_in_s, period_pos_of_exponent_pos exp_pos g x,
    fun h y y_in_s => period_eq_sSup ▸ le_csSup bounded ⟨h, y, y_in_s, rfl⟩⟩

end MonoidExponent

section InjOn

/-! ## Injectivity of the action in relation to `period`
-/

/--
All the values `g ^ i` with `i < period g x` will map `x` to different points.
-/
@[to_additive "All the values `i • g` with `i < period g x` will map `x` to different points."]
theorem smul_injOn_pow_lt_period (g : G) (x : α) :
    { g ^ i | i < period g x }.InjOn (· • x) := by
  intro h ⟨a, a_lt_n, ga_eq_h⟩ i ⟨b, b_lt_n, gb_eq_i⟩ img_eq
  rw [← ga_eq_h, ← gb_eq_i, MulAction.smul_pow_eq_of_period_dvd] at img_eq
  rw [← ga_eq_h, ← gb_eq_i]
  by_cases eq : a = b
  · rw [eq]
  · exfalso
    refine Nat.not_lt.mpr
      (Nat.le_of_dvd ?pos img_eq)
      (Int.natAbs_coe_sub_coe_lt_of_lt b_lt_n a_lt_n)
    rwa [Int.natAbs_sub_pos_iff, ne_eq, Nat.cast_inj]

/--
If the action of `g` on `x` is aperiodic, then the action of `g ^ i` on `x` is injective.
-/
@[to_additive
  "If the action of `g` on `x` is aperiodic, then the action of `i • g` on `x` is injective."]
theorem smul_injOn_zpow_of_period_eq_zero {g : G} {x : α} (period_eq_zero : period g x = 0) :
    { g ^ i | i : ℤ }.InjOn (· • x) := by
  intro g₁ ⟨i, g₁_eq⟩ g₂ ⟨j, g₂_eq⟩ img_eq
  rw [← g₁_eq, ← g₂_eq, MulAction.smul_zpow_eq_of_period_dvd, period_eq_zero,
    Int.ofNat_zero, zero_dvd_iff, sub_eq_zero] at img_eq
  rw [← g₁_eq, ← g₂_eq, img_eq]

-- TODO: use smul_injOn_pow_lt_period and smul_injOn_zpow_of_period_eq_zero
lemma smul_pow_inj_of_le_period {g : G} {x : α} {n m : ℕ}
    (n_lt_period : n < MulAction.period g x) (m_lt_period : m < MulAction.period g x)
    (pow_eq : g ^ n = g ^ m): n = m := by
  rw [← mul_inv_eq_one, ← zpow_ofNat, ← zpow_ofNat, ← zpow_neg, ← zpow_add,
    ← sub_eq_add_neg] at pow_eq
  by_contra ne
  apply lt_iff_not_le.mp (Int.natAbs_coe_sub_coe_lt_of_lt m_lt_period n_lt_period)

  apply MulAction.period_le_natAbs_of_fixed
  · rwa [ne_eq, sub_eq_zero, Nat.cast_inj]
  · rw [pow_eq, one_smul]

lemma smul_pow_inj_of_period_eq_zero {g : G} {x : α} {n m : ℕ}
    (period_eq_zero : MulAction.period g x = 0) (pow_eq : g ^ n = g ^ m) : n = m := by
  rw [← mul_inv_eq_one, ← zpow_ofNat, ← zpow_ofNat, ← zpow_neg, ← zpow_add,
    ← sub_eq_add_neg] at pow_eq
  by_contra ne

  rw [MulAction.period_eq_zero_iff_forall_zpow] at period_eq_zero
  apply period_eq_zero (↑n - ↑m)
  · rwa [ne_eq, sub_eq_zero, Nat.cast_inj]
  · rw [pow_eq, one_smul]
end InjOn

end MulAction
