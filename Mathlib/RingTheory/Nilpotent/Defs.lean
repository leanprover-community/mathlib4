/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Lattice

#align_import ring_theory.nilpotent from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Definition of nilpotent elements

This file defines the notion of a nilpotent element and proves the immediate consequences.
For results that require further theory, see `Mathlib.RingTheory.Nilpotent.Basic`
and `Mathlib.RingTheory.Nilpotent.Lemmas`.

## Main definitions

  * `IsNilpotent`
  * `Commute.isNilpotent_mul_left`
  * `Commute.isNilpotent_mul_right`
  * `nilpotencyClass`

-/

universe u v

open Function Set

variable {R S : Type*} {x y : R}

/-- An element is said to be nilpotent if some natural-number-power of it equals zero.

Note that we require only the bare minimum assumptions for the definition to make sense. Even
`MonoidWithZero` is too strong since nilpotency is important in the study of rings that are only
power-associative. -/
def IsNilpotent [Zero R] [Pow R ℕ] (x : R) : Prop :=
  ∃ n : ℕ, x ^ n = 0
#align is_nilpotent IsNilpotent

theorem IsNilpotent.mk [Zero R] [Pow R ℕ] (x : R) (n : ℕ) (e : x ^ n = 0) : IsNilpotent x :=
  ⟨n, e⟩
#align is_nilpotent.mk IsNilpotent.mk

@[simp] lemma isNilpotent_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] : IsNilpotent x :=
  ⟨0, Subsingleton.elim _ _⟩

@[simp] theorem IsNilpotent.zero [MonoidWithZero R] : IsNilpotent (0 : R) :=
  ⟨1, pow_one 0⟩
#align is_nilpotent.zero IsNilpotent.zero

theorem not_isNilpotent_one [MonoidWithZero R] [Nontrivial R] :
    ¬ IsNilpotent (1 : R) := fun ⟨_, H⟩ ↦ zero_ne_one (H.symm.trans (one_pow _))

lemma IsNilpotent.pow_succ (n : ℕ) {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (x ^ n.succ) := by
  obtain ⟨N,hN⟩ := hx
  use N
  rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]

theorem  IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : ℕ}
    (h : IsNilpotent (x ^ m)) : IsNilpotent x := by
  obtain ⟨n, h⟩ := h
  use m*n
  rw [← h, pow_mul x m n]

lemma IsNilpotent.pow_of_pos {n} {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) (hn : n ≠ 0) : IsNilpotent (x ^ n) := by
  cases n with
  | zero => contradiction
  | succ => exact  IsNilpotent.pow_succ _ hx

@[simp]
lemma IsNilpotent.pow_iff_pos {n} {S : Type*} [MonoidWithZero S] {x : S}
    (hn : n ≠ 0) : IsNilpotent (x ^ n) ↔ IsNilpotent x :=
 ⟨fun h => of_pow h, fun h => pow_of_pos h hn⟩

theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) :
    IsNilpotent (f r) := by
  use hr.choose
  rw [← map_pow, hr.choose_spec, map_zero]
#align is_nilpotent.map IsNilpotent.map

lemma IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F} (hf : Function.Injective f) :
    IsNilpotent (f r) ↔ IsNilpotent r :=
  ⟨fun ⟨k, hk⟩ ↦ ⟨k, (map_eq_zero_iff f hf).mp <| by rwa [map_pow]⟩, fun h ↦ h.map f⟩

theorem IsUnit.isNilpotent_mul_unit_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (r * u) ↔ IsNilpotent r :=
  exists_congr fun n ↦ by rw [h_comm.mul_pow, (hu.pow n).mul_left_eq_zero]

theorem IsUnit.isNilpotent_unit_mul_of_commute_iff [MonoidWithZero R] {r u : R}
    (hu : IsUnit u) (h_comm : Commute r u) :
    IsNilpotent (u * r) ↔ IsNilpotent r :=
  h_comm ▸ hu.isNilpotent_mul_unit_of_commute_iff h_comm

section NilpotencyClass

section ZeroPow

variable [Zero R] [Pow R ℕ]

variable (x) in
/-- If `x` is nilpotent, the nilpotency class is the smallest natural number `k` such that
`x ^ k = 0`. If `x` is not nilpotent, the nilpotency class takes the junk value `0`. -/
noncomputable def nilpotencyClass : ℕ := sInf {k | x ^ k = 0}

@[simp] lemma nilpotencyClass_eq_zero_of_subsingleton [Subsingleton R] :
    nilpotencyClass x = 0 := by
  let s : Set ℕ := {k | x ^ k = 0}
  suffices s = univ by change sInf _ = 0; simp [s] at this; simp [this]
  exact eq_univ_iff_forall.mpr fun k ↦ Subsingleton.elim _ _

lemma isNilpotent_of_pos_nilpotencyClass (hx : 0 < nilpotencyClass x) :
    IsNilpotent x := by
  let s : Set ℕ := {k | x ^ k = 0}
  change s.Nonempty
  change 0 < sInf s at hx
  by_contra contra
  simp [not_nonempty_iff_eq_empty.mp contra] at hx

lemma pow_nilpotencyClass (hx : IsNilpotent x) : x ^ (nilpotencyClass x) = 0 :=
  Nat.sInf_mem hx

end ZeroPow

section MonoidWithZero

variable [MonoidWithZero R]

lemma nilpotencyClass_eq_succ_iff {k : ℕ} :
    nilpotencyClass x = k + 1 ↔ x ^ (k + 1) = 0 ∧ x ^ k ≠ 0 := by
  let s : Set ℕ := {k | x ^ k = 0}
  have : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s := fun k₁ k₂ h_le hk₁ ↦ pow_eq_zero_of_le h_le hk₁
  simp [s, nilpotencyClass, Nat.sInf_upward_closed_eq_succ_iff this]

@[simp] lemma nilpotencyClass_zero [Nontrivial R] :
    nilpotencyClass (0 : R) = 1 :=
  nilpotencyClass_eq_succ_iff.mpr <| by constructor <;> simp

@[simp] lemma pos_nilpotencyClass_iff [Nontrivial R] :
    0 < nilpotencyClass x ↔ IsNilpotent x := by
  refine ⟨isNilpotent_of_pos_nilpotencyClass, fun hx ↦ Nat.pos_of_ne_zero fun hx' ↦ ?_⟩
  replace hx := pow_nilpotencyClass hx
  rw [hx', pow_zero] at hx
  exact one_ne_zero hx

lemma pow_pred_nilpotencyClass [Nontrivial R] (hx : IsNilpotent x) :
    x ^ (nilpotencyClass x - 1) ≠ 0 :=
  (nilpotencyClass_eq_succ_iff.mp <| Nat.eq_add_of_sub_eq (pos_nilpotencyClass_iff.mpr hx) rfl).2

lemma eq_zero_of_nilpotencyClass_eq_one (hx : nilpotencyClass x = 1) :
    x = 0 := by
  have : IsNilpotent x := isNilpotent_of_pos_nilpotencyClass (hx ▸ Nat.one_pos)
  rw [← pow_nilpotencyClass this, hx, pow_one]

@[simp] lemma nilpotencyClass_eq_one [Nontrivial R] :
    nilpotencyClass x = 1 ↔ x = 0 :=
  ⟨eq_zero_of_nilpotencyClass_eq_one, fun hx ↦ hx ▸ nilpotencyClass_zero⟩

end MonoidWithZero

end NilpotencyClass

/-- A structure that has zero and pow is reduced if it has no nonzero nilpotent elements. -/
@[mk_iff]
class IsReduced (R : Type*) [Zero R] [Pow R ℕ] : Prop where
  /-- A reduced structure has no nonzero nilpotent elements. -/
  eq_zero : ∀ x : R, IsNilpotent x → x = 0
#align is_reduced IsReduced

instance (priority := 900) isReduced_of_noZeroDivisors [MonoidWithZero R] [NoZeroDivisors R] :
    IsReduced R :=
  ⟨fun _ ⟨_, hn⟩ => pow_eq_zero hn⟩
#align is_reduced_of_no_zero_divisors isReduced_of_noZeroDivisors

instance (priority := 900) isReduced_of_subsingleton [Zero R] [Pow R ℕ] [Subsingleton R] :
    IsReduced R :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩
#align is_reduced_of_subsingleton isReduced_of_subsingleton

theorem IsNilpotent.eq_zero [Zero R] [Pow R ℕ] [IsReduced R] (h : IsNilpotent x) : x = 0 :=
  IsReduced.eq_zero x h
#align is_nilpotent.eq_zero IsNilpotent.eq_zero

@[simp]
theorem isNilpotent_iff_eq_zero [MonoidWithZero R] [IsReduced R] : IsNilpotent x ↔ x = 0 :=
  ⟨fun h => h.eq_zero, fun h => h.symm ▸ IsNilpotent.zero⟩
#align is_nilpotent_iff_eq_zero isNilpotent_iff_eq_zero

theorem isReduced_of_injective [MonoidWithZero R] [MonoidWithZero S] {F : Type*}
    [FunLike F R S] [MonoidWithZeroHomClass F R S]
    (f : F) (hf : Function.Injective f) [IsReduced S] :
    IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero
#align is_reduced_of_injective isReduced_of_injective

instance (ι) (R : ι → Type*) [∀ i, Zero (R i)] [∀ i, Pow (R i) ℕ]
    [∀ i, IsReduced (R i)] : IsReduced (∀ i, R i) where
  eq_zero _ := fun ⟨n, hn⟩ ↦ funext fun i ↦ IsReduced.eq_zero _ ⟨n, congr_fun hn i⟩

/-- An element `y` in a monoid is radical if for any element `x`, `y` divides `x` whenever it
  divides a power of `x`. -/
def IsRadical [Dvd R] [Pow R ℕ] (y : R) : Prop :=
  ∀ (n : ℕ) (x), y ∣ x ^ n → y ∣ x
#align is_radical IsRadical

theorem isRadical_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsRadical y ↔ ∀ x, y ∣ x ^ k → y ∣ x :=
  ⟨(· k), k.pow_imp_self_of_one_lt hk _ fun _ _ h ↦ .inl (dvd_mul_of_dvd_left h _)⟩
#align is_radical_iff_pow_one_lt isRadical_iff_pow_one_lt

namespace Commute

section Semiring

variable [Semiring R] (h_comm : Commute x y)

theorem isNilpotent_mul_left (h : IsNilpotent x) : IsNilpotent (x * y) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow, hn, zero_mul]
#align commute.is_nilpotent_mul_left Commute.isNilpotent_mul_left

theorem isNilpotent_mul_right (h : IsNilpotent y) : IsNilpotent (x * y) := by
  rw [h_comm.eq]
  exact h_comm.symm.isNilpotent_mul_left h
#align commute.is_nilpotent_mul_right Commute.isNilpotent_mul_right

end Semiring

end Commute
