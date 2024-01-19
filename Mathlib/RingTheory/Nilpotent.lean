/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.GeomSum
import Mathlib.LinearAlgebra.Matrix.ToLin

#align_import ring_theory.nilpotent from "leanprover-community/mathlib"@"da420a8c6dd5bdfb85c4ced85c34388f633bc6ff"

/-!
# Nilpotent elements

## Main definitions

  * `IsNilpotent`
  * `isNilpotent_neg_iff`
  * `Commute.isNilpotent_add`
  * `Commute.isNilpotent_mul_left`
  * `Commute.isNilpotent_mul_right`
  * `Commute.isNilpotent_sub`

-/

universe u v

open BigOperators Function Set

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

theorem IsNilpotent.neg [Ring R] (h : IsNilpotent x) : IsNilpotent (-x) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [neg_pow, hn, mul_zero]
#align is_nilpotent.neg IsNilpotent.neg

lemma IsNilpotent.pow_succ (n : ℕ) {S : Type*} [MonoidWithZero S] {x : S}
    (hx : IsNilpotent x) : IsNilpotent (x ^ n.succ) := by
  obtain ⟨N,hN⟩ := hx
  use N
  rw [← pow_mul, Nat.succ_mul, pow_add, hN, mul_zero]

theorem  IsNilpotent.of_pow [MonoidWithZero R] {x : R} {m : ℕ}
    (h : IsNilpotent (x ^ m)) : IsNilpotent x := by
  obtain ⟨n, h⟩ := h
  use (m*n)
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

@[simp]
theorem isNilpotent_neg_iff [Ring R] : IsNilpotent (-x) ↔ IsNilpotent x :=
  ⟨fun h => neg_neg x ▸ h.neg, fun h => h.neg⟩
#align is_nilpotent_neg_iff isNilpotent_neg_iff

lemma IsNilpotent.smul [MonoidWithZero R] [MonoidWithZero S] [MulActionWithZero R S]
    [SMulCommClass R S S] [IsScalarTower R S S] {a : S} (ha : IsNilpotent a) (t : R) :
    IsNilpotent (t • a) := by
  obtain ⟨k, ha⟩ := ha
  use k
  rw [smul_pow, ha, smul_zero]

theorem IsNilpotent.map [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [MonoidWithZeroHomClass F R S] (hr : IsNilpotent r) (f : F) : IsNilpotent (f r) := by
  use hr.choose
  rw [← map_pow, hr.choose_spec, map_zero]
#align is_nilpotent.map IsNilpotent.map

lemma IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZero S] {r : R} {F : Type*}
    [MonoidWithZeroHomClass F R S] {f : F} (hf : Function.Injective f) :
    IsNilpotent (f r) ↔ IsNilpotent r :=
  ⟨fun ⟨k, hk⟩ ↦ ⟨k, (map_eq_zero_iff f hf).mp <| by rwa [map_pow]⟩, fun h ↦ h.map f⟩

theorem IsNilpotent.sub_one_isUnit [Ring R] {r : R} (hnil : IsNilpotent r) : IsUnit (r - 1) := by
  obtain ⟨n, hn⟩ := hnil
  refine' ⟨⟨r - 1, -∑ i in Finset.range n, r ^ i, _, _⟩, rfl⟩
  · rw [mul_neg, mul_geom_sum, hn]
    simp
  · rw [neg_mul, geom_sum_mul, hn]
    simp

theorem Commute.IsNilpotent.add_isUnit [Ring R] {r : R} {u : Rˣ} (hnil : IsNilpotent r)
    (hru : Commute r (↑u⁻¹ : R)) : IsUnit (u + r) := by
  rw [← Units.isUnit_mul_units _ u⁻¹, add_mul, Units.mul_inv, ← IsUnit.neg_iff, add_comm, neg_add,
    ← sub_eq_add_neg]
  obtain ⟨n, hn⟩ := hnil
  refine' IsNilpotent.sub_one_isUnit ⟨n, _⟩
  rw [neg_pow, hru.mul_pow, hn]
  simp

section NilpotencyClass

section ZeroPow

variable [Zero R] [Pow R ℕ]

variable (x) in
/-- If `x` is nilpotent the nilpotency class is the small natural number `k` such that `x ^ k = 0`.
If `x` is not nilpotent, then the nilpotency class takes the junk value `0`. -/
noncomputable def nilpotencyClass : ℕ := sInf {k | x ^ k = 0}

@[simp] lemma nilpotencyClass_eq_zero_of_subsingleton [Subsingleton R] :
    nilpotencyClass x = 0 := by
  let s : Set ℕ := {k | x ^ k = 0}
  suffices s = univ by change sInf _ = 0; simp [this]
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
  simp [nilpotencyClass, Nat.sInf_upward_closed_eq_succ_iff this]

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
  have : IsNilpotent x := isNilpotent_of_pos_nilpotencyClass (hx ▸ one_pos)
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
    [MonoidWithZeroHomClass F R S] (f : F) (hf : Function.Injective f) [IsReduced S] :
    IsReduced R := by
  constructor
  intro x hx
  apply hf
  rw [map_zero]
  exact (hx.map f).eq_zero
#align is_reduced_of_injective isReduced_of_injective

theorem RingHom.ker_isRadical_iff_reduced_of_surjective {S F} [CommSemiring R] [CommRing S]
    [RingHomClass F R S] {f : F} (hf : Function.Surjective f) :
    (RingHom.ker f).IsRadical ↔ IsReduced S := by
  simp_rw [isReduced_iff, hf.forall, IsNilpotent, ← map_pow, ← RingHom.mem_ker]
  rfl
#align ring_hom.ker_is_radical_iff_reduced_of_surjective RingHom.ker_isRadical_iff_reduced_of_surjective

/-- An element `y` in a monoid is radical if for any element `x`, `y` divides `x` whenever it
  divides a power of `x`. -/
def IsRadical [Dvd R] [Pow R ℕ] (y : R) : Prop :=
  ∀ (n : ℕ) (x), y ∣ x ^ n → y ∣ x
#align is_radical IsRadical

theorem zero_isRadical_iff [MonoidWithZero R] : IsRadical (0 : R) ↔ IsReduced R := by
  simp_rw [isReduced_iff, IsNilpotent, exists_imp, ← zero_dvd_iff]
  exact forall_swap
#align zero_is_radical_iff zero_isRadical_iff

theorem isRadical_iff_span_singleton [CommSemiring R] :
    IsRadical y ↔ (Ideal.span ({y} : Set R)).IsRadical := by
  simp_rw [IsRadical, ← Ideal.mem_span_singleton]
  exact forall_swap.trans (forall_congr' fun r => exists_imp.symm)
#align is_radical_iff_span_singleton isRadical_iff_span_singleton

theorem isRadical_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsRadical y ↔ ∀ x, y ∣ x ^ k → y ∣ x :=
  ⟨fun h x => h k x, fun h =>
    k.cauchy_induction_mul (fun n h x hd => h x <| (pow_succ' x n).symm ▸ hd.mul_right x) 0 hk
      (fun x hd => pow_one x ▸ hd) fun n _ hn x hd => h x <| hn _ <| (pow_mul x k n).subst hd⟩
#align is_radical_iff_pow_one_lt isRadical_iff_pow_one_lt

theorem isReduced_iff_pow_one_lt [MonoidWithZero R] (k : ℕ) (hk : 1 < k) :
    IsReduced R ↔ ∀ x : R, x ^ k = 0 → x = 0 := by
  simp_rw [← zero_isRadical_iff, isRadical_iff_pow_one_lt k hk, zero_dvd_iff]
#align is_reduced_iff_pow_one_lt isReduced_iff_pow_one_lt

namespace Commute

section Semiring

variable [Semiring R] (h_comm : Commute x y)

theorem isNilpotent_add (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x + y) := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  use n + m - 1
  rw [h_comm.add_pow']
  apply Finset.sum_eq_zero
  rintro ⟨i, j⟩ hij
  suffices x ^ i * y ^ j = 0 by simp only [this, nsmul_eq_mul, mul_zero]
  cases' Nat.le_or_le_of_add_eq_add_pred (Finset.mem_antidiagonal.mp hij) with hi hj
  · rw [pow_eq_zero_of_le hi hn, zero_mul]
  · rw [pow_eq_zero_of_le hj hm, mul_zero]
#align commute.is_nilpotent_add Commute.isNilpotent_add

protected lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) (h_comm : ∀ i j, i ∈ s → j ∈ s → Commute (f i) (f j)) :
    IsNilpotent (∑ i in s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert j s hj ih => ?_
  rw [Finset.sum_insert hj]
  apply Commute.isNilpotent_add
  · exact Commute.sum_right _ _ _ (fun i hi ↦ h_comm _ _ (by simp) (by simp [hi]))
  · apply hnp; simp
  · exact ih (fun i hi ↦ hnp i (by simp [hi]))
      (fun i j hi hj ↦ h_comm i j (by simp [hi]) (by simp [hj]))

theorem isNilpotent_mul_left (h : IsNilpotent x) : IsNilpotent (x * y) := by
  obtain ⟨n, hn⟩ := h
  use n
  rw [h_comm.mul_pow, hn, zero_mul]
#align commute.is_nilpotent_mul_left Commute.isNilpotent_mul_left

protected lemma isNilpotent_mul_left_iff (hy : y ∈ nonZeroDivisorsLeft R) :
    IsNilpotent (x * y) ↔ IsNilpotent x := by
  refine' ⟨_, h_comm.isNilpotent_mul_left⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsLeft R).pow_mem hy k _ hk⟩

theorem isNilpotent_mul_right (h : IsNilpotent y) : IsNilpotent (x * y) := by
  rw [h_comm.eq]
  exact h_comm.symm.isNilpotent_mul_left h
#align commute.is_nilpotent_mul_right Commute.isNilpotent_mul_right

protected lemma isNilpotent_mul_right_iff (hx : x ∈ nonZeroDivisorsRight R) :
    IsNilpotent (x * y) ↔ IsNilpotent y := by
  refine' ⟨_, h_comm.isNilpotent_mul_right⟩
  rintro ⟨k, hk⟩
  rw [mul_pow h_comm] at hk
  exact ⟨k, (nonZeroDivisorsRight R).pow_mem hx k _ hk⟩

end Semiring

section Ring

variable [Ring R] (h_comm : Commute x y)

theorem isNilpotent_sub (hx : IsNilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y) := by
  rw [← neg_right_iff] at h_comm
  rw [← isNilpotent_neg_iff] at hy
  rw [sub_eq_add_neg]
  exact h_comm.isNilpotent_add hx hy
#align commute.is_nilpotent_sub Commute.isNilpotent_sub

end Ring

end Commute

section CommSemiring

variable [CommSemiring R] {x y : R}

lemma isNilpotent_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (hnp : ∀ i ∈ s, IsNilpotent (f i)) :
    IsNilpotent (∑ i in s, f i) :=
  Commute.isNilpotent_sum hnp fun _ _ _ _ ↦ Commute.all _ _

/-- The nilradical of a commutative semiring is the ideal of nilpotent elements. -/
def nilradical (R : Type*) [CommSemiring R] : Ideal R :=
  (0 : Ideal R).radical
#align nilradical nilradical

theorem mem_nilradical : x ∈ nilradical R ↔ IsNilpotent x :=
  Iff.rfl
#align mem_nilradical mem_nilradical

theorem nilradical_eq_sInf (R : Type*) [CommSemiring R] :
    nilradical R = sInf { J : Ideal R | J.IsPrime } :=
  (Ideal.radical_eq_sInf ⊥).trans <| by simp_rw [and_iff_right bot_le]
#align nilradical_eq_Inf nilradical_eq_sInf

theorem nilpotent_iff_mem_prime : IsNilpotent x ↔ ∀ J : Ideal R, J.IsPrime → x ∈ J := by
  rw [← mem_nilradical, nilradical_eq_sInf, Submodule.mem_sInf]
  rfl
#align nilpotent_iff_mem_prime nilpotent_iff_mem_prime

theorem nilradical_le_prime (J : Ideal R) [H : J.IsPrime] : nilradical R ≤ J :=
  (nilradical_eq_sInf R).symm ▸ sInf_le H
#align nilradical_le_prime nilradical_le_prime

@[simp]
theorem nilradical_eq_zero (R : Type*) [CommSemiring R] [IsReduced R] : nilradical R = 0 :=
  Ideal.ext fun _ => isNilpotent_iff_eq_zero
#align nilradical_eq_zero nilradical_eq_zero

end CommSemiring

namespace LinearMap

variable (R) {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

@[simp]
theorem isNilpotent_mulLeft_iff (a : A) : IsNilpotent (mulLeft R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulLeft_eq_zero_iff, pow_mulLeft] at hn ⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_left_iff LinearMap.isNilpotent_mulLeft_iff

@[simp]
theorem isNilpotent_mulRight_iff (a : A) : IsNilpotent (mulRight R a) ↔ IsNilpotent a := by
  constructor <;> rintro ⟨n, hn⟩ <;> use n <;>
      simp only [mulRight_eq_zero_iff, pow_mulRight] at hn ⊢ <;>
    exact hn
#align linear_map.is_nilpotent_mul_right_iff LinearMap.isNilpotent_mulRight_iff

variable {R}
variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] [Module R M]

@[simp]
lemma isNilpotent_toMatrix_iff (b : Basis ι R M) (f : M →ₗ[R] M) :
    IsNilpotent (toMatrix b b f) ↔ IsNilpotent f := by
  refine' exists_congr fun k ↦ _
  rw [toMatrix_pow]
  exact (toMatrix b b).map_eq_zero_iff

end LinearMap

namespace Module.End

variable {M : Type v} [Ring R] [AddCommGroup M] [Module R M]

variable {f : Module.End R M} {p : Submodule R M} (hp : p ≤ p.comap f)

theorem IsNilpotent.mapQ (hnp : IsNilpotent f) : IsNilpotent (p.mapQ p f hp) := by
  obtain ⟨k, hk⟩ := hnp
  use k
  simp [← p.mapQ_pow, hk]
#align module.End.is_nilpotent.mapq Module.End.IsNilpotent.mapQ

end Module.End

lemma NoZeroSMulDivisors.isReduced (R M : Type*)
    [MonoidWithZero R] [Zero M] [MulActionWithZero R M] [Nontrivial M] [NoZeroSMulDivisors R M] :
    IsReduced R := by
  refine ⟨fun x ⟨k, hk⟩ ↦ ?_⟩
  induction' k with k ih
  · rw [Nat.zero_eq, pow_zero] at hk
    exact eq_zero_of_zero_eq_one hk.symm x
  · obtain ⟨m : M, hm : m ≠ 0⟩ := exists_ne (0 : M)
    have : x ^ (k + 1) • m = 0 := by simp only [hk, zero_smul]
    rw [pow_succ, mul_smul] at this
    rcases eq_zero_or_eq_zero_of_smul_eq_zero this with rfl | hx; rfl
    exact ih <| (eq_zero_or_eq_zero_of_smul_eq_zero hx).resolve_right hm
