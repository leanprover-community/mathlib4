/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Primitive roots of unity

We define a predicate `IsPrimitiveRoot` on commutative
monoids, expressing that an element is a primitive root of unity.

## Main definitions

* `IsPrimitiveRoot ζ k`: an element `ζ` is a primitive `k`-th root of unity if `ζ ^ k = 1`,
  and if `l` satisfies `ζ ^ l = 1` then `k ∣ l`.
* `primitiveRoots k R`: the finset of primitive `k`-th roots of unity in an integral domain `R`.
* `IsPrimitiveRoot.autToPow`: the monoid hom that takes an automorphism of a ring to the power
  it sends that specific primitive root, as a member of `(ZMod n)ˣ`.

## Main results

* `IsPrimitiveRoot.zmodEquivZPowers`: `ZMod k` is equivalent to
  the subgroup generated by a primitive `k`-th root of unity.
* `IsPrimitiveRoot.zpowers_eq`: in an integral domain, the subgroup generated by
  a primitive `k`-th root of unity is equal to the `k`-th roots of unity.
* `IsPrimitiveRoot.card_primitiveRoots`: if an integral domain
   has a primitive `k`-th root of unity, then it has `φ k` of them.

## Implementation details

For primitive roots of unity, it is desirable to have a predicate
not just on units, but directly on elements of the ring/field.
For example, we want to say that `exp (2 * pi * I / n)` is a primitive `n`-th root of unity
in the complex numbers, without having to turn that number into a unit first.

This creates a little bit of friction with how `rootsOfUnity` is implemented (as a subgroup
of the `Units`), but lemmas like `IsPrimitiveRoot.isUnit` and
`IsPrimitiveRoot.coe_units_iff` should provide the necessary glue.
-/

noncomputable section

open Polynomial Finset

variable {M N G R S F : Type*} [CommMonoid M] [CommMonoid N] [DivisionCommMonoid G]


/-- An element `ζ` is a primitive `k`-th root of unity if `ζ ^ k = 1`,
and if `l` satisfies `ζ ^ l = 1` then `k ∣ l`. -/
@[mk_iff IsPrimitiveRoot.iff_def]
structure IsPrimitiveRoot (ζ : M) (k : ℕ) : Prop where
  pow_eq_one : ζ ^ k = 1
  dvd_of_pow_eq_one : ∀ l : ℕ, ζ ^ l = 1 → k ∣ l

/-- Turn a primitive root μ into a member of the `rootsOfUnity` subgroup. -/
@[simps!]
def IsPrimitiveRoot.toRootsOfUnity {μ : M} {n : ℕ} [NeZero n] (h : IsPrimitiveRoot μ n) :
    rootsOfUnity n M :=
  rootsOfUnity.mkOfPowEq μ h.pow_eq_one

section primitiveRoots

variable {k : ℕ}

open scoped Classical in
/-- `primitiveRoots k R` is the finset of primitive `k`-th roots of unity
in the integral domain `R`. -/
def primitiveRoots (k : ℕ) (R : Type*) [CommRing R] [IsDomain R] : Finset R :=
  {ζ ∈ (nthRoots k (1 : R)).toFinset | IsPrimitiveRoot ζ k}

variable [CommRing R] [IsDomain R]

-- TODO?: replace `(h0 : 0 < k)` by `[NeZero k]`
@[simp]
theorem mem_primitiveRoots {ζ : R} (h0 : 0 < k) : ζ ∈ primitiveRoots k R ↔ IsPrimitiveRoot ζ k := by
  classical
  rw [primitiveRoots, mem_filter, Multiset.mem_toFinset, mem_nthRoots h0, and_iff_right_iff_imp]
  exact IsPrimitiveRoot.pow_eq_one

@[simp]
theorem primitiveRoots_zero : primitiveRoots 0 R = ∅ := by
  classical
  rw [primitiveRoots, nthRoots_zero, Multiset.toFinset_zero, Finset.filter_empty]

theorem isPrimitiveRoot_of_mem_primitiveRoots {ζ : R} (h : ζ ∈ primitiveRoots k R) :
    IsPrimitiveRoot ζ k :=
  k.eq_zero_or_pos.elim (fun hk ↦ by simp [hk] at h) fun hk ↦ (mem_primitiveRoots hk).1 h

end primitiveRoots

namespace IsPrimitiveRoot

variable {k l : ℕ}

theorem mk_of_lt (ζ : M) (hk : 0 < k) (h1 : ζ ^ k = 1) (h : ∀ l : ℕ, 0 < l → l < k → ζ ^ l ≠ 1) :
    IsPrimitiveRoot ζ k := by
  refine ⟨h1, fun l hl ↦ ?_⟩
  suffices k.gcd l = k by exact this ▸ k.gcd_dvd_right l
  rw [eq_iff_le_not_lt]
  refine ⟨Nat.le_of_dvd hk (k.gcd_dvd_left l), ?_⟩
  intro h'; apply h _ (Nat.gcd_pos_of_pos_left _ hk) h'
  exact pow_gcd_eq_one _ h1 hl

section CommMonoid

variable {ζ : M} {f : F}

@[nontriviality]
theorem of_subsingleton [Subsingleton M] (x : M) : IsPrimitiveRoot x 1 :=
  ⟨Subsingleton.elim _ _, fun _ _ ↦ one_dvd _⟩

theorem pow_eq_one_iff_dvd (h : IsPrimitiveRoot ζ k) (l : ℕ) : ζ ^ l = 1 ↔ k ∣ l :=
  ⟨h.dvd_of_pow_eq_one l, by
    rintro ⟨i, rfl⟩; simp only [pow_mul, h.pow_eq_one, one_pow]⟩

theorem isUnit (h : IsPrimitiveRoot ζ k) (h0 : 0 < k) : IsUnit ζ := by
  apply isUnit_of_mul_eq_one ζ (ζ ^ (k - 1))
  rw [← pow_succ', tsub_add_cancel_of_le h0.nat_succ_le, h.pow_eq_one]

theorem pow_ne_one_of_pos_of_lt (h : IsPrimitiveRoot ζ k) (h0 : 0 < l) (hl : l < k) : ζ ^ l ≠ 1 :=
  mt (Nat.le_of_dvd h0 ∘ h.dvd_of_pow_eq_one _) <| not_le_of_lt hl

theorem ne_one (h : IsPrimitiveRoot ζ k) (hk : 1 < k) : ζ ≠ 1 :=
  h.pow_ne_one_of_pos_of_lt zero_lt_one hk ∘ (pow_one ζ).trans

theorem pow_inj (h : IsPrimitiveRoot ζ k) ⦃i j : ℕ⦄ (hi : i < k) (hj : j < k) (H : ζ ^ i = ζ ^ j) :
    i = j := by
  wlog hij : i ≤ j generalizing i j
  · exact (this hj hi H.symm (le_of_not_le hij)).symm
  apply le_antisymm hij
  rw [← tsub_eq_zero_iff_le]
  apply Nat.eq_zero_of_dvd_of_lt _ (lt_of_le_of_lt tsub_le_self hj)
  apply h.dvd_of_pow_eq_one
  rw [← ((h.isUnit (lt_of_le_of_lt (Nat.zero_le _) hi)).pow i).mul_left_inj, ← pow_add,
    tsub_add_cancel_of_le hij, H, one_mul]

theorem one : IsPrimitiveRoot (1 : M) 1 :=
  { pow_eq_one := pow_one _
    dvd_of_pow_eq_one := fun _ _ ↦ one_dvd _ }

@[simp]
theorem one_right_iff : IsPrimitiveRoot ζ 1 ↔ ζ = 1 := by
  constructor
  · intro h; rw [← pow_one ζ, h.pow_eq_one]
  · rintro rfl; exact one

@[simp]
theorem coe_submonoidClass_iff {M B : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M]
    {N : B} {ζ : N} : IsPrimitiveRoot (ζ : M) k ↔ IsPrimitiveRoot ζ k := by
  simp_rw [iff_def]
  norm_cast

@[simp]
theorem coe_units_iff {ζ : Mˣ} : IsPrimitiveRoot (ζ : M) k ↔ IsPrimitiveRoot ζ k := by
  simp only [iff_def, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]

lemma isUnit_unit {ζ : M} {n} (hn) (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (hζ.isUnit hn).unit n := coe_units_iff.mp hζ

lemma isUnit_unit' {ζ : G} {n} (hn) (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (hζ.isUnit hn).unit' n := coe_units_iff.mp hζ

theorem pow_of_coprime (h : IsPrimitiveRoot ζ k) (i : ℕ) (hi : i.Coprime k) :
    IsPrimitiveRoot (ζ ^ i) k := by
  by_cases h0 : k = 0
  · subst k; simp_all only [pow_one, Nat.coprime_zero_right]
  rcases h.isUnit (Nat.pos_of_ne_zero h0) with ⟨ζ, rfl⟩
  rw [← Units.val_pow_eq_pow_val]
  rw [coe_units_iff] at h ⊢
  refine
    { pow_eq_one := by rw [← pow_mul', pow_mul, h.pow_eq_one, one_pow]
      dvd_of_pow_eq_one := fun l hl ↦ h.dvd_of_pow_eq_one l ?_ }
  rw [← pow_one ζ, ← zpow_natCast ζ, ← hi.gcd_eq_one, Nat.gcd_eq_gcd_ab, zpow_add, mul_pow,
    ← zpow_natCast, ← zpow_mul, mul_right_comm]
  simp only [zpow_mul, hl, h.pow_eq_one, one_zpow, one_pow, one_mul, zpow_natCast]

theorem pow_of_prime (h : IsPrimitiveRoot ζ k) {p : ℕ} (hprime : Nat.Prime p) (hdiv : ¬p ∣ k) :
    IsPrimitiveRoot (ζ ^ p) k :=
  h.pow_of_coprime p (hprime.coprime_iff_not_dvd.2 hdiv)

theorem pow_iff_coprime (h : IsPrimitiveRoot ζ k) (h0 : 0 < k) (i : ℕ) :
    IsPrimitiveRoot (ζ ^ i) k ↔ i.Coprime k := by
  refine ⟨fun hi ↦ ?_, h.pow_of_coprime i⟩
  obtain ⟨a, ha⟩ := i.gcd_dvd_left k
  obtain ⟨b, hb⟩ := i.gcd_dvd_right k
  suffices b = k by
    rwa [this, eq_comm, Nat.mul_left_eq_self_iff h0, ← Nat.coprime_iff_gcd_eq_one] at hb
  rw [ha] at hi
  rw [mul_comm] at hb
  apply Nat.dvd_antisymm ⟨i.gcd k, hb⟩ (hi.dvd_of_pow_eq_one b _)
  rw [← pow_mul', ← mul_assoc, ← hb, pow_mul, h.pow_eq_one, one_pow]

protected theorem orderOf (ζ : M) : IsPrimitiveRoot ζ (orderOf ζ) :=
  ⟨pow_orderOf_eq_one ζ, fun _ ↦ orderOf_dvd_of_pow_eq_one⟩

theorem unique {ζ : M} (hk : IsPrimitiveRoot ζ k) (hl : IsPrimitiveRoot ζ l) : k = l :=
  Nat.dvd_antisymm (hk.2 _ hl.1) (hl.2 _ hk.1)

theorem eq_orderOf (h : IsPrimitiveRoot ζ k) : k = orderOf ζ :=
  h.unique (IsPrimitiveRoot.orderOf ζ)

protected theorem iff (hk : 0 < k) :
    IsPrimitiveRoot ζ k ↔ ζ ^ k = 1 ∧ ∀ l : ℕ, 0 < l → l < k → ζ ^ l ≠ 1 := by
  refine ⟨fun h ↦ ⟨h.pow_eq_one, fun l hl' hl ↦ ?_⟩,
    fun ⟨hζ, hl⟩ ↦ IsPrimitiveRoot.mk_of_lt ζ hk hζ hl⟩
  rw [h.eq_orderOf] at hl
  exact pow_ne_one_of_lt_orderOf hl'.ne' hl

protected theorem not_iff : ¬IsPrimitiveRoot ζ k ↔ orderOf ζ ≠ k :=
  ⟨fun h hk ↦ h <| hk ▸ IsPrimitiveRoot.orderOf ζ,
    fun h hk ↦ h.symm <| hk.unique <| IsPrimitiveRoot.orderOf ζ⟩

theorem pow_mul_pow_lcm {ζ' : M} {k' : ℕ} (hζ : IsPrimitiveRoot ζ k) (hζ' : IsPrimitiveRoot ζ' k')
    (hk : k ≠ 0) (hk' : k' ≠ 0) :
    IsPrimitiveRoot
      (ζ ^ (k / Nat.factorizationLCMLeft k k') * ζ' ^ (k' / Nat.factorizationLCMRight k k'))
      (Nat.lcm k k') := by
  convert IsPrimitiveRoot.orderOf _
  convert ((Commute.all ζ ζ').orderOf_mul_pow_eq_lcm
    (by simpa [← hζ.eq_orderOf]) (by simpa [← hζ'.eq_orderOf])).symm using 2
  all_goals simp [hζ.eq_orderOf, hζ'.eq_orderOf]

theorem pow_of_dvd (h : IsPrimitiveRoot ζ k) {p : ℕ} (hp : p ≠ 0) (hdiv : p ∣ k) :
    IsPrimitiveRoot (ζ ^ p) (k / p) := by
  rw [h.eq_orderOf] at hdiv ⊢
  rw [← orderOf_pow_of_dvd hp hdiv]
  exact IsPrimitiveRoot.orderOf _

protected theorem mem_rootsOfUnity {ζ : Mˣ} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    ζ ∈ rootsOfUnity n M :=
  h.pow_eq_one

/-- If there is an `n`-th primitive root of unity in `R` and `b` divides `n`,
then there is a `b`-th primitive root of unity in `R`. -/
theorem pow {n : ℕ} {a b : ℕ} (hn : 0 < n) (h : IsPrimitiveRoot ζ n) (hprod : n = a * b) :
    IsPrimitiveRoot (ζ ^ a) b := by
  subst n
  simp only [iff_def, ← pow_mul, h.pow_eq_one, true_and]
  intro l hl
  exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_mul_pos_right hn) <| h.dvd_of_pow_eq_one _ hl

lemma injOn_pow {n : ℕ} {ζ : M} (hζ : IsPrimitiveRoot ζ n) :
    Set.InjOn (ζ ^ ·) (Finset.range n) := by
  intros i hi j hj e
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  exact hζ.pow_inj hi hj e

lemma exists_pos {k : ℕ} (hζ : ζ ^ k = 1) (hk : k ≠ 0) :
    ∃ k' > 0, IsPrimitiveRoot ζ k' :=
  ⟨orderOf ζ, by
    rw [gt_iff_lt, orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    exact ⟨k, Nat.pos_iff_ne_zero.mpr hk, hζ⟩, .orderOf _⟩

lemma existsUnique : ∃! k, IsPrimitiveRoot ζ k :=
  ⟨_, .orderOf _, fun _ hl ↦ unique hl (.orderOf _)⟩

section Maps

open Function

variable [FunLike F M N]

theorem map_of_injective [MonoidHomClass F M N] (h : IsPrimitiveRoot ζ k) (hf : Injective f) :
    IsPrimitiveRoot (f ζ) k where
  pow_eq_one := by rw [← map_pow, h.pow_eq_one, map_one]
  dvd_of_pow_eq_one := by
    rw [h.eq_orderOf]
    intro l hl
    rw [← map_pow, ← map_one f] at hl
    exact orderOf_dvd_of_pow_eq_one (hf hl)

theorem of_map_of_injective [MonoidHomClass F M N] (h : IsPrimitiveRoot (f ζ) k)
    (hf : Injective f) : IsPrimitiveRoot ζ k where
  pow_eq_one := by apply_fun f; rw [map_pow, map_one, h.pow_eq_one]
  dvd_of_pow_eq_one := by
    rw [h.eq_orderOf]
    intro l hl
    apply_fun f at hl
    rw [map_pow, map_one] at hl
    exact orderOf_dvd_of_pow_eq_one hl

theorem map_iff_of_injective [MonoidHomClass F M N] (hf : Injective f) :
    IsPrimitiveRoot (f ζ) k ↔ IsPrimitiveRoot ζ k :=
  ⟨fun h => h.of_map_of_injective hf, fun h => h.map_of_injective hf⟩

end Maps

end CommMonoid

section CommMonoidWithZero

variable {M₀ : Type*} [CommMonoidWithZero M₀]

theorem zero [Nontrivial M₀] : IsPrimitiveRoot (0 : M₀) 0 :=
  ⟨pow_zero 0, fun l hl ↦ by simpa [zero_pow_eq] using hl⟩

protected theorem ne_zero [Nontrivial M₀] {ζ : M₀} (h : IsPrimitiveRoot ζ k) : k ≠ 0 → ζ ≠ 0 :=
  mt fun hn ↦ h.unique (hn.symm ▸ IsPrimitiveRoot.zero)

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable {M₀ : Type*} [CancelCommMonoidWithZero M₀]

lemma injOn_pow_mul {n : ℕ} {ζ : M₀} (hζ : IsPrimitiveRoot ζ n) {α : M₀} (hα : α ≠ 0) :
    Set.InjOn (ζ ^ · * α) (Finset.range n) :=
  fun i hi j hj e ↦
    hζ.injOn_pow hi hj (by simpa [mul_eq_mul_right_iff, or_iff_left hα] using e)

end CancelCommMonoidWithZero

section DivisionCommMonoid

variable {ζ : G}

theorem zpow_eq_one (h : IsPrimitiveRoot ζ k) : ζ ^ (k : ℤ) = 1 := by
  exact_mod_cast h.pow_eq_one

theorem zpow_eq_one_iff_dvd (h : IsPrimitiveRoot ζ k) (l : ℤ) : ζ ^ l = 1 ↔ (k : ℤ) ∣ l := by
  by_cases h0 : 0 ≤ l
  · lift l to ℕ using h0; exact_mod_cast h.pow_eq_one_iff_dvd l
  · have : 0 ≤ -l := (Int.neg_pos_of_neg <| Int.lt_of_not_ge h0).le
    lift -l to ℕ using this with l' hl'
    rw [← dvd_neg, ← hl']
    norm_cast
    rw [← h.pow_eq_one_iff_dvd, ← inv_inj, ← zpow_neg, ← hl', zpow_natCast, inv_one]

theorem inv (h : IsPrimitiveRoot ζ k) : IsPrimitiveRoot ζ⁻¹ k :=
  { pow_eq_one := by simp only [h.pow_eq_one, inv_one, eq_self_iff_true, inv_pow]
    dvd_of_pow_eq_one := by
      intro l hl
      apply h.dvd_of_pow_eq_one l
      rw [← inv_inj, ← inv_pow, hl, inv_one] }

@[simp]
theorem inv_iff : IsPrimitiveRoot ζ⁻¹ k ↔ IsPrimitiveRoot ζ k :=
  ⟨fun h ↦ inv_inv ζ ▸ inv h, fun h ↦ inv h⟩

theorem zpow_of_gcd_eq_one (h : IsPrimitiveRoot ζ k) (i : ℤ) (hi : i.gcd k = 1) :
    IsPrimitiveRoot (ζ ^ i) k := by
  by_cases h0 : 0 ≤ i
  · lift i to ℕ using h0
    exact_mod_cast h.pow_of_coprime i hi
  have : 0 ≤ -i := (Int.neg_pos_of_neg <| Int.lt_of_not_ge h0).le
  lift -i to ℕ using this with i' hi'
  rw [← inv_iff, ← zpow_neg, ← hi', zpow_natCast]
  apply h.pow_of_coprime
  rwa [Int.gcd, ← Int.natAbs_neg, ← hi'] at hi

end DivisionCommMonoid

section CommRing

variable [CommRing R] {n : ℕ} {ζ : R}

theorem sub_one_ne_zero (hn : 1 < n) (hζ : IsPrimitiveRoot ζ n) : ζ - 1 ≠ 0 :=
  sub_ne_zero.mpr <| hζ.ne_one hn

end CommRing

section IsDomain

variable {ζ : R} [CommRing R] [IsDomain R]

@[simp]
theorem primitiveRoots_one : primitiveRoots 1 R = {(1 : R)} := by
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun x hx ↦ ?_⟩
  · simp only [IsPrimitiveRoot.one_right_iff, mem_primitiveRoots zero_lt_one]
  · rwa [mem_primitiveRoots zero_lt_one, IsPrimitiveRoot.one_right_iff] at hx

theorem neZero' {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) : NeZero ((n : ℕ) : R) := by
  let p := ringChar R
  have hfin := Nat.finiteMultiplicity_iff.2 ⟨CharP.char_ne_one R p, NeZero.pos n⟩
  obtain ⟨m, hm⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  by_cases hp : p ∣ n
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (multiplicity_pos_of_dvd hp).ne'
    have : NeZero p := NeZero.of_pos (Nat.pos_of_dvd_of_pos hp (NeZero.pos n))
    have hpri : Fact p.Prime := CharP.char_is_prime_of_pos R p
    have := hζ.pow_eq_one
    rw [hm.1, hk, pow_succ', mul_assoc, pow_mul', ← frobenius_def, ← frobenius_one p] at this
    exfalso
    have hpos : 0 < p ^ k * m :=
      mul_pos (pow_pos hpri.1.pos _) <| Nat.pos_of_ne_zero (fun H ↦ hm.2 <| H ▸ p.dvd_zero)
    refine hζ.pow_ne_one_of_pos_of_lt hpos ?_ (frobenius_inj R p this)
    rw [hm.1, hk, pow_succ', mul_assoc, mul_comm p]
    exact lt_mul_of_one_lt_right hpos hpri.1.one_lt
  · exact NeZero.of_not_dvd R hp

nonrec theorem mem_nthRootsFinset (hζ : IsPrimitiveRoot ζ k) (hk : 0 < k) :
    ζ ∈ nthRootsFinset k R :=
  (mem_nthRootsFinset hk).2 hζ.pow_eq_one

end IsDomain

section IsDomain

variable [CommRing R] {ζ : Rˣ} (h : IsPrimitiveRoot ζ k)

theorem eq_neg_one_of_two_right [NoZeroDivisors R] {ζ : R} (h : IsPrimitiveRoot ζ 2) : ζ = -1 :=
  (sq_eq_one_iff.mp h.pow_eq_one).resolve_left <| ne_one h one_lt_two

theorem neg_one (p : ℕ) [Nontrivial R] [h : CharP R p] (hp : p ≠ 2) :
    IsPrimitiveRoot (-1 : R) 2 := by
  convert IsPrimitiveRoot.orderOf (-1 : R)
  rw [orderOf_neg_one, if_neg <| by rwa [ringChar.eq_iff.mpr h]]

/-- If `1 < k` then `(∑ i ∈ range k, ζ ^ i) = 0`. -/
theorem geom_sum_eq_zero [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) :
    ∑ i ∈ range k, ζ ^ i = 0 := by
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne (hζ.ne_one hk).symm) ?_
  rw [mul_neg_geom_sum, hζ.pow_eq_one, sub_self]

/-- If `1 < k`, then `ζ ^ k.pred = -(∑ i ∈ range k.pred, ζ ^ i)`. -/
theorem pow_sub_one_eq [IsDomain R] {ζ : R} (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) :
    ζ ^ k.pred = -∑ i ∈ range k.pred, ζ ^ i := by
  rw [eq_neg_iff_add_eq_zero, add_comm, ← sum_range_succ, ← Nat.succ_eq_add_one,
    Nat.succ_pred_eq_of_pos (pos_of_gt hk), hζ.geom_sum_eq_zero hk]

/-- The (additive) monoid equivalence between `ZMod k`
and the powers of a primitive root of unity `ζ`. -/
def zmodEquivZPowers (h : IsPrimitiveRoot ζ k) : ZMod k ≃+ Additive (Subgroup.zpowers ζ) :=
  AddEquiv.ofBijective
    (AddMonoidHom.liftOfRightInverse (Int.castAddHom <| ZMod k) _ ZMod.intCast_rightInverse
      ⟨{  toFun := fun i ↦ Additive.ofMul (⟨_, i, rfl⟩ : Subgroup.zpowers ζ)
          map_zero' := by simp only [zpow_zero]; rfl
          map_add' := by intro i j; simp only [zpow_add]; rfl }, fun i hi ↦ by
        simp only [AddMonoidHom.mem_ker, CharP.intCast_eq_zero_iff (ZMod k) k, AddMonoidHom.coe_mk,
          Int.coe_castAddHom] at hi ⊢
        obtain ⟨i, rfl⟩ := hi
        simp [zpow_mul, h.pow_eq_one, one_zpow, zpow_natCast]⟩)
    (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro i hi
        rw [Subtype.ext_iff] at hi
        have := (h.zpow_eq_one_iff_dvd _).mp hi
        rw [← (CharP.intCast_eq_zero_iff (ZMod k) k _).mpr this, eq_comm]
        exact ZMod.intCast_rightInverse i
      · rintro ⟨ξ, i, rfl⟩
        refine ⟨Int.castAddHom (ZMod k) i, ?_⟩
        rw [AddMonoidHom.liftOfRightInverse_comp_apply]
        rfl)

@[simp]
theorem zmodEquivZPowers_apply_coe_int (i : ℤ) :
    h.zmodEquivZPowers i = Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ) := by
  rw [zmodEquivZPowers, AddEquiv.ofBijective_apply] -- Porting note: Original proof didn't have `rw`
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ ZMod.intCast_rightInverse _ _

@[simp]
theorem zmodEquivZPowers_apply_coe_nat (i : ℕ) :
    h.zmodEquivZPowers i = Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ) := by
  have : (i : ZMod k) = (i : ℤ) := by norm_cast
  simp only [this, zmodEquivZPowers_apply_coe_int, zpow_natCast]

@[simp]
theorem zmodEquivZPowers_symm_apply_zpow (i : ℤ) :
    h.zmodEquivZPowers.symm (Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ)) = i := by
  rw [← h.zmodEquivZPowers.symm_apply_apply i, zmodEquivZPowers_apply_coe_int]

@[simp]
theorem zmodEquivZPowers_symm_apply_zpow' (i : ℤ) : h.zmodEquivZPowers.symm ⟨ζ ^ i, i, rfl⟩ = i :=
  h.zmodEquivZPowers_symm_apply_zpow i

@[simp]
theorem zmodEquivZPowers_symm_apply_pow (i : ℕ) :
    h.zmodEquivZPowers.symm (Additive.ofMul (⟨ζ ^ i, i, rfl⟩ : Subgroup.zpowers ζ)) = i := by
  rw [← h.zmodEquivZPowers.symm_apply_apply i, zmodEquivZPowers_apply_coe_nat]

@[simp]
theorem zmodEquivZPowers_symm_apply_pow' (i : ℕ) : h.zmodEquivZPowers.symm ⟨ζ ^ i, i, rfl⟩ = i :=
  h.zmodEquivZPowers_symm_apply_pow i

variable [IsDomain R]

theorem zpowers_eq {k : ℕ} [NeZero k] {ζ : Rˣ} (h : IsPrimitiveRoot ζ k) :
    Subgroup.zpowers ζ = rootsOfUnity k R := by
  apply SetLike.coe_injective
  have F : Fintype (Subgroup.zpowers ζ) := Fintype.ofEquiv _ h.zmodEquivZPowers.toEquiv
  refine
    @Set.eq_of_subset_of_card_le Rˣ _ _ F (rootsOfUnity.fintype R k)
      (Subgroup.zpowers_le_of_mem <| show ζ ∈ rootsOfUnity k R from h.pow_eq_one) ?_
  calc
    Fintype.card (rootsOfUnity k R) ≤ k := card_rootsOfUnity R k
    _ = Fintype.card (ZMod k) := (ZMod.card k).symm
    _ = Fintype.card (Subgroup.zpowers ζ) := Fintype.card_congr h.zmodEquivZPowers.toEquiv

lemma map_rootsOfUnity {S F} [CommRing S] [IsDomain S] [FunLike F R S] [MonoidHomClass F R S]
    {ζ : R} {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n) {f : F} (hf : Function.Injective f) :
    (rootsOfUnity n R).map (Units.map f) = rootsOfUnity n S := by
  letI : CommMonoid Sˣ := inferInstance
  replace hζ := hζ.isUnit_unit <| NeZero.pos n
  rw [← hζ.zpowers_eq,
    ← (hζ.map_of_injective (Units.map_injective (f := (f : R →* S)) hf)).zpowers_eq,
    MonoidHom.map_zpowers]

/-- If `R` contains an `n`-th primitive root, and `S/R` is a ring extension,
then the `n`-th roots of unity in `R` and `S` are isomorphic.
Also see `IsPrimitiveRoot.map_rootsOfUnity` for the equality as `Subgroup Sˣ`. -/
@[simps! -isSimp apply_coe_val apply_coe_inv_val]
noncomputable
def _root_.rootsOfUnityEquivOfPrimitiveRoots {S F} [CommRing S] [IsDomain S]
    [FunLike F R S] [MonoidHomClass F R S]
    {n : ℕ} [NeZero n] {f : F} (hf : Function.Injective f) (hζ : (primitiveRoots n R).Nonempty) :
    (rootsOfUnity n R) ≃* rootsOfUnity n S :=
  (Subgroup.equivMapOfInjective _ (Units.map f) (Units.map_injective hf)).trans
    (MulEquiv.subgroupCongr <|
      ((mem_primitiveRoots <| NeZero.pos n).mp hζ.choose_spec).map_rootsOfUnity hf)

lemma _root_.rootsOfUnityEquivOfPrimitiveRoots_symm_apply
    {S F} [CommRing S] [IsDomain S] [FunLike F R S] [MonoidHomClass F R S] {n : ℕ} [NeZero n]
    {f : F} (hf : Function.Injective f) (hζ : (primitiveRoots n R).Nonempty) (η) :
    f ((rootsOfUnityEquivOfPrimitiveRoots hf hζ).symm η : Rˣ) = (η : Sˣ) := by
  obtain ⟨ε, rfl⟩ := (rootsOfUnityEquivOfPrimitiveRoots hf hζ).surjective η
  rw [MulEquiv.symm_apply_apply, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe]

-- Porting note: rephrased the next few lemmas to avoid `∃ (Prop)`
theorem eq_pow_of_mem_rootsOfUnity {k : ℕ} [NeZero k] {ζ ξ : Rˣ} (h : IsPrimitiveRoot ζ k)
    (hξ : ξ ∈ rootsOfUnity k R) : ∃ i < k, ζ ^ i = ξ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℤ, ζ ^ n = ξ := by rwa [← h.zpowers_eq] at hξ
  have hk0 : (0 : ℤ) < k := mod_cast NeZero.pos k
  let i := n % k
  have hi0 : 0 ≤ i := Int.emod_nonneg _ (ne_of_gt hk0)
  lift i to ℕ using hi0 with i₀ hi₀
  refine ⟨i₀, ?_, ?_⟩
  · zify; rw [hi₀]; exact Int.emod_lt_of_pos _ hk0
  · rw [← zpow_natCast, hi₀, ← Int.emod_add_ediv n k, zpow_add, zpow_mul, h.zpow_eq_one, one_zpow,
      mul_one]

theorem eq_pow_of_pow_eq_one {k : ℕ} [NeZero k] {ζ ξ : R} (h : IsPrimitiveRoot ζ k)
    (hξ : ξ ^ k = 1) :
    ∃ i < k, ζ ^ i = ξ := by
  lift ζ to Rˣ using h.isUnit <| NeZero.pos k
  lift ξ to Rˣ using .of_pow_eq_one hξ <| NeZero.ne k
  simp only [← Units.val_pow_eq_pow_val, ← Units.ext_iff]
  rw [coe_units_iff] at h
  exact h.eq_pow_of_mem_rootsOfUnity <| (mem_rootsOfUnity' k ξ).mpr hξ

theorem isPrimitiveRoot_iff' {k : ℕ} [NeZero k] {ζ ξ : Rˣ} (h : IsPrimitiveRoot ζ k) :
    IsPrimitiveRoot ξ k ↔ ∃ i < k, i.Coprime k ∧ ζ ^ i = ξ := by
  constructor
  · intro hξ
    obtain ⟨i, hik, rfl⟩ := h.eq_pow_of_mem_rootsOfUnity hξ.pow_eq_one
    rw [h.pow_iff_coprime <| NeZero.pos k] at hξ
    exact ⟨i, hik, hξ, rfl⟩
  · rintro ⟨i, -, hi, rfl⟩; exact h.pow_of_coprime i hi

theorem isPrimitiveRoot_iff {k : ℕ} [NeZero k] {ζ ξ : R} (h : IsPrimitiveRoot ζ k) :
    IsPrimitiveRoot ξ k ↔ ∃ i < k, i.Coprime k ∧ ζ ^ i = ξ := by
  constructor
  · intro hξ
    obtain ⟨i, hik, rfl⟩ := h.eq_pow_of_pow_eq_one hξ.pow_eq_one
    rw [h.pow_iff_coprime <| NeZero.pos k] at hξ
    exact ⟨i, hik, hξ, rfl⟩
  · rintro ⟨i, -, hi, rfl⟩; exact h.pow_of_coprime i hi

theorem nthRoots_eq {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) {α a : R} (e : α ^ n = a) :
    nthRoots n a = (Multiset.range n).map (ζ ^ · * α) := by
  obtain (rfl | hn) := n.eq_zero_or_pos; · simp
  by_cases hα : α = 0
  · rw [hα, zero_pow hn.ne'] at e
    simp only [hα, e.symm, nthRoots_zero_right, mul_zero,
      Finset.range_val, Multiset.map_const', Multiset.card_range]
  classical
  symm; apply Multiset.eq_of_le_of_card_le
  · rw [← Finset.range_val,
      ← Finset.image_val_of_injOn (hζ.injOn_pow_mul hα), Finset.val_le_iff_val_subset]
    intro x hx
    simp only [Finset.image_val, Finset.range_val, Multiset.mem_dedup, Multiset.mem_map,
      Multiset.mem_range] at hx
    obtain ⟨m, _, rfl⟩ := hx
    rw [mem_nthRoots hn, mul_pow, e, ← pow_mul, mul_comm m,
      pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  · simpa only [Multiset.card_map, Multiset.card_range] using card_nthRoots n a

open scoped Classical in
theorem card_nthRoots {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) (a : R) :
    Multiset.card (nthRoots n a) = if ∃ α, α ^ n = a then n else 0 := by
  split_ifs with h
  · obtain ⟨α, hα⟩ := h
    rw [nthRoots_eq hζ hα, Multiset.card_map, Multiset.card_range]
  · obtain (rfl|hn) := n.eq_zero_or_pos; · simp
    push_neg at h
    simpa only [Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_not_mem, mem_nthRoots hn]

/-- A variant of `IsPrimitiveRoot.card_rootsOfUnity` for `ζ : Rˣ`. -/
theorem card_rootsOfUnity' {n : ℕ} [NeZero n] (h : IsPrimitiveRoot ζ n) :
    Fintype.card (rootsOfUnity n R) = n := by
  let e := h.zmodEquivZPowers
  have : Fintype (Subgroup.zpowers ζ) := Fintype.ofEquiv _ e.toEquiv
  calc
    Fintype.card (rootsOfUnity n R) = Fintype.card (Subgroup.zpowers ζ) :=
      Fintype.card_congr <| by rw [h.zpowers_eq]
    _ = Fintype.card (ZMod n) := Fintype.card_congr e.toEquiv.symm
    _ = n := ZMod.card n

theorem card_rootsOfUnity {ζ : R} {n : ℕ} [NeZero n] (h : IsPrimitiveRoot ζ n) :
    Fintype.card (rootsOfUnity n R) = n := by
  obtain ⟨ζ, hζ⟩ := h.isUnit <| NeZero.pos n
  rw [← hζ, IsPrimitiveRoot.coe_units_iff] at h
  exact h.card_rootsOfUnity'

/-- The cardinality of the multiset `nthRoots ↑n (1 : R)` is `n`
if there is a primitive root of unity in `R`. -/
theorem card_nthRoots_one {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    Multiset.card (nthRoots n (1 : R)) = n := by
  rw [card_nthRoots h, if_pos ⟨ζ, h.pow_eq_one⟩]

theorem nthRoots_nodup {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) {a : R} (ha : a ≠ 0) :
    (nthRoots n a).Nodup := by
  obtain (rfl | hn) := n.eq_zero_or_pos; · simp
  by_cases h : ∃ α, α ^ n = a
  · obtain ⟨α, hα⟩ := h
    by_cases hα' : α = 0
    · exact (ha (by rwa [hα', zero_pow hn.ne', eq_comm] at hα)).elim
    rw [nthRoots_eq h hα, Multiset.nodup_map_iff_inj_on (Multiset.nodup_range n)]
    exact h.injOn_pow_mul hα'
  · suffices nthRoots n a = 0 by simp [this]
    push_neg at h
    simpa only [Multiset.card_eq_zero, Multiset.eq_zero_iff_forall_not_mem, mem_nthRoots hn]

/-- The multiset `nthRoots ↑n (1 : R)` has no repeated elements
if there is a primitive root of unity in `R`. -/
theorem nthRoots_one_nodup {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    (nthRoots n (1 : R)).Nodup :=
  h.nthRoots_nodup one_ne_zero

@[simp]
theorem card_nthRootsFinset {ζ : R} {n : ℕ} (h : IsPrimitiveRoot ζ n) :
    #(nthRootsFinset n R) = n := by
  classical
  rw [nthRootsFinset, ← Multiset.toFinset_eq (nthRoots_one_nodup h), card_mk, h.card_nthRoots_one]

open scoped Nat

/-- If an integral domain has a primitive `k`-th root of unity, then it has `φ k` of them. -/
theorem card_primitiveRoots {ζ : R} {k : ℕ} (h : IsPrimitiveRoot ζ k) :
    #(primitiveRoots k R) = φ k := by
  by_cases h0 : k = 0
  · simp [h0]
  have : NeZero k := ⟨h0⟩
  symm
  refine Finset.card_bij (fun i _ ↦ ζ ^ i) ?_ ?_ ?_
  · simp only [and_imp, mem_filter, mem_range, mem_univ]
    rintro i - hi
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero h0)]
    exact h.pow_of_coprime i hi.symm
  · simp only [and_imp, mem_filter, mem_range, mem_univ]
    rintro i hi - j hj - H
    exact h.pow_inj hi hj H
  · simp only [exists_prop, mem_filter, mem_range, mem_univ]
    intro ξ hξ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero h0), h.isPrimitiveRoot_iff] at hξ
    rcases hξ with ⟨i, hin, hi, H⟩
    exact ⟨i, ⟨hin, hi.symm⟩, H⟩

/-- The sets `primitiveRoots k R` are pairwise disjoint. -/
theorem disjoint {k l : ℕ} (h : k ≠ l) : Disjoint (primitiveRoots k R) (primitiveRoots l R) :=
  Finset.disjoint_left.2 fun _ hk hl ↦
    h <|
      (isPrimitiveRoot_of_mem_primitiveRoots hk).unique <| isPrimitiveRoot_of_mem_primitiveRoots hl

/-- `nthRoots n` as a `Finset` is equal to the union of `primitiveRoots i R` for `i ∣ n`. -/
private -- marking as `private` since `nthRoots_one_eq_biUnion_primitiveRoots` can be used instead
theorem nthRoots_one_eq_biUnion_primitiveRoots' [DecidableEq R] {n : ℕ} [NeZero n] :
    nthRootsFinset n R = (Nat.divisors n).biUnion fun i ↦ primitiveRoots i R := by
  ext x
  suffices x ^ n = 1 ↔ ∃ a, a ∣ n ∧ x ∈ primitiveRoots a R by
    simpa [Polynomial.mem_nthRootsFinset (NeZero.pos n), (NeZero.ne n)]
  constructor
  · intro H
    obtain ⟨k, hk, hx⟩ := exists_pos H (NeZero.ne n)
    exact ⟨k, hx.2 _ H, (mem_primitiveRoots hk).mpr hx⟩
  · rintro ⟨a, ⟨d, hd⟩, ha⟩
    have hazero : 0 < a := Nat.pos_of_ne_zero fun ha₀ ↦ by simp_all
    rw [mem_primitiveRoots hazero] at ha
    rw [hd, pow_mul, ha.pow_eq_one, one_pow]

/-- `nthRoots n` as a `Finset` is equal to the union of `primitiveRoots i R` for `i ∣ n`. -/
theorem nthRoots_one_eq_biUnion_primitiveRoots [DecidableEq R] {n : ℕ} :
    nthRootsFinset n R = (Nat.divisors n).biUnion fun i ↦ primitiveRoots i R := by
  by_cases hn : n = 0
  · simp only [hn, nthRootsFinset_zero, Nat.divisors_zero, biUnion_empty]
  have : NeZero n := ⟨hn⟩
  exact nthRoots_one_eq_biUnion_primitiveRoots'

end IsDomain

section Automorphisms

variable [CommRing S] [IsDomain S] {μ : S} {n : ℕ} (hμ : IsPrimitiveRoot μ n) (R) [CommRing R]
  [Algebra R S]

/-- The `MonoidHom` that takes an automorphism to the power of `μ` that `μ` gets mapped to
under it. -/
noncomputable def autToPow [NeZero n] : (S ≃ₐ[R] S) →* (ZMod n)ˣ :=
  let μ' := hμ.toRootsOfUnity
  have ho : orderOf μ' = n := by
    refine Eq.trans ?_ hμ.eq_orderOf.symm -- `rw [hμ.eq_orderOf]` gives "motive not type correct"
    rw [← hμ.val_toRootsOfUnity_coe, orderOf_units, Subgroup.orderOf_coe]
  MonoidHom.toHomUnits
    { toFun := fun σ ↦ (map_rootsOfUnity_eq_pow_self σ.toAlgHom μ').choose
      map_one' := by
        dsimp only
        generalize_proofs h1
        have h := h1.choose_spec
        replace h : μ' = μ' ^ h1.choose :=
          rootsOfUnity.coe_injective (by simpa only [rootsOfUnity.coe_pow] using h)
        nth_rw 1 [← pow_one μ'] at h
        convert ho ▸ (ZMod.natCast_eq_natCast_iff ..).mpr (pow_eq_pow_iff_modEq.mp h).symm
        exact Nat.cast_one.symm
      map_mul' := by
        intro x y
        dsimp only
        generalize_proofs hxy' hx' hy'
        have hxy := hxy'.choose_spec
        replace hxy : x (((μ' : Sˣ) : S) ^ hy'.choose) = ((μ' : Sˣ) : S) ^ hxy'.choose :=
          hy'.choose_spec ▸ hxy
        rw [map_pow] at hxy
        replace hxy : (((μ' : Sˣ) : S) ^ hx'.choose) ^ hy'.choose = ((μ' : Sˣ) : S) ^ hxy'.choose :=
          hx'.choose_spec ▸ hxy
        rw [← pow_mul] at hxy
        replace hxy : μ' ^ (hx'.choose * hy'.choose) = μ' ^ hxy'.choose :=
          rootsOfUnity.coe_injective (by simpa only [rootsOfUnity.coe_pow] using hxy)
        convert ho ▸ (ZMod.natCast_eq_natCast_iff ..).mpr (pow_eq_pow_iff_modEq.mp hxy).symm
        exact (Nat.cast_mul ..).symm }

-- We are not using @[simps] in `autToPow` to avoid a timeout.
theorem coe_autToPow_apply [NeZero n] (f : S ≃ₐ[R] S) :
    (autToPow R hμ f : ZMod n) =
      ((map_rootsOfUnity_eq_pow_self f hμ.toRootsOfUnity).choose : ZMod n) :=
  rfl

@[simp]
theorem autToPow_spec [NeZero n] (f : S ≃ₐ[R] S) : μ ^ (hμ.autToPow R f : ZMod n).val = f μ := by
  rw [IsPrimitiveRoot.coe_autToPow_apply]
  generalize_proofs h
  refine (?_ : ((hμ.toRootsOfUnity : Sˣ) : S) ^ _ = _).trans h.choose_spec.symm
  rw [← rootsOfUnity.coe_pow, ← rootsOfUnity.coe_pow]
  congr 2
  rw [pow_eq_pow_iff_modEq, ZMod.val_natCast]
  conv => enter [2, 2]; rw [hμ.eq_orderOf]
  rw [← Subgroup.orderOf_coe, ← orderOf_units]
  exact Nat.mod_modEq _ _

end Automorphisms

end IsPrimitiveRoot

section cyclic

/-- If `G` is cyclic of order `n` and `G'` contains a primitive `n`th root of unity,
then for each `a : G` with `a ≠ 1` there is a homomorphism `φ : G →* G'` such that `φ a ≠ 1`. -/
lemma IsCyclic.exists_apply_ne_one {G G' : Type*} [CommGroup G] [IsCyclic G] [Finite G]
    [CommGroup G'] (hG' : ∃ ζ : G', IsPrimitiveRoot ζ (Nat.card G)) ⦃a : G⦄ (ha : a ≠ 1) :
    ∃ φ : G →* G', φ a ≠ 1 := by
  let inst : Fintype G := Fintype.ofFinite _
  obtain ⟨ζ, hζ⟩ := hG'
  -- pick a generator `g` of `G`
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hζg : orderOf ζ ∣ orderOf g := by
    rw [← hζ.eq_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  -- use the homomorphism `φ` given by `g ↦ ζ`
  let φ := monoidHomOfForallMemZpowers hg hζg
  have hφg : IsPrimitiveRoot (φ g) (Nat.card G) := by
    rwa [monoidHomOfForallMemZpowers_apply_gen hg hζg]
  use φ
  contrapose! ha
  specialize hg a
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hg
  obtain ⟨k, hk⟩ := hg
  rw [← hk, map_pow] at ha
  obtain ⟨l, rfl⟩ := (hφg.pow_eq_one_iff_dvd k).mp ha
  rw [← hk, pow_mul, Nat.card_eq_fintype_card, pow_card_eq_one, one_pow]

/-- If `M` is a commutative group that contains a primitive `n`th root of unity
and `a : ZMod n` is nonzero, then there exists a group homomorphism `φ` from the
additive group `ZMod n` to the multiplicative group `Mˣ` such that `φ a ≠ 1`. -/
lemma ZMod.exists_monoidHom_apply_ne_one {M : Type*} [CommMonoid M] {n : ℕ} [NeZero n]
    (hG : ∃ ζ : M, IsPrimitiveRoot ζ n) {a : ZMod n} (ha : a ≠ 0) :
    ∃ φ : Multiplicative (ZMod n) →* Mˣ, φ (Multiplicative.ofAdd a) ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := hG
  have hc : n = Nat.card (Multiplicative (ZMod n)) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, card]
  exact IsCyclic.exists_apply_ne_one
    (hc ▸ ⟨hζ.toRootsOfUnity.val, IsPrimitiveRoot.coe_units_iff.mp hζ⟩) <|
    by simp only [ne_eq, ofAdd_eq_one, ha, not_false_eq_true]

end cyclic
