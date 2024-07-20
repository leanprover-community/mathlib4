/-
Copyright (c) 2020 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Newell Jensen
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.PresentedGroup

/-!
# Dihedral Groups

We define the dihedral groups `DihedralGroup n`, with elements `r i` and `sr i` for `i : ZMod n`.

For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon. `r i`
represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of the
`n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/


/-- For `n ≠ 0`, `DihedralGroup n` represents the symmetry group of the regular `n`-gon.
`r i` represents the rotations of the `n`-gon by `2πi/n`, and `sr i` represents the reflections of
the `n`-gon. `DihedralGroup 0` corresponds to the infinite dihedral group.
-/
inductive DihedralGroup (n : ℕ) : Type
  | r : ZMod n → DihedralGroup n
  | sr : ZMod n → DihedralGroup n
  deriving DecidableEq

namespace DihedralGroup

variable {n : ℕ}

/-- Multiplication of the dihedral group.
-/
private def mul : DihedralGroup n → DihedralGroup n → DihedralGroup n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

/-- The identity `1` is the rotation by `0`.
-/
private def one : DihedralGroup n :=
  r 0

instance : Inhabited (DihedralGroup n) :=
  ⟨one⟩

/-- The inverse of an element of the dihedral group.
-/
private def inv : DihedralGroup n → DihedralGroup n
  | r i => r (-i)
  | sr i => sr i

/-- The group structure on `DihedralGroup n`.
-/
instance : Group (DihedralGroup n) where
  mul := mul
  mul_assoc := by rintro (a | a) (b | b) (c | c) <;> simp only [(· * ·), mul] <;> ring_nf
  one := one
  one_mul := by
    rintro (a | a)
    · exact congr_arg r (zero_add a)
    · exact congr_arg sr (sub_zero a)
  mul_one := by
    rintro (a | a)
    · exact congr_arg r (add_zero a)
    · exact congr_arg sr (add_zero a)
  inv := inv
  mul_left_inv := by
    rintro (a | a)
    · exact congr_arg r (neg_add_self a)
    · exact congr_arg r (sub_self a)

@[simp]
theorem r_mul_r (i j : ZMod n) : r i * r j = r (i + j) :=
  rfl

@[simp]
theorem r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) :=
  rfl

@[simp]
theorem sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) :=
  rfl

@[simp]
theorem sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) :=
  rfl

@[simp]
theorem one_def : (1 : DihedralGroup n) = r 0 :=
  rfl

@[simp]
theorem r_inv_eq_r_neg {i : ZMod n} : (r i)⁻¹ = r (-i) :=
  rfl

private def fintypeHelper : Sum (ZMod n) (ZMod n) ≃ DihedralGroup n where
  invFun i := match i with
    | r j => Sum.inl j
    | sr j => Sum.inr j
  toFun i := match i with
    | Sum.inl j => r j
    | Sum.inr j => sr j
  left_inv := by rintro (x | x) <;> rfl
  right_inv := by rintro (x | x) <;> rfl

/-- If `0 < n`, then `DihedralGroup n` is a finite group.
-/
instance [NeZero n] : Fintype (DihedralGroup n) :=
  Fintype.ofEquiv _ fintypeHelper

instance : Infinite (DihedralGroup 0) :=
  DihedralGroup.fintypeHelper.infinite_iff.mp inferInstance

instance : Nontrivial (DihedralGroup n) :=
  ⟨⟨r 0, sr 0, by simp_rw [ne_eq, not_false_eq_true]⟩⟩

/-- If `0 < n`, then `DihedralGroup n` has `2n` elements.
-/
theorem card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n := by
  rw [← Fintype.card_eq.mpr ⟨fintypeHelper⟩, Fintype.card_sum, ZMod.card, two_mul]

theorem nat_card : Nat.card (DihedralGroup n) = 2 * n := by
  cases n
  · rw [Nat.card_eq_zero_of_infinite]
  · rw [Nat.card_eq_fintype_card, card]

@[simp]
theorem r_one_pow (k : ℕ) : (r 1 : DihedralGroup n) ^ k = r k := by
  induction' k with k IH
  · rw [Nat.cast_zero]
    rfl
  · rw [pow_succ', IH, r_mul_r]
    congr 1
    norm_cast
    rw [Nat.one_add]

@[simp]
theorem r_one_zpow (n : ℕ) (i : ℤ) :
    r (1 : ZMod n) ^ i = r i := by
  obtain ⟨j, hj⟩ := i.eq_nat_or_neg
  rcases hj with rfl | rfl
  · simp only [zpow_coe_nat, r_one_pow, Int.cast_ofNat]
  · simp only [zpow_neg, zpow_coe_nat, r_one_pow, Int.cast_neg, Int.cast_ofNat, r_inv_eq_r_neg]

-- @[simp] -- Porting note: simp changes the goal to `r 0 = 1`. `r_one_pow_n` is no longer useful.
theorem r_one_pow_n : r (1 : ZMod n) ^ n = 1 := by
  rw [r_one_pow, one_def]
  congr 1
  exact ZMod.natCast_self _

@[simp]
theorem r_zpow_n {i : ZMod n} [NeZero n] : r i ^ n = 1 := by
  have h1 : r 1 ^ i.val = r i := by
    simp only [r_one_pow, r.injEq]
    exact ZMod.nat_cast_zmod_val i
  have h2 : (r 1 ^ i.val) ^ n = r 1 ^ (i.val * n) := by
    exact Eq.symm (pow_mul (r 1 : DihedralGroup n) i.val n)
  have h3 : (r 1) ^ (i.val * n) = (1 : DihedralGroup n) := by
    simp only [r_one_pow, Nat.cast_mul, ZMod.nat_cast_val, ZMod.cast_id',
      id_eq, CharP.cast_eq_zero, mul_zero, one_def]
  rw [← h1, h2, h3]

-- @[simp] -- Porting note: simp changes the goal to `r 0 = 1`. `sr_mul_self` is no longer useful.
theorem sr_mul_self (i : ZMod n) : sr i * sr i = 1 := by rw [sr_mul_sr, sub_self, one_def]

/-- If `0 < n`, then `sr i` has order 2.
-/
@[simp]
theorem orderOf_sr (i : ZMod n) : orderOf (sr i) = 2 := by
  apply orderOf_eq_prime
  · rw [sq, sr_mul_self]
  · -- Porting note: Previous proof was `decide`
    revert n
    simp_rw [one_def, ne_eq, forall_const, not_false_eq_true]

-- @[simp]
-- theorem sr_one_pow (k : ℕ) : (sr 1 : DihedralGroup n) ^ k = sr k := by
--   induction' k with k IH
--   · rw [Nat.cast_zero]
--     simp only [Nat.zero_eq, pow_zero]


--   · rw [pow_succ, IH, r_mul_r]
--     congr 1
--     norm_cast
--     rw [Nat.one_add]


-- @[simp]
-- theorem sr_one_zpow (n : ℕ) (i : ℤ) :
--     (sr (1 : ZMod n)) ^ i = sr i := by

--   obtain ⟨j, hj⟩ := i.eq_nat_or_neg
--   rcases hj with rfl | rfl
--   · simp only [zpow_coe_nat, Int.cast_ofNat]

--   · simp only [zpow_neg, zpow_coe_nat, sr_one_pow, Int.cast_neg, Int.cast_ofNat]

/-- If `0 < n`, then `r 1` has order `n`.
-/
@[simp]
theorem orderOf_r_one : orderOf (r 1 : DihedralGroup n) = n := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · rw [orderOf_eq_zero_iff']
    intro n hn
    rw [r_one_pow, one_def]
    apply mt r.inj
    simpa using hn.ne'
  · apply (Nat.le_of_dvd (NeZero.pos n) <|
      orderOf_dvd_of_pow_eq_one <| @r_one_pow_n n).lt_or_eq.resolve_left
    intro h
    have h1 : (r 1 : DihedralGroup n) ^ orderOf (r 1) = 1 := pow_orderOf_eq_one _
    rw [r_one_pow] at h1
    injection h1 with h2
    rw [← ZMod.val_eq_zero, ZMod.val_natCast, Nat.mod_eq_of_lt h] at h2
    exact absurd h2.symm (orderOf_pos _).ne

/-- If `0 < n`, then `i : ZMod n` has order `n / gcd n i`.
-/
theorem orderOf_r [NeZero n] (i : ZMod n) : orderOf (r i) = n / Nat.gcd n i.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i]
  rw [← r_one_pow, orderOf_pow, orderOf_r_one]

theorem exponent : Monoid.exponent (DihedralGroup n) = lcm n 2 := by
  rcases eq_zero_or_neZero n with (rfl | hn)
  · exact Monoid.exponent_eq_zero_of_order_zero orderOf_r_one
  apply Nat.dvd_antisymm
  · apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro (m | m)
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_r]
      refine Nat.dvd_trans ⟨gcd n m.val, ?_⟩ (dvd_lcm_left n 2)
      exact (Nat.div_mul_cancel (Nat.gcd_dvd_left n m.val)).symm
    · rw [← orderOf_dvd_iff_pow_eq_one, orderOf_sr]
      exact dvd_lcm_right n 2
  · apply lcm_dvd
    · convert Monoid.order_dvd_exponent (r (1 : ZMod n))
      exact orderOf_r_one.symm
    · convert Monoid.order_dvd_exponent (sr (0 : ZMod n))
      exact (orderOf_sr 0).symm

/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs (represented as
$n + n + n + n*n$) of commuting elements. -/
@[simps]
def OddCommuteEquiv (hn : Odd n) : { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } ≃
    ZMod n ⊕ ZMod n ⊕ ZMod n ⊕ ZMod n × ZMod n :=
  let u := ZMod.unitOfCoprime 2 (Nat.prime_two.coprime_iff_not_dvd.mpr hn.not_two_dvd_nat)
  have hu : ∀ a : ZMod n, a + a = 0 ↔ a = 0 := fun a => ZMod.add_self_eq_zero_iff_eq_zero hn
  { toFun := fun
      | ⟨⟨sr i, r _⟩, _⟩ => Sum.inl i
      | ⟨⟨r _, sr j⟩, _⟩ => Sum.inr (Sum.inl j)
      | ⟨⟨sr i, sr j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inl (i + j)))
      | ⟨⟨r i, r j⟩, _⟩ => Sum.inr (Sum.inr (Sum.inr ⟨i, j⟩))
    invFun := fun
      | .inl i => ⟨⟨sr i, r 0⟩, congrArg sr ((add_zero i).trans (sub_zero i).symm)⟩
      | .inr (.inl j) => ⟨⟨r 0, sr j⟩, congrArg sr ((sub_zero j).trans (add_zero j).symm)⟩
      | .inr (.inr (.inl k)) => ⟨⟨sr (u⁻¹ * k), sr (u⁻¹ * k)⟩, rfl⟩
      | .inr (.inr (.inr ⟨i, j⟩)) => ⟨⟨r i, r j⟩, congrArg r (add_comm i j)⟩
    left_inv := fun
      | ⟨⟨r i, r j⟩, h⟩ => rfl
      | ⟨⟨r i, sr j⟩, h⟩ => by
        simpa [sub_eq_add_neg, neg_eq_iff_add_eq_zero, hu, eq_comm (a := i) (b := 0)] using h.eq
      | ⟨⟨sr i, r j⟩, h⟩ => by
        simpa [sub_eq_add_neg, eq_neg_iff_add_eq_zero, hu, eq_comm (a := j) (b := 0)] using h.eq
      | ⟨⟨sr i, sr j⟩, h⟩ => by
        replace h := r.inj h
        rw [← neg_sub, neg_eq_iff_add_eq_zero, hu, sub_eq_zero] at h
        rw [Subtype.ext_iff, Prod.ext_iff, sr.injEq, sr.injEq, h, and_self, ← two_mul]
        exact u.inv_mul_cancel_left j
    right_inv := fun
      | .inl i => rfl
      | .inr (.inl j) => rfl
      | .inr (.inr (.inl k)) =>
        congrArg (Sum.inr ∘ Sum.inr ∘ Sum.inl) <| two_mul (u⁻¹ * k) ▸ u.mul_inv_cancel_left k
      | .inr (.inr (.inr ⟨i, j⟩)) => rfl }

/-- If n is odd, then the Dihedral group of order $2n$ has $n(n+3)$ pairs of commuting elements. -/
lemma card_commute_odd (hn : Odd n) :
    Nat.card { p : DihedralGroup n × DihedralGroup n // Commute p.1 p.2 } = n * (n + 3) := by
  have hn' : NeZero n := ⟨hn.pos.ne'⟩
  simp_rw [Nat.card_congr (OddCommuteEquiv hn), Nat.card_sum, Nat.card_prod, Nat.card_zmod]
  ring

lemma card_conjClasses_odd (hn : Odd n) :
    Nat.card (ConjClasses (DihedralGroup n)) = (n + 3) / 2 := by
  rw [← Nat.mul_div_mul_left _ 2 hn.pos, ← card_commute_odd hn, mul_comm,
    card_comm_eq_card_conjClasses_mul_card, nat_card, Nat.mul_div_left _ (mul_pos two_pos hn.pos)]

end DihedralGroup

namespace PresentedDihedralGroup

variable {n : ℕ}

inductive Generators (n : ℕ)
  | a : Generators n
  | b : Generators n
  deriving DecidableEq

open DihedralGroup Generators

/-- a² = sr² = 1, bⁿ = rⁿ = 1 -/
def GenMap : Generators n → DihedralGroup n
  | a => sr 1
  | b => r 1

/-- Presentation ⟨a, b | a² = 1, bⁿ = 1, (a * b)² = 1⟩  -/
def Rels (n : ℕ) : Set (FreeGroup (Generators n)) :=
  {FreeGroup.of b ^ n} ∪ {FreeGroup.of a * FreeGroup.of a} ∪
  {(FreeGroup.of a * FreeGroup.of b) * (FreeGroup.of a * FreeGroup.of b)}

abbrev PresentedDihedralGroup (n : ℕ) := PresentedGroup <| Rels n

def GenMapInv : DihedralGroup n → PresentedDihedralGroup n
  | sr i => QuotientGroup.mk (FreeGroup.of a ^ (i : ℤ))
  | r i => QuotientGroup.mk (FreeGroup.of b ^ (i : ℤ))

theorem one_of_Rels : ∀ r ∈ Rels n, FreeGroup.lift GenMap r = 1 := by
  intro r hr
  simp only [Rels] at hr
  simp only [Set.union_singleton, Set.mem_singleton_iff, Set.mem_insert_iff] at hr
  rcases hr with hr₁ | hr₂ | hr₃
  · rw [hr₁]
    simp only [map_pow, map_mul, FreeGroup.lift.of]
    simp [GenMap]
  · rw [hr₂]
    simp only [map_mul, FreeGroup.lift.of]
    simp [GenMap]
  · rw [hr₃]
    simp only [map_pow, FreeGroup.lift.of, one_def]
    simp [GenMap]

/-- Group presentation induced morphism to the DihedarlGroup n. -/
@[simp] theorem presentedGroupHom : PresentedDihedralGroup n →* DihedralGroup n :=
    PresentedGroup.toGroup (f := GenMap) one_of_Rels

lemma powLaw1 {i k : ZMod n} :
    QuotientGroup.mk (FreeGroup.of b) ^ ((i + k : ZMod n) : ℤ) =
    QuotientGroup.mk (s := Subgroup.normalClosure (Rels n)) (FreeGroup.of b) ^ (i : ℤ) *
    QuotientGroup.mk (FreeGroup.of b) ^ (k : ℤ) := by
  have h1 := ZMod.coe_add_eq_ite i k
  symm at h1
  obtain ⟨h2, h3⟩ := ite_eq_iff'.mp h1
  push_neg at h3
  by_cases H : (i : ℤ) + (k : ℤ) < n
  · rw [← h3 H]
    exact zpow_add (QuotientGroup.mk (FreeGroup.of b)) (i : ℤ) (k : ℤ)
  · push_neg at H
    rw [← h2 H]
    have h5 : (i : ℤ) + (k : ℤ) = (i : ℤ) + (k : ℤ) - (n : ℤ) + (n : ℤ) := by linarith
    have h6 := zpow_add ((QuotientGroup.mk (s := Subgroup.normalClosure (Rels n))
      (FreeGroup.of (@b n))) * (QuotientGroup.mk (FreeGroup.of b)))
      (i : ℤ) (k : ℤ)
    sorry
    -- have h7 := @a_b_zpow_mem_normalClosure_eq_identity n
    -- rw [h5] at h6
    -- rw [← h6]
    -- have h8 := zpow_add ((QuotientGroup.mk (s := Subgroup.normalClosure (Rels n))
    --   (FreeGroup.of (@a n))) * (QuotientGroup.mk (FreeGroup.of b)))
    --   (i + k - n : ℤ) (n : ℤ)
    -- simp only [QuotientGroup.mk_mul] at h7
    -- rw [h8, h7, mul_one]

lemma map_mul' : ∀ a b : DihedralGroup n, GenMapInv (a * b) = GenMapInv a * GenMapInv b := by
  intro d₁ d₂
  simp only [GenMapInv]
  rcases d₁ with i | j
  · rcases d₂ with k | l
    · simp only [r_mul_r, QuotientGroup.mk_zpow]
      exact powLaw1
    · simp only [r_mul_sr, QuotientGroup.mk_zpow]
      sorry
  · rcases d₂ with k | l
    · simp only [sr_mul_r, QuotientGroup.mk_zpow]
      sorry
    · simp only [sr_mul_sr, QuotientGroup.mk_zpow]
      sorry

/-- Homorphism from DihedralGroup n to group presentation of DihedralGroup n. -/
def dihedralGroupHom : DihedralGroup n →* PresentedDihedralGroup n where
  toFun := GenMapInv
  map_one' := by
    simp only [GenMapInv, one_def, QuotientGroup.mk_zpow, QuotientGroup.mk_mul,
      ZMod.cast_zero, zpow_zero]
  map_mul' := map_mul'

lemma dihedralGroupHom1 {i : ZMod n} : dihedralGroupHom (r i : DihedralGroup n) =
    (PresentedGroup.of b) ^ (i : ℤ) := by
  unfold dihedralGroupHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, GenMapInv, PresentedGroup.of,
    QuotientGroup.mk_zpow, QuotientGroup.mk_mul]

lemma dihedralGroupHom2 {i : ZMod n} : dihedralGroupHom (sr i : DihedralGroup n) =
    (PresentedGroup.of a) ^ (i : ℤ) := by
  unfold dihedralGroupHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, GenMapInv, PresentedGroup.of,
    QuotientGroup.mk_zpow, QuotientGroup.mk_mul]

theorem rightInverseHoms : Function.RightInverse (@dihedralGroupHom n) (@presentedGroupHom n) := by
  intro dn
  rcases dn with i | i
  · rw [dihedralGroupHom1]
    unfold presentedGroupHom
    simp only [map_mul, PresentedGroup.toGroup.of]
    simp_rw [GenMap]
    simp only [map_zpow, PresentedGroup.toGroup.of, r_one_zpow,
      ZMod.int_cast_cast, ZMod.cast_id', id_eq]
  · rw [dihedralGroupHom2]
    unfold presentedGroupHom
    simp only [map_mul, PresentedGroup.toGroup.of, map_zpow]
    simp [GenMap]
    sorry

theorem tryingToFigureOut : (@dihedralGroupHom n).comp (@presentedGroupHom n) =
    MonoidHom.id (PresentedDihedralGroup n) := by
  refine PresentedGroup.ext ?_

theorem leftInverseHoms : Function.LeftInverse (@dihedralGroupHom n) (@presentedGroupHom n) := by
  intro pd
  unfold dihedralGroupHom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  simp [GenMapInv]
  match presentedGroupHom pd with
  | r i => sorry
  | sr i => sorry

noncomputable
def DihedralGroupIsoPresentedDihedralGroup : PresentedDihedralGroup n ≃* DihedralGroup n where
  toFun := sorry
  invFun := dihedralGroupHom
  left_inv := sorry
  right_inv := sorry
  map_mul' x y := sorry -- by simp only [map_mul]

end PresentedDihedralGroup
