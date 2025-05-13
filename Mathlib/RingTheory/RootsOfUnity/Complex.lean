/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Complex roots of unity

In this file we show that the `n`-th complex roots of unity
are exactly the complex numbers `exp (2 * π * I * (i / n))` for `i ∈ Finset.range n`.

## Main declarations

* `Complex.mem_rootsOfUnity`: the complex `n`-th roots of unity are exactly the
  complex numbers of the form `exp (2 * π * I * (i / n))` for some `i < n`.
* `Complex.card_rootsOfUnity`: the number of `n`-th roots of unity is exactly `n`.
* `Complex.norm_rootOfUnity_eq_one`: A complex root of unity has norm `1`.
* `Units.expHom`: The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂˣ`,
  considered as a homomorphism of groups.
* `rootsOfUnity.expHom`: The map `fun k => exp ((2 * π * (k.val / n)) * I)` from `ZMod n` to the
  `n`th roots of unity in `ℂ`, considered as a homomorphism of groups.
-/


section Units.exp

namespace Units

open Complex in
/-- The map `fun t => exp (t * I)` from `ℝ` to `ℂˣ`. -/
noncomputable def exp : ℝ → ℂˣ := fun t =>
  ⟨(t * I).exp, (-t * I).exp, by rw [← exp_add, neg_mul, add_neg_cancel, exp_zero],
    by rw [← exp_add, neg_mul, neg_add_cancel, exp_zero]⟩

@[simp, norm_cast]
theorem coe_exp (t : ℝ) : exp t = Complex.exp (t * Complex.I) := rfl

@[simp]
theorem exp_zero : exp 0 = 1 := by
  ext : 1
  rw [coe_exp, Complex.ofReal_zero, zero_mul, Complex.exp_zero, val_one]

@[simp]
theorem exp_add (x y : ℝ) : exp (x + y) = exp x * exp y := by
  ext
  simp only [coe_exp, Submonoid.coe_mul, Complex.ofReal_add, add_mul, Complex.exp_add, val_mul,
    coe_exp]

lemma exp_iff (t s : ℝ) :
    exp s = exp t ↔ Complex.exp (t * Complex.I) = Complex.exp (s * Complex.I) := by
  constructor <;> intro h
  · simp [exp, exp] at h
    simp_all only
  · ext : 1
    simp_all only [coe_exp]

open scoped Interval in
open Real in
/-- `exp` is injective on `Ι a b` if the distance between `a` and `b` is at most `2π`. -/
lemma injOn_exp_of_abs_sub_le {x y : ℝ} (hxy : |x - y| ≤ 2 * π) : (Ι x y).InjOn exp :=
    fun t₁ ht₁ t₂ ht₂ h => injOn_circleMap_of_abs_sub_le (c := 0) (zero_ne_one' ℝ).symm hxy ht₁ ht₂
    (by rw [circleMap_origin_unit, circleMap_origin_unit]; exact (exp_iff t₁ t₂).mp h.symm)

open Real in
/-- `exp` is injective on `Ico a b` if the distance between `a` and `b` is at most `2π`. -/
theorem injOn_exp_of_abs_sub_le' {x y : ℝ} (hxy : y - x ≤ 2 * π) : (Set.Ico x y).InjOn exp :=
  fun t₁ ht₁ t₂ ht₂ h => injOn_circleMap_of_abs_sub_le' (c := 0) (zero_ne_one' ℝ).symm hxy ht₁ ht₂
     (by rw [circleMap_origin_unit, circleMap_origin_unit]; exact (exp_iff t₁ t₂).mp h.symm)

open Real in
/-- `exp` is `2π`-periodic. -/
theorem periodic_exp : Function.Periodic (exp) (2 * π) := fun θ => by
  simp only [exp_iff, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat, add_mul,
    Complex.exp_periodic _]

open Real in
lemma exp_2pi_mul_add_ZMod (n : ℕ) [NeZero n] (j k : ZMod n) :
  Units.exp (2 * π * ((j + k).val / n)) = Units.exp (2 * π * (j.val/n) + 2 * π * (k.val/n)) := by
  rcases (Nat.lt_or_ge _ _) with h1 | h2
  · rw [ZMod.val_add_of_lt h1, Nat.cast_add, add_div, mul_add]
  · rw [ZMod.val_add_of_le h2, Nat.cast_sub h2, sub_div, div_self ((NeZero.ne' _).symm), mul_sub,
      mul_one, Units.periodic_exp.sub_eq, Nat.cast_add, add_div, mul_add]

open Real in
lemma exp_two_pi_mul_div_inj_ZMod (n : ℕ) [NeZero n] (j k : ZMod n)
    (h : Units.exp (2 * π * (↑j.val / ↑n)) = Units.exp (2 * π * (↑k.val / ↑n))) : j = k :=
  ZMod.val_injective _
    ((Nat.cast_inj.mp ((div_left_inj' (Nat.cast_ne_zero.mpr (NeZero.ne' n).symm)).mp
      ((mul_right_inj' two_pi_ne_zero).mp (Units.injOn_exp_of_abs_sub_le'
        (by rw [sub_zero])
        ⟨(mul_nonneg_iff_of_pos_left two_pi_pos).mpr
          (div_nonneg (Nat.cast_nonneg' _) n.cast_nonneg'),
          (mul_lt_iff_lt_one_right two_pi_pos).mpr ((div_lt_one (Nat.cast_pos.mpr
              (Nat.pos_of_ne_zero (NeZero.ne' n).symm))).mpr (Nat.strictMono_cast (ZMod.val_lt _)))⟩
        ⟨(mul_nonneg_iff_of_pos_left two_pi_pos).mpr
          (div_nonneg (Nat.cast_nonneg' _) n.cast_nonneg'),
          (mul_lt_iff_lt_one_right two_pi_pos).mpr ((div_lt_one (Nat.cast_pos.mpr
              (Nat.pos_of_ne_zero (NeZero.ne' n).symm))).mpr (Nat.strictMono_cast (ZMod.val_lt _)))⟩
        h)))))

/-- The map `fun t => exp (t * I)` from `ℝ` to the unit circle in `ℂˣ`,
considered as a homomorphism of groups. -/
@[simps]
noncomputable def expHom : ℝ →+ Additive ℂˣ where
  toFun := Additive.ofMul ∘ _root_.Units.exp
  map_zero' := exp_zero
  map_add' := exp_add

end Units

end Units.exp

namespace Complex

open Polynomial Real

open scoped Nat Real

theorem isPrimitiveRoot_exp_of_coprime (i n : ℕ) (h0 : n ≠ 0) (hi : i.Coprime n) :
    IsPrimitiveRoot (exp (2 * π * I * (i / n))) n := by
  rw [IsPrimitiveRoot.iff_def]
  simp only [← exp_nat_mul, exp_eq_one_iff]
  have hn0 : (n : ℂ) ≠ 0 := mod_cast h0
  constructor
  · use i
    field_simp [hn0, mul_comm (i : ℂ), mul_comm (n : ℂ)]
  · simp only [hn0, mul_right_comm _ _ ↑n, mul_left_inj' two_pi_I_ne_zero, Ne, not_false_iff,
      mul_comm _ (i : ℂ), ← mul_assoc _ (i : ℂ), exists_imp, field_simps]
    norm_cast
    rintro l k hk
    conv_rhs at hk => rw [mul_comm, ← mul_assoc]
    have hz : 2 * ↑π * I ≠ 0 := by simp [pi_pos.ne.symm, I_ne_zero]
    field_simp [hz] at hk
    norm_cast at hk
    have : n ∣ i * l := by rw [← Int.natCast_dvd_natCast, hk, mul_comm]; apply dvd_mul_left
    exact hi.symm.dvd_of_dvd_mul_left this

theorem isPrimitiveRoot_exp (n : ℕ) (h0 : n ≠ 0) : IsPrimitiveRoot (exp (2 * π * I / n)) n := by
  simpa only [Nat.cast_one, one_div] using
    isPrimitiveRoot_exp_of_coprime 1 n h0 n.coprime_one_left

theorem isPrimitiveRoot_iff (ζ : ℂ) (n : ℕ) (hn : n ≠ 0) :
    IsPrimitiveRoot ζ n ↔ ∃ i < n, ∃ _ : i.Coprime n, exp (2 * π * I * (i / n)) = ζ := by
  have hn0 : (n : ℂ) ≠ 0 := mod_cast hn
  constructor; swap
  · rintro ⟨i, -, hi, rfl⟩; exact isPrimitiveRoot_exp_of_coprime i n hn hi
  intro h
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, hi, rfl⟩ :=
    (isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one h.pow_eq_one
  refine ⟨i, hi, ((isPrimitiveRoot_exp n hn).pow_iff_coprime (Nat.pos_of_ne_zero hn) i).mp h, ?_⟩
  rw [← exp_nat_mul]
  congr 1
  field_simp [hn0, mul_comm (i : ℂ)]

/-- The complex `n`-th roots of unity are exactly the
complex numbers of the form `exp (2 * Real.pi * Complex.I * (i / n))` for some `i < n`. -/
nonrec theorem mem_rootsOfUnity (n : ℕ) [NeZero n] (x : Units ℂ) :
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < n, exp (2 * π * I * (i / n)) = x := by
  rw [mem_rootsOfUnity, Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one]
  have hn0 : (n : ℂ) ≠ 0 := mod_cast NeZero.out
  constructor
  · intro h
    obtain ⟨i, hi, H⟩ : ∃ i < (n : ℕ), exp (2 * π * I / n) ^ i = x := by
      simpa only using (isPrimitiveRoot_exp n NeZero.out).eq_pow_of_pow_eq_one h
    refine ⟨i, hi, ?_⟩
    rw [← H, ← exp_nat_mul]
    congr 1
    field_simp [hn0, mul_comm (i : ℂ)]
  · rintro ⟨i, _, H⟩
    rw [← H, ← exp_nat_mul, exp_eq_one_iff]
    use i
    field_simp [hn0, mul_comm ((n : ℕ) : ℂ), mul_comm (i : ℂ)]

-- Rework `mem_rootsOfUnity` into a more usable form
nonrec theorem mem_rootsOfUnity' (n : ℕ) [NeZero n] (x : Units ℂ) :
    x ∈ rootsOfUnity n ℂ ↔ ∃ i < n, Units.exp (2 * π * (i / n)) = x := by
  simp_rw [mem_rootsOfUnity, Units.exp, ofReal_mul, ofReal_ofNat, ofReal_div, ofReal_natCast,
    ← Units.eq_iff]
  constructor <;> ({ intro ⟨i, hi1, hi2⟩; exact ⟨i, ⟨hi1, by rw [← hi2]; ring_nf⟩ ⟩})

theorem card_rootsOfUnity (n : ℕ) [NeZero n] : Fintype.card (rootsOfUnity n ℂ) = n :=
  (isPrimitiveRoot_exp n NeZero.out).card_rootsOfUnity

theorem card_primitiveRoots (k : ℕ) : (primitiveRoots k ℂ).card = φ k := by
  by_cases h : k = 0
  · simp [h]
  exact (isPrimitiveRoot_exp k h).card_primitiveRoots

end Complex

theorem IsPrimitiveRoot.norm'_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖ = 1 :=
  Complex.norm_eq_one_of_pow_eq_one h.pow_eq_one hn

theorem IsPrimitiveRoot.nnnorm_eq_one {ζ : ℂ} {n : ℕ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ‖ζ‖₊ = 1 :=
  Subtype.ext <| h.norm'_eq_one hn

theorem IsPrimitiveRoot.arg_ext {n m : ℕ} {ζ μ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    (hμ : IsPrimitiveRoot μ m) (hn : n ≠ 0) (hm : m ≠ 0) (h : ζ.arg = μ.arg) : ζ = μ :=
  Complex.ext_norm_arg ((hζ.norm'_eq_one hn).trans (hμ.norm'_eq_one hm).symm) h

theorem IsPrimitiveRoot.arg_eq_zero_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = 0 ↔ ζ = 1 :=
  ⟨fun h => hζ.arg_ext IsPrimitiveRoot.one hn one_ne_zero (h.trans Complex.arg_one.symm), fun h =>
    h.symm ▸ Complex.arg_one⟩

theorem IsPrimitiveRoot.arg_eq_pi_iff {n : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ζ.arg = Real.pi ↔ ζ = -1 :=
  ⟨fun h =>
    hζ.arg_ext (IsPrimitiveRoot.neg_one 0 two_ne_zero.symm) hn two_ne_zero
      (h.trans Complex.arg_neg_one.symm),
    fun h => h.symm ▸ Complex.arg_neg_one⟩

theorem IsPrimitiveRoot.arg {n : ℕ} {ζ : ℂ} (h : IsPrimitiveRoot ζ n) (hn : n ≠ 0) :
    ∃ i : ℤ, ζ.arg = i / n * (2 * Real.pi) ∧ IsCoprime i n ∧ i.natAbs < n := by
  rw [Complex.isPrimitiveRoot_iff _ _ hn] at h
  obtain ⟨i, h, hin, rfl⟩ := h
  rw [mul_comm, ← mul_assoc, Complex.exp_mul_I]
  refine ⟨if i * 2 ≤ n then i else i - n, ?_, ?isCoprime, by omega⟩
  case isCoprime =>
    replace hin := Nat.isCoprime_iff_coprime.mpr hin
    split_ifs
    · exact hin
    · convert hin.add_mul_left_left (-1) using 1
      rw [mul_neg_one, sub_eq_add_neg]
  split_ifs with h₂
  · convert Complex.arg_cos_add_sin_mul_I _
    · push_cast; rfl
    · push_cast; rfl
    field_simp [hn]
    refine ⟨(neg_lt_neg Real.pi_pos).trans_le ?_, ?_⟩
    · rw [neg_zero]
      exact mul_nonneg (mul_nonneg i.cast_nonneg <| by simp [Real.pi_pos.le])
        (by rw [inv_nonneg]; simp only [Nat.cast_nonneg])
    rw [← mul_rotate', mul_div_assoc]
    rw [← mul_one n] at h₂
    exact mul_le_of_le_one_right Real.pi_pos.le
      ((div_le_iff₀' <| mod_cast pos_of_gt h).mpr <| mod_cast h₂)
  rw [← Complex.cos_sub_two_pi, ← Complex.sin_sub_two_pi]
  convert Complex.arg_cos_add_sin_mul_I _
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
    exact mod_cast hn
  · push_cast
    rw [← sub_one_mul, sub_div, div_self]
    exact mod_cast hn
  field_simp [hn]
  refine ⟨?_, le_trans ?_ Real.pi_pos.le⟩
  on_goal 2 =>
    rw [mul_div_assoc]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr <| mod_cast h.le)
      (div_nonneg (by simp [Real.pi_pos.le]) <| by simp)
  rw [← mul_rotate', mul_div_assoc, neg_lt, ← mul_neg, mul_lt_iff_lt_one_right Real.pi_pos, ←
    neg_div, ← neg_mul, neg_sub, div_lt_iff₀, one_mul, sub_mul, sub_lt_comm, ← mul_sub_one]
  · norm_num
    exact mod_cast not_le.mp h₂
  · exact Nat.cast_pos.mpr hn.bot_lt

lemma Complex.norm_eq_one_of_mem_rootsOfUnity {ζ : ℂˣ} {n : ℕ} [NeZero n]
    (hζ : ζ ∈ rootsOfUnity n ℂ) :
    ‖(ζ : ℂ)‖ = 1 := by
  refine norm_eq_one_of_pow_eq_one ?_ <| NeZero.ne n
  norm_cast
  rw [_root_.mem_rootsOfUnity] at hζ
  rw [hζ, Units.val_one]

theorem Complex.conj_rootsOfUnity {ζ : ℂˣ} {n : ℕ} [NeZero n] (hζ : ζ ∈ rootsOfUnity n ℂ) :
    (starRingEnd ℂ) ζ = ζ⁻¹ := by
  rw [← Units.mul_eq_one_iff_eq_inv, conj_mul', norm_eq_one_of_mem_rootsOfUnity hζ, ofReal_one,
    one_pow]

namespace rootsOfUnity

open Real in
/-- The map `fun k => exp ((2 * π * (k.val / n)) * I)` from `ZMod n` to the `n`th roots of unity in
`ℂ`. -/
noncomputable def exp (n : ℕ) [NeZero n] : ZMod n → rootsOfUnity n ℂ :=
  fun k => ⟨Units.exp (2 * π * (k.val / n)),by
    rw [Complex.mem_rootsOfUnity']
    exact ⟨k.val, ⟨k.val_lt, by congr⟩⟩⟩

variable (n : ℕ) [NeZero n]

@[simp]
theorem exp_zero : exp n 0 = 1 := by
  ext : 1
  simp only [exp, ZMod.val_zero, CharP.cast_eq_zero, zero_div, mul_zero, Units.exp_zero,
    OneMemClass.coe_one]

@[simp]
theorem exp_add (x y : ZMod n) : exp n (x + y) = exp n x * exp n y := by
  simp_rw [exp,Units.exp_2pi_mul_add_ZMod]
  simp_all only [Units.exp_add, ZMod.natCast_val, Units.val_mul, Units.coe_exp, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_div, Complex.ofReal_natCast, MulMemClass.mk_mul_mk]

theorem exp_inj : Function.Injective (exp n) := fun i j hij => by
  simp only [exp, Subtype.mk.injEq] at hij
  exact Units.exp_two_pi_mul_div_inj_ZMod _ _ _ hij

theorem exp_sur : Function.Surjective (exp n) := fun ⟨w,hw⟩ =>  by
  obtain ⟨j, hj1, hj2⟩ := (Complex.mem_rootsOfUnity' n w).mp hw
  exact ⟨j, by simp_rw [exp, ZMod.val_natCast_of_lt hj1, ← hj2]⟩

/-- The map `fun k => exp ((2 * π * (k.val / n)) * I)` from `ZMod n` to the `n`th roots of unity in
`ℂ`, considered as a homomorphism of groups. -/
noncomputable def expHom (n : ℕ) [NeZero n] :
    ZMod n  ≃+ Additive (rootsOfUnity n ℂ) :=
      AddEquiv.mk' (Equiv.ofBijective (Additive.ofMul ∘ exp n)  ⟨exp_inj n, exp_sur n⟩ ) (exp_add n)

end rootsOfUnity
