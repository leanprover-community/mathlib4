import Mathlib.NumberTheory.KroneckerWeber.Cyclotomic.UnitLemmas
import Mathlib.NumberTheory.KroneckerWeber.Cyclotomic.CyclRat

open scoped NumberField nonZeroDivisors

variable {p : ℕ+} {K : Type _} [Field K] [CharZero K] [IsCyclotomicExtension {p} ℚ K]

variable {ζ : K} (hζ : IsPrimitiveRoot ζ p)

open FractionalIdeal

variable (i : ℤ)

namespace FltRegular.CaseI

lemma coe_unitGalConj (x : (𝓞 K)ˣ) : ↑(unitGalConj K p x) = intGal (galConj K p) (x : 𝓞 K) :=
rfl

theorem pow_sub_intGalConj_mem (hp : (p : ℕ).Prime) (α : 𝓞 K) :
    (α ^ (p : ℕ) - intGal (galConj K p) (α ^ (p : ℕ))) ∈ Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  have : Fact (p : ℕ).Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := exists_int_sub_pow_prime_dvd p α
  rw [Ideal.mem_span_singleton] at ha ⊢
  obtain ⟨γ, hγ⟩ := ha
  rw [sub_eq_iff_eq_add] at hγ
  rw [hγ, _root_.map_add, _root_.map_mul, map_natCast, map_intCast, add_sub_add_right_eq_sub,
    ← mul_sub]
  exact dvd_mul_right _ _

theorem exists_int_sum_eq_zero'_aux (x y i : ℤ) :
  intGal (galConj K p) (x + y * ↑(hζ.unit' ^ i) : 𝓞 K) = x + y * (hζ.unit' ^ (-i) : (𝓞 K)ˣ) := by
  ext1
  rw [intGal_apply_coe]
  simp only [_root_.map_add, map_intCast, _root_.map_mul, AlgHom.coe_coe, zpow_neg, map_units_inv,
    add_right_inj, mul_eq_mul_left_iff, Int.cast_eq_zero]
  simp_rw [NumberField.Units.coe_zpow]
  left
  simp only [map_zpow₀]
  rw [← inv_zpow]
  congr
  exact galConj_zeta_runity hζ

theorem exists_int_sum_eq_zero' (hpodd : p ≠ 2) (hp : (p : ℕ).Prime) (x y i : ℤ) {u : (𝓞 K)ˣ}
    {α : 𝓞 K} (h : (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) = u * α ^ (p : ℕ)) :
    ∃ k : ℕ, (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) - ((hζ.unit' ^ k) ^ 2 : (𝓞 K)ˣ) *
    (x + y * (hζ.unit' ^ (-i) : (𝓞 K)ˣ)) ∈
    Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  letI : NumberField K := IsCyclotomicExtension.numberField { p } ℚ _
  have : Fact (p : ℕ).Prime := ⟨hp⟩
  obtain ⟨k, H⟩ := unit_inv_conj_is_root_of_unity hζ hpodd hp u
  refine ⟨k, ?_⟩
  rw [← exists_int_sum_eq_zero'_aux, h, ← H, Units.val_mul, mul_assoc, ← mul_sub, _root_.map_mul,
    ← coe_unitGalConj, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  exact Ideal.mul_mem_left _ _ (pow_sub_intGalConj_mem hp α)

theorem exists_int_sum_eq_zero (hpodd : p ≠ 2) (hp : (p : ℕ).Prime) (x y i : ℤ) {u : (𝓞 K)ˣ}
    {α : 𝓞 K} (h : (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) = u * α ^ (p : ℕ)) :
    ∃ k : ℤ, (x : 𝓞 K) + y * (hζ.unit' ^ i : (𝓞 K)ˣ) - (hζ.unit' ^ (2 * k) : (𝓞 K)ˣ) *
    (x + y * (hζ.unit' ^ (-i) : (𝓞 K)ˣ)) ∈
    Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  obtain ⟨k, hk⟩ := exists_int_sum_eq_zero' hζ hpodd hp x y i h
  use k
  convert hk
  rw [mul_comm, zpow_mul, zpow_ofNat]
  rfl

end FltRegular.CaseI
