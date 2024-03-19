/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
import Mathlib.NumberTheory.Cyclotomic.Three
import Mathlib.NumberTheory.Cyclotomic.PID
import Mathlib.NumberTheory.FLT.Basic

/-!
# Fermat Last Theorem in the case `n = 3`
The goal of this file is to prove Fermat Last theorem in the case `n = 3`.

## Main results
* `fermatLastTheoremThree_case_1`: the first case of Fermat Last Theorem when `n = 3`:
  if `a b c : ℕ` are such that `¬ 3 ∣ a * b * c`, then `a ^ 3 + b ^ 3 ≠ c ^ 3`.

## TODO
Prove case 2.
-/

open NumberField Units InfinitePlace nonZeroDivisors Polynomial IsCyclotomicExtension.Rat.Three

section case1

open ZMod

private lemma cube_of_castHom_ne_zero {n : ZMod 9} :
    castHom (show 3 ∣ 9 by norm_num) (ZMod 3) n ≠ 0 → n ^ 3 = 1 ∨ n ^ 3 = 8 := by
  fin_cases n <;> decide

private lemma cube_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  apply cube_of_castHom_ne_zero
  rwa [map_natCast, Ne, Fin.nat_cast_eq_zero]

/--If `a b c : ℕ` are such that `¬ 3 ∣ a * b * c`, then `a ^ 3 + b ^ 3 ≠ c ^ 3`. -/
theorem fermatLastTheoremThree_case_1 {a b c : ℕ} (hdvd : ¬ 3 ∣ a * b * c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  simp_rw [Nat.prime_three.dvd_mul, not_or] at hdvd
  apply mt (congrArg (Nat.cast : ℕ → ZMod 9))
  simp_rw [Nat.cast_add, Nat.cast_pow]
  rcases cube_of_not_dvd hdvd.1.1 with ha | ha <;>
  rcases cube_of_not_dvd hdvd.1.2 with hb | hb <;>
  rcases cube_of_not_dvd hdvd.2 with hc | hc <;>
  rw [ha, hb, hc] <;> decide

end case1

section case2

section misc

/-- To prove `FermatLastTheoremFor 3`, we may assume that `3 ∣ c`. -/
theorem fermatLastTheoremThree_of_three_dvd_c
    (H : ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → 3 ∣ c → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    FermatLastTheoremFor 3 := by
  intro a b c ha hb hc habc
  by_cases h1 : 3 ∣ a * b * c
  swap
  · exact fermatLastTheoremThree_case_1 h1 habc
  rw [Nat.Prime.dvd_mul (Nat.prime_three), Nat.Prime.dvd_mul (Nat.prime_three)] at h1
  rcases h1 with ((⟨k, hk⟩ | ⟨k, hk⟩) | ⟨k, hk⟩)
  · refine H (-(c : ℤ)) b (-(a : ℤ)) (by simp [hc]) (by simp [hb]) (by simp [ha]) ?_ ?_
    · exact ⟨-k, by simp [hk]⟩
    · rw [Odd.neg_pow (by decide), Odd.neg_pow (by decide), add_comm, ← sub_eq_add_neg,
        sub_eq_iff_eq_add, add_comm, ← sub_eq_add_neg, eq_sub_iff_add_eq, add_comm]
      exact_mod_cast habc
  · refine H a (-(c : ℤ)) ((-(b : ℤ))) (by simp [ha]) (by simp [hc]) (by simp [hb]) ?_ ?_
    · exact ⟨-k, by simp [hk]⟩
    · rw [Odd.neg_pow (by decide), Odd.neg_pow (by decide), ← sub_eq_add_neg, sub_eq_iff_eq_add,
        add_comm, ← sub_eq_add_neg, eq_sub_iff_add_eq]
      exact_mod_cast habc
  · refine H a b c (by simp [ha]) (by simp [hb]) (by simp [hc]) ?_ ?_
    · exact ⟨k, by simp [hk]⟩
    · exact_mod_cast habc

lemma three_dvd_gcd_of_dvd_a_of_dvd_c {a b c : ℕ} (ha : 3 ∣ a) (hc : 3 ∣ c)
    (hF : a ^ 3 + b ^ 3 = c ^ 3) : 3 ∣ ({a, b, c} : Finset ℕ).gcd id := by
  have hb : 3 ∣ b := by
    have : 3 ∣ (b : ℤ) ^ 3 := by
      replace hF : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 := by exact_mod_cast hF
      rw [add_comm, ← eq_sub_iff_add_eq] at hF
      rw [hF]
      exact dvd_sub (dvd_pow (by exact_mod_cast hc) (by decide))
        (dvd_pow (by exact_mod_cast ha) (by decide))
    exact Int.coe_nat_dvd.1 <| Int.prime_three.dvd_of_dvd_pow this
  refine Finset.dvd_gcd (fun x hx ↦ ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (hx | hx | hx)
  · exact hx ▸ ha
  · exact hx ▸ hb
  · exact hx ▸ hc

lemma three_dvd_gcd_of_dvd_a_of_dvd_b {a b c : ℕ} (ha : 3 ∣ a) (hb : 3 ∣ b)
    (hF : a ^ 3 + b ^ 3 = c ^ 3) : 3 ∣ ({a, b, c} : Finset ℕ).gcd id := by
  have hc : 3 ∣ c := by
    have : 3 ∣ (c : ℤ) ^ 3 := by
      replace hF : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 := by exact_mod_cast hF
      rw [← hF]
      exact dvd_add (dvd_pow (by exact_mod_cast ha) (by decide))
        (dvd_pow (by exact_mod_cast hb) (by decide))
    exact Int.coe_nat_dvd.1 <| Int.prime_three.dvd_of_dvd_pow this
  refine Finset.dvd_gcd (fun x hx ↦ ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (hx | hx | hx)
  · exact hx ▸ ha
  · exact hx ▸ hb
  · exact hx ▸ hc

lemma three_dvd_gcd_of_dvd_b_of_dvd_c {a b c : ℕ} (hb : 3 ∣ b) (hc : 3 ∣ c)
    (hF : a ^ 3 + b ^ 3 = c ^ 3) : 3 ∣ ({a, b, c} : Finset ℕ).gcd id := by
  have ha : 3 ∣ a := by
    have : 3 ∣ (a : ℤ) ^ 3 := by
      replace hF : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 := by exact_mod_cast hF
      rw [← eq_sub_iff_add_eq] at hF
      rw [hF]
      exact dvd_sub (dvd_pow (by exact_mod_cast hc) (by decide))
            (dvd_pow (by exact_mod_cast hb) (by decide))
    exact Int.coe_nat_dvd.1 <| Int.prime_three.dvd_of_dvd_pow this
  refine Finset.dvd_gcd (fun x hx ↦ ?_)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (hx | hx | hx)
  · exact hx ▸ ha
  · exact hx ▸ hb
  · exact hx ▸ hc

open Finset Int Nat in
/-- To prove `FermatLastTheoremFor 3`, we may assume that `¬ 3 ∣ a`, `¬ 3 ∣ b`, `a` and `b`
are coprime and `3 ∣ c`. -/
theorem fermatLastTheoremThree_of_three_dvd_only_c
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    FermatLastTheoremFor 3 := by
  refine FermatLastTheoremFor_of_FermatLastTheoremFor_coprime (fun a b c ha hb hc Hgcd hF ↦?_)
  by_cases h1 : 3 ∣ a * b * c
  swap; exact fermatLastTheoremThree_case_1 h1 hF
  rw [(Nat.prime_three).dvd_mul, (Nat.prime_three).dvd_mul] at h1
  have h3 : ¬(3 ∣ 1) := by decide
  rcases h1 with ((⟨k, hk⟩ | ⟨k, hk⟩) | ⟨k, hk⟩)
  · refine H (-(c : ℤ)) b (-(a : ℤ)) (by simp [ha]) (fun hdvd ↦ h3 ?_) (fun hdvd ↦ h3 ?_) ?_ ?_ ?_
    · exact Hgcd.symm ▸ three_dvd_gcd_of_dvd_a_of_dvd_c ⟨k, hk⟩ (coe_nat_dvd.1 (dvd_neg.1 hdvd)) hF
    · exact Hgcd.symm ▸ three_dvd_gcd_of_dvd_a_of_dvd_b ⟨k, hk⟩ (by exact_mod_cast hdvd) hF
    · exact ⟨-k, by simp [hk]⟩
    · refine (isCoprime_iff_coprime.2 (coprime_of_dvd' (fun p hp hpc hpb ↦ ?_))).neg_left
      rw [← Hgcd]; refine dvd_gcd (fun x hx ↦ ?_)
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with (hx | hx | hx)
      · refine hx ▸ (hp.dvd_of_dvd_pow <| (Nat.dvd_add_iff_right (m := b ^ 3) (n := a ^ 3)
          (dvd_pow hpb (by decide))).2 ?_)
        rw [add_comm, hF]
        exact dvd_pow hpc (by decide)
      · exact hx ▸ hpb
      · exact hx ▸ hpc
    · rw [Odd.neg_pow (by decide), Odd.neg_pow (by decide), add_comm, ← sub_eq_add_neg,
        sub_eq_iff_eq_add, add_comm, ← sub_eq_add_neg, eq_sub_iff_add_eq, add_comm]
      exact_mod_cast hF
  · refine H a (-(c : ℤ)) ((-(b : ℤ))) (by simp [hb]) (fun hdvd ↦ h3 ?_) (fun hdvd ↦ h3 ?_) ?_ ?_ ?_
    · exact Hgcd.symm ▸ three_dvd_gcd_of_dvd_a_of_dvd_b (by exact_mod_cast hdvd) ⟨k, hk⟩ hF
    · exact Hgcd.symm ▸ three_dvd_gcd_of_dvd_b_of_dvd_c ⟨k, hk⟩ (coe_nat_dvd.1 (dvd_neg.1 hdvd)) hF
    · exact ⟨-k, by simp [hk]⟩
    · refine (Nat.isCoprime_iff_coprime.2 (coprime_of_dvd' (fun p hp hpa hpc ↦ ?_))).neg_right
      rw [← Hgcd]; refine dvd_gcd (fun x hx ↦ ?_)
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with (hx | hx | hx)
      · exact hx ▸ hpa
      · exact hx ▸ (hp.dvd_of_dvd_pow <| (Nat.dvd_add_iff_right (m := a ^ 3) (n := b ^ 3)
          (dvd_pow hpa (by decide))).2 (hF ▸ dvd_pow hpc (by decide)))
      · exact hx ▸ hpc
    · rw [Odd.neg_pow (by decide), Odd.neg_pow (by decide), ← sub_eq_add_neg, sub_eq_iff_eq_add,
        add_comm, ← sub_eq_add_neg, eq_sub_iff_add_eq]
      exact_mod_cast hF
  · refine H a b c (by simp [hc]) (fun hdvd ↦ h3 ?_) (fun hdvd ↦ h3 ?_) ?_ ?_ ?_
    · exact Hgcd.symm ▸ three_dvd_gcd_of_dvd_a_of_dvd_c (by exact_mod_cast hdvd) ⟨k, hk⟩ hF
    · exact Hgcd.symm ▸ three_dvd_gcd_of_dvd_b_of_dvd_c (by exact_mod_cast hdvd) ⟨k, hk⟩ hF
    · exact ⟨k, by simp [hk]⟩
    · refine isCoprime_iff_coprime.2 (coprime_of_dvd' (fun p hp hpa hpb ↦ ?_))
      rw [← Hgcd]; refine dvd_gcd (fun x hx ↦ ?_)
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with (hx | hx | hx)
      · exact hx ▸ hpa
      · exact hx ▸ hpb
      · refine hx ▸ hp.dvd_of_dvd_pow (n := 3) ?_
        exact hF.symm ▸ dvd_add (dvd_pow hpa (by decide)) (dvd_pow hpb (by decide))
    · exact_mod_cast hF

end misc

section eisenstein

attribute [instance] IsCyclotomicExtension.Rat.three_pid

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+))

noncomputable
instance : NormalizedGCDMonoid (𝓞 K) :=
  have : Nonempty (NormalizedGCDMonoid (𝓞 K)) := inferInstance
  this.some

local notation3 "η" => hζ.toInteger

local notation3 "λ" => hζ.toInteger - 1

/-- Let `K` be a `3`-rd cyclotomic extension of `ℚ` and let `ζ : K` be such that
`hζ : IsPrimitiveRoot ζ 3`. Setting `λ = ζ - 1` (in `𝓞 K`), `FermatLastTheoremForThreeGen hζ`
is the statement that `a ^ 3 + b ^ 3 = u * c ^ 3` has no nontrivial solutions in `𝓞 K` for all
`u : (𝓞 K)ˣ` such that `¬ λ ∣ a`, `¬ λ ∣ b` and `λ ∣ c`.
The reason to consider `FermatLastTheoremForThreeGen hζ` is to make a descent argument working. -/
def FermatLastTheoremForThreeGen : Prop :=
  ∀ a b c : 𝓞 K, ∀ u : (𝓞 K)ˣ, c ≠ 0 → ¬ λ ∣ a → ¬ λ ∣ b  → λ ∣ c → IsCoprime a b →
    a ^ 3 + b ^ 3 ≠ u * c ^ 3

/-- To prove `FermatLastTheoremFor 3`, it is enough to prove `FermatLastTheoremForThreeGen hζ`. -/
lemma FermatLastTheoremForThree_of_FermatLastTheoremThreeGen :
    FermatLastTheoremForThreeGen hζ → FermatLastTheoremFor 3 := by
  intro H
  refine fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h ↦ ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd ↦ ha ?_) (fun hdvd ↦ hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (norm_lambda_prime hζ), norm_lambda hζ] at hdvd
  · rwa [← Ideal.norm_dvd_iff (norm_lambda_prime hζ), norm_lambda hζ] at hdvd
  · exact dvd_trans (lambda_dvd_three hζ) ⟨x, by simp [hx]⟩
  · rw [show a = algebraMap _ (𝓞 K) a by simp, show b = algebraMap _ (𝓞 K) b by simp]
    exact hcoprime.map _
  · simp only [val_one, one_mul]
    exact_mod_cast h

section FermatLastTheoremForThreeGen

variable {a b c : 𝓞 K} {u : (𝓞 K)ˣ} (hc : c ≠ 0) (H : a ^ 3 + b ^ 3 = u * c ^ 3)
  (hcoprime : IsCoprime a b) (ha : ¬ (hζ.toInteger - 1) ∣ a) (hb : ¬ (hζ.toInteger - 1) ∣ b)
  (hcdvd : (hζ.toInteger - 1) ∣ c)

lemma a_cube_b_cube_same_congr :
    λ ^ 4 ∣ a ^ 3 - 1 ∧ λ ^ 4 ∣ b ^ 3 + 1 ∨  λ ^ 4 ∣ a ^ 3 + 1 ∧ λ ^ 4 ∣ b ^ 3 - 1 := by
  obtain ⟨z, hz⟩ := hcdvd
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ ha with
    (⟨x, hx⟩ | ⟨x, hx⟩) <;>
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ hb with
    (⟨y, hy⟩ | ⟨y, hy⟩)
  · exfalso
    refine lambda_not_dvd_two hζ ⟨u * λ ^ 2 * z ^ 3 - λ ^ 3 * (x + y), ?_⟩
    symm
    calc _ = u * (λ * z) ^ 3 - λ ^ 4 * x - λ ^ 4 * y := by ring
    _ = (a ^ 3 + b ^ 3) - (a ^ 3 - 1) - (b ^ 3 - 1) := by rw [← hx, ← hy, ← hz, ← H]
    _ = 2 := by ring
  · left
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · right
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exfalso
    refine lambda_not_dvd_two hζ ⟨λ ^ 3 * (x + y) - u * λ ^ 2 * z ^ 3, ?_⟩
    symm
    calc _ =  λ ^ 4 * x + λ ^ 4 * y - u * (λ * z) ^ 3 := by ring
    _ = (a ^ 3 + 1) + (b ^ 3 + 1) - (a ^ 3 + b ^ 3) := by rw [← hx, ← hy, ← hz, ← H]
    _ = 2 := by ring

lemma lambda_pow_four_dvd_c_cube : λ ^ 4 ∣ c ^ 3 := by
  rcases a_cube_b_cube_same_congr hζ H ha hb hcdvd with
    (⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩) <;> {
  refine ⟨u⁻¹ * (x + y), ?_⟩
  symm
  calc _ = u⁻¹ * (λ ^ 4 * x + λ ^ 4 * y) := by ring
  _ = u⁻¹ * (a ^ 3 + b ^ 3) := by rw [← hx, ← hy]; ring
  _ = u⁻¹ * (u * c ^ 3) := by rw [H]
  _ = c ^ 3 := by simp }

lemma multiplicity_lambda_c_finite : multiplicity.Finite (hζ.toInteger - 1) c := by
  have := IsCyclotomicExtension.Rat.three_pid K
  exact multiplicity.finite_of_not_isUnit (lambda_not_unit hζ) hc

lemma lambda_pow_two_dvd_c : λ ^ 2 ∣ c := by
  classical
  have  hm := multiplicity_lambda_c_finite hζ hc
  suffices 2 ≤ (multiplicity ((hζ.toInteger - 1)) c).get hm by
    · obtain ⟨x, hx⟩ := multiplicity.pow_multiplicity_dvd hm
      refine ⟨λ ^ ((multiplicity ((hζ.toInteger - 1)) c).get hm - 2) * x, ?_⟩
      rw [← mul_assoc, ← pow_add]
      convert hx using 3
      simp [this]
  have := lambda_pow_four_dvd_c_cube hζ H ha hb hcdvd
  have hm1 :(multiplicity (hζ.toInteger - 1) (c ^ 3)).get
    (multiplicity.finite_pow hζ.zeta_sub_one_prime' hm) =
    multiplicity (hζ.toInteger - 1) (c ^ 3) := by simp
  rw [multiplicity.pow_dvd_iff_le_multiplicity, ← hm1, multiplicity.pow' hζ.zeta_sub_one_prime' hm,
    Nat.cast_ofNat, Nat.ofNat_le_cast] at this
  linarith

variable (a b) in
lemma cube_add_cube_eq_mul : a ^ 3 + b ^ 3 = (a + b) * (a + η * b) * (a + η ^ 2 * b) := by
  symm
  calc _ = a^3+a^2*b*(η^2+η+1)+a*b^2*(η^2+η+η^3)+η^3*b^3 := by ring
  _ = a^3+a^2*b*(η^2+η+1)+a*b^2*(η^2+η+1)+b^3 := by rw [hζ.toInteger_cube_eq_one, one_mul]
  _ = a ^ 3 + b ^ 3 := by rw [hζ.toInteger_eval_cyclo]; ring

open PartENat in
lemma lambda_sq_dvd_or_dvd_or_dvd : λ ^ 2 ∣ a + b ∨ λ ^ 2 ∣ a + η * b ∨ λ ^ 2 ∣ a + η ^ 2 * b := by
  classical
  by_contra! h
  rcases h with ⟨h1, h2, h3⟩
  rw [← multiplicity.multiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : multiplicity.Finite (hζ.toInteger - 1) (a + b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h1)
  have h2' : multiplicity.Finite (hζ.toInteger - 1) (a + η * b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h2)
  have h3' : multiplicity.Finite (hζ.toInteger - 1) (a + η ^ 2 * b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h3)
  replace h1' : (multiplicity (hζ.toInteger - 1) (a + b)).get h1' =
    multiplicity (hζ.toInteger - 1) (a + b) := by simp
  replace h2' : (multiplicity (hζ.toInteger - 1) (a + η * b)).get h2' =
    multiplicity (hζ.toInteger - 1) (a + η * b) := by simp
  replace h3' : (multiplicity (hζ.toInteger - 1) (a + η ^ 2 * b)).get h3' =
    multiplicity (hζ.toInteger - 1) (a + η ^ 2 * b) := by simp
  rw [← h1', coe_lt_coe] at h1; rw [← h2', coe_lt_coe] at h2; rw [← h3', coe_lt_coe] at h3
  have := (pow_dvd_pow_of_dvd (lambda_pow_two_dvd_c hζ hc H ha hb hcdvd) 3).mul_left u
  rw [← pow_mul, ← H, cube_add_cube_eq_mul hζ, multiplicity.pow_dvd_iff_le_multiplicity,
    multiplicity.mul hζ.zeta_sub_one_prime', multiplicity.mul hζ.zeta_sub_one_prime', ← h1', ← h2',
    ← h3', ← Nat.cast_add, ← Nat.cast_add, coe_le_coe] at this
  linarith

lemma ex_dvd_a_add_b : ∃ (a' b' c' : 𝓞 K) (u' : (𝓞 K)ˣ), c' ≠ 0 ∧  a' ^ 3 + b' ^ 3 = u' * c' ^ 3 ∧
    IsCoprime a' b' ∧ ¬ λ ∣ a' ∧ ¬ λ ∣ b' ∧ λ ^ 2 ∣ a' + b' := by
  rcases lambda_sq_dvd_or_dvd_or_dvd hζ hc H ha hb  hcdvd with (h | h | h)
  · exact ⟨a, b, c, u, hc, H, hcoprime, ha, hb, h⟩
  · refine ⟨a, η * b, c, u, hc, ?_, ?_, ha, fun ⟨x, hx⟩ ↦ hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · rwa [mul_pow, hζ.toInteger_cube_eq_one, one_mul]
    · exact (isCoprime_mul_unit_left_right hζ.eta_isUnit _ _).2 hcoprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ b, mul_assoc, ← pow_succ,
        hζ.toInteger_cube_eq_one, mul_one]
  · refine ⟨a, η ^ 2 * b, c, u, hc, ?_, ?_, ha, fun ⟨x, hx⟩ ↦ hb ⟨η * x, ?_⟩, h⟩
    · rwa [mul_pow, ← pow_mul, mul_comm 2, pow_mul, hζ.toInteger_cube_eq_one, one_pow, one_mul]
    · exact (isCoprime_mul_unit_left_right (hζ.eta_isUnit.pow _) _ _).2 hcoprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ b, mul_assoc, ← pow_succ',
        hζ.toInteger_cube_eq_one, mul_one]

variable (hab : (hζ.toInteger - 1) ^ 2 ∣ a + b)

lemma lambda_dvd_add_eta_mul : λ ∣ a + η * b := by
  rw [show a + η * b = (a + b) + λ * b by ring]
  exact dvd_add (dvd_trans (dvd_pow_self _ (by decide)) hab) ⟨b, by rw [mul_comm]⟩

lemma lambda_dvd_add_eta_sq_mul : λ ∣ a + η ^ 2 * b := by
  rw [show a + η ^ 2 * b = (a + b) + λ ^ 2 * b + 2 * λ * b by ring]
  exact dvd_add (dvd_add (dvd_trans (dvd_pow_self _ (by decide)) hab) ⟨λ * b, by ring⟩)
    ⟨2 * b, by ring⟩

lemma lambda_sq_not_dvd_add_eta_mul : ¬ λ ^ 2 ∣ a + η * b := by
  sorry

lemma lambda_sq_not_dvd_add_eta_sq_mul : ¬ λ ^ 2 ∣ a + η ^ 2 * b := by
  sorry

theorem final (hc : c ≠ 0) (ha : ¬ λ ∣ a) (hb : ¬ λ ∣ b) (hcdvd : λ ∣ c)
    (hcoprime : IsCoprime a b) : a ^ 3 + b ^ 3 ≠ u * c ^ 3 := by
  sorry

end FermatLastTheoremForThreeGen

end eisenstein

end case2

theorem fermatLastTheoremThree : FermatLastTheoremFor 3 := by
  let K := CyclotomicField 3 ℚ
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ (CyclotomicField 3 ℚ)
  have : NumberField K := IsCyclotomicExtension.numberField {3} ℚ _
  apply FermatLastTheoremForThree_of_FermatLastTheoremThreeGen hζ
  intro a b c u hc ha hb hcdvd hcoprime H
  exact final hζ hc ha hb hcdvd hcoprime H
