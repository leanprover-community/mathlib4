/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda,
  Lorenzo Luccioli, Pietro Monticone, Alexis Saurin, Florent Schaffhauser
-/
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Three
import Mathlib.Algebra.Ring.Divisibility.Lemmas

/-!
# Fermat Last Theorem in the case `n = 3`
The goal of this file is to prove Fermat Last theorem in the case `n = 3`.

## Main results
* `fermatLastTheoremThree_case1`: the first case of Fermat Last Theorem when `n = 3`:
  if `a b c : ℤ` are such that `¬ 3 ∣ a * b * c`, then `a ^ 3 + b ^ 3 ≠ c ^ 3`.

## TODO
Prove case 2.

## Implementation details
We follow the proof in <https://webusers.imj-prg.fr/~marc.hindry/Cours-arith.pdf>, page 43. The
strategy is the following:
* Case 1 is completely elementary and is proved using congruences modulo `9`.
* To prove case 2, we consider the generalized equation `a ^ 3 + b ^ 3 = u * c ^ 3`, where `a`, `b`,
  and `c` are in the cyclotomic ring `ℤ[ζ₃]` (where `ζ₃` is a primitive cube root of unity) and `u`
  is a unit of `ℤ[ζ₃]`. `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen` (whose proof is
  rather elementary on paper) says that to prove Fermat's last theorem for exponent `3`, it is
  enough to prove that this equation has no  solutions such that `c ≠ 0`, `¬ λ ∣ a`, `¬ λ ∣ b`,
  `λ ∣ c` and `IsCoprime a b`. We call such a tuple a `Solution'`. A `Solution` is the same as a
  `Solution'` with the additional assumption that `λ ^ 2 ∣ a + b`. We then prove that, given
  `S' : Solution'`, there is `S : Solution` such that the multiplicity of `λ = ζ₃ - 1` in `c` is
  the same in `S'` and `S`. In particular it is enough to prove that no `Solution` exists.
  The key point is a descent argument on the multiplicity of `λ` in `c`: starting with
  `S : Solution` we can find `S₁ : Solution` with multiplicity strictly smaller and this finishes
  the proof. To construct `S₁` we go through a `Solution'` and then back to a `Solution`. More
  importantly, we cannot control the unit `u`, and this is the reason why we need to consider
  the generalized equation `a ^ 3 + b ^ 3 = u * c ^ 3`.

-/

section case1

open ZMod

private lemma cube_of_castHom_ne_zero {n : ZMod 9} :
    castHom (show 3 ∣ 9 by norm_num) (ZMod 3) n ≠ 0 → n ^ 3 = 1 ∨ n ^ 3 = 8 := by
  revert n; decide

private lemma cube_of_not_dvd {n : ℤ} (h : ¬ 3 ∣ n) :
    (n : ZMod 9) ^ 3 = 1 ∨ (n : ZMod 9) ^ 3 = 8 := by
  apply cube_of_castHom_ne_zero
  rwa [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- If `a b c : ℤ` are such that `¬ 3 ∣ a * b * c`, then `a ^ 3 + b ^ 3 ≠ c ^ 3`. -/
theorem fermatLastTheoremThree_case_1 {a b c : ℤ} (hdvd : ¬ 3 ∣ a * b * c) :
    a ^ 3 + b ^ 3 ≠ c ^ 3 := by
  simp_rw [Int.prime_three.dvd_mul, not_or] at hdvd
  apply mt (congrArg (Int.cast : ℤ → ZMod 9))
  simp_rw [Int.cast_add, Int.cast_pow]
  rcases cube_of_not_dvd hdvd.1.1 with ha | ha <;>
  rcases cube_of_not_dvd hdvd.1.2 with hb | hb <;>
  rcases cube_of_not_dvd hdvd.2 with hc | hc <;>
  rw [ha, hb, hc] <;> decide

end case1

section case2

private lemma three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : ℤ} (ha : a ≠ 0)
    (Hgcd: Finset.gcd {a, b, c} id = 1) (h3a : 3 ∣ a) (HF : a ^ 3 + b ^ 3 + c ^ 3 = 0)
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    3 ∣ b := by
  have hbc : IsCoprime (-b) (-c) := by
    refine IsCoprime.neg_neg ?_
    rw [add_comm (a ^ 3), add_assoc, add_comm (a ^ 3), ← add_assoc] at HF
    refine isCoprime_of_gcd_eq_one_of_FLT ?_ HF
    convert Hgcd using 2
    rw [Finset.pair_comm, Finset.Insert.comm]
  by_contra! h3b
  by_cases h3c : 3 ∣ c
  · apply h3b
    rw [add_assoc, add_comm (b ^ 3), ← add_assoc] at HF
    exact dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT Int.prime_three h3a h3c HF
  · refine H (-b) (-c) a ha (by simp [h3b]) (by simp [h3c]) h3a hbc ?_
    rw [add_eq_zero_iff_eq_neg, ← (show Odd 3 by decide).neg_pow] at HF
    rw [← HF]
    ring

open Finset in
private lemma fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : ℤ} (ha : a ≠ 0)
    (h3a : 3 ∣ a) (Hgcd: Finset.gcd {a, b, c} id = 1)
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    a ^ 3 + b ^ 3 + c ^ 3 ≠ 0 := by
  intro HF
  apply (show ¬(3 ∣ (1 : ℤ)) by decide)
  rw [← Hgcd]
  refine dvd_gcd (fun x hx ↦ ?_)
  simp only [mem_insert, mem_singleton] at hx
  have h3b : 3 ∣ b := by
    refine three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 ha ?_ h3a HF H
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← Int.abs_eq_normalize, abs_neg]
  rcases hx with (hx | hx | hx)
  · exact hx ▸ h3a
  · exact hx ▸ h3b
  · simpa [hx] using dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT Int.prime_three h3a h3b HF

open Finset Int in
/--
  To prove Fermat's Last Theorem for `n = 3`, it is enough to show that that for all `a`, `b`, `c`
  in `ℤ` such that `c ≠ 0`, `¬ 3 ∣ a`, `¬ 3 ∣ b`, `a` and `b` are coprime and `3 ∣ c`, we have
  `a ^ 3 + b ^ 3 ≠ c ^ 3`.
-/
theorem fermatLastTheoremThree_of_three_dvd_only_c
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b  → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    FermatLastTheoremFor 3 := by
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime (fun a b c ha hb hc Hgcd hF ↦?_)
  by_cases h1 : 3 ∣ a * b * c
  swap
  · exact fermatLastTheoremThree_case_1 h1 hF
  rw [(prime_three).dvd_mul, (prime_three).dvd_mul] at h1
  rw [← sub_eq_zero, sub_eq_add_neg, ← (show Odd 3 by decide).neg_pow] at hF
  rcases h1 with ((h3a | h3b) | h3c)
  · refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 ha h3a ?_ H hF
    simp only [← Hgcd, Insert.comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm (a ^ 3)] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 hb h3b ?_ H hF
    simp only [← Hgcd, Insert.comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm _ ((-c) ^ 3), ← add_assoc] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 (neg_ne_zero.2 hc) (by simp [h3c])
      ?_ H hF
    rw [Finset.Insert.comm (-c), Finset.pair_comm (-c) b]
    simp only [← Hgcd, Insert.comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]

section eisenstein

open NumberField IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ (3 : ℕ+))

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

/-- `FermatLastTheoremForThreeGen` is the statement that `a ^ 3 + b ^ 3 = u * c ^ 3` has no
nontrivial solutions in `𝓞 K` for all `u : (𝓞 K)ˣ` such that `¬ λ ∣ a`, `¬ λ ∣ b` and `λ ∣ c`.
The reason to consider `FermatLastTheoremForThreeGen` is to make a descent argument working. -/
def FermatLastTheoremForThreeGen : Prop :=
  ∀ a b c : 𝓞 K, ∀ u : (𝓞 K)ˣ, c ≠ 0 → ¬ λ ∣ a → ¬ λ ∣ b  → λ ∣ c → IsCoprime a b →
    a ^ 3 + b ^ 3 ≠ u * c ^ 3

/-- To prove `FermatLastTheoremFor 3`, it is enough to prove `FermatLastTheoremForThreeGen`. -/
lemma FermatLastTheoremForThree_of_FermatLastTheoremThreeGen :
    FermatLastTheoremForThreeGen hζ → FermatLastTheoremFor 3 := by
  intro H
  refine fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h ↦ ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd ↦ ha ?_) (fun hdvd ↦ hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · exact dvd_trans hζ.toInteger_sub_one_dvd_prime' ⟨x, by simp [hx]⟩
  · rw [show a = algebraMap _ (𝓞 K) a by simp, show b = algebraMap _ (𝓞 K) b by simp]
    exact hcoprime.map _
  · simp only [Units.val_one, one_mul]
    exact_mod_cast h

namespace FermatLastTheoremForThreeGen

/-- `Solution'` is a tuple given by a solution to `a ^ 3 + b ^ 3 = u * c ^ 3`,
where `a`, `b`, `c` and `u` are as in `FermatLastTheoremForThreeGen`.
See `Solution` for the actual structure on which we will do the descent. -/
structure Solution' where
  a : 𝓞 K
  b : 𝓞 K
  c : 𝓞 K
  u : (𝓞 K)ˣ
  ha : ¬ λ ∣ a
  hb : ¬ λ ∣ b
  hc : c ≠ 0
  coprime : IsCoprime a b
  hcdvd : λ ∣ c
  H : a ^ 3 + b ^ 3 = u * c ^ 3
attribute [nolint docBlame] Solution'.a
attribute [nolint docBlame] Solution'.b
attribute [nolint docBlame] Solution'.c
attribute [nolint docBlame] Solution'.u

/-- `Solution` is the same as `Solution'` with the additional assumption that `λ ^ 2 ∣ a + b`. -/
structure Solution extends Solution' hζ where
  hab : λ ^ 2 ∣ a + b

variable {hζ}
variable (S : Solution hζ) (S' : Solution' hζ) [DecidableRel fun (a b : 𝓞 K) ↦ a ∣ b]

/-- For any `S' : Solution'`, the multiplicity of `λ` in `S'.c` is finite. -/
lemma Solution'.multiplicity_lambda_c_finite :
    multiplicity.Finite (hζ.toInteger - 1) S'.c :=
  multiplicity.finite_of_not_isUnit hζ.zeta_sub_one_prime'.not_unit S'.hc

/-- Given `S' : Solution'`, `S'.multiplicity` is the multiplicity of `λ` in `S'.c`, as a natural
number. -/
def Solution'.multiplicity :=
  (_root_.multiplicity (hζ.toInteger - 1) S'.c).get (multiplicity_lambda_c_finite S')

/-- Given `S : Solution`, `S.multiplicity` is the multiplicity of `λ` in `S.c`, as a natural
number. -/
def Solution.multiplicity := S.toSolution'.multiplicity

/-- We say that `S : Solution` is minimal if for all `S₁ : Solution`, the multiplicity of `λ` in
`S.c` is less or equal than the multiplicity in `S₁.c`. -/
def Solution.isMinimal : Prop := ∀ (S₁ : Solution hζ), S.multiplicity ≤ S₁.multiplicity

/-- If there is a solution then there is a minimal one. -/
lemma Solution.exists_minimal : ∃ (S₁ : Solution hζ), S₁.isMinimal := by
  classical
  let T := {n | ∃ (S' : Solution hζ), S'.multiplicity = n}
  rcases Nat.find_spec (⟨S.multiplicity, ⟨S, rfl⟩⟩ : T.Nonempty) with ⟨S₁, hS₁⟩
  exact ⟨S₁, fun S'' ↦ hS₁ ▸ Nat.find_min' _ ⟨S'', rfl⟩⟩

/-- Given `S' : Solution'`, then `S'.a` and `S'.b` are both congruent to `1` modulo `λ ^ 4` or are
both congruent to `-1`.  -/
lemma a_cube_b_cube_congr_one_or_neg_one :
    λ ^ 4 ∣ S'.a ^ 3 - 1 ∧ λ ^ 4 ∣ S'.b ^ 3 + 1 ∨ λ ^ 4 ∣ S'.a ^ 3 + 1 ∧ λ ^ 4 ∣ S'.b ^ 3 - 1 := by
  obtain ⟨z, hz⟩ := S'.hcdvd
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.ha with
    (⟨x, hx⟩ | ⟨x, hx⟩) <;>
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.hb with
    (⟨y, hy⟩ | ⟨y, hy⟩)
  · exfalso
    replace hζ : IsPrimitiveRoot ζ ((3 : ℕ+) ^ 1) := by rwa [pow_one]
    refine hζ.toInteger_sub_one_not_dvd_two (by decide) ⟨S'.u * λ ^ 2 * z ^ 3 - λ ^ 3 * (x + y), ?_⟩
    symm
    calc _ = S'.u * (λ * z) ^ 3 - λ ^ 4 * x - λ ^ 4 * y := by ring
    _ = (S'.a ^ 3 + S'.b ^ 3) - (S'.a ^ 3 - 1) - (S'.b ^ 3 - 1) := by rw [← hx, ← hy, ← hz, ← S'.H]
    _ = 2 := by ring
  · left
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · right
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exfalso
    replace hζ : IsPrimitiveRoot ζ ((3 : ℕ+) ^ 1) := by rwa [pow_one]
    refine hζ.toInteger_sub_one_not_dvd_two (by decide) ⟨λ ^ 3 * (x + y) - S'.u * λ ^ 2 * z ^ 3, ?_⟩
    symm
    calc _ =  λ ^ 4 * x + λ ^ 4 * y - S'.u * (λ * z) ^ 3 := by ring
    _ = (S'.a ^ 3 + 1) + (S'.b ^ 3 + 1) - (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy, ← hz, ← S'.H]
    _ = 2 := by ring

/-- Given `S' : Solution'`, we have that `λ ^ 4` divides `S'.c ^ 3`. -/
lemma lambda_pow_four_dvd_c_cube : λ ^ 4 ∣ S'.c ^ 3 := by
  rcases a_cube_b_cube_congr_one_or_neg_one S' with
    (⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩) <;>
  · refine ⟨S'.u⁻¹ * (x + y), ?_⟩
    symm
    calc _ = S'.u⁻¹ * (λ ^ 4 * x + λ ^ 4 * y) := by ring
    _ = S'.u⁻¹ * (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy]; ring
    _ = S'.u⁻¹ * (S'.u * S'.c ^ 3) := by rw [S'.H]
    _ = S'.c ^ 3 := by simp

/-- Given `S' : Solution'`, we have that `λ ^ 2` divides `S'.c`. -/
lemma lambda_sq_dvd_c : λ ^ 2 ∣ S'.c := by
  have hm := S'.multiplicity_lambda_c_finite
  suffices 2 ≤ (multiplicity ((hζ.toInteger - 1)) S'.c).get hm by
    obtain ⟨x, hx⟩ := multiplicity.pow_multiplicity_dvd hm
    refine ⟨λ ^ ((multiplicity ((hζ.toInteger - 1)) S'.c).get hm - 2) * x, ?_⟩
    rw [← mul_assoc, ← pow_add]
    convert hx using 3
    simp [this]
  have := lambda_pow_four_dvd_c_cube S'
  have hm1 : (multiplicity (hζ.toInteger - 1) (S'.c ^ 3)).get
    (multiplicity.finite_pow hζ.zeta_sub_one_prime' hm) =
    multiplicity (hζ.toInteger - 1) (S'.c ^ 3) := by simp
  rw [multiplicity.pow_dvd_iff_le_multiplicity, ← hm1, multiplicity.pow' hζ.zeta_sub_one_prime' hm,
    Nat.cast_ofNat, Nat.ofNat_le_cast] at this
  omega

/-- Given `S' : Solution'`, we have that `2 ≤ S'.multiplicity`. -/
lemma Solution'.two_le_multiplicity : 2 ≤ S'.multiplicity := by
  simpa [← PartENat.coe_le_coe, Solution'.multiplicity] using
    multiplicity.le_multiplicity_of_pow_dvd (lambda_sq_dvd_c S')

/-- Given `S : Solution`, we have that `2 ≤ S.multiplicity`. -/
lemma Solution.two_le_multiplicity : 2 ≤ S.multiplicity :=
  S.toSolution'.two_le_multiplicity

/-- Given `S' : Solution'`, the key factorization of `S'.a ^ 3 + S'.b ^ 3`. -/
lemma a_cube_add_b_cube_eq_mul :
    S'.a ^ 3 + S'.b ^ 3 = (S'.a + S'.b) * (S'.a + η * S'.b) * (S'.a + η ^ 2 * S'.b) := by
  have := hζ.isRoot_cyclotomic (by decide)
  simp only [PNat.val_ofNat, Polynomial.cyclotomic_three, Polynomial.IsRoot.def,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at this
  symm
  calc _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+η^3)+η^3*S'.b^3 := by ring
  _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+1)+S'.b^3 := by
    simp [hζ.toInteger_cube_eq_one]
  _ = S'.a ^ 3 + S'.b ^ 3 := by ext; simp [this]

open PartENat in
/-- Given `S' : Solution'`, we have that `λ ^ 2` divides one amongst `S'.a + S'.b`,
`S'.a + η * S'.b` and `S'.a + η ^ 2 * S'.b`. -/
lemma lambda_sq_dvd_or_dvd_or_dvd :
    λ ^ 2 ∣ S'.a + S'.b ∨ λ ^ 2 ∣ S'.a + η * S'.b ∨ λ ^ 2 ∣ S'.a + η ^ 2 * S'.b := by
  by_contra! h
  rcases h with ⟨h1, h2, h3⟩
  rw [← multiplicity.multiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : multiplicity.Finite (hζ.toInteger - 1) (S'.a + S'.b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h1)
  have h2' : multiplicity.Finite (hζ.toInteger - 1) (S'.a + η * S'.b) := by
    refine multiplicity.ne_top_iff_finite.1 (fun ht ↦ ?_)
    rw [coe_eta] at ht
    simp [ht] at h2
  have h3' : multiplicity.Finite (hζ.toInteger - 1) (S'.a + η ^ 2 * S'.b) := by
    refine multiplicity.ne_top_iff_finite.1 (fun ht ↦ ?_)
    rw [coe_eta] at ht
    simp [ht] at h3
  replace h1' : (multiplicity (hζ.toInteger - 1) (S'.a + S'.b)).get h1' =
    multiplicity (hζ.toInteger - 1) (S'.a + S'.b) := by simp
  replace h2' : (multiplicity (hζ.toInteger - 1) (S'.a + η * S'.b)).get h2' =
    multiplicity (hζ.toInteger - 1) (S'.a + η * S'.b) := by simp
  replace h3' : (multiplicity (hζ.toInteger - 1) (S'.a + η ^ 2 * S'.b)).get h3' =
    multiplicity (hζ.toInteger - 1) (S'.a + η ^ 2 * S'.b) := by simp
  rw [← h1', coe_lt_coe] at h1; rw [← h2', coe_lt_coe] at h2; rw [← h3', coe_lt_coe] at h3
  have := (pow_dvd_pow_of_dvd (lambda_sq_dvd_c S') 3).mul_left S'.u
  rw [← pow_mul, ← S'.H, a_cube_add_b_cube_eq_mul, multiplicity.pow_dvd_iff_le_multiplicity,
    multiplicity.mul hζ.zeta_sub_one_prime', multiplicity.mul hζ.zeta_sub_one_prime', ← h1', ← h2',
    ← h3', ← Nat.cast_add, ← Nat.cast_add, coe_le_coe] at this
  omega

open Units in
/-- Given `S' : Solution'`, we may assume that `λ ^ 2` divides `S'.a + S'.b ∨ λ ^ 2` (see also the
result below). -/
lemma ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd :
    ∃ (a' b' : 𝓞 K), a' ^ 3 + b' ^ 3 = S'.u * S'.c ^ 3 ∧ IsCoprime a' b' ∧ ¬ λ ∣ a' ∧
      ¬ λ ∣ b' ∧ λ ^ 2 ∣ a' + b' := by
  rcases lambda_sq_dvd_or_dvd_or_dvd S' with (h | h | h)
  · exact ⟨S'.a, S'.b, S'.H, S'.coprime, S'.ha, S'.hb, h⟩
  · refine ⟨S'.a, η * S'.b, ?_, ?_, S'.ha, fun ⟨x, hx⟩ ↦ S'.hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · simp [mul_pow, ← val_pow_eq_pow_val, hζ.toInteger_cube_eq_one, val_one, one_mul, S'.H]
    · refine (isCoprime_mul_unit_left_right (Units.isUnit η) _ _).2 S'.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S'.b, mul_assoc, ← pow_succ', coe_eta,
        hζ.toInteger_cube_eq_one, mul_one]
  · refine ⟨S'.a, η ^ 2 * S'.b, ?_, ?_, S'.ha, fun ⟨x, hx⟩ ↦ S'.hb ⟨η * x, ?_⟩, h⟩
    · rw [mul_pow, ← pow_mul, mul_comm 2, pow_mul, coe_eta, hζ.toInteger_cube_eq_one, one_pow,
        one_mul, S'.H]
    · exact (isCoprime_mul_unit_left_right ((Units.isUnit η).pow _) _ _).2 S'.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S'.b, mul_assoc, ← pow_succ, coe_eta,
        hζ.toInteger_cube_eq_one, mul_one]

/-- Given `S' : Solution'`, then there is `S₁ : Solution` such that
`S₁.multiplicity = S'.multiplicity`. -/
lemma exists_Solution_of_Solution' : ∃ (S₁ : Solution hζ), S₁.multiplicity = S'.multiplicity := by
  obtain ⟨a, b, H, coprime, ha, hb, hab⟩ := ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd S'
  exact ⟨
  { a := a
    b := b
    c := S'.c
    u := S'.u
    ha := ha
    hb := hb
    hc := S'.hc
    coprime := coprime
    hcdvd := S'.hcdvd
    H := H
    hab := hab }, rfl⟩

namespace Solution

lemma a_add_eta_mul_b : S.a + η * S.b = (S.a + S.b) + λ * S.b := by rw [coe_eta]; ring

/-- Given `(S : Solution)`, we have that `λ ∣ (S.a + η * S.b)`. -/
lemma lambda_dvd_a_add_eta_mul_b : λ ∣ (S.a + η * S.b) :=
  a_add_eta_mul_b S ▸ dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨S.b, by rw [mul_comm]⟩

/-- Given `(S : Solution)`, we have that `λ ∣ (S.a + η ^ 2 * S.b)`. -/
lemma lambda_dvd_a_add_eta_sq_mul_b : λ ∣ (S.a + η ^ 2 * S.b) := by
  rw [show S.a + η ^ 2 * S.b = (S.a + S.b) + λ ^ 2 * S.b + 2 * λ * S.b by rw [coe_eta]; ring]
  exact dvd_add (dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨λ * S.b, by ring⟩)
    ⟨2 * S.b, by ring⟩

/-- Given `(S : Solution)`, we have that `λ ^ 2` does not divide `S.a + η * S.b`. -/
lemma lambda_sq_not_dvd_a_add_eta_mul_b : ¬ λ ^ 2 ∣ (S.a + η * S.b) := by
  simp_rw [a_add_eta_mul_b, dvd_add_right S.hab, pow_two, mul_dvd_mul_iff_left
    hζ.zeta_sub_one_prime'.ne_zero, S.hb, not_false_eq_true]

/-- Given `(S : Solution)`, we have that `λ ^ 2` does not divide `S.a + η ^ 2 * S.b`. -/
lemma lambda_sq_not_dvd_a_add_eta_sq_mul_b : ¬ λ ^ 2 ∣ (S.a + η ^ 2 * S.b) := by
  intro ⟨k, hk⟩
  rcases S.hab with ⟨k', hk'⟩
  refine S.hb ⟨(k - k') * (-η), ?_⟩
  rw [show S.a + η ^ 2 * S.b = S.a + S.b - S.b + η ^ 2 * S.b by ring, hk',
    show λ ^ 2 * k' - S.b + η ^ 2 * S.b = λ * (S.b * (η +1) + λ * k') by rw [coe_eta]; ring,
    pow_two, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, hζ.zeta_sub_one_prime'.ne_zero, or_false] at hk
  apply_fun (· * -↑η) at hk
  rw [show (S.b * (η + 1) + λ * k') * -η = (- S.b) * (η ^ 2 + η + 1 - 1) - η * λ * k' by ring,
    eta_sq, show -S.b * (-↑η - 1 + ↑η + 1 - 1) = S.b by ring, sub_eq_iff_eq_add] at hk
  rw [hk]
  ring

lemma eta_add_one_mul_neg_eta_eq_one : ((η : 𝓞 K) + 1) * (-η) = 1 :=
  calc ((η : 𝓞 K) + 1) * -η = -(η ^ 2 + η + 1) + 1 := by ring
  _ = 1 := by rw [eta_sq]; ring

attribute [local instance] IsCyclotomicExtension.Rat.three_pid
attribute [local instance] UniqueFactorizationMonoid.toGCDMonoid

/-- If `p : 𝓞 K` is a prime that divides both `S.a + S.b` and `S.a + η * S.b`, then `p`
is associated with `λ`. -/
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpab : p ∣ S.a + S.b) (hpaηb : p ∣ S.a + η * S.b) : Associated p λ := by
  suffices p_lam : p ∣ λ from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a, ← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηb
  rwa [one_mul, one_mul, coe_eta, IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime] at this

/-- If `p : 𝓞 K` is a prime that divides both `S.a + S.b` and `S.a + η ^ 2 * S.b`, then `p`
is associated with `λ`. -/
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpab : p ∣ (S.a + S.b)) (hpaηsqb : p ∣ (S.a + η ^ 2 * S.b)) : Associated p λ := by
  suffices p_lam : p ∣ λ from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  rw [← one_mul S.a, ← one_mul S.b] at hpab
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpab hpaηsqb
  rw [one_mul, mul_one, IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime, ← dvd_neg] at this
  convert dvd_mul_of_dvd_left this η using 1
  rw [eta_sq, neg_sub, sub_mul, sub_mul, neg_mul, ← pow_two, eta_sq, coe_eta]
  ring

/-- If `p : 𝓞 K` is a prime that divides both `S.a + η * S.b` and `S.a + η ^ 2 * S.b`, then `p`
is associated with `λ`. -/
lemma associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpaηb : p ∣ S.a + η * S.b) (hpaηsqb : p ∣ S.a + η ^ 2 * S.b) : Associated p λ := by
  suffices p_lam : p ∣ λ from hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  by_contra p_lam
  refine hp.not_unit <| S.coprime.isUnit_of_dvd' ?_ ?_
  · refine (hp.dvd_or_dvd ?_).resolve_left p_lam
    rw [show λ * S.a = η * (S.a + η * S.b) - (S.a + η ^ 2 * S.b) by rw [coe_eta]; ring]
    exact dvd_mul_of_dvd_right hpaηb _ |>.sub hpaηsqb
  · refine (hp.dvd_or_dvd ?_).resolve_left p_lam
    rw [← (Units.isUnit η).dvd_mul_left, show η * (λ * S.b) = (S.a + η ^ 2 * S.b) - (S.a + η * S.b)
      by rw [coe_eta]; ring]
    exact hpaηsqb.sub hpaηb

/-- Given `S : Solution`, we let `S.y` be any element such that `S.a + η * S.b = λ * S.y` -/
private noncomputable def y := (lambda_dvd_a_add_eta_mul_b S).choose

private lemma y_spec : S.a + η * S.b = λ * S.y :=
  (lambda_dvd_a_add_eta_mul_b S).choose_spec

/-- Given `S : Solution`, we let `S.z` be any element such that `S.a + η ^ 2 * S.b = λ * S.z` -/
private noncomputable def z := (lambda_dvd_a_add_eta_sq_mul_b S).choose

private lemma z_spec : S.a + η ^ 2 * S.b = λ * S.z :=
  (lambda_dvd_a_add_eta_sq_mul_b S).choose_spec

private lemma lambda_not_dvd_y : ¬ λ ∣ S.y := fun h ↦ by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta, ← y_spec, ← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_mul_b _ h

private lemma lambda_not_dvd_z : ¬ λ ∣ S.z := fun h ↦ by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta, ← z_spec, ← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_sq_mul_b _ h

/-- We have that `λ ^ (3*S.multiplicity-2)` divides `S.a + S.b`. -/
lemma lambda_pow_dvd_a_add_b : λ ^ (3 * S.multiplicity - 2) ∣ S.a + S.b := by
  have h : λ ^ S.multiplicity ∣ S.c := multiplicity.pow_multiplicity_dvd _
  replace h : (λ ^ multiplicity S) ^ 3 ∣ S.u * S.c ^ 3 := by simp [h]
  rw [← S.H, a_cube_add_b_cube_eq_mul, ← pow_mul, mul_comm, y_spec, z_spec] at h
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_z
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_y
  have := S.two_le_multiplicity
  rw [show 3 * multiplicity S = 3 * multiplicity S - 2 + 1 + 1 by omega, pow_succ, pow_succ,
    show (S.a + S.b) * (λ * y S) * (λ * z S) = (S.a + S.b) * y S * z S * λ * λ by ring] at h
  simp only [mul_dvd_mul_iff_right hζ.zeta_sub_one_prime'.ne_zero] at h
  rwa [show (S.a + S.b) * y S * z S = y S * (z S * (S.a + S.b)) by ring] at h

/-- Given `S : Solution`, we let `S.x` be any element such that
`S.a + S.b = λ ^ (3*S.multiplicity-2) * S.x` -/
private noncomputable def x := (lambda_pow_dvd_a_add_b S).choose

private lemma x_spec : S.a + S.b = λ ^ (3 * S.multiplicity - 2) * S.x :=
  (lambda_pow_dvd_a_add_b S).choose_spec

/-- Given `S : Solution`, we let `S.w` be any element such that `S.c = λ ^ S.multiplicity * S.w` -/
private noncomputable def w :=
  (multiplicity.pow_multiplicity_dvd S.toSolution'.multiplicity_lambda_c_finite).choose

private lemma w_spec : S.c = λ ^ S.multiplicity * S.w :=
  (multiplicity.pow_multiplicity_dvd S.toSolution'.multiplicity_lambda_c_finite).choose_spec

private lemma lambda_not_dvd_w : ¬ λ ∣ S.w := by
  intro h
  replace h := mul_dvd_mul_left (λ ^ S.multiplicity) h
  rw [← w_spec] at h
  have hh : _ := multiplicity.is_greatest' S.toSolution'.multiplicity_lambda_c_finite
    (lt_add_one S.multiplicity)
  rw [pow_succ', mul_comm] at hh
  exact hh h

private lemma lambda_not_dvd_x : ¬ λ ∣ S.x := fun h ↦ by
  replace h := mul_dvd_mul_left (λ ^ (3 * S.multiplicity - 2)) h
  rw [mul_comm, ← x_spec] at h
  replace h :=
    mul_dvd_mul (mul_dvd_mul h S.lambda_dvd_a_add_eta_mul_b) S.lambda_dvd_a_add_eta_sq_mul_b
  simp only [← a_cube_add_b_cube_eq_mul, S.H, w_spec, Units.isUnit, IsUnit.dvd_mul_left] at h
  rw [← pow_succ', mul_comm, ← mul_assoc, ← pow_succ'] at h
  have := S.two_le_multiplicity
  rw [show 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S by omega, mul_pow, ← pow_mul,
    mul_comm _ 3, mul_dvd_mul_iff_left _] at h
  · exact lambda_not_dvd_w _ <| hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h
  · simp [hζ.zeta_sub_one_prime'.ne_zero]

private lemma isCoprime_helper {r s t w : 𝓞 K} (hr : ¬ λ ∣ r) (hs : ¬ λ ∣ s)
    (Hp : ∀ {p}, Prime p → p ∣ t → p ∣ w → Associated p λ) (H₁ : ∀ {q}, q ∣ r → q ∣ t)
    (H₂ : ∀ {q}, q ∣ s → q ∣ w) : IsCoprime r s := by
  refine isCoprime_of_prime_dvd (not_and.2 (fun _ hz ↦ hs (by simp [hz])))
    (fun p hp p_dvd_r p_dvd_s ↦ hr ?_)
  rwa [← Associated.dvd_iff_dvd_left <| Hp hp (H₁ p_dvd_r) (H₂ p_dvd_s)]

private lemma isCoprime_x_y : IsCoprime S.x S.y :=
  isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_y S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b S) (fun hq ↦ x_spec S ▸ hq.mul_left _)
      (fun hq ↦ y_spec S ▸ hq.mul_left _)

private lemma isCoprime_x_z : IsCoprime S.x S.z :=
  isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b S) (fun hq ↦ x_spec S ▸ hq.mul_left _)
      (fun hq ↦ z_spec S ▸ hq.mul_left _)

private lemma isCoprime_y_z : IsCoprime S.y S.z :=
  isCoprime_helper (lambda_not_dvd_y S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b S)
    (fun hq ↦ y_spec S ▸ hq.mul_left _) (fun hq ↦ z_spec S ▸ hq.mul_left _)

private lemma x_mul_y_mul_z_eq_u_mul_w_cube : S.x * S.y * S.z = S.u * S.w ^ 3 := by
  suffices hh : λ ^ (3 * S.multiplicity - 2) * S.x * λ * S.y * λ * S.z =
      S.u * λ ^ (3 * S.multiplicity) * S.w ^ 3 by
    rw [show λ ^ (3 * multiplicity S - 2) * x S * λ * y S * λ * z S =
      λ ^ (3 * multiplicity S - 2) * λ * λ * x S * y S * z S by ring] at hh
    have := S.two_le_multiplicity
    rw [mul_comm _ (λ ^ (3 * multiplicity S)), ← pow_succ, ← pow_succ,
      show 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S by omega, mul_assoc, mul_assoc,
      mul_assoc] at hh
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.zeta_sub_one_prime'.ne_zero, ne_eq,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or, false_and, or_false] at hh
    convert hh using 1
    ring
  simp only [← x_spec, mul_assoc, ← y_spec, ← z_spec]
  simp only [mul_comm 3, pow_mul, ← mul_pow, ← w_spec]
  rw [← S.H, a_cube_add_b_cube_eq_mul]
  ring

private lemma exists_cube_associated :
    (∃ X, Associated (X ^ 3) S.x) ∧ (∃ Y, Associated (Y ^ 3) S.y) ∧
      ∃ Z, Associated (Z ^ 3) S.z := by
  have h₁ := S.isCoprime_x_z.mul_left S.isCoprime_y_z
  have h₂ : Associated (S.w ^ 3) (S.x * S.y * S.z) :=
    ⟨S.u, by rw [x_mul_y_mul_z_eq_u_mul_w_cube S, mul_comm]⟩
  obtain ⟨T, h₃⟩ := exists_associated_pow_of_associated_mul_pow h₁ h₂
  exact ⟨exists_associated_pow_of_associated_mul_pow S.isCoprime_x_y h₃,
    exists_associated_pow_of_associated_mul_pow S.isCoprime_x_y.symm (mul_comm _ S.x ▸ h₃),
    exists_associated_pow_of_associated_mul_pow h₁.symm (mul_comm _ S.z ▸ h₂)⟩

/-- Given `S : Solution`, we let `S.u₁` and `S.X` be any elements such that
`S.X ^ 3 * S.u₁ = S.x` -/
private noncomputable def X := (exists_cube_associated S).1.choose
private noncomputable def u₁ := (exists_cube_associated S).1.choose_spec.choose
private lemma X_u₁_spec : S.X ^ 3 * S.u₁ = S.x :=
  (exists_cube_associated S).1.choose_spec.choose_spec

/-- Given `S : Solution`, we let `S.u₂` and `S.Y` be any elements such that
`S.Y ^ 3 * S.u₂ = S.y` -/
private noncomputable def Y := (exists_cube_associated S).2.1.choose
private noncomputable def u₂ := (exists_cube_associated S).2.1.choose_spec.choose
private lemma Y_u₂_spec : S.Y ^ 3 * S.u₂ = S.y :=
  (exists_cube_associated S).2.1.choose_spec.choose_spec

/-- Given `S : Solution`, we let `S.u₃` and `S.Z` be any elements such that
`S.Z ^ 3 * S.u₃ = S.z` -/
private noncomputable def Z := (exists_cube_associated S).2.2.choose
private noncomputable def u₃ :=(exists_cube_associated S).2.2.choose_spec.choose
private lemma Z_u₃_spec : S.Z ^ 3 * S.u₃ = S.z :=
  (exists_cube_associated S).2.2.choose_spec.choose_spec

end Solution

end FermatLastTheoremForThreeGen

end eisenstein

end case2
