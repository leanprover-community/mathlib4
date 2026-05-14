/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda,
  Lorenzo Luccioli, Pietro Monticone, Alexis Saurin, Florent Schaffhauser
-/
module

public import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Divisibility.Lemmas
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.ArithMult.Init
import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Fermat Last Theorem in the case `n = 3`
The goal of this file is to prove Fermat's Last Theorem in the case `n = 3`.

## Main results
* `fermatLastTheoremThree`: Fermat's Last Theorem for `n = 3`: if `a b c : ℕ` are all non-zero then
  `a ^ 3 + b ^ 3 ≠ c ^ 3`.

## Implementation details
We follow the proof in <https://webusers.imj-prg.fr/~marc.hindry/Cours-arith.pdf>, page 43.

The strategy is the following:
* The so-called "Case 1", when `3 ∣ a * b * c` is completely elementary and is proved using
  congruences modulo `9`.
* To prove case 2, we consider the generalized equation `a ^ 3 + b ^ 3 = u * c ^ 3`, where `a`, `b`,
  and `c` are in the cyclotomic ring `ℤ[ζ₃]` (where `ζ₃` is a primitive cube root of unity) and `u`
  is a unit of `ℤ[ζ₃]`. `FermatLastTheoremForThree_of_FermatLastTheoremThreeGen` (whose proof is
  rather elementary on paper) says that to prove Fermat's last theorem for exponent `3`, it is
  enough to prove that this equation has no solutions such that `c ≠ 0`, `¬ λ ∣ a`, `¬ λ ∣ b`,
  `λ ∣ c` and `IsCoprime a b` (where we set `λ := ζ₃ - 1`). We call such a tuple a `Solution'`.
  A `Solution` is the same as a `Solution'` with the additional assumption that `λ ^ 2 ∣ a + b`.
  We then prove that, given `S' : Solution'`, there is `S : Solution` such that the multiplicity of
  `λ = ζ₃ - 1` in `c` is the same in `S'` and `S` (see `exists_Solution_of_Solution'`).
  In particular it is enough to prove that no `Solution` exists. The key point is a descent argument
  on the multiplicity of `λ` in `c`: starting with `S : Solution` we can find `S₁ : Solution` with
  multiplicity strictly smaller (see `exists_Solution_multiplicity_lt`) and this finishes the proof.
  To construct `S₁` we go through a `Solution'` and then back to a `Solution`. More importantly, we
  cannot control the unit `u`, and this is the reason why we need to consider the generalized
  equation `a ^ 3 + b ^ 3 = u * c ^ 3`. The construction is completely explicit, but it depends
  crucially on `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`, a special
  case of Kummer's lemma.
* Note that we don't prove Case 1 for the generalized equation (in particular we don't prove that
  the generalized equation has no nontrivial solutions). This is because the proof, even if
  elementary on paper, would be quite annoying to formalize: indeed it involves a lot of explicit
  computations in `ℤ[ζ₃] / (λ)`: this ring is isomorphic to `ℤ / 9ℤ`, but of course, even if we
  construct such an isomorphism, tactics like `decide` would not work.

-/

section case1

open ZMod

lemma cube_of_castHom_ne_zero {n : ZMod 9} :
    castHom (show 3 ∣ 9 by simp) (ZMod 3) n ≠ 0 → n ^ 3 = 1 ∨ n ^ 3 = 8 := by
  revert n; decide

lemma cube_of_not_dvd {n : ℤ} (h : ¬ 3 ∣ n) :
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

lemma three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : ℤ} (ha : a ≠ 0)
    (Hgcd : Finset.gcd {a, b, c} id = 1) (h3a : 3 ∣ a) (HF : a ^ 3 + b ^ 3 + c ^ 3 = 0)
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    3 ∣ b := by
  have hbc : IsCoprime (-b) (-c) := by
    refine IsCoprime.neg_neg ?_
    rw [add_comm (a ^ 3), add_assoc, add_comm (a ^ 3), ← add_assoc] at HF
    refine isCoprime_of_gcd_eq_one_of_FLT ?_ HF
    convert Hgcd using 2
    rw [Finset.pair_comm, Finset.insert_comm]
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
lemma fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 {a b c : ℤ} (ha : a ≠ 0)
    (h3a : 3 ∣ a) (Hgcd : Finset.gcd {a, b, c} id = 1)
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    a ^ 3 + b ^ 3 + c ^ 3 ≠ 0 := by
  intro HF
  apply (show ¬(3 ∣ (1 : ℤ)) by decide)
  rw [← Hgcd]
  refine dvd_gcd (fun x hx ↦ ?_)
  simp only [mem_insert, mem_singleton] at hx
  have h3b : 3 ∣ b := by
    refine three_dvd_b_of_dvd_a_of_gcd_eq_one_of_case2 ha ?_ h3a HF H
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← Int.abs_eq_normalize]
  rcases hx with hx | hx | hx
  · exact hx ▸ h3a
  · exact hx ▸ h3b
  · simpa [hx] using dvd_c_of_prime_of_dvd_a_of_dvd_b_of_FLT Int.prime_three h3a h3b HF

open Finset Int in
/--
To prove Fermat's Last Theorem for `n = 3`, it is enough to show that for all `a`, `b`, `c`
in `ℤ` such that `c ≠ 0`, `¬ 3 ∣ a`, `¬ 3 ∣ b`, `a` and `b` are coprime and `3 ∣ c`, we have
`a ^ 3 + b ^ 3 ≠ c ^ 3`.
-/
theorem fermatLastTheoremThree_of_three_dvd_only_c
    (H : ∀ a b c : ℤ, c ≠ 0 → ¬ 3 ∣ a → ¬ 3 ∣ b → 3 ∣ c → IsCoprime a b → a ^ 3 + b ^ 3 ≠ c ^ 3) :
    FermatLastTheoremFor 3 := by
  rw [fermatLastTheoremFor_iff_int]
  refine fermatLastTheoremWith_of_fermatLastTheoremWith_coprime (fun a b c ha hb hc Hgcd hF ↦ ?_)
  by_cases h1 : 3 ∣ a * b * c
  swap
  · exact fermatLastTheoremThree_case_1 h1 hF
  rw [prime_three.dvd_mul, prime_three.dvd_mul] at h1
  rw [← sub_eq_zero, sub_eq_add_neg, ← (show Odd 3 by decide).neg_pow] at hF
  rcases h1 with (h3a | h3b) | h3c
  · refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 ha h3a ?_ H hF
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm (a ^ 3)] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 hb h3b ?_ H hF
    simp only [← Hgcd, insert_comm, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]
  · rw [add_comm _ ((-c) ^ 3), ← add_assoc] at hF
    refine fermatLastTheoremThree_of_dvd_a_of_gcd_eq_one_of_case2 (neg_ne_zero.2 hc) (by simp [h3c])
      ?_ H hF
    rw [Finset.insert_comm (-c), Finset.pair_comm (-c) b]
    simp only [← Hgcd, gcd_insert, gcd_singleton, id_eq, ← abs_eq_normalize, abs_neg]

section eisenstein

open NumberField IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

/-- `FermatLastTheoremForThreeGen` is the statement that `a ^ 3 + b ^ 3 = u * c ^ 3` has no
nontrivial solutions in `𝓞 K` for all `u : (𝓞 K)ˣ` such that `¬ λ ∣ a`, `¬ λ ∣ b` and `λ ∣ c`.
The reason to consider `FermatLastTheoremForThreeGen` is to make a descent argument working. -/
def FermatLastTheoremForThreeGen : Prop :=
  ∀ a b c : 𝓞 K, ∀ u : (𝓞 K)ˣ, c ≠ 0 → ¬ λ ∣ a → ¬ λ ∣ b → λ ∣ c → IsCoprime a b →
    a ^ 3 + b ^ 3 ≠ u * c ^ 3

/-- To prove `FermatLastTheoremFor 3`, it is enough to prove `FermatLastTheoremForThreeGen`. -/
lemma FermatLastTheoremForThree_of_FermatLastTheoremThreeGen
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    FermatLastTheoremForThreeGen hζ → FermatLastTheoremFor 3 := by
  intro H
  refine fermatLastTheoremThree_of_three_dvd_only_c (fun a b c hc ha hb ⟨x, hx⟩ hcoprime h ↦ ?_)
  refine H a b c 1 (by simp [hc]) (fun hdvd ↦ ha ?_) (fun hdvd ↦ hb ?_) ?_ ?_ ?_
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · rwa [← Ideal.norm_dvd_iff (hζ.prime_norm_toInteger_sub_one_of_prime_ne_two' (by decide)),
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)] at hdvd
  · exact dvd_trans hζ.toInteger_sub_one_dvd_prime' ⟨x, by simp [hx]⟩
  · exact IsCoprime.intCast hcoprime
  · simpa using mod_cast h

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
variable (S : Solution hζ) (S' : Solution' hζ)

section IsCyclotomicExtension

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- For any `S' : Solution'`, the multiplicity of `λ` in `S'.c` is finite. -/
lemma Solution'.multiplicity_lambda_c_finite :
    FiniteMultiplicity (hζ.toInteger - 1) S'.c :=
  .of_not_isUnit hζ.zeta_sub_one_prime'.not_unit S'.hc

/-- Given `S' : Solution'`, `S'.multiplicity` is the multiplicity of `λ` in `S'.c`, as a natural
number. -/
noncomputable def Solution'.multiplicity :=
  _root_.multiplicity (hζ.toInteger - 1) S'.c

/-- Given `S : Solution`, `S.multiplicity` is the multiplicity of `λ` in `S.c`, as a natural
number. -/
noncomputable def Solution.multiplicity := S.toSolution'.multiplicity

/-- We say that `S : Solution` is minimal if for all `S₁ : Solution`, the multiplicity of `λ` in
`S.c` is less or equal than the multiplicity in `S₁.c`. -/
def Solution.isMinimal : Prop := ∀ (S₁ : Solution hζ), S.multiplicity ≤ S₁.multiplicity

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
include S in
/-- If there is a solution then there is a minimal one. -/
lemma Solution.exists_minimal : ∃ (S₁ : Solution hζ), S₁.isMinimal := by
  classical
  let T := {n | ∃ (S' : Solution hζ), S'.multiplicity = n}
  rcases Nat.find_spec (⟨S.multiplicity, ⟨S, rfl⟩⟩ : T.Nonempty) with ⟨S₁, hS₁⟩
  exact ⟨S₁, fun S'' ↦ hS₁ ▸ Nat.find_min' _ ⟨S'', rfl⟩⟩

/-- Given `S' : Solution'`, then `S'.a` and `S'.b` are both congruent to `1` modulo `λ ^ 4` or are
both congruent to `-1`. -/
lemma a_cube_b_cube_congr_one_or_neg_one :
    λ ^ 4 ∣ S'.a ^ 3 - 1 ∧ λ ^ 4 ∣ S'.b ^ 3 + 1 ∨ λ ^ 4 ∣ S'.a ^ 3 + 1 ∧ λ ^ 4 ∣ S'.b ^ 3 - 1 := by
  obtain ⟨z, hz⟩ := S'.hcdvd
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.ha with
    ⟨x, hx⟩ | ⟨x, hx⟩ <;>
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S'.hb with
    ⟨y, hy⟩ | ⟨y, hy⟩
  · exfalso
    replace hζ : IsPrimitiveRoot ζ (3 ^ 1) := by rwa [pow_one]
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
    replace hζ : IsPrimitiveRoot ζ (3 ^ 1) := by rwa [pow_one]
    refine hζ.toInteger_sub_one_not_dvd_two (by decide) ⟨λ ^ 3 * (x + y) - S'.u * λ ^ 2 * z ^ 3, ?_⟩
    symm
    calc _ = λ ^ 4 * x + λ ^ 4 * y - S'.u * (λ * z) ^ 3 := by ring
    _ = (S'.a ^ 3 + 1) + (S'.b ^ 3 + 1) - (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy, ← hz, ← S'.H]
    _ = 2 := by ring

/-- Given `S' : Solution'`, we have that `λ ^ 4` divides `S'.c ^ 3`. -/
lemma lambda_pow_four_dvd_c_cube : λ ^ 4 ∣ S'.c ^ 3 := by
  rcases a_cube_b_cube_congr_one_or_neg_one S' with
    ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ <;>
  · refine ⟨S'.u⁻¹ * (x + y), ?_⟩
    symm
    calc _ = S'.u⁻¹ * (λ ^ 4 * x + λ ^ 4 * y) := by ring
    _ = S'.u⁻¹ * (S'.a ^ 3 + S'.b ^ 3) := by rw [← hx, ← hy]; ring
    _ = S'.u⁻¹ * (S'.u * S'.c ^ 3) := by rw [S'.H]
    _ = S'.c ^ 3 := by simp

/-- Given `S' : Solution'`, we have that `λ ^ 2` divides `S'.c`. -/
lemma lambda_sq_dvd_c : λ ^ 2 ∣ S'.c := by
  have hm := S'.multiplicity_lambda_c_finite
  have := lambda_pow_four_dvd_c_cube S'
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_pow hζ.zeta_sub_one_prime',
    hm.emultiplicity_eq_multiplicity] at this
  norm_cast at this
  exact (FiniteMultiplicity.pow_dvd_iff_le_multiplicity hm).mpr (by lia)

/-- Given `S' : Solution'`, we have that `2 ≤ S'.multiplicity`. -/
lemma Solution'.two_le_multiplicity : 2 ≤ S'.multiplicity := by
  simpa [Solution'.multiplicity] using
    S'.multiplicity_lambda_c_finite.le_multiplicity_of_pow_dvd (lambda_sq_dvd_c S')

/-- Given `S : Solution`, we have that `2 ≤ S.multiplicity`. -/
lemma Solution.two_le_multiplicity : 2 ≤ S.multiplicity :=
  S.toSolution'.two_le_multiplicity

end IsCyclotomicExtension

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
/-- Given `S' : Solution'`, the key factorization of `S'.a ^ 3 + S'.b ^ 3`. -/
lemma a_cube_add_b_cube_eq_mul :
    S'.a ^ 3 + S'.b ^ 3 = (S'.a + S'.b) * (S'.a + η * S'.b) * (S'.a + η ^ 2 * S'.b) := by
  symm
  calc _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+η^3)+η^3*S'.b^3 := by ring
  _ = S'.a^3+S'.a^2*S'.b*(η^2+η+1)+S'.a*S'.b^2*(η^2+η+1)+S'.b^3 := by
    simp [hζ.toInteger_cube_eq_one]
  _ = S'.a ^ 3 + S'.b ^ 3 := by rw [eta_sq]; ring

section IsCyclotomicExtension
variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- Given `S' : Solution'`, we have that `λ ^ 2` divides one amongst `S'.a + S'.b`,
`S'.a + η * S'.b` and `S'.a + η ^ 2 * S'.b`. -/
lemma lambda_sq_dvd_or_dvd_or_dvd :
    λ ^ 2 ∣ S'.a + S'.b ∨ λ ^ 2 ∣ S'.a + η * S'.b ∨ λ ^ 2 ∣ S'.a + η ^ 2 * S'.b := by
  by_contra! ⟨h1, h2, h3⟩
  rw [← emultiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + S'.b) :=
    finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht ↦ by simp [ht] at h1)
  have h2' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + η * S'.b) := by
    refine finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht ↦ ?_)
    rw [coe_eta] at ht
    simp [ht] at h2
  have h3' : FiniteMultiplicity (hζ.toInteger - 1) (S'.a + η ^ 2 * S'.b) := by
    refine finiteMultiplicity_iff_emultiplicity_ne_top.2 (fun ht ↦ ?_)
    rw [coe_eta] at ht
    simp [ht] at h3
  rw [h1'.emultiplicity_eq_multiplicity, Nat.cast_lt] at h1
  rw [h2'.emultiplicity_eq_multiplicity, Nat.cast_lt] at h2
  rw [h3'.emultiplicity_eq_multiplicity, Nat.cast_lt] at h3
  have := (pow_dvd_pow_of_dvd (lambda_sq_dvd_c S') 3).mul_left S'.u
  rw [← pow_mul, ← S'.H, a_cube_add_b_cube_eq_mul, pow_dvd_iff_le_emultiplicity,
    emultiplicity_mul hζ.zeta_sub_one_prime', emultiplicity_mul hζ.zeta_sub_one_prime',
      h1'.emultiplicity_eq_multiplicity, h2'.emultiplicity_eq_multiplicity,
      h3'.emultiplicity_eq_multiplicity, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_le] at this
  lia

open Units in
/-- Given `S' : Solution'`, we may assume that `λ ^ 2` divides `S'.a + S'.b ∨ λ ^ 2` (see also the
result below). -/
lemma ex_cube_add_cube_eq_and_isCoprime_and_not_dvd_and_dvd :
    ∃ (a' b' : 𝓞 K), a' ^ 3 + b' ^ 3 = S'.u * S'.c ^ 3 ∧ IsCoprime a' b' ∧ ¬ λ ∣ a' ∧
      ¬ λ ∣ b' ∧ λ ^ 2 ∣ a' + b' := by
  rcases lambda_sq_dvd_or_dvd_or_dvd S' with h | h | h
  · exact ⟨S'.a, S'.b, S'.H, S'.coprime, S'.ha, S'.hb, h⟩
  · refine ⟨S'.a, η * S'.b, ?_, ?_, S'.ha, fun ⟨x, hx⟩ ↦ S'.hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · simp [mul_pow, hζ.toInteger_cube_eq_one, one_mul, S'.H]
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

end IsCyclotomicExtension

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

section IsCyclotomicExtension

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

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
    show λ ^ 2 * k' - S.b + η ^ 2 * S.b = λ * (S.b * (η + 1) + λ * k') by rw [coe_eta]; ring,
    pow_two, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, hζ.zeta_sub_one_prime'.ne_zero, or_false] at hk
  apply_fun (· * -↑η) at hk
  rw [show (S.b * (η + 1) + λ * k') * -η = (-S.b) * (η ^ 2 + η + 1 - 1) - η * λ * k' by ring,
    eta_sq, show -S.b * (-↑η - 1 + ↑η + 1 - 1) = S.b by ring, sub_eq_iff_eq_add] at hk
  rw [hk]
  ring

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
  rw [← one_mul S.a] at hpaηb
  rw [← one_mul S.a] at hpaηsqb
  have := dvd_mul_sub_mul_mul_gcd_of_dvd hpaηb hpaηsqb
  rw [one_mul, mul_one, IsUnit.dvd_mul_right <| (gcd_isUnit_iff _ _).2 S.coprime] at this
  convert (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left this η) η) using 1
  symm
  calc _ = (-η.1 - 1 - η) * (-η - 1) := by rw [eta_sq, mul_assoc, ← pow_two, eta_sq]
  _ = 2 * η.1 ^ 2 + 3 * η + 1 := by ring
  _ = λ := by rw [eta_sq, coe_eta]; ring

end IsCyclotomicExtension

/-- Given `S : Solution`, we let `S.y` be any element such that `S.a + η * S.b = λ * S.y` -/
noncomputable def y := (lambda_dvd_a_add_eta_mul_b S).choose
lemma y_spec : S.a + η * S.b = λ * S.y :=
  (lambda_dvd_a_add_eta_mul_b S).choose_spec

/-- Given `S : Solution`, we let `S.z` be any element such that `S.a + η ^ 2 * S.b = λ * S.z` -/
noncomputable def z := (lambda_dvd_a_add_eta_sq_mul_b S).choose
lemma z_spec : S.a + η ^ 2 * S.b = λ * S.z :=
  (lambda_dvd_a_add_eta_sq_mul_b S).choose_spec

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

lemma lambda_not_dvd_y : ¬ λ ∣ S.y := fun h ↦ by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta, ← y_spec, ← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_mul_b _ h

lemma lambda_not_dvd_z : ¬ λ ∣ S.z := fun h ↦ by
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta, ← z_spec, ← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_sq_mul_b _ h

/-- We have that `λ ^ (3*S.multiplicity-2)` divides `S.a + S.b`. -/
lemma lambda_pow_dvd_a_add_b : λ ^ (3 * S.multiplicity - 2) ∣ S.a + S.b := by
  have h : λ ^ S.multiplicity ∣ S.c := pow_multiplicity_dvd _ _
  replace h : (λ ^ multiplicity S) ^ 3 ∣ S.u * S.c ^ 3 := by simp [h]
  rw [← S.H, a_cube_add_b_cube_eq_mul, ← pow_mul, mul_comm, y_spec, z_spec] at h
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_z
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_y
  have := S.two_le_multiplicity
  rw [show 3 * multiplicity S = 3 * multiplicity S - 2 + 1 + 1 by lia, pow_succ, pow_succ,
    show (S.a + S.b) * (λ * y S) * (λ * z S) = (S.a + S.b) * y S * z S * λ * λ by ring] at h
  simp only [mul_dvd_mul_iff_right hζ.zeta_sub_one_prime'.ne_zero] at h
  rwa [show (S.a + S.b) * y S * z S = y S * (z S * (S.a + S.b)) by ring] at h

/-- Given `S : Solution`, we let `S.x` be any element such that
`S.a + S.b = λ ^ (3*S.multiplicity-2) * S.x` -/
noncomputable def x := (lambda_pow_dvd_a_add_b S).choose
lemma x_spec : S.a + S.b = λ ^ (3 * S.multiplicity - 2) * S.x :=
  (lambda_pow_dvd_a_add_b S).choose_spec

/-- Given `S : Solution`, we let `S.w` be any element such that `S.c = λ ^ S.multiplicity * S.w` -/
noncomputable def w :=
  (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
lemma w_spec : S.c = λ ^ S.multiplicity * S.w :=
  (pow_multiplicity_dvd (hζ.toInteger - 1) S.c).choose_spec

lemma lambda_not_dvd_w : ¬ λ ∣ S.w := fun h ↦ by
  refine S.toSolution'.multiplicity_lambda_c_finite.not_pow_dvd_of_multiplicity_lt
    (lt_add_one S.multiplicity) ?_
  rw [pow_succ', mul_comm]
  exact S.w_spec ▸ (mul_dvd_mul_left (λ ^ S.multiplicity) h)

lemma lambda_not_dvd_x : ¬ λ ∣ S.x := fun h ↦ by
  replace h := mul_dvd_mul_left (λ ^ (3 * S.multiplicity - 2)) h
  rw [mul_comm, ← x_spec] at h
  replace h :=
    mul_dvd_mul (mul_dvd_mul h S.lambda_dvd_a_add_eta_mul_b) S.lambda_dvd_a_add_eta_sq_mul_b
  simp only [← a_cube_add_b_cube_eq_mul, S.H, w_spec, Units.isUnit, IsUnit.dvd_mul_left] at h
  rw [← pow_succ', mul_comm, ← mul_assoc, ← pow_succ'] at h
  have := S.two_le_multiplicity
  rw [show 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S by lia, mul_pow, ← pow_mul,
    mul_comm _ 3, mul_dvd_mul_iff_left _] at h
  · exact lambda_not_dvd_w _ <| hζ.zeta_sub_one_prime'.dvd_of_dvd_pow h
  · simp [hζ.zeta_sub_one_prime'.ne_zero]

attribute [local instance] IsCyclotomicExtension.Rat.three_pid

lemma isCoprime_helper {r s t w : 𝓞 K} (hr : ¬ λ ∣ r) (hs : ¬ λ ∣ s)
    (Hp : ∀ {p}, Prime p → p ∣ t → p ∣ w → Associated p λ) (H₁ : ∀ {q}, q ∣ r → q ∣ t)
    (H₂ : ∀ {q}, q ∣ s → q ∣ w) : IsCoprime r s := by
  refine isCoprime_of_prime_dvd (not_and.2 (fun _ hz ↦ hs (by simp [hz])))
    (fun p hp p_dvd_r p_dvd_s ↦ hr ?_)
  rwa [← Associated.dvd_iff_dvd_left <| Hp hp (H₁ p_dvd_r) (H₂ p_dvd_s)]

lemma isCoprime_x_y : IsCoprime S.x S.y :=
  isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_y S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b S) (fun hq ↦ x_spec S ▸ hq.mul_left _)
      (fun hq ↦ y_spec S ▸ hq.mul_left _)

lemma isCoprime_x_z : IsCoprime S.x S.z :=
  isCoprime_helper (lambda_not_dvd_x S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b S) (fun hq ↦ x_spec S ▸ hq.mul_left _)
      (fun hq ↦ z_spec S ▸ hq.mul_left _)

lemma isCoprime_y_z : IsCoprime S.y S.z :=
  isCoprime_helper (lambda_not_dvd_y S) (lambda_not_dvd_z S)
    (associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b S)
    (fun hq ↦ y_spec S ▸ hq.mul_left _) (fun hq ↦ z_spec S ▸ hq.mul_left _)

lemma x_mul_y_mul_z_eq_u_mul_w_cube : S.x * S.y * S.z = S.u * S.w ^ 3 := by
  suffices hh : λ ^ (3 * S.multiplicity - 2) * S.x * λ * S.y * λ * S.z =
      S.u * λ ^ (3 * S.multiplicity) * S.w ^ 3 by
    rw [show λ ^ (3 * multiplicity S - 2) * x S * λ * y S * λ * z S =
      λ ^ (3 * multiplicity S - 2) * λ * λ * x S * y S * z S by ring] at hh
    have := S.two_le_multiplicity
    rw [mul_comm _ (λ ^ (3 * multiplicity S)), ← pow_succ, ← pow_succ,
      show 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S by lia, mul_assoc, mul_assoc,
      mul_assoc] at hh
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.zeta_sub_one_prime'.ne_zero, ne_eq,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or, false_and, or_false] at hh
    convert hh using 1
    ring
  simp only [← x_spec, mul_assoc, ← y_spec, ← z_spec]
  rw [mul_comm 3, pow_mul, ← mul_pow, ← w_spec, ← S.H, a_cube_add_b_cube_eq_mul]
  ring

lemma exists_cube_associated :
    (∃ X, Associated (X ^ 3) S.x) ∧ (∃ Y, Associated (Y ^ 3) S.y) ∧
      ∃ Z, Associated (Z ^ 3) S.z := by classical
  have h₁ := S.isCoprime_x_z.mul_left S.isCoprime_y_z
  have h₂ : Associated (S.w ^ 3) (S.x * S.y * S.z) :=
    ⟨S.u, by rw [x_mul_y_mul_z_eq_u_mul_w_cube S, mul_comm]⟩
  obtain ⟨T, h₃⟩ := exists_associated_pow_of_associated_pow_mul h₁ h₂
  exact ⟨exists_associated_pow_of_associated_pow_mul S.isCoprime_x_y h₃,
    exists_associated_pow_of_associated_pow_mul S.isCoprime_x_y.symm (mul_comm _ S.x ▸ h₃),
    exists_associated_pow_of_associated_pow_mul h₁.symm (mul_comm _ S.z ▸ h₂)⟩

/-- Given `S : Solution`, we let `S.u₁` and `S.X` be any elements such that
`S.X ^ 3 * S.u₁ = S.x` -/
noncomputable def X := (exists_cube_associated S).1.choose
noncomputable def u₁ := (exists_cube_associated S).1.choose_spec.choose
lemma X_u₁_spec : S.X ^ 3 * S.u₁ = S.x :=
  (exists_cube_associated S).1.choose_spec.choose_spec

/-- Given `S : Solution`, we let `S.u₂` and `S.Y` be any elements such that
`S.Y ^ 3 * S.u₂ = S.y` -/
noncomputable def Y := (exists_cube_associated S).2.1.choose
noncomputable def u₂ := (exists_cube_associated S).2.1.choose_spec.choose
lemma Y_u₂_spec : S.Y ^ 3 * S.u₂ = S.y :=
  (exists_cube_associated S).2.1.choose_spec.choose_spec

/-- Given `S : Solution`, we let `S.u₃` and `S.Z` be any elements such that
`S.Z ^ 3 * S.u₃ = S.z` -/
noncomputable def Z := (exists_cube_associated S).2.2.choose
noncomputable def u₃ := (exists_cube_associated S).2.2.choose_spec.choose
lemma Z_u₃_spec : S.Z ^ 3 * S.u₃ = S.z :=
  (exists_cube_associated S).2.2.choose_spec.choose_spec

lemma X_ne_zero : S.X ≠ 0 :=
  fun h ↦ lambda_not_dvd_x S <| by simp [← X_u₁_spec, h]

lemma lambda_not_dvd_X : ¬ λ ∣ S.X :=
  fun h ↦ lambda_not_dvd_x S <| X_u₁_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

lemma lambda_not_dvd_Y : ¬ λ ∣ S.Y :=
  fun h ↦ lambda_not_dvd_y S <| Y_u₂_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

lemma lambda_not_dvd_Z : ¬ λ ∣ S.Z :=
  fun h ↦ lambda_not_dvd_z S <| Z_u₃_spec S ▸ dvd_mul_of_dvd_left (dvd_pow h (by decide)) _

lemma isCoprime_Y_Z : IsCoprime S.Y S.Z := by
  rw [← IsCoprime.pow_iff (m := 3) (n := 3) (by decide) (by decide),
    ← isCoprime_mul_unit_right_left S.u₂.isUnit, ← isCoprime_mul_unit_right_right S.u₃.isUnit,
    Y_u₂_spec, Z_u₃_spec]
  exact isCoprime_y_z S

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
lemma formula1 : S.X^3*S.u₁*λ^(3*S.multiplicity-2)+S.Y^3*S.u₂*λ*η+S.Z^3*S.u₃*λ*η^2 = 0 := by
  rw [X_u₁_spec, Y_u₂_spec, Z_u₃_spec, mul_comm S.x, ← x_spec, mul_comm S.y, ← y_spec, mul_comm S.z,
    ← z_spec, eta_sq]
  calc _ = S.a+S.b+η^2*S.b-S.a+η^2*S.b+2*η*S.b+S.b := by ring
  _ = 0 := by rw [eta_sq]; ring

/-- Let `u₄ := η * S.u₃ * S.u₂⁻¹` -/
noncomputable def u₄ := η * S.u₃ * S.u₂⁻¹
lemma u₄_def : S.u₄ = η * S.u₃ * S.u₂⁻¹ := rfl
/-- Let `u₅ := -η ^ 2 * S.u₁ * S.u₂⁻¹` -/
noncomputable def u₅ := -η ^ 2 * S.u₁ * S.u₂⁻¹
lemma u₅_def : S.u₅ = -η ^ 2 * S.u₁ * S.u₂⁻¹ := rfl

example (a b : 𝓞 K) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  exact mul_ne_zero ha hb

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
lemma formula2 :
    S.Y ^ 3 + S.u₄ * S.Z ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  rw [u₅_def, neg_mul, neg_mul, Units.val_neg, neg_mul, eq_neg_iff_add_eq_zero, add_assoc,
    add_comm (S.u₄ * S.Z ^ 3), ← add_assoc, add_comm (S.Y ^ 3)]
  apply mul_right_cancel₀ <| mul_ne_zero
    (mul_ne_zero hζ.zeta_sub_one_prime'.ne_zero S.u₂.isUnit.ne_zero) (Units.isUnit η).ne_zero
  simp only [zero_mul, add_mul]
  rw [← formula1 S]
  congrm ?_ + ?_ + ?_
  · have : (S.multiplicity-1)*3+1 = 3*S.multiplicity-2 := by have := S.two_le_multiplicity; lia
    calc _ = S.X^3 *(S.u₂*S.u₂⁻¹)*(η^3*S.u₁)*(λ^((S.multiplicity-1)*3)*λ) := by push_cast; ring
    _ = S.X^3*S.u₁*λ^(3*S.multiplicity-2) := by simp [hζ.toInteger_cube_eq_one, ← pow_succ, this]
  · ring
  · simp only [u₄_def, inv_eq_one_div, mul_div_assoc', mul_one, val_div_eq_divp, Units.val_mul,
      IsUnit.unit_spec, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]
    ring

-- This is just a computation and the formulas are too long.
set_option linter.style.whitespace false in
lemma lambda_sq_div_u₅_mul : λ ^ 2 ∣ S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  use λ^(3*S.multiplicity-5)*S.u₅*(S.X^3)
  have : 3*(S.multiplicity-1) = 2+(3*S.multiplicity-5) := by have := S.two_le_multiplicity; lia
  calc _ = λ^(3*(S.multiplicity-1))*S.u₅*S.X^3 := by ring
  _ = λ^2*λ^(3*S.multiplicity-5)*S.u₅*S.X^3 := by rw [this, pow_add]
  _ = λ^2*(λ^(3*S.multiplicity-5)*S.u₅*S.X^3) := by ring

lemma u₄_eq_one_or_neg_one : S.u₄ = 1 ∨ S.u₄ = -1 := by
  have : λ ^ 2 ∣ λ ^ 4 := ⟨λ ^ 2, by ring⟩
  have h := S.lambda_sq_div_u₅_mul
  apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hζ
  rcases h with ⟨X, hX⟩
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S.lambda_not_dvd_Y with
    HY | HY <;> rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd
      hζ S.lambda_not_dvd_Z with HZ | HZ <;> replace HY := this.trans HY <;> replace HZ :=
      this.trans HZ <;> rcases HY with ⟨Y, hY⟩ <;> rcases HZ with ⟨Z, hZ⟩
  · refine ⟨-1, X - Y - S.u₄ * Z, ?_⟩
    rw [show λ ^ 2 * (X - Y - S.u₄ * Z) = λ ^ 2 * X - λ ^ 2 * Y - S.u₄ * (λ ^ 2 * Z) by ring,
      ← hX, ← hY, ← hZ, ← formula2]
    ring
  · refine ⟨1, -X + Y + S.u₄ * Z, ?_⟩
    rw [show λ ^ 2 * (-X + Y + S.u₄ * Z) = -(λ ^ 2 * X - λ ^ 2 * Y - S.u₄ * (λ ^ 2 * Z)) by ring,
      ← hX, ← hY, ← hZ, ← formula2]
    ring
  · refine ⟨1, X - Y - S.u₄ * Z, ?_⟩
    rw [show λ ^ 2 * (X - Y - S.u₄ * Z) = λ ^ 2 * X - λ ^ 2 * Y - S.u₄ * (λ ^ 2 * Z) by ring,
      ← hX, ← hY, ← hZ, ← formula2]
    ring
  · refine ⟨-1, -X + Y + S.u₄ * Z, ?_⟩
    rw [show λ ^ 2 * (-X + Y + S.u₄ * Z) = -(λ ^ 2 * X - λ ^ 2 * Y - S.u₄ * (λ ^ 2 * Z)) by ring,
      ← hX, ← hY, ← hZ, ← formula2]
    ring

lemma u₄_sq : S.u₄ ^ 2 = 1 := by
  rcases S.u₄_eq_one_or_neg_one with h | h <;> simp [h]

/-- Given `S : Solution`, we have that
`S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3`. -/
lemma formula3 :
    S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 :=
  calc S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.Y ^ 3 + S.u₄ ^ 2 * S.u₄ * S.Z ^ 3 := by ring
  _ = S.Y ^ 3 + S.u₄ * S.Z ^ 3 := by simp [← Units.val_pow_eq_pow_val, S.u₄_sq]
  _ = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 := S.formula2

/-- Given `S : Solution`, we construct `S₁ : Solution'`, with smaller multiplicity of `λ` in
  `c` (see `Solution'_descent_multiplicity_lt` below.). -/
noncomputable def Solution'_descent : Solution' hζ where
  a := S.Y
  b := S.u₄ * S.Z
  c := λ ^ (S.multiplicity - 1) * S.X
  u := S.u₅
  ha := S.lambda_not_dvd_Y
  hb := fun h ↦ S.lambda_not_dvd_Z <| Units.dvd_mul_left.1 h
  hc := fun h ↦ S.X_ne_zero <| by simpa [hζ.zeta_sub_one_prime'.ne_zero] using h
  coprime := (isCoprime_mul_unit_left_right S.u₄.isUnit _ _).2 S.isCoprime_Y_Z
  hcdvd := by
    refine dvd_mul_of_dvd_left (dvd_pow_self _ (fun h ↦ ?_)) _
    rw [Nat.sub_eq_iff_eq_add (le_trans (by simp) S.two_le_multiplicity), zero_add] at h
    simpa [h] using S.two_le_multiplicity
  H := formula3 S

/-- We have that `S.Solution'_descent.multiplicity = S.multiplicity - 1`. -/
lemma Solution'_descent_multiplicity : S.Solution'_descent.multiplicity = S.multiplicity - 1 := by
  refine multiplicity_eq_of_dvd_of_not_dvd
    (by simp [Solution'_descent]) (fun h ↦ S.lambda_not_dvd_X ?_)
  obtain ⟨k, hk : λ ^ (S.multiplicity - 1) * S.X = λ ^ (S.multiplicity - 1 + 1) * k⟩ := h
  rw [pow_succ, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.zeta_sub_one_prime'.ne_zero, ne_eq,
    false_and, or_false] at hk
  simp [hk]

/-- We have that `S.Solution'_descent.multiplicity < S.multiplicity`. -/
lemma Solution'_descent_multiplicity_lt :
    (Solution'_descent S).multiplicity < S.multiplicity := by
  rw [Solution'_descent_multiplicity S, Nat.sub_one]
  exact Nat.pred_lt <| by have := S.two_le_multiplicity; lia

/-- Given any `S : Solution`, there is another `S₁ : Solution` such that
  `S₁.multiplicity < S.multiplicity` -/
theorem exists_Solution_multiplicity_lt :
    ∃ S₁ : Solution hζ, S₁.multiplicity < S.multiplicity := by classical
  obtain ⟨S', hS'⟩ := exists_Solution_of_Solution' (Solution'_descent S)
  exact ⟨S', hS' ▸ Solution'_descent_multiplicity_lt S⟩

end Solution

end FermatLastTheoremForThreeGen

end eisenstein

end case2

set_option backward.isDefEq.respectTransparency false in
/-- Fermat's Last Theorem for `n = 3`: if `a b c : ℕ` are all non-zero then
`a ^ 3 + b ^ 3 ≠ c ^ 3`. -/
public theorem fermatLastTheoremThree : FermatLastTheoremFor 3 := by
  classical
  let K := CyclotomicField 3 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have : NumberField K := IsCyclotomicExtension.numberField {3} ℚ _
  apply FermatLastTheoremForThree_of_FermatLastTheoremThreeGen hζ
  intro a b c u hc ha hb hcdvd coprime H
  let S' : FermatLastTheoremForThreeGen.Solution' hζ :=
  { a := a
    b := b
    c := c
    u := u
    ha := ha
    hb := hb
    hc := hc
    coprime := coprime
    hcdvd := hcdvd
    H := H }
  obtain ⟨S, -⟩ := FermatLastTheoremForThreeGen.exists_Solution_of_Solution' S'
  obtain ⟨Smin, hSmin⟩ := S.exists_minimal
  obtain ⟨Sfin, hSfin⟩ := Smin.exists_Solution_multiplicity_lt
  linarith [hSmin Sfin]
