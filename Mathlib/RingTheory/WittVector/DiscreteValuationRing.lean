/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth, Johan Commelin
-/
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.MulCoeff
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.LinearCombination

#align_import ring_theory.witt_vector.discrete_valuation_ring from "leanprover-community/mathlib"@"c163ec99dfc664628ca15d215fce0a5b9c265b68"

/-!

# Witt vectors over a perfect ring

This file establishes that Witt vectors over a perfect field are a discrete valuation ring.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `WittVector.exists_eq_pow_p_mul`: the existence of this element `b` over a perfect ring
* `WittVector.exists_eq_pow_p_mul'`: the existence of this unit `b` over a perfect field
* `WittVector.discreteValuationRing`: `𝕎 k` is a discrete valuation ring if `k` is a perfect field

-/


noncomputable section

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

section CommRing

variable {k : Type*} [CommRing k] [CharP k p]

/-- This is the `n+1`st coefficient of our inverse. -/
def succNthValUnits (n : ℕ) (a : Units k) (A : 𝕎 k) (bs : Fin (n + 1) → k) : k :=
  -↑(a⁻¹ ^ p ^ (n + 1)) *
    (A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) + nthRemainder p n (truncateFun (n + 1) A) bs)
#align witt_vector.succ_nth_val_units WittVector.succNthValUnits

/--
Recursively defines the sequence of coefficients for the inverse to a Witt vector whose first entry
is a unit.
-/
noncomputable def inverseCoeff (a : Units k) (A : 𝕎 k) : ℕ → k
  | 0 => ↑a⁻¹
  | n + 1 => succNthValUnits n a A fun i => inverseCoeff a A i.val
#align witt_vector.inverse_coeff WittVector.inverseCoeff

/--
Upgrade a Witt vector `A` whose first entry `A.coeff 0` is a unit to be, itself, a unit in `𝕎 k`.
-/
def mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k) :=
  Units.mkOfMulEqOne A (@WittVector.mk' p _ (inverseCoeff a A)) (by
    ext n
    -- ⊢ coeff (A * { coeff := inverseCoeff a A }) n = coeff 1 n
    induction' n with n _
    -- ⊢ coeff (A * { coeff := inverseCoeff a A }) Nat.zero = coeff 1 Nat.zero
    · simp [WittVector.mul_coeff_zero, inverseCoeff, hA]
      -- 🎉 no goals
    let H_coeff := A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
      nthRemainder p n (truncateFun (n + 1) A) fun i : Fin (n + 1) => inverseCoeff a A i
    have H := Units.mul_inv (a ^ p ^ (n + 1))
    -- ⊢ coeff (A * { coeff := inverseCoeff a A }) (Nat.succ n) = coeff 1 (Nat.succ n)
    linear_combination (norm := skip) -H_coeff * H
    -- ⊢ coeff (A * { coeff := inverseCoeff a A }) (Nat.succ n) - coeff 1 (Nat.succ n …
    have ha : (a : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1)) := by norm_cast
    -- ⊢ coeff (A * { coeff := inverseCoeff a A }) (Nat.succ n) - coeff 1 (Nat.succ n …
    have ha_inv : (↑a⁻¹ : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1))⁻¹ := by norm_cast; norm_num
    -- ⊢ coeff (A * { coeff := inverseCoeff a A }) (Nat.succ n) - coeff 1 (Nat.succ n …
    simp only [nthRemainder_spec, inverseCoeff, succNthValUnits, hA,
      one_coeff_eq_of_pos, Nat.succ_pos', ha_inv, ha, inv_pow]
    ring!)
    -- 🎉 no goals
#align witt_vector.mk_unit WittVector.mkUnit

@[simp]
theorem coe_mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mkUnit hA : 𝕎 k) = A :=
  rfl
#align witt_vector.coe_mk_unit WittVector.coe_mkUnit

end CommRing

section Field

variable {k : Type*} [Field k] [CharP k p]

theorem isUnit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 ≠ 0) : IsUnit x := by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  -- ⊢ IsUnit x
  have hy : x.coeff 0 = y := rfl
  -- ⊢ IsUnit x
  exact (mkUnit hy).isUnit
  -- 🎉 no goals
#align witt_vector.is_unit_of_coeff_zero_ne_zero WittVector.isUnit_of_coeff_zero_ne_zero

variable (p)

theorem irreducible : Irreducible (p : 𝕎 k) := by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [constantCoeff_apply, coeff_p_zero, not_isUnit_zero] using
      (constantCoeff : WittVector p k →+* _).isUnit_map hp
  refine' ⟨hp, fun a b hab => _⟩
  -- ⊢ IsUnit a ∨ IsUnit b
  obtain ⟨ha0, hb0⟩ : a ≠ 0 ∧ b ≠ 0 := by
    rw [← mul_ne_zero_iff]; intro h; rw [h] at hab; exact p_nonzero p k hab
  obtain ⟨m, a, ha, rfl⟩ := verschiebung_nonzero ha0
  -- ⊢ IsUnit ((↑verschiebung)^[m] a) ∨ IsUnit b
  obtain ⟨n, b, hb, rfl⟩ := verschiebung_nonzero hb0
  -- ⊢ IsUnit ((↑verschiebung)^[m] a) ∨ IsUnit ((↑verschiebung)^[n] b)
  cases m; · exact Or.inl (isUnit_of_coeff_zero_ne_zero a ha)
  -- ⊢ IsUnit ((↑verschiebung)^[Nat.zero] a) ∨ IsUnit ((↑verschiebung)^[n] b)
             -- 🎉 no goals
  cases' n with n; · exact Or.inr (isUnit_of_coeff_zero_ne_zero b hb)
  -- ⊢ IsUnit ((↑verschiebung)^[Nat.succ n✝] a) ∨ IsUnit ((↑verschiebung)^[Nat.zero …
                     -- 🎉 no goals
  rw [iterate_verschiebung_mul] at hab
  -- ⊢ IsUnit ((↑verschiebung)^[Nat.succ n✝] a) ∨ IsUnit ((↑verschiebung)^[Nat.succ …
  apply_fun fun x => coeff x 1 at hab
  -- ⊢ IsUnit ((↑verschiebung)^[Nat.succ n✝] a) ∨ IsUnit ((↑verschiebung)^[Nat.succ …
  simp only [coeff_p_one, Nat.add_succ, add_comm _ n, Function.iterate_succ', Function.comp_apply,
    verschiebung_coeff_add_one, verschiebung_coeff_zero] at hab
  exact (one_ne_zero hab).elim
  -- 🎉 no goals
#align witt_vector.irreducible WittVector.irreducible

end Field

section PerfectRing

variable {k : Type*} [CommRing k] [CharP k p] [PerfectRing k p]

theorem exists_eq_pow_p_mul (a : 𝕎 k) (ha : a ≠ 0) :
    ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  -- ⊢ ∃ m b, coeff b 0 ≠ 0 ∧ a = ↑p ^ m * b
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).surjective.iterate m c
  -- ⊢ ∃ m b, coeff b 0 ≠ 0 ∧ a = ↑p ^ m * b
  rw [WittVector.iterate_frobenius_coeff] at hc
  -- ⊢ ∃ m b, coeff b 0 ≠ 0 ∧ a = ↑p ^ m * b
  have := congr_fun (WittVector.verschiebung_frobenius_comm.comp_iterate m) b
  -- ⊢ ∃ m b, coeff b 0 ≠ 0 ∧ a = ↑p ^ m * b
  simp only [Function.comp_apply] at this
  -- ⊢ ∃ m b, coeff b 0 ≠ 0 ∧ a = ↑p ^ m * b
  rw [← this] at hcm
  -- ⊢ ∃ m b, coeff b 0 ≠ 0 ∧ a = ↑p ^ m * b
  refine' ⟨m, b, _, _⟩
  -- ⊢ coeff b 0 ≠ 0
  · contrapose! hc
    -- ⊢ coeff b 0 ^ p ^ m = 0
    have : 0 < p ^ m := pow_pos (Nat.Prime.pos Fact.out) _
    -- ⊢ coeff b 0 ^ p ^ m = 0
    simp [hc, zero_pow this]
    -- 🎉 no goals
  · simp_rw [← mul_left_iterate (p : 𝕎 k) m]
    -- ⊢ a = (fun x => ↑p * x)^[m] b
    convert hcm using 2
    -- ⊢ (fun x => ↑p * x) = ↑verschiebung ∘ ↑frobenius
    ext1 x
    -- ⊢ ↑p * x = (↑verschiebung ∘ ↑frobenius) x
    rw [mul_comm, ← WittVector.verschiebung_frobenius x]; rfl
    -- ⊢ ↑verschiebung (↑frobenius x) = (↑verschiebung ∘ ↑frobenius) x
                                                          -- 🎉 no goals
#align witt_vector.exists_eq_pow_p_mul WittVector.exists_eq_pow_p_mul

end PerfectRing

section PerfectField

variable {k : Type*} [Field k] [CharP k p] [PerfectRing k p]

theorem exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a ≠ 0) :
    ∃ (m : ℕ) (b : Units (𝕎 k)), a = (p : 𝕎 k) ^ m * b := by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  -- ⊢ ∃ m b, a = ↑p ^ m * ↑b
  let b₀ := Units.mk0 (b.coeff 0) h₁
  -- ⊢ ∃ m b, a = ↑p ^ m * ↑b
  have hb₀ : b.coeff 0 = b₀ := rfl
  -- ⊢ ∃ m b, a = ↑p ^ m * ↑b
  exact ⟨m, mkUnit hb₀, h₂⟩
  -- 🎉 no goals
#align witt_vector.exists_eq_pow_p_mul' WittVector.exists_eq_pow_p_mul'

/-
Note: The following lemma should be an instance, but it seems to cause some
exponential blowups in certain typeclass resolution problems.
See the following Lean4 issue as well as the zulip discussion linked there:
https://github.com/leanprover/lean4/issues/1102
-/
/-- The ring of Witt Vectors of a perfect field of positive characteristic is a DVR.
-/
theorem discreteValuationRing : DiscreteValuationRing (𝕎 k) :=
  DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization (by
    refine' ⟨p, irreducible p, fun {x} hx => _⟩
    -- ⊢ ∃ n, Associated (↑p ^ n) x
    obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
    -- ⊢ ∃ n, Associated (↑p ^ n) x
    exact ⟨n, b, hb.symm⟩)
    -- 🎉 no goals
#align witt_vector.discrete_valuation_ring WittVector.discreteValuationRing

end PerfectField

end WittVector
