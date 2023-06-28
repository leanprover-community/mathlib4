/-
Copyright (c) 2022 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Heather Macbeth, Johan Commelin

! This file was ported from Lean 3 source module ring_theory.witt_vector.discrete_valuation_ring
! leanprover-community/mathlib commit c163ec99dfc664628ca15d215fce0a5b9c265b68
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.RingTheory.WittVector.Domain
import Mathlib.RingTheory.WittVector.MulCoeff
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.LinearCombination

/-!

# Witt vectors over a perfect ring

This file establishes that Witt vectors over a perfect field are a discrete valuation ring.
When `k` is a perfect ring, a nonzero `a : 𝕎 k` can be written as `p^m * b` for some `m : ℕ` and
`b : 𝕎 k` with nonzero 0th coefficient.
When `k` is also a field, this `b` can be chosen to be a unit of `𝕎 k`.

## Main declarations

* `witt_vector.exists_eq_pow_p_mul`: the existence of this element `b` over a perfect ring
* `witt_vector.exists_eq_pow_p_mul'`: the existence of this unit `b` over a perfect field
* `witt_vector.discrete_valuation_ring`: `𝕎 k` is a discrete valuation ring if `k` is a perfect
    field

-/


noncomputable section

namespace WittVector

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝕎" => WittVector p

section CommRing

variable {k : Type _} [CommRing k] [CharP k p]

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
  | n + 1 => succNthValUnits n a A fun i => inverse_coeff i.val
decreasing_by apply Fin.is_lt
#align witt_vector.inverse_coeff WittVector.inverseCoeff

/--
Upgrade a Witt vector `A` whose first entry `A.coeff 0` is a unit to be, itself, a unit in `𝕎 k`.
-/
def mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : Units (𝕎 k) :=
  Units.mkOfMulEqOne A (WittVector.mk' p (inverseCoeff a A))
    (by
      ext n
      induction' n with n ih
      · simp [WittVector.mul_coeff_zero, inverse_coeff, hA]
      let H_coeff :=
        A.coeff (n + 1) * ↑(a⁻¹ ^ p ^ (n + 1)) +
          nth_remainder p n (truncate_fun (n + 1) A) fun i : Fin (n + 1) => inverse_coeff a A i
      have H := Units.mul_inv (a ^ p ^ (n + 1))
      linear_combination (norm := skip) -H_coeff * H
      have ha : (a : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1)) := by norm_cast
      have ha_inv : (↑a⁻¹ : k) ^ p ^ (n + 1) = ↑(a ^ p ^ (n + 1))⁻¹ := by exact_mod_cast inv_pow _ _
      simp only [nth_remainder_spec, inverse_coeff, succ_nth_val_units, hA, Fin.val_eq_coe,
        one_coeff_eq_of_pos, Nat.succ_pos', H_coeff, ha_inv, ha, inv_pow]
      ring!)
#align witt_vector.mk_unit WittVector.mkUnit

@[simp]
theorem coe_mkUnit {a : Units k} {A : 𝕎 k} (hA : A.coeff 0 = a) : (mkUnit hA : 𝕎 k) = A :=
  rfl
#align witt_vector.coe_mk_unit WittVector.coe_mkUnit

end CommRing

section Field

variable {k : Type _} [Field k] [CharP k p]

theorem isUnit_of_coeff_zero_ne_zero (x : 𝕎 k) (hx : x.coeff 0 ≠ 0) : IsUnit x := by
  let y : kˣ := Units.mk0 (x.coeff 0) hx
  have hy : x.coeff 0 = y := rfl
  exact (mk_unit hy).IsUnit
#align witt_vector.is_unit_of_coeff_zero_ne_zero WittVector.isUnit_of_coeff_zero_ne_zero

variable (p)

theorem irreducible : Irreducible (p : 𝕎 k) := by
  have hp : ¬IsUnit (p : 𝕎 k) := by
    intro hp
    simpa only [constant_coeff_apply, coeff_p_zero, not_isUnit_zero] using
      (constant_coeff : WittVector p k →+* _).isUnit_map hp
  refine' ⟨hp, fun a b hab => _⟩
  obtain ⟨ha0, hb0⟩ : a ≠ 0 ∧ b ≠ 0 := by rw [← mul_ne_zero_iff]; intro h; rw [h] at hab ;
    exact p_nonzero p k hab
  obtain ⟨m, a, ha, rfl⟩ := verschiebung_nonzero ha0
  obtain ⟨n, b, hb, rfl⟩ := verschiebung_nonzero hb0
  cases m; · exact Or.inl (is_unit_of_coeff_zero_ne_zero a ha)
  cases n; · exact Or.inr (is_unit_of_coeff_zero_ne_zero b hb)
  rw [iterate_verschiebung_mul] at hab 
  apply_fun fun x => coeff x 1 at hab 
  simp only [coeff_p_one, Nat.add_succ, add_comm _ n, Function.iterate_succ', Function.comp_apply,
    verschiebung_coeff_add_one, verschiebung_coeff_zero] at hab 
  exact (one_ne_zero hab).elim
#align witt_vector.irreducible WittVector.irreducible

end Field

section PerfectRing

variable {k : Type _} [CommRing k] [CharP k p] [PerfectRing k p]

theorem exists_eq_pow_p_mul (a : 𝕎 k) (ha : a ≠ 0) :
    ∃ (m : ℕ) (b : 𝕎 k), b.coeff 0 ≠ 0 ∧ a = p ^ m * b := by
  obtain ⟨m, c, hc, hcm⟩ := WittVector.verschiebung_nonzero ha
  obtain ⟨b, rfl⟩ := (frobenius_bijective p k).Surjective.iterate m c
  rw [WittVector.iterate_frobenius_coeff] at hc 
  have := congr_fun (witt_vector.verschiebung_frobenius_comm.comp_iterate m) b
  simp only [Function.comp_apply] at this 
  rw [← this] at hcm 
  refine' ⟨m, b, _, _⟩
  · contrapose! hc
    have : 0 < p ^ m := pow_pos (Nat.Prime.pos (Fact.out _)) _
    simp [hc, zero_pow this]
  · rw [← mul_left_iterate (p : 𝕎 k) m]
    convert hcm
    ext1 x
    rw [mul_comm, ← WittVector.verschiebung_frobenius x]
#align witt_vector.exists_eq_pow_p_mul WittVector.exists_eq_pow_p_mul

end PerfectRing

section PerfectField

variable {k : Type _} [Field k] [CharP k p] [PerfectRing k p]

theorem exists_eq_pow_p_mul' (a : 𝕎 k) (ha : a ≠ 0) : ∃ (m : ℕ) (b : Units (𝕎 k)), a = p ^ m * b :=
  by
  obtain ⟨m, b, h₁, h₂⟩ := exists_eq_pow_p_mul a ha
  let b₀ := Units.mk0 (b.coeff 0) h₁
  have hb₀ : b.coeff 0 = b₀ := rfl
  exact ⟨m, mk_unit hb₀, h₂⟩
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
  DiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    (by
      refine' ⟨p, Irreducible p, fun x hx => _⟩
      obtain ⟨n, b, hb⟩ := exists_eq_pow_p_mul' x hx
      exact ⟨n, b, hb.symm⟩)
#align witt_vector.discrete_valuation_ring WittVector.discreteValuationRing

end PerfectField

end WittVector

