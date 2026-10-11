/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.HasseDeriv
public import Mathlib.Data.Nat.Choose.Lucas

/-!
# Hasse derivatives in prime characteristic

Over a ring of prime characteristic `p`, the Hasse derivatives `hasseDeriv k f` of orders
`0 < k < p ^ e` all vanish if and only if `f` is a polynomial in `X ^ (p ^ e)`.

## Main statements

* `Polynomial.forall_hasseDeriv_eq_zero_iff`: the Hasse derivatives of `f` of orders
  `0 < k < p ^ e` vanish if and only if `p ^ e` divides every exponent of `f`.
* `Polynomial.forall_hasseDeriv_eq_zero_iff_exists_expand`: the same condition holds if and only if
  `f = expand R (p ^ e) g` for some `g`.
-/

public section

namespace Polynomial

variable {R : Type*} (p : ℕ) [hp : Fact p.Prime]

section Ring

variable [Ring R] [CharP R p]

/-- In characteristic `p`, the Hasse derivatives of `f` of orders `0 < k < p ^ e` vanish if and
only if `p ^ e` divides every exponent of `f`. -/
theorem forall_hasseDeriv_eq_zero_iff {e : ℕ} {f : R[X]} :
    (∀ k, 0 < k → k < p ^ e → hasseDeriv k f = 0) ↔ ∀ n, f.coeff n ≠ 0 → p ^ e ∣ n := by
  have key (c : ℕ) (a : R) : (c : R) * a = 0 ↔ p ∣ c ∨ a = 0 := by
    by_cases hc : p ∣ c
    · simp [hc, (CharP.cast_eq_zero_iff R p c).2 hc]
    · simp [hc, ((CharP.isUnit_natCast_iff (R := R) hp.out).2 hc).mul_right_eq_zero]
  simp_rw [hasseDeriv_eq_zero_iff, key, Choose.pow_dvd_iff_forall_dvd_choose (p := p)]
  exact ⟨fun h n hn k hk hk' ↦ (h k hk hk' n).resolve_right hn,
    fun h k hk hk' n ↦ or_iff_not_imp_right.2 fun hn ↦ h n hn k hk hk'⟩

end Ring

section CommRing

variable [CommRing R] [CharP R p]

/-- In characteristic `p`, the Hasse derivatives of `f` of orders `0 < k < p ^ e` vanish if and
only if `f` is a polynomial in `X ^ (p ^ e)`. -/
theorem forall_hasseDeriv_eq_zero_iff_exists_expand {e : ℕ} {f : R[X]} :
    (∀ k, 0 < k → k < p ^ e → hasseDeriv k f = 0) ↔ ∃ g, expand R (p ^ e) g = f := by
  have hpe : 0 < p ^ e := pow_pos hp.out.pos e
  rw [forall_hasseDeriv_eq_zero_iff]
  refine ⟨fun h ↦ ⟨contract (p ^ e) f, ext fun n ↦ ?_⟩, ?_⟩
  · rw [coeff_expand hpe, coeff_contract hpe.ne']
    split_ifs with hn
    · rw [Nat.div_mul_cancel hn]
    · exact (not_imp_comm.1 (h n) hn).symm
  · rintro ⟨g, rfl⟩ n hn
    rw [coeff_expand hpe] at hn
    exact of_not_not fun h' ↦ hn (by simp [h'])

end CommRing

end Polynomial
