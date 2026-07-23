/-
Copyright (c) 2026 Eliott Cassidy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliott Cassidy
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-!
# Vieta valuation-0 input for the orbit-product wrapper

`GMC2.Thm2067Wrapper.thm2067_contradiction` consumes two number-theoretic inputs about the roots of
`Φ(X) = Xᴹ − t·R(X)` over `F(t)`:

* `hS` (the small-root product identity): the small-root product equals `c·t` (`t`-adic valuation 1)
  — the deep analytic gap;
* `hΩ` (**Vieta**): the full-root product is a nonzero *constant* `d ∈ F` (`t`-adic valuation 0).

This module supplies the number-theoretic content of the second input. By Vieta's formula the
product of the roots of `Φ` (over a splitting field) is `(−1)^{deg} · Φ.coeff 0 / Φ.leadingCoeff`,
so the point is that this ratio is *constant in `t`*: `Φ.coeff 0 = −t·r₀` and
`Φ.leadingCoeff = −t·lc(R)`, and the `t` cancels, leaving `r₀/lc(R) ∈ F`. Hence the root product has
`t`-adic valuation `0`.
-/

open Polynomial

namespace GMC2.PhiVieta

variable {F : Type*} [Field F]

/-- `Φ = Xᴹ − t·R` over `F(t)` (`t = RatFunc.X`, `R` embedded as constants). -/
noncomputable def Phi (R : F[X]) (M : ℕ) : (RatFunc F)[X] :=
  X ^ M - C (RatFunc.X) * R.map (algebraMap F (RatFunc F))

theorem natDegree_t_Rmap (R : F[X]) :
    (C (RatFunc.X) * R.map (algebraMap F (RatFunc F))).natDegree = R.natDegree := by
  rw [Polynomial.natDegree_C_mul (by simpa using RatFunc.X_ne_zero),
    Polynomial.natDegree_map_eq_of_injective (algebraMap F (RatFunc F)).injective]

/-- With `M < deg R`, the `−t·R` term dominates, so `natDegree Φ = deg R`. -/
theorem natDegree_Phi (R : F[X]) (M : ℕ) (hMd : M < R.natDegree) :
    (Phi R M).natDegree = R.natDegree := by
  unfold Phi
  rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_right_of_natDegree_lt, natDegree_neg,
    natDegree_t_Rmap R]
  rw [natDegree_neg, natDegree_t_Rmap R, Polynomial.natDegree_X_pow]; exact hMd

/-- `Φ.coeff 0 = −t·r₀`. -/
theorem coeff_zero_Phi (R : F[X]) (M : ℕ) (hM : 1 ≤ M) :
    (Phi R M).coeff 0 = - RatFunc.X * (algebraMap F (RatFunc F)) (R.coeff 0) := by
  unfold Phi
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega),
    Polynomial.coeff_C_mul, Polynomial.coeff_map]; ring

/-- `Φ.leadingCoeff = −t·lc(R)`. -/
theorem leadingCoeff_Phi (R : F[X]) (M : ℕ) (hMd : M < R.natDegree) :
    (Phi R M).leadingCoeff = - RatFunc.X * (algebraMap F (RatFunc F)) R.leadingCoeff := by
  simp only [Polynomial.leadingCoeff]
  rw [natDegree_Phi R M hMd]
  unfold Phi
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega),
    Polynomial.coeff_C_mul, Polynomial.coeff_map]; ring

/-- **The Vieta core (valuation-0 fact).** `Φ.coeff 0 / Φ.leadingCoeff = r₀/lc(R)` is the image of a
CONSTANT of `F` (the `t` cancels), so the product of the roots of `Φ` (= `±` this ratio) has
`t`-adic valuation `0` — the `hΩ` input of `GMC2.Thm2067Wrapper.thm2067_contradiction`. -/
theorem coeff_ratio_Phi_eq_const (R : F[X]) (M : ℕ) (hM : 1 ≤ M) (hR : R ≠ 0)
    (hMd : M < R.natDegree) :
    (Phi R M).coeff 0 / (Phi R M).leadingCoeff
      = (algebraMap F (RatFunc F)) (R.coeff 0 / R.leadingCoeff) := by
  rw [coeff_zero_Phi R M hM, leadingCoeff_Phi R M hMd, map_div₀]
  have hX : (RatFunc.X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
  have hlc : (algebraMap F (RatFunc F)) R.leadingCoeff ≠ 0 := by
    simp only [Ne, (algebraMap F (RatFunc F)).injective.eq_iff' (map_zero _)]
    exact Polynomial.leadingCoeff_ne_zero.mpr hR
  field_simp

/-- **Vieta: the product of the roots of `Φ` is a constant** (`t`-adic valuation 0). Over any field
`E` where `Φ` splits, `∏ roots = (−1)^d · (r₀/lc R)`, the image of a constant of `F`. This is the
`hΩ` input of `GMC2.Thm2067Wrapper.thm2067_contradiction` (the full-root product is a nonzero
constant). -/
theorem prod_roots_Phi (R : F[X]) (M : ℕ) (hM : 1 ≤ M) (hMd : M < R.natDegree)
    {E : Type*} [Field E] [Algebra (RatFunc F) E]
    (hsplit : Splits ((Phi R M).map (algebraMap (RatFunc F) E))) :
    (((Phi R M).map (algebraMap (RatFunc F) E)).roots).prod
      = ((-1) ^ R.natDegree : E) *
        (algebraMap (RatFunc F) E) ((algebraMap F (RatFunc F)) (R.coeff 0 / R.leadingCoeff)) := by
  have hR : R ≠ 0 := by intro h; rw [h] at hMd; simp at hMd
  have hPne : Phi R M ≠ 0 := by
    intro h; have h2 := natDegree_Phi R M hMd; rw [h, natDegree_zero] at h2; omega
  have hnd : ((Phi R M).map (algebraMap (RatFunc F) E)).natDegree = R.natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap (RatFunc F) E).injective,
      natDegree_Phi R M hMd]
  have hkey := Splits.coeff_zero_eq_leadingCoeff_mul_prod_roots hsplit
  rw [hnd, Polynomial.coeff_map, Polynomial.leadingCoeff, hnd, Polynomial.coeff_map] at hkey
  have hcd : (Phi R M).coeff R.natDegree = (Phi R M).leadingCoeff := by
    rw [Polynomial.leadingCoeff, natDegree_Phi R M hMd]
  have hB : (algebraMap (RatFunc F) E) ((Phi R M).coeff R.natDegree) ≠ 0 := by
    rw [hcd, Ne, (algebraMap (RatFunc F) E).injective.eq_iff' (map_zero _)]
    exact Polynomial.leadingCoeff_ne_zero.mpr hPne
  have hsign : ((-1 : E) ^ R.natDegree) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hratio : (Phi R M).coeff 0 / (Phi R M).coeff R.natDegree
      = (algebraMap F (RatFunc F)) (R.coeff 0 / R.leadingCoeff) := by
    rw [hcd]; exact coeff_ratio_Phi_eq_const R M hM hR hMd
  have hP : ((Phi R M).map (algebraMap (RatFunc F) E)).roots.prod
      = (algebraMap (RatFunc F) E) ((Phi R M).coeff 0)
        / (((-1 : E) ^ R.natDegree)
            * (algebraMap (RatFunc F) E) ((Phi R M).coeff R.natDegree)) := by
    rw [eq_div_iff (mul_ne_zero hsign hB)]; linear_combination -hkey
  rw [hP, mul_comm ((-1 : E) ^ R.natDegree), ← div_div, ← map_div₀, hratio, div_eq_mul_inv]
  rw [mul_comm]; congr 1
  rw [← inv_pow, inv_neg_one]

/-- **Vieta, rootSet form (the `hΩ` input of
`GMC2.Thm2067Concrete.thm2067_contradiction_concrete`).** Over the splitting field of
`Φ = Xᴹ − t·R`, the product of the *distinct* roots (the `rootSet`) is the image of the single
constant `d = (−1)^{deg R}·(r₀/lc R) ∈ F`. Separability turns the product over the `rootSet` subtype
into the multiset root product, to which `prod_roots_Phi` applies; the sign and the nested
`algebraMap`/`RatFunc.C` then fold into `RatFunc.C d` (`t`-adic valuation `0`).

This is exactly the shape the concrete orbit-product wrapper takes as `hΩ` (with
`d := (−1)^{R.natDegree}·(R.coeff 0 / R.leadingCoeff)`), so together with `irreducible_Phi` (`hΦ`)
it reduces the concrete orbit-product contradiction to the single deep analytic input
`hS` (the small-root product identity). -/
theorem prod_rootSet_Phi (R : F[X]) (M : ℕ) (hM : 1 ≤ M) (hMd : M < R.natDegree)
    (hsep : Separable ((Phi R M).map (algebraMap (RatFunc F) (Phi R M).SplittingField))) :
    (∏ α : (Phi R M).rootSet (Phi R M).SplittingField, (α : (Phi R M).SplittingField))
      = algebraMap (RatFunc F) (Phi R M).SplittingField
          (RatFunc.C ((-1) ^ R.natDegree * (R.coeff 0 / R.leadingCoeff))) := by
  classical
  set SF := (Phi R M).SplittingField with hSFdef
  have hsplit : Splits ((Phi R M).map (algebraMap (RatFunc F) SF)) :=
    Polynomial.IsSplittingField.splits SF (Phi R M)
  have hnd : (((Phi R M).map (algebraMap (RatFunc F) SF)).roots).Nodup := nodup_roots hsep
  -- the product over the `rootSet` subtype is the multiset root product (separable ⇒ nodup)
  have hbridge :
      (∏ α : (Phi R M).rootSet SF, (α : SF))
        = ((Phi R M).map (algebraMap (RatFunc F) SF)).roots.prod := by
    have h1 : (∏ α : (Phi R M).rootSet SF, (α : SF))
        = ∏ x ∈ ((Phi R M).aroots SF).toFinset, x := by
      first
      | exact Finset.prod_attach _ id
      | exact Finset.prod_attach _ _
    rw [h1, Polynomial.aroots, Finset.prod_eq_multiset_prod, Multiset.map_id',
      Multiset.toFinset_val, hnd.dedup]
  rw [hbridge, prod_roots_Phi R M hM hMd hsplit]
  -- fold the `(−1)^d` sign and the nested `algebraMap`/`RatFunc.C` into `RatFunc.C d`
  simp only [map_mul, map_pow, map_neg, map_one]
  first
  | rfl
  | rw [RatFunc.algebraMap_eq_C]

end GMC2.PhiVieta

