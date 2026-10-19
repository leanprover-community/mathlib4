/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-!
# The graded ring of level-1 modular forms

This file collects structural results about the graded ring `⨁ k, ModularForm 𝒮ℒ k` of
level-1 modular forms, beyond those that fall out of the dimension formula directly. In
particular, every level-1 modular form is a polynomial in the Eisenstein series `E₄` and `E₆`,
and `E₄` and `E₆` are algebraically independent.

## Main definitions

* `ModularForm.evalE₄E₆`: the evaluation homomorphism
  `ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` sending `X₀ ↦ E₄` and `X₁ ↦ E₆`.
* `ModularForm.mvPolynomialEquivModularForms`: the `ℂ`-algebra isomorphism
  `ℂ[X₀, X₁] ≃ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` given by `evalE₄E₆`.

## Main results

* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`: the pointwise identity
  `Δ = (E₄³ - E₆²) / 1728`.
* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded`: the same identity in the graded
  ring `⨁ k, ModularForm 𝒮ℒ k`.
* `ModularForm.evalE₄E₆_surjective`: `evalE₄E₆` is surjective.
* `ModularForm.adjoin_E₄_E₆_eq_top`: `E₄` and `E₆` generate `⨁ k, ModularForm 𝒮ℒ k` as a
  `ℂ`-algebra; in particular it is a finitely generated `ℂ`-algebra and a Noetherian ring.
* `ModularForm.evalE₄E₆_injective`: `evalE₄E₆` is injective, i.e. `E₄` and `E₆` are
  algebraically independent (`ModularForm.algebraicIndependent_E₄_E₆`); in particular
  `⨁ k, ModularForm 𝒮ℒ k` is an integral domain.

## Implementation notes

Surjectivity is proved by induction on the weight `k`. Forms of negative or odd weight, or of
weight `2`, vanish. Otherwise `k = 4 * a + 6 * b` for some `a b : ℕ`, and subtracting a multiple
of `E₄ ^ a * E₆ ^ b` from a form `f` of weight `k` leaves a cusp form. That cusp form is `Δ`
times a form of weight `k - 12` (`CuspForm.discriminantEquiv`), which is a polynomial in `E₄` and
`E₆` by induction, and so is `Δ = (E₄³ - E₆²) / 1728`. The same step covers the weights `k < 12`,
where the form of weight `k - 12` is zero.

Injectivity is proved one weight at a time. Since `E₄` and `E₆` have constant term `1`, the
constant term of the `q`-expansion of the image of a polynomial `p` is `p (1, 1)`. Let
`D = (X₀³ - X₁²) / 1728`, which maps to `Δ`. Division with remainder by `D` for the lexicographic
monomial order (`MonomialOrder.div_single`), in which the leading monomial of `D` is `X₀³`,
followed by taking weight-`k` components, writes a weighted-homogeneous polynomial `p` of weight
`k ≥ 12` as `r + D * s` with `r` and `s` weighted-homogeneous, where every monomial
`X₀ ^ a * X₁ ^ b` of `r` has `a < 3` (for `k < 12`, `p` itself has this property); so `r` is a
multiple of a single monomial. If `p` maps to zero, then `r (1, 1) = 0` because `D (1, 1) = 0`, so
`r = 0`; and then `Δ * evalE₄E₆ s = 0` gives `s = 0` by induction on the weight.

## References

* [J.-P. Serre, *A Course in Arithmetic*][serre1973], VII.3.2.
-/

public noncomputable section

open UpperHalfPlane ModularForm ModularFormClass EisensteinSeries

open scoped MatrixGroups

namespace ModularForm

/-- The combination `E₄³ - E₆²` viewed as a level-1 modular form of weight 12. -/
private noncomputable def E₄CubeSubE₆SqForm : ModularForm 𝒮ℒ 12 :=
  ModularForm.mcast (by decide) (E₄.pow 3) - ModularForm.mcast (by decide) (E₆.pow 2)

private lemma E₄CubeSubE₆SqForm_apply (z : ℍ) :
    E₄CubeSubE₆SqForm z = E₄ z ^ 3 - E₆ z ^ 2 := by
  simp only [E₄CubeSubE₆SqForm, coe_mcast, coe_pow, sub_apply, Pi.pow_apply]

private lemma E₄CubeSubE₆SqForm_qExpansion_eq :
    qExpansion 1 E₄CubeSubE₆SqForm = qExpansion 1 E₄ * qExpansion 1 E₄ * qExpansion 1 E₄ -
      qExpansion 1 E₆ * qExpansion 1 E₆ := by
  simp only [E₄CubeSubE₆SqForm, FunLike.coe_sub, coe_mcast,
    ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  ring

private lemma E₄CubeSubE₆SqForm_isCuspForm : IsCuspForm E₄CubeSubE₆SqForm := by
  simp [isCuspForm_iff_coeffZero_eq_zero, E₄CubeSubE₆SqForm_qExpansion_eq,
    PowerSeries.coeff_mul, -PowerSeries.coeff_zero_eq_constantCoeff,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

private lemma E₄CubeSubE₆SqForm_qExpansion_coeff_one :
    (qExpansion 1 E₄CubeSubE₆SqForm).coeff 1 = 1728 := by
  rw [E₄CubeSubE₆SqForm_qExpansion_eq]
  norm_num [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, E₄_qExpansion_coeff_one,
    E₆_qExpansion_coeff_one, E_qExpansion_coeff_zero _ ⟨2, rfl⟩,
    E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

/-- The modular discriminant equals `(E₄³ - E₆²) / 1728`. -/
theorem discriminant_eq_E₄_cube_sub_E₆_sq (z : ℍ) :
    discriminant z = (E₄ z ^ 3 - E₆ z ^ 2) / 1728 := by
  obtain ⟨g, hg⟩ := E₄CubeSubE₆SqForm_isCuspForm
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hgE : (g : ℍ → ℂ) = E₄CubeSubE₆SqForm := congrArg DFunLike.coe hg
  have hc_eq : c = 1728 := by
    have hcΔ : (c • CuspForm.discriminant : ℍ → ℂ) = g := congrArg DFunLike.coe hc
    have hgΔ := ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL c
      CuspForm.discriminant
    rw [hcΔ, hgE] at hgΔ
    simpa [PowerSeries.coeff_smul, discriminant_qExpansion_coeff_one,
      E₄CubeSubE₆SqForm_qExpansion_coeff_one] using congr($(hgΔ).coeff 1).symm
  have h1728 : (1728 : ℂ) * discriminant z = E₄ z ^ 3 - E₆ z ^ 2 := by
    rw [← hc_eq, show c * discriminant z = (c • CuspForm.discriminant) z from rfl, hc,
      congr($hgE z), E₄CubeSubE₆SqForm_apply]
  linear_combination h1728 / 1728

/-- The modular discriminant equals `(E₄³ - E₆²) / 1728` in the graded ring
`⨁ k, ModularForm 𝒮ℒ k`. -/
theorem discriminant_eq_E₄_cube_sub_E₆_sq_graded :
    DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant =
      (1 / 1728 : ℂ) • (.of (ModularForm 𝒮ℒ) 4 E₄ ^ 3 - .of (ModularForm 𝒮ℒ) 6 E₆ ^ 2) := by
  simp only [ModularForm.directSum_of_pow]
  change DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant = (1 / 1728 : ℂ) •
    (DirectSum.of (ModularForm 𝒮ℒ) 12 (E₄.pow 3) - DirectSum.of (ModularForm 𝒮ℒ) 12 (E₆.pow 2))
  rw [← map_sub (DirectSum.of (ModularForm 𝒮ℒ) 12), ← DirectSum.of_smul]
  congr 1
  ext z
  change ModularForm.discriminant z = (1 / 1728 : ℂ) * (E₄ z ^ 3 - E₆ z ^ 2)
  grind [discriminant_eq_E₄_cube_sub_E₆_sq z]

/-! ### `E₄` and `E₆` generate the graded ring -/

/-- The evaluation homomorphism from `ℂ[X₀, X₁]` to the graded ring `⨁ k, ModularForm 𝒮ℒ k` of
level-1 modular forms, sending `X₀ = MvPolynomial.X 0` to `E₄` (in weight `4`) and
`X₁ = MvPolynomial.X 1` to `E₆` (in weight `6`). It is surjective (`evalE₄E₆_surjective`). -/
def evalE₄E₆ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  MvPolynomial.aeval ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄, DirectSum.of (ModularForm 𝒮ℒ) 6 E₆]

/-- `evalE₄E₆` sends `X 0` to `E₄`, in weight `4` of the graded ring `⨁ k, ModularForm 𝒮ℒ k`. -/
@[simp]
lemma evalE₄E₆_X_zero : evalE₄E₆ (MvPolynomial.X 0) = DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ :=
  MvPolynomial.aeval_X _ 0

/-- `evalE₄E₆` sends `X 1` to `E₆`, in weight `6` of the graded ring `⨁ k, ModularForm 𝒮ℒ k`. -/
@[simp]
lemma evalE₄E₆_X_one : evalE₄E₆ (MvPolynomial.X 1) = DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ :=
  MvPolynomial.aeval_X _ 1

private lemma discriminant_mem_range : DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant ∈
    evalE₄E₆.range :=
  ⟨(1 / 1728 : ℂ) • (.X 0 ^ 3 - .X 1 ^ 2), by simp [discriminant_eq_E₄_cube_sub_E₆_sq_graded]⟩

private lemma exists_mem_range_coeff_zero_eq_one {k : ℕ} (hk : Even k) (h2 : k ≠ 2) :
    ∃ m : ModularForm 𝒮ℒ k, DirectSum.of _ _ m ∈ evalE₄E₆.range ∧ (qExpansion 1 m).coeff 0 = 1 := by
  -- Take `m = E₄ ^ a * E₆ ^ b` with `4 * a + 6 * b = k`: here `b = 1` exactly when
  -- `k ≡ 2 [MOD 4]`, and then `k ≠ 2` gives `1 ≤ k / 4`.
  rw [Nat.even_iff] at hk
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, 4 * a + 6 * b = k := ⟨k / 4 - k % 4 / 2, k % 4 / 2, by lia⟩
  -- `E₄ ^ a * E₆ ^ b` has degree `a • 4 + b • 6 = k`, so it is its own weight-`k` component.
  have h : DirectSum.of _ (k : ℤ) (evalE₄E₆ (.X 0 ^ a * .X 1 ^ b) k) =
      evalE₄E₆ (.X 0 ^ a * .X 1 ^ b) := by
    rw [map_mul, map_pow, map_pow, evalE₄E₆_X_zero, evalE₄E₆_X_one, DirectSum.ofPow,
      DirectSum.ofPow, DirectSum.of_mul_of, show (k : ℤ) = a • 4 + b • 6 by lia,
      DirectSum.of_eq_same]
  refine ⟨evalE₄E₆ (.X 0 ^ a * .X 1 ^ b) k, h.symm ▸ ⟨_, rfl⟩, ?_⟩
  -- Transport along `qExpansionRingHom`; both Eisenstein series have constant term `1`.
  rw [← qExpansionRingHom_apply one_pos one_mem_strictPeriods_SL, h]
  simpa using
    congr($(E_qExpansion_coeff_zero _ ⟨2, rfl⟩) ^ a * $(E_qExpansion_coeff_zero _ ⟨3, rfl⟩) ^ b)

private lemma cuspForm_eq_discriminant_mul {k : ℤ} (g : CuspForm 𝒮ℒ k) :
    DirectSum.of (ModularForm 𝒮ℒ) k g = DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant *
      DirectSum.of (ModularForm 𝒮ℒ) (k - 12) (CuspForm.discriminantEquiv g) := by
  rw [DirectSum.of_mul_of]
  symm
  -- The degrees agree as `12 + (k - 12) = k`, and `mcast` along this identity does not change
  -- the underlying function, so the coercion goal is definitionally `Δ * (g / Δ) = g`.
  refine DirectSum.of_eq_of_gradedMonoid_eq (gradedMonoid_eq_of_cast (add_sub_cancel _ _) ?_)
  exact DFunLike.coe_injective (discriminant_mul_discriminantEquiv _)

private lemma directSum_of_mem_range (k : ℤ) (f : ModularForm 𝒮ℒ k) :
    DirectSum.of _ k f ∈ evalE₄E₆.range := by
  induction k using Int.strongRec (m := 0) with
  | lt k hk => simp [rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f]
  | ge k hk ih =>
    lift k to ℕ using hk
    by_cases hodd : Odd k
    · simp [levelOne_odd_weight_eq_zero hodd.natCast f]
    obtain rfl | h2 := eq_or_ne k 2
    · simp [rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f]
    -- `f` minus its constant term times `m` is a cusp form `g`, and `g` is `Δ` times the form
    -- `g / Δ` of weight `k - 12`, which lies in the range by `ih`.
    obtain ⟨m, hm, hm1⟩ := exists_mem_range_coeff_zero_eq_one (Nat.not_odd_iff_even.mp hodd) h2
    obtain ⟨g, hg⟩ := sub_smul_isCuspForm f m hm1
    rw [← sub_add_cancel f ((qExpansion 1 f).coeff 0 • m), ← hg, map_add, DirectSum.of_smul,
      CuspForm.toModularFormₗ_eq_coe, cuspForm_eq_discriminant_mul]
    exact add_mem (mul_mem discriminant_mem_range (ih _ (by lia) _)) (Subalgebra.smul_mem _ hm _)

/-- The evaluation homomorphism `evalE₄E₆` is surjective: every element of the graded ring
`⨁ k, ModularForm 𝒮ℒ k`, i.e. every finite sum of level-1 modular forms of possibly different
weights, is a polynomial in `E₄` and `E₆`. -/
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := fun x ↦
  evalE₄E₆.mem_range.mp <| DirectSum.induction_on x (zero_mem _) directSum_of_mem_range
    fun _ _ ↦ add_mem

/-- `E₄` and `E₆` generate the graded ring `⨁ k, ModularForm 𝒮ℒ k` of level-1 modular forms
as a `ℂ`-algebra. -/
theorem adjoin_E₄_E₆_eq_top : Algebra.adjoin ℂ {DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
    DirectSum.of (ModularForm 𝒮ℒ) 6 E₆} = ⊤ := by
  rw [← Matrix.range_cons_cons_empty _ _ ![], Algebra.adjoin_range_eq_range_aeval]
  exact evalE₄E₆.range_eq_top.2 evalE₄E₆_surjective

/-- The graded ring `⨁ k, ModularForm 𝒮ℒ k` of level-1 modular forms is a finitely generated
`ℂ`-algebra. -/
instance : Algebra.FiniteType ℂ (DirectSum ℤ (ModularForm 𝒮ℒ)) :=
  .of_surjective evalE₄E₆ evalE₄E₆_surjective

/-- The graded ring `⨁ k, ModularForm 𝒮ℒ k` of level-1 modular forms is a Noetherian ring. -/
instance : IsNoetherianRing (DirectSum ℤ (ModularForm 𝒮ℒ)) :=
  Algebra.FiniteType.isNoetherianRing ℂ _

/-! ### `E₄` and `E₆` are algebraically independent -/

private def discriminantPoly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

private lemma evalE₄E₆_discriminantPoly : evalE₄E₆ discriminantPoly =
    DirectSum.of (ModularForm 𝒮ℒ) 12 CuspForm.discriminant := by
  simp [discriminantPoly, discriminant_eq_E₄_cube_sub_E₆_sq_graded]

private lemma weight_four_six_apply (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = d 0 * 4 + d 1 * 6 := by
  simp [Finsupp.weight_eq_sum]

private lemma eq_of_weight_eq_of_lt_three {d d' : Fin 2 →₀ ℕ} (hd : d 0 < 3) (hd' : d' 0 < 3)
    (h : Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = Finsupp.weight ![4, 6] d') : d = d' := by
  rw [weight_four_six_apply, weight_four_six_apply] at h
  exact Finsupp.ext fun i ↦ by fin_cases i <;> lia

private lemma evalE₄E₆_monomial_apply_eq_zero_of_ne (d : Fin 2 →₀ ℕ) (c : ℂ) (k : ℤ)
    (hk : k ≠ d 0 * 4 + d 1 * 6) : evalE₄E₆ (MvPolynomial.monomial d c) k = 0 := by
  simp [MvPolynomial.monomial_fin_two, MvPolynomial.C_mul', DirectSum.ofPow, DirectSum.of_mul_of,
    DirectSum.smul_apply, DirectSum.of_eq_of_ne, hk]

private lemma evalE₄E₆_eq_of_isWeightedHomogeneous {n : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n) :
    evalE₄E₆ p = DirectSum.of (ModularForm 𝒮ℒ) n (evalE₄E₆ p n) := by
  ext k : 1
  obtain rfl | hk := eq_or_ne k n
  · simp
  -- Every monomial of `p` has weight `n`, so its image vanishes in degree `k ≠ n`.
  rw [DirectSum.of_eq_of_ne _ _ _ hk, p.as_sum, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd ↦ evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ ?_
  simpa [← hp (MvPolynomial.mem_support_iff.mp hd), weight_four_six_apply] using hk

private lemma evalE₄E₆_weightedHomogeneousComponent_apply (p : MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    evalE₄E₆ (MvPolynomial.weightedHomogeneousComponent ![4, 6] n p) n = evalE₄E₆ p n := by
  -- Both sides are sums over the monomials of `p`; those of weight `≠ n` vanish in degree `n`.
  conv_rhs => rw [p.as_sum]
  simp only [MvPolynomial.weightedHomogeneousComponent_apply, map_sum, DirectSum.sum_apply]
  exact Finset.sum_filter_of_ne fun d _ ↦ Not.imp_symm fun h ↦
    evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ <| by lia [weight_four_six_apply d]

private lemma discriminantPoly_isWeightedHomogeneous :
    discriminantPoly.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) 12 :=
  (MvPolynomial.weightedHomogeneousSubmodule ℂ _ 12).smul_mem _ <|
    ((MvPolynomial.isWeightedHomogeneous_X ℂ _ 0).pow 3).sub <|
      (MvPolynomial.isWeightedHomogeneous_X ℂ _ 1).pow 2

private lemma constantCoeff_qExpansionAlgHom_evalE₄E₆ (p : MvPolynomial (Fin 2) ℂ) :
    PowerSeries.constantCoeff (qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL (evalE₄E₆ p)) =
      MvPolynomial.eval 1 p := by
  -- Both sides are ring homomorphisms in `p`; on `X 0` and `X 1` they are `1`, since `E₄` and `E₆`
  -- have constant term `1`.
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    fin_cases i
    · simpa [hp] using congr(MvPolynomial.eval 1 p * $(E_qExpansion_coeff_zero _ ⟨2, rfl⟩))
    · simpa [hp] using congr(MvPolynomial.eval 1 p * $(E_qExpansion_coeff_zero _ ⟨3, rfl⟩))

attribute [local instance] MvPolynomial.weightedGradedAlgebra in
private lemma weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right {σ R : Type*}
    [CommSemiring R] {w : σ → ℕ} {i n : ℕ} {f q : MvPolynomial σ R}
    (hq : q.IsWeightedHomogeneous w i) (hin : i ≤ n) :
    MvPolynomial.weightedHomogeneousComponent w n (f * q) =
      MvPolynomial.weightedHomogeneousComponent w (n - i) f * q := by
  simp_rw [← MvPolynomial.weightedDecomposition.decompose'_apply]
  exact DirectSum.coe_decompose_mul_of_right_mem_of_le _ hq hin

private lemma div_single_of_isWeightedHomogeneous {σ R : Type*} [CommRing R] (m : MonomialOrder σ)
    {w : σ → ℕ} {i n : ℕ} {b f : MvPolynomial σ R} (hb : IsUnit (m.leadingCoeff b))
    (hbi : b.IsWeightedHomogeneous w i) (hf : f.IsWeightedHomogeneous w n) (hin : i ≤ n) :
    ∃ g r : MvPolynomial σ R, g.IsWeightedHomogeneous w (n - i) ∧ r.IsWeightedHomogeneous w n ∧
      f = g * b + r ∧ ∀ c ∈ r.support, ¬m.degree b ≤ c := by
  obtain ⟨g, r, hgr, -, hr⟩ := m.div_single hb f
  -- Take weight-`n` components in `f = g * b + r`.
  apply_fun MvPolynomial.weightedHomogeneousComponent w n at hgr
  rw [hf.weightedHomogeneousComponent_same, map_add,
    weightedHomogeneousComponent_mul_of_isWeightedHomogeneous_right hbi hin] at hgr
  refine ⟨_, _, MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous (n - i) g,
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous n r, hgr, fun c hc ↦ ?_⟩
  rw [MvPolynomial.support_weightedHomogeneousComponent, Finset.mem_filter] at hc
  exact hr c hc.1

private lemma lex_degree_discriminantPoly : MonomialOrder.lex.degree discriminantPoly =
    Finsupp.single 0 3 := by
  -- The leading monomial of `X₀ ^ 3 - X₁ ^ 2` is `X₀ ^ 3`, as `X₁ ^ 2 < X₀ ^ 3` lexicographically.
  rw [discriminantPoly, MonomialOrder.degree_smul_of_isRegular (.of_ne_zero (by norm_num)),
    MonomialOrder.degree_sub_of_lt] <;>
    simp [MonomialOrder.degree_pow, MonomialOrder.degree_X, MonomialOrder.lex_lt_iff,
      Finsupp.Lex.lt_iff]

private lemma exists_eq_reduced_add_discriminantPoly_mul {n : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hp : p.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n) (hn : 12 ≤ n) :
    ∃ r s : MvPolynomial (Fin 2) ℂ, r.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n ∧
      s.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (n - 12) ∧
      p = r + discriminantPoly * s ∧ ∀ d ∈ r.support, d 0 < 3 := by
  -- Divide by `discriminantPoly`, whose leading monomial for the lexicographic order is `X₀ ^ 3`:
  -- every monomial of the remainder `r` then has `X₀`-degree `< 3`.
  obtain ⟨s, r, hs, hr, rfl, hr_red⟩ := div_single_of_isWeightedHomogeneous .lex
    (MonomialOrder.isUnit_leadingCoeff.mpr <| MonomialOrder.lex.ne_zero_of_degree_ne_zero <| by
      simp [lex_degree_discriminantPoly])
    discriminantPoly_isWeightedHomogeneous hp hn
  refine ⟨r, s, hr, hs, by ring, fun d hd ↦ ?_⟩
  simpa [lex_degree_discriminantPoly, Finsupp.single_le_iff] using hr_red d hd

private lemma reduced_isWeightedHomogeneous_eq_monomial {n : ℕ} {r : MvPolynomial (Fin 2) ℂ}
    (hr : r.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) {d₀ : Fin 2 →₀ ℕ} (hd₀ : d₀ ∈ r.support) :
    r = MvPolynomial.monomial d₀ (r.coeff d₀) :=
  -- An exponent `(a, b)` with `a < 3` is determined by its weight `4 * a + 6 * b`.
  MvPolynomial.eq_monomial_of_support_subset_singleton fun d hd ↦
    eq_of_weight_eq_of_lt_three (hr_red d hd) (hr_red d₀ hd₀) <|
      (hr (MvPolynomial.mem_support_iff.mp hd)).trans
        (hr (MvPolynomial.mem_support_iff.mp hd₀)).symm

private lemma reduced_eq_zero_of_eval_one_eq_zero {n : ℕ} {r : MvPolynomial (Fin 2) ℂ}
    (hr : r.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) (h0 : MvPolynomial.eval 1 r = 0) : r = 0 := by
  -- A nonzero `r` is a single monomial `c • X₀ ^ a * X₁ ^ b` with `c ≠ 0`, since its monomials
  -- all have weight `n` and `a < 3`; its value at `(1, 1)` is `c`.
  contrapose! h0 with hr0
  obtain ⟨d₀, hd₀⟩ := MvPolynomial.exists_coeff_ne_zero hr0
  rw [reduced_isWeightedHomogeneous_eq_monomial hr hr_red (MvPolynomial.mem_support_iff.mpr hd₀)]
  simpa [MvPolynomial.eval_monomial] using hd₀

private lemma evalE₄E₆_apply_eq_zero_of_discriminantPoly_mul_eq_zero {n : ℕ}
    {s : MvPolynomial (Fin 2) ℂ} (hs : s.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (hds : evalE₄E₆ (discriminantPoly * s) = 0) : evalE₄E₆ s n = 0 := by
  rw [map_mul, evalE₄E₆_discriminantPoly, evalE₄E₆_eq_of_isWeightedHomogeneous hs,
    DirectSum.of_mul_of, map_eq_zero_iff _ (DirectSum.of_injective _)] at hds
  -- Now `hds : Δ * g = 0` with `g = (evalE₄E₆ s) n`, and `Δ` has no zeros on `ℍ`.
  simpa [DFunLike.ext_iff, discriminant_ne_zero, GradedMonoid.GMul.mul] using hds

private lemma eq_zero_of_isWeightedHomogeneous_of_evalE₄E₆_apply_eq_zero {n : ℕ}
    {p : MvPolynomial (Fin 2) ℂ} (hp : p.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) n)
    (heval : evalE₄E₆ p n = 0) : p = 0 := by
  induction n using Nat.strong_induction_on generalizing p with | _ n ih => ?_
  -- `evalE₄E₆ p` lies in degree `n`, so it vanishes, and so does the constant term `p (1, 1)` of
  -- its `q`-expansion.
  replace heval : evalE₄E₆ p = 0 := by
    rw [evalE₄E₆_eq_of_isWeightedHomogeneous hp, heval, map_zero]
  have h1 : MvPolynomial.eval 1 p = 0 := by
    rw [← constantCoeff_qExpansionAlgHom_evalE₄E₆, heval, map_zero, map_zero]
  obtain hn12 | hn12 := lt_or_ge n 12
  · -- In weight `n < 12`, every monomial `X₀ ^ a * X₁ ^ b` has `a < 3`.
    refine reduced_eq_zero_of_eval_one_eq_zero hp (fun d hd ↦ ?_) h1
    lia [weight_four_six_apply d, hp (MvPolynomial.mem_support_iff.mp hd)]
  -- Otherwise `p = r + D * s` with `r` reduced: `D (1, 1) = 0` gives `r (1, 1) = 0`, so `r = 0`;
  -- then `Δ * evalE₄E₆ s = 0` gives `s = 0` by induction.
  obtain ⟨r, s, hr, hs, rfl, hr_red⟩ := exists_eq_reduced_add_discriminantPoly_mul hp hn12
  obtain rfl : r = 0 :=
    reduced_eq_zero_of_eval_one_eq_zero hr hr_red (by simpa [discriminantPoly] using h1)
  rw [zero_add] at heval
  simp [ih _ (by lia) hs (evalE₄E₆_apply_eq_zero_of_discriminantPoly_mul_eq_zero hs heval)]

/-- The evaluation homomorphism `evalE₄E₆` is injective, i.e. `E₄` and `E₆` are algebraically
independent over `ℂ` in the graded ring `⨁ k, ModularForm 𝒮ℒ k`. Together with
`evalE₄E₆_surjective`, this gives the isomorphism `mvPolynomialEquivModularForms`. -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
  rw [← MvPolynomial.sum_weightedHomogeneousComponent ![4, 6] p]
  refine finsum_eq_zero_of_forall_eq_zero fun n ↦
    eq_zero_of_isWeightedHomogeneous_of_evalE₄E₆_apply_eq_zero
      (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _) ?_
  -- The weight-`n` component of `p` maps to the weight-`n` part of `evalE₄E₆ p = 0`.
  rw [evalE₄E₆_weightedHomogeneousComponent_apply, hp, DirectSum.zero_apply]

/-- `E₄` and `E₆` are algebraically independent over `ℂ` in the graded ring
`⨁ k, ModularForm 𝒮ℒ k`; this is `evalE₄E₆_injective` stated with `AlgebraicIndependent`. -/
theorem algebraicIndependent_E₄_E₆ : AlgebraicIndependent ℂ ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄,
    DirectSum.of (ModularForm 𝒮ℒ) 6 E₆] :=
  evalE₄E₆_injective

/-- The `ℂ`-algebra isomorphism `ℂ[X₀, X₁] ≃ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` given by `evalE₄E₆`,
sending `X₀` to `E₄` (in weight `4`) and `X₁` to `E₆` (in weight `6`). Its inverse writes each
element of the graded ring of level-1 modular forms uniquely as a polynomial in `E₄` and `E₆`. -/
def mvPolynomialEquivModularForms : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩

/-- As a function, `mvPolynomialEquivModularForms` is the evaluation map `evalE₄E₆`, so `simp`
computes it on explicit polynomials via `evalE₄E₆_X_zero` and `evalE₄E₆_X_one`. -/
@[simp]
lemma mvPolynomialEquivModularForms_apply (p : MvPolynomial (Fin 2) ℂ) :
    mvPolynomialEquivModularForms p = evalE₄E₆ p :=
  AlgEquiv.ofBijective_apply _ _ p

/-- `mvPolynomialEquivModularForms.symm` inverts the evaluation map `evalE₄E₆`. -/
@[simp]
lemma mvPolynomialEquivModularForms_symm_evalE₄E₆ (p : MvPolynomial (Fin 2) ℂ) :
    mvPolynomialEquivModularForms.symm (evalE₄E₆ p) = p :=
  AlgEquiv.ofBijective_symm_apply_apply _ _ p

/-- The graded ring `⨁ k, ModularForm 𝒮ℒ k` of level-1 modular forms is an integral domain. -/
instance : IsDomain (DirectSum ℤ (ModularForm 𝒮ℒ)) :=
  -- The graded ring is isomorphic to the polynomial ring `ℂ[X₀, X₁]`, which is a domain.
  mvPolynomialEquivModularForms.symm.toMulEquiv.isDomain _

end ModularForm

end
