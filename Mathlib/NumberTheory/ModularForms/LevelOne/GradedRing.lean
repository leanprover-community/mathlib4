/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Mathlib.Algebra.MvPolynomial.CommRing
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
  algebraically independent; in particular `⨁ k, ModularForm 𝒮ℒ k` is an integral domain.

## Implementation notes

Surjectivity is proved by induction on the weight `k`. Forms of negative or odd weight, or of
weight `2`, vanish. Otherwise `k = 4 * a + 6 * b` for some `a b : ℕ`, and subtracting a multiple
of `E₄ ^ a * E₆ ^ b` from a form `f` of weight `k` leaves a cusp form. That cusp form is `Δ`
times a form of weight `k - 12` (`CuspForm.discriminantEquiv`), which is a polynomial in `E₄` and
`E₆` by induction, and so is `Δ = (E₄³ - E₆²) / 1728`. The same step covers the weights `k < 12`,
where the form of weight `k - 12` is zero.

Injectivity is proved one weight at a time. A weighted-homogeneous polynomial `p` of weight
`k ≥ 12` can be written as `r + D * s`, where `D = (X₀³ - X₁²) / 1728` maps to `Δ` and `r` is a
single monomial `X₀ ^ a * X₁ ^ b` with `a < 3`. If `p` maps to zero, comparing constant terms of
`q`-expansions gives `r = 0`, and then `Δ * evalE₄E₆ s = 0` gives `s = 0` by induction.

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

private lemma evalE₄E₆_C (c : ℂ) :
    evalE₄E₆ (MvPolynomial.C c) = algebraMap ℂ (DirectSum ℤ (ModularForm 𝒮ℒ)) c :=
  MvPolynomial.algHom_C _ c

private lemma evalE₄E₆_monomial (a b : ℕ) :
    evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b) =
      DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a * DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b := by
  simp

private lemma directSum_of_E₄_pow_mul_E₆_pow_apply {a b n : ℕ} (hab : 4 * a + 6 * b = n) :
    DirectSum.of (ModularForm 𝒮ℒ) n
        ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a * DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) n) =
      DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a * DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b := by
  -- The graded degree of `E₄^a * E₆^b` is `a • 4 + b • 6`; reshape the index `n` into
  -- that form so that `of_eq_same` extracts the component.
  rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of, show (n : ℤ) = a • 4 + b • 6 by lia,
    DirectSum.of_eq_same]

private lemma monomial_qExpansion_coeff_zero_eq_one {n a b : ℕ} (hab : 4 * a + 6 * b = n) :
    (qExpansion 1 ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a * DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b)
      (n : ℤ))).coeff 0 = 1 := by
  -- Transport along the ring homomorphism `qExpansionRingHom` to the product of `q`-expansions.
  -- Both Eisenstein series are normalized to constant term `1`, so the zeroth
  -- coefficient of the product of their powers is `1`.
  rw [← qExpansionRingHom_apply one_pos one_mem_strictPeriods_SL,
    directSum_of_E₄_pow_mul_E₆_pow_apply hab]
  simpa using
    congr($(E_qExpansion_coeff_zero _ ⟨2, rfl⟩) ^ a * $(E_qExpansion_coeff_zero _ ⟨3, rfl⟩) ^ b)

private def discriminantPoly : MvPolynomial (Fin 2) ℂ :=
  (1 / 1728 : ℂ) • (MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2)

private lemma evalE₄E₆_discriminantPoly :
    evalE₄E₆ discriminantPoly =
      DirectSum.of (ModularForm 𝒮ℒ) 12
        ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) := by
  rw [discriminantPoly, map_smul, map_sub, map_pow, map_pow, evalE₄E₆_X_zero, evalE₄E₆_X_one,
    ← discriminant_eq_E₄_cube_sub_E₆_sq_graded]

private lemma one_ne_zero_modularForm : (1 : ModularForm 𝒮ℒ 0) ≠ 0 := fun h ↦
  one_ne_zero (α := ℂ) (congr_fun (congr_arg (DFunLike.coe (F := ModularForm 𝒮ℒ 0)) h)
    UpperHalfPlane.I)

private lemma discriminantPoly_smul_eq :
    (1728 : ℂ) • discriminantPoly = MvPolynomial.X 0 ^ 3 - MvPolynomial.X 1 ^ 2 := by
  rw [discriminantPoly, smul_smul]
  norm_num

/-- Transporting a modular form along an equality of weights does not change its
pointwise values. -/
private theorem cast_apply {Γ : Subgroup (GL (Fin 2) ℝ)} {k₁ k₂ : ℤ}
    (heq : k₁ = k₂) (f : ModularForm Γ k₁) (z : ℍ) :
    (heq ▸ f : ModularForm Γ k₂) z = f z := by
  subst heq
  rfl



private lemma weight_eq_4a_6b (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = d 0 * 4 + d 1 * 6 := by
  simp [Finsupp.weight_eq_sum, Fin.sum_univ_two, mul_comm]

private lemma no_weight_monomial_of_odd {n : ℕ} (hn : Odd n) (d : Fin 2 →₀ ℕ) :
    Finsupp.weight (![4, 6] : Fin 2 → ℕ) d ≠ n := by
  intro h
  rw [weight_eq_4a_6b] at h
  exact Nat.not_odd_iff_even.mpr ⟨d 0 * 2 + d 1 * 3, by lia⟩ hn

private lemma unique_small_weight_solution {a₁ b₁ a₂ b₂ : ℕ}
    (ha₁ : a₁ < 3) (ha₂ : a₂ < 3)
    (h : a₁ * 4 + b₁ * 6 = a₂ * 4 + b₂ * 6) : a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨by interval_cases a₁ <;> lia, by lia⟩

private lemma evalE₄E₆_X_pow_mul_apply_eq_zero_of_ne (a b : ℕ) (k : ℤ)
    (hk : k ≠ (↑a * 4 + ↑b * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.X 0 ^ a * MvPolynomial.X 1 ^ b)) k = 0 := by
  rw [evalE₄E₆_monomial, DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of]
  refine DirectSum.of_eq_of_ne _ _ _ fun heq ↦ hk ?_
  simpa using heq

private lemma evalE₄E₆_monomial_apply_eq_zero_of_ne (d : Fin 2 →₀ ℕ) (c : ℂ) (k : ℤ)
    (hk : k ≠ (↑(d 0) * 4 + ↑(d 1) * 6 : ℤ)) :
    (evalE₄E₆ (MvPolynomial.monomial d c)) k = 0 := by
  rw [MvPolynomial.monomial_fin_two, mul_assoc, map_mul,
    evalE₄E₆_C _,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, DirectSum.smul_apply,
    evalE₄E₆_X_pow_mul_apply_eq_zero_of_ne (d 0) (d 1) k hk, smul_zero]

private lemma evalE₄E₆_apply_eq_zero_of_ne {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (k : ℤ) (hk : k ≠ ↑n) :
    (evalE₄E₆ p) k = 0 := by
  rw [← MvPolynomial.support_sum_monomial_coeff p, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd ↦
    evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ fun heq ↦ hk ?_
  have hw := (weight_eq_4a_6b d).symm.trans (hp (MvPolynomial.mem_support_iff.mp hd))
  rw [heq]
  lia

private lemma evalE₄E₆_eq_of_apply (n : ℕ) (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n) :
    evalE₄E₆ p = DirectSum.of (ModularForm 𝒮ℒ) (↑n : ℤ) ((evalE₄E₆ p) ↑n) := by
  refine DFinsupp.ext fun k : ℤ ↦ ?_
  by_cases hk : k = (↑n : ℤ)
  · subst hk
    simp
  · rw [DirectSum.of_eq_of_ne _ _ _ hk, evalE₄E₆_apply_eq_zero_of_ne p hp k hk]

private lemma evalE₄E₆_component_eq (p : MvPolynomial (Fin 2) ℂ) (n : ℕ) :
    (evalE₄E₆
        (MvPolynomial.weightedHomogeneousComponent (![4, 6] : Fin 2 → ℕ) n p)) (↑n : ℤ) =
      (evalE₄E₆ p) (↑n : ℤ) := by
  set q := p - MvPolynomial.weightedHomogeneousComponent (![4, 6] : Fin 2 → ℕ) n p with hq_def
  have hdecomp :
      p = MvPolynomial.weightedHomogeneousComponent (![4, 6] : Fin 2 → ℕ) n p + q := by
    simp [q]
  conv_rhs => rw [hdecomp, map_add, DirectSum.add_apply]
  suffices h : (evalE₄E₆ q) (↑n : ℤ) = 0 by rw [h, add_zero]
  rw [← MvPolynomial.support_sum_monomial_coeff q, map_sum, DirectSum.sum_apply]
  refine Finset.sum_eq_zero fun d hd ↦
    evalE₄E₆_monomial_apply_eq_zero_of_ne _ _ _ fun heq ↦ MvPolynomial.mem_support_iff.mp hd ?_
  rw [hq_def, MvPolynomial.coeff_sub, MvPolynomial.coeff_weightedHomogeneousComponent,
    ite_eq_left ?_, sub_self]
  rw [weight_eq_4a_6b]
  lia

private lemma X0_pow_mul_X1_pow_isWeightedHomogeneous (a b n : ℕ) (hab : a * 4 + b * 6 = n) :
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ)
      (MvPolynomial.X (0 : Fin 2) ^ a * MvPolynomial.X (1 : Fin 2) ^ b :
        MvPolynomial (Fin 2) ℂ) n := by
  convert
    ((MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (0 : Fin 2)).pow a).mul
      ((MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (1 : Fin 2)).pow b)
    using 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  lia

private lemma discriminantPoly_isWeightedHomogeneous :
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) discriminantPoly 12 := by
  rw [discriminantPoly, MvPolynomial.smul_eq_C_mul]
  refine MvPolynomial.IsWeightedHomogeneous.C_mul (.sub ?_ ?_) _
  · exact (MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (0 : Fin 2)).pow 3
  · exact (MvPolynomial.isWeightedHomogeneous_X ℂ (![4, 6] : Fin 2 → ℕ) (1 : Fin 2)).pow 2

private lemma evalE₄E₆_discriminantPoly_mul_apply {n : ℕ}
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12))
    (hcast : (12 : ℤ) + ((n - 12 : ℕ) : ℤ) = (↑n : ℤ)) :
    (evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ) =
      hcast ▸ GradedMonoid.GMul.mul (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
        ((evalE₄E₆ s) ↑(n - 12)) := by
  conv_lhs => rw [map_mul, evalE₄E₆_discriminantPoly, evalE₄E₆_eq_of_apply (n - 12) s hs,
    DirectSum.of_mul_of, DirectSum.of_apply, dite_eq_left hcast]

private lemma evalE₄E₆_discriminantPoly_mul_coeff_zero {n : ℕ} (hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12)) :
    (qExpansion 1 ↑((evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ))).coeff 0 = 0 := by
  have hcast : (12 : ℤ) + ((n - 12 : ℕ) : ℤ) = (↑n : ℤ) := by lia
  rw [evalE₄E₆_discriminantPoly_mul_apply s hs hcast]
  set f := (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  set g := (evalE₄E₆ s) ((n - 12 : ℕ) : ℤ)
  -- Transporting along the degree identity does not change pointwise values
  -- (`cast_apply`); `show` states the function-level identification.
  rw [show ((hcast ▸ GradedMonoid.GMul.mul f g : ModularForm 𝒮ℒ ↑n) : ℍ → ℂ) =
      ((f.mul g : ModularForm 𝒮ℒ (12 + ((n - 12 : ℕ) : ℤ))) : ℍ → ℂ) from
        funext fun z ↦ cast_apply hcast _ z,
    ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL f g, PowerSeries.coeff_mul]
  simp [(ModularForm.isCuspForm_iff_coeffZero_eq_zero f).mp ⟨CuspForm.discriminant, rfl⟩]

private lemma per_weight_injective_unique_monomial {n : ℕ} (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (d₀ : Fin 2 →₀ ℕ)
    (huniq : ∀ d : Fin 2 →₀ ℕ, Finsupp.weight (![4, 6] : Fin 2 → ℕ) d = n → d = d₀)
    (hmf_ne : (DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ d₀ 0 *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ d₀ 1) (↑n : ℤ) ≠ 0) : p = 0 := by
  have hpc := hp.eq_monomial_of_unique_weight huniq
  rw [hpc] at heval ⊢
  rw [MvPolynomial.monomial_fin_two, mul_assoc, map_mul,
    evalE₄E₆_C _,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, evalE₄E₆_monomial,
    DirectSum.smul_apply] at heval
  rcases smul_eq_zero.mp heval with hc | hmz
  · rw [hc, MvPolynomial.monomial_zero]
  · exact absurd hmz hmf_ne

private lemma per_weight_injective_small {n : ℕ} (a b : ℕ) (hn : n < 12)
    (hab : 4 * a + 6 * b = n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0) : p = 0 := by
  have ha : a < 3 := by lia
  obtain ⟨d₀, hd0a, hd0b⟩ : ∃ d : Fin 2 →₀ ℕ, d 0 = a ∧ d 1 = b :=
    ⟨Finsupp.equivFunOnFinite.invFun ![a, b], rfl, rfl⟩
  apply per_weight_injective_unique_monomial p hp heval d₀
  · intro d hd
    have h46 := weight_eq_4a_6b d
    rw [hd] at h46
    obtain ⟨hda, hdb⟩ := unique_small_weight_solution (by lia : d 0 < 3) ha
      (show d 0 * 4 + d 1 * 6 = a * 4 + b * 6 by lia)
    ext i
    fin_cases i <;> [exact hda ▸ hd0a.symm; exact hdb ▸ hd0b.symm]
  · rw [hd0a, hd0b]
    intro habs
    have hcz := monomial_qExpansion_coeff_zero_eq_one (n := n) (a := a) (b := b) (by lia)
    rw [habs] at hcz
    simp [UpperHalfPlane.qExpansion_zero] at hcz

private lemma per_weight_injective_zero
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p 0)
    (heval : (evalE₄E₆ p) (0 : ℤ) = 0) : p = 0 := by
  have hpc : p = MvPolynomial.monomial (0 : Fin 2 →₀ ℕ) (p.coeff 0) :=
    hp.eq_monomial_of_unique_weight (d₀ := 0) (fun d hd ↦ by
      rw [weight_eq_4a_6b] at hd
      ext i
      fin_cases i <;> simp <;> lia)
  rw [hpc, MvPolynomial.monomial_zero'] at heval ⊢
  -- The degree-`0` component of the graded unit is the unit form; `show` states the
  -- component extraction so `of_eq_same` can close it.
  rw [evalE₄E₆_C _, Algebra.algebraMap_eq_smul_one, DirectSum.smul_apply,
    show (1 : DirectSum ℤ (ModularForm 𝒮ℒ)) (0 : ℤ) = (1 : ModularForm 𝒮ℒ 0) from by
      conv_lhs => rw [← DirectSum.of_zero_one (ModularForm 𝒮ℒ)]
      exact DirectSum.of_eq_same _ _] at heval
  rcases smul_eq_zero.mp heval with hc | h1z
  · simp [hc]
  · exact absurd h1z one_ne_zero_modularForm

private lemma discriminantPoly_piece_isWeightedHomogeneous {n : ℕ}
    (d : Fin 2 →₀ ℕ) (hd_ge : 3 ≤ d 0) (hwd : d 0 * 4 + d 1 * 6 = n) (c : ℂ) :
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ)
      (MvPolynomial.C c * ((1728 : ℂ) • discriminantPoly *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
          MvPolynomial.X (1 : Fin 2) ^ (d 1)))) n := by
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  rw [MvPolynomial.smul_eq_C_mul, mul_assoc]
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  convert discriminantPoly_isWeightedHomogeneous.mul
    (X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12) (by lia))
    using 1
  lia

private lemma discriminantPoly_piece_eq_monomial_sub
    (d : Fin 2 →₀ ℕ) (hd_ge : 3 ≤ d 0) (c : ℂ) :
    MvPolynomial.C c * ((1728 : ℂ) • discriminantPoly *
        (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)) =
    MvPolynomial.monomial d c - MvPolynomial.monomial
      (Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)) c := by
  have hX0 : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ d 0 =
      MvPolynomial.X 0 ^ 3 * MvPolynomial.X 0 ^ (d 0 - 3) := by
    rw [← pow_add]
    congr 1
    lia
  have h0 : (Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)) 0
      = d 0 - 3 := by simp
  have h1 : (Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)) 1
      = d 1 + 2 := by simp
  rw [discriminantPoly_smul_eq, MvPolynomial.monomial_fin_two, MvPolynomial.monomial_fin_two,
    h0, h1, hX0, pow_add (MvPolynomial.X (1 : Fin 2)) (d 1) 2]
  ring

private lemma support_degreeSum_lt_of_sub_discriminantPoly_piece (p : MvPolynomial (Fin 2) ℂ)
    {d : Fin 2 →₀ ℕ} (hd_mem : d ∈ p.support) (hd_ge : 3 ≤ d 0) :
    ∑ d' ∈ (p - MvPolynomial.C (p.coeff d) * ((1728 : ℂ) • discriminantPoly *
          (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) *
            MvPolynomial.X (1 : Fin 2) ^ d 1))).support, d' 0 <
      ∑ d' ∈ p.support, d' 0 := by
  set d' := Finsupp.single (0 : Fin 2) (d 0 - 3) + Finsupp.single (1 : Fin 2) (d 1 + 2)
  have hdd' : d ≠ d' := fun heq ↦ by
    have h0 := Finsupp.ext_iff.mp heq (0 : Fin 2)
    simp only [Fin.isValue, d', Finsupp.add_apply, Finsupp.single_eq_same,
      ne_eq, zero_ne_one, not_false_eq_true, Finsupp.single_eq_of_ne, add_zero] at h0
    lia
  have hsupp := (discriminantPoly_piece_eq_monomial_sub d hd_ge _ : _ = _) ▸
    MvPolynomial.support_sub_monomial_sub_monomial_subset p d d' _ hdd' rfl
  refine Finset.sum_lt_sum_of_subset_erase_union_singleton hd_mem hsupp ?_
  simp [d', Finsupp.add_apply]
  lia

private lemma weightedHomogeneous_poly_Delta_decomp_step {n : ℕ}
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (hnotall : ¬ ∀ d ∈ p.support, d 0 < 3) :
    ∃ p' q₁ : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p' n ∧
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) q₁ (n - 12) ∧
      p = p' + discriminantPoly * q₁ ∧
      ∑ d ∈ p'.support, d 0 < ∑ d ∈ p.support, d 0 := by
  push Not at hnotall
  obtain ⟨d, hd_mem, hd_ge⟩ := hnotall
  have hwd : d 0 * 4 + d 1 * 6 = n := by
    have := (weight_eq_4a_6b d).symm.trans <| hp <| MvPolynomial.mem_support_iff.mp hd_mem
    lia
  set c := p.coeff d
  set δ_piece := MvPolynomial.C c * ((1728 : ℂ) • discriminantPoly *
    (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1))
  set q₁ := MvPolynomial.C (c * 1728) *
    (MvPolynomial.X (0 : Fin 2) ^ (d 0 - 3) * MvPolynomial.X (1 : Fin 2) ^ d 1)
  have hδ_eq : δ_piece = discriminantPoly * q₁ := by
    simp only [δ_piece, q₁, MvPolynomial.smul_eq_C_mul, map_mul]
    ring
  refine ⟨p - δ_piece, q₁, hp.sub
      (discriminantPoly_piece_isWeightedHomogeneous d hd_ge hwd c),
    .C_mul (X0_pow_mul_X1_pow_isWeightedHomogeneous (d 0 - 3) (d 1) (n - 12) (by lia)) _, ?_,
    support_degreeSum_lt_of_sub_discriminantPoly_piece p hd_mem hd_ge⟩
  rw [← hδ_eq]
  ring

private lemma weightedHomogeneous_poly_Delta_decomp {n : ℕ}
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n) :
    ∃ r s : MvPolynomial (Fin 2) ℂ,
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) r n ∧
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12) ∧
      p = r + discriminantPoly * s ∧
      (∀ d ∈ r.support, d 0 < 3) := by
  generalize hM : ∑ d ∈ p.support, d 0 = M
  induction M using Nat.strong_induction_on generalizing p with | _ M ih => ?_
  by_cases hall : ∀ d ∈ p.support, d 0 < 3
  · exact ⟨p, 0, hp, MvPolynomial.isWeightedHomogeneous_zero ℂ _ _,
      by simp only [mul_zero, add_zero], hall⟩
  obtain ⟨p', q₁, hp'_wh, hq₁_wh, hp_eq, hlt⟩ :=
    weightedHomogeneous_poly_Delta_decomp_step p hp hall
  obtain ⟨r, s', hr_wh, hs'_wh, hp'_eq, hr_red⟩ :=
    ih _ (hM ▸ hlt) p' hp'_wh rfl
  refine ⟨r, s' + q₁, hr_wh, hs'_wh.add hq₁_wh, ?_, hr_red⟩
  rw [hp_eq, hp'_eq, mul_add]
  ring

private lemma reduced_isWeightedHomogeneous_eq_monomial {n : ℕ}
    (r : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) r n)
    (hr_red : ∀ d ∈ r.support, d 0 < 3) {d₀ : Fin 2 →₀ ℕ} (hd₀ : d₀ ∈ r.support) :
    r = MvPolynomial.monomial d₀ (r.coeff d₀) := by
  ext d
  rw [MvPolynomial.coeff_monomial]
  by_cases hd : d = d₀
  · simp [hd]
  rw [ite_eq_right (Ne.symm hd)]
  by_cases hd_supp : d ∈ r.support
  · obtain ⟨ha, hb⟩ := unique_small_weight_solution (hr_red d hd_supp) (hr_red d₀ hd₀)
      (by rw [← weight_eq_4a_6b, ← weight_eq_4a_6b,
        hr (MvPolynomial.mem_support_iff.mp hd_supp), hr (MvPolynomial.mem_support_iff.mp hd₀)])
    exact absurd (Finsupp.ext fun i ↦ by fin_cases i <;> [exact ha; exact hb]) hd
  · rwa [MvPolynomial.mem_support_iff, not_not] at hd_supp

private lemma evalE₄E₆_monomial_qExpansion_coeff_zero {n : ℕ} {d₀ : Fin 2 →₀ ℕ}
    (hd₀_weight : 4 * d₀ 0 + 6 * d₀ 1 = n) (c : ℂ) :
    (qExpansion 1 ↑((evalE₄E₆ (MvPolynomial.monomial d₀ c)) (↑n : ℤ))).coeff 0 = c := by
  rw [MvPolynomial.monomial_fin_two, mul_assoc, map_mul,
    evalE₄E₆_C _,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, evalE₄E₆_monomial,
    DirectSum.smul_apply,
    -- Scalar action commutes with the coercion to functions
    -- (`FunLike.coe_smul`); the ascribed `show` pins the statement at the
    -- right type.
    show (↑(c • ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ d₀ 0 *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ d₀ 1) (↑n : ℤ))) : ℍ → ℂ) =
      c • (↑((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ d₀ 0 *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ d₀ 1) (↑n : ℤ)) : ℍ → ℂ) from
      FunLike.coe_smul c _,
    UpperHalfPlane.qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero _
      one_pos one_mem_strictPeriods_SL) c, PowerSeries.coeff_smul,
    monomial_qExpansion_coeff_zero_eq_one hd₀_weight]
  simp

private lemma reduced_part_eq_zero {n : ℕ} (hn12 : 12 ≤ n)
    (r s : MvPolynomial (Fin 2) ℂ)
    (hr : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) r n)
    (hs : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12))
    (hr_red : ∀ d ∈ r.support, d 0 < 3)
    (heval : (evalE₄E₆ (r + discriminantPoly * s)) (↑n : ℤ) = 0) :
    r = 0 := by
  by_cases hr_empty : r.support = ∅
  · rwa [MvPolynomial.support_eq_empty] at hr_empty
  obtain ⟨d₀, hd₀⟩ := Finset.nonempty_of_ne_empty hr_empty
  have hr_mono := reduced_isWeightedHomogeneous_eq_monomial r hr hr_red hd₀
  set c := r.coeff d₀
  suffices hc : c = 0 by rw [hr_mono, hc, MvPolynomial.monomial_zero]
  have hd₀_weight : 4 * d₀ 0 + 6 * d₀ 1 = n := by
    have := (weight_eq_4a_6b d₀).symm.trans (hr (MvPolynomial.mem_support_iff.mp hd₀))
    lia
  rw [hr_mono, map_add, DirectSum.add_apply] at heval
  set Q := ModularForm.qExpansionAddHom (h := 1) one_pos one_mem_strictPeriods_SL (↑n : ℤ)
  have hQ : (Q ((evalE₄E₆ (MvPolynomial.monomial d₀ c)) (↑n : ℤ))).coeff 0 +
      (Q ((evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ))).coeff 0 = 0 := by
    rw [← LinearMap.map_add, ← Q.map_add, heval, map_zero, map_zero]
  -- Name the two constant coefficients through `Q`: the discriminant part vanishes,
  -- the monomial part is the coefficient itself.
  rw [show (Q ((evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ))).coeff 0 = 0 from
      evalE₄E₆_discriminantPoly_mul_coeff_zero hn12 s hs, add_zero,
    show (Q ((evalE₄E₆ (MvPolynomial.monomial d₀ c)) (↑n : ℤ))).coeff 0 = c from
      evalE₄E₆_monomial_qExpansion_coeff_zero hd₀_weight c] at hQ
  exact hQ

private lemma eval_discriminantPoly_mul_eq_zero_imp_eval_eq_zero {n : ℕ} (hn12 : 12 ≤ n)
    (s : MvPolynomial (Fin 2) ℂ)
    (hs : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) s (n - 12))
    (hds : (evalE₄E₆ (discriminantPoly * s)) (↑n : ℤ) = 0) :
    (evalE₄E₆ s) (↑(n - 12) : ℤ) = 0 := by
  have hcast : (12 : ℤ) + ((n - 12 : ℕ) : ℤ) = (↑n : ℤ) := by lia
  rw [evalE₄E₆_discriminantPoly_mul_apply s hs hcast] at hds
  ext z
  have hpw := DFunLike.congr_fun hds z
  simp only [_root_.zero_apply, cast_apply hcast] at hpw ⊢
  exact (mul_eq_zero.mp hpw).resolve_left (discriminant_ne_zero z)

private lemma per_weight_injective_inductive_step (n : ℕ)
    (ih : ∀ m < n, ∀ (p : MvPolynomial (Fin 2) ℂ),
      MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p m →
        (evalE₄E₆ p) (↑m : ℤ) = 0 → p = 0)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0)
    (hn12 : 12 ≤ n) : p = 0 := by
  obtain ⟨r, s, hr_wh, hs_wh, hp_eq, hr_red⟩ := weightedHomogeneous_poly_Delta_decomp p hp
  have hr0 : r = 0 := reduced_part_eq_zero hn12 r s hr_wh hs_wh hr_red (hp_eq ▸ heval)
  rw [hp_eq, hr0, zero_add] at heval ⊢
  rw [ih (n - 12) (by lia) s hs_wh
    (eval_discriminantPoly_mul_eq_zero_imp_eval_eq_zero hn12 s hs_wh heval), mul_zero]

private lemma per_weight_injective_at_small_weight {n : ℕ} (hn12 : n < 12) (hk_even : Even n)
    (p : MvPolynomial (Fin 2) ℂ)
    (hp : MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n)
    (heval : (evalE₄E₆ p) (↑n : ℤ) = 0) : p = 0 := by
  obtain rfl | rfl | rfl | rfl | rfl | rfl :
      n = 0 ∨ n = 2 ∨ n = 4 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by
    rcases hk_even with ⟨m, hm⟩
    lia
  · exact per_weight_injective_zero p hp heval
  · exact hp.eq_zero_of_no_monomials fun d h ↦ by rw [weight_eq_4a_6b] at h; lia
  · exact per_weight_injective_small 1 0 (by lia) rfl p hp heval
  · exact per_weight_injective_small 0 1 (by lia) rfl p hp heval
  · exact per_weight_injective_small 2 0 (by lia) rfl p hp heval
  · exact per_weight_injective_small 1 1 (by lia) rfl p hp heval

private lemma per_weight_injective : ∀ (n : ℕ) (p : MvPolynomial (Fin 2) ℂ),
    MvPolynomial.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) p n →
    (evalE₄E₆ p) (↑n : ℤ) = 0 → p = 0 := by
  intro n
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro p hp heval
  by_cases hk_odd : Odd n
  · exact hp.eq_zero_of_no_monomials (no_weight_monomial_of_odd hk_odd)
  rw [Nat.not_odd_iff_even] at hk_odd
  by_cases hn12 : n < 12
  · exact per_weight_injective_at_small_weight hn12 hk_odd p hp heval
  push Not at hn12
  exact per_weight_injective_inductive_step n ih p hp heval hn12

/-- The evaluation homomorphism `evalE₄E₆` is injective: `E₄` and `E₆` are algebraically
independent. -/
theorem evalE₄E₆_injective : Function.Injective evalE₄E₆ := by
  intro p q hpq
  rw [← sub_eq_zero,
    ← MvPolynomial.sum_weightedHomogeneousComponent ((![4, 6] : Fin 2 → ℕ)) (p - q)]
  refine finsum_eq_zero_of_forall_eq_zero fun n ↦ per_weight_injective n _
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous _ _) ?_
  rw [evalE₄E₆_component_eq, map_sub, hpq, sub_self, DirectSum.zero_apply]

/-- The graded ring of level-1 modular forms is isomorphic to the polynomial ring
`ℂ[X₀, X₁]` via evaluation at `E₄` and `E₆`. -/
noncomputable def mvPolynomialEquivModularForms :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩

@[simp]
lemma mvPolynomialEquivModularForms_apply (p : MvPolynomial (Fin 2) ℂ) :
    mvPolynomialEquivModularForms p = evalE₄E₆ p := by
  -- `change` exposes the sealed definition once, explicitly; the identification is
  -- then Mathlib's `AlgEquiv.ofBijective_apply`.
  change AlgEquiv.ofBijective evalE₄E₆ ⟨evalE₄E₆_injective, evalE₄E₆_surjective⟩ p = evalE₄E₆ p
  exact AlgEquiv.ofBijective_apply _ _ p

/-- The graded ring of level-1 modular forms is an integral domain, being isomorphic (via
`mvPolynomialEquivModularForms`) to the polynomial ring `ℂ[X₀, X₁]`. -/
instance : IsDomain (DirectSum ℤ (ModularForm 𝒮ℒ)) :=
  mvPolynomialEquivModularForms.symm.toMulEquiv.isDomain _

end ModularForm

end
