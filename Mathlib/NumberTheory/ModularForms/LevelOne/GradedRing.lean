/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-!
# The graded ring of level-1 modular forms

This file collects structural results about the graded ring `⨁ k, ModularForm 𝒮ℒ k` of
level-1 modular forms, beyond those that fall out of the dimension formula directly. In
particular, every level-1 modular form is a polynomial in the Eisenstein series `E₄` and `E₆`.

## Main definitions

* `ModularForm.evalE₄E₆`: the evaluation homomorphism
  `ℂ[X₀, X₁] →ₐ[ℂ] ⨁ k, ModularForm 𝒮ℒ k` sending `X₀ ↦ E₄` and `X₁ ↦ E₆`.

## Main results

* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq`: the pointwise identity
  `Δ = (E₄³ - E₆²) / 1728`.
* `ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq_graded`: the same identity in the graded
  ring `⨁ k, ModularForm 𝒮ℒ k`.
* `ModularForm.evalE₄E₆_surjective`: `evalE₄E₆` is surjective.
* `ModularForm.adjoin_E₄_E₆_eq_top`: `E₄` and `E₆` generate `⨁ k, ModularForm 𝒮ℒ k` as a
  `ℂ`-algebra; in particular it is a finitely generated `ℂ`-algebra and a Noetherian ring.

## Implementation notes

Surjectivity is proved by induction on the weight `k`. Forms of negative or odd weight, or of
weight `2`, vanish. Otherwise `k = 4 * a + 6 * b` for some `a b : ℕ`, and subtracting a multiple
of `E₄ ^ a * E₆ ^ b` from a form `f` of weight `k` leaves a cusp form. That cusp form is `Δ`
times a form of weight `k - 12` (`CuspForm.discriminantEquiv`), which is a polynomial in `E₄` and
`E₆` by induction, and so is `Δ = (E₄³ - E₆²) / 1728`. The same step covers the weights `k < 12`,
where the form of weight `k - 12` is zero.

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

end ModularForm

end
