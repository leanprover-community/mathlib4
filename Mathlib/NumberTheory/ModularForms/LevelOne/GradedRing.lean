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
  `ℂ`-algebra; in particular it is a finitely generated `ℂ`-algebra.

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
level-1 modular forms, sending `X₀ = MvPolynomial.X 0` to `E₄` in weight `4` and
`X₁ = MvPolynomial.X 1` to `E₆` in weight `6`; thus the monomial `X₀ ^ a * X₁ ^ b` maps to
`E₄ ^ a * E₆ ^ b`, of weight `4 * a + 6 * b`. It is surjective by `evalE₄E₆_surjective`. -/
def evalE₄E₆ : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] DirectSum ℤ (ModularForm 𝒮ℒ) :=
  MvPolynomial.aeval ![DirectSum.of (ModularForm 𝒮ℒ) 4 E₄, DirectSum.of (ModularForm 𝒮ℒ) 6 E₆]

@[simp]
lemma evalE₄E₆_X_zero : evalE₄E₆ (MvPolynomial.X 0) = DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ := by
  simp [evalE₄E₆]

@[simp]
lemma evalE₄E₆_X_one : evalE₄E₆ (MvPolynomial.X 1) = DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ := by
  simp [evalE₄E₆]

private lemma E₄_mem_range : DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ∈ evalE₄E₆.range :=
  ⟨_, evalE₄E₆_X_zero⟩

private lemma E₆_mem_range : DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ∈ evalE₄E₆.range :=
  ⟨_, evalE₄E₆_X_one⟩

private lemma discriminant_mem_range :
    DirectSum.of (ModularForm 𝒮ℒ) 12
      ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) ∈ evalE₄E₆.range := by
  rw [discriminant_eq_E₄_cube_sub_E₆_sq_graded]
  exact Subalgebra.smul_mem _ (sub_mem (pow_mem E₄_mem_range 3) (pow_mem E₆_mem_range 2)) _

private lemma exists_monomial_weight {k : ℕ} (hk : k ≠ 2) (hkeven : Even k) :
    ∃ a b : ℕ, 4 * a + 6 * b = k := by
  obtain ⟨m, rfl⟩ := hkeven
  rcases Nat.even_or_odd m with ⟨n, hn⟩ | ⟨n, hn⟩
  exacts [⟨n, 0, by lia⟩, ⟨n - 1, 1, by lia⟩]

private lemma directSum_of_E₄_pow_mul_E₆_pow_apply {a b n : ℕ}
    (hab : 4 * a + 6 * b = n) :
    DirectSum.of (ModularForm 𝒮ℒ) (↑n : ℤ)
        ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
          DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (↑n : ℤ)) =
      DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b := by
  -- The graded degree of `E₄^a * E₆^b` is `a • 4 + b • 6`; reshape the index `n` into
  -- that form so that `of_eq_same` extracts the component.
  rw [DirectSum.ofPow, DirectSum.ofPow, DirectSum.of_mul_of,
    show (↑n : ℤ) = a • (4 : ℤ) + b • (6 : ℤ) by
      simp only [Int.nsmul_eq_mul]
      push_cast [← hab]
      ring,
    DirectSum.of_eq_same]

/-- Transport along the ring homomorphism `qExpansionRingHom`: the `q`-expansion of the
weight-`n` component of `E₄^a * E₆^b` is the product of the `q`-expansions. -/
private lemma qExpansion_of_E₄_pow_mul_E₆_pow {n a b : ℕ} (hab : 4 * a + 6 * b = n) :
    qExpansion 1 ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
      DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (n : ℤ)) =
      qExpansion 1 E₄ ^ a * qExpansion 1 E₆ ^ b := by
  rw [← ModularForm.qExpansionRingHom_apply (h := 1) one_pos one_mem_strictPeriods_SL,
    directSum_of_E₄_pow_mul_E₆_pow_apply hab, map_mul, map_pow, map_pow,
    ModularForm.qExpansionRingHom_apply, ModularForm.qExpansionRingHom_apply]

private lemma monomial_qExpansion_coeff_zero_eq_one {n a b : ℕ} (hab : 4 * a + 6 * b = n) :
    (qExpansion 1
      ((DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a *
        DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) (n : ℤ))).coeff 0 = 1 := by
  -- Both Eisenstein series are normalized to constant term `1`, so the zeroth
  -- coefficient of the product of their powers is `1`.
  rw [qExpansion_of_E₄_pow_mul_E₆_pow hab, PowerSeries.coeff_mul]
  simp [PowerSeries.coeff_pow,
    E_qExpansion_coeff_zero _ ⟨2, rfl⟩, E_qExpansion_coeff_zero _ ⟨3, rfl⟩]

private lemma cuspForm_eq_discriminant_mul {n : ℕ} (g : ModularForm 𝒮ℒ ↑n)
    (hg : ModularForm.IsCuspForm g) :
    DirectSum.of (ModularForm 𝒮ℒ) (↑n : ℤ) g =
      DirectSum.of (ModularForm 𝒮ℒ) (↑n - 12 : ℤ)
        (CuspForm.discriminantEquiv (ModularForm.toCuspForm g
          ((ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp hg))) *
        DirectSum.of (ModularForm 𝒮ℒ) 12
          ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12) := by
  rw [DirectSum.of_mul_of]
  symm
  -- The degrees agree because `(n − 12) + 12 = n`; the goal is definitionally that
  -- integer identity, exposed by `change`.
  refine DirectSum.of_eq_of_gradedMonoid_eq
    (ModularForm.gradedMonoid_eq_of_cast (by change (↑n - 12 + 12 : ℤ) = ↑n; ring) ?_)
  refine DFunLike.coe_injective ?_
  have hcusp := (ModularForm.isCuspForm_iff_coeffZero_eq_zero g).mp hg
  -- `mcast` along the degree identity does not change the underlying function, so the
  -- coercion goal is definitionally the product form; `change` exposes it.
  change ⇑((CuspForm.discriminantEquiv (ModularForm.toCuspForm g hcusp)).mul
      ((CuspForm.discriminant : CuspForm 𝒮ℒ 12) : ModularForm 𝒮ℒ 12)) = ⇑g
  rw [ModularForm.coe_mul, mul_comm]
  exact ModularForm.discriminant_mul_discriminantEquiv (ModularForm.toCuspForm g hcusp)

/-- The inductive step: if `4 * a + 6 * b = n` and every form of weight `n - 12` lies in the
range of `evalE₄E₆`, then so does every form `f` of weight `n`, since `f` minus its constant term
times `E₄ ^ a * E₆ ^ b` is `Δ` times a form of weight `n - 12`. -/
private lemma of_mem_range_of_sub_twelve {n a b : ℕ} (hab : 4 * a + 6 * b = n)
    (ih : ∀ g : ModularForm 𝒮ℒ ((n : ℤ) - 12), DirectSum.of _ _ g ∈ evalE₄E₆.range)
    (f : ModularForm 𝒮ℒ n) : DirectSum.of _ (n : ℤ) f ∈ evalE₄E₆.range := by
  set m := (DirectSum.of (ModularForm 𝒮ℒ) 4 E₄ ^ a * DirectSum.of (ModularForm 𝒮ℒ) 6 E₆ ^ b) n
  set c := (qExpansion 1 f).coeff 0
  have hcusp := sub_smul_isCuspForm f m (monomial_qExpansion_coeff_zero_eq_one hab)
  rw [← sub_add_cancel f (c • m), map_add, cuspForm_eq_discriminant_mul _ hcusp,
    DirectSum.of_smul, directSum_of_E₄_pow_mul_E₆_pow_apply hab]
  exact add_mem (mul_mem (ih _) discriminant_mem_range)
    (Subalgebra.smul_mem _ (mul_mem (pow_mem E₄_mem_range a) (pow_mem E₆_mem_range b)) c)

private lemma of_mem_range (k : ℤ) (f : ModularForm 𝒮ℒ k) :
    DirectSum.of _ k f ∈ evalE₄E₆.range := by
  have of_zero {k : ℤ} (f : ModularForm 𝒮ℒ k) (hf : f = 0) :
      DirectSum.of _ k f ∈ evalE₄E₆.range := by
    simp [hf, zero_mem]
  obtain hk | hk := lt_or_ge k 0
  · exact of_zero f (rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero hk) f)
  lift k to ℕ using hk
  induction k using Nat.strong_induction_on with | _ n ih => ?_
  by_cases hodd : Odd (n : ℤ)
  · exact of_zero f (levelOne_odd_weight_eq_zero hodd f)
  obtain rfl | h2 := eq_or_ne n 2
  · exact of_zero f (rank_zero_iff_forall_zero.mp levelOne_weight_two_rank_zero f)
  obtain ⟨a, b, hab⟩ := exists_monomial_weight h2 (by simpa [Int.not_odd_iff_even] using hodd)
  refine of_mem_range_of_sub_twelve hab (fun g ↦ ?_) f
  obtain hn | hn := lt_or_ge n 12
  · exact of_zero g (rank_zero_iff_forall_zero.mp (levelOne_neg_weight_rank_zero (by lia)) g)
  rw [← congr_eqRec (DirectSum.of _ ·) (show (n : ℤ) - 12 = (n - 12 : ℕ) by lia)]
  exact ih _ (by lia) _

/-- The evaluation homomorphism `evalE₄E₆` is surjective: every element of the graded ring
`⨁ k, ModularForm 𝒮ℒ k` of level-1 modular forms is a polynomial in `E₄` and `E₆`. -/
theorem evalE₄E₆_surjective : Function.Surjective evalE₄E₆ := by
  rw [← AlgHom.range_eq_top, eq_top_iff]
  rintro x -
  induction x using DirectSum.induction_on with
  | zero => exact zero_mem _
  | of k f => exact of_mem_range k f
  | add x y hx hy => exact add_mem hx hy

/-- `E₄` and `E₆` generate the graded ring `⨁ k, ModularForm 𝒮ℒ k` of level-1 modular forms
as a `ℂ`-algebra. -/
theorem adjoin_E₄_E₆_eq_top :
    Algebra.adjoin ℂ
      {DirectSum.of (ModularForm 𝒮ℒ) 4 E₄, DirectSum.of (ModularForm 𝒮ℒ) 6 E₆} = ⊤ := by
  rw [← Matrix.range_cons_cons_empty, Algebra.adjoin_range_eq_range_aeval]
  exact AlgHom.range_eq_top _ |>.mpr evalE₄E₆_surjective

/-- The graded ring of level-1 modular forms is a finitely generated `ℂ`-algebra. -/
instance : Algebra.FiniteType ℂ (DirectSum ℤ (ModularForm 𝒮ℒ)) :=
  .of_surjective evalE₄E₆ evalE₄E₆_surjective

end ModularForm

end
