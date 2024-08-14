/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Heights on Weierstrass curves
-/

open IsDedekindDomain NumberField

universe u v

theorem one_le_finprod {α : Type u} {M : Type v} [OrderedCommSemiring M] {f : α → M}
    (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul_of_one_le_of_one_le) hf

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K]

noncomputable def IsDedekindDomain.HeightOneSpectrum.realValuation (v : HeightOneSpectrum R)
    (x : K) : ℝ :=
  (v.valuation x).casesOn 0 (fun x => (Nat.card <| R ⧸ v.asIdeal : ℝ) ^ Multiplicative.toAdd x)

variable [NumberField K]

namespace NumberField

variable (K) in
def Place : Type v :=
  HeightOneSpectrum (𝓞 K) ⊕ InfinitePlace K

noncomputable def Place.valuation (v : Place K) (x : K) : ℝ :=
  v.casesOn (fun v => v.realValuation x) (fun v => v x)

-- TODO: define the prime p below v and [Kᵥ : ℚₚ]
open Classical in
noncomputable def Place.localDegree (v : Place K) : ℕ :=
  v.casesOn (fun v => sorry) (fun v => if v.IsReal then 1 else 2)

end NumberField

namespace WeierstrassCurve.Affine.Point

variable {W : Affine K}

/-! ### The naive height -/

/-- The naive height of a point on a Weierstrass curve. -/
noncomputable def naiveHeight : W.Point → ℝ
  | zero => 1
  | @some _ _ _ x _ _ => (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.localDegree)) ^
    (1 / FiniteDimensional.finrank ℚ K : ℝ)

@[simp]
lemma naiveHeight_zero : (0 : W.Point).naiveHeight = 1 :=
  rfl

@[simp]
lemma naiveHeight_some {x y : K} (h : W.Nonsingular x y) : (some h).naiveHeight =
    (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.localDegree)) ^
      (1 / FiniteDimensional.finrank ℚ K : ℝ) :=
  rfl

lemma naiveHeight_neg (P : W.Point) : (-P).naiveHeight = P.naiveHeight := by
  cases P <;> rfl

private lemma one_le_prod {x : K} : 1 ≤ ∏ᶠ v : Place K, max 1 (v.valuation x ^ v.localDegree) :=
  one_le_finprod fun _ => le_max_left ..

lemma naiveHeight_ge_one (P : W.Point) : 1 ≤ P.naiveHeight := by
  rcases P with _ | _
  · rfl
  · exact Real.one_le_rpow one_le_prod <| one_div_nonneg.mpr <| Nat.cast_nonneg _

/-! ### The logarithmic height -/

/-- The logarithmic height of a point on a Weierstrass curve. -/
noncomputable def logHeight (P : W.Point) : ℝ :=
  P.naiveHeight.log

@[simp]
lemma logHeight_zero : (0 : W.Point).logHeight = 0 :=
  Real.log_one

@[simp]
lemma logHeight_some {x y : K} (h : W.Nonsingular x y) : (some h).logHeight =
    (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.localDegree)).log /
      FiniteDimensional.finrank ℚ K := by
  erw [logHeight, Real.log_rpow <| one_pos.trans_le one_le_prod, one_div_mul_eq_div]

lemma logHeight_neg (P : W.Point) : (-P).logHeight = P.logHeight := by
  cases P <;> rfl

lemma logHeight_nonneg (P : W.Point) : 0 ≤ P.logHeight :=
  Real.log_nonneg P.naiveHeight_ge_one

-- TODO: difficult
/-- The logarithmic height satisfies the parallelogram law of a quadratic form up to a constant. -/
theorem logHeight_quadratic : ∃ C : ℝ, ∀ P Q : W.Point,
    |(P + Q).logHeight + (P - Q).logHeight - (2 * P.logHeight + 2 * Q.logHeight)| ≤ C :=
  sorry

lemma logHeight_add_sub_two_mul (Q : W.Point) : ∃ C : ℝ, ∀ P : W.Point,
    (P + Q).logHeight - 2 * P.logHeight ≤ C := by
  rcases logHeight_quadratic (W := W) with ⟨C, h⟩
  exact ⟨2 * Q.logHeight + C,
    fun P => by linarith only [abs_le.mp <| h P Q, (P - Q).logHeight_nonneg]⟩

lemma logHeight_smul_sub_sq_mul (n : ℤ) : ∃ C : ℝ, ∀ P : W.Point,
    |(n • P).logHeight - n ^ 2 * P.logHeight| ≤ C := by
  induction n using Int.negInduction with
  | nat n => induction n using Nat.strongRec with
    | ind n ih =>
      rcases n with _ | _ | n; exact ⟨0, by simp⟩; exact ⟨0, by simp⟩
      · simp only [← nsmul_eq_smul_cast, Int.cast_natCast] at ih ⊢
        rcases ih n <| by linarith only with ⟨C', h'⟩
        rcases ih (n + 1) <| by linarith only with ⟨C'', h''⟩
        push_cast [add_smul, one_smul] at h'' ⊢
        rcases logHeight_quadratic (W := W) with ⟨C, h⟩
        refine ⟨C + C' + 2 * C'', fun P => abs_le.mpr ⟨?_, ?_⟩⟩
        all_goals linarith only [abs_le.mp <| add_sub_cancel_right _ P ▸ h (n • P + P) P,
          abs_le.mp <| h' P, abs_le.mp <| h'' P]
  | neg => simpa only [neg_smul, logHeight_neg, Int.cast_neg, neg_sq]

/-! ### The canonical height -/

/-- The Cauchy sequence of logarithmic heights used to construct the canonical height. -/
noncomputable def canonHeightSeq (P : W.Point) (n : ℕ) : ℝ :=
  ((2 ^ n) • P).logHeight / 4 ^ n

lemma cauchySeq_canonHeightSeq (P : W.Point) : CauchySeq P.canonHeightSeq := by
  rcases logHeight_smul_sub_sq_mul 2 (W := W) with ⟨C, h⟩
  refine cauchySeq_of_le_geometric (1 / 4) (C / 4) (by norm_num1) fun n => ?_
  rw [dist_comm, Real.dist_eq, canonHeightSeq, pow_succ', mul_smul, canonHeightSeq,
    ← mul_div_mul_left _ (4 ^ n) four_ne_zero, ← pow_succ', div_sub_div_same, abs_div, abs_pow,
    Nat.abs_ofNat, one_div_pow, mul_one_div, div_div, ← pow_succ',
    div_le_div_right <| pow_pos four_pos _, show (4 : ℝ) = (2 ^ 2) by norm_num1]
  exact h <| 2 ^ n • P

/-- The canonical height of a point on a Weierstrass curve. -/
noncomputable def canonHeight (P : W.Point) : ℝ :=
  (cauchySeq_tendsto_of_complete P.cauchySeq_canonHeightSeq).choose

lemma canonHeightSeq_tendsto_canonHeight (P : W.Point) :
    Filter.atTop.Tendsto P.canonHeightSeq <| nhds P.canonHeight :=
  (cauchySeq_tendsto_of_complete P.cauchySeq_canonHeightSeq).choose_spec

end WeierstrassCurve.Affine.Point
