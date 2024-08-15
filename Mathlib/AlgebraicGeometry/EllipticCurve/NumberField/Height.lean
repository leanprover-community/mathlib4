/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.LinearAlgebra.QuadraticForm.Basic
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

noncomputable def IsDedekindDomain.HeightOneSpectrum.realValuation {R : Type u} [CommRing R]
    [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (x : K) : ℝ :=
  (v.valuation x).casesOn 0 (fun x => (Nat.card <| R ⧸ v.asIdeal : ℝ) ^ Multiplicative.toAdd x)

def NumberField.Place (K : Type u) [Field K] [NumberField K] : Type u :=
  HeightOneSpectrum (𝓞 K) ⊕ InfinitePlace K

noncomputable def NumberField.Place.valuation {K : Type u} [Field K] [NumberField K] (v : Place K)
    (x : K) : ℝ :=
  v.casesOn (fun v => v.realValuation x) (fun v => v x)

-- TODO: define the prime p below v and [Kᵥ : ℚₚ]
open Classical in
noncomputable def NumberField.Place.localDegree {K : Type u} [Field K] [NumberField K]
    (v : Place K) : ℕ :=
  v.casesOn (fun v => sorry) (fun v => if v.IsReal then 1 else 2)

namespace ParMap

variable {A : Type u} {R : Type v} [AddCommGroup A] [CommRing R] [IsDomain R] [NeZero (2 : R)]

variable (A R) in
/-- The type of parallelogram maps `p : A → R` from an additive abelian group `A` to an integral
domain `R` of characteristic different from 2 satisfying the parallelogram law. -/
@[ext]
structure _root_.ParMap : Type (max u v) :=
  /-- The parallelogram map `p : A → R`. -/
  (toFun : A → R)
  /-- The parallelogram law `p (a + b) + p (a - b) = 2 * p a + 2 * p b`. -/
  (parLaw' : ∀ a b : A, toFun (a + b) + toFun (a - b) = 2 * toFun a + 2 * toFun b)

instance : FunLike (ParMap A R) A R where
  coe := toFun
  coe_injective' := ParMap.ext

variable (p : ParMap A R)

lemma parLaw (a b : A) : p (a + b) + p (a - b) = 2 * p a + 2 * p b :=
  p.parLaw' a b

@[simp]
lemma zero : p 0 = 0 :=
  mul_right_injective₀ two_ne_zero <| by linear_combination (norm := (simp; ring1)) -p.parLaw 0 0

@[simp]
lemma neg (a : A) : p (-a) = p a := by
  linear_combination (norm := (simp; ring1)) p.parLaw 0 a

@[simp]
lemma smul (a : A) (n : ℤ) : p (n • a) = n ^ 2 * p a := by
  induction n using Int.negInduction with
  | nat n => induction n using Nat.strongRec with
    | ind n ih =>
      rcases n with _ | _ | n; simp; simp
      simp only [← nsmul_eq_smul_cast] at ih ⊢
      linear_combination (norm := (push_cast [add_smul, one_smul, add_sub_cancel_right]; ring1))
        p.parLaw (n • a + a) a - ih n (by linarith only) + 2 * ih (n + 1) (by linarith only)
  | neg => rwa [neg_smul, neg, Int.cast_neg, neg_sq]

/-- The `ℤ`-bilinear function associated to a parallelogram map. -/
def bilinFun (a b : A) : R :=
  p (a + b) - p a - p b

lemma bilinFun_symm (a b : A) : p.bilinFun a b = p.bilinFun b a := by
  rw [bilinFun, add_comm, sub_right_comm, bilinFun]

@[simp]
lemma bilinFun_zero_left (b : A) : p.bilinFun 0 b = 0 := by
  rw [bilinFun, zero_add, zero, sub_zero, sub_self]

@[simp]
lemma bilinFun_zero_right (a : A) : p.bilinFun a 0 = 0 := by
  rw [bilinFun_symm, bilinFun_zero_left]

@[simp]
lemma bilinFun_add_left (a b c : A) : p.bilinFun (a + b) c = p.bilinFun a c + p.bilinFun b c :=
  mul_left_injective₀ two_ne_zero <| by
    linear_combination
      (norm := (simp_rw [bilinFun, add_assoc, add_comm, add_sub,sub_sub_eq_add_sub]; ring1))
      p.parLaw (a + c) b - p.parLaw a (c - b) + p.parLaw (a + b) c - 2 * p.parLaw c b

@[simp]
lemma bilinFun_add_right (a b c : A) : p.bilinFun a (b + c) = p.bilinFun a b + p.bilinFun a c := by
  rw [bilinFun_symm, bilinFun_add_left, bilinFun_symm, p.bilinFun_symm c]

@[simp]
lemma bilinFun_neg_left (a b : A) : p.bilinFun (-a) b = -p.bilinFun a b := by
  rw [eq_neg_iff_add_eq_zero, ← bilinFun_add_left, neg_add_self, bilinFun_zero_left]

@[simp]
lemma bilinFun_neg_right (a b : A) : p.bilinFun a (-b) = -p.bilinFun a b := by
  rw [bilinFun_symm, bilinFun_neg_left, bilinFun_symm]

@[simp]
lemma bilinFun_smul_left (n : ℤ) (a b : A) : p.bilinFun (n • a) b = n • p.bilinFun a b := by
  induction n using Int.negInduction with
  | nat n => induction n with
    | zero => simp
    | succ _ ih =>
      push_cast [← nsmul_eq_smul_cast, add_smul, one_smul, bilinFun_add_left] at ih ⊢
      rw [ih]
  | neg n ih => rw [neg_smul, bilinFun_neg_left, ih, neg_smul]

@[simp]
lemma bilinFun_smul_right (n : ℤ) (a b : A) : p.bilinFun a (n • b) = n • p.bilinFun a b := by
  rw [bilinFun_symm, bilinFun_smul_left, bilinFun_symm]

/-- The `ℤ`-bilinear map associated to a parallelogram map. -/
def bilinMap : LinearMap.BilinMap ℤ A R :=
  .mk₂ ℤ p.bilinFun p.bilinFun_add_left p.bilinFun_smul_left p.bilinFun_add_right
    p.bilinFun_smul_right

end ParMap

namespace WeierstrassCurve.Affine

variable {K : Type v} [Field K] [NumberField K] {W : Affine K}

/-! ### The naive height -/

variable (W) in
/-- The naive height of a point on a Weierstrass curve. -/
noncomputable def naiveHeight : W.Point → ℝ
  | .zero => 1
  | @Point.some _ _ _ x _ _ => (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.localDegree)) ^
    (1 / FiniteDimensional.finrank ℚ K : ℝ)

@[simp]
lemma naiveHeight_zero : W.naiveHeight (0 : W.Point) = 1 :=
  rfl

@[simp]
lemma naiveHeight_some {x y : K} (h : W.Nonsingular x y) : W.naiveHeight (.some h) =
    (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.localDegree)) ^
      (1 / FiniteDimensional.finrank ℚ K : ℝ) :=
  rfl

lemma naiveHeight_neg (P : W.Point) : W.naiveHeight (-P) = W.naiveHeight P := by
  cases P <;> rfl

lemma naiveHeight_ge_one (P : W.Point) : 1 ≤ W.naiveHeight P := by
  rcases P with _ | _
  · rfl
  · exact Real.one_le_rpow (one_le_finprod fun _ => le_max_left ..) <| one_div_nonneg.mpr <|
      Nat.cast_nonneg _

/-! ### The logarithmic height -/

variable (W) in
/-- The logarithmic height of a point on a Weierstrass curve. -/
noncomputable def logHeight (P : W.Point) : ℝ :=
  (W.naiveHeight P).log

@[simp]
lemma logHeight_zero : W.logHeight 0 = 0 :=
  Real.log_one

@[simp]
lemma logHeight_some {x y : K} (h : W.Nonsingular x y) : W.logHeight (.some h) =
    (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.localDegree)).log /
      FiniteDimensional.finrank ℚ K := by
  erw [logHeight, Real.log_rpow <| one_pos.trans_le <| one_le_finprod fun _ => le_max_left ..,
    one_div_mul_eq_div]

lemma logHeight_neg (P : W.Point) : W.logHeight (-P) = W.logHeight P := by
  cases P <;> rfl

lemma logHeight_nonneg (P : W.Point) : 0 ≤ W.logHeight P :=
  Real.log_nonneg <| naiveHeight_ge_one P

-- TODO: difficult
/-- The logarithmic height satisfies the parallelogram law of a quadratic form up to a constant. -/
theorem logHeight_parLaw : ∃ C : ℝ, ∀ P Q : W.Point,
    |W.logHeight (P + Q) + W.logHeight (P - Q) - (2 * W.logHeight P + 2 * W.logHeight Q)| ≤ C :=
  sorry

lemma logHeight_add (Q : W.Point) : ∃ C : ℝ, ∀ P : W.Point,
    W.logHeight (P + Q) - 2 * W.logHeight P ≤ C := by
  rcases W.logHeight_parLaw with ⟨C, h⟩
  exact ⟨2 * W.logHeight Q + C,
    fun P => by linarith only [(abs_le.mp <| h P Q).right, logHeight_nonneg (P - Q)]⟩

lemma logHeight_smul (n : ℤ) : ∃ C : ℝ, ∀ P : W.Point,
    |W.logHeight (n • P) - n ^ 2 * W.logHeight P| ≤ C := by
  induction n using Int.negInduction with
  | nat n => induction n using Nat.strongRec with
    | ind n ih =>
      rcases n with _ | _ | n; exact ⟨0, by simp⟩; exact ⟨0, by simp⟩
      simp only [← nsmul_eq_smul_cast, Int.cast_natCast] at ih ⊢
      rcases ih n <| by linarith only with ⟨C', h'⟩
      rcases ih (n + 1) <| by linarith only with ⟨C'', h''⟩
      push_cast [add_smul, one_smul] at h'' ⊢
      rcases W.logHeight_parLaw with ⟨C, h⟩
      refine ⟨C + C' + 2 * C'', fun P => abs_le.mpr ⟨?_, ?_⟩⟩
      all_goals linarith only [abs_le.mp <| add_sub_cancel_right _ P ▸ h (n • P + P) P,
        abs_le.mp <| h' P, abs_le.mp <| h'' P]
  | neg => simpa only [neg_smul, logHeight_neg, Int.cast_neg, neg_sq]

/-! ### The canonical height -/

/-- The Cauchy sequence of logarithmic heights used to construct the canonical height. -/
noncomputable def canonHeightSeq (P : W.Point) (n : ℕ) : ℝ :=
  W.logHeight ((2 ^ n) • P) / 4 ^ n

lemma canonHeightSeq_zero (P : W.Point) : canonHeightSeq P 0 = W.logHeight P := by
  rw [canonHeightSeq, pow_zero, one_smul, pow_zero, div_one]

lemma canonHeightSeq_sub_succ (P : W.Point) : ∃ C : ℝ, ∀ n : ℕ,
    |canonHeightSeq P n - canonHeightSeq P (n + 1)| ≤ C * (1 / 4) ^ n := by
  rcases W.logHeight_smul 2 with ⟨C, h⟩
  refine ⟨C / 4, fun n => ?_⟩
  rw [abs_sub_comm, canonHeightSeq, pow_succ', mul_smul, canonHeightSeq,
    ← mul_div_mul_left _ (4 ^ n) four_ne_zero, ← pow_succ', div_sub_div_same, abs_div, abs_pow,
    Nat.abs_ofNat, one_div_pow, mul_one_div, div_div, ← pow_succ',
    div_le_div_right <| pow_pos four_pos _, show (4 : ℝ) = (2 ^ 2) by norm_num1]
  exact h <| 2 ^ n • P

lemma cauchySeq_canonHeightSeq (P : W.Point) : CauchySeq <| canonHeightSeq P := by
  rcases canonHeightSeq_sub_succ P with ⟨C, h⟩
  exact cauchySeq_of_le_geometric (1 / 4) C (by norm_num1) h

variable (W) in
/-- The canonical height parallelogram map on a Weierstrass curve. -/
noncomputable def canonHeightFun (P : W.Point) : ℝ :=
  (cauchySeq_tendsto_of_complete <| cauchySeq_canonHeightSeq P).choose

lemma canonHeightSeq_tendsto_canonHeightFun (P : W.Point) :
    Filter.atTop.Tendsto (canonHeightSeq P) <| nhds <| W.canonHeightFun P :=
  (cauchySeq_tendsto_of_complete <| cauchySeq_canonHeightSeq P).choose_spec

variable (W) in
/-- The canonical height parallelogram map on a Weierstrass curve. -/
@[simps]
noncomputable def canonHeight : ParMap W.Point ℝ where
  toFun := W.canonHeightFun
  parLaw' := sorry

lemma canonHeightSeq_tendsto_canonHeight (P : W.Point) :
    Filter.atTop.Tendsto (canonHeightSeq P) <| nhds <| W.canonHeight P :=
  canonHeightSeq_tendsto_canonHeightFun P

lemma canonHeight_sub_logHeight (P : W.Point) : ∃ C : ℝ, |W.canonHeight P - W.logHeight P| ≤ C := by
  rcases canonHeightSeq_sub_succ P with ⟨C, h⟩
  refine ⟨C / (1 - 1 / 4), ?_⟩
  rw [abs_sub_comm, ← canonHeightSeq_zero]
  exact dist_le_of_le_geometric_of_tendsto₀ (1 / 4) C (by norm_num1) (by exact h) <|
    canonHeightSeq_tendsto_canonHeight P

lemma canonHeight_nonneg (P : W.Point) : 0 ≤ W.canonHeight P :=
  ge_of_tendsto' (canonHeightSeq_tendsto_canonHeight P) fun n =>
    div_nonneg (logHeight_nonneg <| 2 ^ n • P) <| pow_nonneg zero_le_four n

/-! ### The canonical height pairing -/

variable (W) in
/-- The quadratic map associated to the canonical height. -/
noncomputable def canonPairing : LinearMap.BilinMap ℤ W.Point ℝ :=
  W.canonHeight.bilinMap

end WeierstrassCurve.Affine
