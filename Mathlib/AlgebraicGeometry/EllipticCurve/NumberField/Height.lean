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

section ForMathlib

theorem one_le_finprod {α : Type u} {M : Type v} [OrderedCommSemiring M] {f : α → M}
    (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul_of_one_le_of_one_le) hf

lemma tendsto_geometric_atTop_nhds_zero_of_lt_one {𝕜 : Type u} [LinearOrderedField 𝕜]
    [Archimedean 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] {C r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) :
    Filter.atTop.Tendsto (fun n => C * r ^ n) <| nhds 0 :=
  mul_zero C ▸ (tendsto_pow_atTop_nhds_zero_of_lt_one h₁ h₂).const_mul C

lemma tendsto_geometric_atTop_nhds_zero_of_norm_lt_one {R : Type u} [NormedRing R] {C x : R}
    (h : ‖x‖ < 1) : Filter.atTop.Tendsto (fun n => C * x ^ n) <| nhds 0 :=
  mul_zero C ▸ (tendsto_pow_atTop_nhds_zero_of_norm_lt_one h).const_mul C

lemma tendsto_geometric_atTop_nhds_zero_of_abs_lt_one {C r : ℝ} (h : |r| < 1) :
    Filter.atTop.Tendsto (fun n => C * r ^ n) <| nhds 0 :=
  mul_zero C ▸ (tendsto_pow_atTop_nhds_zero_of_abs_lt_one h).const_mul C

lemma eq_zero_of_tendsto_squeeze_zero_norm' {α : Type u} {t₀ : Filter α} [t₀.NeBot] {E : Type v}
    [SeminormedAddGroup E] [T2Space E] {f : α → E} {x : E} (hf : Filter.Tendsto f t₀ <| nhds x)
    {a : α → ℝ} (ha : Filter.Tendsto a t₀ <| nhds 0) (h : ∀ᶠ n : α in t₀, ‖f n‖ ≤ a n) : x = 0 :=
  tendsto_nhds_unique hf <| squeeze_zero_norm' h ha

lemma eq_of_tendsto_squeeze_zero_norm' {α : Type u} {t₀ : Filter α} [t₀.NeBot] {E : Type v}
    [SeminormedAddCommGroup E] [T2Space E] {f g : α → E} {x y : E}
    (hf : Filter.Tendsto f t₀ <| nhds x) (hg : Filter.Tendsto g t₀ <| nhds y) {a : α → ℝ}
    (ha : Filter.Tendsto a t₀ <| nhds 0) (h : ∀ᶠ n : α in t₀, ‖f n - g n‖ ≤ a n) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_tendsto_squeeze_zero_norm' (hf.sub hg) ha h

lemma eq_zero_of_tendsto_norm'_le_geometric {R : Type u} [NormedRing R] {f : ℕ → R} {a : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) {C x : ℝ} (hx : |x| < 1)
    (h : ∀ᶠ n : ℕ in .atTop, ‖f n‖ ≤ C * x ^ n) : a = 0 :=
  eq_zero_of_tendsto_squeeze_zero_norm' hf (tendsto_geometric_atTop_nhds_zero_of_abs_lt_one hx) h

lemma eq_of_tendsto_norm'_le_geometric {R : Type u} [NormedRing R] {f g : ℕ → R} {a b : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) (hg : Filter.atTop.Tendsto g <| nhds b) {C x : ℝ}
    (hx : |x| < 1) (h : ∀ᶠ n : ℕ in .atTop, ‖f n - g n‖ ≤ C * x ^ n) : a = b :=
  sub_eq_zero.mp <| eq_zero_of_tendsto_norm'_le_geometric (hf.sub hg) hx h

lemma eq_zero_of_tendsto_norm'_le_pow {R : Type u} [NormedRing R] {f : ℕ → R} {a : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) {x : ℝ} (hx : |x| < 1)
    (h : ∀ᶠ n : ℕ in .atTop, ‖f n‖ ≤ x ^ n) : a = 0 :=
  eq_zero_of_tendsto_squeeze_zero_norm' hf (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx) h

lemma eq_of_tendsto_norm'_le_pow {R : Type u} [NormedRing R] {f g : ℕ → R} {a b : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) (hg : Filter.atTop.Tendsto g <| nhds b) {x : ℝ}
    (hx : |x| < 1) (h : ∀ᶠ n : ℕ in .atTop, ‖f n - g n‖ ≤ x ^ n) : a = b :=
  sub_eq_zero.mp <| eq_zero_of_tendsto_norm'_le_pow (hf.sub hg) hx h

lemma eq_zero_of_tendsto_squeeze_zero_norm {α : Type u} {t₀ : Filter α} [t₀.NeBot]
    {E : Type v} [SeminormedAddGroup E] [T2Space E] {f : α → E} {x : E}
    (hf : Filter.Tendsto f t₀ <| nhds x) {a : α → ℝ} (ha : Filter.Tendsto a t₀ <| nhds 0)
    (h : ∀ n : α, ‖f n‖ ≤ a n) : x = 0 :=
  tendsto_nhds_unique hf <| squeeze_zero_norm h ha

lemma eq_of_tendsto_squeeze_zero_norm {α : Type u} {t₀ : Filter α} [t₀.NeBot] {E : Type v}
    [SeminormedAddCommGroup E] [T2Space E] {f g : α → E} {x y : E}
    (hf : Filter.Tendsto f t₀ <| nhds x) (hg : Filter.Tendsto g t₀ <| nhds y) {a : α → ℝ}
    (ha : Filter.Tendsto a t₀ <| nhds 0) (h : ∀ n : α, ‖f n - g n‖ ≤ a n) : x = y :=
  sub_eq_zero.mp <| eq_zero_of_tendsto_squeeze_zero_norm (hf.sub hg) ha h

lemma eq_zero_of_tendsto_norm_le_geometric {R : Type u} [NormedRing R] {f : ℕ → R} {a : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) {C x : ℝ} (hx : |x| < 1)
    (h : ∀ n : ℕ, ‖f n‖ ≤ C * x ^ n) : a = 0 :=
  eq_zero_of_tendsto_squeeze_zero_norm hf (tendsto_geometric_atTop_nhds_zero_of_abs_lt_one hx) h

lemma eq_of_tendsto_norm_le_geometric {R : Type u} [NormedRing R] {f g : ℕ → R} {a b : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) (hg : Filter.atTop.Tendsto g <| nhds b) {C x : ℝ}
    (hx : |x| < 1) (h : ∀ n : ℕ, ‖f n - g n‖ ≤ C * x ^ n) : a = b :=
  sub_eq_zero.mp <| eq_zero_of_tendsto_norm_le_geometric (hf.sub hg) hx h

lemma eq_zero_of_norm_le_geometric {R : Type u} [NormedRing R] {a : R} {C x : ℝ} (hx : |x| < 1)
    (h : ∀ n : ℕ, ‖a‖ ≤ C * x ^ n) : a = 0 :=
  eq_zero_of_tendsto_norm_le_geometric tendsto_const_nhds hx h

lemma eq_of_norm_le_geometric {R : Type u} [NormedRing R] {a b : R} {C x : ℝ} (hx : |x| < 1)
    (h : ∀ n : ℕ, ‖a - b‖ ≤ C * x ^ n) : a = b :=
  sub_eq_zero.mp <| eq_zero_of_norm_le_geometric hx h

lemma eq_zero_of_tendsto_norm_le_pow {R : Type u} [NormedRing R] {f : ℕ → R} {a : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) {x : ℝ} (hx : |x| < 1) (h : ∀ n : ℕ, ‖f n‖ ≤ x ^ n) :
    a = 0 :=
  eq_zero_of_tendsto_squeeze_zero_norm hf (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx) h

lemma eq_of_tendsto_norm_le_pow {R : Type u} [NormedRing R] {f g : ℕ → R} {a b : R}
    (hf : Filter.atTop.Tendsto f <| nhds a) (hg : Filter.atTop.Tendsto g <| nhds b) {x : ℝ}
    (hx : |x| < 1) (h : ∀ n : ℕ, ‖f n - g n‖ ≤ x ^ n) : a = b :=
  sub_eq_zero.mp <| eq_zero_of_tendsto_norm_le_pow (hf.sub hg) hx h

lemma eq_zero_of_norm_le_pow {R : Type u} [NormedRing R] {a : R} {x : ℝ} (hx : |x| < 1)
    (h : ∀ n : ℕ, ‖a‖ ≤ x ^ n) : a = 0 :=
  eq_zero_of_tendsto_norm_le_pow tendsto_const_nhds hx h

lemma eq_of_norm_le_pow {R : Type u} [NormedRing R] {a b : R} {x : ℝ} (hx : |x| < 1)
    (h : ∀ n : ℕ, ‖a - b‖ ≤ x ^ n) : a = b :=
  sub_eq_zero.mp <| eq_zero_of_norm_le_pow hx h

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
lemma smul (n : ℤ) (a : A) : p (n • a) = n ^ 2 * p a := by
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

end ForMathlib

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

lemma naiveHeight_pos (P : W.Point) : 0 < W.naiveHeight P :=
  one_pos.trans_le <| naiveHeight_ge_one P

/-- **Northcott's theorem**: there are finitely many points with bounded naive height. -/
theorem naiveHeight_le_finite (C : ℝ) : {P : W.Point | W.naiveHeight P ≤ C}.Finite := by
  sorry -- TODO: difficult

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

lemma logHeight_le_finite (C : ℝ) : {P : W.Point | W.logHeight P ≤ C}.Finite := by
  simpa only [logHeight, Real.log_le_iff_le_exp <| naiveHeight_pos _] using naiveHeight_le_finite _

/-- The logarithmic height satisfies the parallelogram law of a quadratic form up to a constant. -/
theorem logHeight_parLaw : ∃ C : ℝ, ∀ P Q : W.Point,
    |W.logHeight (P + Q) + W.logHeight (P - Q) - (2 * W.logHeight P + 2 * W.logHeight Q)| ≤ C :=
  sorry -- TODO: difficult

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
      rcases ih n <| by linarith only, ih (n + 1) <| by linarith only with ⟨⟨C', h'⟩, ⟨C'', h''⟩⟩
      push_cast [add_smul, one_smul] at h'' ⊢
      rcases W.logHeight_parLaw with ⟨C, h⟩
      refine ⟨C + C' + 2 * C'', fun P => abs_le.mpr ⟨?_, ?_⟩⟩
      all_goals linarith only [abs_le.mp <| add_sub_cancel_right _ P ▸ h (n • P + P) P,
        abs_le.mp <| h' P, abs_le.mp <| h'' P]
  | neg => simpa only [neg_smul, logHeight_neg, Int.cast_neg, neg_sq]

/-! ### The canonical height -/

/-- The Cauchy sequence of logarithmic heights used to construct the canonical height. -/
noncomputable def canonHeightSeq (P : W.Point) (n : ℕ) : ℝ :=
  W.logHeight ((2 ^ n) • P) * 4⁻¹ ^ n

lemma canonHeightSeq_zero (P : W.Point) : canonHeightSeq P 0 = W.logHeight P := by
  rw [canonHeightSeq, pow_zero, one_smul, pow_zero, mul_one]

lemma canonHeightSeq_sub_succ : ∃ C : ℝ, ∀ P : W.Point, ∀ n : ℕ,
    |canonHeightSeq P n - canonHeightSeq P (n + 1)| ≤ C * 4⁻¹ ^ n := by
  rcases W.logHeight_smul 2 with ⟨C, h⟩
  refine ⟨C * 4⁻¹, fun P n => ?_⟩
  rw [abs_sub_comm, canonHeightSeq, pow_succ', mul_smul, canonHeightSeq,
    ← mul_inv_cancel_right₀ four_ne_zero <| W.logHeight (_ • P), mul_comm _ 4, mul_assoc,
    ← pow_succ', ← sub_mul, abs_mul, abs_pow, abs_inv, Nat.abs_ofNat, mul_assoc, ← pow_succ',
    mul_le_mul_right <| pow_pos (inv_pos_of_pos four_pos) _, show (4 : ℝ) = (2 ^ 2) by norm_num1]
  exact h <| 2 ^ n • P

lemma cauchySeq_canonHeightSeq (P : W.Point) : CauchySeq <| canonHeightSeq P := by
  rcases W.canonHeightSeq_sub_succ with ⟨C, h⟩
  exact cauchySeq_of_le_geometric 4⁻¹ C (by norm_num1) <| h P

lemma canonHeightSeq_parLaw : ∃ C : ℝ, ∀ P Q : W.Point, ∀ n : ℕ,
    |canonHeightSeq (P + Q) n + canonHeightSeq (P - Q) n -
      (2 * canonHeightSeq P n + 2 * canonHeightSeq Q n)| ≤ C * 4⁻¹ ^ n := by
  rcases W.logHeight_parLaw with ⟨C, h⟩
  refine ⟨C, fun P Q n => ?_⟩
  rw [canonHeightSeq, smul_add, canonHeightSeq, smul_sub, ← add_mul, canonHeightSeq, ← mul_assoc,
    canonHeightSeq, ← mul_assoc, ← add_mul, ← sub_mul, abs_mul, abs_pow, abs_inv, Nat.abs_ofNat]
  exact (mul_le_mul_right <| pow_pos (inv_pos_of_pos four_pos) n).mpr <| h (2 ^ n • P) (2 ^ n • Q)

variable (W) in
/-- The canonical height parallelogram map on a Weierstrass curve. -/
@[simps]
noncomputable def canonHeight : ParMap W.Point ℝ where
  toFun P := (cauchySeq_tendsto_of_complete <| cauchySeq_canonHeightSeq P).choose
  parLaw' P Q :=
    let t {R : W.Point} := (cauchySeq_tendsto_of_complete <| cauchySeq_canonHeightSeq R).choose_spec
    eq_of_tendsto_norm_le_geometric (t.add t) ((t.const_mul 2).add <| t.const_mul 2)
      (by norm_num [abs_div]) <| canonHeightSeq_parLaw.choose_spec P Q

lemma canonHeightSeq_tendsto_canonHeight (P : W.Point) :
    Filter.atTop.Tendsto (canonHeightSeq P) <| nhds <| W.canonHeight P :=
  (cauchySeq_tendsto_of_complete <| cauchySeq_canonHeightSeq P).choose_spec

lemma canonHeight_zero : W.canonHeight 0 = 0 :=
  W.canonHeight.zero

lemma canonHeight_neg (P : W.Point) : W.canonHeight (-P) = W.canonHeight P :=
  W.canonHeight.neg P

lemma canonHeight_smul (n : ℤ) (P : W.Point) : W.canonHeight (n • P) = n ^ 2 * W.canonHeight P :=
  W.canonHeight.smul n P

lemma canonHeight_nonneg (P : W.Point) : 0 ≤ W.canonHeight P :=
  ge_of_tendsto' (canonHeightSeq_tendsto_canonHeight P) fun n =>
    mul_nonneg (logHeight_nonneg <| 2 ^ n • P) <| pow_nonneg (inv_nonneg_of_nonneg zero_le_four) n

lemma canonHeight_sub_logHeight : ∃ C : ℝ, ∀ P : W.Point,
    |W.canonHeight P - W.logHeight P| ≤ C := by
  rcases W.canonHeightSeq_sub_succ with ⟨C, h⟩
  refine ⟨C / (1 - 4⁻¹), fun P => ?_⟩
  rw [abs_sub_comm, ← canonHeightSeq_zero]
  exact dist_le_of_le_geometric_of_tendsto₀ 4⁻¹ C (by norm_num1) (by exact h P) <|
    canonHeightSeq_tendsto_canonHeight P

lemma canonHeight_unique {h : W.Point → ℝ}
    (hsub : ∃ C : ℝ, ∀ P : W.Point, |h P - W.logHeight P| ≤ C)
    (hsmul : ∀ n : ℤ, ∀ P : W.Point, h (n • P) = n ^ 2 * h P) (P : W.Point) :
    h P = W.canonHeight P := by
  rcases hsub, W.canonHeight_sub_logHeight with ⟨⟨C, hsub⟩, ⟨C', hsub'⟩⟩
  refine eq_of_norm_le_geometric (by norm_num [abs_div]) (C := C + C') (x := |2 ^ 2|⁻¹) fun n => ?_
  erw [inv_pow, ← abs_pow, pow_right_comm, ← Int.cast_pow, ← div_eq_mul_inv,
    le_div_iff' <| abs_pos_of_pos <| pow_pos (Int.cast_pos.mpr <| pow_pos two_pos n) 2, ← abs_mul,
    mul_sub, ← hsmul, ← canonHeight_smul, ← sub_sub_sub_cancel_right]
  exact (abs_sub ..).trans <| add_le_add (hsub <| 2 ^ n • P) (hsub' <| 2 ^ n • P)

/-! ### The canonical height pairing -/

variable (W) in
/-- The quadratic map associated to the canonical height. -/
noncomputable def canonPairing : LinearMap.BilinMap ℤ W.Point ℝ :=
  W.canonHeight.bilinMap

end WeierstrassCurve.Affine
