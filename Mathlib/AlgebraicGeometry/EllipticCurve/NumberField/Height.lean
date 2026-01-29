/-
Copyright (c) 2024 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Group
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.NumberTheory.NumberField.Embeddings
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Heights on Weierstrass curves
-/

open IsDedekindDomain NumberField

universe u v u' v'

section ForMathlib

lemma one_le_finprod {α : Type u} {M : Type v} [OrderedCommSemiring M] {f : α → M}
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

namespace IsDedekindDomain.HeightOneSpectrum

variable {A : Type u} {B : Type v} (K : Type u') (L : Type v') [CommRing A] [CommRing B]
  [IsDedekindDomain A] [IsDedekindDomain B] [Field K] [Field L] [Algebra A B] [Algebra A K]
  [Algebra A L] [Algebra B L] [Algebra K L] [IsFractionRing A K] [IsFractionRing B L]
  [IsIntegralClosure B A L] [IsScalarTower A B L] [IsScalarTower A K L] (v : HeightOneSpectrum A)
  (w : HeightOneSpectrum B)

variable {K} in
noncomputable def realValuation (x : K) : ℝ :=
  (v.valuation x).casesOn 0 (fun x => (Nat.card <| A ⧸ v.asIdeal : ℝ) ^ Multiplicative.toAdd x)

noncomputable def localDeg : ℕ :=
  v.asIdeal.ramificationIdx (algebraMap A B) w.asIdeal *
    v.asIdeal.inertiaDeg (algebraMap A B) w.asIdeal

variable (A) in
noncomputable def below : HeightOneSpectrum A :=
  ⟨.comap .., Ideal.comap_isPrime .., w.ne_bot ∘ Ideal.IsIntegralClosure.eq_bot_of_comap_eq_bot L⟩

noncomputable def absLocalDeg [IsIntegralClosure A ℤ K] : ℕ :=
  (v.below ℤ K).localDeg v

end IsDedekindDomain.HeightOneSpectrum

namespace NumberField.Place

variable {K : Type u} [Field K] [NumberField K]

variable (K) in
def _root_.NumberField.Place : Type u :=
  HeightOneSpectrum (𝓞 K) ⊕ InfinitePlace K

noncomputable def valuation (v : Place K) (x : K) : ℝ :=
  v.casesOn (fun v => v.realValuation x) (fun v => v x)

open Classical in
noncomputable def absLocalDeg (v : Place K) : ℕ :=
  v.casesOn (fun v => v.absLocalDeg K) (fun v => if v.IsReal then 1 else 2)

end NumberField.Place

namespace ParMap

/-! ### Parallelogram maps -/

variable {A : Type u} {R : Type v} [AddCommGroup A] [CommRing R] [IsDomain R] [Invertible (2 : R)]

variable (A R) in
/-- The type of parallelogram maps `p : A → R` from an additive abelian group `A` to an integral
domain `R` of characteristic different from 2 satisfying the parallelogram law. -/
@[ext]
structure _root_.ParMap : Type (max u v) :=
  /-- The parallelogram map `p : A → R`. -/
  (toFun : A → R)
  /-- The parallelogram law `p (a + b) + p (a - b) = 2 * p a + 2 * p b`. -/
  (par_law' : ∀ a b : A, toFun (a + b) + toFun (a - b) = 2 * toFun a + 2 * toFun b)

instance : FunLike (ParMap A R) A R where
  coe := toFun
  coe_injective' := ParMap.ext

variable (p : ParMap A R)

lemma par_law (a b : A) : p (a + b) + p (a - b) = 2 * p a + 2 * p b :=
  p.par_law' a b

@[simp]
lemma zero : p 0 = 0 :=
  mul_right_injective₀ two_ne_zero <| by linear_combination (norm := (simp; ring1)) -p.par_law 0 0

@[simp]
lemma neg (a : A) : p (-a) = p a := by
  linear_combination (norm := (simp; ring1)) p.par_law 0 a

@[simp]
lemma smul (n : ℤ) (a : A) : p (n • a) = n ^ 2 * p a := by
  induction n using Int.negInduction with
  | nat n => induction n using Nat.strongRec with
    | ind n ih =>
      rcases n with _ | _ | n; simp; simp
      simp only [← nsmul_eq_smul_cast] at ih ⊢
      linear_combination (norm := (push_cast [add_smul, one_smul, add_sub_cancel_right]; ring1))
        p.par_law (n • a + a) a - ih n (by linarith only) + 2 * ih (n + 1) (by linarith only)
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
      p.par_law (a + c) b - p.par_law a (c - b) + p.par_law (a + b) c - 2 * p.par_law c b

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

/-- The equivalence between the nonsingular rational points on a Weierstrass curve `W` satisfying a
predicate `p` and the set of pairs `⟨x, y⟩` satisfying `W.Nonsingular x y` with zero. -/
def pointEquivNonsingularSubtype {p : W.Point → Prop} (p0 : p .zero) : {P : W.Point // p P} ≃
    WithZero {xy : K × K // ∃ h : W.Nonsingular xy.fst xy.snd, p <| .some h} where
  toFun P := match P with
    | ⟨.zero, _⟩ => none
    | ⟨@Point.some _ _ _ x y h, ph⟩ => .some ⟨⟨x, y⟩, h, ph⟩
  invFun P := P.casesOn ⟨.zero, p0⟩ fun xy => ⟨.some xy.property.choose, xy.property.choose_spec⟩
  left_inv := by rintro (_ | _) <;> rfl
  right_inv := by rintro (_ | _) <;> rfl

/-! ### The naive height -/

variable (W) in
/-- The naive height of a point on a Weierstrass curve. -/
noncomputable def naiveHeight : W.Point → ℝ
  | .zero => 1
  | @Point.some _ _ _ x _ _ => (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.absLocalDeg)) ^
    (1 / FiniteDimensional.finrank ℚ K : ℝ)

@[simp]
lemma naiveHeight_zero : W.naiveHeight 0 = 1 :=
  rfl

@[simp]
lemma naiveHeight_some {x y : K} (h : W.Nonsingular x y) : W.naiveHeight (.some h) =
    (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.absLocalDeg)) ^
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
  by_cases hC : 1 ≤ C
  · refine (pointEquivNonsingularSubtype hC).finite_iff.mpr ?_
    sorry -- TODO: difficult (Sil09 Theorem VIII.5.11)
  · convert Set.finite_empty using 1
    exact Set.eq_empty_of_forall_not_mem fun P => hC ∘ (naiveHeight_ge_one P).trans

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
    (∏ᶠ v : Place K, max 1 (v.valuation x ^ v.absLocalDeg)).log /
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
theorem logHeight_par_law : ∃ C : ℝ, ∀ P Q : W.Point,
    |W.logHeight (P + Q) + W.logHeight (P - Q) - (2 * W.logHeight P + 2 * W.logHeight Q)| ≤ C :=
  sorry -- TODO: difficult (Sil09 Theorem VIII.6.2)

lemma logHeight_add (Q : W.Point) : ∃ C : ℝ, ∀ P : W.Point,
    W.logHeight (P + Q) - 2 * W.logHeight P ≤ C := by
  rcases W.logHeight_par_law with ⟨C, h⟩
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
      rcases W.logHeight_par_law with ⟨C, h⟩
      refine ⟨C + C' + 2 * C'', fun P => abs_le.mpr ⟨?_, ?_⟩⟩
      all_goals linarith only [abs_le.mp <| add_sub_cancel_right _ P ▸ h (n • P + P) P,
        abs_le.mp <| h' P, abs_le.mp <| h'' P]
  | neg => simpa only [neg_smul, logHeight_neg, Int.cast_neg, neg_sq]

end WeierstrassCurve.Affine

/-! ### Canonical heights -/

namespace CanonHeight

/-- The type of canonical heights `p : A → ℝ` on an additive abelian group `A`, which are
nonnegative parallelogram maps satisfying the Northcott property. -/
@[ext]
structure _root_.CanonHeight (A : Type u) [AddCommGroup A] extends ParMap A ℝ : Type u :=
  /-- The nonnegativity condition. -/
  (nonneg' : ∀ a : A, 0 ≤ toFun a)
  /-- The Northcott property of finitely many elements with bounded canonical height. -/
  (le_finite' : ∀ C : ℝ, {a : A | toFun a ≤ C}.Finite)

variable {A : Type u} [AddCommGroup A] (H : CanonHeight A)

instance : FunLike (CanonHeight A) A ℝ where
  coe h := h.toFun
  coe_injective' := CanonHeight.ext

lemma par_law (a b : A) : H (a + b) + H (a - b) = 2 * H a + 2 * H b :=
  H.toParMap.par_law a b

@[simp]
lemma zero : H 0 = 0 :=
  H.toParMap.zero

@[simp]
lemma neg (a : A) : H (-a) = H a :=
  H.toParMap.neg a

@[simp]
lemma smul (n : ℤ) (a : A) : H (n • a) = n ^ 2 * H a :=
  H.toParMap.smul n a

lemma nonneg (a : A) : 0 ≤ H a :=
  H.nonneg' a

lemma le_finite (C : ℝ) : {a : A | H a ≤ C}.Finite :=
  H.le_finite' C

lemma le_nonempty {C : ℝ} (hC : 0 ≤ C) : {a : A | H a ≤ C}.Nonempty :=
  ⟨0, by convert H.zero ▸ hC⟩

lemma exists_max' {C : ℝ} {p : A → Prop} (h : {a : A | p a ∧ H a ≤ C}.Nonempty) :
    ∃ a : A, p a ∧ H a ≤ C ∧ ∀ b : A, p b → H b ≤ C → H b ≤ H a := by
  rcases Set.exists_max_image _ H ((H.le_finite C).inter_of_right _) h with ⟨a, ⟨hp, hC⟩, ha⟩
  exact ⟨a, hp, hC, fun b hb hb' => ha b ⟨hb, hb'⟩⟩

lemma exists_max {C : ℝ} (hC : 0 ≤ C) : ∃ a : A, H a ≤ C ∧ ∀ b : A, H b ≤ C → H b ≤ H a := by
  rcases H.exists_max' ⟨0, trivial, H.zero ▸ hC⟩ (p := fun _ => True) with ⟨a, _, hC, ha⟩
  exact ⟨a, hC, fun b => ha b trivial⟩

lemma exists_min' {C : ℝ} {p : A → Prop} (h : {a : A | p a ∧ H a ≤ C}.Nonempty) :
    ∃ a : A, p a ∧ H a ≤ C ∧ ∀ b : A, p b → H a ≤ H b := by
  rcases Set.exists_min_image _ H ((H.le_finite C).inter_of_right _) h with ⟨a, ⟨hp, hC⟩, ha⟩
  exact ⟨a, hp, hC,
    fun b hb => if hb' : H b ≤ C then ha b ⟨hb, hb'⟩ else le_trans hC (lt_of_not_le hb').le⟩

lemma exists_min {C : ℝ} (hC : 0 ≤ C) : ∃ a : A, H a ≤ C ∧ ∀ b : A, H a ≤ H b := by
  rcases H.exists_min' ⟨0, trivial, H.zero ▸ hC⟩ (p := fun _ => True) with ⟨a, _, hC, ha⟩
  exact ⟨a, hC, fun b => ha b trivial⟩

/-- **Descent theorem**: if the cokernel of multiplication by `n` for some `1 < |n|` on an additive
abelain group is finite, then the additive abelian group is finitely generated. -/
theorem fg_of_zsmul_coker_finite {n : ℤ} (hn : 1 < |n|) [Finite <| A ⧸ (zsmulAddGroupHom n).range] :
    AddGroup.FG A := by
  have : Nonempty <| A ⧸ (zsmulAddGroupHom n).range := inferInstance
  replace hn : 2 + 2 ≤ (n : ℝ) ^ 2 := by
    simpa only [← two_mul, ← sq, sq_le_sq] using by exact_mod_cast hn
  have hn' : 0 < (n : ℝ) ^ 2 := (add_pos two_pos two_pos).trans_le hn
  rcases (Quotient.out' '' (⊤ : Set <| A ⧸ (zsmulAddGroupHom n).range)).exists_max_image H
    (Set.toFinite _) Set.nonempty_of_nonempty_subtype with ⟨max, _, hmax⟩
  let S : Set A := {a : A | H a ≤ H max}
  refine AddGroup.fg_iff.mpr ⟨S, eq_top_iff.mpr fun b _ => ?_, H.le_finite <| H max⟩
  by_contra! hb
  rcases H.exists_min' (p := (· ∉ AddSubgroup.closure S)) ⟨b, hb, le_rfl⟩ with ⟨min, hmin, _, hmin'⟩
  let min' : S := ⟨⟦min⟧.out', hmax _ <| Set.mem_image_of_mem _ trivial⟩
  have : H min' < H min := lt_of_le_of_lt min'.property <| lt_of_not_le <| by
    convert AddSubgroup.not_mem_of_not_mem_closure hmin
  rcases QuotientAddGroup.mk_out'_eq_mul (zsmulAddGroupHom n).range min with
    ⟨⟨_, c, rfl⟩, hc : min' = min + n • c⟩
  rw [← sub_eq_iff_eq_add'] at hc
  rw [← AddSubgroup.neg_mem_iff, ← AddSubgroup.add_mem_cancel_left _ <| AddSubgroup.mem_closure.mpr
      fun _ h => h min'.property, ← sub_eq_add_neg, hc] at hmin
  refine (hmin' c fun h => hmin <| AddSubgroup.zsmul_mem _ h n).not_lt ?_
  rw [← mul_lt_mul_left hn', ← smul, ← hc]
  calc H (min' - min) ≤ H (min' + min) + H (min' - min) := le_add_of_nonneg_left <| H.nonneg _
    _ < 2 * H min + 2 * H min := by rw [par_law]; gcongr
    _ ≤ n ^ 2 * H min := by rw [← add_mul]; gcongr; exact H.nonneg min

variable (W) in
/-- The quadratic map associated to the canonical height. -/
noncomputable def pairing : LinearMap.BilinMap ℤ A ℝ :=
  H.bilinMap

end CanonHeight

namespace WeierstrassCurve.Affine

open CanonHeight

variable {K : Type v} [Field K] [NumberField K] {W : Affine K}

/-! ### The canonical height sequence -/

/-- The Cauchy sequence of logarithmic heights used to construct the canonical height. -/
noncomputable def canonHeightSeq (P : W.Point) (n : ℕ) : ℝ :=
  W.logHeight (2 ^ n • P) * 4⁻¹ ^ n

lemma canonHeightSeq_zero (P : W.Point) : canonHeightSeq P 0 = W.logHeight P := by
  rw [canonHeightSeq, pow_zero, one_smul, pow_zero, mul_one]

lemma canonHeightSeq_nonneg (P : W.Point) (n : ℕ) : 0 ≤ canonHeightSeq P n :=
  mul_nonneg (logHeight_nonneg <| 2 ^ n • P) <| pow_nonneg (inv_nonneg_of_nonneg zero_le_four) n

lemma canonHeightSeq_sub_succ : ∃ C : ℝ, ∀ P : W.Point, ∀ n : ℕ,
    |canonHeightSeq P n - canonHeightSeq P (n + 1)| ≤ C * 4⁻¹ ^ n := by
  rcases W.logHeight_smul 2 with ⟨C, h⟩
  refine ⟨C * 4⁻¹, fun P n => ?_⟩
  rw [abs_sub_comm, canonHeightSeq, pow_succ', mul_smul, canonHeightSeq,
    ← mul_inv_cancel_right₀ four_ne_zero <| W.logHeight (_ • P), mul_comm _ 4, mul_assoc,
    ← pow_succ', ← sub_mul, abs_mul, abs_pow, abs_inv, Nat.abs_ofNat, mul_assoc, ← pow_succ',
    mul_le_mul_right <| pow_pos (inv_pos_of_pos four_pos) _, show (4 : ℝ) = 2 ^ 2 by norm_num1]
  exact h <| 2 ^ n • P

lemma cauchySeq_canonHeightSeq (P : W.Point) : CauchySeq <| canonHeightSeq P := by
  rcases W.canonHeightSeq_sub_succ with ⟨C, h⟩
  exact cauchySeq_of_le_geometric 4⁻¹ C (by norm_num1) <| h P

lemma canonHeightSeq_par_law : ∃ C : ℝ, ∀ P Q : W.Point, ∀ n : ℕ,
    |canonHeightSeq (P + Q) n + canonHeightSeq (P - Q) n -
      (2 * canonHeightSeq P n + 2 * canonHeightSeq Q n)| ≤ C * 4⁻¹ ^ n := by
  rcases W.logHeight_par_law with ⟨C, h⟩
  refine ⟨C, fun P Q n => ?_⟩
  rw [canonHeightSeq, smul_add, canonHeightSeq, smul_sub, ← add_mul, canonHeightSeq, ← mul_assoc,
    canonHeightSeq, ← mul_assoc, ← add_mul, ← sub_mul, abs_mul, abs_pow, abs_inv, Nat.abs_ofNat]
  exact (mul_le_mul_right <| pow_pos (inv_pos_of_pos four_pos) n).mpr <| h (2 ^ n • P) (2 ^ n • Q)

/-! ### The canonical height function -/

variable (W) in
/-- The canonical height function of a point on a Weierstrass curve. -/
noncomputable def canonHeightFun (P : W.Point) : ℝ :=
  (cauchySeq_tendsto_of_complete <| cauchySeq_canonHeightSeq P).choose

lemma canonHeightSeq_tendsto_canonHeightFun (P : W.Point) :
    Filter.atTop.Tendsto (canonHeightSeq P) <| nhds <| W.canonHeightFun P :=
  (cauchySeq_tendsto_of_complete <| cauchySeq_canonHeightSeq P).choose_spec

lemma canonHeightFun_par_law (P Q : W.Point) : W.canonHeightFun (P + Q) + W.canonHeightFun (P - Q) =
    2 * W.canonHeightFun P + 2 * W.canonHeightFun Q :=
  eq_of_tendsto_norm_le_geometric
    ((canonHeightSeq_tendsto_canonHeightFun _).add <| canonHeightSeq_tendsto_canonHeightFun _) (((canonHeightSeq_tendsto_canonHeightFun _).const_mul 2).add <|
      (canonHeightSeq_tendsto_canonHeightFun _).const_mul 2) (by norm_num [abs_div]) <|
    canonHeightSeq_par_law.choose_spec P Q

lemma canonHeightFun_nonneg (P : W.Point) : 0 ≤ W.canonHeightFun P :=
  ge_of_tendsto' (canonHeightSeq_tendsto_canonHeightFun P) <| canonHeightSeq_nonneg P

lemma canonHeightFun_sub_canonHeightSeq : ∃ C : ℝ, ∀ P : W.Point, ∀ n : ℕ,
    |W.canonHeightFun P - canonHeightSeq P n| ≤ C * 4⁻¹ ^ n := by
  rcases W.canonHeightSeq_sub_succ with ⟨C, h⟩
  refine ⟨C / (1 - 4⁻¹), fun P n => ?_⟩
  rw [abs_sub_comm, ← mul_div_right_comm]
  exact dist_le_of_le_geometric_of_tendsto 4⁻¹ C (by norm_num1) (by exact h P)
    (canonHeightSeq_tendsto_canonHeightFun P) n

lemma canonHeightFun_sub_logHeight : ∃ C : ℝ, ∀ P : W.Point,
    |W.canonHeightFun P - W.logHeight P| ≤ C := by
  rcases W.canonHeightFun_sub_canonHeightSeq with ⟨C, h⟩
  exact ⟨C, fun P => mul_one C ▸ canonHeightSeq_zero P ▸ h P 0⟩

lemma canonHeightFun_le_finite (C : ℝ) : {P : W.Point | W.canonHeightFun P ≤ C}.Finite := by
  rcases W.canonHeightFun_sub_logHeight with ⟨C', h⟩
  refine (logHeight_le_finite <| C + C').subset fun P hP => ?_
  rw [Set.mem_setOf_eq, ← abs_of_nonneg <| canonHeightFun_nonneg P] at hP
  rw [Set.mem_setOf_eq, ← abs_of_nonneg <| logHeight_nonneg P]
  linarith only [hP, (abs_sub_abs_le_abs_sub ..).trans <| abs_sub_comm (W.canonHeightFun P) _ ▸ h P]

/-! ### The canonical height parallelogram map -/

variable (W) in
/-- The canonical height parallelogram map on a Weierstrass curve. -/
@[simps]
noncomputable def canonHeight : CanonHeight W.Point :=
  ⟨⟨W.canonHeightFun, canonHeightFun_par_law⟩, canonHeightFun_nonneg, canonHeightFun_le_finite⟩

lemma canonHeightSeq_tendsto_canonHeight (P : W.Point) :
    Filter.atTop.Tendsto (canonHeightSeq P) <| nhds <| W.canonHeight P :=
  canonHeightSeq_tendsto_canonHeightFun P

lemma canonHeight_sub_canonHeightSeq : ∃ C : ℝ, ∀ P : W.Point, ∀ n : ℕ,
    |W.canonHeight P - canonHeightSeq P n| ≤ C * 4⁻¹ ^ n :=
  canonHeightFun_sub_canonHeightSeq

lemma canonHeight_sub_logHeight : ∃ C : ℝ, ∀ P : W.Point,
    |W.canonHeight P - W.logHeight P| ≤ C :=
  canonHeightFun_sub_logHeight

lemma canonHeight_par_law (P Q : W.Point) :
    W.canonHeight (P + Q) + W.canonHeight (P - Q) = 2 * W.canonHeight P + 2 * W.canonHeight Q :=
  W.canonHeight.par_law P Q

lemma canonHeight_zero : W.canonHeight 0 = 0 :=
  W.canonHeight.zero

lemma canonHeight_neg (P : W.Point) : W.canonHeight (-P) = W.canonHeight P :=
  W.canonHeight.neg P

lemma canonHeight_smul (n : ℤ) (P : W.Point) : W.canonHeight (n • P) = n ^ 2 * W.canonHeight P :=
  W.canonHeight.smul n P

lemma canonHeight_nonneg (P : W.Point) : 0 ≤ W.canonHeight P :=
  W.canonHeight.nonneg P

lemma canonHeight_le_finite (C : ℝ) : {P : W.Point | W.canonHeight P ≤ C}.Finite :=
  W.canonHeight.le_finite C

lemma canonHeight_le_nonempty {C : ℝ} (hC : 0 ≤ C) : {P : W.Point | W.canonHeight P ≤ C}.Nonempty :=
  W.canonHeight.le_nonempty hC

lemma canonHeight_exists_max' {C : ℝ} {p : W.Point → Prop}
    (h : {P : W.Point | p P ∧ W.canonHeight P ≤ C}.Nonempty) :
    ∃ P : W.Point, p P ∧ W.canonHeight P ≤ C ∧
      ∀ Q : W.Point, p Q → W.canonHeight Q ≤ C → W.canonHeight Q ≤ W.canonHeight P :=
  W.canonHeight.exists_max' h

lemma canonHeight_exists_max {C : ℝ} (hC : 0 ≤ C) :
    ∃ P : W.Point, W.canonHeight P ≤ C ∧
      ∀ Q : W.Point, W.canonHeight Q ≤ C → W.canonHeight Q ≤ W.canonHeight P :=
  W.canonHeight.exists_max hC

lemma canonHeight_exists_min' {C : ℝ} {p : W.Point → Prop}
    (h : {P : W.Point | p P ∧ W.canonHeight P ≤ C}.Nonempty) :
    ∃ P : W.Point, p P ∧ W.canonHeight P ≤ C ∧
      ∀ Q : W.Point, p Q → W.canonHeight P ≤ W.canonHeight Q :=
  W.canonHeight.exists_min' h

lemma canonHeight_exists_min {C : ℝ} (hC : 0 ≤ C) :
    ∃ P : W.Point, W.canonHeight P ≤ C ∧ ∀ Q : W.Point, W.canonHeight P ≤ W.canonHeight Q :=
  W.canonHeight.exists_min hC

lemma canonHeight_fg_of_zsmul_coker_finite {n : ℤ} (hn : 1 < |n|)
    [Finite <| W.Point ⧸ (zsmulAddGroupHom n).range] : AddGroup.FG W.Point :=
  W.canonHeight.fg_of_zsmul_coker_finite hn

lemma canonHeight_unique {h : W.Point → ℝ}
    (hsub : ∃ C : ℝ, ∀ P : W.Point, |h P - W.logHeight P| ≤ C)
    (hsmul : ∃ n : ℤ, 1 < |n| ∧ ∀ P : W.Point, h (n • P) = n ^ 2 * h P) (P : W.Point) :
    h P = W.canonHeight P := by
  rcases hsub, hsmul, W.canonHeight_sub_logHeight with ⟨⟨C, hsub⟩, ⟨n, hn, hsmul⟩, ⟨C', hsub'⟩⟩
  replace hn : 1 < |(n : ℝ)| := by exact_mod_cast hn
  have hn' : |(|(n : ℝ) ^ 2|⁻¹)| < 1 := by
    simpa only [abs_inv, abs_abs, abs_pow] using inv_lt_one <| one_lt_pow hn two_ne_zero
  refine eq_of_norm_le_geometric hn' (C := C + C') fun m => ?_
  induction m generalizing P with
  | zero =>
    rw [pow_zero, mul_one, ← sub_sub_sub_cancel_right]
    exact norm_sub_le_of_le (hsub P) (hsub' P)
  | succ _ ih =>
    rw [pow_succ, ← mul_assoc, ← div_eq_mul_inv, le_div_iff' <| abs_pow (n : ℝ) 2 ▸ pow_pos
        (one_pos.trans hn) 2, Real.norm_eq_abs, ← abs_mul, mul_sub, ← hsmul, ← smul]
    exact ih <| n • P

lemma canonHeight_eq_zero (P : W.Point) : W.canonHeight P = 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ n • P = 0 := by
  rw [← isOfFinAddOrder_iff_zsmul_eq_zero, ← finite_multiples]
  refine ⟨fun hP => ?_, fun hP => ?_⟩
  · rcases W.canonHeight_sub_logHeight with ⟨C, h⟩
    replace hP (n : ℤ) : W.logHeight (n • P) ≤ C := by
      convert h <| n • P using 1
      rw [smul, hP, mul_zero, zero_sub, abs_neg, abs_of_nonneg <| logHeight_nonneg _]
    exact (logHeight_le_finite C).subset fun _ ⟨n, hn⟩ => hn ▸ hP n
  · replace hP : (Set.range fun n => 2 ^ n • P).Finite := hP.subset fun _ ⟨n, hn⟩ => ⟨2 ^ n, hn⟩
    rcases Set.exists_max_image _ W.logHeight hP ⟨P, 0, one_smul ..⟩ with ⟨Q, _, hQ⟩
    refine eq_zero_of_tendsto_norm_le_geometric (canonHeightSeq_tendsto_canonHeight P)
      (by norm_num [abs_div]) (C := W.logHeight Q) (x := 4⁻¹) fun n => ?_
    rw [Real.norm_of_nonneg <| canonHeightSeq_nonneg P n, canonHeightSeq,
      mul_le_mul_right <| pow_pos (inv_pos_of_pos four_pos) n]
    exact hQ (2 ^ n • P) ⟨n, rfl⟩

end WeierstrassCurve.Affine
