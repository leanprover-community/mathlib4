/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.AlgebraNorm
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# SeminormFromConst


In this file, we prove [BGR, Proposition 1.3.2/2][bosch-guntzer-remmert] : starting from a
power-multiplicative seminorm on a commutative ring `R` and a nonzero `c : R`, we create a new
power-multiplicative seminorm for which `c` is multiplicative.

## Main Definitions

* `seminormFromConst` : for a ring seminorm `f` on `R` and `c ∈ R`, the ring seminorm on `R` defined
  as the limit of `f (x * c ^ n) / (f c) ^ n`.

## Main Results
* `seminormFromConst_isNonarchimedean` : the function `seminormFromConst c f`
  is nonarchimedean when `f` is nonarchimedean.
* `seminormFromConst_isPowMul` : the function `seminormFromConst c f`
  is power-multiplicative when `f` is power multiplicative.
* `seminormFromConst_const_mul` : if `f` is power multiplicative, then
  `seminormFromConst c f (c * x) = seminormFromConst c f c * seminormFromConst c f x`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

SeminormFromConst, Seminorm, Nonarchimedean
-/

@[expose] public section

noncomputable section

open Filter

open scoped Topology

section Ring

variable {R : Type*} [CommRing R] (c : R) (f : RingSeminorm R)

/-- For a ring seminorm `f` on `R` and `c ∈ R`, the sequence `n ↦ f (x * c ^ n) / (f c) ^ n`. -/
def seminormFromConst_seq (x : R) : ℕ → ℝ := fun n ↦ f (x * c ^ n) / f c ^ n

lemma seminormFromConst_seq_def (x : R) :
    seminormFromConst_seq c f x = fun n ↦ f (x * c ^ n) / f c ^ n := rfl

/-- The terms in the sequence `seminormFromConst_seq c f x` are nonnegative. -/
theorem seminormFromConst_seq_nonneg (x : R) : 0 ≤ seminormFromConst_seq c f x :=
  fun n ↦ div_nonneg (apply_nonneg f (x * c ^ n)) (pow_nonneg (apply_nonneg f c) n)

/-- The image of `seminormFromConst_seq c f x` is bounded below by zero. -/
theorem seminormFromConst_bddBelow (x : R) :
    BddBelow (Set.range (seminormFromConst_seq c f x)) := by
  use 0
  rintro r ⟨n, rfl⟩
  exact seminormFromConst_seq_nonneg c f x n

/-- `seminormFromConst_seq c f 0` is the constant sequence zero. -/
theorem seminormFromConst_seq_zero : seminormFromConst_seq c f 0 = 0 := by
  ext n
  simp [seminormFromConst_seq]

/-- `seminormFromConst_seq c f 0` is the constant sequence zero. -/
theorem seminormFromConst_seq_apply_zero (x : R) : seminormFromConst_seq c f x 0 = f x := by
  simp [seminormFromConst_seq]

/-- `seminormFromConst_seq c f x` is antitone. -/
theorem seminormFromConst_seq_antitone (x : R) : Antitone (seminormFromConst_seq c f x) := by
  apply antitone_nat_of_succ_le
  intro n
  by_cases hc : f c = 0
  · rw [seminormFromConst_seq, hc, zero_pow n.add_one_ne_zero, div_zero]
    exact seminormFromConst_seq_nonneg c f x n
  · grw [seminormFromConst_seq, pow_succ, ← mul_assoc, map_mul_le_mul, pow_succ,
      mul_div_mul_right _ _ hc, seminormFromConst_seq]

/-- `seminormFromConst_seq c f x` is antitone. -/
theorem seminormFromConst_le (x : R) (n : ℕ) : seminormFromConst_seq c f x n ≤ f x :=
  (seminormFromConst_seq_antitone c f x n.zero_le).trans_eq (seminormFromConst_seq_apply_zero c f x)

/-- The real-valued function sending `x ∈ R` to the limit of `(f (x * c^n))/((f c)^n)`. -/
@[deprecated "Use `seminormFromConst` directly." (since := "2026-09-24")]
def seminormFromConst' (c : R) (f : RingSeminorm R) (x : R) : ℝ :=
  iInf (seminormFromConst_seq c f x)

/-- We prove that `seminormFromConst' c f x` is the limit of the sequence
  `seminormFromConst_seq c f x` as `n` tends to infinity. -/
@[deprecated "Use `seminormFromConst` directly." (since := "2026-09-24")]
theorem tendsto_seminormFromConst_seq_atTop (x : R) :
    Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (seminormFromConst' c f x)) :=
  tendsto_atTop_ciInf (seminormFromConst_seq_antitone c f x)
    (seminormFromConst_bddBelow c f x)

/-- For a ring seminorm `f` on `R` and `c ∈ R`, the ring seminorm on `R` defined as the limit of
`f (x * c ^ n) / (f c) ^ n`.

We leave this definition unexposed. Use the limit `tendsto_seminormFromConst` instead. -/
@[no_expose]
def seminormFromConst : RingSeminorm R :=
  let g x : ℝ := iInf (seminormFromConst_seq c f x)
  have hg x : Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (g x)) :=
     tendsto_atTop_ciInf (seminormFromConst_seq_antitone c f x) (seminormFromConst_bddBelow c f x)
  { toFun := g
    map_zero' := tendsto_nhds_unique_of_forall (hg 0) tendsto_const_nhds
      (funext_iff.mp (seminormFromConst_seq_zero c f))
    add_le' x y := by
      refine le_of_tendsto_of_tendsto' (hg (x + y)) ((hg x).add (hg y)) fun n ↦ ?_
      simp only [seminormFromConst_seq]
      grw [add_mul, map_add_le_add, add_div]
    neg' x := tendsto_nhds_unique_of_forall (hg (-x)) (hg x) (by simp [seminormFromConst_seq])
    mul_le' x y := by
      refine le_of_tendsto_of_tendsto' ((hg (x * y)).comp
        (strictMono_mul_left_of_pos two_pos).tendsto_atTop) ((hg x).mul (hg y)) fun n ↦ ?_
      simp only [seminormFromConst_seq, Function.comp_apply]
      grw [two_mul, pow_add, mul_mul_mul_comm, map_mul_le_mul, pow_add, div_mul_div_comm] }

theorem tendsto_seminormFromConst (x : R) :
    Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (seminormFromConst c f x)) :=
  tendsto_atTop_ciInf (seminormFromConst_seq_antitone c f x) (seminormFromConst_bddBelow c f x)

theorem seminormFromConst_def (x : R) :
    seminormFromConst c f x = iInf (seminormFromConst_seq c f x) := by
  rfl

theorem seminormFromConst_one_le : seminormFromConst c f 1 ≤ 1 := by
  apply le_of_tendsto (tendsto_seminormFromConst c f 1) (eventually_atTop.mpr ⟨1, fun n hn ↦ ?_⟩)
  simp only [seminormFromConst_seq]
  grw [one_mul, map_pow_le_pow f c (ne_of_gt hn), div_self_le_one]

/-- The function `seminormFromConst c f` is bounded above by `f`. -/
theorem seminormFromConst_le_seminorm (x : R) : seminormFromConst c f x ≤ f x :=
  le_of_tendsto' (tendsto_seminormFromConst c f x) (seminormFromConst_le c f x)

variable {c f}
variable (hc : f c ≠ 0) (hpm : IsPowMul f)

include hc hpm

/-- If `1 ≤ n`, then `seminormFromConst_seq c f 1 n = 1`. -/
theorem seminormFromConst_seq_one (n : ℕ) (hn : 1 ≤ n) : seminormFromConst_seq c f 1 n = 1 := by
  simp only [seminormFromConst_seq]
  rw [one_mul, hpm _ hn, div_self (pow_ne_zero n hc)]

theorem seminormFromConst_one : seminormFromConst c f 1 = 1 :=
  tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst c f 1)
    tendsto_const_nhds (eventually_atTop.mpr ⟨1, seminormFromConst_seq_one hc hpm⟩)

omit hpm in
theorem seminormFromConst_isNonarchimedean (hna : IsNonarchimedean f) :
    IsNonarchimedean (seminormFromConst c f) := fun x y ↦ by
  apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst c f (x + y)) <|
    (tendsto_seminormFromConst c f x).max (tendsto_seminormFromConst c f y)
  intro n
  simp only [seminormFromConst_seq]
  grw [add_mul, hna _, max_div_div_right (by positivity)]

omit hc in
theorem seminormFromConst_isPowMul : IsPowMul (seminormFromConst c f) := fun x m hm ↦ by
  refine tendsto_nhds_unique_of_forall ((tendsto_seminormFromConst c f (x ^ m)).comp
      (strictMono_mul_right_of_pos hm).tendsto_atTop)
    ((tendsto_seminormFromConst c f x).pow m) fun n ↦ ?_
  simp only [seminormFromConst_seq, Function.comp_apply]
  rw [div_pow, ← hpm _ hm, mul_pow, pow_mul, pow_mul]

/-- If `x : R` is multiplicative for `f`, then `seminormFromConst c f x = f x`. -/
theorem seminormFromConst_apply_of_isMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) :
    seminormFromConst c f x = f x :=
  have hlim : Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (f x)) := by
    have hseq : seminormFromConst_seq c f x = fun _n ↦ f x := by
      ext n
      by_cases hn : n = 0
      · simp only [seminormFromConst_seq, hn, pow_zero, mul_one, div_one]
      · simp only [seminormFromConst_seq, hx (c ^ n), hpm _ (Nat.one_le_iff_ne_zero.mpr hn),
          mul_div_assoc, div_self (pow_ne_zero n hc), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst c f x) hlim

/-- If `x : R` is multiplicative for `f`, then it is multiplicative for
  `seminormFromConst c f`. -/
theorem seminormFromConst_isMul_of_isMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromConst c f (x * y) =
      seminormFromConst c f x * seminormFromConst c f y :=
  have hlim : Tendsto (seminormFromConst_seq c f (x * y)) atTop
      (𝓝 (seminormFromConst c f x * seminormFromConst c f y)) := by
    rw [seminormFromConst_apply_of_isMul hc hpm hx]
    have hseq : seminormFromConst_seq c f (x * y) =
        fun n ↦ f x * seminormFromConst_seq c f y n := by
      ext n
      simp only [seminormFromConst_seq, mul_assoc, hx, mul_div_assoc]
    simpa [hseq] using (tendsto_seminormFromConst c f y).const_mul _
  tendsto_nhds_unique (tendsto_seminormFromConst c f (x * y)) hlim

theorem seminormFromConst_apply_c : seminormFromConst c f c = f c :=
  have hlim : Tendsto (seminormFromConst_seq c f c) atTop (𝓝 (f c)) := by
    have hseq : seminormFromConst_seq c f c = fun _n ↦ f c := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_comm, ← pow_succ, hpm _ le_add_self, pow_succ, mul_comm, mul_div_assoc,
        div_self (pow_ne_zero n hc), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst c f c) hlim

theorem seminormFromConst_const_mul (x : R) :
    seminormFromConst c f (c * x) =
      seminormFromConst c f c * seminormFromConst c f x := by
  have hlim : Tendsto (fun n ↦ seminormFromConst_seq c f x (n + 1)) atTop
      (𝓝 (seminormFromConst c f x)) := by
    apply (tendsto_seminormFromConst c f x).comp
      (tendsto_atTop_atTop_of_monotone add_left_mono _)
    rintro n; use n; lia
  rw [seminormFromConst_apply_c hc hpm]
  apply tendsto_nhds_unique (tendsto_seminormFromConst c f (c * x))
  have hterm : seminormFromConst_seq c f (c * x) =
      fun n ↦ f c * seminormFromConst_seq c f x (n + 1) := by
    simp only [seminormFromConst_seq_def]
    ext n
    ring_nf
    rw [mul_assoc _ (f c), mul_inv_cancel₀ hc, mul_one]
  simpa [hterm] using tendsto_const_nhds.mul hlim

end Ring

section Field

variable {F K : Type*} [NormedField F] [Field K] [Algebra F K]

/-- If `K` is a field, the function `seminormFromConst` is a `RingNorm` on `K`. -/
def normFromConst {k : K} {g : RingSeminorm K} (hg_k : g k ≠ 0)
    (hg_pm : IsPowMul g) : RingNorm K :=
  (seminormFromConst k g).toRingNorm (RingSeminorm.ne_zero_iff.mpr
    ⟨k, by rwa [seminormFromConst_apply_c hg_k hg_pm]⟩)

@[simp]
theorem seminormFromConstRingNormOfField_toFun {k : K} {g : RingSeminorm K}
    (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) :
    ⇑(normFromConst hg_k hg_pm) = seminormFromConst k g :=
  rfl

theorem seminormFromConstRingNormOfField_def {k : K} {g : RingSeminorm K}
    (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) (x : K) :
    normFromConst hg_k hg_pm x = seminormFromConst k g x := rfl

/-- If `K` is a field, `seminormFromConst` applied to an `AlgebraNorm` is an `AlgebraNorm`. -/
def algNormFromConst {k : K} {g : AlgebraNorm F K} (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) :
    AlgebraNorm F K where
  __ := normFromConst hg_k hg_pm
  smul' x y := by
    have hx : g (algebraMap F K x) = ‖x‖ := by
      have hg1 : g 1 = 1 := by simpa [map_ne_zero_iff_ne_zero, sq] using hg_pm 1 one_le_two
      rw [Algebra.algebraMap_eq_smul_one, map_smul_eq_mul, hg1, mul_one]
    have hy y : g (algebraMap F K x * y) = g (algebraMap F K x) * g y := by
      rw [← Algebra.smul_def, map_smul_eq_mul, hx]
    simp [Algebra.smul_def, seminormFromConst_isMul_of_isMul hg_k hg_pm hy y,
      seminormFromConst_apply_of_isMul hg_k hg_pm hy, hx]

@[simp]
theorem algNormFromConst_toFun {k : K} {g : AlgebraNorm F K} (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) :
    ⇑(algNormFromConst hg_k hg_pm) = seminormFromConst k g.toRingSeminorm :=
  rfl

theorem algNormFromConst_def {k x : K} {g : AlgebraNorm F K} (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) :
    algNormFromConst hg_k hg_pm x = seminormFromConst k g.toRingSeminorm x :=
  rfl

end Field
