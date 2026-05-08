/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# SeminormFromConst


In this file, we prove [BGR, Proposition 1.3.2/2][bosch-guntzer-remmert] : starting from a
power-multiplicative seminorm on a commutative ring `R` and a nonzero `c : R`, we create a new
power-multiplicative seminorm for which `c` is multiplicative.

## Main Definitions

* `seminormFromConst'` : the real-valued function sending `x ∈ R` to the limit of
  `(f (x * c^n))/((f c)^n)`.
* `seminormFromConst` : the function `seminormFromConst'` as a `RingSeminorm` on `R`.


## Main Results
* `seminormFromConst_isNonarchimedean` : the function `seminormFromConst' c f`
  is nonarchimedean when f is nonarchimedean.
* `seminormFromConst_isPowMul` : the function `seminormFromConst' c f`
  is power-multiplicative.
* `seminormFromConst_const_mul` : for every `x : R`, `seminormFromConst' c f (c * x)`
  equals the product `seminormFromConst' c f c * seminormFromConst' c f x`.

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

/-- For a ring seminorm `f` on `R` and `c ∈ R`, the sequence given by `(f (x * c^n))/((f c)^n)`. -/
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

variable {f}

/-- `seminormFromConst_seq c f 0` is the constant sequence zero. -/
theorem seminormFromConst_seq_zero (hf : f 0 = 0) : seminormFromConst_seq c f 0 = 0 := by
  rw [seminormFromConst_seq_def]
  ext n
  rw [zero_mul, hf, zero_div, Pi.zero_apply]

variable {c}
variable (hf1 : f 1 ≤ 1) (hc : f c ≠ 0) (hpm : IsPowMul f)
include hpm hc

/-- If `1 ≤ n`, then `seminormFromConst_seq c f 1 n = 1`. -/
theorem seminormFromConst_seq_one (n : ℕ) (hn : 1 ≤ n) : seminormFromConst_seq c f 1 n = 1 := by
  simp only [seminormFromConst_seq]
  rw [one_mul, hpm _ hn, div_self (pow_ne_zero n hc)]

include hf1

/-- `seminormFromConst_seq c f x` is antitone. -/
theorem seminormFromConst_seq_antitone (x : R) : Antitone (seminormFromConst_seq c f x) := by
  intro m n hmn
  simp only [seminormFromConst_seq]
  nth_rw 1 [← Nat.add_sub_of_le hmn]
  rw [pow_add, ← mul_assoc]
  have hc_pos : 0 < f c := lt_of_le_of_ne (apply_nonneg f _) hc.symm
  apply le_trans ((div_le_div_iff_of_pos_right (pow_pos hc_pos _)).mpr (map_mul_le_mul f _ _))
  cases hmn.eq_or_lt with
  | inl heq =>
    have hnm : n - m = 0 := by rw [heq, Nat.sub_self n]
    rw [hnm, heq, div_le_div_iff_of_pos_right (pow_pos hc_pos _), pow_zero]
    conv_rhs => rw [← mul_one (f (x * c ^ n))]
    gcongr
  | inr hlt =>
    have h1 : 1 ≤ n - m := by
      rw [Nat.one_le_iff_ne_zero]
      exact Nat.sub_ne_zero_of_lt hlt
    rw [hpm c h1, mul_div_assoc, div_eq_mul_inv, pow_sub₀ _ hc hmn, mul_assoc, mul_comm (f c ^ m)⁻¹,
      ← mul_assoc (f c ^ n), mul_inv_cancel₀ (pow_ne_zero n hc), one_mul, div_eq_mul_inv]

/-- The real-valued function sending `x ∈ R` to the limit of `(f (x * c^n))/((f c)^n)`. -/
def seminormFromConst' (c : R) (f : RingSeminorm R) (x : R) : ℝ :=
  iInf (seminormFromConst_seq c f x)

/-- We prove that `seminormFromConst' c f x` is the limit of the sequence
  `seminormFromConst_seq c f x` as `n` tends to infinity. -/
theorem tendsto_seminormFromConst_seq_atTop (x : R) :
    Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (seminormFromConst' c f x)) :=
  tendsto_atTop_ciInf (seminormFromConst_seq_antitone hf1 hc hpm x)
    (seminormFromConst_bddBelow c f x)

@[deprecated (since := "2026-01-14")]
alias seminormFromConst_isLimit := tendsto_seminormFromConst_seq_atTop

theorem seminormFromConst_one : seminormFromConst' c f 1 = 1 := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 1)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop, ge_iff_le]
  exact ⟨1, seminormFromConst_seq_one hc hpm⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The function `seminormFromConst` is a `RingSeminorm` on `R`. -/
def seminormFromConst : RingSeminorm R where
  toFun     := seminormFromConst' c f
  map_zero' := tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 0)
    (by simpa [seminormFromConst_seq_zero c (map_zero _)] using tendsto_const_nhds)
  add_le' x y := by
    apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y)) <|
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).add
        (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
    intro n
    have h_add : f ((x + y) * c ^ n) ≤ f (x * c ^ n) + f (y * c ^ n) := by
      simp only [add_mul, map_add_le_add f _ _]
    simp only [seminormFromConst_seq, ← add_div]
    gcongr
  neg' x := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (-x))
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
    simp only [EventuallyEq, eventually_atTop]
    use 0
    simp only [seminormFromConst_seq, neg_mul, map_neg_eq_map, zero_le, implies_true]
  mul_le' x y := by
    have hlim : Tendsto (fun n ↦ seminormFromConst_seq c f (x * y) (2 * n)) atTop
        (𝓝 (seminormFromConst' c f (x * y))) := by
      apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)).comp
        (tendsto_atTop_atTop_of_monotone (fun _ _ hnm ↦ by
          simp only [mul_le_mul_iff_right₀, Nat.succ_pos', hnm]) _)
      · rintro n; use n; lia
    refine le_of_tendsto_of_tendsto' hlim ((tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).mul
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)) (fun n ↦ ?_)
    simp only [seminormFromConst_seq]
    rw [div_mul_div_comm, ← pow_add, two_mul,
      div_le_div_iff_of_pos_right (pow_pos (lt_of_le_of_ne (apply_nonneg f _) hc.symm) _), pow_add,
      ← mul_assoc, mul_comm (x * y), ← mul_assoc, mul_assoc, mul_comm (c ^ n)]
    exact map_mul_le_mul f (x * c ^ n) (y * c ^ n)

theorem seminormFromConst_def (x : R) :
    seminormFromConst hf1 hc hpm x = seminormFromConst' c f x :=
  rfl

theorem seminormFromConst_one_le : seminormFromConst' c f 1 ≤ 1 :=
  le_of_eq (seminormFromConst_one hf1 hc hpm)

theorem seminormFromConst_isNonarchimedean (hna : IsNonarchimedean f) :
    IsNonarchimedean (seminormFromConst' c f) := fun x y ↦ by
  apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y)) <|
    (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).max
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
  intro n
  have hmax : f ((x + y) * c ^ n) ≤ max (f (x * c ^ n)) (f (y * c ^ n)) := by
    simp only [add_mul, hna _ _]
  rw [le_max_iff] at hmax ⊢
  unfold seminormFromConst_seq
  apply hmax.imp <;> intro <;> gcongr

theorem seminormFromConst_isPowMul : IsPowMul (seminormFromConst' c f) := fun x m hm ↦ by
  simp only [seminormFromConst']
  have hlim : Tendsto (fun n ↦ seminormFromConst_seq c f (x ^ m) (m * n)) atTop
      (𝓝 (seminormFromConst' c f (x ^ m))) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x ^ m)).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ hnk ↦ mul_le_mul_right hnk m) _)
    rintro n; use n; exact le_mul_of_one_le_left' hm
  apply tendsto_nhds_unique hlim
  convert (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).pow m using 1
  ext n
  simp only [seminormFromConst_seq, div_pow, ← hpm _ hm, ← pow_mul, mul_pow, mul_comm m n]

/-- The function `seminormFromConst' c f` is bounded above by `f`. -/
theorem seminormFromConst_le_seminorm (x : R) : seminormFromConst' c f x ≤ f x := by
  apply le_of_tendsto (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
  simp only [eventually_atTop, ge_iff_le]
  use 1
  intro n hn
  rw [seminormFromConst_seq, div_le_iff₀ (by positivity), ← hpm c hn]
  exact map_mul_le_mul ..

/-- If `x : R` is multiplicative for `f`, then `seminormFromConst' c f x = f x`. -/
theorem seminormFromConst_apply_of_isMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) :
    seminormFromConst' c f x = f x :=
  have hlim : Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (f x)) := by
    have hseq : seminormFromConst_seq c f x = fun _n ↦ f x := by
      ext n
      by_cases hn : n = 0
      · simp only [seminormFromConst_seq, hn, pow_zero, mul_one, div_one]
      · simp only [seminormFromConst_seq, hx (c ^ n), hpm _ (Nat.one_le_iff_ne_zero.mpr hn),
          mul_div_assoc, div_self (pow_ne_zero n hc), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x) hlim

/-- If `x : R` is multiplicative for `f`, then it is multiplicative for
  `seminormFromConst' c f`. -/
theorem seminormFromConst_isMul_of_isMul {x : R} (hx : ∀ y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromConst' c f (x * y) =
      seminormFromConst' c f x * seminormFromConst' c f y :=
  have hlim : Tendsto (seminormFromConst_seq c f (x * y)) atTop
      (𝓝 (seminormFromConst' c f x * seminormFromConst' c f y)) := by
    rw [seminormFromConst_apply_of_isMul hf1 hc hpm hx]
    have hseq : seminormFromConst_seq c f (x * y) =
        fun n ↦ f x * seminormFromConst_seq c f y n := by
      ext n
      simp only [seminormFromConst_seq, mul_assoc, hx, mul_div_assoc]
    simpa [hseq] using (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y).const_mul _
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)) hlim

theorem seminormFromConst_apply_c : seminormFromConst' c f c = f c :=
  have hlim : Tendsto (seminormFromConst_seq c f c) atTop (𝓝 (f c)) := by
    have hseq : seminormFromConst_seq c f c = fun _n ↦ f c := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_comm, ← pow_succ, hpm _ le_add_self, pow_succ, mul_comm, mul_div_assoc,
        div_self (pow_ne_zero n hc), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm c) hlim

theorem seminormFromConst_const_mul (x : R) :
    seminormFromConst' c f (c * x) =
      seminormFromConst' c f c * seminormFromConst' c f x := by
  have hlim : Tendsto (fun n ↦ seminormFromConst_seq c f x (n + 1)) atTop
      (𝓝 (seminormFromConst' c f x)) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).comp
      (tendsto_atTop_atTop_of_monotone add_left_mono _)
    rintro n; use n; lia
  rw [seminormFromConst_apply_c hf1 hc hpm]
  apply tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (c * x))
  have hterm : seminormFromConst_seq c f (c * x) =
      fun n ↦ f c * seminormFromConst_seq c f x (n + 1) := by
    simp only [seminormFromConst_seq_def]
    ext n
    ring_nf
    rw [mul_assoc _ (f c), mul_inv_cancel₀ hc, mul_one]
  simpa [hterm] using tendsto_const_nhds.mul hlim

end Ring

section Field

variable {K : Type*} [Field K]

/-- If `K` is a field, the function `seminormFromConst` is a `RingNorm` on `K`. -/
def normFromConst {k : K} {g : RingSeminorm K} (hg1 : g 1 ≤ 1) (hg_k : g k ≠ 0)
    (hg_pm : IsPowMul g) : RingNorm K :=
  (seminormFromConst hg1 hg_k hg_pm).toRingNorm (RingSeminorm.ne_zero_iff.mpr
    ⟨k, by rwa [seminormFromConst_def hg1 hg_k, seminormFromConst_apply_c hg1 hg_k hg_pm]⟩)

theorem seminormFromConstRingNormOfField_def {k : K} {g : RingSeminorm K} (hg1 : g 1 ≤ 1)
    (hg_k : g k ≠ 0) (hg_pm : IsPowMul g) (x : K) :
    normFromConst hg1 hg_k hg_pm x = seminormFromConst' k g x := rfl

end Field
