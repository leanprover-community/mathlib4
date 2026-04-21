/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Tactic.MoveAdd

/-! # Functions and measures of temperate growth -/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

noncomputable section

open scoped Nat NNReal ContDiff

open Asymptotics

variable {ι 𝕜 R D E F G H : Type*}

namespace Function

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function is called of temperate growth if it is smooth and all iterated derivatives are
polynomially bounded. -/
@[fun_prop]
def HasTemperateGrowth (f : E → F) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ (k : ℕ) (C : ℝ), ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ C * (1 + ‖x‖) ^ k

/-- A function has temperate growth if and only if it is smooth and its `n`-th iterated
derivative is `O((1 + ‖x‖) ^ k)` for some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.

TODO: when `E` is finite dimensional, this is equivalent to the derivatives being `O(‖x‖ ^ k)`
as `‖x‖ → ∞`.
-/
theorem hasTemperateGrowth_iff_isBigO {f : E → F} :
    f.HasTemperateGrowth ↔ ContDiff ℝ ∞ f ∧
      ∀ n, ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
  simp_rw [Asymptotics.isBigO_top]
  congrm ContDiff ℝ ∞ f ∧ (∀ n, ∃ k C, ∀ x, _ ≤ C * ?_)
  rw [norm_pow, Real.norm_of_nonneg (by positivity)]

/-- If `f` has temperate growth, then its `n`-th iterated derivative is `O((1 + ‖x‖) ^ k)` for
some `k : ℕ` (depending on `n`).

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.
-/
theorem HasTemperateGrowth.isBigO {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (n : ℕ) :
    ∃ k, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) :=
  Function.hasTemperateGrowth_iff_isBigO.mp hf_temperate |>.2 n

/-- If `f` has temperate growth, then for any `N : ℕ` one can find `k` such that *all* iterated
derivatives of `f` of order `≤ N` are `O((1 + ‖x‖) ^ k)`.

Note that the `O` here is with respect to the `⊤` filter, meaning that the bound holds everywhere.
-/
theorem HasTemperateGrowth.isBigO_uniform {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (N : ℕ) :
    ∃ k, ∀ n ≤ N, iteratedFDeriv ℝ n f =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
  choose k hk using hf_temperate.isBigO
  use (Finset.range (N + 1)).sup k
  intro n hn
  refine (hk n).trans (isBigO_of_le _ fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  gcongr
  · simp
  · exact Finset.le_sup (by simpa using hn)

theorem HasTemperateGrowth.norm_iteratedFDeriv_le_uniform {f : E → F}
    (hf_temperate : f.HasTemperateGrowth) (n : ℕ) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ N ≤ n, ∀ x : E, ‖iteratedFDeriv ℝ N f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  rcases hf_temperate.isBigO_uniform n with ⟨k, hk⟩
  set F := fun x (N : Fin (n + 1)) ↦ iteratedFDeriv ℝ N f x
  have : F =O[⊤] (fun x ↦ (1 + ‖x‖) ^ k) := by
    simp_rw [F, isBigO_pi, Fin.forall_iff, Nat.lt_succ_iff]
    exact hk
  rcases this.exists_nonneg with ⟨C, C_nonneg, hC⟩
  simp (discharger := positivity) only [isBigOWith_top, Real.norm_of_nonneg,
    pi_norm_le_iff_of_nonneg, Fin.forall_iff, Nat.lt_succ_iff] at hC
  exact ⟨k, C, C_nonneg, fun N hN x ↦ hC x N hN⟩

@[deprecated (since := "2025-10-30")]
alias HasTemperateGrowth.norm_iteratedFDeriv_le_uniform_aux :=
  HasTemperateGrowth.norm_iteratedFDeriv_le_uniform

lemma HasTemperateGrowth.of_fderiv {f : E → F}
    (h'f : Function.HasTemperateGrowth (fderiv ℝ f)) (hf : Differentiable ℝ f) {k : ℕ} {C : ℝ}
    (h : ∀ x, ‖f x‖ ≤ C * (1 + ‖x‖) ^ k) :
    Function.HasTemperateGrowth f := by
  refine ⟨contDiff_succ_iff_fderiv.2 ⟨hf, by simp, h'f.1⟩, fun n ↦ ?_⟩
  rcases n with rfl | m
  · exact ⟨k, C, fun x ↦ by simpa using h x⟩
  · rcases h'f.2 m with ⟨k', C', h'⟩
    refine ⟨k', C', ?_⟩
    simpa [iteratedFDeriv_succ_eq_comp_right] using h'

@[fun_prop]
lemma HasTemperateGrowth.zero :
    Function.HasTemperateGrowth (fun _ : E ↦ (0 : F)) := by
  refine ⟨contDiff_const, fun n ↦ ⟨0, 0, fun x ↦ ?_⟩⟩
  simp

@[fun_prop, simp]
lemma HasTemperateGrowth.const (c : F) :
    Function.HasTemperateGrowth (fun _ : E ↦ c) :=
  .of_fderiv (by simpa using .zero) (differentiable_const c) (k := 0) (C := ‖c‖) (fun x ↦ by simp)

@[fun_prop]
lemma _root_.HasCompactSupport.hasTemperateGrowth {f : E → F} (h₁ : HasCompactSupport f)
    (h₂ : ContDiff ℝ ∞ f) : f.HasTemperateGrowth := by
  refine ⟨h₂, fun n ↦ ?_⟩
  set g := fun x ↦ ‖iteratedFDeriv ℝ n f x‖
  have hg : Continuous g := (h₂.continuous_iteratedFDeriv <| mod_cast le_top).norm
  obtain ⟨x₀, hx₀⟩ := hg.exists_forall_ge_of_hasCompactSupport ((h₁.iteratedFDeriv _).norm)
  refine ⟨0, g x₀, fun x ↦ ?_⟩
  simpa using hx₀ x

/-- Composition of two temperate growth functions is of temperate growth.

Version where the outer function `g` is only of temperate growth on the image of inner function
`f`. -/
theorem HasTemperateGrowth.comp' [NormedAddCommGroup D] [NormedSpace ℝ D] {g : E → F} {f : D → E}
    {t : Set E} (ht : Set.range f ⊆ t) (ht' : UniqueDiffOn ℝ t) (hg₁ : ContDiffOn ℝ ∞ g t)
    (hg₂ : ∀ N, ∃ k C, ∃ (_hC : 0 ≤ C), ∀ n ≤ N, ∀ x ∈ t,
    ‖iteratedFDerivWithin ℝ n g t x‖ ≤ C * (1 + ‖x‖) ^ k)
    (hf : f.HasTemperateGrowth) : (g ∘ f).HasTemperateGrowth := by
  refine ⟨hg₁.comp_contDiff hf.1 (ht ⟨·, rfl⟩), fun n ↦ ?_⟩
  obtain ⟨k₁, C₁, hC₁, h₁⟩ := hf.norm_iteratedFDeriv_le_uniform n
  obtain ⟨k₂, C₂, hC₂, h₂⟩ := hg₂ n
  have h₁' : ∀ x, ‖f x‖ ≤ C₁ * (1 + ‖x‖) ^ k₁ := by simpa using h₁ 0 (zero_le _)
  set C₃ := ∑ k ∈ Finset.range (k₂ + 1), C₂ * (k₂.choose k : ℝ) * (C₁ ^ k)
  use k₁ * k₂ + k₁ * n, n ! * C₃ * (1 + C₁) ^ n
  intro x
  have hg' : ∀ i, i ≤ n → ‖iteratedFDerivWithin ℝ i g t (f x)‖ ≤ C₃ * (1 + ‖x‖) ^ (k₁ * k₂) := by
    intro i hi
    calc _ ≤ C₂ * (1 + ‖f x‖) ^ k₂ := h₂ i hi (f x) (ht ⟨x, rfl⟩)
      _ = ∑ i ∈ Finset.range (k₂ + 1), C₂ * (‖f x‖ ^ i * (k₂.choose i)) := by
        rw [add_comm, add_pow, Finset.mul_sum]
        simp
      _ ≤ ∑ i ∈ Finset.range (k₂ + 1), C₂ * (k₂.choose i) * C₁ ^ i * (1 + ‖x‖) ^ (k₁ * k₂) := by
        apply Finset.sum_le_sum
        intro i hi
        grw [h₁']
        simp_rw [mul_pow, ← pow_mul]
        move_mul [← (k₂.choose _ : ℝ), C₂]
        gcongr
        · simp
        · grind
      _ = _ := by simp [C₃, Finset.sum_mul]
  have hf' : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ i := by
    intro i hi hi'
    calc _ ≤ C₁ * (1 + ‖x‖) ^ k₁ := h₁ i hi' x
      _ ≤ (1 + C₁) * (1 + ‖x‖) ^ k₁ := by gcongr; simp
      _ ≤ _ := by
        apply le_self_pow₀ (one_le_mul_of_one_le_of_one_le (by simp [hC₁]) (by simp [one_le_pow₀]))
        grind
  calc _ ≤ n ! * (C₃ * (1 + ‖x‖) ^ (k₁ * k₂)) * ((1 + C₁) * (1 + ‖x‖) ^ k₁) ^ n :=
      norm_iteratedFDeriv_comp_le' ht ht' hg₁ hf.1 (mod_cast le_top) x hg' hf'
    _ = _ := by rw [mul_pow, ← pow_mul, pow_add]; ring

/-- Composition of two temperate growth functions is of temperate growth. -/
@[fun_prop]
theorem HasTemperateGrowth.comp [NormedAddCommGroup D] [NormedSpace ℝ D] {g : E → F} {f : D → E}
    (hg : g.HasTemperateGrowth) (hf : f.HasTemperateGrowth) : (g ∘ f).HasTemperateGrowth := by
  apply hf.comp' (t := Set.univ)
  · simp
  · simp
  · rw [contDiffOn_univ]
    exact hg.1
  · simpa [iteratedFDerivWithin_univ] using hg.norm_iteratedFDeriv_le_uniform

section Addition

variable {f g : E → F}

@[to_fun (attr := fun_prop)]
theorem HasTemperateGrowth.neg (hf : f.HasTemperateGrowth) : (-f).HasTemperateGrowth := by
  refine ⟨hf.1.neg, fun n ↦ ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 n
  exact ⟨k, C, fun x ↦ by simpa [iteratedFDeriv_neg_apply] using h x⟩

@[to_fun (attr := fun_prop)]
theorem HasTemperateGrowth.add (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (f + g).HasTemperateGrowth := by
  rw [hasTemperateGrowth_iff_isBigO] at *
  refine ⟨hf.1.add hg.1, fun n ↦ ?_⟩
  obtain ⟨k₁, h₁⟩ := hf.2 n
  obtain ⟨k₂, h₂⟩ := hg.2 n
  use max k₁ k₂
  rw [iteratedFDeriv_add (hf.1.of_le <| mod_cast le_top) (hg.1.of_le <| mod_cast le_top)]
  have : 1 ≤ᶠ[⊤] fun (x : E) ↦ 1 + ‖x‖ := by
    filter_upwards with _ using (le_add_iff_nonneg_right _).mpr (by positivity)
  exact (h₁.trans (IsBigO.pow_of_le_right this (k₁.le_max_left k₂))).add
    (h₂.trans (IsBigO.pow_of_le_right this (k₁.le_max_right k₂)))

@[to_fun (attr := fun_prop)]
theorem HasTemperateGrowth.sub (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    (f - g).HasTemperateGrowth := by
  convert hf.add hg.neg using 1
  grind

@[fun_prop]
theorem HasTemperateGrowth.sum {f : ι → E → F} {s : Finset ι}
    (hf : ∀ i ∈ s, (f i).HasTemperateGrowth) : (∑ i ∈ s, f i ·).HasTemperateGrowth := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    obtain ⟨hf, h⟩ := by simpa using hf
    simpa [has] using hf.add (ih h)

end Addition

section Multiplication

variable [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- The product of two functions of temperate growth is again of temperate growth.

Version for bilinear maps. -/
@[fun_prop]
theorem _root_.ContinuousLinearMap.bilinear_hasTemperateGrowth [NormedSpace 𝕜 E]
    (B : E →L[𝕜] F →L[𝕜] G) {f : D → E} {g : D → F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (fun x ↦ B (f x) (g x)).HasTemperateGrowth := by
  rw [Function.hasTemperateGrowth_iff_isBigO]
  constructor
  · apply (B.bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hf.1.prodMk hg.1)
  intro n
  rcases hf.isBigO_uniform n with ⟨k1, h1⟩
  rcases hg.isBigO_uniform n with ⟨k2, h2⟩
  use k1 + k2
  have estimate (x : D) : ‖iteratedFDeriv ℝ n (fun x ↦ B (f x) (g x)) x‖ ≤
      ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ :=
    (B.bilinearRestrictScalars ℝ).norm_iteratedFDeriv_le_of_bilinear hf.1 hg.1 x (mod_cast le_top)
  refine (IsBigO.of_norm_le estimate).trans (.const_mul_left (.sum fun i hi ↦ ?_) _)
  simp_rw [mul_assoc, pow_add]
  refine .const_mul_left (.mul (h1 i ?_).norm_left (h2 (n - i) ?_).norm_left) _ <;>
  grind

lemma HasTemperateGrowth.id : Function.HasTemperateGrowth (id : E → E) := by
  apply Function.HasTemperateGrowth.of_fderiv (k := 1) (C := 1)
  · convert Function.HasTemperateGrowth.const (ContinuousLinearMap.id ℝ E)
    exact fderiv_id'
  · apply differentiable_id
  · simp

@[fun_prop]
lemma HasTemperateGrowth.id' : Function.HasTemperateGrowth (fun (x : E) ↦ x) :=
  Function.HasTemperateGrowth.id

/-- The product of two functions of temperate growth is again of temperate growth.

Version for scalar multiplication. -/
@[to_fun (attr := fun_prop)]
theorem HasTemperateGrowth.smul {f : E → 𝕜} {g : E → F} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f • g).HasTemperateGrowth :=
  (ContinuousLinearMap.lsmul ℝ 𝕜).bilinear_hasTemperateGrowth hf hg

variable [NormedRing R] [NormedAlgebra ℝ R]

/-- The product of two functions of temperate growth is again of temperate growth. -/
@[to_fun (attr := fun_prop)]
theorem HasTemperateGrowth.mul {f g : E → R} (hf : f.HasTemperateGrowth)
    (hg : g.HasTemperateGrowth) : (f * g).HasTemperateGrowth :=
  (ContinuousLinearMap.mul ℝ R).bilinear_hasTemperateGrowth hf hg

@[to_fun (attr := fun_prop)]
theorem HasTemperateGrowth.pow {f : E → R} (hf : f.HasTemperateGrowth) (k : ℕ) :
    (f ^ k).HasTemperateGrowth := by
  induction k with
  | zero => simpa only [pow_zero] using HasTemperateGrowth.const 1
  | succ k IH => rw [pow_succ]; fun_prop

end Multiplication

@[fun_prop]
lemma _root_.ContinuousLinearMap.hasTemperateGrowth (f : E →L[ℝ] F) :
    Function.HasTemperateGrowth f := by
  apply Function.HasTemperateGrowth.of_fderiv ?_ f.differentiable (k := 1) (C := ‖f‖) (fun x ↦ ?_)
  · have : fderiv ℝ f = fun _ ↦ f := by ext1 v; simp only [ContinuousLinearMap.fderiv]
    simp [this]
  · exact (f.le_opNorm x).trans (by simp [mul_add])

@[fun_prop]
lemma _root_.ContinuousLinearEquiv.hasTemperateGrowth (f : E ≃L[ℝ] F) :
    Function.HasTemperateGrowth f :=
  f.toContinuousLinearMap.hasTemperateGrowth

@[fun_prop]
theorem Complex.hasTemperateGrowth_ofReal : Complex.ofReal.HasTemperateGrowth :=
  (Complex.ofRealCLM).hasTemperateGrowth

variable (𝕜) in
@[fun_prop]
theorem RCLike.hasTemperateGrowth_ofReal [RCLike 𝕜] : (RCLike.ofReal (K := 𝕜)).HasTemperateGrowth :=
  (RCLike.ofRealCLM (K := 𝕜)).hasTemperateGrowth

variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

@[fun_prop]
theorem hasTemperateGrowth_inner_left (c : H) : (inner ℝ · c).HasTemperateGrowth :=
  ((innerSL ℝ).flip c).hasTemperateGrowth

@[fun_prop]
theorem hasTemperateGrowth_inner_right (c : H) : (inner ℝ c ·).HasTemperateGrowth :=
  (innerSL ℝ c).hasTemperateGrowth

variable (H) in
@[fun_prop]
theorem hasTemperateGrowth_norm_sq : (fun (x : H) ↦ ‖x‖ ^ 2).HasTemperateGrowth := by
  apply _root_.Function.HasTemperateGrowth.of_fderiv (C := 1) (k := 2)
  · rw [fderiv_norm_sq]
    convert (2 • innerSL ℝ).hasTemperateGrowth
  · exact .norm_sq ℝ differentiable_id
  · intro x
    rw [norm_pow, norm_norm, one_mul, add_pow_two]
    exact le_add_of_nonneg_left (by positivity)

variable (H) in
/-- The Bessel potential `x ↦ (1 + ‖x‖ ^ 2) ^ r` has temperate growth. -/
@[fun_prop]
theorem hasTemperateGrowth_one_add_norm_sq_rpow (r : ℝ) :
    (fun (x : H) ↦ (1 + ‖x‖ ^ 2) ^ r).HasTemperateGrowth := by
  /- We prove this using that the composition of temperate functions is temperate.
  Since `x ^ r` is not smooth at the origin, we have to use `HasTemperateGrowth.comp'`, with any
  open set `t` that is contains the complement of the unit ball and does not contain the origin. -/
  set t := {y : ℝ | 1 / 2 < y}
  have ht : Set.range (fun (x : H) ↦ (1 + ‖x‖ ^ 2)) ⊆ t := by
    rintro - ⟨y, rfl⟩
    simp only [Set.mem_setOf_eq, t]
    exact lt_add_of_lt_add_left (c := 0) (by norm_num) (by positivity)
  have hdiff : ContDiffOn ℝ ∞ (fun x ↦ x ^ r) t :=
    contDiffOn_fun_id.rpow_const_of_ne fun x hx ↦ (lt_trans (by norm_num) hx).ne'
  have hunique : UniqueDiffOn ℝ t := (isOpen_lt' (1 / 2)).uniqueDiffOn
  apply HasTemperateGrowth.comp' ht hunique hdiff _ (by fun_prop)
  -- The remaining part of the proof is proving that `x ↦ x ^ r` has temperate growth on `t`.
  -- This could be generalized to `t := {y : ℝ | ε < y}` for any `0 < ε < 1` if necessary.
  intro N
  /- Since `x ^ r` for negative `r` blows up near the origin (and we can't take
  `t := {y : ℝ | 1 / 2 < y}`), we have to choose `k` later than `N - r` times some factor depending
  on `t`. -/
  obtain ⟨k, hk⟩ := exists_nat_ge (max r <| (N - r) * Real.log 2 / (Real.log (3 / 2)))
  have hk₁ : r ≤ k := le_sup_left.trans hk
  have hk₂ : Real.log 2 * (N - r) ≤ (Real.log (3 / 2)) * k := by
    have := le_sup_right.trans hk
    field_simp at this
    grind
  use k, ∑ k ∈ Finset.range (N + 1), ‖Polynomial.eval r (descPochhammer ℝ k)‖, by positivity
  intro n hn x hx
  have : ContDiffAt ℝ n (fun x ↦ x ^ r) x :=
    Real.contDiffAt_rpow_const <| Or.inl (lt_trans (by norm_num) hx).ne'
  -- We calculate the derivative of `x ^ r`.
  rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin,
    iteratedDerivWithin_eq_iteratedDeriv hunique this hx, iteratedDeriv_eq_iterate,
    Real.iter_deriv_rpow_const, norm_mul]
  gcongr 1
  · have : n ∈ Finset.range (N + 1) := by grind
    apply Finset.single_le_sum (fun _ _ ↦ by positivity) this
  -- It remains to show that `‖x ^ (r - n)‖ ≤ (1 + ‖x‖) ^ k`:
  have hx' : 1 / 2 < x := by simpa [t] using hx
  have hx'' : 0 < x := lt_of_lt_of_le (by norm_num) hx'.le
  simp only [Real.norm_eq_abs]
  apply (Real.abs_rpow_le_abs_rpow _ _).trans
  -- We consider the two cases `n ≤ r` and `r < n`.
  by_cases! h : 0 ≤ r - n
  · have : r - n ≤ k := by simpa using hk₁.trans (by simp)
    rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow (by positivity) (by simp) h).trans
      (Real.rpow_le_rpow_of_exponent_le (by simp) this)
  have h : 0 < n - r := by grind
  calc
    /- In the case `0 < n - r`, we need the factor `Real.log 2 / (Real.log (3 / 2))` to control
    the growth near `‖x‖ = 1/2`. -/
    _ = x ^ (-(n - r)) := by
      rw [neg_sub]
      congr
      simpa using hx''.le
    _ ≤ (2 : ℝ) ^ (n - r) := by
      simp only [one_div, Set.mem_setOf_eq, t] at hx
      rw [Real.rpow_neg_eq_inv_rpow]
      gcongr
      exact ((inv_lt_comm₀ hx'' (by norm_num)).mpr hx).le
    _ = Real.exp (Real.log 2 * (n - r)) := by
      rw [Real.rpow_def_of_pos]
      norm_num
    _ ≤ Real.exp (Real.log (3 / 2) * k) := by
      gcongr 1
      apply le_trans _ hk₂
      gcongr
    _ ≤ (3 / 2) ^ k := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos]
      norm_num
    _ ≤ _ := by
      gcongr
      grind

end Function

namespace MeasureTheory.Measure

variable [NormedAddCommGroup E] [MeasurableSpace E]

open Module
open scoped ENNReal

/-- A measure `μ` has temperate growth if there is an `n : ℕ` such that `(1 + ‖x‖) ^ (- n)` is
`μ`-integrable. -/
class HasTemperateGrowth (μ : Measure E) : Prop where
  exists_integrable : ∃ (n : ℕ), Integrable (fun x ↦ (1 + ‖x‖) ^ (- (n : ℝ))) μ

open Classical in
/-- An integer exponent `l` such that `(1 + ‖x‖) ^ (-l)` is integrable if `μ` has
temperate growth. -/
def integrablePower (μ : Measure E) : ℕ :=
  if h : μ.HasTemperateGrowth then h.exists_integrable.choose else 0

lemma integrable_pow_neg_integrablePower
    (μ : Measure E) [h : μ.HasTemperateGrowth] :
    Integrable (fun x ↦ (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ))) μ := by
  simpa [Measure.integrablePower, h] using h.exists_integrable.choose_spec

instance _root_.MeasureTheory.IsFiniteMeasure.instHasTemperateGrowth {μ : Measure E}
    [h : IsFiniteMeasure μ] : μ.HasTemperateGrowth := ⟨⟨0, by simp⟩⟩

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
instance IsAddHaarMeasure.instHasTemperateGrowth {μ : Measure E}
    [h : μ.IsAddHaarMeasure] : μ.HasTemperateGrowth :=
  ⟨⟨finrank ℝ E + 1, by apply integrable_one_add_norm; norm_num⟩⟩

/-- Pointwise inequality to control `x ^ k * f` in terms of `1 / (1 + x) ^ l` if one controls both
`f` (with a bound `C₁`) and `x ^ (k + l) * f` (with a bound `C₂`). This will be used to check
integrability of `x ^ k * f x` when `f` is a Schwartz function, and to control explicitly its
integral in terms of suitable seminorms of `f`. -/
lemma _root_.pow_mul_le_of_le_of_pow_mul_le {C₁ C₂ : ℝ} {k l : ℕ} {x f : ℝ} (hx : 0 ≤ x)
    (hf : 0 ≤ f) (h₁ : f ≤ C₁) (h₂ : x ^ (k + l) * f ≤ C₂) :
    x ^ k * f ≤ 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : ℝ)) := by
  have : 0 ≤ C₂ := le_trans (by positivity) h₂
  have : 2 ^ l * (C₁ + C₂) * (1 + x) ^ (- (l : ℝ)) = ((1 + x) / 2) ^ (-(l : ℝ)) * (C₁ + C₂) := by
    rw [Real.div_rpow (by positivity) zero_le_two]
    simp [div_eq_inv_mul, ← Real.rpow_neg_one, ← Real.rpow_mul]
    ring
  rw [this]
  rcases le_total x 1 with h'x | h'x
  · gcongr
    · apply (pow_le_one₀ hx h'x).trans
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      · positivity
      · linarith
      · simp
    · linarith
  · calc
    x ^ k * f = x ^ (-(l : ℝ)) * (x ^ (k + l) * f) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← mul_assoc, ← Real.rpow_add (by positivity)]
      simp
    _ ≤ ((1 + x) / 2) ^ (-(l : ℝ)) * (C₁ + C₂) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by simp)
      · exact h₂.trans (by linarith)

variable [NormedAddCommGroup F]

variable [BorelSpace E] [SecondCountableTopology E] in
/-- Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable `l`, then
`x ^ k * f` is integrable. The bounds are not relevant for the integrability conclusion, but they
are relevant for bounding the integral in `integral_pow_mul_le_of_le_of_pow_mul_le`. We formulate
the two lemmas with the same set of assumptions for ease of applications. -/
lemma _root_.integrable_of_le_of_pow_mul_le {μ : Measure E} [μ.HasTemperateGrowth] {f : E → F}
    {C₁ C₂ : ℝ} {k : ℕ} (hf : ∀ x, ‖f x‖ ≤ C₁)
    (h'f : ∀ x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ ≤ C₂) (h''f : AEStronglyMeasurable f μ) :
    Integrable (fun x ↦ ‖x‖ ^ k * ‖f x‖) μ := by
  apply ((integrable_pow_neg_integrablePower μ).const_mul (2 ^ μ.integrablePower * (C₁ + C₂))).mono'
  · exact AEStronglyMeasurable.mul (aestronglyMeasurable_id.norm.pow _) h''f.norm
  · filter_upwards with v
    simp only [norm_mul, norm_pow, norm_norm]
    apply pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)

/-- Given a function such that `f` and `x ^ (k + l) * f` are bounded for a suitable `l`, then
one can bound explicitly the integral of `x ^ k * f`. -/
lemma _root_.integral_pow_mul_le_of_le_of_pow_mul_le
    {μ : Measure E} [μ.HasTemperateGrowth] {f : E → F} {C₁ C₂ : ℝ} {k : ℕ}
    (hf : ∀ x, ‖f x‖ ≤ C₁) (h'f : ∀ x, ‖x‖ ^ (k + μ.integrablePower) * ‖f x‖ ≤ C₂) :
    ∫ x, ‖x‖ ^ k * ‖f x‖ ∂μ ≤ 2 ^ μ.integrablePower *
      (∫ x, (1 + ‖x‖) ^ (- (μ.integrablePower : ℝ)) ∂μ) * (C₁ + C₂) := by
  rw [← integral_const_mul, ← integral_mul_const]
  apply integral_mono_of_nonneg
  · filter_upwards with v using by positivity
  · exact ((integrable_pow_neg_integrablePower μ).const_mul _).mul_const _
  filter_upwards with v
  exact (pow_mul_le_of_le_of_pow_mul_le (norm_nonneg _) (norm_nonneg _) (hf v) (h'f v)).trans
    (le_of_eq (by ring))

/-- For any `HasTemperateGrowth` measure and `p`, there exists an integer power `k` such that
`(1 + ‖x‖) ^ (-k)` is in `L^p`. -/
theorem HasTemperateGrowth.exists_eLpNorm_lt_top (p : ℝ≥0∞)
    {μ : Measure E} (hμ : μ.HasTemperateGrowth) :
    ∃ k : ℕ, eLpNorm (fun x ↦ (1 + ‖x‖) ^ (-k : ℝ)) p μ < ⊤ := by
  cases p with
  | top => exact ⟨0, eLpNormEssSup_lt_top_of_ae_bound (C := 1) (by simp)⟩
  | coe p =>
    cases eq_or_ne (p : ℝ≥0∞) 0 with
    | inl hp => exact ⟨0, by simp [hp]⟩
    | inr hp =>
      have h_one_add (x : E) : 0 < 1 + ‖x‖ := lt_add_of_pos_of_le zero_lt_one (norm_nonneg x)
      have hp_pos : 0 < (p : ℝ) := by simpa [zero_lt_iff] using hp
      rcases hμ.exists_integrable with ⟨l, hl⟩
      let k := ⌈(l / p : ℝ)⌉₊
      have hlk : l ≤ k * (p : ℝ) := by simpa [div_le_iff₀ hp_pos] using Nat.le_ceil (l / p : ℝ)
      use k
      suffices HasFiniteIntegral (fun x ↦ ((1 + ‖x‖) ^ (-(k * p) : ℝ))) μ by
        rw [hasFiniteIntegral_iff_enorm] at this
        rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp ENNReal.coe_ne_top]
        simp only [ENNReal.coe_toReal]
        refine Eq.subst (motive := (∫⁻ x, · x ∂μ < ⊤)) (funext fun x ↦ ?_) this
        rw [← neg_mul, Real.rpow_mul (h_one_add x).le]
        exact Real.enorm_rpow_of_nonneg (by positivity) NNReal.zero_le_coe
      refine hl.hasFiniteIntegral.mono' (ae_of_all μ fun x ↦ ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (h_one_add x).le _)]
      gcongr
      simp

end MeasureTheory.Measure
