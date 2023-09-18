/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ContDiff_aux
import Mathlib.Data.Finset.Interval
import Mathlib.MeasureTheory.Integral.Bochner_aux
import Mathlib.MeasureTheory.Integral.IntegralEqImproper_aux
import Mathlib.MeasureTheory.Integral.MeanInequalities_aux

/-!
# Gagliardo-Nirenberg-Sobolev inequality
-/


open scoped Classical BigOperators ENNReal NNReal
open Set Function Finset MeasureTheory Measure
set_option autoImplicit true

noncomputable section

section RPow

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

theorem NNReal.rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
  x ^ (y + z) = x ^ y * x ^ z := by
  by_cases h : y + z = 0
  · obtain rfl : y = 0 := by linarith
    obtain rfl : z = 0 := by linarith
    simp [h]
  · exact rpow_add' _ h

theorem ENNReal.rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl|hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl|hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

end RPow

section NormedAddCommGroup
variable {ι : Type*} [Fintype ι] {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)]

theorem Pi.nnnorm_single (y : E i) : ‖Pi.single i y‖₊ = ‖y‖₊ := by
  classical
  have H : ∀ b, ‖single i y b‖₊ = single (f := fun _ ↦ ℝ≥0) i ‖y‖₊ b
  · intro b
    refine Pi.apply_single (fun i (x : E i) ↦ ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite,
    Finset.filter_eq' (Finset.univ : Finset ι)]

theorem Pi.norm_single (y : E i) : ‖Pi.single i y‖ = ‖y‖ :=
  congr_arg Subtype.val (Pi.nnnorm_single y)

end NormedAddCommGroup

section ClosedEmbedding
variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, T2Space (X i)]

theorem closedEmbedding_update  (x : ∀ i, X i) (i : ι) : ClosedEmbedding (update x i) := by
  have h : LeftInverse (fun v ↦ v i) (update x i) := fun t ↦ update_same i t x
  apply h.closedEmbedding (continuous_apply i)
  have : Continuous (fun t : X i ↦ (x, t)) := continuous_const.prod_mk continuous_id
  exact (continuous_update i).comp this

end ClosedEmbedding

variable {ι : Type*} [Fintype ι]

local prefix:max "#" => Fintype.card

/-! ## The grid-lines lemma -/

variable {A : ι → Type*} [∀ i, MeasurableSpace (A i)]
  (μ : ∀ i, Measure (A i)) [∀ i, SigmaFinite (μ i)]

namespace GridLines

/-- The "grid-lines operation" (not a standard name) which is central in the inductive proof of the
Sobolev inequality.

For a finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, a finite set `s` of
indices from `ι`, and a (later assumed nonnegative) real number `p`, this operation acts on a
function `f` from `Π i, A i` into the extended nonnegative reals.  The operation is to partially
integrate, in the `s` co-ordinates, the function whose value at `x : Π i, A i` is obtained by
multiplying a certain power of `f` with the product, for each co-ordinate `i` in `s`, of a certain
power of the integral of `f` along the "grid line" in the `i` direction through `x`.

We are most interested in this operation when the set `s` is the universe in `ι`, but as a proxy for
"induction on dimension" we define it for a general set `s` of co-ordinates: the `s`-grid-lines
operation on a function `f` which is constant along the co-ordinates in `sᶜ` is morally (that is, up
to type-theoretic nonsense) the same thing as the universe-grid-lines operation on the associated
function on the "lower-dimensional" space `Π i : s, A i`. -/
def T (p : ℝ) (f : (∀ i, A i) → ℝ≥0∞) (s : Finset ι) : (∀ i, A i) → ℝ≥0∞ :=
  ∫⋯∫_s, f ^ (1 - (s.card - 1 : ℝ) * p) * ∏ i in s, (∫⋯∫_{i}, f ∂μ) ^ p ∂μ

variable {p : ℝ}

@[simp] lemma T_univ (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f univ x
    = ∫⁻ (x : ∀ i, A i), (f x ^ (1 - (#ι - 1 : ℝ) * p)
      * ∏ i : ι, (∫⁻ t : A i, f (update x i t) ∂(μ i)) ^ p) ∂(.pi μ) := by
  simp [T, marginal_univ, marginal_singleton, card_univ]

@[simp] lemma T_empty (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f ∅ x = f x ^ (1 + p) := by
  simp [T]

set_option maxHeartbeats 500000 in
/-- The main inductive step in the grid-lines lemma for the Gagliardo-Nirenberg-Sobolev inequality.

The grid-lines operation `GridLines.T` on a nonnegative function on a finitary product type is
less than or equal to the grid-lines operation of its partial integral in one co-ordinate
(the latter intuitively considered as a function on a space "one dimension down"). -/
theorem T_insert_le_T_marginal_singleton (hp₀ : 0 ≤ p) (s : Finset ι) (hp : (s.card : ℝ) * p ≤ 1)
    (i : ι) (hi : i ∉ s) {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    T μ p f (insert i s) ≤ T μ p (∫⋯∫_{i}, f ∂μ) s := by
  calc T μ p f (insert i s)
      = ∫⋯∫_insert i s,
            f ^ (1 - (s.card : ℝ) * p) * ∏ j in (insert i s), (∫⋯∫_{j}, f ∂μ) ^ p ∂μ := by
          simp_rw [T, card_insert_of_not_mem hi]
          congr!
          push_cast
          ring
    _ = ∫⋯∫_s, (fun x ↦ ∫⁻ (t : A i),
            (f (update x i t) ^ (1 - (s.card : ℝ) * p)
            * ∏ j in (insert i s), (∫⋯∫_{j}, f ∂μ) (update x i t) ^ p)  ∂ (μ i)) ∂μ := by
          rw [marginal_insert' _ _ hi]
          · congr! with x t
            simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
          · change Measurable (fun x ↦ _)
            simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
            refine (hf.pow_const _).mul <| Finset.measurable_prod _ ?_
            exact fun _ _ ↦ hf.marginal μ |>.pow_const _
    _ ≤ T μ p (∫⋯∫_{i}, f ∂μ) s := marginal_mono (fun x ↦ ?_)
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
  have hF₁ : ∀ {j : ι}, Measurable fun t ↦ (∫⋯∫_{j}, f ∂μ) (update x i t) :=
    fun {_} ↦ hf.marginal μ |>.comp <| measurable_update _
  have hF₀ : Measurable fun t ↦ f (update x i t) := hf.comp <| measurable_update _
  let k : ℝ := s.card
  have hk' : 0 ≤ 1 - k * p := by linarith only [hp]
  let X := update x i
  calc ∫⁻ t, f (X t) ^ (1 - k * p)
          * ∏ j in (insert i s), (∫⋯∫_{j}, f ∂μ) (X t) ^ p ∂ (μ i)
      = ∫⁻ t, (∫⋯∫_{i}, f ∂μ) (X t) ^ p * (f (X t) ^ (1 - k * p)
          * ∏ j in s, ((∫⋯∫_{j}, f ∂μ) (X t) ^ p)) ∂(μ i) := by
              -- rewrite integrand so that `(∫⋯∫_insert i s, f ∂μ) ^ p` comes first
              clear_value X
              congr! 2 with t
              simp_rw [prod_insert hi]
              ring_nf
    _ = (∫⋯∫_{i}, f ∂μ) x ^ p *
          ∫⁻ t, f (X t) ^ (1 - k * p) * ∏ j in s, ((∫⋯∫_{j}, f ∂μ) (X t)) ^ p ∂(μ i) := by
              -- pull out this constant factor
              have : ∀ t, (∫⋯∫_{i}, f ∂μ) (X t) = (∫⋯∫_{i}, f ∂μ) x
              · intro t
                rw [marginal_update_of_mem]
                exact Iff.mpr Finset.mem_singleton rfl
              simp_rw [this]
              rw [lintegral_const_mul]
              exact (hF₀.pow_const _).mul <| Finset.measurable_prod _ fun _ _ ↦ hF₁.pow_const _
    _ ≤ (∫⋯∫_{i}, f ∂μ) x ^ p *
          ((∫⁻ t, f (X t) ∂μ i) ^ (1 - k * p)
          * ∏ j in s, (∫⁻ t, (∫⋯∫_{j}, f ∂μ) (X t) ∂μ i) ^ p) := by
              -- apply Hölder's inequality
              gcongr
              apply ENNReal.lintegral_mul_prod_norm_pow_le
              · exact hF₀.aemeasurable
              · intros
                exact hF₁.aemeasurable
              · simp only [sum_const, nsmul_eq_mul]
                ring
              · exact hk'
              · exact fun _ _ ↦ hp₀
    _ = (∫⋯∫_{i}, f ∂μ) x ^ p *
          ((∫⋯∫_{i}, f ∂μ) x ^ (1 - k * p) * ∏ j in s, (∫⋯∫_{i, j}, f ∂μ) x ^ p) := by
              -- absorb the newly-created integrals into `∫⋯∫`
              dsimp only
              congr! 2
              · rw [marginal_singleton]
              refine prod_congr rfl fun j hj => ?_
              have hi' : i ∉ ({j} : Finset ι)
              · simp only [Finset.mem_singleton, Finset.mem_insert, Finset.mem_compl] at hj ⊢
                exact fun h ↦ hi (h ▸ hj)
              rw [marginal_insert _ hf hi']
    _ = (∫⋯∫_{i}, f ∂μ) x ^ (p + (1 - k * p)) *  ∏ j in s, (∫⋯∫_{i, j}, f ∂μ) x ^ p := by
              -- combine two `(∫⋯∫_insert i s, f ∂μ) x` terms
              rw [ENNReal.rpow_add_of_nonneg]
              · ring
              · exact hp₀
              · exact hk'
    _ ≤ (∫⋯∫_{i}, f ∂μ) x ^ (1 - (s.card - 1 : ℝ) * p) *
          ∏ j in s, (∫⋯∫_{j}, (∫⋯∫_{i}, f ∂μ) ∂μ) x ^ p := by
              -- identify the result with the RHS integrand
              congr! 2 with j hj
              · push_cast
                ring_nf
              · congr! 1
                rw [← marginal_union μ f hf]
                · congr
                  rw [Finset.union_comm]
                  rfl
                · rw [Finset.disjoint_singleton]
                  simp only [Finset.mem_insert, Finset.mem_compl] at hj
                  exact fun h ↦ hi (h ▸ hj)

/-- Auxiliary result for the grid-lines lemma.  Given a nonnegative function on a finitary product
type indexed by `ι`, and a set `s` in `ι`, consider partially integrating over the variables in
`sᶜ` and performing the "grid-lines operation" (see `GridLines.T`) to the resulting function in the
variables `s`.  This theorem states that this operation decreases as the number of grid-lines taken
increases. -/
theorem T_marginal_antitone (hp₀ : 0 ≤ p) (hp : (#ι - 1 : ℝ) * p ≤ 1)
    {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    Antitone (fun s ↦ T μ p (∫⋯∫_sᶜ, f ∂μ) s) := by
  -- Reformulate (by induction): a function is decreasing on `Finset ι` if it decreases under the
  -- insertion of any element to any set.
  rw [Finset.antitone_iff']
  intro s i hi
  -- apply the lemma designed to encapsulate the inductive step
  convert T_insert_le_T_marginal_singleton μ hp₀ s ?_ i hi (hf.marginal μ) using 2
  · rw [← marginal_union μ f hf]
    · rw [← insert_compl_insert hi]
      rfl
    rw [Finset.disjoint_singleton_left, not_mem_compl]
    exact mem_insert_self i s
  · -- the main nontrivial point is to check that an exponent `p` satisfying `0 ≤ p` and
    -- `(#ι - 1) * p ≤ 1` is in the valid range for the inductive-step lemma
    refine le_trans ?_ hp
    gcongr
    suffices (s.card : ℝ) + 1 ≤ #ι by linarith
    rw [← s.card_add_card_compl]
    norm_cast
    gcongr
    have hi' : sᶜ.Nonempty := ⟨i, by rwa [Finset.mem_compl]⟩
    rwa [← card_pos] at hi'

end GridLines

/-- The "grid-lines lemma" (not a standard name), stated with a general parameter `p` as the
exponent.  Compare with `lintegral_prod_lintegral_pow_le`.

For any finite dependent product `Π i : ι, A i` of sigma-finite measure spaces, for any
nonnegative real number `p` such that `(#ι - 1) * p ≤ 1`, for any function `f` from `Π i, A i` into
the extended nonnegative reals, we consider an associated "grid-lines quantity", the integral of an
associated function from `Π i, A i` into the extended nonnegative reals.  The value of this function
at `x : Π i, A i` is obtained by multiplying a certain power of `f` with the product, for each
co-ordinate `i`, of a certain power of the integral of `f` along the "grid line" in the `i`
direction through `x`.

This lemma bounds the Lebesgue integral of the grid-lines quantity by a power of the Lebesgue
integral of `f`. -/
theorem lintegral_mul_prod_lintegral_pow_le {p : ℝ} (hp₀ : 0 ≤ p)
    (hp : (#ι - 1 : ℝ) * p ≤ 1) {f : (∀ i : ι, A i) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ^ (1 - (#ι - 1 : ℝ) * p) * ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ p ∂.pi μ
    ≤ (∫⁻ x, f x ∂.pi μ) ^ (1 + p) := by
  cases isEmpty_or_nonempty (∀ i, A i)
  · simp_rw [lintegral_of_isEmpty]; refine' zero_le _
  inhabit ∀ i, A i
  have H : (∅ : Finset ι) ≤ Finset.univ := Finset.empty_subset _
  simpa [marginal_univ] using GridLines.T_marginal_antitone μ hp₀ hp hf H default

/-- Special case of the grid-lines lemma `lintegral_mul_prod_lintegral_pow_le`, taking the extremal
exponent `p = (#ι - 1)⁻¹`. -/
theorem lintegral_prod_lintegral_pow_le [Nontrivial ι] {f} (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂.pi μ
    ≤ (∫⁻ x, f x ∂.pi μ) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  have : (1:ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have : (0:ℝ) < #ι - 1 := by linarith
  have hp₀ : 0 ≤ ((1 : ℝ) / (#ι - 1 : ℝ)) := by positivity
  have hp : (#ι - 1 : ℝ) * ((1 : ℝ) / (#ι - 1 : ℝ)) ≤ 1 := by field_simp
  convert lintegral_mul_prod_lintegral_pow_le μ hp₀ hp hf using 2 <;> field_simp

/-! ## The Gagliardo-Nirenberg-Sobolev inequality -/

variable [Nontrivial ι] {u : (ι → ℝ) → ℝ}

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported real-valued function on `ℝⁿ`, for `n ≥ 2`.  (More literally we encode `ℝⁿ` as
`ι → ℝ` where `n := #ι` is finite and at least 2.)  Then the Lebesgue integral of the pointwise
expression `|u x| ^ (n / (n - 1))` is bounded above by the `n / (n - 1)`-th power of the Lebesgue
integral of the Fréchet derivative of `u`. -/
theorem lintegral_pow_le (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u) :
    ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ))
    ≤ (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
  have : (1:ℝ) ≤ ↑#ι - 1
  · have hι : (2:ℝ) ≤ #ι := by exact_mod_cast Fintype.one_lt_card
    linarith
  calc ∫⁻ x, ‖u x‖₊ ^ ((#ι : ℝ) / (#ι - 1 : ℝ))
      = ∫⁻ x, ((‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ))) ^ (#ι : ℝ) := by
        -- a little algebraic manipulation of the exponent
        congr! 2 with x
        rw [← ENNReal.coe_rpow_of_nonneg _ (by positivity), ← ENNReal.rpow_mul]
        field_simp
    _ = ∫⁻ x, ∏ _i : ι, (‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ)) := by
        -- express the left-hand integrand as a product of identical factors
        congr! 2 with x
        simp_rw [prod_const, card_univ]
        norm_cast
    _ ≤ ∫⁻ x, ∏ i, (∫⁻ xᵢ, ‖fderiv ℝ u (update x i xᵢ)‖₊) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := ?_
    _ ≤ (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ ((#ι : ℝ) / (#ι - 1 : ℝ)) := by
        -- apply the grid-lines lemma
        apply lintegral_prod_lintegral_pow_le
        borelize ((ι → ℝ) →L[ℝ] ℝ)
        have : Measurable (fun x ↦ fderiv ℝ u x) := (hu.continuous_fderiv (le_refl _)).measurable
        measurability
  gcongr with x i
  calc (‖u x‖₊ : ℝ≥0∞)
      = (‖∫ xᵢ in Iic (x i), deriv (u ∘ update x i) xᵢ‖₊ : ℝ≥0∞) := by
        -- apply the half-infinite fundamental theorem of calculus
        have h3u : ContDiff ℝ 1 (u ∘ update x i) := hu.comp (contDiff_update 1 x i)
        have h4u : HasCompactSupport (u ∘ update x i) :=
          h2u.comp_closedEmbedding (closedEmbedding_update x i)
        simp [h4u.integral_deriv_eq h3u (x i)]
    _ ≤ ∫⁻ xᵢ in Iic (x i), ‖deriv (u ∘ update x i) xᵢ‖₊ :=
        nnnorm_integral_le_lintegral_nnnorm _ -- apply the triangle inequality
    _ ≤ ∫⁻ xᵢ, (‖fderiv ℝ u (update x i xᵢ)‖₊ : ℝ≥0∞) := ?_
  gcongr with y; swap; exact Measure.restrict_le_self
  -- bound the derivative which appears
  calc ‖deriv (u ∘ update x i) y‖₊ = ‖fderiv ℝ u (update x i y) (deriv (update x i) y)‖₊ := by
        rw [fderiv.comp_deriv _ (hu.differentiable le_rfl).differentiableAt
          (hasDerivAt_update y).differentiableAt]
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ * ‖deriv (update x i) y‖₊ :=
        ContinuousLinearMap.le_op_nnnorm ..
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ := by simp [deriv_update, Pi.nnnorm_single]
