/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Finset.Interval
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Gagliardo-Nirenberg-Sobolev inequality
-/


open scoped Classical BigOperators ENNReal NNReal
open Set Function Finset MeasureTheory Measure
set_option autoImplicit true

noncomputable section

section RPow

theorem NNReal.rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  by_cases h : y + z = 0
  · obtain rfl : y = 0 := by linarith
    obtain rfl : z = 0 := by linarith
    simp [h]
  · exact rpow_add' _ h

theorem Real.nnnorm_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : ‖x ^ y‖₊ = ‖x‖₊ ^ y := by
  ext; exact Real.norm_rpow_of_nonneg hx

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

namespace HasCompactSupport
variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [AddGroup β] [Lattice β]
  [CovariantClass β β (· + ·) (· ≤ ·)]

protected theorem abs {f : α → β} (hf : HasCompactSupport f) : HasCompactSupport |f| :=
  hf.comp_left (g := abs) abs_zero

protected theorem rpow_const {f : α → ℝ} (hf : HasCompactSupport f) {r : ℝ} (hr : r ≠ 0) :
    HasCompactSupport (fun x ↦ f x ^ r) :=
  hf.comp_left (g := (· ^ r)) (Real.zero_rpow hr)

end HasCompactSupport

section

variable {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}

theorem Continuous.memℒp_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] : Memℒp f p μ := by
  have := hf.memℒp_top_of_hasCompactSupport h'f μ
  exact this.memℒp_of_exponent_le_of_measure_support_ne_top
    (fun x ↦ image_eq_zero_of_nmem_tsupport) (h'f.measure_lt_top.ne) le_top

end

namespace ENNReal

protected theorem inv_mul_le_iff {x y z : ℝ≥0∞} (h1 : x ≠ 0) (h2 : x ≠ ∞) :
    x⁻¹ * y ≤ z ↔ y ≤ x * z := by
  rw [← mul_le_mul_left h1 h2, ← mul_assoc, ENNReal.mul_inv_cancel h1 h2, one_mul]

protected theorem mul_inv_le_iff {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x * y⁻¹ ≤ z ↔ x ≤ z * y := by
  rw [mul_comm, ENNReal.inv_mul_le_iff h1 h2, mul_comm]

protected theorem div_le_iff {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ z * y := by
  rw [div_eq_mul_inv, ENNReal.mul_inv_le_iff h1 h2]

protected theorem div_le_iff' {x y z : ℝ≥0∞} (h1 : y ≠ 0) (h2 : y ≠ ∞) :
    x / y ≤ z ↔ x ≤ y * z := by
  rw [mul_comm, ENNReal.div_le_iff h1 h2]

end ENNReal

namespace Real.IsConjExponent

variable {p q : ℝ} (h : IsConjExponent p q)
lemma conj_inv_eq : q⁻¹ = 1 - p⁻¹ := by
  rw [eq_sub_iff_add_eq, add_comm, h.inv_add_inv_conj]

end Real.IsConjExponent

namespace MeasureTheory

variable {α E : Type*} [NormedAddCommGroup E] {_ : MeasurableSpace α}
  {f : α → E} {μ : Measure α}

lemma snorm_nnreal_eq_snorm' {p : ℝ≥0} (hp : p ≠ 0) : snorm f p μ = snorm' f p μ :=
  snorm_eq_snorm' (by exact_mod_cast hp) ENNReal.coe_ne_top

lemma snorm_nnreal_eq_lintegral {p : ℝ≥0} (hp : p ≠ 0) :
    snorm f p μ = (∫⁻ x, ‖f x‖₊ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
  snorm_nnreal_eq_snorm' hp

lemma snorm_nnreal_pow_eq_lintegral {p : ℝ≥0} (hp : p ≠ 0) :
    snorm f p μ ^ (p : ℝ) = ∫⁻ x, ‖f x‖₊ ^ (p : ℝ) ∂μ := by
  simp [snorm_eq_snorm' (by exact_mod_cast hp) ENNReal.coe_ne_top,
    lintegral_rpow_nnnorm_eq_rpow_snorm' (show 0 < (p : ℝ) from pos_iff_ne_zero.mpr hp)]

end MeasureTheory

namespace MeasureTheory

end MeasureTheory

section NormedAddCommGroup
variable {ι : Type*} [Fintype ι] {E : ι → Type _} [∀ i, NormedAddCommGroup (E i)]

theorem Pi.nnnorm_single (y : E i) : ‖Pi.single i y‖₊ = ‖y‖₊ := by
  classical
  have H : ∀ b, ‖single i y b‖₊ = single (f := fun _ ↦ ℝ≥0) i ‖y‖₊ b := by
    intro b
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
  ∫⋯∫⁻_s, f ^ (1 - (s.card - 1 : ℝ) * p) * ∏ i in s, (∫⋯∫⁻_{i}, f ∂μ) ^ p ∂μ

variable {p : ℝ}

@[simp] lemma T_univ (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f univ x
    = ∫⁻ (x : ∀ i, A i), (f x ^ (1 - (#ι - 1 : ℝ) * p)
      * ∏ i : ι, (∫⁻ t : A i, f (update x i t) ∂(μ i)) ^ p) ∂(.pi μ) := by
  simp [T, lmarginal_univ, lmarginal_singleton, card_univ]

@[simp] lemma T_empty (f : (∀ i, A i) → ℝ≥0∞) (x : ∀ i, A i) :
    T μ p f ∅ x = f x ^ (1 + p) := by
  simp [T]

set_option maxHeartbeats 500000 in
/-- The main inductive step in the grid-lines lemma for the Gagliardo-Nirenberg-Sobolev inequality.

The grid-lines operation `GridLines.T` on a nonnegative function on a finitary product type is
less than or equal to the grid-lines operation of its partial integral in one co-ordinate
(the latter intuitively considered as a function on a space "one dimension down"). -/
theorem T_insert_le_T_lmarginal_singleton (hp₀ : 0 ≤ p) (s : Finset ι) (hp : (s.card : ℝ) * p ≤ 1)
    (i : ι) (hi : i ∉ s) {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    T μ p f (insert i s) ≤ T μ p (∫⋯∫⁻_{i}, f ∂μ) s := by
  calc T μ p f (insert i s)
      = ∫⋯∫⁻_insert i s,
            f ^ (1 - (s.card : ℝ) * p) * ∏ j in (insert i s), (∫⋯∫⁻_{j}, f ∂μ) ^ p ∂μ := by
          simp_rw [T, card_insert_of_not_mem hi]
          congr!
          push_cast
          ring
    _ = ∫⋯∫⁻_s, (fun x ↦ ∫⁻ (t : A i),
            (f (update x i t) ^ (1 - (s.card : ℝ) * p)
            * ∏ j in (insert i s), (∫⋯∫⁻_{j}, f ∂μ) (update x i t) ^ p)  ∂ (μ i)) ∂μ := by
          rw [lmarginal_insert' _ _ hi]
          · congr! with x t
            simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
          · change Measurable (fun x ↦ _)
            simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
            refine (hf.pow_const _).mul <| Finset.measurable_prod _ ?_
            exact fun _ _ ↦ hf.lmarginal μ |>.pow_const _
    _ ≤ T μ p (∫⋯∫⁻_{i}, f ∂μ) s := lmarginal_mono (fun x ↦ ?_)
  simp only [Pi.mul_apply, Pi.pow_apply, Finset.prod_apply]
  have hF₁ : ∀ {j : ι}, Measurable fun t ↦ (∫⋯∫⁻_{j}, f ∂μ) (update x i t) :=
    fun {_} ↦ hf.lmarginal μ |>.comp <| measurable_update _
  have hF₀ : Measurable fun t ↦ f (update x i t) := hf.comp <| measurable_update _
  let k : ℝ := s.card
  have hk' : 0 ≤ 1 - k * p := by linarith only [hp]
  let X := update x i
  calc ∫⁻ t, f (X t) ^ (1 - k * p)
          * ∏ j in (insert i s), (∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p ∂ (μ i)
      = ∫⁻ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) ^ p * (f (X t) ^ (1 - k * p)
          * ∏ j in s, ((∫⋯∫⁻_{j}, f ∂μ) (X t) ^ p)) ∂(μ i) := by
              -- rewrite integrand so that `(∫⋯∫⁻_insert i s, f ∂μ) ^ p` comes first
              clear_value X
              congr! 2 with t
              simp_rw [prod_insert hi]
              ring_nf
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ∫⁻ t, f (X t) ^ (1 - k * p) * ∏ j in s, ((∫⋯∫⁻_{j}, f ∂μ) (X t)) ^ p ∂(μ i) := by
              -- pull out this constant factor
              have : ∀ t, (∫⋯∫⁻_{i}, f ∂μ) (X t) = (∫⋯∫⁻_{i}, f ∂μ) x := by
                intro t
                rw [lmarginal_update_of_mem]
                exact Iff.mpr Finset.mem_singleton rfl
              simp_rw [this]
              rw [lintegral_const_mul]
              exact (hF₀.pow_const _).mul <| Finset.measurable_prod _ fun _ _ ↦ hF₁.pow_const _
    _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ((∫⁻ t, f (X t) ∂μ i) ^ (1 - k * p)
          * ∏ j in s, (∫⁻ t, (∫⋯∫⁻_{j}, f ∂μ) (X t) ∂μ i) ^ p) := by
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
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ p *
          ((∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - k * p) * ∏ j in s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p) := by
              -- absorb the newly-created integrals into `∫⋯∫`
              dsimp only
              congr! 2
              · rw [lmarginal_singleton]
              refine prod_congr rfl fun j hj => ?_
              have hi' : i ∉ ({j} : Finset ι) := by
                simp only [Finset.mem_singleton, Finset.mem_insert, Finset.mem_compl] at hj ⊢
                exact fun h ↦ hi (h ▸ hj)
              rw [lmarginal_insert _ hf hi']
    _ = (∫⋯∫⁻_{i}, f ∂μ) x ^ (p + (1 - k * p)) *  ∏ j in s, (∫⋯∫⁻_{i, j}, f ∂μ) x ^ p := by
              -- combine two `(∫⋯∫⁻_insert i s, f ∂μ) x` terms
              rw [ENNReal.rpow_add_of_nonneg]
              · ring
              · exact hp₀
              · exact hk'
    _ ≤ (∫⋯∫⁻_{i}, f ∂μ) x ^ (1 - (s.card - 1 : ℝ) * p) *
          ∏ j in s, (∫⋯∫⁻_{j}, (∫⋯∫⁻_{i}, f ∂μ) ∂μ) x ^ p := by
              -- identify the result with the RHS integrand
              congr! 2 with j hj
              · push_cast
                ring_nf
              · congr! 1
                rw [← lmarginal_union μ f hf]
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
theorem T_lmarginal_antitone (hp₀ : 0 ≤ p) (hp : (#ι - 1 : ℝ) * p ≤ 1)
    {f : (∀ i, A i) → ℝ≥0∞} (hf : Measurable f) :
    Antitone (fun s ↦ T μ p (∫⋯∫⁻_sᶜ, f ∂μ) s) := by
  -- Reformulate (by induction): a function is decreasing on `Finset ι` if it decreases under the
  -- insertion of any element to any set.
  rw [Finset.antitone_iff_forall_insert_le]
  intro s i hi
  -- apply the lemma designed to encapsulate the inductive step
  convert T_insert_le_T_lmarginal_singleton μ hp₀ s ?_ i hi (hf.lmarginal μ) using 2
  · rw [← lmarginal_union μ f hf]
    · rw [← insert_compl_insert hi]
      rfl
    rw [Finset.disjoint_singleton_left, not_mem_compl]
    exact mem_insert_self i s
  · -- the main nontrivial point is to check that an exponent `p` satisfying `0 ≤ p` and
    -- `(#ι - 1) * p ≤ 1` is in the valid range for the inductive-step lemma
    refine le_trans ?_ hp
    gcongr
    suffices (s.card : ℝ) + 1 ≤ #ι by linarith
    rw [← card_add_card_compl s]
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
  simpa [lmarginal_univ] using GridLines.T_lmarginal_antitone μ hp₀ hp hf H default

/-- Special case of the grid-lines lemma `lintegral_mul_prod_lintegral_pow_le`, taking the extremal
exponent `p = (#ι - 1)⁻¹`. -/
theorem lintegral_prod_lintegral_pow_le [Nontrivial ι]
    {p : ℝ} (hp : Real.IsConjExponent #ι p)
    {f} (hf : Measurable f) :
    ∫⁻ x, ∏ i, (∫⁻ xᵢ, f (update x i xᵢ) ∂μ i) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) ∂.pi μ
    ≤ (∫⁻ x, f x ∂.pi μ) ^ p := by
  have h0 : (1:ℝ) < #ι := by norm_cast; exact Fintype.one_lt_card
  have h1 : (0:ℝ) < #ι - 1 := by linarith
  have h3 : 0 ≤ ((1 : ℝ) / (#ι - 1 : ℝ)) := by positivity
  have h4 : (#ι - 1 : ℝ) * ((1 : ℝ) / (#ι - 1 : ℝ)) ≤ 1 := by field_simp
  have h5 : p = 1 + 1 / (↑#ι - 1) := by field_simp; rw [mul_comm, hp.sub_one_mul_conj]
  rw [h5]
  convert lintegral_mul_prod_lintegral_pow_le μ h3 h4 hf using 2
  field_simp

/-! ## The Gagliardo-Nirenberg-Sobolev inequality -/

variable [Nontrivial ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function on `ℝⁿ`, for `n ≥ 2`.  (More literally we encode `ℝⁿ` as
`ι → ℝ` where `n := #ι` is finite and at least 2.)  Then the Lebesgue integral of the pointwise
expression `|u x| ^ (n / (n - 1))` is bounded above by the `n / (n - 1)`-th power of the Lebesgue
integral of the Fréchet derivative of `u`.

For a basis-free version, see `lintegral_pow_le_pow_lintegral_fderiv`. -/
theorem lintegral_pow_le_pow_lintegral_fderiv_aux
    {p : ℝ} (hp : Real.IsConjExponent #ι p)
    {u : (ι → ℝ) → F} (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) :
    ∫⁻ x, (‖u x‖₊ : ℝ≥0∞) ^ p ≤ (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ p := by
  have : (1:ℝ) ≤ ↑#ι - 1 := by
    have hι : (2:ℝ) ≤ #ι := by exact_mod_cast Fintype.one_lt_card
    linarith
  calc ∫⁻ x, (‖u x‖₊ : ℝ≥0∞) ^ p
      = ∫⁻ x, ((‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ))) ^ (#ι : ℝ) := by
        -- a little algebraic manipulation of the exponent
        congr! 2 with x
        rw [← ENNReal.rpow_mul, hp.conj_eq]
        field_simp
    _ = ∫⁻ x, ∏ _i : ι, (‖u x‖₊ : ℝ≥0∞) ^ (1 / (#ι - 1 : ℝ)) := by
        -- express the left-hand integrand as a product of identical factors
        congr! 2 with x
        simp_rw [prod_const, card_univ]
        norm_cast
    _ ≤ ∫⁻ x, ∏ i, (∫⁻ xᵢ, ‖fderiv ℝ u (update x i xᵢ)‖₊) ^ ((1 : ℝ) / (#ι - 1 : ℝ)) := ?_
    _ ≤ (∫⁻ x, ‖fderiv ℝ u x‖₊) ^ p := by
        -- apply the grid-lines lemma
        apply lintegral_prod_lintegral_pow_le _ hp
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
        simp [HasCompactSupport.integral_Iic_deriv_eq h3u h4u (x i), neg_le_self_iff]
    _ ≤ ∫⁻ xᵢ in Iic (x i), ‖deriv (u ∘ update x i) xᵢ‖₊ :=
        ennnorm_integral_le_lintegral_ennnorm _ -- apply the triangle inequality
    _ ≤ ∫⁻ xᵢ, (‖fderiv ℝ u (update x i xᵢ)‖₊ : ℝ≥0∞) := ?_
  gcongr with y; swap; exact Measure.restrict_le_self
  -- bound the derivative which appears
  calc ‖deriv (u ∘ update x i) y‖₊ = ‖fderiv ℝ u (update x i y) (deriv (update x i) y)‖₊ := by
        rw [fderiv.comp_deriv _ (hu.differentiable le_rfl).differentiableAt
          (hasDerivAt_update x i y).differentiableAt]
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ * ‖deriv (update x i) y‖₊ :=
        ContinuousLinearMap.le_opNNNorm ..
    _ ≤ ‖fderiv ℝ u (update x i y)‖₊ := by simp [deriv_update, Pi.nnnorm_single]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [IsAddHaarMeasure μ]

open FiniteDimensional

section

example (c : ℝ≥0) (μ : Measure E) : c • μ = (c : ℝ≥0∞) • μ := by rw [@ENNReal.smul_def]

set_option linter.unusedVariables false in
variable (F) in
/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function on a normed space `E` of finite dimension `n ≥ 2`, equipped
with Haar measure. There exists a constant `C` depending only on `E`, such that the Lebesgue
integral of the pointwise expression `|u x| ^ (n / (n - 1))` is bounded above by `C` times the
`n / (n - 1)`-th power of the Lebesgue integral of the Fréchet derivative of `u`. -/
theorem lintegral_pow_le_pow_lintegral_fderiv (hE : 2 ≤ finrank ℝ E)
    {p : ℝ} (hp : Real.IsConjExponent (finrank ℝ E) p) :
    ∃ C : ℝ≥0, ∀ {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u),
    ∫⁻ x, (‖u x‖₊ : ℝ≥0∞) ^ p ∂μ ≤ C * (∫⁻ x, ‖fderiv ℝ u x‖₊ ∂μ) ^ p := by
  -- we reduce to the case of `E = ι → ℝ`, for which we have already proved the result using
  -- matrices in `lintegral_pow_le_pow_lintegral_fderiv_aux`.
  let ι := Fin (finrank ℝ E)
  have hιcard : #ι = finrank ℝ E := Fintype.card_fin (finrank ℝ E)
  have : Nontrivial ι := by rwa [Fin.nontrivial_iff_two_le]
  haveI : FiniteDimensional ℝ (ι → ℝ) := by infer_instance
  have : finrank ℝ E = finrank ℝ (ι → ℝ) := by simp
  have e : E ≃L[ℝ] ι → ℝ := ContinuousLinearEquiv.ofFinrankEq this
  haveI : IsAddHaarMeasure ((volume : Measure (ι → ℝ)).map e.symm) :=
    (e.symm : (ι → ℝ) ≃+ E).isAddHaarMeasure_map _ e.symm.continuous e.symm.symm.continuous
  have hp : Real.IsConjExponent #ι p := by rwa [hιcard]
  have h0p : 0 ≤ p := hp.symm.nonneg
  let c := addHaarScalarFactor μ ((volume : Measure (ι → ℝ)).map e.symm)
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure ..
  have h2c : μ = c • ((volume : Measure (ι → ℝ)).map e.symm) := isAddLeftInvariant_eq_smul ..
  have h3c : (c : ℝ≥0∞) ≠ 0 := by simp_rw [ne_eq, ENNReal.coe_eq_zero, hc.ne', not_false_eq_true]
  have : ∃ C : ℝ≥0, C * c ^ p = c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p := by
    use (c * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p) * (c ^ p)⁻¹
    rw [inv_mul_cancel_right₀]
    exact (NNReal.rpow_pos hc).ne'
  refine this.imp fun C hC u hu h2u ↦ ?_
  rw [h2c, ENNReal.smul_def, lintegral_smul_measure, lintegral_smul_measure]
  let v : (ι → ℝ) → F := u ∘ e.symm
  have hv : ContDiff ℝ 1 v := hu.comp e.symm.contDiff
  have h2v : HasCompactSupport v := h2u.comp_homeomorph e.symm.toHomeomorph
  have :=
  calc ∫⁻ x, (‖u x‖₊ : ℝ≥0∞) ^ p ∂(volume : Measure (ι → ℝ)).map e.symm
      = ∫⁻ y, (‖v y‖₊ : ℝ≥0∞) ^ p := by
        refine lintegral_map ?_ e.symm.continuous.measurable
        borelize F
        exact hu.continuous.measurable.nnnorm.coe_nnreal_ennreal.pow_const _
    _ ≤ (∫⁻ y, ‖fderiv ℝ v y‖₊) ^ p :=
        lintegral_pow_le_pow_lintegral_fderiv_aux hp hv h2v
    _ = (∫⁻ y, ‖(fderiv ℝ u (e.symm y)).comp (fderiv ℝ e.symm y)‖₊) ^ p := by
        congr! with y
        apply fderiv.comp _ (hu.differentiable (le_refl _) _)
        exact e.symm.differentiableAt
    _ ≤ (∫⁻ y, ‖fderiv ℝ u (e.symm y)‖₊ * ‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊) ^ p := by
        gcongr with y
        norm_cast
        rw [e.symm.fderiv]
        apply ContinuousLinearMap.opNNNorm_comp_le
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ * ∫⁻ y, ‖fderiv ℝ u (e.symm y)‖₊) ^ p := by
        rw [lintegral_mul_const, mul_comm]
        refine (Continuous.nnnorm ?_).measurable.coe_nnreal_ennreal
        exact (hu.continuous_fderiv (le_refl _)).comp e.symm.continuous
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p : ℝ≥0) * (∫⁻ y, ‖fderiv ℝ u (e.symm y)‖₊) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ h0p, ENNReal.coe_rpow_of_nonneg _ h0p]
    _ = (‖(e.symm : (ι → ℝ) →L[ℝ] E)‖₊ ^ p : ℝ≥0)
        * (∫⁻ x, ‖fderiv ℝ u x‖₊ ∂(volume : Measure (ι → ℝ)).map e.symm) ^ p := by
        congr
        rw [lintegral_map _ e.symm.continuous.measurable]
        exact (hu.continuous_fderiv (le_refl _)).measurable.nnnorm.coe_nnreal_ennreal
  rw [← ENNReal.mul_le_mul_left h3c ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul, ← hC,
    ENNReal.coe_mul] at this
  rw [ENNReal.mul_rpow_of_nonneg _ _ h0p, ← mul_assoc, ENNReal.coe_rpow_of_ne_zero hc.ne']
  exact this

set_option linter.unusedVariables false in
variable (F) in
/-- The **Gagliardo-Nirenberg-Sobolev inequality**.  Let `u` be a continuously differentiable
compactly-supported function on a normed space `E` of finite dimension `n ≥ 2`, equipped
with Haar measure. There exists a constant `C` depending only on `E`, such that the `Lᵖ` norm of
`u`, where `p := n / (n - 1)`, is bounded above by `C` times the `L¹` norm of the Fréchet derivative
of `u`. -/
theorem snorm_le_snorm_fderiv (hE : 2 ≤ finrank ℝ E)
    {p : ℝ≥0} (hp : NNReal.IsConjExponent (finrank ℝ E) p) :
    ∃ C : ℝ≥0, ∀ {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u),
    snorm u p μ ≤ C * snorm (fderiv ℝ u) 1 μ := by
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ E = m + 2 := Nat.exists_eq_add_of_le' hE
  have h0p : 0 < (p : ℝ) := hp.coe.symm.pos
  obtain ⟨C, hC⟩ := lintegral_pow_le_pow_lintegral_fderiv F μ hE hp.coe
  use C ^ (p : ℝ)⁻¹
  intro u hu h2u
  rw [snorm_one_eq_lintegral_nnnorm,
    ← ENNReal.rpow_le_rpow_iff h0p, ENNReal.mul_rpow_of_nonneg _ _ h0p.le,
    ENNReal.coe_rpow_of_nonneg _ h0p.le, ← NNReal.rpow_mul,
    snorm_nnreal_pow_eq_lintegral hp.symm.pos.ne',
    inv_mul_cancel h0p.ne', NNReal.rpow_one]
  exact hC hu h2u

example (a b c d : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) : a * (b * c) * d / ((d * b) * a) = c := by
  field_simp; ring

attribute [fun_prop] AEMeasurable Continuous.aemeasurable
  ENNReal.continuous_coe ENNReal.continuous_rpow_const ContDiff.continuous

variable (F) in
theorem snorm_le_snorm_fderiv_of_eq (hE : 2 ≤ finrank ℝ E) {p p' : ℝ≥0} (hp : 1 ≤ p)
    (h2p : p < finrank ℝ E) (hp' : (p' : ℝ)⁻¹ = p⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ {u : E → F} (hu : ContDiff ℝ 1 u) (h2u : HasCompactSupport u),
    snorm u p' μ ≤ C * snorm (fderiv ℝ u) p μ := by
  set n := finrank ℝ E
  let n' := NNReal.conjExponent n
  have hn : NNReal.IsConjExponent n n' := .conjExponent (by norm_cast)
  have h1n : 1 ≤ (n : ℝ≥0) := hn.one_le
  have h2n : (0 : ℝ) < n - 1 := by simp_rw [sub_pos]; exact hn.coe.one_lt
  have hnp : (0 : ℝ) < n - p := by simp_rw [sub_pos]; exact h2p
  rcases hp.eq_or_lt with rfl|hp
  -- the case `p = 1`
  · obtain ⟨C, hC⟩ := snorm_le_snorm_fderiv F μ hE hn
    refine ⟨C, @fun u hu h2u ↦ ?_⟩
    convert hC hu h2u
    ext
    rw [← inv_inj, hp']
    field_simp [NNReal.conjExponent]
  -- the case `p > 1`
  let q := Real.conjExponent p
  have hq : Real.IsConjExponent p q := .conjExponent hp
  have h0p : p ≠ 0 := zero_lt_one.trans hp |>.ne'
  have h1p : (p : ℝ) ≠ 1 := hq.one_lt.ne'
  -- have h3p : (p : ℝ) ≠ 0 := hq.pos.ne'
  have h3p : (p : ℝ) - 1 ≠ 0 := sub_ne_zero_of_ne h1p
  have h0p' : p' ≠ 0 := by
    suffices 0 < (p' : ℝ) from (show 0 < p' from this) |>.ne'
    rw [← inv_pos, hp', sub_pos]
    exact inv_lt_inv_of_lt hq.pos h2p
  have h2q : 1 / n' - 1 / q = 1 / p' := by
    simp_rw (config := {zeta := false}) [one_div, hp']
    rw [hq.conj_inv_eq, hn.coe.conj_inv_eq, sub_sub_sub_cancel_left]
    simp
  let γ : ℝ≥0 := ⟨p * (n - 1) / (n - p), by positivity⟩
  have h0γ : (γ : ℝ) = p * (n - 1) / (n - p) := rfl
  have h1γ : 1 < (γ : ℝ) := by
    rwa [h0γ, one_lt_div hnp, mul_sub, mul_one, sub_lt_sub_iff_right, lt_mul_iff_one_lt_left]
    exact hn.coe.pos
  have h2γ : γ * n' = p' := by
    rw [← NNReal.coe_inj, ← inv_inj, hp', NNReal.coe_mul, h0γ, hn.coe.conj_eq]
    field_simp; ring
  have h3γ : (γ - 1) * q = p' := by
    rw [← inv_inj, hp', h0γ, hq.conj_eq]
    have : (p : ℝ) * (n - 1) - (n - p) = n * (p - 1) := by ring
    field_simp; rw [this]; field_simp; ring
  have h4γ : (γ : ℝ) ≠ 0 := (zero_lt_one.trans h1γ).ne'
  obtain ⟨C, hC⟩ := snorm_le_snorm_fderiv ℝ μ hE hn
  refine ⟨C * γ, @fun u hu h2u ↦ ?_⟩
  by_cases h3u : ∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ = 0
  · rw [snorm_nnreal_eq_lintegral h0p', h3u, ENNReal.zero_rpow_of_pos] <;> positivity
  have h4u : ∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ ≠ ∞ := by
    refine lintegral_rpow_nnnorm_lt_top_of_snorm'_lt_top (pos_iff_ne_zero.mpr h0p') ?_ |>.ne
    dsimp only
    rw [NNReal.val_eq_coe, ← snorm_nnreal_eq_snorm' h0p']
    exact hu.continuous.memℒp_of_hasCompactSupport (μ := μ) h2u |>.snorm_lt_top
  have h5u : (∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ 0 :=
    ENNReal.rpow_pos (pos_iff_ne_zero.mpr h3u) h4u |>.ne'
  have h6u : (∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ) ^ (1 / q) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (div_nonneg zero_le_one hq.symm.nonneg) h4u
  let v : E → ℝ := fun x ↦ ‖u x‖ ^ (γ : ℝ)
  have hv : ContDiff ℝ 1 v := sorry
  have h2v : HasCompactSupport v := h2u.norm.rpow_const h4γ
  have :=
  calc (∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ) ^ (1 / (n' : ℝ)) = snorm v n' μ := by
        rw [← h2γ, snorm_nnreal_eq_lintegral hn.symm.pos.ne']
        congr! 3
        simp [Real.nnnorm_rpow_of_nonneg, ENNReal.rpow_mul]
        rw [ENNReal.coe_rpow_of_nonneg]
        positivity
    _ ≤ C * snorm (fderiv ℝ v) 1 μ := hC hv h2v
    _ = C * ∫⁻ x, ‖fderiv ℝ v x‖₊ ∂μ := by rw [snorm_one_eq_lintegral_nnnorm]
    _ = C * γ * ∫⁻ x, ‖u x‖₊ ^ ((γ : ℝ) - 1) * ‖fderiv ℝ u x‖₊ ∂μ := by sorry
    _ ≤ C * γ * ((∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ) ^ (1 / q) *
        (∫⁻ x, ‖fderiv ℝ u x‖₊ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ))) := by
        gcongr
        convert ENNReal.lintegral_mul_le_Lp_mul_Lq μ
          (.symm <| .conjExponent <| show 1 < (p : ℝ) from hp) ?_ ?_ using 5
        · simp_rw [← ENNReal.rpow_mul, ← h3γ]
        · -- `fun_prop` can do this with a bit of help
          apply Continuous.aemeasurable
          have := hu.continuous
          fun_prop
        · apply Continuous.aemeasurable
          have := (hu.fderiv_right (m := 0) le_rfl).continuous
          fun_prop
    _ = C * γ * (∫⁻ x, ‖fderiv ℝ u x‖₊ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) *
      (∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ) ^ (1 / q) := by ring
  calc
    snorm u p' μ = (∫⁻ x, ‖u x‖₊ ^ (p' : ℝ) ∂μ) ^ (1 / (p' : ℝ)) := snorm_nnreal_eq_lintegral h0p'
    _ ≤ C * γ * (∫⁻ x, ‖fderiv ℝ u x‖₊ ^ (p : ℝ) ∂μ) ^ (1 / (p : ℝ)) :=
      by rwa [← h2q, ENNReal.rpow_sub _ _ h3u h4u, ENNReal.div_le_iff h5u h6u]
    _ = C * γ *  snorm (fderiv ℝ u) (↑p) μ := by rw [snorm_nnreal_eq_lintegral h0p]
