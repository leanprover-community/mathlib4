/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.Distribution.FourierMultiplier
public import Mathlib.Analysis.Fourier.LpSpace

/-! # Sobolev spaces (Bessel potential spaces)

-/

@[expose] public noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

open FourierTransform TemperedDistribution ENNReal MeasureTheory
open scoped SchwartzMap

section BesselPotential

section normed

variable [NormedSpace ℂ F]

variable (E F) in
def besselPotential (s : ℝ) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, F) :=
  fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))

variable (E F) in
@[simp]
theorem besselPotential_zero : besselPotential E F 0 = ContinuousLinearMap.id ℂ _ := by
  ext f
  simp [besselPotential]

@[simp]
theorem besselPotential_besselPotential_apply (s s' : ℝ) (f : 𝓢'(E, F)) :
    besselPotential E F s' (besselPotential E F s f) = besselPotential E F (s + s') f := by
  simp_rw [besselPotential]
  rw [fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
  congr
  ext x
  simp only [Pi.mul_apply]
  norm_cast
  calc
    _ = (1 + ‖x‖ ^ 2) ^ (s / 2 + s' / 2) := by
      rw [← Real.rpow_add (by positivity)]
    _ = _ := by congr; ring

theorem besselPotential_compL_besselPotential (s s' : ℝ) :
    besselPotential E F s' ∘L besselPotential E F s = besselPotential E F (s + s') := by
  ext1 f
  exact besselPotential_besselPotential_apply s s' f

open scoped Real Laplacian

theorem besselPotential_neg_two_laplacian_eq (f : 𝓢'(E, F)) :
    ((besselPotential E F (-2)) (Δ f)) = fourierMultiplierCLM F (fun x ↦ Complex.ofReal <|
      -(2 * π) ^ 2 * ‖x‖ ^ 2 * (1 + ‖x‖ ^ 2) ^ (-1 : ℝ)) f := calc
  _ = -(2 * π) ^ 2 • (fourierMultiplierCLM F
      (fun x ↦ Complex.ofReal <| (‖x‖ ^ 2) * (1 + ‖x‖ ^ 2) ^ (- (1 : ℝ)))) f := by
    rw [laplacian_eq_fourierMultiplierCLM, besselPotential,
      ContinuousLinearMap.map_smul_of_tower,
      fourierMultiplierCLM_fourierMultiplierCLM_apply (by fun_prop) (by fun_prop)]
    congr
    ext x
    simp
  _ = _ := by
    rw [← Complex.coe_smul, ← fourierMultiplierCLM_smul_apply (by fun_prop)]
    congr
    ext x
    simp [mul_assoc]

end normed

section inner

variable [InnerProductSpace ℂ F]

open FourierTransform

@[simp]
theorem fourier_besselPotential_eq_smulLeftCLM_fourierInv_apply (s : ℝ) (f : 𝓢'(E, F)) :
    𝓕 (besselPotential E F s f) =
      smulLeftCLM F (fun x : E ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) := by
  simp [besselPotential, fourierMultiplierCLM]

end inner

end BesselPotential

section normed

variable [NormedSpace ℂ F] [CompleteSpace F]

def MemSobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (f : 𝓢'(E, F)) : Prop :=
  ∃ (f' : Lp F p (volume : Measure E)),
    besselPotential E F s f = f'

theorem memSobolev_zero_iff {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} : MemSobolev 0 p f ↔
    ∃ (f' : Lp F p (volume : Measure E)), f = f' := by
  simp [MemSobolev]

theorem memSobolev_add {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : 𝓢'(E, F)}
    (hf : MemSobolev s p f) (hg : MemSobolev s p g) : MemSobolev s p (f + g) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  use f' + g'
  change _ = Lp.toTemperedDistributionCLM F volume p (f' + g')
  simp [map_add, hf, hg]

theorem memSobolev_smul {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (c : ℂ) {f : 𝓢'(E, F)}
    (hf : MemSobolev s p f) : MemSobolev s p (c • f) := by
  obtain ⟨f', hf⟩ := hf
  use c • f'
  change _ = Lp.toTemperedDistributionCLM F volume p (c • f')
  simp [hf]

variable (E F) in
theorem memSobolev_zero (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] : MemSobolev s p (0 : 𝓢'(E, F)) := by
  use 0
  change _ = Lp.toTemperedDistributionCLM F volume p 0
  simp only [map_zero]

@[simp]
theorem memSobolev_besselPotential_iff {s r : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f : 𝓢'(E, F)} :
    MemSobolev s p (besselPotential E F r f) ↔ MemSobolev (r + s) p f := by
  simp [MemSobolev]

/-- Schwartz functions are in every Sobolev space. -/
theorem memSobolev_toTemperedDistributionCLM {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] (f : 𝓢(E, F)) :
    MemSobolev s p (f : 𝓢'(E, F)) := by
  use (SchwartzMap.fourierMultiplierCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) f).toLp p
  rw [besselPotential, Lp.toTemperedDistribution_toLp_eq,
    fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop)]
  congr 1
  apply SchwartzMap.fourierMultiplierCLM_ofReal ℂ
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow E (s / 2))

variable (E F) in
structure Sobolev (s : ℝ) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] where
  toDistr : 𝓢'(E, F)
  sobFn : Lp F p (volume : Measure E)
  bessel_toDistr_eq_sobFn : besselPotential E F s toDistr = sobFn

namespace Sobolev

variable {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]

theorem ext' {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : Sobolev E F s p}
    (h₁ : f.toDistr = g.toDistr) (h₂ : f.sobFn = g.sobFn) : f = g := by
  cases f; cases g; congr

theorem memSobolev_toDistr (f : Sobolev E F s p) : MemSobolev s p f.toDistr :=
  ⟨f.sobFn, f.bessel_toDistr_eq_sobFn⟩

@[simp]
theorem besselPotential_neg_sobFn_eq {f : Sobolev E F s p} :
    besselPotential E F (-s) f.sobFn = f.toDistr := by
  simp [← f.bessel_toDistr_eq_sobFn]

@[ext]
theorem ext {s : ℝ} {p : ℝ≥0∞} [hp : Fact (1 ≤ p)] {f g : Sobolev E F s p}
    (h₁ : f.toDistr = g.toDistr) : f = g := by
  apply ext' h₁
  apply_fun MeasureTheory.Lp.toTemperedDistribution; swap
  · apply LinearMap.ker_eq_bot.mp MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
  calc
    f.sobFn = besselPotential E F s f.toDistr := f.bessel_toDistr_eq_sobFn.symm
    _ = besselPotential E F s g.toDistr := by congr
    _ = g.sobFn := g.bessel_toDistr_eq_sobFn

def _root_.MemSobolev.toSobolev {f : 𝓢'(E, F)} (hf : MemSobolev s p f) : Sobolev E F s p where
  toDistr := f
  sobFn := hf.choose
  bessel_toDistr_eq_sobFn := hf.choose_spec

@[simp]
theorem _root_.MemSobolev.toSobolev_toDistr {f : 𝓢'(E, F)} (hf : MemSobolev s p f) :
    hf.toSobolev.toDistr = f := rfl

theorem _root_.MemSobolev.toSobolev_injective {f g : 𝓢'(E, F)} (hf : MemSobolev s p f)
    (hg : MemSobolev s p g) (h : hf.toSobolev = hg.toSobolev) : f = g := by
  rw [← hf.toSobolev_toDistr, ← hg.toSobolev_toDistr, h]

variable (E F s p) in
theorem injective_sobFn :
    Function.Injective (sobFn (s := s) (p := p) (E := E) (F := F)) := by
  intro f g hfg
  refine ext' ?_ hfg
  calc
    f.toDistr = besselPotential E F (-s) (Sobolev.sobFn f) := by simp
    _ = besselPotential E F (-s) (Sobolev.sobFn g) := by congr
    _ = g.toDistr := by simp

instance instZero : Zero (Sobolev E F s p) where
  zero := {
    toDistr := 0
    sobFn := 0
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [-Lp.toTemperedDistributionCLM_apply] }

instance instAdd : Add (Sobolev E F s p) where
  add f g := {
    toDistr := f.toDistr + g.toDistr
    sobFn := f.sobFn + g.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (_ + _)
      simp [map_add, f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_add (f g : Sobolev E F s p) : (f + g).toDistr = f.toDistr + g.toDistr := rfl

instance instSub : Sub (Sobolev E F s p) where
  sub f g := {
    toDistr := f.toDistr - g.toDistr
    sobFn := f.sobFn - g.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (_ - _)
      simp [map_sub, f.bessel_toDistr_eq_sobFn, g.bessel_toDistr_eq_sobFn] }

instance instNeg : Neg (Sobolev E F s p) where
  neg f := {
    toDistr := -f.toDistr
    sobFn := -f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p (- _)
      simp [map_neg, f.bessel_toDistr_eq_sobFn] }

instance instNSMul : SMul ℕ (Sobolev E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [f.bessel_toDistr_eq_sobFn] }

instance instZSMul : SMul ℤ (Sobolev E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [f.bessel_toDistr_eq_sobFn] }

/- Generalize this-/
instance instSMul : SMul ℂ (Sobolev E F s p) where
  smul c f := {
    toDistr := c • f.toDistr
    sobFn := c • f.sobFn
    bessel_toDistr_eq_sobFn := by
      change _ = Lp.toTemperedDistributionCLM F volume p _
      simp [map_smul, f.bessel_toDistr_eq_sobFn] }

@[simp]
theorem toDistr_smul (c : ℂ) (f : Sobolev E F s p) : (c • f).toDistr = c • f.toDistr := rfl

instance instAddCommGroup : AddCommGroup (Sobolev E F s p) :=
  (injective_sobFn E F s p).addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

variable (E F s p) in
/-- Coercion as an additive homomorphism. -/
def coeHom : Sobolev E F s p →+ 𝓢'(E, F) where
  toFun f := f.toDistr
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coeHom_injective : Function.Injective (coeHom E F s p) := by
  apply ext

instance instModule : Module ℂ (Sobolev E F s p) :=
  coeHom_injective.module ℂ (coeHom E F s p) fun _ _ => rfl

variable (E F s p) in
def toLpₗ : Sobolev E F s p →ₗ[ℂ] Lp F p (volume : Measure E) where
  toFun := sobFn
  map_add' f g := by rfl
  map_smul' c f := by rfl

@[simp]
theorem toLpₗ_apply (f : Sobolev E F s p) :
    toLpₗ E F s p f = sobFn f := rfl

theorem sobFn_add (f g : Sobolev E F s p) :
    sobFn (f + g) = sobFn f + sobFn g := rfl

theorem sobFn_smul (c : ℂ) (f : Sobolev E F s p) :
    sobFn (c • f) = c • sobFn f := rfl

instance instNormedAddCommGroup :
    NormedAddCommGroup (Sobolev E F s p) :=
  NormedAddCommGroup.induced (Sobolev E F s p) (Lp F p (volume : Measure E)) (toLpₗ E F s p)
    (injective_sobFn E F s p)

@[simp]
theorem norm_sobFn_eq (f : Sobolev E F s p) : ‖f.sobFn‖ = ‖f‖ :=
  rfl

instance instNormedSpace :
    NormedSpace ℂ (Sobolev E F s p) where
  norm_smul_le c f := by
    simp_rw [← norm_sobFn_eq, ← norm_smul]
    rfl

variable (E F s p) in
def toLpₗᵢ :
    Sobolev E F s p →ₗᵢ[ℂ] Lp F p (volume : Measure E) where
  __ := toLpₗ E F s p
  norm_map' _ := rfl

end Sobolev

end normed

section inner

variable [InnerProductSpace ℂ F] [CompleteSpace F]

theorem memSobolev_two_iff_fourier {s : ℝ} {f : 𝓢'(E, F)} :
    MemSobolev s 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)),
    smulLeftCLM F (fun (x : E) ↦ ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 f) = f' := by
  rw [MemSobolev]
  constructor
  · intro ⟨f', hf'⟩
    use 𝓕 f'
    apply_fun 𝓕 at hf'
    rw [fourier_besselPotential_eq_smulLeftCLM_fourierInv_apply] at hf'
    rw [hf', Lp.fourier_toTemperedDistribution_eq f']
  · intro ⟨f', hf'⟩
    use 𝓕⁻ f'
    rw [besselPotential, TemperedDistribution.fourierMultiplierCLM_apply]
    apply_fun 𝓕⁻ at hf'
    rw [hf', Lp.fourierInv_toTemperedDistribution_eq f']

theorem memSobolev_zero_two_iff_fourierTransform {f : 𝓢'(E, F)} :
    MemSobolev 0 2 f ↔ ∃ (f' : Lp F 2 (volume : Measure E)), 𝓕 f = f' := by
  simp [memSobolev_two_iff_fourier]

open scoped BoundedContinuousFunction

theorem BoundedContinuousFunction.memLp_top (u : E →ᵇ ℂ) : MemLp u ⊤ (volume : Measure E) := by
  constructor
  · fun_prop
  · apply MeasureTheory.eLpNormEssSup_lt_top_of_ae_bound (C := ‖u‖)
    filter_upwards with x
    exact BoundedContinuousFunction.norm_coe_le_norm u x

theorem foo {p q r : ℝ≥0∞} [p.HolderTriple q r] [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    {g : E → ℂ} (hg₁ : g.HasTemperateGrowth) (hg₂ : MemLp g p) (f : Lp F q (volume : Measure E)) :
    Lp.toTemperedDistribution ((ContinuousLinearMap.lsmul ℂ ℂ).holder r (hg₂.toLp _) f) =
    smulLeftCLM F g f := by
  ext u
  simp only [Lp.toTemperedDistribution_apply, smulLeftCLM_apply_apply]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.lsmul ℂ ℂ).coeFn_holder (r := r) (hg₂.toLp _) f,
    hg₂.coeFn_toLp] with x h_holder hg'
  simp [h_holder, hg', hg₁, smul_smul, mul_comm]

theorem memSobolev_fourierMultiplierCLM_bounded {s : ℝ} {g : E → ℂ} (hg₁ : g.HasTemperateGrowth)
    (hg₂ : ∃ C, ∀ x, ‖g x‖ ≤ C) {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev s 2 (fourierMultiplierCLM F g f) := by
  rw [memSobolev_two_iff_fourier] at hf ⊢
  obtain ⟨f', hf⟩ := hf
  obtain ⟨C, hC⟩ := hg₂
  set g' : E →ᵇ ℂ := BoundedContinuousFunction.ofNormedAddCommGroup g hg₁.1.continuous C hC
  use (ContinuousLinearMap.lsmul ℂ ℂ).holderL volume ⊤ 2 2 (g'.memLp_top.toLp _) f'
  rw [ContinuousLinearMap.holderL_apply_apply, foo (by apply hg₁),
    ← hf, fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    smulLeftCLM_smulLeftCLM_apply hg₁ (by fun_prop),
    smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by apply hg₁)]
  congr 2
  ext x
  rw [mul_comm]
  congr

section LineDeriv

open scoped LineDeriv Laplacian Real

/-- The Laplacian maps `H^{s}` to `H^{s - 2}`.

The other implication is slightly harder :-) -/
theorem MemSobolev.laplacian {s : ℝ} {f : 𝓢'(E, F)} (hf : MemSobolev s 2 f) :
    MemSobolev (s - 2) 2 (Δ f) := by
  rw [SubNegMonoid.sub_eq_add_neg s 2, add_comm, ← memSobolev_besselPotential_iff,
    besselPotential_neg_two_laplacian_eq f]
  apply memSobolev_fourierMultiplierCLM_bounded (by fun_prop) _ hf
  use (2 * π) ^ 2
  intro x
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  simp only [pow_one, norm_mul, norm_pow, norm_inv, Real.norm_eq_abs]
  simp only [abs_neg, abs_pow, abs_mul, Nat.abs_ofNat, abs_norm]
  have : 0 < π := by positivity
  rw [abs_of_pos this]
  rw [mul_inv_le_iff₀]
  · gcongr
    grind
  norm_cast
  positivity

end LineDeriv

namespace Sobolev

instance instInnerProductSpace (s : ℝ) :
    InnerProductSpace ℂ (Sobolev E F s 2) where
  inner f g := inner ℂ f.sobFn g.sobFn
  norm_sq_eq_re_inner f := by simp; norm_cast
  conj_inner_symm f g := by simp
  add_left f g h := by rw [sobFn_add, inner_add_left]
  smul_left f g c := by rw [sobFn_smul, inner_smul_left]

open Laplacian

instance instLaplacian (s : ℝ) : Laplacian (Sobolev E F s 2) (Sobolev E F (s - 2) 2) where
  laplacian f := f.memSobolev_toDistr.laplacian.toSobolev

@[simp]
theorem laplacian_toDistr {s : ℝ} (f : Sobolev E F s 2) : (Δ f).toDistr = Δ f.toDistr := rfl

def laplacianₗ {s : ℝ} : Sobolev E F s 2 →ₗ[ℂ] Sobolev E F (s - 2) 2 where
  toFun := Δ
  map_add' f g := by
    ext1
    simpa using (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)).map_add f.toDistr g.toDistr
  map_smul' c f := by
    ext1
    simpa only [laplacian_toDistr, laplacianCLM_apply] using
      (LineDeriv.laplacianCLM ℂ E 𝓢'(E, F)).map_smul c f.toDistr

end Sobolev

end inner
