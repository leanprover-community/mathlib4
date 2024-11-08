/-
Copyright (c) 2024 Alex Kontorovich, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/
import Mathlib

open scoped ComplexConjugate
open scoped NNReal ENNReal Matrix Real
open MeasureTheory Complex

/-! Delaborator for complex conjugation -- to be added to Mathlib. -/
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.DFunLike.coe]
def conjDelab : Delab := do
  let f ← withNaryArg 4 delab
  let Syntax.node _ _ #[starRingEndSyntax, cplxSyntax₁] := (f : Syntax) | failure
  let Syntax.ident _ _ ``starRingEnd _ := starRingEndSyntax | failure
  let Syntax.node _ _ #[cplxSyntax₂] := cplxSyntax₁ | failure
  let Syntax.node _ _ #[cplxSyntax₃] := cplxSyntax₂ | failure
  let Syntax.atom _ "ℂ" := cplxSyntax₃ | failure
  let z ← withNaryArg 5 delab
  `(conj $z)

def SupportedCoprime (μ : (Fin 2 → ℤ) →₀ ℝ≥0) : Prop :=
  ∀ p ∈ μ.support, IsCoprime (p 0) (p 1)

class WellDistributed {ι : Type*} (μ : ι →₀ ℝ≥0) : Prop where
  is_well_distributed : ∀ i : ι, μ i ≤ 1


variable (μ ν : (Fin 2 → ℤ) →₀ ℝ≥0)
  (hμ : SupportedCoprime μ) (hν : SupportedCoprime ν)
  (β : ℝ) (a q : ℕ) (hq₀ : q ≠ 0) (haq : IsCoprime a q) (N Q K : ℝ) (hK₀ : 0 ≤ K) (hQ₀ : 0 ≤ Q)
  (hQ : Q ^ 2 < N)
  (hK : Q ^ 2 * K ^ 2 < N) (hq₁ : Q / 2 ≤ q) (hq₂ : q ≤ Q) (hβ₁ : K / (2 * N) ≤ |β|)
  (hβ₂ : |β| ≤ K / N)
  (hμN : ∀ x ∈ μ.support, x ⬝ᵥ x ≤ N)
  (hνN : ∀ y ∈ ν.support, y ⬝ᵥ y ≤ N)

-- FIXME why isn't this notation showing up?
set_option quotPrecheck false in
notation "θ" => (a:ℝ) / q + β

@[simps] def Finsupp.pointwise_prod {α β A : Type*} [Semiring A] [NoZeroDivisors A]
    (f : α →₀ A) (g : β →₀ A) : α × β →₀ A where
  support := f.support ×ˢ g.support
  toFun p := f p.1 * g p.2
  mem_support_toFun := by simp [mul_ne_zero_iff]

def Finsupp.mass {α A : Type*} [AddCommMonoid A] (a : α →₀ A) : A := a.sum (fun _ ↦ id)

notation "coe" => Finsupp.mapRange (fun a ↦ a : ℝ≥0 → ℂ) (by simp)

set_option quotPrecheck false in
notation "S" => Finsupp.mass <|
 (fun (x, y) ↦ exp (2 * π * I * θ * (x ⬝ᵥ y)) : (Fin 2 → ℤ) × (Fin 2 → ℤ) → ℂ)
  • (coe (μ.pointwise_prod ν))

example : ‖S‖ ^ 2 ≤ ((μ * μ).mass * (ν * ν).mass : ℝ) / (K * Q) ^ 2 := by
  sorry

#exit


-- rename

-- alternative implementation: l∞ norm ≤ 1
-- variable (μ ν : lp (fun _ : (Fin 2 → ℤ) ↦ ℝ) ∞)

def SupportedCoprime (μ : Measure (Fin 2 → ℤ)) : Prop :=
  ∀ p : Fin 2 → ℤ, μ {p} ≠ 0 → IsCoprime (p 0) (p 1)

variable (μ ν : Measure (Fin 2 → ℤ)) [IsFiniteMeasure μ]
  [WellDistributed μ] [WellDistributed ν]
  (hμ : SupportedCoprime μ) (hν : SupportedCoprime ν)
  (β : ℝ) (a q : ℕ) (hq₀ : q ≠ 0) (haq : IsCoprime a q) (N Q K : ℝ) (hK₀ : 0 ≤ K) (hQ₀ : 0 ≤ Q)
  (hQ : Q ^ 2 < N)
  (hK : Q ^ 2 * K ^ 2 < N) (hq₁ : Q ≤ q) (hq₂ : q ≤ 2 * Q) (hβ₁ : K / (2 * N) ≤ |β|)
  (hβ₂ : |β| ≤ K / N)
  (hμN : ∀ x : Fin 2 → ℤ, μ {x} ≠ 0 → x ⬝ᵥ x ≤ N)
  (hνN : ∀ y : Fin 2 → ℤ, ν {y} ≠ 0 → y ⬝ᵥ y ≤ N)



theorem MeasureTheory.Lp.norm_const'' {α : Type*} {E : Type*} {m0 : MeasurableSpace α} (p : ℝ≥0∞)
    (μ : Measure α) [NormedAddCommGroup E] [IsFiniteMeasure μ] (c : E) [NeZero μ]
    (hp_zero : p ≠ 0) :
    ‖(Lp.const p μ) c‖ = ‖c‖ * (measureUnivNNReal μ) ^ (1 / p.toReal) :=
  sorry

section CauchySchwarzIntegral

variable {α : Type*} {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
  (μ : Measure α)
  (f g : α → 𝕜)

theorem cauchy_schwarz (hf : Memℒp f 2 μ) (hg : Memℒp g 2 μ) :
    ‖∫ a, f a * g a ∂μ‖ ^ 2 ≤ (∫ a, ‖f a‖ ^ 2 ∂μ) * (∫ a, ‖g a‖ ^ 2 ∂μ) :=
  sorry

@[simp] theorem measure_univ_toReal : (μ Set.univ).toReal = measureUnivNNReal μ := rfl

end CauchySchwarzIntegral

/-- Nonnegative function at least one near zero, whose Fourier transform is supported near 0. -/
def γ (x : Fin 2 → ℝ) : ℝ≥0 := sorry

example : ‖S‖ ^ 2 ≤ (measureUnivNNReal μ) ^ 2 * (measureUnivNNReal ν) ^ 2 / (K * Q) ^ 2 := by
  have : SFinite ν := sorry
  let f : (Fin 2 → ℤ) → ℂ := 1
  have hf : Memℒp f 2 μ := sorry --indicatorConstLp (μ := μ) (s := Set.univ) 2 sorry sorry 1
  let g : (Fin 2 → ℤ) → ℂ := fun x ↦ ∫ y : Fin 2 → ℤ, exp (2 * π * I * θ * (x ⬝ᵥ y)) ∂ν
  calc
    _ = _ := by simp [f, g]
    _ ≤ _ := cauchy_schwarz (𝕜 := ℂ) μ f g hf sorry
    _ = (measureUnivNNReal μ) * (∫ a, ‖g a‖ ^ 2 ∂μ) := by simp [f]
    _ ≤ (measureUnivNNReal μ) *
          ((measureUnivNNReal μ) * (measureUnivNNReal ν) ^ 2 / (K * Q) ^ 2) := ?_
    _ = _ := by ring
  gcongr
  let μ' : Measure (Fin 2 → ℤ) := (γ ((N:ℝ)⁻¹ • (Int.cast ∘ a))) • Measure.count
  have : SFinite μ' := sorry
  have hμ : μ ≤ μ' := sorry
  calc _ ≤ ∫ (a : Fin 2 → ℤ), ‖g a‖ ^ 2  ∂μ' := by
          refine integral_mono_measure hμ ?hf ?hfi
          · apply Filter.Eventually.of_forall (fun _ ↦ ?_)
            positivity
          · sorry -- integrability
    _ = ‖∫ (a : Fin 2 → ℤ), conj (g a) * g a ∂μ'‖ := sorry
    _ ≤ _ := ?_
  dsimp only [g]
  simp_rw [← integral_conj]
  simp_rw [← integral_prod_mul]
  rw [integral_integral_swap]
  calc _ ≤ _ := norm_integral_le_integral_norm ..
    _ ≤ _ := ?_
  norm_cast
  simp only [← exp_conj, ← exp_add]
  set θ' := a / q + β
  conv =>
    enter [1, 2, a, 1, 2, x, 1]
    simp [conj_ofNat, -Matrix.vec2_dotProduct]
    rw [add_comm]
    rw [← sub_eq_add_neg]
    rw [← mul_sub]
  norm_cast
  conv =>
    enter [1, 2, a, 1, 2, x, 1, 2, 1]
    rw [← Matrix.dotProduct_sub]
  dsimp only [μ']
  -- simp_rw [integral_smul_measure]
  sorry
  sorry
