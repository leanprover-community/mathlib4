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

attribute [-instance] Finsupp.pointwiseScalar

-- #check Coe*

noncomputable
instance Finsupp.pointwiseScalar' {α β γ : Type*} [AddCommMonoid β] [Semiring γ] [Module γ β] :
    HSMul (α → β) (α →₀ γ) (α →₀ β) where
  hSMul f g :=
    Finsupp.ofSupportFinite (fun a ↦ g a • f a) (by
      apply Set.Finite.subset g.finite_support
      simp only [Function.support_subset_iff, Finsupp.mem_support_iff, Ne,
        Finsupp.fun_support_eq, Finset.mem_coe]
      intro x hx h
      apply hx
      rw [h, zero_smul])

@[simp] theorem Finsupp.pointwiseScalar.smul_apply {α β γ : Type*}
    [AddCommMonoid β] [Semiring γ] [Module γ β] (f : α → β) (g : α →₀ γ) (a : α) :
    (f • g) a = g a • f a := by
  rfl

def SupportedCoprime (μ : (Fin 2 → ℤ) →₀ ℝ≥0) : Prop :=
  ∀ p ∈ μ.support, IsCoprime (p 0) (p 1)

class WellDistributed {ι : Type*} (μ : ι →₀ ℝ≥0) : Prop where
  is_well_distributed : ∀ i : ι, μ i ≤ 1


variable (μ ν : (Fin 2 → ℤ) →₀ ℝ≥0)
  (hμ : SupportedCoprime μ) (hν : SupportedCoprime ν)
  (hμ_le : WellDistributed μ) (hν_le : WellDistributed ν)
  (β : ℝ) (a q : ℕ) (hq₀ : q ≠ 0) (haq : IsCoprime a q) (N Q K : ℝ≥0) (hK₀ : 0 ≤ K) (hQ₀ : 0 ≤ Q)
  (hQ : Q ^ 2 < N)
  (hK : Q ^ 2 * K ^ 2 < N) (hq₁ : Q / 2 ≤ q) (hq₂ : q ≤ Q) (hβ₁ : K / (2 * N) ≤ |β|)
  (hβ₂ : |β| ≤ K / N)
  (hμN : ∀ x ∈ μ.support, x ⬝ᵥ x ≤ (N : ℝ))
  (hνN : ∀ y ∈ ν.support, y ⬝ᵥ y ≤ (N : ℝ))

-- FIXME why isn't this notation showing up?
set_option quotPrecheck false in
notation "θ" => (a:ℝ) / q + β

@[simps] def Finsupp.pointwise_prod {α β A : Type*} [Semiring A] [DecidableEq A]
    (f : α →₀ A) (g : β →₀ A) : α × β →₀ A where
  support := (f.support ×ˢ g.support).filter (fun x ↦ f x.1 * g x.2 ≠ 0)
  toFun p := f p.1 * g p.2
  mem_support_toFun := by
    intro x
    simp [-ne_eq]
    contrapose
    push_neg
    intro h
    by_cases h' : f x.1 = 0
    · simp [h']
    · simp [h h']

def Finsupp.mass {α A : Type*} [AddCommMonoid A] (a : α →₀ A) : A := a.sum (fun _ ↦ id)

notation3 "∑ "(...)", "r:60:(scoped f => f)" ∂"μ:70 => Finsupp.mass (r • μ)
notation3 "∑ "(...)" in "s", "r:60:(scoped f => f)" ∂"μ:70 => Finsupp.mass (r • (Finsupp.filter (· ∈ s) μ))

-- TODO figure out how to get `∑ x ∈ s`, not just `∑ x in s`
theorem Finsupp.smul_mass {α A : Type*} [AddCommMonoid A] [Module ℝ≥0 A] (μ : α →₀ ℝ≥0) (f : α → A)
    (c : ℝ≥0) :
    (c • ∑ a, f a ∂μ) = ∑ a, c • f a ∂μ := by
  unfold Finsupp.mass
  symm
  convert Finsupp.sum_smul_index_linearMap' (v := (fun a ↦ f a) • μ) (h := fun _ ↦ LinearMap.id)
  ext a
  simp only [pointwiseScalar.smul_apply, coe_smul, Pi.smul_apply]
  rw [smul_comm]

set_option quotPrecheck false in
notation "S" =>
 ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), exp (2 * π * I * θ * (p.1 ⬝ᵥ p.2)) ∂(μ.pointwise_prod ν)

-- TODO ok for both to be simp?

theorem Finsupp.mass_eq_tsum {α A K : Type*} [Semiring A] [AddCommMonoid K] [TopologicalSpace K]
    [Module A K]
    (f : α → K) (μ : α →₀ A) :
    ∑ x, f x ∂μ  = ∑' x, μ x • f x := by
  sorry

@[simp]
theorem fubini {α β : Type*} {A K : Type*} [DecidableEq A] [Semiring A] [AddCommMonoid K]
    [Module A K] (f : α → β → K)
    (μ : α →₀ A) (ν : β →₀ A) :
    ∑ p : α × β, f p.1 p.2 ∂(μ.pointwise_prod ν) = ∑ x, (∑ y, f x y ∂ν) ∂μ := by
  sorry

@[simp]
theorem fubini' {α β : Type*} {A K : Type*} [DecidableEq A] [Semiring A] [AddCommMonoid K]
    [Module A K] (f : α × β → K)
    (μ : α →₀ A) (ν : β →₀ A) :
    ∑ p : α × β, f p ∂(μ.pointwise_prod ν) = ∑ x, (∑ y, f (x, y) ∂ν) ∂μ := by
  sorry

@[simp]
theorem Finsupp.sum_const {α A K : Type*} [Semiring A] [AddCommMonoid K] [Module A K] (c : K)
    (μ : α →₀ A) :
    ∑ x : α, c ∂μ = μ.mass • c := by
  sorry

theorem cauchy_schwarz {α : Type*} (μ : α →₀ ℝ≥0) (f g : α → ℂ) :
    ‖∑ x, f x * g x ∂μ‖₊ ^ 2 ≤ (∑ x, ‖f x‖₊ ^ 2 ∂μ) * (∑ x, ‖g x‖₊ ^ 2 ∂μ) := by
  sorry

theorem Finsupp.sum_comm_tsum {α β E : Type*} [AddCommMonoid E] [Module ℝ≥0 E] [TopologicalSpace E]
    [T2Space E] [ContinuousAdd E] [ContinuousConstSMul ℝ≥0 E]
    (μ : α →₀ ℝ≥0) (f : α → β → E) (hf : ∀ a ∈ μ.support, Summable (f a)) :
    ∑ a : α, (∑' b : β, f a b) ∂μ = ∑' b : β, (∑ a : α, f a b ∂μ) := by
  calc
  ∑ a : α, (∑' b : β, f a b) ∂μ
    = ∑ a ∈ μ.support, μ a • (∑' b : β, f a b) := by
      -- FIXME lemma here
      refine Finsupp.sum_of_support_subset _ ?_ _ (by simp)
      intro a
      contrapose!
      simp
      intro ha
      simp [ha]
  _ = ∑ a ∈ μ.support, (∑' b : β, μ a • f a b) := by
      congr! with a ha
      rw [tsum_const_smul _ (hf _ ha)]
  _ = ∑' b : β, (∑ a ∈ μ.support, μ a • f a b) := by
      symm
      apply tsum_sum
      intro a ha
      apply (hf a ha).const_smul
  _ = ∑' b : β, (∑ a : α, f a b ∂μ) := by
      congr! with b
      symm
      -- FIXME use previous lemma
      refine Finsupp.sum_of_support_subset _ ?_ _ (by simp)
      intro a
      contrapose!
      simp
      intro ha
      simp [ha]

theorem Finsupp.sum_comm_tsum_weight {α β E : Type*} [AddCommMonoid E] [Module ℝ≥0 E]
    [TopologicalSpace E] [T2Space E] [ContinuousAdd E] [ContinuousConstSMul ℝ≥0 E]
    (μ : α →₀ ℝ≥0) (ν : β → ℝ≥0) (f : α → β → E) (hf : ∀ a ∈ μ.support, Summable (ν • f a)) :
    ∑ a : α, (∑' b : β, ν b • f a b) ∂μ = ∑' b : β, ν b • (∑ a : α, f a b ∂μ) := by
  convert Finsupp.sum_comm_tsum μ (ν • f) ?_ with _ _ b
  · apply Finsupp.smul_mass
  · exact hf

noncomputable def FT (f : (Fin 2 → ℝ) → ℂ) : (Fin 2 → ℝ) → ℂ := sorry

lemma FTtwist (f : (Fin 2 → ℝ) → ℂ) (t k : Fin 2 → ℝ) : -- add side conditions
    FT (fun x ↦ f x * exp (2 * π * I * (x ⬝ᵥ t))) k = FT f (k - t) := by
  sorry

lemma FTdilate (f : (Fin 2 → ℝ) → ℂ) (t : ℝ) (k : Fin 2 → ℝ) : -- add side conditions
    FT (fun x ↦ f (t⁻¹ • x)) k = t ^ 2 * FT f (t • k) := by
  sorry

lemma PoissonSum (f : (Fin 2 → ℝ) → ℂ) : -- add conditions
    ∑' (x : Fin 2 → ℤ), f (Int.cast ∘ x) = ∑' (k : Fin 2 → ℤ), FT f (Int.cast ∘ k) := by
  sorry

-- distance to nearest lattice point in `Fin 2 → ℤ`
noncomputable def Hdist (z : Fin 2 → ℝ) : ℝ≥0 := sorry

-- set_option synthInstance.maxHeartbeats 400000 in
example : ‖S‖₊ ^ 2 ≤ (μ.mass ^ 2 * ν.mass ^ 2) / (K * Q) ^ 2 := by
  let f : (Fin 2 → ℤ) → ℂ := 1
  let g (x : Fin 2 → ℤ) : ℂ :=  ∑ y : Fin 2 → ℤ, exp (2 * π * I * θ * (x ⬝ᵥ y)) ∂ν
  calc _ = _ := by simp [f, g]
    _ ≤ _ := cauchy_schwarz μ f g
    _ = μ.mass * ∑ x, ‖g x‖₊ ^ 2 ∂μ := by
        congr
        simp only [Pi.one_apply, nnnorm_one, one_pow, f]
        --change (algebraMap NNReal ℝ μ.mass) * 1 = _
        sorry -- should be ring
    _ ≤ μ.mass * ((μ.mass * ν.mass ^ 2) / (K * Q) ^ 2) := ?_
    _ = _ := by
      sorry -- should be ring
  gcongr
  rw [Finsupp.mass_eq_tsum]
  let φ : (Fin 2 → ℝ) → ℝ≥0 := sorry
  have φ_bnd : ∀ x, (∀ i, (x i)^2 ≤ 1) → 1 ≤ φ x := sorry
  let ψ : (Fin 2 → ℝ) → ℝ≥0 := sorry
  let ψ_max : ℝ≥0 := sorry
  have ψ_bnd : ∀ k, ψ k ≤ ψ_max := sorry
  have ψ_eq_FTφ : FT (fun x ↦ (φ x : ℂ)) = (fun x ↦ (ψ x : ℂ)) := sorry
  have FTφ_supp : (FT (fun x ↦ (φ x : ℂ))).support ⊆ {x : Fin 2 → ℝ | ∀ i, (x i)^2 ≤ 1/4} := sorry
  let μ' : (Fin 2 → ℝ) → ℝ≥0 := fun x ↦ φ ((√N)⁻¹ • x)
  have hμ : ∀ x : Fin 2 → ℤ, μ x ≤ μ' (Int.cast ∘ x) := sorry -- prove from `φ_bnd`
  have hμ' : Summable (fun (x : Fin 2 → ℤ) ↦ μ' (Int.cast ∘ x)) := sorry
  have hμ'_exp (n : Fin 2 → ℤ) : Summable (fun (y : Fin 2 → ℤ) ↦
    μ' (Int.cast ∘ y) • exp (2 * π * I * (a / q + β) * (y ⬝ᵥ n))) := sorry
  calc _ ≤ ∑' (x : Fin 2 → ℤ), μ' (Int.cast ∘ x) • ‖g x‖₊ ^ 2 := by
        apply tsum_mono
        · sorry -- summability of finsupps
        · sorry -- summability of the new `μ'`
        intro x
        dsimp
        gcongr
        apply hμ
    _ ≤ _ := ?_
  have hg (x : Fin 2 → ℤ) :=
  calc
    ‖g x‖₊ ^ 2
      = g x * conj (g x) := sorry
    _ = (∑ y : Fin 2 → ℤ, exp (2 * π * I * θ * (x ⬝ᵥ y)) ∂ν)
        * conj (∑ y' : Fin 2 → ℤ, exp (2 * π * I * θ * (x ⬝ᵥ y')) ∂ν) := sorry
    _ = ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ),
          exp (2 * π * I * θ * (x ⬝ᵥ p.1))
          * conj (exp (2 * π * I * θ * (x ⬝ᵥ p.2))) ∂(ν.pointwise_prod ν) := sorry
    _ = ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ),
          exp (2 * π * I * θ * (x ⬝ᵥ (p.1 - p.2))) ∂(ν.pointwise_prod ν) := sorry
  have :=
  calc ∑' (x : Fin 2 → ℤ), μ' (Int.cast ∘ x) • ‖g x‖₊ ^ 2
      = ∑' (x : Fin 2 → ℤ), μ' (Int.cast ∘ x) • (∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ),
          exp (2 * π * I * θ * (x ⬝ᵥ (p.1 - p.2))) ∂(ν.pointwise_prod ν)) := by
        push_cast
        congr! with x
        trans μ' (Int.cast ∘ x) • ‖g x‖₊ ^ 2
        · sorry -- casting issue
        rw [hg]
        rfl
    _ = ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), (∑' (x : Fin 2 → ℤ),
          (μ' (Int.cast ∘ x) • exp (2 * π * I * θ * (x ⬝ᵥ (p.1 - p.2)))))
            ∂(ν.pointwise_prod ν) := by
        rw [Finsupp.sum_comm_tsum_weight]
        intro (n₁, n₂) hn
        exact hμ'_exp _
    _ = ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), (∑' (k : Fin 2 → ℤ),
          FT (fun (x : Fin 2 → ℝ) ↦ μ' x • exp (2 * π * I * θ * (x ⬝ᵥ (Int.cast ∘ (p.1 - p.2)))))
            (Int.cast ∘ k)) ∂(ν.pointwise_prod ν) := by
        congr! 3 with p
        rw [← PoissonSum]
        congr! with k
        simp only [Matrix.dotProduct_sub, Matrix.vec2_dotProduct, Fin.isValue, Int.cast_sub,
          Int.cast_add, Int.cast_mul, Function.comp_apply, Pi.sub_apply, ofReal_add, ofReal_mul,
          ofReal_intCast, ofReal_sub]
        ring
    _ = ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), (∑' (k : Fin 2 → ℤ),
          FT (fun x ↦ (μ' x : ℂ)) ((Int.cast ∘ k) - θ • (Int.cast ∘ (p.1 - p.2))))
             ∂(ν.pointwise_prod ν) := by
        congr! 5 with p k
        rw [← FTtwist]
        congr! 2 with x
        sorry -- casting and ring
    _ = ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), (∑' (k : Fin 2 → ℤ),
          (√N)^2 * FT (fun x ↦ (φ x : ℂ)) (√N • ((Int.cast ∘ k) - θ • (Int.cast ∘ (p.1 - p.2)))))
             ∂(ν.pointwise_prod ν) := by
        congr! 5 with p k
        dsimp [μ']
        apply FTdilate
    _ = ((∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), (∑' (k : Fin 2 → ℤ),
          (NNReal.sqrt N)^2 * ψ (√N • ((Int.cast ∘ k) - θ • (Int.cast ∘ (p.1 - p.2)))))
             ∂(ν.pointwise_prod ν) ) ) := by
        sorry
    _ = ((∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), (∑' (k : Fin 2 → ℤ),
          N * ψ (√N • ((Int.cast ∘ k) - θ • (Int.cast ∘ (p.1 - p.2)))))
             ∂(ν.pointwise_prod ν) ) ) := by
        sorry
  norm_cast at this
  rw [this]; clear this
  have fact1 (z : Fin 2 → ℝ) (k : Fin 2 → ℤ) : ψ (√N • (Int.cast ∘ k - z)) ≠ 0 →
    Hdist z < 1 / (NNReal.sqrt N) := sorry
  have fact2 (z : Fin 2 → ℝ) : {k : Fin 2 → ℤ | ψ (√N • (Int.cast ∘ k - z)) ≠ 0}.ncard ≤ 1 := by
    sorry
  let IndSet : Set ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
    {p : (Fin 2 → ℤ) × (Fin 2 → ℤ) | Hdist (θ • Int.cast ∘ (p.1 - p.2)) < 1 / NNReal.sqrt N}
  classical
  calc
    ∑ p : (Fin 2 → ℤ) × (Fin 2 → ℤ), ∑' k : Fin 2 → ℤ,
      N * ψ (√↑N • (Int.cast ∘ k - θ • Int.cast ∘ (p.1 - p.2))) ∂ν.pointwise_prod ν
      = ∑ (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) in IndSet, ∑' k : Fin 2 → ℤ,
        -- TODO can the notation be prettier?
          N * ψ (√↑N • (Int.cast ∘ k - θ • Int.cast ∘ (p.1 - p.2)))
          ∂ν.pointwise_prod ν := sorry
    _ ≤ ∑ (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) in IndSet,
        N * ψ_max ∂ν.pointwise_prod ν := sorry
    _ = N * ψ_max *
          ∑ (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) in IndSet, (1 : ℝ≥0) ∂ν.pointwise_prod ν := sorry
    _ ≤ N * ψ_max * Finset.card ((ν.support ×ˢ ν.support).filter IndSet) := sorry

  have H1 : ∀ p ∈ (ν.support ×ˢ ν.support).filter IndSet,
      p.1 0 ≡ p.2 0 [ZMOD q] ∧ p.1 1 ≡ p.2 1 [ZMOD q] := by
    sorry

  -- TODO maybe use ‖p.1 - p.2‖₊ (the max norm) throughout, rather than L^2 norm
  have H2 : ∀ p ∈ (ν.support ×ˢ ν.support).filter IndSet,
      (↑((p.1 - p.2) ⬝ᵥ (p.1 - p.2)) : ℝ) ≤ NNReal.sqrt N / K := by
    sorry

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
  (β : ℝ) (a q : ℕ) (hq₀ : q ≠ 0) (haq : IsCoprime a q) (N Q K : ℝ) (hK₀ : 1 ≤ K) (hQ₀ : 1 ≤ Q)
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
