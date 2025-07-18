/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.SeparationQuotient.Basic
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `LipschitzMul`, `LipschitzAdd`,
`IsBoundedSMul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `ContinuousMul` instance from `LipschitzMul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`IsUniformGroup`) is structured differently.

-/


open NNReal

noncomputable section

variable (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β]

section LipschitzMul

/-- Class `LipschitzAdd M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
class LipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : ∃ C, LipschitzWith C fun p : β × β => p.1 + p.2

/-- Class `LipschitzMul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive]
class LipschitzMul [Monoid β] : Prop where
  lipschitz_mul : ∃ C, LipschitzWith C fun p : β × β => p.1 * p.2

/-- The Lipschitz constant of an `AddMonoid` `β` satisfying `LipschitzAdd` -/
def LipschitzAdd.C [AddMonoid β] [_i : LipschitzAdd β] : ℝ≥0 := Classical.choose _i.lipschitz_add

variable [Monoid β]

/-- The Lipschitz constant of a monoid `β` satisfying `LipschitzMul` -/
@[to_additive existing] -- Porting note: had to add `LipschitzAdd.C`. to_additive silently failed
def LipschitzMul.C [_i : LipschitzMul β] : ℝ≥0 := Classical.choose _i.lipschitz_mul

variable {β}

@[to_additive]
theorem lipschitzWith_lipschitz_const_mul_edist [_i : LipschitzMul β] :
    LipschitzWith (LipschitzMul.C β) fun p : β × β => p.1 * p.2 :=
  Classical.choose_spec _i.lipschitz_mul

variable [LipschitzMul β]

@[to_additive]
theorem lipschitz_with_lipschitz_const_mul :
    ∀ p q : β × β, dist (p.1 * p.2) (q.1 * q.2) ≤ LipschitzMul.C β * dist p q := by
  rw [← lipschitzWith_iff_dist_le_mul]
  exact lipschitzWith_lipschitz_const_mul_edist

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LipschitzMul.continuousMul : ContinuousMul β :=
  ⟨lipschitzWith_lipschitz_const_mul_edist.continuous⟩

@[to_additive]
instance Submonoid.lipschitzMul (s : Submonoid β) : LipschitzMul s where
  lipschitz_mul := ⟨LipschitzMul.C β, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    convert lipschitzWith_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩

@[to_additive]
instance MulOpposite.lipschitzMul : LipschitzMul βᵐᵒᵖ where
  lipschitz_mul := ⟨LipschitzMul.C β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
    (lipschitzWith_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
      (congr_arg _ <| max_comm _ _)⟩

-- this instance could be deduced from `NormedAddCommGroup.lipschitzAdd`, but we prove it
-- separately here so that it is available earlier in the hierarchy
instance Real.hasLipschitzAdd : LipschitzAdd ℝ where
  lipschitz_add := ⟨2, LipschitzWith.of_dist_le_mul fun p q => by
    simp only [Real.dist_eq, Prod.dist_eq, NNReal.coe_ofNat,
      add_sub_add_comm, two_mul]
    refine le_trans (abs_add (p.1 - q.1) (p.2 - q.2)) ?_
    exact add_le_add (le_max_left _ _) (le_max_right _ _)⟩

-- this instance has the same proof as `AddSubmonoid.lipschitzAdd`, but the former can't
-- directly be applied here since `ℝ≥0` is a subtype of `ℝ`, not an additive submonoid.
instance NNReal.hasLipschitzAdd : LipschitzAdd ℝ≥0 where
  lipschitz_add := ⟨LipschitzAdd.C ℝ, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    exact lipschitzWith_lipschitz_const_add_edist ⟨(x₁ : ℝ), x₂⟩ ⟨y₁, y₂⟩⟩

end LipschitzMul

section IsBoundedSMul

variable [Zero α] [Zero β] [SMul α β]

/-- Mixin typeclass on a scalar action of a metric space `α` on a metric space `β` both with
distinguished points `0`, requiring compatibility of the action in the sense that
`dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂` and
`dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0`.

If `[NormedDivisionRing α] [SeminormedAddCommGroup β] [Module α β]` are assumed, then prefer writing
`[NormSMulClass α β]` instead of using `[IsBoundedSMul α β]`, since while equivalent, typeclass
search can only infer the latter from the former and not vice versa. -/
class IsBoundedSMul : Prop where
  dist_smul_pair' : ∀ x : α, ∀ y₁ y₂ : β, dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂
  dist_pair_smul' : ∀ x₁ x₂ : α, ∀ y : β, dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0

@[deprecated (since := "2025-03-10")] alias BoundedSMul := IsBoundedSMul

variable {α β}
variable [IsBoundedSMul α β]

theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂ :=
  IsBoundedSMul.dist_smul_pair' x y₁ y₂

theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0 :=
  IsBoundedSMul.dist_pair_smul' x₁ x₂ y

-- see Note [lower instance priority]
/-- The typeclass `IsBoundedSMul` on a metric-space scalar action implies continuity of the
action. -/
instance (priority := 100) IsBoundedSMul.continuousSMul : ContinuousSMul α β where
  continuous_smul := by
    rw [Metric.continuous_iff]
    rintro ⟨a, b⟩ ε ε0
    obtain ⟨δ, δ0, hδε⟩ : ∃ δ > 0, δ * (δ + dist b 0) + dist a 0 * δ < ε := by
      have : Continuous fun δ ↦ δ * (δ + dist b 0) + dist a 0 * δ := by fun_prop
      refine ((this.tendsto' _ _ ?_).eventually (gt_mem_nhds ε0)).exists_gt
      simp
    refine ⟨δ, δ0, fun (a', b') hab' => ?_⟩
    obtain ⟨ha, hb⟩ := max_lt_iff.1 hab'
    calc dist (a' • b') (a • b)
        ≤ dist (a' • b') (a • b') + dist (a • b') (a • b) := dist_triangle ..
      _ ≤ dist a' a * dist b' 0 + dist a 0 * dist b' b :=
        add_le_add (dist_pair_smul _ _ _) (dist_smul_pair _ _ _)
      _ ≤ δ * (δ + dist b 0) + dist a 0 * δ := by
          have : dist b' 0 ≤ δ + dist b 0 := (dist_triangle _ _ _).trans <| add_le_add_right hb.le _
          gcongr
      _ < ε := hδε

instance (priority := 100) IsBoundedSMul.toUniformContinuousConstSMul :
    UniformContinuousConstSMul α β :=
  ⟨fun c => ((lipschitzWith_iff_dist_le_mul (K := nndist c 0)).2 fun _ _ =>
    dist_smul_pair c _ _).uniformContinuous⟩

-- this instance could be deduced from `NormedSpace.isBoundedSMul`, but we prove it separately
-- here so that it is available earlier in the hierarchy
instance Real.isBoundedSMul : IsBoundedSMul ℝ ℝ where
  dist_smul_pair' x y₁ y₂ := by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le

instance NNReal.isBoundedSMul : IsBoundedSMul ℝ≥0 ℝ≥0 where
  dist_smul_pair' x y₁ y₂ := by convert dist_smul_pair (x : ℝ) (y₁ : ℝ) y₂ using 1
  dist_pair_smul' x₁ x₂ y := by convert dist_pair_smul (x₁ : ℝ) x₂ (y : ℝ) using 1

/-- If a scalar is central, then its right action is bounded when its left action is. -/
instance IsBoundedSMul.op [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : IsBoundedSMul αᵐᵒᵖ β where
  dist_smul_pair' :=
    MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using dist_smul_pair x y₁ y₂
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using dist_pair_smul x₁ x₂ y

end IsBoundedSMul

instance [Monoid α] [LipschitzMul α] : LipschitzAdd (Additive α) :=
  ⟨@LipschitzMul.lipschitz_mul α _ _ _⟩

instance [AddMonoid α] [LipschitzAdd α] : LipschitzMul (Multiplicative α) :=
  ⟨@LipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]
instance [Monoid α] [LipschitzMul α] : LipschitzMul αᵒᵈ :=
  ‹LipschitzMul α›

variable {ι : Type*} [Fintype ι]

instance Pi.instIsBoundedSMul {α : Type*} {β : ι → Type*} [PseudoMetricSpace α]
    [∀ i, PseudoMetricSpace (β i)] [Zero α] [∀ i, Zero (β i)] [∀ i, SMul α (β i)]
    [∀ i, IsBoundedSMul α (β i)] : IsBoundedSMul α (∀ i, β i) where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (dist_le_pi_dist _ _ _) dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (dist_le_pi_dist _ 0 _) dist_nonneg

instance Pi.instIsBoundedSMul' {α β : ι → Type*} [∀ i, PseudoMetricSpace (α i)]
    [∀ i, PseudoMetricSpace (β i)] [∀ i, Zero (α i)] [∀ i, Zero (β i)] [∀ i, SMul (α i) (β i)]
    [∀ i, IsBoundedSMul (α i) (β i)] : IsBoundedSMul (∀ i, α i) (∀ i, β i) where
  dist_smul_pair' x y₁ y₂ :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_smul_pair _ _ _).trans <|
        mul_le_mul (dist_le_pi_dist _ 0 _) (dist_le_pi_dist _ _ _) dist_nonneg dist_nonneg
  dist_pair_smul' x₁ x₂ y :=
    (dist_pi_le_iff <| by positivity).2 fun _ ↦
      (dist_pair_smul _ _ _).trans <|
        mul_le_mul (dist_le_pi_dist _ _ _) (dist_le_pi_dist _ 0 _) dist_nonneg dist_nonneg

instance Prod.instIsBoundedSMul {α β γ : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [PseudoMetricSpace γ] [Zero α] [Zero β] [Zero γ] [SMul α β] [SMul α γ] [IsBoundedSMul α β]
    [IsBoundedSMul α γ] : IsBoundedSMul α (β × γ) where
  dist_smul_pair' _x _y₁ _y₂ :=
    max_le ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_smul_pair _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)
  dist_pair_smul' _x₁ _x₂ _y :=
    max_le ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_left _ _) dist_nonneg)
      ((dist_pair_smul _ _ _).trans <| mul_le_mul_of_nonneg_left (le_max_right _ _) dist_nonneg)

instance {α β : Type*}
    [PseudoMetricSpace α] [PseudoMetricSpace β] [Zero α] [Zero β] [SMul α β] [IsBoundedSMul α β] :
    IsBoundedSMul α (SeparationQuotient β) where
  dist_smul_pair' _ := Quotient.ind₂ <| dist_smul_pair _
  dist_pair_smul' _ _ := Quotient.ind <| dist_pair_smul _ _

-- We don't have the `SMul α γ → SMul β δ → SMul (α × β) (γ × δ)` instance, but if we did, then
-- `IsBoundedSMul α γ → IsBoundedSMul β δ → IsBoundedSMul (α × β) (γ × δ)` would hold
