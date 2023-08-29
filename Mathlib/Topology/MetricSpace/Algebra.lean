/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Monotonicity
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Lipschitz

#align_import topology.metric_space.algebra from "leanprover-community/mathlib"@"14d34b71b6d896b6e5f1ba2ec9124b9cd1f90fca"

/-!
# Compatibility of algebraic operations with metric space structures

In this file we define mixin typeclasses `LipschitzMul`, `LipschitzAdd`,
`BoundedSMul` expressing compatibility of multiplication, addition and scalar-multiplication
operations with an underlying metric space structure.  The intended use case is to abstract certain
properties shared by normed groups and by `R≥0`.

## Implementation notes

We deduce a `ContinuousMul` instance from `LipschitzMul`, etc.  In principle there should
be an intermediate typeclass for uniform spaces, but the algebraic hierarchy there (see
`UniformGroup`) is structured differently.

-/


open NNReal

noncomputable section

variable (α β : Type*) [PseudoMetricSpace α] [PseudoMetricSpace β]

section LipschitzMul

/-- Class `LipschitzAdd M` says that the addition `(+) : X × X → X` is Lipschitz jointly in
the two arguments. -/
class LipschitzAdd [AddMonoid β] : Prop where
  lipschitz_add : ∃ C, LipschitzWith C fun p : β × β => p.1 + p.2
#align has_lipschitz_add LipschitzAdd

/-- Class `LipschitzMul M` says that the multiplication `(*) : X × X → X` is Lipschitz jointly
in the two arguments. -/
@[to_additive]
class LipschitzMul [Monoid β] : Prop where
  lipschitz_mul : ∃ C, LipschitzWith C fun p : β × β => p.1 * p.2
#align has_lipschitz_mul LipschitzMul

/-- The Lipschitz constant of an `AddMonoid` `β` satisfying `LipschitzAdd` -/
def LipschitzAdd.C [AddMonoid β] [_i : LipschitzAdd β] : ℝ≥0 := Classical.choose _i.lipschitz_add
set_option linter.uppercaseLean3 false in
#align has_lipschitz_add.C LipschitzAdd.C

variable [Monoid β]

/-- The Lipschitz constant of a monoid `β` satisfying `LipschitzMul` -/
@[to_additive existing] -- porting note: had to add `LipschitzAdd.C`. to_additive silently failed
def LipschitzMul.C [_i : LipschitzMul β] : ℝ≥0 := Classical.choose _i.lipschitz_mul
set_option linter.uppercaseLean3 false in
#align has_lipschitz_mul.C LipschitzMul.C

variable {β}

@[to_additive]
theorem lipschitzWith_lipschitz_const_mul_edist [_i : LipschitzMul β] :
    LipschitzWith (LipschitzMul.C β) fun p : β × β => p.1 * p.2 :=
  Classical.choose_spec _i.lipschitz_mul
#align lipschitz_with_lipschitz_const_mul_edist lipschitzWith_lipschitz_const_mul_edist
#align lipschitz_with_lipschitz_const_add_edist lipschitzWith_lipschitz_const_add_edist

variable [LipschitzMul β]

@[to_additive]
theorem lipschitz_with_lipschitz_const_mul :
    ∀ p q : β × β, dist (p.1 * p.2) (q.1 * q.2) ≤ LipschitzMul.C β * dist p q := by
  rw [← lipschitzWith_iff_dist_le_mul]
  -- ⊢ LipschitzWith (LipschitzMul.C β) fun p => p.fst * p.snd
  exact lipschitzWith_lipschitz_const_mul_edist
  -- 🎉 no goals
#align lipschitz_with_lipschitz_const_mul lipschitz_with_lipschitz_const_mul
#align lipschitz_with_lipschitz_const_add lipschitz_with_lipschitz_const_add

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) LipschitzMul.continuousMul : ContinuousMul β :=
  ⟨lipschitzWith_lipschitz_const_mul_edist.continuous⟩
#align has_lipschitz_mul.has_continuous_mul LipschitzMul.continuousMul
#align has_lipschitz_add.has_continuous_add LipschitzAdd.continuousAdd

@[to_additive]
instance Submonoid.lipschitzMul (s : Submonoid β) : LipschitzMul s where
  lipschitz_mul := ⟨LipschitzMul.C β, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    -- ⊢ edist ((fun p => p.fst * p.snd) (x₁, x₂)) ((fun p => p.fst * p.snd) (y₁, y₂) …
    convert lipschitzWith_lipschitz_const_mul_edist ⟨(x₁ : β), x₂⟩ ⟨y₁, y₂⟩ using 1⟩
    -- 🎉 no goals
#align submonoid.has_lipschitz_mul Submonoid.lipschitzMul
#align add_submonoid.has_lipschitz_add AddSubmonoid.lipschitzAdd

@[to_additive]
instance MulOpposite.lipschitzMul : LipschitzMul βᵐᵒᵖ where
  lipschitz_mul := ⟨LipschitzMul.C β, fun ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ =>
    (lipschitzWith_lipschitz_const_mul_edist ⟨x₂.unop, x₁.unop⟩ ⟨y₂.unop, y₁.unop⟩).trans_eq
      (congr_arg _ <| max_comm _ _)⟩
#align mul_opposite.has_lipschitz_mul MulOpposite.lipschitzMul
#align add_opposite.has_lipschitz_add AddOpposite.lipschitzAdd

-- this instance could be deduced from `NormedAddCommGroup.lipschitzAdd`, but we prove it
-- separately here so that it is available earlier in the hierarchy
instance Real.hasLipschitzAdd : LipschitzAdd ℝ where
  lipschitz_add := ⟨2, LipschitzWith.of_dist_le_mul <| fun p q => by
    simp only [Real.dist_eq, Prod.dist_eq, Prod.fst_sub, Prod.snd_sub, NNReal.coe_ofNat,
      add_sub_add_comm, two_mul]
    refine le_trans (abs_add (p.1 - q.1) (p.2 - q.2)) ?_
    -- ⊢ |p.fst - q.fst| + |p.snd - q.snd| ≤ max |p.fst - q.fst| |p.snd - q.snd| + ma …
    exact add_le_add (le_max_left _ _) (le_max_right _ _)⟩
    -- 🎉 no goals
#align real.has_lipschitz_add Real.hasLipschitzAdd

-- this instance has the same proof as `AddSubmonoid.lipschitzAdd`, but the former can't
-- directly be applied here since `ℝ≥0` is a subtype of `ℝ`, not an additive submonoid.
instance NNReal.hasLipschitzAdd : LipschitzAdd ℝ≥0 where
  lipschitz_add := ⟨LipschitzAdd.C ℝ, by
    rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩
    -- ⊢ edist ((fun p => p.fst + p.snd) (x₁, x₂)) ((fun p => p.fst + p.snd) (y₁, y₂) …
    exact lipschitzWith_lipschitz_const_add_edist ⟨(x₁ : ℝ), x₂⟩ ⟨y₁, y₂⟩⟩
    -- 🎉 no goals
#align nnreal.has_lipschitz_add NNReal.hasLipschitzAdd

end LipschitzMul

section BoundedSMul

variable [Zero α] [Zero β] [SMul α β]

/-- Mixin typeclass on a scalar action of a metric space `α` on a metric space `β` both with
distinguished points `0`, requiring compatibility of the action in the sense that
`dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂` and
`dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0`. -/
class BoundedSMul : Prop where
  dist_smul_pair' : ∀ x : α, ∀ y₁ y₂ : β, dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂
  dist_pair_smul' : ∀ x₁ x₂ : α, ∀ y : β, dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0
#align has_bounded_smul BoundedSMul

variable {α β}
variable [BoundedSMul α β]

theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂ :=
  BoundedSMul.dist_smul_pair' x y₁ y₂
#align dist_smul_pair dist_smul_pair

theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0 :=
  BoundedSMul.dist_pair_smul' x₁ x₂ y
#align dist_pair_smul dist_pair_smul

-- see Note [lower instance priority]
/-- The typeclass `BoundedSMul` on a metric-space scalar action implies continuity of the action. -/
instance (priority := 100) BoundedSMul.continuousSMul : ContinuousSMul α β where
  continuous_smul := by
    rw [Metric.continuous_iff]
    -- ⊢ ∀ (b : α × β) (ε : ℝ), ε > 0 → ∃ δ, δ > 0 ∧ ∀ (a : α × β), dist a b < δ → di …
    rintro ⟨a, b⟩ ε ε0
    -- ⊢ ∃ δ, δ > 0 ∧ ∀ (a_1 : α × β), dist a_1 (a, b) < δ → dist (a_1.fst • a_1.snd) …
    obtain ⟨δ, δ0, hδε⟩ : ∃ δ > 0, δ * (δ + dist b 0) + dist a 0 * δ < ε
    -- ⊢ ∃ δ, δ > 0 ∧ δ * (δ + dist b 0) + dist a 0 * δ < ε
    · have : Continuous fun δ ↦ δ * (δ + dist b 0) + dist a 0 * δ := by continuity
      -- ⊢ ∃ δ, δ > 0 ∧ δ * (δ + dist b 0) + dist a 0 * δ < ε
      refine ((this.tendsto' _ _ ?_).eventually (gt_mem_nhds ε0)).exists_gt
      -- ⊢ 0 * (0 + dist b 0) + dist a 0 * 0 = 0
      simp
      -- 🎉 no goals
    refine ⟨δ, δ0, fun (a', b') hab' => ?_⟩
    -- ⊢ dist ((a', b').fst • (a', b').snd) ((a, b).fst • (a, b).snd) < ε
    obtain ⟨ha, hb⟩ := max_lt_iff.1 hab'
    -- ⊢ dist ((a', b').fst • (a', b').snd) ((a, b).fst • (a, b).snd) < ε
    calc dist (a' • b') (a • b)
        ≤ dist (a' • b') (a • b') + dist (a • b') (a • b) := dist_triangle ..
      _ ≤ dist a' a * dist b' 0 + dist a 0 * dist b' b :=
        add_le_add (dist_pair_smul _ _ _) (dist_smul_pair _ _ _)
      _ ≤ δ * (δ + dist b 0) + dist a 0 * δ := by
          have : dist b' 0 ≤ δ + dist b 0 := (dist_triangle _ _ _).trans <| add_le_add_right hb.le _
          mono* <;> apply_rules [dist_nonneg, le_of_lt]
      _ < ε := hδε
#align has_bounded_smul.has_continuous_smul BoundedSMul.continuousSMul

-- this instance could be deduced from `NormedSpace.boundedSMul`, but we prove it separately
-- here so that it is available earlier in the hierarchy
instance Real.boundedSMul : BoundedSMul ℝ ℝ where
  dist_smul_pair' x y₁ y₂ := by simpa [Real.dist_eq, mul_sub] using (abs_mul x (y₁ - y₂)).le
                                -- 🎉 no goals
  dist_pair_smul' x₁ x₂ y := by simpa [Real.dist_eq, sub_mul] using (abs_mul (x₁ - x₂) y).le
                                -- 🎉 no goals
#align real.has_bounded_smul Real.boundedSMul

instance NNReal.boundedSMul : BoundedSMul ℝ≥0 ℝ≥0 where
  dist_smul_pair' x y₁ y₂ := by convert dist_smul_pair (x : ℝ) (y₁ : ℝ) y₂ using 1
                                -- 🎉 no goals
  dist_pair_smul' x₁ x₂ y := by convert dist_pair_smul (x₁ : ℝ) x₂ (y : ℝ) using 1
                                -- 🎉 no goals
#align nnreal.has_bounded_smul NNReal.boundedSMul

/-- If a scalar is central, then its right action is bounded when its left action is. -/
instance BoundedSMul.op [SMul αᵐᵒᵖ β] [IsCentralScalar α β] : BoundedSMul αᵐᵒᵖ β where
  dist_smul_pair' :=
    MulOpposite.rec' fun x y₁ y₂ => by simpa only [op_smul_eq_smul] using dist_smul_pair x y₁ y₂
                                       -- 🎉 no goals
  dist_pair_smul' :=
    MulOpposite.rec' fun x₁ =>
      MulOpposite.rec' fun x₂ y => by simpa only [op_smul_eq_smul] using dist_pair_smul x₁ x₂ y
                                      -- 🎉 no goals
#align has_bounded_smul.op BoundedSMul.op

end BoundedSMul

instance [Monoid α] [LipschitzMul α] : LipschitzAdd (Additive α) :=
  ⟨@LipschitzMul.lipschitz_mul α _ _ _⟩

instance [AddMonoid α] [LipschitzAdd α] : LipschitzMul (Multiplicative α) :=
  ⟨@LipschitzAdd.lipschitz_add α _ _ _⟩

@[to_additive]
instance [Monoid α] [LipschitzMul α] : LipschitzMul αᵒᵈ :=
  ‹LipschitzMul α›
