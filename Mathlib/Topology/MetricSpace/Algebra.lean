/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Algebra.SeparationQuotient.Basic
public import Mathlib.Topology.Algebra.UniformMulAction
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LiminfLimsup

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

@[expose] public section

open NNReal Filter Set
open scoped Topology Uniformity

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

variable [Monoid β]

/-- The Lipschitz constant of a monoid `β` satisfying `LipschitzMul` -/
@[to_additive /-- The Lipschitz constant of an `AddMonoid` `β` satisfying `LipschitzAdd` -/]
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
    refine le_trans (abs_add_le (p.1 - q.1) (p.2 - q.2)) ?_
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

variable {α β}
variable [IsBoundedSMul α β]

theorem dist_smul_pair (x : α) (y₁ y₂ : β) : dist (x • y₁) (x • y₂) ≤ dist x 0 * dist y₁ y₂ :=
  IsBoundedSMul.dist_smul_pair' x y₁ y₂

theorem dist_pair_smul (x₁ x₂ : α) (y : β) : dist (x₁ • y) (x₂ • y) ≤ dist x₁ x₂ * dist y 0 :=
  IsBoundedSMul.dist_pair_smul' x₁ x₂ y

theorem Bornology.IsBounded.uniformContinuousOn_smul {s : Set (α × β)} (hs : IsBounded s) :
    UniformContinuousOn (· • ·).uncurry s := by
  rcases hs.subset_ball_lt 0 0 with ⟨C, hC₀, hC⟩
  rw [Metric.uniformContinuousOn_iff_le]
  intro ε hε
  refine ⟨ε / (2 * C), by positivity, fun ⟨a, b⟩ hab ⟨x, y⟩ hxy h ↦ ?_⟩
  grw [hC, Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hab hxy
  rw [Prod.dist_eq, max_le_iff] at h
  dsimp at hab hxy h ⊢
  grw [dist_triangle _ (a • y), dist_pair_smul, dist_smul_pair, hab.1, hxy.2, h.2, h.1]
  field_simp
  norm_num1

-- see Note [lower instance priority]
/-- The typeclass `IsBoundedSMul` on a metric-space scalar action implies continuity of the
action. -/
instance (priority := 100) IsBoundedSMul.continuousSMul : ContinuousSMul α β where
  continuous_smul := by
    rw [continuous_iff_continuousAt]
    intro x
    refine Metric.isBounded_ball (x := 0) (r := dist x 0 + 1) |>.uniformContinuousOn_smul
      |>.continuousOn |>.continuousAt ?_
    exact Metric.isOpen_ball.mem_nhds (by simp)

instance (priority := 100) IsBoundedSMul.toUniformContinuousConstSMul :
    UniformContinuousConstSMul α β :=
  ⟨fun c => ((lipschitzWith_iff_dist_le_mul (K := nndist c 0)).2 fun _ _ =>
    dist_smul_pair c _ _).uniformContinuous⟩

@[to_fun]
theorem TendstoLocallyUniformlyOn.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformlyOn (F • G) (f • g) l s := by
  have H := hF.prodMk hG
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  rcases (hf x hx).sup (hg x hx) with ⟨C, hC⟩
  simp_rw [Filter.eventually_map, max_le_iff] at hC
  refine Tendsto.comp
    (Metric.isBounded_ball (x := (0 : α × β)) (r := C + 1)).uniformContinuousOn_smul
    (tendsto_inf.mpr ⟨H x hx, tendsto_principal.mpr ?_⟩)
  filter_upwards [hF x hx (Metric.dist_mem_uniformity one_pos),
    hG x hx (Metric.dist_mem_uniformity one_pos), tendsto_snd hC] with ⟨n, y⟩ hFn hGn hfg
  simp only [mem_prod, Metric.mem_ball, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, sup_lt_iff,
    mem_preimage, mem_setOf] at hFn hGn hfg ⊢
  grw [dist_triangle_left (F n y) 0 (f y), dist_triangle_left (G n y) 0 (g y)]
  constructor <;> constructor <;> linarith

@[to_fun]
theorem TendstoLocallyUniformlyOn.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {s : Set X} {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x ∈ s, (𝓝[s] x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformlyOn (F * G) (f * g) l s :=
  hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]
theorem TendstoLocallyUniformly.smul₀_of_isBoundedUnder {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformly (F • G) (f • g) l := by
  rw [← tendstoLocallyUniformlyOn_univ] at *
  apply hF.smul₀_of_isBoundedUnder hG <;> simpa

@[to_fun]
theorem TendstoLocallyUniformly.mul₀_of_isBoundedUnder {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (f y) 0))
    (hg : ∀ x, (𝓝 x).IsBoundedUnder (· ≤ ·) (fun y ↦ dist (g y) 0)) :
    TendstoLocallyUniformly (F * G) (f * g) l :=
  hF.smul₀_of_isBoundedUnder hG hf hg

@[to_fun]
theorem TendstoLocallyUniformlyOn.smul₀ {X ι : Type*} [TopologicalSpace X]
    {s : Set X} {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hfc : ContinuousOn f s) (hgc : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (F • G) (f • g) l s :=
  hF.smul₀_of_isBoundedUnder hG
    (fun x hx ↦ ((hfc x hx).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x hx ↦ ((hgc x hx).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]
theorem TendstoLocallyUniformlyOn.mul₀ {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {s : Set X} {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformlyOn F f l s) (hG : TendstoLocallyUniformlyOn G g l s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    TendstoLocallyUniformlyOn (F * G) (f * g) l s :=
  hF.smul₀ hG hf hg

@[to_fun]
theorem TendstoLocallyUniformly.smul₀ {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → α} {G : ι → X → β} {f : X → α} {g : X → β} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hfc : Continuous f) (hgc : Continuous g) :
    TendstoLocallyUniformly (F • G) (f • g) l :=
  hF.smul₀_of_isBoundedUnder hG
    (fun x ↦ ((hfc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)
    (fun x ↦ ((hgc.tendsto x).dist tendsto_const_nhds).isBoundedUnder_le)

@[to_fun]
theorem TendstoLocallyUniformly.mul₀ {X M ι : Type*} [TopologicalSpace X]
    [PseudoMetricSpace M] [Zero M] [Mul M] [IsBoundedSMul M M]
    {F : ι → X → M} {G : ι → X → M} {f : X → M} {g : X → M} {l : Filter ι}
    (hF : TendstoLocallyUniformly F f l) (hG : TendstoLocallyUniformly G g l)
    (hf : Continuous f) (hg : Continuous g) :
    TendstoLocallyUniformly (F * G) (f * g) l :=
  hF.smul₀ hG hf hg

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
