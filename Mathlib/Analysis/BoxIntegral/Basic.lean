/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.BoxIntegral.Partition.Filter
import Mathlib.Analysis.BoxIntegral.Partition.Measure
import Mathlib.Topology.UniformSpace.Compact

#align_import analysis.box_integral.basic from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

/-!
# Integrals of Riemann, Henstock-Kurzweil, and McShane

In this file we define the integral of a function over a box in `ℝⁿ`. The same definition works for
Riemann, Henstock-Kurzweil, and McShane integrals.

As usual, we represent `ℝⁿ` as the type of functions `ι → ℝ` for some finite type `ι`. A rectangular
box `(l, u]` in `ℝⁿ` is defined to be the set `{x : ι → ℝ | ∀ i, l i < x i ∧ x i ≤ u i}`, see
`BoxIntegral.Box`.

Let `vol` be a box-additive function on boxes in `ℝⁿ` with codomain `E →L[ℝ] F`. Given a function
`f : ℝⁿ → E`, a box `I` and a tagged partition `π` of this box, the *integral sum* of `f` over `π`
with respect to the volume `vol` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. Here
`π.tag J` is the point (tag) in `ℝⁿ` associated with the box `J`.

The integral is defined as the limit of integral sums along a filter. Different filters correspond
to different integration theories. In order to avoid code duplication, all our definitions and
theorems take an argument `l : BoxIntegral.IntegrationParams`. This is a type that holds three
boolean values, and encodes eight filters including those corresponding to Riemann,
Henstock-Kurzweil, and McShane integrals.

Following the design of infinite sums (see `hasSum` and `tsum`), we define a predicate
`BoxIntegral.HasIntegral` and a function `BoxIntegral.integral` that returns a vector satisfying
the predicate or zero if the function is not integrable.

Then we prove some basic properties of box integrals (linearity, a formula for the integral of a
constant). We also prove a version of the Henstock-Sacks inequality (see
`BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet` and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`), prove
integrability of continuous functions, and provide a criterion for integrability w.r.t. a
non-Riemann filter (e.g., Henstock-Kurzweil and McShane).

## Notation

- `ℝⁿ`: local notation for `ι → ℝ`

## Tags

integral
-/


open scoped BigOperators Classical Topology NNReal Filter Uniformity BoxIntegral

open Set Finset Function Filter Metric BoxIntegral.IntegrationParams

noncomputable section

namespace BoxIntegral

universe u v w

variable {ι : Type u} {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {I J : Box ι} {π : TaggedPrepartition I}

open TaggedPrepartition

local notation "ℝⁿ" => ι → ℝ

/-!
### Integral sum and its basic properties
-/


/-- The integral sum of `f : ℝⁿ → E` over a tagged prepartition `π` w.r.t. box-additive volume `vol`
with codomain `E →L[ℝ] F` is the sum of `vol J (f (π.tag J))` over all boxes of `π`. -/
def integralSum (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) : F :=
  ∑ J in π.boxes, vol J (f (π.tag J))
#align box_integral.integral_sum BoxIntegral.integralSum

theorem integralSum_biUnionTagged (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : Prepartition I)
    (πi : ∀ J, TaggedPrepartition J) :
    integralSum f vol (π.biUnionTagged πi) = ∑ J in π.boxes, integralSum f vol (πi J) := by
  refine (π.sum_biUnion_boxes _ _).trans <| sum_congr rfl fun J hJ => sum_congr rfl fun J' hJ' => ?_
  rw [π.tag_biUnionTagged hJ hJ']
#align box_integral.integral_sum_bUnion_tagged BoxIntegral.integralSum_biUnionTagged

theorem integralSum_biUnion_partition (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) (πi : ∀ J, Prepartition J) (hπi : ∀ J ∈ π, (πi J).IsPartition) :
    integralSum f vol (π.biUnionPrepartition πi) = integralSum f vol π := by
  refine' (π.sum_biUnion_boxes _ _).trans (sum_congr rfl fun J hJ => _)
  calc
    (∑ J' in (πi J).boxes, vol J' (f (π.tag <| π.toPrepartition.biUnionIndex πi J'))) =
        ∑ J' in (πi J).boxes, vol J' (f (π.tag J)) :=
      sum_congr rfl fun J' hJ' => by rw [Prepartition.biUnionIndex_of_mem _ hJ hJ']
    _ = vol J (f (π.tag J)) :=
      (vol.map ⟨⟨fun g : E →L[ℝ] F => g (f (π.tag J)), rfl⟩, fun _ _ => rfl⟩).sum_partition_boxes
        le_top (hπi J hJ)
#align box_integral.integral_sum_bUnion_partition BoxIntegral.integralSum_biUnion_partition

theorem integralSum_inf_partition (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I)
    {π' : Prepartition I} (h : π'.IsPartition) :
    integralSum f vol (π.infPrepartition π') = integralSum f vol π :=
  integralSum_biUnion_partition f vol π _ fun _J hJ => h.restrict (Prepartition.le_of_mem _ hJ)
#align box_integral.integral_sum_inf_partition BoxIntegral.integralSum_inf_partition

theorem integralSum_fiberwise {α} (g : Box ι → α) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    (π : TaggedPrepartition I) :
    (∑ y in π.boxes.image g, integralSum f vol (π.filter (g · = y))) = integralSum f vol π :=
  π.sum_fiberwise g fun J => vol J (f <| π.tag J)
#align box_integral.integral_sum_fiberwise BoxIntegral.integralSum_fiberwise

theorem integralSum_sub_partitions (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F)
    {π₁ π₂ : TaggedPrepartition I} (h₁ : π₁.IsPartition) (h₂ : π₂.IsPartition) :
    integralSum f vol π₁ - integralSum f vol π₂ =
      ∑ J in (π₁.toPrepartition ⊓ π₂.toPrepartition).boxes,
        (vol J (f <| (π₁.infPrepartition π₂.toPrepartition).tag J) -
          vol J (f <| (π₂.infPrepartition π₁.toPrepartition).tag J)) := by
  rw [← integralSum_inf_partition f vol π₁ h₂, ← integralSum_inf_partition f vol π₂ h₁,
    integralSum, integralSum, Finset.sum_sub_distrib]
  simp only [infPrepartition_toPrepartition, inf_comm]
#align box_integral.integral_sum_sub_partitions BoxIntegral.integralSum_sub_partitions

@[simp]
theorem integralSum_disjUnion (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) {π₁ π₂ : TaggedPrepartition I}
    (h : Disjoint π₁.iUnion π₂.iUnion) :
    integralSum f vol (π₁.disjUnion π₂ h) = integralSum f vol π₁ + integralSum f vol π₂ := by
  refine' (Prepartition.sum_disj_union_boxes h _).trans
      (congr_arg₂ (· + ·) (sum_congr rfl fun J hJ => _) (sum_congr rfl fun J hJ => _))
  · rw [disjUnion_tag_of_mem_left _ hJ]
  · rw [disjUnion_tag_of_mem_right _ hJ]
#align box_integral.integral_sum_disj_union BoxIntegral.integralSum_disjUnion

@[simp]
theorem integralSum_add (f g : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) :
    integralSum (f + g) vol π = integralSum f vol π + integralSum g vol π := by
  simp only [integralSum, Pi.add_apply, (vol _).map_add, Finset.sum_add_distrib]
#align box_integral.integral_sum_add BoxIntegral.integralSum_add

@[simp]
theorem integralSum_neg (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) :
    integralSum (-f) vol π = -integralSum f vol π := by
  simp only [integralSum, Pi.neg_apply, (vol _).map_neg, Finset.sum_neg_distrib]
#align box_integral.integral_sum_neg BoxIntegral.integralSum_neg

@[simp]
theorem integralSum_smul (c : ℝ) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (π : TaggedPrepartition I) :
    integralSum (c • f) vol π = c • integralSum f vol π := by
  simp only [integralSum, Finset.smul_sum, Pi.smul_apply, ContinuousLinearMap.map_smul]
#align box_integral.integral_sum_smul BoxIntegral.integralSum_smul

variable [Fintype ι]

/-!
### Basic integrability theory
-/


/-- The predicate `HasIntegral I l f vol y` says that `y` is the integral of `f` over `I` along `l`
w.r.t. volume `vol`. This means that integral sums of `f` tend to `𝓝 y` along
`BoxIntegral.IntegrationParams.toFilteriUnion I ⊤`. -/
def HasIntegral (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) (y : F) :
    Prop :=
  Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y)
#align box_integral.has_integral BoxIntegral.HasIntegral

/-- A function is integrable if there exists a vector that satisfies the `HasIntegral`
predicate. -/
def Integrable (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  ∃ y, HasIntegral I l f vol y
#align box_integral.integrable BoxIntegral.Integrable

/-- The integral of a function `f` over a box `I` along a filter `l` w.r.t. a volume `vol`.
Returns zero on non-integrable functions. -/
def integral (I : Box ι) (l : IntegrationParams) (f : ℝⁿ → E) (vol : ι →ᵇᵃ E →L[ℝ] F) :=
  if h : Integrable I l f vol then h.choose else 0
#align box_integral.integral BoxIntegral.integral

-- Porting note: using the above notation ℝⁿ here causes the theorem below to be silently ignored
-- see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Lean.204.20doesn't.20add.20lemma.20to.20the.20environment/near/363764522
-- and https://github.com/leanprover/lean4/issues/2257
variable {l : IntegrationParams} {f g : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F} {y y' : F}

/-- Reinterpret `BoxIntegral.HasIntegral` as `Filter.Tendsto`, e.g., dot-notation theorems
that are shadowed in the `BoxIntegral.HasIntegral` namespace. -/
theorem HasIntegral.tendsto (h : HasIntegral I l f vol y) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I ⊤) (𝓝 y) :=
  h
#align box_integral.has_integral.tendsto BoxIntegral.HasIntegral.tendsto

/-- The `ε`-`δ` definition of `BoxIntegral.HasIntegral`. -/
theorem hasIntegral_iff : HasIntegral I l f vol y ↔
    ∀ ε > (0 : ℝ), ∃ r : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ), (∀ c, l.RCond (r c)) ∧
      ∀ c π, l.MemBaseSet I c (r c) π → IsPartition π → dist (integralSum f vol π) y ≤ ε :=
  ((l.hasBasis_toFilteriUnion_top I).tendsto_iff nhds_basis_closedBall).trans <| by
    simp only [exists_and_right, mem_setOf_eq, mem_closedBall, and_imp, forall_exists_index,
      @forall_swap ℝ≥0 (TaggedPrepartition I)]
#align box_integral.has_integral_iff BoxIntegral.hasIntegral_iff

/-- Quite often it is more natural to prove an estimate of the form `a * ε`, not `ε` in the RHS of
`BoxIntegral.hasIntegral_iff`, so we provide this auxiliary lemma.  -/
theorem HasIntegral.of_mul (a : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ r : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ), (∀ c, l.RCond (r c)) ∧ ∀ c π,
      l.MemBaseSet I c (r c) π → IsPartition π → dist (integralSum f vol π) y ≤ a * ε) :
    HasIntegral I l f vol y := by
  refine' hasIntegral_iff.2 fun ε hε => _
  rcases exists_pos_mul_lt hε a with ⟨ε', hε', ha⟩
  rcases h ε' hε' with ⟨r, hr, H⟩
  exact ⟨r, hr, fun c π hπ hπp => (H c π hπ hπp).trans ha.le⟩
#align box_integral.has_integral_of_mul BoxIntegral.HasIntegral.of_mul

theorem integrable_iff_cauchy [CompleteSpace F] :
    Integrable I l f vol ↔ Cauchy ((l.toFilteriUnion I ⊤).map (integralSum f vol)) :=
  cauchy_map_iff_exists_tendsto.symm
#align box_integral.integrable_iff_cauchy BoxIntegral.integrable_iff_cauchy

/-- In a complete space, a function is integrable if and only if its integral sums form a Cauchy
net. Here we restate this fact in terms of `∀ ε > 0, ∃ r, ...`. -/
theorem integrable_iff_cauchy_basis [CompleteSpace F] : Integrable I l f vol ↔
    ∀ ε > (0 : ℝ), ∃ r : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ), (∀ c, l.RCond (r c)) ∧
      ∀ c₁ c₂ π₁ π₂, l.MemBaseSet I c₁ (r c₁) π₁ → π₁.IsPartition → l.MemBaseSet I c₂ (r c₂) π₂ →
        π₂.IsPartition → dist (integralSum f vol π₁) (integralSum f vol π₂) ≤ ε := by
  rw [integrable_iff_cauchy, cauchy_map_iff',
    (l.hasBasis_toFilteriUnion_top _).prod_self.tendsto_iff uniformity_basis_dist_le]
  refine' forall₂_congr fun ε _ => exists_congr fun r => _
  simp only [exists_prop, Prod.forall, Set.mem_iUnion, exists_imp, prod_mk_mem_set_prod_eq, and_imp,
    mem_inter_iff, mem_setOf_eq]
  exact
    and_congr Iff.rfl
      ⟨fun H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂ => H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂,
        fun H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂ => H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂⟩
#align box_integral.integrable_iff_cauchy_basis BoxIntegral.integrable_iff_cauchy_basis

theorem HasIntegral.mono {l₁ l₂ : IntegrationParams} (h : HasIntegral I l₁ f vol y) (hl : l₂ ≤ l₁) :
    HasIntegral I l₂ f vol y :=
  h.mono_left <| IntegrationParams.toFilteriUnion_mono _ hl _
#align box_integral.has_integral.mono BoxIntegral.HasIntegral.mono

protected theorem Integrable.hasIntegral (h : Integrable I l f vol) :
    HasIntegral I l f vol (integral I l f vol) := by
  rw [integral, dif_pos h]
  exact Classical.choose_spec h
#align box_integral.integrable.has_integral BoxIntegral.Integrable.hasIntegral

theorem Integrable.mono {l'} (h : Integrable I l f vol) (hle : l' ≤ l) : Integrable I l' f vol :=
  ⟨_, h.hasIntegral.mono hle⟩
#align box_integral.integrable.mono BoxIntegral.Integrable.mono

theorem HasIntegral.unique (h : HasIntegral I l f vol y) (h' : HasIntegral I l f vol y') : y = y' :=
  tendsto_nhds_unique h h'
#align box_integral.has_integral.unique BoxIntegral.HasIntegral.unique

theorem HasIntegral.integrable (h : HasIntegral I l f vol y) : Integrable I l f vol :=
  ⟨_, h⟩
#align box_integral.has_integral.integrable BoxIntegral.HasIntegral.integrable

theorem HasIntegral.integral_eq (h : HasIntegral I l f vol y) : integral I l f vol = y :=
  h.integrable.hasIntegral.unique h
#align box_integral.has_integral.integral_eq BoxIntegral.HasIntegral.integral_eq

nonrec theorem HasIntegral.add (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f + g) vol (y + y') := by
  simpa only [HasIntegral, ← integralSum_add] using h.add h'
#align box_integral.has_integral.add BoxIntegral.HasIntegral.add

theorem Integrable.add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    Integrable I l (f + g) vol :=
  (hf.hasIntegral.add hg.hasIntegral).integrable
#align box_integral.integrable.add BoxIntegral.Integrable.add

theorem integral_add (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    integral I l (f + g) vol = integral I l f vol + integral I l g vol :=
  (hf.hasIntegral.add hg.hasIntegral).integral_eq
#align box_integral.integral_add BoxIntegral.integral_add

nonrec theorem HasIntegral.neg (hf : HasIntegral I l f vol y) : HasIntegral I l (-f) vol (-y) := by
  simpa only [HasIntegral, ← integralSum_neg] using hf.neg
#align box_integral.has_integral.neg BoxIntegral.HasIntegral.neg

theorem Integrable.neg (hf : Integrable I l f vol) : Integrable I l (-f) vol :=
  hf.hasIntegral.neg.integrable
#align box_integral.integrable.neg BoxIntegral.Integrable.neg

theorem Integrable.of_neg (hf : Integrable I l (-f) vol) : Integrable I l f vol :=
  neg_neg f ▸ hf.neg
#align box_integral.integrable.of_neg BoxIntegral.Integrable.of_neg

@[simp]
theorem integrable_neg : Integrable I l (-f) vol ↔ Integrable I l f vol :=
  ⟨fun h => h.of_neg, fun h => h.neg⟩
#align box_integral.integrable_neg BoxIntegral.integrable_neg

@[simp]
theorem integral_neg : integral I l (-f) vol = -integral I l f vol :=
  if h : Integrable I l f vol then h.hasIntegral.neg.integral_eq
  else by rw [integral, integral, dif_neg h, dif_neg (mt Integrable.of_neg h), neg_zero]
#align box_integral.integral_neg BoxIntegral.integral_neg

theorem HasIntegral.sub (h : HasIntegral I l f vol y) (h' : HasIntegral I l g vol y') :
    HasIntegral I l (f - g) vol (y - y') := by simpa only [sub_eq_add_neg] using h.add h'.neg
#align box_integral.has_integral.sub BoxIntegral.HasIntegral.sub

theorem Integrable.sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    Integrable I l (f - g) vol :=
  (hf.hasIntegral.sub hg.hasIntegral).integrable
#align box_integral.integrable.sub BoxIntegral.Integrable.sub

theorem integral_sub (hf : Integrable I l f vol) (hg : Integrable I l g vol) :
    integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
  (hf.hasIntegral.sub hg.hasIntegral).integral_eq
#align box_integral.integral_sub BoxIntegral.integral_sub

theorem hasIntegral_const (c : E) : HasIntegral I l (fun _ => c) vol (vol I c) :=
  tendsto_const_nhds.congr' <| (l.eventually_isPartition I).mono fun _π hπ => Eq.symm <|
    (vol.map ⟨⟨fun g : E →L[ℝ] F ↦ g c, rfl⟩, fun _ _ ↦ rfl⟩).sum_partition_boxes le_top hπ
#align box_integral.has_integral_const BoxIntegral.hasIntegral_const

@[simp]
theorem integral_const (c : E) : integral I l (fun _ => c) vol = vol I c :=
  (hasIntegral_const c).integral_eq
#align box_integral.integral_const BoxIntegral.integral_const

theorem integrable_const (c : E) : Integrable I l (fun _ => c) vol :=
  ⟨_, hasIntegral_const c⟩
#align box_integral.integrable_const BoxIntegral.integrable_const

theorem hasIntegral_zero : HasIntegral I l (fun _ => (0 : E)) vol 0 := by
  simpa only [← (vol I).map_zero] using hasIntegral_const (0 : E)
#align box_integral.has_integral_zero BoxIntegral.hasIntegral_zero

theorem integrable_zero : Integrable I l (fun _ => (0 : E)) vol :=
  ⟨0, hasIntegral_zero⟩
#align box_integral.integrable_zero BoxIntegral.integrable_zero

theorem integral_zero : integral I l (fun _ => (0 : E)) vol = 0 :=
  hasIntegral_zero.integral_eq
#align box_integral.integral_zero BoxIntegral.integral_zero

theorem HasIntegral.sum {α : Type*} {s : Finset α} {f : α → ℝⁿ → E} {g : α → F}
    (h : ∀ i ∈ s, HasIntegral I l (f i) vol (g i)) :
    HasIntegral I l (fun x => ∑ i in s, f i x) vol (∑ i in s, g i) := by
  induction' s using Finset.induction_on with a s ha ihs; · simp [hasIntegral_zero]
  simp only [Finset.sum_insert ha]; rw [Finset.forall_mem_insert] at h
  exact h.1.add (ihs h.2)
#align box_integral.has_integral_sum BoxIntegral.HasIntegral.sum

theorem HasIntegral.smul (hf : HasIntegral I l f vol y) (c : ℝ) :
    HasIntegral I l (c • f) vol (c • y) := by
  simpa only [HasIntegral, ← integralSum_smul] using
    (tendsto_const_nhds : Tendsto _ _ (𝓝 c)).smul hf
#align box_integral.has_integral.smul BoxIntegral.HasIntegral.smul

theorem Integrable.smul (hf : Integrable I l f vol) (c : ℝ) : Integrable I l (c • f) vol :=
  (hf.hasIntegral.smul c).integrable
#align box_integral.integrable.smul BoxIntegral.Integrable.smul

theorem Integrable.of_smul {c : ℝ} (hf : Integrable I l (c • f) vol) (hc : c ≠ 0) :
    Integrable I l f vol := by
  simpa [inv_smul_smul₀ hc] using hf.smul c⁻¹
#align box_integral.integrable.of_smul BoxIntegral.Integrable.of_smul

@[simp]
theorem integral_smul (c : ℝ) : integral I l (fun x => c • f x) vol = c • integral I l f vol := by
  rcases eq_or_ne c 0 with (rfl | hc); · simp only [zero_smul, integral_zero]
  by_cases hf : Integrable I l f vol
  · exact (hf.hasIntegral.smul c).integral_eq
  · have : ¬Integrable I l (fun x => c • f x) vol := mt (fun h => h.of_smul hc) hf
    rw [integral, integral, dif_neg hf, dif_neg this, smul_zero]
#align box_integral.integral_smul BoxIntegral.integral_smul

open MeasureTheory

/-- The integral of a nonnegative function w.r.t. a volume generated by a locally-finite measure is
nonnegative. -/
theorem integral_nonneg {g : ℝⁿ → ℝ} (hg : ∀ x ∈ Box.Icc I, 0 ≤ g x) (μ : Measure ℝⁿ)
    [IsLocallyFiniteMeasure μ] : 0 ≤ integral I l g μ.toBoxAdditive.toSMul := by
  by_cases hgi : Integrable I l g μ.toBoxAdditive.toSMul
  · refine ge_of_tendsto' hgi.hasIntegral fun π => sum_nonneg fun J _ => ?_
    exact mul_nonneg ENNReal.toReal_nonneg (hg _ <| π.tag_mem_Icc _)
  · rw [integral, dif_neg hgi]
#align box_integral.integral_nonneg BoxIntegral.integral_nonneg

/-- If `‖f x‖ ≤ g x` on `[l, u]` and `g` is integrable, then the norm of the integral of `f` is less
than or equal to the integral of `g`. -/
theorem norm_integral_le_of_norm_le {g : ℝⁿ → ℝ} (hle : ∀ x ∈ Box.Icc I, ‖f x‖ ≤ g x)
    (μ : Measure ℝⁿ) [IsLocallyFiniteMeasure μ] (hg : Integrable I l g μ.toBoxAdditive.toSMul) :
    ‖(integral I l f μ.toBoxAdditive.toSMul : E)‖ ≤ integral I l g μ.toBoxAdditive.toSMul := by
  by_cases hfi : Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul
  · refine' le_of_tendsto_of_tendsto' hfi.hasIntegral.norm hg.hasIntegral fun π => _
    refine' norm_sum_le_of_le _ fun J _ => _
    simp only [BoxAdditiveMap.toSMul_apply, norm_smul, smul_eq_mul, Real.norm_eq_abs,
      μ.toBoxAdditive_apply, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hle _ <| π.tag_mem_Icc _) ENNReal.toReal_nonneg
  · rw [integral, dif_neg hfi, norm_zero]
    exact integral_nonneg (fun x hx => (norm_nonneg _).trans (hle x hx)) μ
#align box_integral.norm_integral_le_of_norm_le BoxIntegral.norm_integral_le_of_norm_le

theorem norm_integral_le_of_le_const {c : ℝ} (hc : ∀ x ∈ Box.Icc I, ‖f x‖ ≤ c) (μ : Measure ℝⁿ)
    [IsLocallyFiniteMeasure μ] : ‖(integral I l f μ.toBoxAdditive.toSMul : E)‖ ≤ (μ I).toReal * c :=
  by simpa only [integral_const] using norm_integral_le_of_norm_le hc μ (integrable_const c)
#align box_integral.norm_integral_le_of_le_const BoxIntegral.norm_integral_le_of_le_const

/-!
# Henstock-Sacks inequality and integrability on subboxes

Henstock-Sacks inequality for Henstock-Kurzweil integral says the following. Let `f` be a function
integrable on a box `I`; let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged partition of
`I` subordinate to `r`, the integral sum over this partition is `ε`-close to the integral. Then for
any tagged prepartition (i.e. a finite collections of pairwise disjoint subboxes of `I` with tagged
points) `π`, the integral sum over `π` differs from the integral of `f` over the part of `I` covered
by `π` by at most `ε`. The actual statement in the library is a bit more complicated to make it work
for any `BoxIntegral.IntegrationParams`. We formalize several versions of this inequality in
`BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet`,
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq`, and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet`.

Instead of using predicate assumptions on `r`, we define
`BoxIntegral.Integrable.convergenceR (h : integrable I l f vol) (ε : ℝ) (c : ℝ≥0) : ℝⁿ → (0, ∞)`
to be a function `r` such that

- if `l.bRiemann`, then `r` is a constant;
- if `ε > 0`, then for any tagged partition `π` of `I` subordinate to `r` (more precisely,
  satisfying the predicate `l.mem_base_set I c r`), the integral sum of `f` over `π` differs from
  the integral of `f` over `I` by at most `ε`.

The proof is mostly based on
[Russel A. Gordon, *The integrals of Lebesgue, Denjoy, Perron, and Henstock*][Gordon55].

-/

namespace Integrable

/-- If `ε > 0`, then `BoxIntegral.Integrable.convergenceR` is a function `r : ℝ≥0 → ℝⁿ → (0, ∞)`
such that for every `c : ℝ≥0`, for every tagged partition `π` subordinate to `r` (and satisfying
additional distortion estimates if `BoxIntegral.IntegrationParams.bDistortion l = true`), the
corresponding integral sum is `ε`-close to the integral.

If `BoxIntegral.IntegrationParams.bRiemann = true`, then `r c x` does not depend on `x`. If
`ε ≤ 0`, then we use `r c x = 1`.  -/
def convergenceR (h : Integrable I l f vol) (ε : ℝ) : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ) :=
  if hε : 0 < ε then (hasIntegral_iff.1 h.hasIntegral ε hε).choose
  else fun _ _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩
#align box_integral.integrable.convergence_r BoxIntegral.Integrable.convergenceR

variable {c c₁ c₂ : ℝ≥0} {ε ε₁ ε₂ : ℝ} {π₁ π₂ : TaggedPrepartition I}

theorem convergenceR_cond (h : Integrable I l f vol) (ε : ℝ) (c : ℝ≥0) :
    l.RCond (h.convergenceR ε c) := by
  rw [convergenceR]; split_ifs with h₀
  exacts [(hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.1 _, fun _ x => rfl]
#align box_integral.integrable.convergence_r_cond BoxIntegral.Integrable.convergenceR_cond

theorem dist_integralSum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h₀ : 0 < ε)
    (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) (hπp : π.IsPartition) :
    dist (integralSum f vol π) (integral I l f vol) ≤ ε := by
  rw [convergenceR, dif_pos h₀] at hπ
  exact (hasIntegral_iff.1 h.hasIntegral ε h₀).choose_spec.2 c _ hπ hπp
#align box_integral.integrable.dist_integral_sum_integral_le_of_mem_base_set BoxIntegral.Integrable.dist_integralSum_integral_le_of_memBaseSet

/-- **Henstock-Sacks inequality**. Let `r₁ r₂ : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `rₖ`, `k=1,2`, the integral sum of `f` over this partition differs
from the integral of `f` by at most `εₖ`. Then for any two tagged *prepartition* `π₁ π₂` subordinate
to `r₁` and `r₂` respectively and covering the same part of `I`, the integral sums of `f` over these
prepartitions differ from each other by at most `ε₁ + ε₂`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption on `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion.

See also `BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq` and
`BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet`.
-/
theorem dist_integralSum_le_of_memBaseSet (h : Integrable I l f vol) (hpos₁ : 0 < ε₁)
    (hpos₂ : 0 < ε₂) (h₁ : l.MemBaseSet I c₁ (h.convergenceR ε₁ c₁) π₁)
    (h₂ : l.MemBaseSet I c₂ (h.convergenceR ε₂ c₂) π₂) (HU : π₁.iUnion = π₂.iUnion) :
    dist (integralSum f vol π₁) (integralSum f vol π₂) ≤ ε₁ + ε₂ := by
  rcases h₁.exists_common_compl h₂ HU with ⟨π, hπU, hπc₁, hπc₂⟩
  set r : ℝⁿ → Ioi (0 : ℝ) := fun x => min (h.convergenceR ε₁ c₁ x) (h.convergenceR ε₂ c₂ x)
  have hr : l.RCond r := (h.convergenceR_cond _ c₁).min (h.convergenceR_cond _ c₂)
  set πr := π.toSubordinate r
  have H₁ :
    dist (integralSum f vol (π₁.unionComplToSubordinate π hπU r)) (integral I l f vol) ≤ ε₁ :=
    h.dist_integralSum_integral_le_of_memBaseSet hpos₁
      (h₁.unionComplToSubordinate (fun _ _ => min_le_left _ _) hπU hπc₁)
      (isPartition_unionComplToSubordinate _ _ _ _)
  rw [HU] at hπU
  have H₂ :
    dist (integralSum f vol (π₂.unionComplToSubordinate π hπU r)) (integral I l f vol) ≤ ε₂ :=
    h.dist_integralSum_integral_le_of_memBaseSet hpos₂
      (h₂.unionComplToSubordinate (fun _ _ => min_le_right _ _) hπU hπc₂)
      (isPartition_unionComplToSubordinate _ _ _ _)
  simpa [unionComplToSubordinate] using (dist_triangle_right _ _ _).trans (add_le_add H₁ H₂)
#align box_integral.integrable.dist_integral_sum_le_of_mem_base_set BoxIntegral.Integrable.dist_integralSum_le_of_memBaseSet

/-- If `f` is integrable on `I` along `l`, then for two sufficiently fine tagged prepartitions
(in the sense of the filter `BoxIntegral.IntegrationParams.toFilter l I`) such that they cover
the same part of `I`, the integral sums of `f` over `π₁` and `π₂` are very close to each other.  -/
theorem tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity (h : Integrable I l f vol) :
    Tendsto (fun π : TaggedPrepartition I × TaggedPrepartition I =>
      (integralSum f vol π.1, integralSum f vol π.2))
        ((l.toFilter I ×ˢ l.toFilter I) ⊓ 𝓟 {π | π.1.iUnion = π.2.iUnion}) (𝓤 F) := by
  refine (((l.hasBasis_toFilter I).prod_self.inf_principal _).tendsto_iff
    uniformity_basis_dist_le).2 fun ε ε0 => ?_
  replace ε0 := half_pos ε0
  use h.convergenceR (ε / 2), h.convergenceR_cond (ε / 2); rintro ⟨π₁, π₂⟩ ⟨⟨h₁, h₂⟩, hU⟩
  rw [← add_halves ε]
  exact h.dist_integralSum_le_of_memBaseSet ε0 ε0 h₁.choose_spec h₂.choose_spec hU
#align box_integral.integrable.tendsto_integral_sum_to_filter_prod_self_inf_Union_eq_uniformity BoxIntegral.Integrable.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity

/-- If `f` is integrable on a box `I` along `l`, then for any fixed subset `s` of `I` that can be
represented as a finite union of boxes, the integral sums of `f` over tagged prepartitions that
cover exactly `s` form a Cauchy “sequence” along `l`. -/
theorem cauchy_map_integralSum_toFilteriUnion (h : Integrable I l f vol) (π₀ : Prepartition I) :
    Cauchy ((l.toFilteriUnion I π₀).map (integralSum f vol)) := by
  refine' ⟨inferInstance, _⟩
  rw [prod_map_map_eq, ← toFilter_inf_iUnion_eq, ← prod_inf_prod, prod_principal_principal]
  exact h.tendsto_integralSum_toFilter_prod_self_inf_iUnion_eq_uniformity.mono_left
    (inf_le_inf_left _ <| principal_mono.2 fun π h => h.1.trans h.2.symm)
#align box_integral.integrable.cauchy_map_integral_sum_to_filter_Union BoxIntegral.Integrable.cauchy_map_integralSum_toFilteriUnion

variable [CompleteSpace F]

theorem to_subbox_aux (h : Integrable I l f vol) (hJ : J ≤ I) :
    ∃ y : F, HasIntegral J l f vol y ∧
      Tendsto (integralSum f vol) (l.toFilteriUnion I (Prepartition.single I J hJ)) (𝓝 y) := by
  refine (cauchy_map_iff_exists_tendsto.1
    (h.cauchy_map_integralSum_toFilteriUnion (.single I J hJ))).imp fun y hy ↦ ⟨?_, hy⟩
  convert hy.comp (l.tendsto_embedBox_toFilteriUnion_top hJ) -- faster than `exact` here
#align box_integral.integrable.to_subbox_aux BoxIntegral.Integrable.to_subbox_aux

/-- If `f` is integrable on a box `I`, then it is integrable on any subbox of `I`. -/
theorem to_subbox (h : Integrable I l f vol) (hJ : J ≤ I) : Integrable J l f vol :=
  (h.to_subbox_aux hJ).imp fun _ => And.left
#align box_integral.integrable.to_subbox BoxIntegral.Integrable.to_subbox

/-- If `f` is integrable on a box `I`, then integral sums of `f` over tagged prepartitions
that cover exactly a subbox `J ≤ I` tend to the integral of `f` over `J` along `l`. -/
theorem tendsto_integralSum_toFilteriUnion_single (h : Integrable I l f vol) (hJ : J ≤ I) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I (Prepartition.single I J hJ))
      (𝓝 <| integral J l f vol) :=
  let ⟨_y, h₁, h₂⟩ := h.to_subbox_aux hJ
  h₁.integral_eq.symm ▸ h₂
#align box_integral.integrable.tendsto_integral_sum_to_filter_Union_single BoxIntegral.Integrable.tendsto_integralSum_toFilteriUnion_single

/-- **Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partition differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordinate to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption on `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion;
- takes an extra argument `π₀ : prepartition I` and an assumption `π.Union = π₀.Union` instead of
  using `π.to_prepartition`.
-/
theorem dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq (h : Integrable I l f vol)
    (h0 : 0 < ε) (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) {π₀ : Prepartition I}
    (hU : π.iUnion = π₀.iUnion) :
    dist (integralSum f vol π) (∑ J in π₀.boxes, integral J l f vol) ≤ ε := by
  -- Let us prove that the distance is less than or equal to `ε + δ` for all positive `δ`.
  refine' le_of_forall_pos_le_add fun δ δ0 => _
  -- First we choose some constants.
  set δ' : ℝ := δ / (π₀.boxes.card + 1)
  have H0 : 0 < (π₀.boxes.card + 1 : ℝ) := Nat.cast_add_one_pos _
  have δ'0 : 0 < δ' := div_pos δ0 H0
  set C := max π₀.distortion π₀.compl.distortion
  /- Next we choose a tagged partition of each `J ∈ π₀` such that the integral sum of `f` over this
    partition is `δ'`-close to the integral of `f` over `J`. -/
  have : ∀ J ∈ π₀, ∃ πi : TaggedPrepartition J,
      πi.IsPartition ∧ dist (integralSum f vol πi) (integral J l f vol) ≤ δ' ∧
        l.MemBaseSet J C (h.convergenceR δ' C) πi := by
    intro J hJ
    have Hle : J ≤ I := π₀.le_of_mem hJ
    have HJi : Integrable J l f vol := h.to_subbox Hle
    set r := fun x => min (h.convergenceR δ' C x) (HJi.convergenceR δ' C x)
    have hJd : J.distortion ≤ C := le_trans (Finset.le_sup hJ) (le_max_left _ _)
    rcases l.exists_memBaseSet_isPartition J hJd r with ⟨πJ, hC, hp⟩
    have hC₁ : l.MemBaseSet J C (HJi.convergenceR δ' C) πJ := by
      refine' hC.mono J le_rfl le_rfl fun x _ => _; exact min_le_right _ _
    have hC₂ : l.MemBaseSet J C (h.convergenceR δ' C) πJ := by
      refine' hC.mono J le_rfl le_rfl fun x _ => _; exact min_le_left _ _
    exact ⟨πJ, hp, HJi.dist_integralSum_integral_le_of_memBaseSet δ'0 hC₁ hp, hC₂⟩
  /- Now we combine these tagged partitions into a tagged prepartition of `I` that covers the
    same part of `I` as `π₀` and apply `BoxIntegral.dist_integralSum_le_of_memBaseSet` to
    `π` and this prepartition. -/
  choose! πi hπip hπiδ' hπiC using this
  have : l.MemBaseSet I C (h.convergenceR δ' C) (π₀.biUnionTagged πi) :=
    biUnionTagged_memBaseSet hπiC hπip fun _ => le_max_right _ _
  have hU' : π.iUnion = (π₀.biUnionTagged πi).iUnion :=
    hU.trans (Prepartition.iUnion_biUnion_partition _ hπip).symm
  have := h.dist_integralSum_le_of_memBaseSet h0 δ'0 hπ this hU'
  rw [integralSum_biUnionTagged] at this
  calc
    dist (integralSum f vol π) (∑ J in π₀.boxes, integral J l f vol) ≤
        dist (integralSum f vol π) (∑ J in π₀.boxes, integralSum f vol (πi J)) +
          dist (∑ J in π₀.boxes, integralSum f vol (πi J)) (∑ J in π₀.boxes, integral J l f vol) :=
      dist_triangle _ _ _
    _ ≤ ε + δ' + ∑ _J in π₀.boxes, δ' := (add_le_add this (dist_sum_sum_le_of_le _ hπiδ'))
    _ = ε + δ := by field_simp; ring
#align box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq

/-- **Henstock-Sacks inequality**. Let `r : ℝⁿ → (0, ∞)` be a function such that for any tagged
*partition* of `I` subordinate to `r`, the integral sum of `f` over this partition differs from the
integral of `f` by at most `ε`. Then for any tagged *prepartition* `π` subordinate to `r`, the
integral sum of `f` over this prepartition differs from the integral of `f` over the part of `I`
covered by `π` by at most `ε`.

The actual statement

- uses `BoxIntegral.Integrable.convergenceR` instead of a predicate assumption on `r`;
- uses `BoxIntegral.IntegrationParams.MemBaseSet` instead of “subordinate to `r`” to
  account for additional requirements like being a Henstock partition or having a bounded
  distortion;
-/
theorem dist_integralSum_sum_integral_le_of_memBaseSet (h : Integrable I l f vol) (h0 : 0 < ε)
    (hπ : l.MemBaseSet I c (h.convergenceR ε c) π) :
    dist (integralSum f vol π) (∑ J in π.boxes, integral J l f vol) ≤ ε :=
  h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq h0 hπ rfl
#align box_integral.integrable.dist_integral_sum_sum_integral_le_of_mem_base_set BoxIntegral.Integrable.dist_integralSum_sum_integral_le_of_memBaseSet

/-- Integral sum of `f` over a tagged prepartition `π` such that `π.Union = π₀.Union` tends to the
sum of integrals of `f` over the boxes of `π₀`. -/
theorem tendsto_integralSum_sum_integral (h : Integrable I l f vol) (π₀ : Prepartition I) :
    Tendsto (integralSum f vol) (l.toFilteriUnion I π₀)
      (𝓝 <| ∑ J in π₀.boxes, integral J l f vol) := by
  refine' ((l.hasBasis_toFilteriUnion I π₀).tendsto_iff nhds_basis_closedBall).2 fun ε ε0 => _
  refine' ⟨h.convergenceR ε, h.convergenceR_cond ε, _⟩
  simp only [mem_inter_iff, Set.mem_iUnion, mem_setOf_eq]
  rintro π ⟨c, hc, hU⟩
  exact h.dist_integralSum_sum_integral_le_of_memBaseSet_of_iUnion_eq ε0 hc hU
#align box_integral.integrable.tendsto_integral_sum_sum_integral BoxIntegral.Integrable.tendsto_integralSum_sum_integral

/-- If `f` is integrable on `I`, then `λ J, integral J l f vol` is box-additive on subboxes of `I`:
if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, then the sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the boxes of `π₂`.

See also `BoxIntegral.Integrable.toBoxAdditive` for a bundled version. -/
theorem sum_integral_congr (h : Integrable I l f vol) {π₁ π₂ : Prepartition I}
    (hU : π₁.iUnion = π₂.iUnion) :
    ∑ J in π₁.boxes, integral J l f vol = ∑ J in π₂.boxes, integral J l f vol := by
  refine' tendsto_nhds_unique (h.tendsto_integralSum_sum_integral π₁) _
  rw [l.toFilteriUnion_congr _ hU]
  exact h.tendsto_integralSum_sum_integral π₂
#align box_integral.integrable.sum_integral_congr BoxIntegral.Integrable.sum_integral_congr

/-- If `f` is integrable on `I`, then `λ J, integral J l f vol` is box-additive on subboxes of `I`:
if `π₁`, `π₂` are two prepartitions of `I` covering the same part of `I`, then the sum of integrals
of `f` over the boxes of `π₁` is equal to the sum of integrals of `f` over the boxes of `π₂`.

See also `BoxIntegral.Integrable.sum_integral_congr` for an unbundled version. -/
@[simps]
def toBoxAdditive (h : Integrable I l f vol) : ι →ᵇᵃ[I] F where
  toFun J := integral J l f vol
  sum_partition_boxes' J hJ π hπ := by
    replace hπ := hπ.iUnion_eq; rw [← Prepartition.iUnion_top] at hπ
    rw [(h.to_subbox (WithTop.coe_le_coe.1 hJ)).sum_integral_congr hπ, Prepartition.top_boxes,
      sum_singleton]
#align box_integral.integrable.to_box_additive BoxIntegral.Integrable.toBoxAdditive

end Integrable

open MeasureTheory

/-!
### Integrability conditions
-/


variable (l)

/-- A continuous function is box-integrable with respect to any locally finite measure.

This is true for any volume with bounded variation. -/
theorem integrable_of_continuousOn [CompleteSpace E] {I : Box ι} {f : ℝⁿ → E}
    (hc : ContinuousOn f (Box.Icc I)) (μ : Measure ℝⁿ) [IsLocallyFiniteMeasure μ] :
    Integrable.{u, v, v} I l f μ.toBoxAdditive.toSMul := by
  have huc := I.isCompact_Icc.uniformContinuousOn_of_continuous hc
  rw [Metric.uniformContinuousOn_iff_le] at huc
  refine' integrable_iff_cauchy_basis.2 fun ε ε0 => _
  rcases exists_pos_mul_lt ε0 (μ.toBoxAdditive I) with ⟨ε', ε0', hε⟩
  rcases huc ε' ε0' with ⟨δ, δ0 : 0 < δ, Hδ⟩
  refine' ⟨fun _ _ => ⟨δ / 2, half_pos δ0⟩, fun _ _ _ => rfl, fun c₁ c₂ π₁ π₂ h₁ h₁p h₂ h₂p => _⟩
  simp only [dist_eq_norm, integralSum_sub_partitions _ _ h₁p h₂p, BoxAdditiveMap.toSMul_apply,
    ← smul_sub]
  have : ∀ J ∈ π₁.toPrepartition ⊓ π₂.toPrepartition,
      ‖μ.toBoxAdditive J • (f ((π₁.infPrepartition π₂.toPrepartition).tag J) -
        f ((π₂.infPrepartition π₁.toPrepartition).tag J))‖ ≤ μ.toBoxAdditive J * ε' := by
    intro J hJ
    have : 0 ≤ μ.toBoxAdditive J := ENNReal.toReal_nonneg
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg this, ← dist_eq_norm]
    refine' mul_le_mul_of_nonneg_left _ this
    refine' Hδ _ (TaggedPrepartition.tag_mem_Icc _ _) _ (TaggedPrepartition.tag_mem_Icc _ _) _
    rw [← add_halves δ]
    refine' (dist_triangle_left _ _ J.upper).trans (add_le_add (h₁.1 _ _ _) (h₂.1 _ _ _))
    · exact Prepartition.biUnionIndex_mem _ hJ
    · exact Box.le_iff_Icc.1 (Prepartition.le_biUnionIndex _ hJ) J.upper_mem_Icc
    · rw [_root_.inf_comm] at hJ
      exact Prepartition.biUnionIndex_mem _ hJ
    · rw [_root_.inf_comm] at hJ
      exact Box.le_iff_Icc.1 (Prepartition.le_biUnionIndex _ hJ) J.upper_mem_Icc
  refine' (norm_sum_le_of_le _ this).trans _
  rw [← Finset.sum_mul, μ.toBoxAdditive.sum_partition_boxes le_top (h₁p.inf h₂p)]
  exact hε.le
#align box_integral.integrable_of_continuous_on BoxIntegral.integrable_of_continuousOn

variable {l}

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

/-- This is an auxiliary lemma used to prove two statements at once. Use one of the next two
lemmas instead. -/
theorem HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (hl : l.bRiemann = false)
    (B : ι →ᵇᵃ[I] ℝ) (hB0 : ∀ J, 0 ≤ B J) (g : ι →ᵇᵃ[I] F) (s : Set ℝⁿ) (hs : s.Countable)
    (hlH : s.Nonempty → l.bHenstock = true)
    (H₁ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I ∩ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → x ∈ Box.Icc J →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε)
    (H₂ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I \ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → (l.bHenstock → x ∈ Box.Icc J) →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε * B J) :
    HasIntegral I l f vol (g I) := by
  /- We choose `r x` differently for `x ∈ s` and `x ∉ s`.

    For `x ∈ s`, we choose `εs` such that `∑' x : s, εs x < ε / 2 / 2 ^ #ι`, then choose `r x` so
    that `dist (vol J (f x)) (g J) ≤ εs x` for `J` in the `r x`-neighborhood of `x`. This guarantees
    that the sum of these distances over boxes `J` such that `π.tag J ∈ s` is less than `ε / 2`. We
    need an additional multiplier `2 ^ #ι` because different boxes can have the same tag.

    For `x ∉ s`, we choose `r x` so that `dist (vol (J (f x))) (g J) ≤ (ε / 2 / B I) * B J` for a
    box `J` in the `δ`-neighborhood of `x`. -/
  refine' ((l.hasBasis_toFilteriUnion_top _).tendsto_iff Metric.nhds_basis_closedBall).2 _
  intro ε ε0
  simp only [← exists_prop, gt_iff_lt, Subtype.exists'] at H₁ H₂
  choose! δ₁ Hδ₁ using H₁
  choose! δ₂ Hδ₂ using H₂
  have ε0' := half_pos ε0; have H0 : 0 < (2 : ℝ) ^ Fintype.card ι := pow_pos zero_lt_two _
  rcases hs.exists_pos_forall_sum_le (div_pos ε0' H0) with ⟨εs, hεs0, hεs⟩
  simp only [le_div_iff' H0, mul_sum] at hεs
  rcases exists_pos_mul_lt ε0' (B I) with ⟨ε', ε'0, hεI⟩
  set δ : ℝ≥0 → ℝⁿ → Ioi (0 : ℝ) := fun c x => if x ∈ s then δ₁ c x (εs x) else (δ₂ c) x ε'
  refine' ⟨δ, fun c => l.rCond_of_bRiemann_eq_false hl, _⟩
  simp only [Set.mem_iUnion, mem_inter_iff, mem_setOf_eq]
  rintro π ⟨c, hπδ, hπp⟩
  -- Now we split the sum into two parts based on whether `π.tag J` belongs to `s` or not.
  rw [← g.sum_partition_boxes le_rfl hπp, mem_closedBall, integralSum,
    ← sum_filter_add_sum_filter_not π.boxes fun J => π.tag J ∈ s,
    ← sum_filter_add_sum_filter_not π.boxes fun J => π.tag J ∈ s, ← add_halves ε]
  refine' dist_add_add_le_of_le _ _
  · rcases s.eq_empty_or_nonempty with (rfl | hsne); · simp [ε0'.le]
    /- For the boxes such that `π.tag J ∈ s`, we use the fact that at most `2 ^ #ι` boxes have the
        same tag. -/
    specialize hlH hsne
    have : ∀ J ∈ π.boxes.filter fun J => π.tag J ∈ s,
        dist (vol J (f <| π.tag J)) (g J) ≤ εs (π.tag J) := fun J hJ ↦ by
      rw [Finset.mem_filter] at hJ; cases' hJ with hJ hJs
      refine' Hδ₁ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ (hεs0 _) _ (π.le_of_mem' _ hJ) _
        (hπδ.2 hlH J hJ) fun hD => (Finset.le_sup hJ).trans (hπδ.3 hD)
      convert hπδ.1 J hJ using 3; exact (if_pos hJs).symm
    refine' (dist_sum_sum_le_of_le _ this).trans _
    rw [sum_comp]
    refine' (sum_le_sum _).trans (hεs _ _)
    · rintro b -
      rw [← Nat.cast_two, ← Nat.cast_pow, ← nsmul_eq_mul]
      refine' nsmul_le_nsmul (hεs0 _).le _
      refine' (Finset.card_le_of_subset _).trans ((hπδ.isHenstock hlH).card_filter_tag_eq_le b)
      exact filter_subset_filter _ (filter_subset _ _)
    · rw [Finset.coe_image, Set.image_subset_iff]
      exact fun J hJ => (Finset.mem_filter.1 hJ).2
  /- Now we deal with boxes such that `π.tag J ∉ s`.
    In this case the estimate is straightforward. -/
  -- porting note: avoided strange elaboration issues by rewriting using `calc`
  calc
    dist (∑ J in π.boxes.filter (¬tag π · ∈ s), vol J (f (tag π J)))
      (∑ J in π.boxes.filter (¬tag π · ∈ s), g J)
      ≤ ∑ J in π.boxes.filter (¬tag π · ∈ s), ε' * B J := dist_sum_sum_le_of_le _ fun J hJ ↦ by
      rw [Finset.mem_filter] at hJ; cases' hJ with hJ hJs
      refine' Hδ₂ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ ε'0 _ (π.le_of_mem' _ hJ) _ (fun hH => hπδ.2 hH J hJ)
        fun hD => (Finset.le_sup hJ).trans (hπδ.3 hD)
      convert hπδ.1 J hJ using 3; exact (if_neg hJs).symm
    _ ≤ ∑ J in π.boxes, ε' * B J := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦
      mul_nonneg ε'0.le (hB0 _)
    _ = B I * ε' := by rw [← mul_sum, B.sum_partition_boxes le_rfl hπp, mul_comm]
    _ ≤ ε / 2 := hεI.le
set_option linter.uppercaseLean3 false in
#align box_integral.has_integral_of_bRiemann_eq_ff_of_forall_is_o BoxIntegral.HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO

/-- A function `f` has Henstock (or `⊥`) integral over `I` is equal to the value of a box-additive
function `g` on `I` provided that `vol J (f x)` is sufficiently close to `g J` for sufficiently
small boxes `J ∋ x`. This lemma is useful to prove, e.g., to prove the Divergence theorem for
integral along `⊥`.

Let `l` be either `BoxIntegral.IntegrationParams.Henstock` or `⊥`. Let `g` a box-additive function
on subboxes of `I`. Suppose that there exists a nonnegative box-additive function `B` and a
countable set `s` with the following property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0` such that for any
box `J ≤ I` such that

- `x ∈ J.Icc ⊆ Metric.closedBall x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to `J` and `g J` is
less than or equal to `ε` if `x ∈ s` and is less than or equal to `ε * B J` otherwise.

Then `f` is integrable on `I` along `l` with integral `g I`. -/
theorem HasIntegral.of_le_Henstock_of_forall_isLittleO (hl : l ≤ Henstock) (B : ι →ᵇᵃ[I] ℝ)
    (hB0 : ∀ J, 0 ≤ B J) (g : ι →ᵇᵃ[I] F) (s : Set ℝⁿ) (hs : s.Countable)
    (H₁ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I ∩ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → x ∈ Box.Icc J →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε)
    (H₂ : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I \ s, ∀ ε > (0 : ℝ),
      ∃ δ > 0, ∀ J ≤ I, Box.Icc J ⊆ Metric.closedBall x δ → x ∈ Box.Icc J →
        (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε * B J) :
    HasIntegral I l f vol (g I) :=
  have A : l.bHenstock := Bool.eq_true_of_true_le hl.2.1
  HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (Bool.eq_false_of_le_false hl.1) B hB0 _ s hs
    (fun _ => A) H₁ <| by simpa only [A, true_imp_iff] using H₂
set_option linter.uppercaseLean3 false in
#align box_integral.has_integral_of_le_Henstock_of_forall_is_o BoxIntegral.HasIntegral.of_le_Henstock_of_forall_isLittleO

/-- Suppose that there exists a nonnegative box-additive function `B` with the following property.

For every `c : ℝ≥0`, a point `x ∈ I.Icc`, and a positive `ε` there exists `δ > 0` such that for any
box `J ≤ I` such that

- `J.Icc ⊆ Metric.closedBall x δ`;
- if `l.bDistortion` (i.e., `l = ⊥`), then the distortion of `J` is less than or equal to `c`,

the distance between the term `vol J (f x)` of an integral sum corresponding to `J` and `g J` is
less than or equal to `ε * B J`.

Then `f` is McShane integrable on `I` with integral `g I`. -/
theorem HasIntegral.mcShane_of_forall_isLittleO (B : ι →ᵇᵃ[I] ℝ) (hB0 : ∀ J, 0 ≤ B J)
    (g : ι →ᵇᵃ[I] F) (H : ∀ (c : ℝ≥0), ∀ x ∈ Box.Icc I, ∀ ε > (0 : ℝ), ∃ δ > 0, ∀ J ≤ I,
      Box.Icc J ⊆ Metric.closedBall x δ → dist (vol J (f x)) (g J) ≤ ε * B J) :
    HasIntegral I McShane f vol (g I) :=
  (HasIntegral.of_bRiemann_eq_false_of_forall_isLittleO (l := McShane) rfl B hB0 g ∅ countable_empty
      (fun ⟨_x, hx⟩ => hx.elim) fun c x hx => hx.2.elim) <| by
    simpa only [McShane, Bool.coe_sort_false, false_imp_iff, true_imp_iff, diff_empty] using H
set_option linter.uppercaseLean3 false in
#align box_integral.has_integral_McShane_of_forall_is_o BoxIntegral.HasIntegral.mcShane_of_forall_isLittleO

end BoxIntegral
