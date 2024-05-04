/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Rat
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.DilationEquiv
import Mathlib.Topology.Instances.NNReal.Defs

/-!
# Normed fields

In this file we continue building the theory of (semi)normed rings and fields.

Some useful results that relate the topology of the normed field to the discrete topology include:
* `discreteTopology_or_nontriviallyNormedField`
* `discreteTopology_of_bddAbove_range_norm`

-/

-- Guard against import creep.
assert_not_exists RestrictScalars

variable {α : Type*} {β : Type*} {ι : Type*}

open Filter Bornology
open scoped Topology NNReal Pointwise

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

theorem Filter.Tendsto.zero_mul_isBoundedUnder_le {f g : ι → α} {l : Filter ι}
    (hf : Tendsto f l (𝓝 0)) (hg : IsBoundedUnder (· ≤ ·) l ((‖·‖) ∘ g)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hf.op_zero_isBoundedUnder_le hg (· * ·) norm_mul_le

theorem Filter.isBoundedUnder_le_mul_tendsto_zero {f g : ι → α} {l : Filter ι}
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x * g x) l (𝓝 0) :=
  hg.op_zero_isBoundedUnder_le hf (flip (· * ·)) fun x y =>
    (norm_mul_le y x).trans_eq (mul_comm _ _)

/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedRing (π i)] : NonUnitalSeminormedRing (∀ i, π i) :=
  { Pi.seminormedAddCommGroup, Pi.nonUnitalRing with
    norm_mul := fun x y =>
      NNReal.coe_mono <|
        calc
          (Finset.univ.sup fun i => ‖x i * y i‖₊) ≤
              Finset.univ.sup ((fun i => ‖x i‖₊) * fun i => ‖y i‖₊) :=
            Finset.sup_mono_fun fun _ _ => norm_mul_le _ _
          _ ≤ (Finset.univ.sup fun i => ‖x i‖₊) * Finset.univ.sup fun i => ‖y i‖₊ :=
            Finset.sup_mul_le_mul_sup_of_nonneg (fun _ _ => zero_le _) fun _ _ => zero_le _
           }

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance Pi.seminormedRing {π : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (π i)] :
    SeminormedRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.ring with }

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance Pi.nonUnitalNormedRing {π : ι → Type*} [Fintype ι] [∀ i, NonUnitalNormedRing (π i)] :
    NonUnitalNormedRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
instance Pi.normedRing {π : ι → Type*} [Fintype ι] [∀ i, NormedRing (π i)] :
    NormedRing (∀ i, π i) :=
  { Pi.seminormedRing, Pi.normedAddCommGroup with }

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

/-- Non-unital seminormed commutative ring structure on the product of finitely many non-unital
seminormed commutative rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedCommRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedCommRing (π i)] : NonUnitalSeminormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/-- Normed commutative ring structure on the product of finitely many non-unital normed
commutative rings, using the sup norm. -/
instance Pi.nonUnitalNormedCommRing {π : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalNormedCommRing (π i)] : NonUnitalNormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

/-- Seminormed commutative ring structure on the product of finitely many seminormed commutative
rings, using the sup norm. -/
instance Pi.seminormedCommRing {π : ι → Type*} [Fintype ι] [∀ i, SeminormedCommRing (π i)] :
    SeminormedCommRing (∀ i, π i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

end SeminormedCommRing

section NormedCommRing

variable [NormedCommRing α]

/-- Normed commutative ring structure on the product of finitely many normed commutative rings,
using the sup norm. -/
instance Pi.normedCommutativeRing {π : ι → Type*} [Fintype ι] [∀ i, NormedCommRing (π i)] :
    NormedCommRing (∀ i, π i) :=
  { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

end NormedCommRing

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSeminormedRing.instContinuousMul [NonUnitalSeminormedRing α] :
    ContinuousMul α :=
  ⟨continuous_iff_continuousAt.2 fun x =>
      tendsto_iff_norm_sub_tendsto_zero.2 <| by
        have : ∀ e : α × α,
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ := by
          intro e
          calc
            ‖e.1 * e.2 - x.1 * x.2‖ ≤ ‖e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2‖ := by
              rw [mul_sub, sub_mul, sub_add_sub_cancel]
            _ ≤ ‖e.1‖ * ‖e.2 - x.2‖ + ‖e.1 - x.1‖ * ‖x.2‖ :=
              norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _)
        refine squeeze_zero (fun e => norm_nonneg _) this ?_
        convert
          ((continuous_fst.tendsto x).norm.mul
                ((continuous_snd.tendsto x).sub tendsto_const_nhds).norm).add
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _)
        -- Porting note: `show` used to select a goal to work on
        rotate_right
        · show Tendsto _ _ _
          exact tendsto_const_nhds
        · simp⟩

-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
instance (priority := 100) NonUnitalSeminormedRing.instIsTopologicalRing
    [NonUnitalSeminormedRing α] : IsTopologicalRing α where

namespace SeparationQuotient

instance [NonUnitalSeminormedRing α] : NonUnitalNormedRing (SeparationQuotient α) where
  __ : NonUnitalRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul := Quotient.ind₂ norm_mul_le

instance [NonUnitalSeminormedCommRing α] : NonUnitalNormedCommRing (SeparationQuotient α) where
  __ : NonUnitalCommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul := Quotient.ind₂ norm_mul_le

instance [SeminormedRing α] : NormedRing (SeparationQuotient α) where
  __ : Ring (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul := Quotient.ind₂ norm_mul_le

instance [SeminormedCommRing α] : NormedCommRing (SeparationQuotient α) where
  __ : CommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul := Quotient.ind₂ norm_mul_le

instance [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (SeparationQuotient α) where
  norm_one := norm_one (α := α)

end SeparationQuotient

section NormedDivisionRing

variable [NormedDivisionRing α] {a : α}

lemma antilipschitzWith_mul_left {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (a * ·) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by simp [dist_eq_norm, ← _root_.mul_sub, ha]

lemma antilipschitzWith_mul_right {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (· * a) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by
    simp [dist_eq_norm, ← _root_.sub_mul, ← mul_comm (‖a‖), ha]

/-- Multiplication by a nonzero element `a` on the left
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulLeft (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  toEquiv := Equiv.mulLeft₀ a ha
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩

/-- Multiplication by a nonzero element `a` on the right
as a `DilationEquiv` of a normed division ring. -/
@[simps!]
def DilationEquiv.mulRight (a : α) (ha : a ≠ 0) : α ≃ᵈ α where
  toEquiv := Equiv.mulRight₀ a ha
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩

namespace Filter

@[simp]
lemma comap_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    comap (a * ·) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma map_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    map (a * ·) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulLeft a ha)

@[simp]
lemma comap_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    comap (· * a) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (DilationEquiv.mulRight a ha)

@[simp]
lemma map_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    map (· * a) (cobounded α) = cobounded α :=
  DilationEquiv.map_cobounded (DilationEquiv.mulRight a ha)

/-- Multiplication on the left by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (a * ·) (cobounded α) (cobounded α) :=
  (map_mul_left_cobounded ha).le

/-- Multiplication on the right by a nonzero element of a normed division ring tends to infinity at
infinity. -/
theorem tendsto_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    Tendsto (· * a) (cobounded α) (cobounded α) :=
  (map_mul_right_cobounded ha).le

@[simp]
lemma inv_cobounded₀ : (cobounded α)⁻¹ = 𝓝[≠] 0 := by
  rw [← comap_norm_atTop, ← Filter.comap_inv, ← comap_norm_nhdsGT_zero, ← inv_atTop₀,
    ← Filter.comap_inv]
  simp only [comap_comap, Function.comp_def, norm_inv]

@[simp]
lemma inv_nhdsWithin_ne_zero : (𝓝[≠] (0 : α))⁻¹ = cobounded α := by
  rw [← inv_cobounded₀, inv_inv]

lemma tendsto_inv₀_cobounded' : Tendsto Inv.inv (cobounded α) (𝓝[≠] 0) :=
  inv_cobounded₀.le

theorem tendsto_inv₀_cobounded : Tendsto Inv.inv (cobounded α) (𝓝 0) :=
  tendsto_inv₀_cobounded'.mono_right inf_le_left

lemma tendsto_inv₀_nhdsWithin_ne_zero : Tendsto Inv.inv (𝓝[≠] 0) (cobounded α) :=
  inv_nhdsWithin_ne_zero.le

end Filter

-- see Note [lower instance priority]
instance (priority := 100) NormedDivisionRing.to_hasContinuousInv₀ : HasContinuousInv₀ α := by
  refine ⟨fun r r0 => tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have r0' : 0 < ‖r‖ := norm_pos_iff.2 r0
  rcases exists_between r0' with ⟨ε, ε0, εr⟩
  have : ∀ᶠ e in 𝓝 r, ‖e⁻¹ - r⁻¹‖ ≤ ‖r - e‖ / ‖r‖ / ε := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).eventually_mem εr] with e he
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he)
    calc
      ‖e⁻¹ - r⁻¹‖ = ‖r‖⁻¹ * ‖r - e‖ * ‖e‖⁻¹ := by
        rw [← norm_inv, ← norm_inv, ← norm_mul, ← norm_mul, mul_sub, sub_mul,
          mul_assoc _ e, inv_mul_cancel₀ r0, mul_inv_cancel₀ e0, one_mul, mul_one]
      _ = ‖r - e‖ / ‖r‖ / ‖e‖ := by field_simp [mul_comm]
      _ ≤ ‖r - e‖ / ‖r‖ / ε := by gcongr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) this ?_
  refine (((continuous_const.sub continuous_id).norm.div_const _).div_const _).tendsto' _ _ ?_
  simp

-- see Note [lower instance priority]
/-- A normed division ring is a topological division ring. -/
instance (priority := 100) NormedDivisionRing.to_topologicalDivisionRing :
    TopologicalDivisionRing α where

protected lemma IsOfFinOrder.norm_eq_one (ha : IsOfFinOrder a) : ‖a‖ = 1 :=
  ((normHom : α →*₀ ℝ).toMonoidHom.isOfFinOrder ha).eq_one <| norm_nonneg _

example [Monoid β] (φ : β →* α) {x : β} {k : ℕ+} (h : x ^ (k : ℕ) = 1) :
    ‖φ x‖ = 1 := (φ.isOfFinOrder <| isOfFinOrder_iff_pow_eq_one.2 ⟨_, k.2, h⟩).norm_eq_one

@[simp] lemma AddChar.norm_apply {G : Type*} [AddLeftCancelMonoid G] [Finite G] (ψ : AddChar G α)
    (x : G) : ‖ψ x‖ = 1 := (ψ.toMonoidHom.isOfFinOrder <| isOfFinOrder_of_finite _).norm_eq_one

lemma NormedField.tendsto_norm_inv_nhdsNE_zero_atTop : Tendsto (fun x : α ↦ ‖x⁻¹‖) (𝓝[≠] 0) atTop :=
  (tendsto_inv_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero).congr fun x ↦ (norm_inv x).symm

@[deprecated (since := "2024-12-22")]
alias NormedField.tendsto_norm_inverse_nhdsWithin_0_atTop :=
  NormedField.tendsto_norm_inv_nhdsNE_zero_atTop

lemma NormedField.tendsto_norm_zpow_nhdsNE_zero_atTop {m : ℤ} (hm : m < 0) :
    Tendsto (fun x : α ↦ ‖x ^ m‖) (𝓝[≠] 0) atTop := by
  obtain ⟨m, rfl⟩ := neg_surjective m
  rw [neg_lt_zero] at hm
  lift m to ℕ using hm.le
  rw [Int.natCast_pos] at hm
  simp only [norm_pow, zpow_neg, zpow_natCast, ← inv_pow]
  exact (tendsto_pow_atTop hm.ne').comp NormedField.tendsto_norm_inv_nhdsNE_zero_atTop

@[deprecated (since := "2024-12-22")]
alias NormedField.tendsto_norm_zpow_nhdsWithin_0_atTop :=
  NormedField.tendsto_norm_zpow_nhdsNE_zero_atTop

end NormedDivisionRing

namespace NormedField

/-- A normed field is either nontrivially normed or has a discrete topology.
In the discrete topology case, all the norms are 1, by `norm_eq_one_iff_ne_zero_of_discrete`.
The nontrivially normed field instance is provided by a subtype with a proof that the
forgetful inheritance to the existing `NormedField` instance is definitionally true.
This allows one to have the new `NontriviallyNormedField` instance without data clashes. -/
lemma discreteTopology_or_nontriviallyNormedField (𝕜 : Type*) [h : NormedField 𝕜] :
    DiscreteTopology 𝕜 ∨ Nonempty ({h' : NontriviallyNormedField 𝕜 // h'.toNormedField = h}) := by
  by_cases H : ∃ x : 𝕜, x ≠ 0 ∧ ‖x‖ ≠ 1
  · exact Or.inr ⟨(⟨NontriviallyNormedField.ofNormNeOne H, rfl⟩)⟩
  · simp_rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff, dist_eq_norm,
             sub_zero]
    refine Or.inl ⟨1, zero_lt_one, ?_⟩
    contrapose! H
    refine H.imp ?_
    -- contextual to reuse the `a ≠ 0` hypothesis in the proof of `a ≠ 0 ∧ ‖a‖ ≠ 1`
    simp (config := {contextual := true}) [add_comm, ne_of_lt]

lemma discreteTopology_of_bddAbove_range_norm {𝕜 : Type*} [NormedField 𝕜]
    (h : BddAbove (Set.range fun k : 𝕜 ↦ ‖k‖)) :
    DiscreteTopology 𝕜 := by
  refine (NormedField.discreteTopology_or_nontriviallyNormedField _).resolve_right ?_
  rintro ⟨_, rfl⟩
  obtain ⟨x, h⟩ := h
  obtain ⟨k, hk⟩ := NormedField.exists_lt_norm 𝕜 x
  exact hk.not_le (h (Set.mem_range_self k))

section Densely

variable (α) [DenselyNormedField α]

theorem denseRange_nnnorm : DenseRange (nnnorm : α → ℝ≥0) :=
  dense_of_exists_between fun _ _ hr =>
    let ⟨x, h⟩ := exists_lt_nnnorm_lt α hr
    ⟨‖x‖₊, ⟨x, rfl⟩, h⟩

end Densely

section NontriviallyNormedField
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℤ} {x : 𝕜}

@[simp]
protected lemma continuousAt_zpow : ContinuousAt (fun x ↦ x ^ n) x ↔ x ≠ 0 ∨ 0 ≤ n := by
  refine ⟨?_, continuousAt_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact not_tendsto_atTop_of_tendsto_nhds (hc.tendsto.mono_left nhdsWithin_le_nhds).norm
    (NormedField.tendsto_norm_zpow_nhdsNE_zero_atTop hm)

@[simp]
protected lemma continuousAt_inv : ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa using NormedField.continuousAt_zpow (n := -1) (x := x)

end NontriviallyNormedField
end NormedField

namespace NNReal

lemma lipschitzWith_sub : LipschitzWith 2 (fun (p : ℝ≥0 × ℝ≥0) ↦ p.1 - p.2) := by
  rw [← isometry_subtype_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : ℝ≥0 → ℝ) ((↑) : ℝ≥0 → ℝ)) :=
    isometry_subtype_coe.prod_map isometry_subtype_coe
  convert (((LipschitzWith.prod_fst.comp this.lipschitz).sub
    (LipschitzWith.prod_snd.comp this.lipschitz)).max_const 0)
  norm_num

end NNReal

instance Int.instNormedCommRing : NormedCommRing ℤ where
  __ := instCommRing
  __ := instNormedAddCommGroup
  norm_mul m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]

instance Int.instNormOneClass : NormOneClass ℤ :=
  ⟨by simp [← Int.norm_cast_real]⟩

instance Rat.instNormedField : NormedField ℚ where
  __ := instField
  __ := instNormedAddCommGroup
  norm_mul' a b := by simp only [norm, Rat.cast_mul, abs_mul]

instance Rat.instDenselyNormedField : DenselyNormedField ℚ where
  lt_norm_lt r₁ r₂ h₀ hr :=
    let ⟨q, h⟩ := exists_rat_btwn hr
    ⟨q, by rwa [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_pos (h₀.trans_lt h.1)]⟩

section Complete

lemma NormedField.completeSpace_iff_isComplete_closedBall {K : Type*} [NormedField K] :
    CompleteSpace K ↔ IsComplete (Metric.closedBall 0 1 : Set K) := by
  constructor <;> intro h
  · exact Metric.isClosed_closedBall.isComplete
  rcases NormedField.discreteTopology_or_nontriviallyNormedField K with _|⟨_, rfl⟩
  · rwa [completeSpace_iff_isComplete_univ,
         ← NormedDivisionRing.unitClosedBall_eq_univ_of_discrete]
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  obtain ⟨k, hk⟩ := hu.norm_bddAbove
  have kpos : 0 ≤ k := (_root_.norm_nonneg (u 0)).trans (hk (by simp))
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm K k
  have hu' : CauchySeq ((· / x) ∘ u) := (uniformContinuous_div_const' x).comp_cauchySeq hu
  have hb : ∀ n, ((· / x) ∘ u) n ∈ Metric.closedBall 0 1 := by
    intro
    simp only [Function.comp_apply, Metric.mem_closedBall, dist_zero_right, norm_div]
    rw [div_le_one (kpos.trans_lt hx)]
    exact hx.le.trans' (hk (by simp))
  obtain ⟨a, -, ha'⟩ := cauchySeq_tendsto_of_isComplete h hb hu'
  refine ⟨a * x, (((continuous_mul_right x).tendsto a).comp ha').congr ?_⟩
  have hx' : x ≠ 0 := by
    contrapose! hx
    simp [hx, kpos]
  simp [div_mul_cancel₀ _ hx']

end Complete
