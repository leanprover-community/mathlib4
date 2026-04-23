/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
module

public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Uniform
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Dilation
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Neighborhoods

/-!
# Normed rings

In this file we continue building the theory of (semi)normed rings.
-/

@[expose] public section

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

open Finset in
/-- Non-unital seminormed ring structure on the product of finitely many non-unital seminormed
rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedRing {R : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedRing (R i)] : NonUnitalSeminormedRing (∀ i, R i) :=
  { seminormedAddCommGroup, nonUnitalRing with
    norm_mul_le x y := NNReal.coe_mono <| calc
      (univ.sup fun i ↦ ‖x i * y i‖₊) ≤ univ.sup ((‖x ·‖₊) * (‖y ·‖₊)) :=
        sup_mono_fun fun _ _ ↦ nnnorm_mul_le _ _
      _ ≤ (univ.sup (‖x ·‖₊)) * univ.sup (‖y ·‖₊) :=
        sup_mul_le_mul_sup_of_nonneg (fun _ _ ↦ zero_le _) fun _ _ ↦ zero_le _ }

end NonUnitalSeminormedRing

section SeminormedRing

variable [SeminormedRing α]

/-- Seminormed ring structure on the product of finitely many seminormed rings,
  using the sup norm. -/
instance Pi.seminormedRing {R : ι → Type*} [Fintype ι] [∀ i, SeminormedRing (R i)] :
    SeminormedRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.ring with }

lemma RingHom.isometry {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ →+* 𝕜₂) [RingHomIsometric σ] :
    Isometry σ := AddMonoidHomClass.isometry_of_norm _ fun _ => RingHomIsometric.norm_map

/-- If `σ` and `σ'` are mutually inverse, then one is `RingHomIsometric` if the other is. Not an
instance, as it would cause loops. -/
lemma RingHomIsometric.inv {𝕜₁ 𝕜₂ : Type*} [SeminormedRing 𝕜₁] [SeminormedRing 𝕜₂]
    (σ : 𝕜₁ →+* 𝕜₂) {σ' : 𝕜₂ →+* 𝕜₁} [RingHomInvPair σ σ'] [RingHomIsometric σ] :
    RingHomIsometric σ' :=
  ⟨fun {x} ↦ by rw [← RingHomIsometric.norm_map (σ := σ), RingHomInvPair.comp_apply_eq₂]⟩

lemma tendsto_pow_cobounded_cobounded
    [NormOneClass α] [NormMulClass α] {m : ℕ} (hm : m ≠ 0) :
    Tendsto (· ^ m) (cobounded α) (cobounded α) := by
  simpa [← tendsto_norm_atTop_iff_cobounded] using
    (tendsto_pow_atTop hm).comp (tendsto_norm_cobounded_atTop (E := α))

end SeminormedRing

section NonUnitalNormedRing

variable [NonUnitalNormedRing α]

/-- Normed ring structure on the product of finitely many non-unital normed rings, using the sup
norm. -/
instance Pi.nonUnitalNormedRing {R : ι → Type*} [Fintype ι] [∀ i, NonUnitalNormedRing (R i)] :
    NonUnitalNormedRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.normedAddCommGroup with }

end NonUnitalNormedRing

section NormedRing

variable [NormedRing α]

/-- Normed ring structure on the product of finitely many normed rings, using the sup norm. -/
instance Pi.normedRing {R : ι → Type*} [Fintype ι] [∀ i, NormedRing (R i)] :
    NormedRing (∀ i, R i) :=
  { Pi.seminormedRing, Pi.normedAddCommGroup with }

end NormedRing

section NonUnitalSeminormedCommRing

variable [NonUnitalSeminormedCommRing α]

/-- Non-unital seminormed commutative ring structure on the product of finitely many non-unital
seminormed commutative rings, using the sup norm. -/
instance Pi.nonUnitalSeminormedCommRing {R : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalSeminormedCommRing (R i)] : NonUnitalSeminormedCommRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedRing, Pi.nonUnitalCommRing with }

end NonUnitalSeminormedCommRing

section NonUnitalNormedCommRing

variable [NonUnitalNormedCommRing α]

/-- Normed commutative ring structure on the product of finitely many non-unital normed
commutative rings, using the sup norm. -/
instance Pi.nonUnitalNormedCommRing {R : ι → Type*} [Fintype ι]
    [∀ i, NonUnitalNormedCommRing (R i)] : NonUnitalNormedCommRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.normedAddCommGroup with }

end NonUnitalNormedCommRing

section SeminormedCommRing

variable [SeminormedCommRing α]

/-- Seminormed commutative ring structure on the product of finitely many seminormed commutative
rings, using the sup norm. -/
instance Pi.seminormedCommRing {R : ι → Type*} [Fintype ι] [∀ i, SeminormedCommRing (R i)] :
    SeminormedCommRing (∀ i, R i) :=
  { Pi.nonUnitalSeminormedCommRing, Pi.ring with }

end SeminormedCommRing

section NormedCommRing

variable [NormedCommRing α]

/-- Normed commutative ring structure on the product of finitely many normed commutative rings,
using the sup norm. -/
instance Pi.normedCommutativeRing {R : ι → Type*} [Fintype ι] [∀ i, NormedCommRing (R i)] :
    NormedCommRing (∀ i, R i) :=
  { Pi.seminormedCommRing, Pi.normedAddCommGroup with }

end NormedCommRing

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalSeminormedRing.toContinuousMul [NonUnitalSeminormedRing α] :
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
            (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul tendsto_const_nhds)
        simp⟩

-- see Note [lower instance priority]
/-- A seminormed ring is a topological ring. -/
instance (priority := 100) NonUnitalSeminormedRing.toIsTopologicalRing [NonUnitalSeminormedRing α] :
    IsTopologicalRing α where

namespace SeparationQuotient

instance [NonUnitalSeminormedRing α] : NonUnitalNormedRing (SeparationQuotient α) where
  __ : NonUnitalRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

instance [NonUnitalSeminormedCommRing α] : NonUnitalNormedCommRing (SeparationQuotient α) where
  __ : NonUnitalCommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

instance [SeminormedRing α] : NormedRing (SeparationQuotient α) where
  __ : Ring (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

instance [SeminormedCommRing α] : NormedCommRing (SeparationQuotient α) where
  __ : CommRing (SeparationQuotient α) := inferInstance
  __ : NormedAddCommGroup (SeparationQuotient α) := inferInstance
  norm_mul_le := Quotient.ind₂ norm_mul_le

instance [SeminormedAddCommGroup α] [One α] [NormOneClass α] :
    NormOneClass (SeparationQuotient α) where
  norm_one := norm_one (α := α)

end SeparationQuotient

namespace NNReal

lemma lipschitzWith_sub : LipschitzWith 2 (fun (p : ℝ≥0 × ℝ≥0) ↦ p.1 - p.2) := by
  rw [← NNReal.isometry_coe.lipschitzWith_iff]
  have : Isometry (Prod.map ((↑) : ℝ≥0 → ℝ) ((↑) : ℝ≥0 → ℝ)) :=
    NNReal.isometry_coe.prodMap NNReal.isometry_coe
  convert (((LipschitzWith.prod_fst.comp this.lipschitz).sub
    (LipschitzWith.prod_snd.comp this.lipschitz)).max_const 0)
  norm_num

end NNReal

instance Int.instNormedCommRing : NormedCommRing ℤ where
  __ := instCommRing
  __ := instNormedAddCommGroup
  norm_mul_le m n := by simp only [norm, Int.cast_mul, abs_mul, le_rfl]

instance Int.instNormOneClass : NormOneClass ℤ :=
  ⟨by simp [← Int.norm_cast_real]⟩

instance Int.instNormMulClass : NormMulClass ℤ :=
  ⟨fun a b ↦ by simp [← Int.norm_cast_real, abs_mul]⟩

section NonUnitalNormedRing
variable [NonUnitalNormedRing α] [NormMulClass α] {a : α}

lemma antilipschitzWith_mul_left {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (a * ·) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by simp [dist_eq_norm, ← mul_sub, ha]

lemma antilipschitzWith_mul_right {a : α} (ha : a ≠ 0) : AntilipschitzWith (‖a‖₊⁻¹) (· * a) :=
  AntilipschitzWith.of_le_mul_dist fun _ _ ↦ by simp [dist_eq_norm, ← sub_mul, mul_comm, ha]

/-- Multiplication by a nonzero element `a` on the left, as a `Dilation` of a ring with a strictly
multiplicative norm. -/
@[simps!]
def Dilation.mulLeft (a : α) (ha : a ≠ 0) : α →ᵈ α where
  toFun b := a * b
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← mul_sub]⟩

/-- Multiplication by a nonzero element `a` on the right, as a `Dilation` of a ring with a strictly
multiplicative norm. -/
@[simps!]
def Dilation.mulRight (a : α) (ha : a ≠ 0) : α →ᵈ α where
  toFun b := b * a
  edist_eq' := ⟨‖a‖₊, nnnorm_ne_zero_iff.2 ha, fun x y ↦ by
    simp [edist_nndist, nndist_eq_nnnorm, ← sub_mul, ← mul_comm (‖a‖₊)]⟩

namespace Filter

@[simp]
lemma comap_mul_left_cobounded {a : α} (ha : a ≠ 0) :
    comap (a * ·) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (Dilation.mulLeft a ha)

@[simp]
lemma comap_mul_right_cobounded {a : α} (ha : a ≠ 0) :
    comap (· * a) (cobounded α) = cobounded α :=
  Dilation.comap_cobounded (Dilation.mulRight a ha)

end Filter

end NonUnitalNormedRing
