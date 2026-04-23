/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Order.Monoid.NatCast
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Disjoint
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Order.Interval.Set.OrderIso
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Bornology.Real
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.T5
import Mathlib.Topology.UrysohnsBounded

/-!
# Tietze extension theorem

In this file we prove a few version of the Tietze extension theorem. The theorem says that a
continuous function `s → ℝ` defined on a closed set in a normal topological space `Y` can be
extended to a continuous function on the whole space. Moreover, if all values of the original
function belong to some (finite or infinite, open or closed) interval, then the extension can be
chosen so that it takes values in the same interval. In particular, if the original function is a
bounded function, then there exists a bounded extension of the same norm.

The proof mostly follows <https://ncatlab.org/nlab/show/Tietze+extension+theorem>. We patch a small
gap in the proof for unbounded functions, see
`exists_extension_forall_exists_le_ge_of_isClosedEmbedding`.

In addition we provide a class `TietzeExtension` encoding the idea that a topological space
satisfies the Tietze extension theorem. This allows us to get a version of the Tietze extension
theorem that simultaneously applies to `ℝ`, `ℝ × ℝ`, `ℂ`, `ι → ℝ`, `ℝ≥0` et cetera. At some point
in the future, it may be desirable to provide instead a more general approach via
*absolute retracts*, but the current implementation covers the most common use cases easily.

## Implementation notes

We first prove the theorems for a closed embedding `e : X → Y` of a topological space into a normal
topological space, then specialize them to the case `X = s : Set Y`, `e = (↑)`.

## Tags

Tietze extension theorem, Urysohn's lemma, normal topological space
-/

@[expose] public section

open Topology

/-!  ### The `TietzeExtension` class -/

section TietzeExtensionClass

universe u u₁ u₂ v w

-- TODO: define *absolute retracts* and then prove they satisfy Tietze extension.
-- Then make instances of that instead and remove this class.
/-- A class encoding the concept that a space satisfies the Tietze extension property. -/
class TietzeExtension (Y : Type v) [TopologicalSpace Y] : Prop where
  exists_restrict_eq' {X : Type u} [TopologicalSpace X] [NormalSpace X] (s : Set X)
    (hs : IsClosed s) (f : C(s, Y)) : ∃ (g : C(X, Y)), g.restrict s = f

variable {X₁ : Type u₁} [TopologicalSpace X₁]
variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X}
variable {e : X₁ → X}
variable {Y : Type v} [TopologicalSpace Y] [TietzeExtension.{u, v} Y]

/-- **Tietze extension theorem** for `TietzeExtension` spaces, a version for a closed set. Let
`s` be a closed set in a normal topological space `X`. Let `f` be a continuous function
on `s` with values in a `TietzeExtension` space `Y`. Then there exists a continuous function
`g : C(X, Y)` such that `g.restrict s = f`. -/
theorem ContinuousMap.exists_restrict_eq (hs : IsClosed s) (f : C(s, Y)) :
    ∃ (g : C(X, Y)), g.restrict s = f :=
  TietzeExtension.exists_restrict_eq' s hs f

/-- **Tietze extension theorem** for `TietzeExtension` spaces. Let `e` be a closed embedding of a
nonempty topological space `X₁` into a normal topological space `X`. Let `f` be a continuous
function on `X₁` with values in a `TietzeExtension` space `Y`. Then there exists a
continuous function `g : C(X, Y)` such that `g ∘ e = f`. -/
theorem ContinuousMap.exists_extension (he : IsClosedEmbedding e) (f : C(X₁, Y)) :
    ∃ (g : C(X, Y)), g.comp ⟨e, he.continuous⟩ = f := by
  let e' : X₁ ≃ₜ Set.range e := he.isEmbedding.toHomeomorph
  obtain ⟨g, hg⟩ := (f.comp e'.symm).exists_restrict_eq he.isClosed_range
  exact ⟨g, by ext x; simpa using congr($(hg) ⟨e' x, x, rfl⟩)⟩

/-- **Tietze extension theorem** for `TietzeExtension` spaces. Let `e` be a closed embedding of a
nonempty topological space `X₁` into a normal topological space `X`. Let `f` be a continuous
function on `X₁` with values in a `TietzeExtension` space `Y`. Then there exists a
continuous function `g : C(X, Y)` such that `g ∘ e = f`.

This version is provided for convenience and backwards compatibility. Here the composition is
phrased in terms of bare functions. -/
theorem ContinuousMap.exists_extension' (he : IsClosedEmbedding e) (f : C(X₁, Y)) :
    ∃ (g : C(X, Y)), g ∘ e = f :=
  f.exists_extension he |>.imp fun g hg ↦ by ext x; congrm($(hg) x)

/-- This theorem is not intended to be used directly because it is rare for a set alone to
satisfy `[TietzeExtension t]`. For example, `Metric.ball` in `ℝ` only satisfies it when
the radius is strictly positive, so finding this as an instance will fail.

Instead, it is intended to be used as a constructor for theorems about sets which *do* satisfy
`[TietzeExtension t]` under some hypotheses. -/
theorem ContinuousMap.exists_forall_mem_restrict_eq (hs : IsClosed s)
    {Y : Type v} [TopologicalSpace Y] (f : C(s, Y))
    {t : Set Y} (hf : ∀ x, f x ∈ t) [ht : TietzeExtension.{u, v} t] :
    ∃ (g : C(X, Y)), (∀ x, g x ∈ t) ∧ g.restrict s = f := by
  obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf) |>.exists_restrict_eq hs
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

/-- This theorem is not intended to be used directly because it is rare for a set alone to
satisfy `[TietzeExtension t]`. For example, `Metric.ball` in `ℝ` only satisfies it when
the radius is strictly positive, so finding this as an instance will fail.

Instead, it is intended to be used as a constructor for theorems about sets which *do* satisfy
`[TietzeExtension t]` under some hypotheses. -/
theorem ContinuousMap.exists_extension_forall_mem (he : IsClosedEmbedding e)
    {Y : Type v} [TopologicalSpace Y] (f : C(X₁, Y))
    {t : Set Y} (hf : ∀ x, f x ∈ t) [ht : TietzeExtension.{u, v} t] :
    ∃ (g : C(X, Y)), (∀ x, g x ∈ t) ∧ g.comp ⟨e, he.continuous⟩ = f := by
  obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf) |>.exists_extension he
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

instance Pi.instTietzeExtension {ι : Type*} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    [∀ i, TietzeExtension.{u} (Y i)] : TietzeExtension.{u} (∀ i, Y i) where
  exists_restrict_eq' s hs f := by
    obtain ⟨g', hg'⟩ := Classical.skolem.mp <| fun i ↦
      ContinuousMap.exists_restrict_eq hs (ContinuousMap.piEquiv _ _ |>.symm f i)
    exact ⟨ContinuousMap.piEquiv _ _ g', by ext x i; congrm($(hg' i) x)⟩

instance Prod.instTietzeExtension {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TietzeExtension.{u, v} Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] :
    TietzeExtension.{u, max w v} (Y × Z) where
  exists_restrict_eq' s hs f := by
    obtain ⟨g₁, hg₁⟩ := (ContinuousMap.fst.comp f).exists_restrict_eq hs
    obtain ⟨g₂, hg₂⟩ := (ContinuousMap.snd.comp f).exists_restrict_eq hs
    exact ⟨g₁.prodMk g₂, by ext1 x; congrm(($(hg₁) x), $(hg₂) x)⟩

instance Unique.instTietzeExtension {Y : Type v} [TopologicalSpace Y]
    [Nonempty Y] [Subsingleton Y] : TietzeExtension.{u, v} Y where
  exists_restrict_eq' _ _ f := ‹Nonempty Y›.elim fun y ↦ ⟨.const _ y, by ext; subsingleton⟩

/-- Any retract of a `TietzeExtension` space is one itself. -/
theorem TietzeExtension.of_retract {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (ι : C(Y, Z)) (r : C(Z, Y))
    (h : r.comp ι = .id Y) : TietzeExtension.{u, v} Y where
  exists_restrict_eq' s hs f := by
    obtain ⟨g, hg⟩ := (ι.comp f).exists_restrict_eq hs
    use r.comp g
    ext1 x
    have := congr(r.comp $(hg))
    rw [← r.comp_assoc ι, h, f.id_comp] at this
    congrm($this x)

/-- Any homeomorphism from a `TietzeExtension` space is one itself. -/
theorem TietzeExtension.of_homeo {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y ≃ₜ Z) :
    TietzeExtension.{u, v} Y :=
  .of_retract (e : C(Y, Z)) (e.symm : C(Z, Y)) <| by simp

end TietzeExtensionClass

/-! The Tietze extension theorem for `ℝ`. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]

open Metric Set Filter

open BoundedContinuousFunction Topology

noncomputable section

namespace BoundedContinuousFunction

/-- One step in the proof of the Tietze extension theorem. If `e : C(X, Y)` is a closed embedding
of a topological space into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous
function, then there exists a bounded continuous function `g : Y →ᵇ ℝ` of the norm `‖g‖ ≤ ‖f‖ / 3`
such that the distance between `g ∘ e` and `f` is at most `(2 / 3) * ‖f‖`. -/
theorem tietze_extension_step (f : X →ᵇ ℝ) (e : C(X, Y)) (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (g.compContinuous e) f ≤ 2 / 3 * ‖f‖ := by
  have h3 : (0 : ℝ) < 3 := by norm_num1
  have h23 : 0 < (2 / 3 : ℝ) := by norm_num1
  -- In the trivial case `f = 0`, we take `g = 0`
  rcases eq_or_ne f 0 with (rfl | hf)
  · simp
  replace hf : 0 < ‖f‖ := norm_pos_iff.2 hf
  /- Otherwise, the closed sets `e '' (f ⁻¹' (Iic (-‖f‖ / 3)))` and `e '' (f ⁻¹' (Ici (‖f‖ / 3)))`
    are disjoint, hence by Urysohn's lemma there exists a function `g` that is equal to `-‖f‖ / 3`
    on the former set and is equal to `‖f‖ / 3` on the latter set. This function `g` satisfies the
    assertions of the lemma. -/
  have hf3 : -‖f‖ / 3 < ‖f‖ / 3 := (div_lt_div_iff_of_pos_right h3).2 (Left.neg_lt_self hf)
  have hc₁ : IsClosed (e '' (f ⁻¹' Iic (-‖f‖ / 3))) :=
    he.isClosedMap _ (isClosed_Iic.preimage f.continuous)
  have hc₂ : IsClosed (e '' (f ⁻¹' Ici (‖f‖ / 3))) :=
    he.isClosedMap _ (isClosed_Ici.preimage f.continuous)
  have hd : Disjoint (e '' (f ⁻¹' Iic (-‖f‖ / 3))) (e '' (f ⁻¹' Ici (‖f‖ / 3))) := by
    refine disjoint_image_of_injective he.injective (Disjoint.preimage _ ?_)
    rwa [Iic_disjoint_Ici, not_le]
  rcases exists_bounded_mem_Icc_of_closed_of_le hc₁ hc₂ hd hf3.le with ⟨g, hg₁, hg₂, hgf⟩
  refine ⟨g, ?_, ?_⟩
  · refine (norm_le <| div_nonneg hf.le h3.le).mpr fun y => ?_
    simpa [abs_le, neg_div] using hgf y
  · refine (dist_le <| mul_nonneg h23.le hf.le).mpr fun x => ?_
    have hfx : -‖f‖ ≤ f x ∧ f x ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x
    rcases le_total (f x) (-‖f‖ / 3) with hle₁ | hle₁
    · calc
        |g (e x) - f x| = -‖f‖ / 3 - f x := by
          rw [hg₁ (mem_image_of_mem _ hle₁), Function.const_apply,
            abs_of_nonneg (sub_nonneg.2 hle₁)]
        _ ≤ 2 / 3 * ‖f‖ := by linarith
    · rcases le_total (f x) (‖f‖ / 3) with hle₂ | hle₂
      · simp only [neg_div] at *
        calc
          dist (g (e x)) (f x) ≤ |g (e x)| + |f x| := dist_le_norm_add_norm _ _
          _ ≤ ‖f‖ / 3 + ‖f‖ / 3 := (add_le_add (abs_le.2 <| hgf _) (abs_le.2 ⟨hle₁, hle₂⟩))
          _ = 2 / 3 * ‖f‖ := by linarith
      · calc
          |g (e x) - f x| = f x - ‖f‖ / 3 := by
            rw [hg₂ (mem_image_of_mem _ hle₂), abs_sub_comm, Function.const_apply,
              abs_of_nonneg (sub_nonneg.2 hle₂)]
          _ ≤ 2 / 3 * ‖f‖ := by linarith

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
theorem exists_extension_norm_eq_of_isClosedEmbedding' (f : X →ᵇ ℝ) (e : C(X, Y))
    (he : IsClosedEmbedding e) : ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g.compContinuous e = f := by
  /- For the proof, we iterate `tietze_extension_step`. Each time we apply it to the difference
    between the previous approximation and `f`. -/
  choose F hF_norm hF_dist using fun f : X →ᵇ ℝ => tietze_extension_step f e he
  set g : ℕ → Y →ᵇ ℝ := fun n => (fun g => g + F (f - g.compContinuous e))^[n] 0
  have g0 : g 0 = 0 := rfl
  have g_succ : ∀ n, g (n + 1) = g n + F (f - (g n).compContinuous e) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hgf : ∀ n, dist ((g n).compContinuous e) f ≤ (2 / 3) ^ n * ‖f‖ := by
    intro n
    induction n with
    | zero => simp [g0]
    | succ n ihn =>
      rw [g_succ n, add_compContinuous, ← dist_sub_right, add_sub_cancel_left, pow_succ', mul_assoc]
      refine (hF_dist _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num1))
      rwa [← dist_eq_norm']
  have hg_dist : ∀ n, dist (g n) (g (n + 1)) ≤ 1 / 3 * ‖f‖ * (2 / 3) ^ n := by
    intro n
    calc
      dist (g n) (g (n + 1)) = ‖F (f - (g n).compContinuous e)‖ := by
        rw [g_succ, dist_eq_norm', add_sub_cancel_left]
      _ ≤ ‖f - (g n).compContinuous e‖ / 3 := hF_norm _
      _ = 1 / 3 * dist ((g n).compContinuous e) f := by rw [dist_eq_norm', one_div, div_eq_inv_mul]
      _ ≤ 1 / 3 * ((2 / 3) ^ n * ‖f‖) := mul_le_mul_of_nonneg_left (hgf n) (by norm_num1)
      _ = 1 / 3 * ‖f‖ * (2 / 3) ^ n := by ac_rfl
  have hg_cau : CauchySeq g := cauchySeq_of_le_geometric _ _ (by norm_num1) hg_dist
  have :
    Tendsto (fun n => (g n).compContinuous e) atTop
      (𝓝 <| (limUnder atTop g).compContinuous e) :=
    ((continuous_compContinuous e).tendsto _).comp hg_cau.tendsto_limUnder
  have hge : (limUnder atTop g).compContinuous e = f := by
    refine tendsto_nhds_unique this (tendsto_iff_dist_tendsto_zero.2 ?_)
    refine squeeze_zero (fun _ => dist_nonneg) hgf ?_
    rw [← zero_mul ‖f‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num1
  refine ⟨limUnder atTop g, le_antisymm ?_ ?_, hge⟩
  · rw [← dist_zero_left, ← g0]
    refine
      (dist_le_of_le_geometric_of_tendsto₀ _ _ (by norm_num1)
        hg_dist hg_cau.tendsto_limUnder).trans_eq ?_
    ring
  · rw [← hge]
    exact norm_compContinuous_le _ _

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and unbundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
theorem exists_extension_norm_eq_of_isClosedEmbedding (f : X →ᵇ ℝ) {e : X → Y}
    (he : IsClosedEmbedding e) : ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_isClosedEmbedding' f ⟨e, he.continuous⟩ he with ⟨g, hg, rfl⟩
  exact ⟨g, hg, rfl⟩

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. If `f` is a bounded continuous real-valued function defined on a closed set in a normal
topological space, then it can be extended to a bounded continuous function of the same norm defined
on the whole space. -/
theorem exists_norm_eq_restrict_eq_of_closed {s : Set Y} (f : s →ᵇ ℝ) (hs : IsClosed s) :
    ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g.restrict s = f :=
  exists_extension_norm_eq_of_isClosedEmbedding' f ((ContinuousMap.id _).restrict s)
    hs.isClosedEmbedding_subtypeVal

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding and a bounded continuous function that takes values in a non-trivial closed interval.
See also `exists_extension_forall_mem_of_isClosedEmbedding` for a more general statement that works
for any interval (finite or infinite, open or closed).

If `e : X → Y` is a closed embedding and `f : X →ᵇ ℝ` is a bounded continuous function such that
`f x ∈ [a, b]` for all `x`, where `a ≤ b`, then there exists a bounded continuous function
`g : Y →ᵇ ℝ` such that `g y ∈ [a, b]` for all `y` and `g ∘ e = f`. -/
theorem exists_extension_forall_mem_Icc_of_isClosedEmbedding (f : X →ᵇ ℝ) {a b : ℝ} {e : X → Y}
    (hf : ∀ x, f x ∈ Icc a b) (hle : a ≤ b) (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ Icc a b) ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_isClosedEmbedding (f - const X ((a + b) / 2)) he with
    ⟨g, hgf, hge⟩
  refine ⟨const Y ((a + b) / 2) + g, fun y => ?_, ?_⟩
  · suffices ‖f - const X ((a + b) / 2)‖ ≤ (b - a) / 2 by
      simpa [Real.Icc_eq_closedBall, add_mem_closedBall_iff_norm] using
        (norm_coe_le_norm g y).trans (hgf.trans_le this)
    refine (norm_le <| div_nonneg (sub_nonneg.2 hle) zero_le_two).2 fun x => ?_
    simpa only [Real.Icc_eq_closedBall] using hf x
  · ext x
    have : g (e x) = f x - (a + b) / 2 := congr_fun hge x
    simp [this]

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Then there
exists a bounded continuous function `g : Y →ᵇ ℝ` such that `g ∘ e = f` and each value `g y` belongs
to a closed interval `[f x₁, f x₂]` for some `x₁` and `x₂`. -/
theorem exists_extension_forall_exists_le_ge_of_isClosedEmbedding [Nonempty X] (f : X →ᵇ ℝ)
    {e : X → Y} (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x₁ x₂, g y ∈ Icc (f x₁) (f x₂)) ∧ g ∘ e = f := by
  inhabit X
  -- Put `a = ⨅ x, f x` and `b = ⨆ x, f x`
  obtain ⟨a, ha⟩ : ∃ a, IsGLB (range f) a := ⟨_, isGLB_ciInf f.isBounded_range.bddBelow⟩
  obtain ⟨b, hb⟩ : ∃ b, IsLUB (range f) b := ⟨_, isLUB_ciSup f.isBounded_range.bddAbove⟩
  -- Then `f x ∈ [a, b]` for all `x`
  have hmem : ∀ x, f x ∈ Icc a b := fun x => ⟨ha.1 ⟨x, rfl⟩, hb.1 ⟨x, rfl⟩⟩
  -- Rule out the trivial case `a = b`
  have hle : a ≤ b := (hmem default).1.trans (hmem default).2
  rcases hle.eq_or_lt with (rfl | hlt)
  · have : ∀ x, f x = a := by simpa using hmem
    use const Y a
    simp [this, funext_iff]
  -- Put `c = (a + b) / 2`. Then `a < c < b` and `c - a = b - c`.
  set c := (a + b) / 2
  have hac : a < c := left_lt_add_div_two.2 hlt
  have hcb : c < b := add_div_two_lt_right.2 hlt
  have hsub : c - a = b - c := by
    simp [c]
    ring
  /- Due to `exists_extension_forall_mem_Icc_of_isClosedEmbedding`, there exists an extension `g`
    such that `g y ∈ [a, b]` for all `y`. However, if `a` and/or `b` do not belong to the range of
    `f`, then we need to ensure that these points do not belong to the range of `g`. This is done
    in two almost identical steps. First we deal with the case `∀ x, f x ≠ a`. -/
  obtain ⟨g, hg_mem, hgf⟩ : ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x, g y ∈ Icc (f x) b) ∧ g ∘ e = f := by
    rcases exists_extension_forall_mem_Icc_of_isClosedEmbedding f hmem hle he with ⟨g, hg_mem, hgf⟩
    -- If `a ∈ range f`, then we are done.
    rcases em (∃ x, f x = a) with (⟨x, rfl⟩ | ha')
    · exact ⟨g, fun y => ⟨x, hg_mem _⟩, hgf⟩
    /- Otherwise, `g ⁻¹' {a}` is disjoint with `range e ∪ g ⁻¹' (Ici c)`, hence there exists a
        function `dg : Y → ℝ` such that `dg ∘ e = 0`, `dg y = 0` whenever `c ≤ g y`, `dg y = c - a`
        whenever `g y = a`, and `0 ≤ dg y ≤ c - a` for all `y`. -/
    have hd : Disjoint (range e ∪ g ⁻¹' Ici c) (g ⁻¹' {a}) := by
      refine disjoint_union_left.2 ⟨?_, Disjoint.preimage _ ?_⟩
      · rw [Set.disjoint_left]
        rintro _ ⟨x, rfl⟩ (rfl : g (e x) = a)
        exact ha' ⟨x, (congr_fun hgf x).symm⟩
      · exact Set.disjoint_singleton_right.2 hac.not_ge
    rcases exists_bounded_mem_Icc_of_closed_of_le
        (he.isClosed_range.union <| isClosed_Ici.preimage g.continuous)
        (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hac.le) with
      ⟨dg, dg0, dga, dgmem⟩
    replace hgf : ∀ x, (g + dg) (e x) = f x := by
      intro x
      simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
    refine ⟨g + dg, fun y => ?_, funext hgf⟩
    have hay : a < (g + dg) y := by
      rcases (hg_mem y).1.eq_or_lt with (rfl | hlt)
      · refine (lt_add_iff_pos_right _).2 ?_
        calc
          0 < c - g y := sub_pos.2 hac
          _ = dg y := (dga rfl).symm
      · exact hlt.trans_le (le_add_of_nonneg_right (dgmem y).1)
    rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
    refine ⟨x, hxy.le, ?_⟩
    rcases le_total c (g y) with hc | hc
    · simp [dg0 (Or.inr hc), (hg_mem y).2]
    · calc
        g y + dg y ≤ c + (c - a) := add_le_add hc (dgmem _).2
        _ = b := by rw [hsub, add_sub_cancel]
  /- Now we deal with the case `∀ x, f x ≠ b`. The proof is the same as in the first case, with
    minor modifications that make it hard to deduplicate code. -/
  choose xl hxl hgb using hg_mem
  rcases em (∃ x, f x = b) with (⟨x, rfl⟩ | hb')
  · exact ⟨g, fun y => ⟨xl y, x, hxl y, hgb y⟩, hgf⟩
  have hd : Disjoint (range e ∪ g ⁻¹' Iic c) (g ⁻¹' {b}) := by
    refine disjoint_union_left.2 ⟨?_, Disjoint.preimage _ ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ (rfl : g (e x) = b)
      exact hb' ⟨x, (congr_fun hgf x).symm⟩
    · exact Set.disjoint_singleton_right.2 hcb.not_ge
  rcases exists_bounded_mem_Icc_of_closed_of_le
      (he.isClosed_range.union <| isClosed_Iic.preimage g.continuous)
      (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hcb.le) with
    ⟨dg, dg0, dgb, dgmem⟩
  replace hgf : ∀ x, (g - dg) (e x) = f x := by
    intro x
    simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
  refine ⟨g - dg, fun y => ?_, funext hgf⟩
  have hyb : (g - dg) y < b := by
    rcases (hgb y).eq_or_lt with (rfl | hlt)
    · refine (sub_lt_self_iff _).2 ?_
      calc
        0 < g y - c := sub_pos.2 hcb
        _ = dg y := (dgb rfl).symm
    · exact ((sub_le_self_iff _).2 (dgmem _).1).trans_lt hlt
  rcases hb.exists_between hyb with ⟨_, ⟨xu, rfl⟩, hyxu, _⟩
  rcases lt_or_ge c (g y) with hc | hc
  · rcases em (a ∈ range f) with (⟨x, rfl⟩ | _)
    · refine ⟨x, xu, ?_, hyxu.le⟩
      calc
        f x = c - (b - c) := by rw [← hsub, sub_sub_cancel]
        _ ≤ g y - dg y := sub_le_sub hc.le (dgmem _).2
    · have hay : a < (g - dg) y := by
        calc
          a = c - (b - c) := by rw [← hsub, sub_sub_cancel]
          _ < g y - (b - c) := sub_lt_sub_right hc _
          _ ≤ g y - dg y := sub_le_sub_left (dgmem _).2 _
      rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
      exact ⟨x, xu, hxy.le, hyxu.le⟩
  · refine ⟨xl y, xu, ?_, hyxu.le⟩
    simp [dg0 (Or.inr hc), hxl]

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Let `t` be
a nonempty convex set of real numbers (we use `OrdConnected` instead of `Convex` to automatically
deduce this argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists
a bounded continuous real-valued function `g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and
`g ∘ e = f`. -/
theorem exists_extension_forall_mem_of_isClosedEmbedding (f : X →ᵇ ℝ) {t : Set ℝ} {e : X → Y}
    [hs : OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g ∘ e = f := by
  cases isEmpty_or_nonempty X
  · rcases hne with ⟨c, hc⟩
    exact ⟨const Y c, fun _ => hc, funext fun x => isEmptyElim x⟩
  rcases exists_extension_forall_exists_le_ge_of_isClosedEmbedding f he with ⟨g, hg, hgf⟩
  refine ⟨g, fun y => ?_, hgf⟩
  rcases hg y with ⟨xl, xu, h⟩
  exact hs.out (hf _) (hf _) h

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. Let `s` be a closed set in a normal topological space `Y`. Let `f` be a bounded continuous
real-valued function on `s`. Let `t` be a nonempty convex set of real numbers (we use
`OrdConnected` instead of `Convex` to automatically deduce this argument by typeclass search) such
that `f x ∈ t` for all `x : s`. Then there exists a bounded continuous real-valued function
`g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and `g.restrict s = f`. -/
theorem exists_forall_mem_restrict_eq_of_closed {s : Set Y} (f : s →ᵇ ℝ) (hs : IsClosed s)
    {t : Set ℝ} [OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g.restrict s = f := by
  obtain ⟨g, hg, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f hf hne hs.isClosedEmbedding_subtypeVal
  exact ⟨g, hg, DFunLike.coe_injective hgf⟩

end BoundedContinuousFunction

namespace ContinuousMap

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a continuous real-valued function on `X`. Let `t` be a nonempty
convex set of real numbers (we use `OrdConnected` instead of `Convex` to automatically deduce this
argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists a continuous
real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and `g ∘ e = f`. -/
theorem exists_extension_forall_mem_of_isClosedEmbedding (f : C(X, ℝ)) {t : Set ℝ} {e : X → Y}
    [hs : OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) (he : IsClosedEmbedding e) :
    ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g ∘ e = f := by
  have h : ℝ ≃o Ioo (-1 : ℝ) 1 := orderIsoIooNegOneOne ℝ
  let F : X →ᵇ ℝ :=
    { toFun := (↑) ∘ h ∘ f
      continuous_toFun := by fun_prop
      map_bounded' := isBounded_range_iff.1
        ((isBounded_Ioo (-1 : ℝ) 1).subset <| range_subset_iff.2 fun x => (h (f x)).2) }
  let t' : Set ℝ := (↑) ∘ h '' t
  have ht_sub : t' ⊆ Ioo (-1 : ℝ) 1 := image_subset_iff.2 fun x _ => (h x).2
  have : OrdConnected t' := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
    lift z to Ioo (-1 : ℝ) 1 using Icc_subset_Ioo (h x).2.1 (h y).2.2 hz
    change z ∈ Icc (h x) (h y) at hz
    rw [← h.image_Icc] at hz
    rcases hz with ⟨z, hz, rfl⟩
    exact ⟨z, hs.out hx hy hz, rfl⟩
  have hFt : ∀ x, F x ∈ t' := fun x => mem_image_of_mem _ (hf x)
  rcases F.exists_extension_forall_mem_of_isClosedEmbedding hFt (hne.image _) he with ⟨G, hG, hGF⟩
  let g : C(Y, ℝ) :=
    ⟨h.symm ∘ codRestrict G _ fun y => ht_sub (hG y),
      h.symm.continuous.comp <| G.continuous.subtype_mk _⟩
  have hgG : ∀ {y a}, g y = a ↔ G y = h a := @fun y a =>
    h.toEquiv.symm_apply_eq.trans Subtype.ext_iff
  refine ⟨g, fun y => ?_, ?_⟩
  · rcases hG y with ⟨a, ha, hay⟩
    convert ha
    exact hgG.2 hay.symm
  · ext x
    exact hgG.2 (congr_fun hGF _)

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed set. Let
`s` be a closed set in a normal topological space `Y`. Let `f` be a continuous real-valued function
on `s`. Let `t` be a nonempty convex set of real numbers (we use `OrdConnected` instead of `Convex`
to automatically deduce this argument by typeclass search) such that `f x ∈ t` for all `x : s`. Then
there exists a continuous real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and
`g.restrict s = f`. -/
theorem exists_restrict_eq_forall_mem_of_closed {s : Set Y} (f : C(s, ℝ)) {t : Set ℝ}
    [OrdConnected t] (ht : ∀ x, f x ∈ t) (hne : t.Nonempty) (hs : IsClosed s) :
    ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g.restrict s = f :=
  let ⟨g, hgt, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f ht hne hs.isClosedEmbedding_subtypeVal
  ⟨g, hgt, coe_injective hgf⟩

end ContinuousMap

/-- **Tietze extension theorem** for real-valued continuous maps.
`ℝ` is a `TietzeExtension` space. -/
instance Real.instTietzeExtension : TietzeExtension ℝ where
  exists_restrict_eq' _s hs f :=
    f.exists_restrict_eq_forall_mem_of_closed (fun _ => mem_univ _) univ_nonempty hs |>.imp
      fun _ ↦ (And.right ·)

open NNReal in
/-- **Tietze extension theorem** for nonnegative real-valued continuous maps.
`ℝ≥0` is a `TietzeExtension` space. -/
instance NNReal.instTietzeExtension : TietzeExtension ℝ≥0 :=
  .of_retract ⟨((↑) : ℝ≥0 → ℝ), by continuity⟩ ⟨Real.toNNReal, continuous_real_toNNReal⟩ <| by
    ext; simp
