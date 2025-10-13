/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Topology.Bornology.Hom
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we specialize various facts about Lipschitz continuous maps
to the case of (pseudo) metric spaces.

## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

assert_not_exists Module.Basis Ideal ContinuousMul

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

theorem lipschitzWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} : LipschitzWith K f ↔ ∀ x y, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul

theorem lipschitzOnWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {s : Set α} {f : α → β} :
    LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzOnWith, edist_nndist, dist_nndist]
  norm_cast

alias ⟨LipschitzOnWith.dist_le_mul, LipschitzOnWith.of_dist_le_mul⟩ :=
  lipschitzOnWith_iff_dist_le_mul

namespace LipschitzWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] {K : ℝ≥0} {f : α → β}
  {x y : α} {r : ℝ}

protected theorem of_dist_le' {K : ℝ} (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  of_dist_le_mul fun x y =>
    le_trans (h x y) <| by gcongr; apply Real.le_coe_toNNReal

protected theorem mk_one (h : ∀ x y, dist (f x) (f y) ≤ dist x y) : LipschitzWith 1 f :=
  of_dist_le_mul <| by simpa only [NNReal.coe_one, one_mul] using h

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  have I : ∀ x y, f x - f y ≤ K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith K f := by simpa only [Real.toNNReal_coe] using LipschitzWith.of_le_add_mul' K h

protected theorem of_le_add {f : α → ℝ} (h : ∀ x y, f x ≤ f y + dist x y) : LipschitzWith 1 f :=
  LipschitzWith.of_le_add_mul 1 <| by simpa only [NNReal.coe_one, one_mul]

protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : LipschitzWith K f) (x y) :
    f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_trans (le_abs_self _) <| h.dist_le_mul x y

protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ x y, f x ≤ f y + K * dist x y :=
  ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩

theorem nndist_le (hf : LipschitzWith K f) (x y : α) : nndist (f x) (f y) ≤ K * nndist x y :=
  hf.dist_le_mul x y

theorem dist_le_mul_of_le (hf : LipschitzWith K f) (hr : dist x y ≤ r) : dist (f x) (f y) ≤ K * r :=
  (hf.dist_le_mul x y).trans <| by gcongr

theorem mapsTo_closedBall (hf : LipschitzWith K f) (x : α) (r : ℝ) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) (K * r)) := fun _y hy =>
  hf.dist_le_mul_of_le hy

theorem dist_lt_mul_of_lt (hf : LipschitzWith K f) (hK : K ≠ 0) (hr : dist x y < r) :
    dist (f x) (f y) < K * r :=
  (hf.dist_le_mul x y).trans_lt <| (mul_lt_mul_left <| NNReal.coe_pos.2 hK.bot_lt).2 hr

theorem mapsTo_ball (hf : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) (K * r)) := fun _y hy =>
  hf.dist_lt_mul_of_lt hK hy

/-- A Lipschitz continuous map is a locally bounded map. -/
def toLocallyBoundedMap (f : α → β) (hf : LipschitzWith K f) : LocallyBoundedMap α β :=
  LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, forall_mem_image.2 fun _x hx => forall_mem_image.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩

@[simp]
theorem coe_toLocallyBoundedMap (hf : LipschitzWith K f) : ⇑(hf.toLocallyBoundedMap f) = f :=
  rfl

theorem comap_cobounded_le (hf : LipschitzWith K f) :
    comap f (Bornology.cobounded β) ≤ Bornology.cobounded α :=
  (hf.toLocallyBoundedMap f).2

/-- The image of a bounded set under a Lipschitz map is bounded. -/
theorem isBounded_image (hf : LipschitzWith K f) {s : Set α} (hs : IsBounded s) :
    IsBounded (f '' s) :=
  hs.image (toLocallyBoundedMap f hf)

theorem diam_image_le (hf : LipschitzWith K f) (s : Set α) (hs : IsBounded s) :
    Metric.diam (f '' s) ≤ K * Metric.diam s :=
  Metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg Metric.diam_nonneg) <|
    forall_mem_image.2 fun _x hx =>
      forall_mem_image.2 fun _y hy => hf.dist_le_mul_of_le <| Metric.dist_le_diam_of_mem hs hx hy

protected theorem dist_left (y : α) : LipschitzWith 1 (dist · y) :=
  LipschitzWith.mk_one fun _ _ => dist_dist_dist_le_left _ _ _

protected theorem dist_right (x : α) : LipschitzWith 1 (dist x) :=
  LipschitzWith.of_le_add fun _ _ => dist_triangle_right _ _ _

protected theorem dist : LipschitzWith 2 (Function.uncurry <| @dist α _) := by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry LipschitzWith.dist_left LipschitzWith.dist_right

theorem dist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    dist (f^[n] x) (f^[n+1] x) ≤ dist x (f x) * (K : ℝ) ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [NNReal.coe_pow] using (hf.iterate n).dist_le_mul x (f x)

theorem _root_.lipschitzWith_max : LipschitzWith 1 fun p : ℝ × ℝ => max p.1 p.2 :=
  LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1 <|
    (le_abs_self _).trans (abs_max_sub_max_le_max _ _ _ _)

theorem _root_.lipschitzWith_min : LipschitzWith 1 fun p : ℝ × ℝ => min p.1 p.2 :=
  LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1 <|
    (le_abs_self _).trans (abs_min_sub_min_le_max _ _ _ _)

lemma _root_.Real.lipschitzWith_toNNReal : LipschitzWith 1 Real.toNNReal := by
  refine lipschitzWith_iff_dist_le_mul.mpr (fun x y ↦ ?_)
  simpa only [NNReal.coe_one, dist_prod_same_right, one_mul, Real.dist_eq] using
    lipschitzWith_iff_dist_le_mul.mp lipschitzWith_max (x, 0) (y, 0)

end Metric

section EMetric

variable [PseudoEMetricSpace α] {f g : α → ℝ} {Kf Kg : ℝ≥0}

protected theorem max (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => max (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using lipschitzWith_max.comp (hf.prodMk hg)

protected theorem min (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => min (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using lipschitzWith_min.comp (hf.prodMk hg)

theorem max_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max (f x) a := by
  simpa only [max_eq_left (zero_le Kf)] using hf.max (LipschitzWith.const a)

theorem const_max (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max a (f x) := by
  simpa only [max_comm] using hf.max_const a

theorem min_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min (f x) a := by
  simpa only [max_eq_left (zero_le Kf)] using hf.min (LipschitzWith.const a)

theorem const_min (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min a (f x) := by
  simpa only [min_comm] using hf.min_const a

end EMetric

protected theorem projIcc {a b : ℝ} (h : a ≤ b) : LipschitzWith 1 (projIcc a b h) :=
  ((LipschitzWith.id.const_min _).const_max _).subtype_mk _

end LipschitzWith

/-- The preimage of a proper space under a Lipschitz proper map is proper. -/
lemma LipschitzWith.properSpace {X Y : Type*} [PseudoMetricSpace X]
    [PseudoMetricSpace Y] [ProperSpace Y] {f : X → Y} (hf : IsProperMap f)
    {K : ℝ≥0} (hf' : LipschitzWith K f) : ProperSpace X :=
  ⟨fun x r ↦ (hf.isCompact_preimage (isCompact_closedBall (f x) (K * r))).of_isClosed_subset
    Metric.isClosed_closedBall (hf'.mapsTo_closedBall x r).subset_preimage⟩

namespace Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s : Set α} {t : Set β}

end Metric

namespace LipschitzOnWith

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]
variable {K : ℝ≥0} {s : Set α} {f : α → β}

protected theorem of_dist_le' {K : ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzOnWith (Real.toNNReal K) f s :=
  of_dist_le_mul fun x hx y hy =>
    le_trans (h x hx y hy) <| by gcongr; apply Real.le_coe_toNNReal

protected theorem mk_one (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ dist x y) :
    LipschitzOnWith 1 f s :=
  of_dist_le_mul <| by simpa only [NNReal.coe_one, one_mul] using h

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y) : LipschitzOnWith (Real.toNNReal K) f s :=
  have I : ∀ x ∈ s, ∀ y ∈ s, f x - f y ≤ K * dist x y := fun x hx y hy =>
    sub_le_iff_le_add'.2 (h x hx y hy)
  LipschitzOnWith.of_dist_le' fun x hx y hy =>
    abs_sub_le_iff.2 ⟨I x hx y hy, dist_comm y x ▸ I y hy x hx⟩

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y) : LipschitzOnWith K f s := by
  simpa only [Real.toNNReal_coe] using LipschitzOnWith.of_le_add_mul' K h

protected theorem of_le_add {f : α → ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + dist x y) :
    LipschitzOnWith 1 f s :=
  LipschitzOnWith.of_le_add_mul 1 <| by simpa only [NNReal.coe_one, one_mul]

protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : LipschitzOnWith K f s) {x : α} (hx : x ∈ s)
    {y : α} (hy : y ∈ s) : f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_trans (le_abs_self _) <| h.dist_le_mul x hx y hy

protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
    LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y :=
  ⟨LipschitzOnWith.le_add_mul, LipschitzOnWith.of_le_add_mul K⟩

theorem isBounded_image2 (f : α → β → γ) {K₁ K₂ : ℝ≥0} {s : Set α} {t : Set β}
    (hs : Bornology.IsBounded s) (ht : Bornology.IsBounded t)
    (hf₁ : ∀ b ∈ t, LipschitzOnWith K₁ (fun a => f a b) s)
    (hf₂ : ∀ a ∈ s, LipschitzOnWith K₂ (f a) t) : Bornology.IsBounded (Set.image2 f s t) :=
  Metric.isBounded_iff_ediam_ne_top.2 <|
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top hs.ediam_ne_top,
          ENNReal.mul_ne_top ENNReal.coe_ne_top ht.ediam_ne_top⟩)
      (ediam_image2_le _ _ _ hf₁ hf₂)

end Metric

end LipschitzOnWith

namespace LocallyLipschitz

section Real

variable [PseudoEMetricSpace α] {f g : α → ℝ}

/-- The minimum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma min (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) :=
  lipschitzWith_min.locallyLipschitz.comp (hf.prodMk hg)

/-- The maximum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma max (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) :=
  lipschitzWith_max.locallyLipschitz.comp (hf.prodMk hg)

theorem max_const (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => max (f x) a :=
  hf.max (LocallyLipschitz.const a)

theorem const_max (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => max a (f x) := by
  simpa [max_comm] using (hf.max_const a)

theorem min_const (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => min (f x) a :=
  hf.min (LocallyLipschitz.const a)

theorem const_min (hf : LocallyLipschitz f) (a : ℝ) : LocallyLipschitz fun x => min a (f x) := by
  simpa [min_comm] using (hf.min_const a)

end Real
end LocallyLipschitz

open Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}

/-- A function `f : α → ℝ` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz extension
to the whole space. -/
theorem LipschitzOnWith.extend_real {f : α → ℝ} {s : Set α} {K : ℝ≥0} (hf : LipschitzOnWith K f s) :
    ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  /- An extension is given by `g y = Inf {f x + K * dist y x | x ∈ s}`. Taking `x = y`, one has
    `g y ≤ f y` for `y ∈ s`, and the other inequality holds because `f` is `K`-Lipschitz, so that it
    can not counterbalance the growth of `K * dist y x`. One readily checks from the formula that
    the extended function is also `K`-Lipschitz. -/
  rcases eq_empty_or_nonempty s with (rfl | hs)
  · exact ⟨fun _ => 0, (LipschitzWith.const _).weaken (zero_le _), eqOn_empty _ _⟩
  have : Nonempty s := by simp only [hs, nonempty_coe_sort]
  let g := fun y : α => iInf fun x : s => f x + K * dist y x
  have B : ∀ y : α, BddBelow (range fun x : s => f x + K * dist y x) := fun y => by
    rcases hs with ⟨z, hz⟩
    refine ⟨f z - K * dist y z, ?_⟩
    rintro w ⟨t, rfl⟩
    dsimp
    rw [sub_le_iff_le_add, add_assoc, ← mul_add, add_comm (dist y t)]
    calc
      f z ≤ f t + K * dist z t := hf.le_add_mul hz t.2
      _ ≤ f t + K * (dist y z + dist y t) := by gcongr; apply dist_triangle_left
  have E : EqOn f g s := fun x hx => by
    refine le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) ?_
    simpa only [add_zero, Subtype.coe_mk, mul_zero, dist_self] using ciInf_le (B x) ⟨x, hx⟩
  refine ⟨g, LipschitzWith.of_le_add_mul K fun x y => ?_, E⟩
  rw [← sub_le_iff_le_add]
  refine le_ciInf fun z => ?_
  rw [sub_le_iff_le_add]
  calc
    g x ≤ f z + K * dist x z := ciInf_le (B x) _
    _ ≤ f z + K * dist y z + K * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y z)]
      gcongr
      apply dist_triangle

/-- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space. The same result for the space `ℓ^∞ (ι, ℝ)` over a possibly infinite
type `ι` is implemented in `LipschitzOnWith.extend_lp_infty`. -/
theorem LipschitzOnWith.extend_pi [Fintype ι] {f : α → ι → ℝ} {s : Set α}
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) : ∃ g : α → ι → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  have : ∀ i, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => ?_, fun x hx ↦ ?_⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · ext1 i
    exact (hg i).2 hx
