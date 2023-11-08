/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Data.Set.Intervals.ProjIcc
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Bornology.Hom
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded

#align_import topology.metric_space.lipschitz from "leanprover-community/mathlib"@"c8f305514e0d47dfaa710f5a52f0d21b588e6328"

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous, and that locally Lipschitz functions are continuous.

## Main definitions and lemmas

* `LipschitzWith K f`: states that `f` is Lipschitz with constant `K : ℝ≥0`
* `LipschitzOnWith K f s`: states that `f` is Lipschitz with constant `K : ℝ≥0` on a set `s`
* `LipschitzWith.uniformContinuous`: a Lipschitz function is uniformly continuous
* `LipschitzOnWith.uniformContinuousOn`: a function which is Lipschitz on a set `s` is uniformly
  continuous on `s`.
* `LocallyLipschitz f`: states that `f` is locally Lipschitz
* `LocallyLipschitz.continuous`: a locally Lipschitz function is continuous.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

set_option autoImplicit true

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

/-- A function `f` is **Lipschitz continuous** with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y`. -/
def LipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist (f x) (f y) ≤ K * edist x y
#align lipschitz_with LipschitzWith

theorem lipschitzWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {f : α → β} : LipschitzWith K f ↔ ∀ x y, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzWith, edist_nndist, dist_nndist]
  norm_cast
#align lipschitz_with_iff_dist_le_mul lipschitzWith_iff_dist_le_mul

alias ⟨LipschitzWith.dist_le_mul, LipschitzWith.of_dist_le_mul⟩ := lipschitzWith_iff_dist_le_mul
#align lipschitz_with.dist_le_mul LipschitzWith.dist_le_mul
#align lipschitz_with.of_dist_le_mul LipschitzWith.of_dist_le_mul

/-- A function `f` is **Lipschitz continuous** with constant `K ≥ 0` **on `s`** if
for all `x, y` in `s` we have `dist (f x) (f y) ≤ K * dist x y`. -/
def LipschitzOnWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β)
    (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → edist (f x) (f y) ≤ K * edist x y
#align lipschitz_on_with LipschitzOnWith

/-- `f : α → β` is called **locally Lipschitz continuous** iff every point `x`
has a neighourhood on which `f` is Lipschitz. -/
def LocallyLipschitz [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : Prop :=
  ∀ x : α, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

/-- Every function is Lipschitz on the empty set (with any Lipschitz constant). -/
@[simp]
theorem lipschitzOnWith_empty [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :
    LipschitzOnWith K f ∅ := fun _ => False.elim
#align lipschitz_on_with_empty lipschitzOnWith_empty

/-- Being Lipschitz on a set is monotone w.r.t. that set. -/
theorem LipschitzOnWith.mono [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {s t : Set α}
    {f : α → β} (hf : LipschitzOnWith K f t) (h : s ⊆ t) : LipschitzOnWith K f s :=
  fun _x x_in _y y_in => hf (h x_in) (h y_in)
#align lipschitz_on_with.mono LipschitzOnWith.mono

theorem lipschitzOnWith_iff_dist_le_mul [PseudoMetricSpace α] [PseudoMetricSpace β] {K : ℝ≥0}
    {s : Set α} {f : α → β} :
    LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y := by
  simp only [LipschitzOnWith, edist_nndist, dist_nndist]
  norm_cast
#align lipschitz_on_with_iff_dist_le_mul lipschitzOnWith_iff_dist_le_mul

alias ⟨LipschitzOnWith.dist_le_mul, LipschitzOnWith.of_dist_le_mul⟩ :=
  lipschitzOnWith_iff_dist_le_mul
#align lipschitz_on_with.dist_le_mul LipschitzOnWith.dist_le_mul
#align lipschitz_on_with.of_dist_le_mul LipschitzOnWith.of_dist_le_mul

/-- `f` is Lipschitz iff it is Lipschitz on the entire space. -/
@[simp]
theorem lipschitzOn_univ [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {f : α → β} :
    LipschitzOnWith K f univ ↔ LipschitzWith K f := by simp [LipschitzOnWith, LipschitzWith]
#align lipschitz_on_univ lipschitzOn_univ

theorem lipschitzOnWith_iff_restrict [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0}
    {f : α → β} {s : Set α} : LipschitzOnWith K f s ↔ LipschitzWith K (s.restrict f) := by
  simp only [LipschitzOnWith, LipschitzWith, SetCoe.forall', restrict, Subtype.edist_eq]
#align lipschitz_on_with_iff_restrict lipschitzOnWith_iff_restrict

alias ⟨LipschitzOnWith.to_restrict, _⟩ := lipschitzOnWith_iff_restrict
#align lipschitz_on_with.to_restrict LipschitzOnWith.to_restrict

theorem MapsTo.lipschitzOnWith_iff_restrict [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0}
    {f : α → β} {s : Set α} {t : Set β} (h : MapsTo f s t) :
    LipschitzOnWith K f s ↔ LipschitzWith K (h.restrict f s t) :=
  _root_.lipschitzOnWith_iff_restrict
#align maps_to.lipschitz_on_with_iff_restrict MapsTo.lipschitzOnWith_iff_restrict

alias ⟨LipschitzOnWith.to_restrict_mapsTo, _⟩ := MapsTo.lipschitzOnWith_iff_restrict
#align lipschitz_on_with.to_restrict_maps_to LipschitzOnWith.to_restrict_mapsTo

namespace LipschitzWith

section EMetric

open EMetric

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

variable {K : ℝ≥0} {f : α → β} {x y : α} {r : ℝ≥0∞}

protected theorem lipschitzOnWith (h : LipschitzWith K f) (s : Set α) : LipschitzOnWith K f s :=
  fun x _ y _ => h x y
#align lipschitz_with.lipschitz_on_with LipschitzWith.lipschitzOnWith

theorem edist_le_mul (h : LipschitzWith K f) (x y : α) : edist (f x) (f y) ≤ K * edist x y :=
  h x y
#align lipschitz_with.edist_le_mul LipschitzWith.edist_le_mul

theorem edist_le_mul_of_le (h : LipschitzWith K f) (hr : edist x y ≤ r) :
    edist (f x) (f y) ≤ K * r :=
  (h x y).trans <| ENNReal.mul_left_mono hr
#align lipschitz_with.edist_le_mul_of_le LipschitzWith.edist_le_mul_of_le

theorem edist_lt_mul_of_lt (h : LipschitzWith K f) (hK : K ≠ 0) (hr : edist x y < r) :
    edist (f x) (f y) < K * r :=
  (h x y).trans_lt <| (ENNReal.mul_lt_mul_left (ENNReal.coe_ne_zero.2 hK) ENNReal.coe_ne_top).2 hr
#align lipschitz_with.edist_lt_mul_of_lt LipschitzWith.edist_lt_mul_of_lt

theorem mapsTo_emetric_closedBall (h : LipschitzWith K f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (closedBall x r) (closedBall (f x) (K * r)) := fun _y hy => h.edist_le_mul_of_le hy
#align lipschitz_with.maps_to_emetric_closed_ball LipschitzWith.mapsTo_emetric_closedBall

theorem mapsTo_emetric_ball (h : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ≥0∞) :
    MapsTo f (ball x r) (ball (f x) (K * r)) := fun _y hy => h.edist_lt_mul_of_lt hK hy
#align lipschitz_with.maps_to_emetric_ball LipschitzWith.mapsTo_emetric_ball

theorem edist_lt_top (hf : LipschitzWith K f) {x y : α} (h : edist x y ≠ ⊤) :
    edist (f x) (f y) < ⊤ :=
  (hf x y).trans_lt <| ENNReal.mul_lt_top ENNReal.coe_ne_top h
#align lipschitz_with.edist_lt_top LipschitzWith.edist_lt_top

theorem mul_edist_le (h : LipschitzWith K f) (x y : α) :
    (K⁻¹ : ℝ≥0∞) * edist (f x) (f y) ≤ edist x y := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (h x y)
#align lipschitz_with.mul_edist_le LipschitzWith.mul_edist_le

protected theorem of_edist_le (h : ∀ x y, edist (f x) (f y) ≤ edist x y) : LipschitzWith 1 f :=
  fun x y => by simp only [ENNReal.coe_one, one_mul, h]
#align lipschitz_with.of_edist_le LipschitzWith.of_edist_le

protected theorem weaken (hf : LipschitzWith K f) {K' : ℝ≥0} (h : K ≤ K') : LipschitzWith K' f :=
  fun x y => le_trans (hf x y) <| ENNReal.mul_right_mono (ENNReal.coe_le_coe.2 h)
#align lipschitz_with.weaken LipschitzWith.weaken

theorem ediam_image_le (hf : LipschitzWith K f) (s : Set α) :
    EMetric.diam (f '' s) ≤ K * EMetric.diam s := by
  apply EMetric.diam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.edist_le_mul_of_le (EMetric.edist_le_diam_of_mem hx hy)
#align lipschitz_with.ediam_image_le LipschitzWith.ediam_image_le

theorem edist_lt_of_edist_lt_div (hf : LipschitzWith K f) {x y : α} {d : ℝ≥0∞}
    (h : edist x y < d / K) : edist (f x) (f y) < d :=
  calc
    edist (f x) (f y) ≤ K * edist x y := hf x y
    _ < d := ENNReal.mul_lt_of_lt_div' h
#align lipschitz_with.edist_lt_of_edist_lt_div LipschitzWith.edist_lt_of_edist_lt_div

/-- A Lipschitz function is uniformly continuous. -/
protected theorem uniformContinuous (hf : LipschitzWith K f) : UniformContinuous f :=
  EMetric.uniformContinuous_iff.2 fun ε εpos =>
    ⟨ε / K, ENNReal.div_pos_iff.2 ⟨ne_of_gt εpos, ENNReal.coe_ne_top⟩, hf.edist_lt_of_edist_lt_div⟩
#align lipschitz_with.uniform_continuous LipschitzWith.uniformContinuous

/-- A Lipschitz function is continuous. -/
protected theorem continuous (hf : LipschitzWith K f) : Continuous f :=
  hf.uniformContinuous.continuous
#align lipschitz_with.continuous LipschitzWith.continuous

/-- Constant functions are Lipschitz (with any constant). -/
protected theorem const (b : β) : LipschitzWith 0 fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]
#align lipschitz_with.const LipschitzWith.const

protected theorem const' (b : β) {K : ℝ≥0} : LipschitzWith K fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]

/-- The identity is 1-Lipschitz. -/
protected theorem id : LipschitzWith 1 (@id α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl
#align lipschitz_with.id LipschitzWith.id

/-- The inclusion of a subset is 1-Lipschitz. -/
protected theorem subtype_val (s : Set α) : LipschitzWith 1 (Subtype.val : s → α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl
#align lipschitz_with.subtype_val LipschitzWith.subtype_val
#align lipschitz_with.subtype_coe LipschitzWith.subtype_val

theorem subtype_mk (hf : LipschitzWith K f) {p : β → Prop} (hp : ∀ x, p (f x)) :
    LipschitzWith K (fun x => ⟨f x, hp x⟩ : α → { y // p y }) :=
  hf
#align lipschitz_with.subtype_mk LipschitzWith.subtype_mk

protected theorem eval {α : ι → Type u} [∀ i, PseudoEMetricSpace (α i)] [Fintype ι] (i : ι) :
    LipschitzWith 1 (Function.eval i : (∀ i, α i) → α i) :=
  LipschitzWith.of_edist_le fun f g => by convert edist_le_pi_edist f g i
#align lipschitz_with.eval LipschitzWith.eval

/-- The restriction of a `K`-Lipschitz function is `K`-Lipschitz. -/
protected theorem restrict (hf : LipschitzWith K f) (s : Set α) : LipschitzWith K (s.restrict f) :=
  fun x y => hf x y
#align lipschitz_with.restrict LipschitzWith.restrict

/-- The composition of Lipschitz functions is Lipschitz. -/
protected theorem comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f ∘ g) := fun x y =>
  calc
    edist (f (g x)) (f (g y)) ≤ Kf * edist (g x) (g y) := hf _ _
    _ ≤ Kf * (Kg * edist x y) := (ENNReal.mul_left_mono (hg _ _))
    _ = (Kf * Kg : ℝ≥0) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]
#align lipschitz_with.comp LipschitzWith.comp

theorem comp_lipschitzOnWith {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} {s : Set α}
    (hf : LipschitzWith Kf f) (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf * Kg) (f ∘ g) s :=
  lipschitzOnWith_iff_restrict.mpr <| hf.comp hg.to_restrict
#align lipschitz_with.comp_lipschitz_on_with LipschitzWith.comp_lipschitzOnWith

protected theorem prod_fst : LipschitzWith 1 (@Prod.fst α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_left _ _
#align lipschitz_with.prod_fst LipschitzWith.prod_fst

protected theorem prod_snd : LipschitzWith 1 (@Prod.snd α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_right _ _
#align lipschitz_with.prod_snd LipschitzWith.prod_snd

/-- If `f` and `g` are Lipschitz functions, so is the induced map `f × g` to the product type. -/
protected theorem prod {f : α → β} {Kf : ℝ≥0} (hf : LipschitzWith Kf f) {g : α → γ} {Kg : ℝ≥0}
    (hg : LipschitzWith Kg g) : LipschitzWith (max Kf Kg) fun x => (f x, g x) := by
  intro x y
  rw [ENNReal.coe_mono.map_max, Prod.edist_eq, ENNReal.max_mul]
  exact max_le_max (hf x y) (hg x y)
#align lipschitz_with.prod LipschitzWith.prod

protected theorem prod_mk_left (a : α) : LipschitzWith 1 (Prod.mk a : β → α × β) := by
  simpa only [max_eq_right zero_le_one] using (LipschitzWith.const a).prod LipschitzWith.id
#align lipschitz_with.prod_mk_left LipschitzWith.prod_mk_left

protected theorem prod_mk_right (b : β) : LipschitzWith 1 fun a : α => (a, b) := by
  simpa only [max_eq_left zero_le_one] using LipschitzWith.id.prod (LipschitzWith.const b)
#align lipschitz_with.prod_mk_right LipschitzWith.prod_mk_right

protected theorem uncurry {f : α → β → γ} {Kα Kβ : ℝ≥0} (hα : ∀ b, LipschitzWith Kα fun a => f a b)
    (hβ : ∀ a, LipschitzWith Kβ (f a)) : LipschitzWith (Kα + Kβ) (Function.uncurry f) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [Function.uncurry, ENNReal.coe_add, add_mul]
  apply le_trans (edist_triangle _ (f a₂ b₁) _)
  exact
    add_le_add (le_trans (hα _ _ _) <| ENNReal.mul_left_mono <| le_max_left _ _)
      (le_trans (hβ _ _ _) <| ENNReal.mul_left_mono <| le_max_right _ _)
#align lipschitz_with.uncurry LipschitzWith.uncurry

/-- Iterates of a Lipschitz function are Lipschitz. -/
protected theorem iterate {f : α → α} (hf : LipschitzWith K f) : ∀ n, LipschitzWith (K ^ n) f^[n]
  | 0 => by simpa only [pow_zero] using LipschitzWith.id
  | n + 1 => by rw [pow_succ']; exact (LipschitzWith.iterate hf n).comp hf
#align lipschitz_with.iterate LipschitzWith.iterate

theorem edist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    edist (f^[n] x) (f^[n + 1] x) ≤ edist x (f x) * (K : ℝ≥0∞) ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [ENNReal.coe_pow] using (hf.iterate n) x (f x)
#align lipschitz_with.edist_iterate_succ_le_geometric LipschitzWith.edist_iterate_succ_le_geometric

protected theorem mul_end {f g : Function.End α} {Kf Kg} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f * g : Function.End α) :=
  hf.comp hg
#align lipschitz_with.mul LipschitzWith.mul_end

/-- The product of a list of Lipschitz continuous endomorphisms is a Lipschitz continuous
endomorphism. -/
protected theorem list_prod (f : ι → Function.End α) (K : ι → ℝ≥0)
    (h : ∀ i, LipschitzWith (K i) (f i)) : ∀ l : List ι, LipschitzWith (l.map K).prod (l.map f).prod
  | [] => by simpa using LipschitzWith.id
  | i::l => by
    simp only [List.map_cons, List.prod_cons]
    exact (h i).mul_end (LipschitzWith.list_prod f K h l)
#align lipschitz_with.list_prod LipschitzWith.list_prod

protected theorem pow_end {f : Function.End α} {K} (h : LipschitzWith K f) :
    ∀ n : ℕ, LipschitzWith (K ^ n) (f ^ n : Function.End α)
  | 0 => by simpa only [pow_zero] using LipschitzWith.id
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact h.mul_end (LipschitzWith.pow_end h n)
#align lipschitz_with.pow LipschitzWith.pow_end

end EMetric

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ] {K : ℝ≥0} {f : α → β}
  {x y : α} {r : ℝ}

protected theorem of_dist_le' {K : ℝ} (h : ∀ x y, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  of_dist_le_mul fun x y =>
    le_trans (h x y) <| by gcongr; apply Real.le_coe_toNNReal
#align lipschitz_with.of_dist_le' LipschitzWith.of_dist_le'

protected theorem mk_one (h : ∀ x y, dist (f x) (f y) ≤ dist x y) : LipschitzWith 1 f :=
  of_dist_le_mul <| by simpa only [NNReal.coe_one, one_mul] using h
#align lipschitz_with.mk_one LipschitzWith.mk_one

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith (Real.toNNReal K) f :=
  have I : ∀ x y, f x - f y ≤ K * dist x y := fun x y => sub_le_iff_le_add'.2 (h x y)
  LipschitzWith.of_dist_le' fun x y => abs_sub_le_iff.2 ⟨I x y, dist_comm y x ▸ I y x⟩
#align lipschitz_with.of_le_add_mul' LipschitzWith.of_le_add_mul'

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0) (h : ∀ x y, f x ≤ f y + K * dist x y) :
    LipschitzWith K f := by simpa only [Real.toNNReal_coe] using LipschitzWith.of_le_add_mul' K h
#align lipschitz_with.of_le_add_mul LipschitzWith.of_le_add_mul

protected theorem of_le_add {f : α → ℝ} (h : ∀ x y, f x ≤ f y + dist x y) : LipschitzWith 1 f :=
  LipschitzWith.of_le_add_mul 1 <| by simpa only [NNReal.coe_one, one_mul]
#align lipschitz_with.of_le_add LipschitzWith.of_le_add

protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : LipschitzWith K f) (x y) :
    f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_trans (le_abs_self _) <| h.dist_le_mul x y
#align lipschitz_with.le_add_mul LipschitzWith.le_add_mul

protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
    LipschitzWith K f ↔ ∀ x y, f x ≤ f y + K * dist x y :=
  ⟨LipschitzWith.le_add_mul, LipschitzWith.of_le_add_mul K⟩
#align lipschitz_with.iff_le_add_mul LipschitzWith.iff_le_add_mul

theorem nndist_le (hf : LipschitzWith K f) (x y : α) : nndist (f x) (f y) ≤ K * nndist x y :=
  hf.dist_le_mul x y
#align lipschitz_with.nndist_le LipschitzWith.nndist_le

theorem dist_le_mul_of_le (hf : LipschitzWith K f) (hr : dist x y ≤ r) : dist (f x) (f y) ≤ K * r :=
  (hf.dist_le_mul x y).trans <| by gcongr
#align lipschitz_with.dist_le_mul_of_le LipschitzWith.dist_le_mul_of_le

theorem mapsTo_closedBall (hf : LipschitzWith K f) (x : α) (r : ℝ) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) (K * r)) := fun _y hy =>
  hf.dist_le_mul_of_le hy
#align lipschitz_with.maps_to_closed_ball LipschitzWith.mapsTo_closedBall

theorem dist_lt_mul_of_lt (hf : LipschitzWith K f) (hK : K ≠ 0) (hr : dist x y < r) :
    dist (f x) (f y) < K * r :=
  (hf.dist_le_mul x y).trans_lt <| (mul_lt_mul_left <| NNReal.coe_pos.2 hK.bot_lt).2 hr
#align lipschitz_with.dist_lt_mul_of_lt LipschitzWith.dist_lt_mul_of_lt

theorem mapsTo_ball (hf : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) (K * r)) := fun _y hy =>
  hf.dist_lt_mul_of_lt hK hy
#align lipschitz_with.maps_to_ball LipschitzWith.mapsTo_ball

/-- A Lipschitz continuous map is a locally bounded map. -/
def toLocallyBoundedMap (f : α → β) (hf : LipschitzWith K f) : LocallyBoundedMap α β :=
  LocallyBoundedMap.ofMapBounded f fun _s hs =>
    let ⟨C, hC⟩ := Metric.isBounded_iff.1 hs
    Metric.isBounded_iff.2 ⟨K * C, ball_image_iff.2 fun _x hx => ball_image_iff.2 fun _y hy =>
      hf.dist_le_mul_of_le (hC hx hy)⟩
#align lipschitz_with.to_locally_bounded_map LipschitzWith.toLocallyBoundedMap

@[simp]
theorem coe_toLocallyBoundedMap (hf : LipschitzWith K f) : ⇑(hf.toLocallyBoundedMap f) = f :=
  rfl
#align lipschitz_with.coe_to_locally_bounded_map LipschitzWith.coe_toLocallyBoundedMap

theorem comap_cobounded_le (hf : LipschitzWith K f) :
    comap f (Bornology.cobounded β) ≤ Bornology.cobounded α :=
  (hf.toLocallyBoundedMap f).2
#align lipschitz_with.comap_cobounded_le LipschitzWith.comap_cobounded_le

/-- The image of a bounded set under a Lipschitz map is bounded. -/
theorem isBounded_image (hf : LipschitzWith K f) {s : Set α} (hs : IsBounded s) :
    IsBounded (f '' s) :=
  hs.image (toLocallyBoundedMap f hf)
#align lipschitz_with.bounded_image LipschitzWith.isBounded_image

theorem diam_image_le (hf : LipschitzWith K f) (s : Set α) (hs : IsBounded s) :
    Metric.diam (f '' s) ≤ K * Metric.diam s :=
  Metric.diam_le_of_forall_dist_le (mul_nonneg K.coe_nonneg Metric.diam_nonneg) <|
    ball_image_iff.2 fun _x hx =>
      ball_image_iff.2 fun _y hy => hf.dist_le_mul_of_le <| Metric.dist_le_diam_of_mem hs hx hy
#align lipschitz_with.diam_image_le LipschitzWith.diam_image_le

protected theorem dist_left (y : α) : LipschitzWith 1 (dist · y) :=
  LipschitzWith.mk_one fun _ _ => dist_dist_dist_le_left _ _ _
#align lipschitz_with.dist_left LipschitzWith.dist_left

protected theorem dist_right (x : α) : LipschitzWith 1 (dist x) :=
  LipschitzWith.of_le_add fun _ _ => dist_triangle_right _ _ _
#align lipschitz_with.dist_right LipschitzWith.dist_right

protected theorem dist : LipschitzWith 2 (Function.uncurry <| @dist α _) := by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry LipschitzWith.dist_left LipschitzWith.dist_right
#align lipschitz_with.dist LipschitzWith.dist

theorem dist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    dist (f^[n] x) (f^[n + 1] x) ≤ dist x (f x) * (K : ℝ) ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [NNReal.coe_pow] using (hf.iterate n).dist_le_mul x (f x)
#align lipschitz_with.dist_iterate_succ_le_geometric LipschitzWith.dist_iterate_succ_le_geometric

theorem _root_.lipschitzWith_max : LipschitzWith 1 fun p : ℝ × ℝ => max p.1 p.2 :=
  LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1 <|
    (le_abs_self _).trans (abs_max_sub_max_le_max _ _ _ _)
#align lipschitz_with_max lipschitzWith_max

theorem _root_.lipschitzWith_min : LipschitzWith 1 fun p : ℝ × ℝ => min p.1 p.2 :=
  LipschitzWith.of_le_add fun _ _ => sub_le_iff_le_add'.1 <|
    (le_abs_self _).trans (abs_min_sub_min_le_max _ _ _ _)
#align lipschitz_with_min lipschitzWith_min

end Metric

section EMetric

variable [PseudoEMetricSpace α] {f g : α → ℝ} {Kf Kg : ℝ≥0}

protected theorem max (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => max (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using lipschitzWith_max.comp (hf.prod hg)
#align lipschitz_with.max LipschitzWith.max

protected theorem min (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g) :
    LipschitzWith (max Kf Kg) fun x => min (f x) (g x) := by
  simpa only [(· ∘ ·), one_mul] using lipschitzWith_min.comp (hf.prod hg)
#align lipschitz_with.min LipschitzWith.min

theorem max_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max (f x) a := by
  simpa only [max_eq_left (zero_le Kf)] using hf.max (LipschitzWith.const a)
#align lipschitz_with.max_const LipschitzWith.max_const

theorem const_max (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => max a (f x) := by
  simpa only [max_comm] using hf.max_const a
#align lipschitz_with.const_max LipschitzWith.const_max

theorem min_const (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min (f x) a := by
  simpa only [max_eq_left (zero_le Kf)] using hf.min (LipschitzWith.const a)
#align lipschitz_with.min_const LipschitzWith.min_const

theorem const_min (hf : LipschitzWith Kf f) (a : ℝ) : LipschitzWith Kf fun x => min a (f x) := by
  simpa only [min_comm] using hf.min_const a
#align lipschitz_with.const_min LipschitzWith.const_min

end EMetric

protected theorem projIcc {a b : ℝ} (h : a ≤ b) : LipschitzWith 1 (projIcc a b h) :=
  ((LipschitzWith.id.const_min _).const_max _).subtype_mk _
#align lipschitz_with.proj_Icc LipschitzWith.projIcc

end LipschitzWith

namespace Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {s : Set α} {t : Set β}

#align metric.bounded.left_of_prod Bornology.IsBounded.fst_of_prod
#align metric.bounded.right_of_prod Bornology.IsBounded.snd_of_prod
#align metric.bounded_prod_of_nonempty Bornology.isBounded_prod_of_nonempty
#align metric.bounded_prod Bornology.isBounded_prod

end Metric

namespace LipschitzOnWith

section EMetric

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

variable {K : ℝ≥0} {s : Set α} {f : α → β}

protected theorem uniformContinuousOn (hf : LipschitzOnWith K f s) : UniformContinuousOn f s :=
  uniformContinuousOn_iff_restrict.mpr (lipschitzOnWith_iff_restrict.mp hf).uniformContinuous
#align lipschitz_on_with.uniform_continuous_on LipschitzOnWith.uniformContinuousOn

protected theorem continuousOn (hf : LipschitzOnWith K f s) : ContinuousOn f s :=
  hf.uniformContinuousOn.continuousOn
#align lipschitz_on_with.continuous_on LipschitzOnWith.continuousOn

theorem edist_le_mul_of_le (h : LipschitzOnWith K f s) (hx : x ∈ s) (hy : y ∈ s)
    (hr : edist x y ≤ r) :
    edist (f x) (f y) ≤ K * r :=
  (h hx hy).trans <| ENNReal.mul_left_mono hr

theorem edist_lt_of_edist_lt_div (hf : LipschitzOnWith K f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    {d : ℝ≥0∞} (hd : edist x y < d / K) : edist (f x) (f y) < d :=
   hf.to_restrict.edist_lt_of_edist_lt_div <|
    show edist (⟨x, hx⟩ : s) ⟨y, hy⟩ < d / K from hd
#align lipschitz_on_with.edist_lt_of_edist_lt_div LipschitzOnWith.edist_lt_of_edist_lt_div

protected theorem comp {g : β → γ} {t : Set β} {Kg : ℝ≥0} (hg : LipschitzOnWith Kg g t)
    (hf : LipschitzOnWith K f s) (hmaps : MapsTo f s t) : LipschitzOnWith (Kg * K) (g ∘ f) s :=
  lipschitzOnWith_iff_restrict.mpr <| hg.to_restrict.comp (hf.to_restrict_mapsTo hmaps)
#align lipschitz_on_with.comp LipschitzOnWith.comp

/-- If `f` and `g` are Lipschitz on `s`, so is the induced map `f × g` to the product type. -/
protected theorem prod {g : α → γ} {Kf Kg : ℝ≥0} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (max Kf Kg) (fun x => (f x, g x)) s := by
  intro _ hx _ hy
  rw [ENNReal.coe_mono.map_max, Prod.edist_eq, ENNReal.max_mul]
  exact max_le_max (hf hx hy) (hg hx hy)

theorem ediam_image2_le (f : α → β → γ) {K₁ K₂ : ℝ≥0} (s : Set α) (t : Set β)
    (hf₁ : ∀ b ∈ t, LipschitzOnWith K₁ (fun a => f a b) s)
    (hf₂ : ∀ a ∈ s, LipschitzOnWith K₂ (f a) t) :
    EMetric.diam (Set.image2 f s t) ≤ ↑K₁ * EMetric.diam s + ↑K₂ * EMetric.diam t := by
  apply EMetric.diam_le
  rintro _ ⟨a₁, b₁, ha₁, hb₁, rfl⟩ _ ⟨a₂, b₂, ha₂, hb₂, rfl⟩
  refine' (edist_triangle _ (f a₂ b₁) _).trans _
  exact
    add_le_add
      ((hf₁ b₁ hb₁ ha₁ ha₂).trans <| ENNReal.mul_left_mono <| EMetric.edist_le_diam_of_mem ha₁ ha₂)
      ((hf₂ a₂ ha₂ hb₁ hb₂).trans <| ENNReal.mul_left_mono <| EMetric.edist_le_diam_of_mem hb₁ hb₂)
#align lipschitz_on_with.ediam_image2_le LipschitzOnWith.ediam_image2_le

end EMetric

section Metric

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [PseudoMetricSpace γ]

variable {K : ℝ≥0} {s : Set α} {f : α → β}

protected theorem of_dist_le' {K : ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ K * dist x y) :
    LipschitzOnWith (Real.toNNReal K) f s :=
  of_dist_le_mul fun x hx y hy =>
    le_trans (h x hx y hy) <| by gcongr; apply Real.le_coe_toNNReal
#align lipschitz_on_with.of_dist_le' LipschitzOnWith.of_dist_le'

protected theorem mk_one (h : ∀ x ∈ s, ∀ y ∈ s, dist (f x) (f y) ≤ dist x y) :
    LipschitzOnWith 1 f s :=
  of_dist_le_mul <| by simpa only [NNReal.coe_one, one_mul] using h
#align lipschitz_on_with.mk_one LipschitzOnWith.mk_one

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
doesn't assume `0≤K`. -/
protected theorem of_le_add_mul' {f : α → ℝ} (K : ℝ)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y) : LipschitzOnWith (Real.toNNReal K) f s :=
  have I : ∀ x ∈ s, ∀ y ∈ s, f x - f y ≤ K * dist x y := fun x hx y hy =>
    sub_le_iff_le_add'.2 (h x hx y hy)
  LipschitzOnWith.of_dist_le' fun x hx y hy =>
    abs_sub_le_iff.2 ⟨I x hx y hy, dist_comm y x ▸ I y hy x hx⟩
#align lipschitz_on_with.of_le_add_mul' LipschitzOnWith.of_le_add_mul'

/-- For functions to `ℝ`, it suffices to prove `f x ≤ f y + K * dist x y`; this version
assumes `0≤K`. -/
protected theorem of_le_add_mul {f : α → ℝ} (K : ℝ≥0)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y) : LipschitzOnWith K f s := by
  simpa only [Real.toNNReal_coe] using LipschitzOnWith.of_le_add_mul' K h
#align lipschitz_on_with.of_le_add_mul LipschitzOnWith.of_le_add_mul

protected theorem of_le_add {f : α → ℝ} (h : ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + dist x y) :
    LipschitzOnWith 1 f s :=
  LipschitzOnWith.of_le_add_mul 1 <| by simpa only [NNReal.coe_one, one_mul]
#align lipschitz_on_with.of_le_add LipschitzOnWith.of_le_add

protected theorem le_add_mul {f : α → ℝ} {K : ℝ≥0} (h : LipschitzOnWith K f s) {x : α} (hx : x ∈ s)
    {y : α} (hy : y ∈ s) : f x ≤ f y + K * dist x y :=
  sub_le_iff_le_add'.1 <| le_trans (le_abs_self _) <| h.dist_le_mul x hx y hy
#align lipschitz_on_with.le_add_mul LipschitzOnWith.le_add_mul

protected theorem iff_le_add_mul {f : α → ℝ} {K : ℝ≥0} :
    LipschitzOnWith K f s ↔ ∀ x ∈ s, ∀ y ∈ s, f x ≤ f y + K * dist x y :=
  ⟨LipschitzOnWith.le_add_mul, LipschitzOnWith.of_le_add_mul K⟩
#align lipschitz_on_with.iff_le_add_mul LipschitzOnWith.iff_le_add_mul

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
#align lipschitz_on_with.bounded_image2 LipschitzOnWith.isBounded_image2

end Metric

end LipschitzOnWith

namespace LocallyLipschitz
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : α → β}

/-- A Lipschitz function is locally Lipschitz. -/
protected lemma _root_.LipschitzWith.locallyLipschitz {K : ℝ≥0} (hf : LipschitzWith K f) :
    LocallyLipschitz f :=
  fun _ ↦ ⟨K, univ, Filter.univ_mem, lipschitzOn_univ.mpr hf⟩

/-- The identity function is locally Lipschitz. -/
protected lemma id : LocallyLipschitz (@id α) := LipschitzWith.id.locallyLipschitz

/-- Constant functions are locally Lipschitz. -/
protected lemma const (b : β) : LocallyLipschitz (fun _ : α ↦ b) :=
  (LipschitzWith.const b).locallyLipschitz

/-- A locally Lipschitz function is continuous. (The converse is false: for example,
$x ↦ \sqrt{x}$ is continuous, but not locally Lipschitz at 0.) -/
protected theorem continuous {f : α → β} (hf : LocallyLipschitz f) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  rcases (hf x) with ⟨K, t, ht, hK⟩
  exact (hK.continuousOn).continuousAt ht

/-- The composition of locally Lipschitz functions is locally Lipschitz. --/
protected lemma comp  {f : β → γ} {g : α → β}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f ∘ g) := by
  intro x
  -- g is Lipschitz on t ∋ x, f is Lipschitz on u ∋ g(x)
  rcases hg x with ⟨Kg, t, ht, hgL⟩
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  refine ⟨Kf * Kg, t ∩ g⁻¹' u, inter_mem ht (hg.continuous.continuousAt hu), ?_⟩
  exact hfL.comp (hgL.mono (inter_subset_left _ _))
    ((mapsTo_preimage g u).mono_left (inter_subset_right _ _))

/-- If `f` and `g` are locally Lipschitz, so is the induced map `f × g` to the product type. -/
protected lemma prod {f : α → β} (hf : LocallyLipschitz f) {g : α → γ} (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => (f x, g x) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  refine ⟨max Kf Kg, t₁ ∩ t₂, Filter.inter_mem h₁t h₂t, ?_⟩
  exact (hfL.mono (inter_subset_left t₁ t₂)).prod (hgL.mono (inter_subset_right t₁ t₂))

protected theorem prod_mk_left (a : α) : LocallyLipschitz (Prod.mk a : β → α × β) :=
  (LipschitzWith.prod_mk_left a).locallyLipschitz

protected theorem prod_mk_right (b : β) : LocallyLipschitz (fun a : α => (a, b)) :=
  (LipschitzWith.prod_mk_right b).locallyLipschitz

protected theorem iterate {f : α → α} (hf : LocallyLipschitz f) : ∀ n, LocallyLipschitz f^[n]
  | 0 => by simpa only [pow_zero] using LocallyLipschitz.id
  | n + 1 => by rw [iterate_add, iterate_one]; exact (hf.iterate n).comp hf

protected theorem mul_end {f g : Function.End α} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g) : LocallyLipschitz (f * g : Function.End α) := hf.comp hg

protected theorem pow_end {f : Function.End α} (h : LocallyLipschitz f) :
    ∀ n : ℕ, LocallyLipschitz (f ^ n : Function.End α)
  | 0 => by simpa only [pow_zero] using LocallyLipschitz.id
  | n + 1 => by
    rw [pow_succ]
    exact h.mul_end (h.pow_end n)

section Real
variable {f g : α → ℝ}
/-- The minimum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma min (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => min (f x) (g x)) :=
  lipschitzWith_min.locallyLipschitz.comp (hf.prod hg)

/-- The maximum of locally Lipschitz functions is locally Lipschitz. -/
protected lemma max (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz (fun x => max (f x) (g x)) :=
  lipschitzWith_max.locallyLipschitz.comp (hf.prod hg)

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

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical fiber”
`{a} × t`, `a ∈ s`, and is Lipschitz continuous on each “horizontal fiber” `s × {b}`, `b ∈ t`
with the same Lipschitz constant `K`. Then it is continuous on `s × t`. Moreover, it suffices
to require continuity on vertical fibers for `a` from a subset `s' ⊆ s` that is dense in `s`.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s s' : Set α} {t : Set β}
    (hs' : s' ⊆ s) (hss' : s ⊆ closure s') (K : ℝ≥0)
    (ha : ∀ a ∈ s', ContinuousOn (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) := by
  rintro ⟨x, y⟩ ⟨hx : x ∈ s, hy : y ∈ t⟩
  refine' EMetric.nhds_basis_closed_eball.tendsto_right_iff.2 fun ε (ε0 : 0 < ε) => _
  replace ε0 : 0 < ε / 2 := ENNReal.half_pos ε0.ne'
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) * ↑(3 * K) < ε / 2 :=
    ENNReal.exists_nnreal_pos_mul_lt ENNReal.coe_ne_top ε0.ne'
  rw [← ENNReal.coe_pos] at δpos
  rcases EMetric.mem_closure_iff.1 (hss' hx) δ δpos with ⟨x', hx', hxx'⟩
  have A : s ∩ EMetric.ball x δ ∈ 𝓝[s] x :=
    inter_mem_nhdsWithin _ (EMetric.ball_mem_nhds _ δpos)
  have B : t ∩ { b | edist (f (x', b)) (f (x', y)) ≤ ε / 2 } ∈ 𝓝[t] y :=
    inter_mem self_mem_nhdsWithin (ha x' hx' y hy (EMetric.closedBall_mem_nhds (f (x', y)) ε0))
  filter_upwards [nhdsWithin_prod A B] with ⟨a, b⟩ ⟨⟨has, hax⟩, ⟨hbt, hby⟩⟩
  calc
    edist (f (a, b)) (f (x, y)) ≤ edist (f (a, b)) (f (x', b)) + edist (f (x', b)) (f (x', y)) +
        edist (f (x', y)) (f (x, y)) := edist_triangle4 _ _ _ _
    _ ≤ K * (δ + δ) + ε / 2 + K * δ := by
      gcongr
      · refine (hb b hbt).edist_le_mul_of_le has (hs' hx') ?_
        refine (edist_triangle _ _ _).trans (add_le_add (le_of_lt hax) hxx'.le)
      · exact hby
      · exact (hb y hy).edist_le_mul_of_le (hs' hx') hx ((edist_comm _ _).trans_le hxx'.le)
    _ = δ * ↑(3 * K) + ε / 2 := by push_cast; ring
    _ ≤ ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves _

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical fiber”
`{a} × t`, `a ∈ s`, and is Lipschitz continuous on each “horizontal fiber” `s × {b}`, `b ∈ t`
with the same Lipschitz constant `K`. Then it is continuous on `s × t`.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
theorem continuousOn_prod_of_continuousOn_lipschitzOnWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s : Set α} {t : Set β} (K : ℝ≥0)
    (ha : ∀ a ∈ s, ContinuousOn (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
    f Subset.rfl subset_closure K ha hb
#align continuous_on_prod_of_continuous_on_lipschitz_on continuousOn_prod_of_continuousOn_lipschitzOnWith

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical section”
`{a} × univ` for `a : α` from a dense set. Suppose that it is Lipschitz continuous on each
“horizontal section” `univ × {b}`, `b : β` with the same Lipschitz constant `K`. Then it is
continuous.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
theorem continuous_prod_of_dense_continuous_lipschitzWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) {s : Set α}
    (hs : Dense s) (ha : ∀ a ∈ s, Continuous fun y => f (a, y))
    (hb : ∀ b, LipschitzWith K fun x => f (x, b)) : Continuous f := by
  simp only [continuous_iff_continuousOn_univ, ← univ_prod_univ, ← lipschitzOn_univ] at *
  exact continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith f (subset_univ _)
    hs.closure_eq.ge K ha fun b _ => hb b

/-- Consider a function `f : α × β → γ`. Suppose that it is continuous on each “vertical section”
`{a} × univ`, `a : α`, and is Lipschitz continuous on each “horizontal section”
`univ × {b}`, `b : β` with the same Lipschitz constant `K`. Then it is continuous.

The actual statement uses (Lipschitz) continuity of `fun y ↦ f (a, y)` and `fun x ↦ f (x, b)`
instead of continuity of `f` on subsets of the product space. -/
theorem continuous_prod_of_continuous_lipschitzWith [PseudoEMetricSpace α] [TopologicalSpace β]
    [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) (ha : ∀ a, Continuous fun y => f (a, y))
    (hb : ∀ b, LipschitzWith K fun x => f (x, b)) : Continuous f :=
  continuous_prod_of_dense_continuous_lipschitzWith f K dense_univ (fun _ _ ↦ ha _) hb
#align continuous_prod_of_continuous_lipschitz continuous_prod_of_continuous_lipschitzWith

open Metric

/-- If a function is locally Lipschitz around a point, then it is continuous at this point. -/
theorem continuousAt_of_locally_lipschitz [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}
    {x : α} {r : ℝ} (hr : 0 < r) (K : ℝ) (h : ∀ y, dist y x < r → dist (f y) (f x) ≤ K * dist y x) :
    ContinuousAt f x := by
  -- We use `h` to squeeze `dist (f y) (f x)` between `0` and `K * dist y x`
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (eventually_of_forall fun _ => dist_nonneg)
    (mem_of_superset (ball_mem_nhds _ hr) h) ?_)
  -- Then show that `K * dist y x` tends to zero as `y → x`
  refine (continuous_const.mul (continuous_id.dist continuous_const)).tendsto' _ _ ?_
  simp
#align continuous_at_of_locally_lipschitz continuousAt_of_locally_lipschitz

/-- A function `f : α → ℝ` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz extension
to the whole space. -/
theorem LipschitzOnWith.extend_real [PseudoMetricSpace α] {f : α → ℝ} {s : Set α} {K : ℝ≥0}
    (hf : LipschitzOnWith K f s) : ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn f g s := by
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
    refine' ⟨f z - K * dist y z, _⟩
    rintro w ⟨t, rfl⟩
    dsimp
    rw [sub_le_iff_le_add, add_assoc, ← mul_add, add_comm (dist y t)]
    calc
      f z ≤ f t + K * dist z t := hf.le_add_mul hz t.2
      _ ≤ f t + K * (dist y z + dist y t) := by gcongr; apply dist_triangle_left
  have E : EqOn f g s := fun x hx => by
    refine' le_antisymm (le_ciInf fun y => hf.le_add_mul hx y.2) _
    simpa only [add_zero, Subtype.coe_mk, mul_zero, dist_self] using ciInf_le (B x) ⟨x, hx⟩
  refine' ⟨g, LipschitzWith.of_le_add_mul K fun x y => _, E⟩
  rw [← sub_le_iff_le_add]
  refine' le_ciInf fun z => _
  rw [sub_le_iff_le_add]
  calc
    g x ≤ f z + K * dist x z := ciInf_le (B x) _
    _ ≤ f z + K * dist y z + K * dist x y := by
      rw [add_assoc, ← mul_add, add_comm (dist y z)]
      gcongr
      apply dist_triangle
#align lipschitz_on_with.extend_real LipschitzOnWith.extend_real

/-- A function `f : α → (ι → ℝ)` which is `K`-Lipschitz on a subset `s` admits a `K`-Lipschitz
extension to the whole space. The same result for the space `ℓ^∞ (ι, ℝ)` over a possibly infinite
type `ι` is implemented in `LipschitzOnWith.extend_lp_infty`.-/
theorem LipschitzOnWith.extend_pi [PseudoMetricSpace α] [Fintype ι] {f : α → ι → ℝ} {s : Set α}
    {K : ℝ≥0} (hf : LipschitzOnWith K f s) : ∃ g : α → ι → ℝ, LipschitzWith K g ∧ EqOn f g s := by
  have : ∀ i, ∃ g : α → ℝ, LipschitzWith K g ∧ EqOn (fun x => f x i) g s := fun i => by
    have : LipschitzOnWith K (fun x : α => f x i) s :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        (dist_le_pi_dist _ _ i).trans (hf.dist_le_mul x hx y hy)
    exact this.extend_real
  choose g hg using this
  refine' ⟨fun x i => g i x, LipschitzWith.of_dist_le_mul fun x y => _, _⟩
  · exact (dist_pi_le_iff (mul_nonneg K.2 dist_nonneg)).2 fun i => (hg i).1.dist_le_mul x y
  · intro x hx
    ext1 i
    exact (hg i).2 hx
#align lipschitz_on_with.extend_pi LipschitzOnWith.extend_pi
