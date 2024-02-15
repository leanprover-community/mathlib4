/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Tactic.GCongr

#align_import topology.metric_space.lipschitz from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

/-- A function `f` is **Lipschitz continuous** with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y`. -/
def LipschitzWith [PseudoEMetricSpace α] [PseudoEMetricSpace β] (K : ℝ≥0) (f : α → β) :=
  ∀ x y, edist (f x) (f y) ≤ K * edist x y
#align lipschitz_with LipschitzWith

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

end LipschitzWith

namespace LipschitzOnWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

variable {K : ℝ≥0} {s : Set α} {f : α → β}

protected theorem uniformContinuousOn (hf : LipschitzOnWith K f s) : UniformContinuousOn f s :=
  uniformContinuousOn_iff_restrict.mpr (lipschitzOnWith_iff_restrict.mp hf).uniformContinuous
#align lipschitz_on_with.uniform_continuous_on LipschitzOnWith.uniformContinuousOn

protected theorem continuousOn (hf : LipschitzOnWith K f s) : ContinuousOn f s :=
  hf.uniformContinuousOn.continuousOn
#align lipschitz_on_with.continuous_on LipschitzOnWith.continuousOn

theorem edist_le_mul_of_le (h : LipschitzOnWith K f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    {r : ℝ≥0∞} (hr : edist x y ≤ r) :
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
    (hf₁ : ∀ b ∈ t, LipschitzOnWith K₁ (f · b) s) (hf₂ : ∀ a ∈ s, LipschitzOnWith K₂ (f a) t) :
    EMetric.diam (Set.image2 f s t) ≤ ↑K₁ * EMetric.diam s + ↑K₂ * EMetric.diam t := by
  simp only [EMetric.diam_le_iff, forall_image2_iff]
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
  refine (edist_triangle _ (f a₂ b₁) _).trans ?_
  exact
    add_le_add
      ((hf₁ b₁ hb₁ ha₁ ha₂).trans <| ENNReal.mul_left_mono <| EMetric.edist_le_diam_of_mem ha₁ ha₂)
      ((hf₂ a₂ ha₂ hb₁ hb₂).trans <| ENNReal.mul_left_mono <| EMetric.edist_le_diam_of_mem hb₁ hb₂)
#align lipschitz_on_with.ediam_image2_le LipschitzOnWith.ediam_image2_le

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
