/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov, Winston Yin
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Finiteness
public import Mathlib.Topology.EMetricSpace.Diam

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
* `LocallyLipschitzOn f s`: states that `f` is locally Lipschitz on `s`.
* `LocallyLipschitz.continuous`: a locally Lipschitz function is continuous.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

@[expose] public section

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

section PseudoEMetricSpace
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {s t : Set α} {f : α → β}

/-- A function `f` is **Lipschitz continuous** with constant `K ≥ 0` if for all `x, y`
we have `dist (f x) (f y) ≤ K * dist x y`. -/
def LipschitzWith (K : ℝ≥0) (f : α → β) := ∀ x y, edist (f x) (f y) ≤ K * edist x y

/-- A function `f` is **Lipschitz continuous** with constant `K ≥ 0` **on `s`** if
for all `x, y` in `s` we have `dist (f x) (f y) ≤ K * dist x y`. -/
def LipschitzOnWith (K : ℝ≥0) (f : α → β) (s : Set α) :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → edist (f x) (f y) ≤ K * edist x y

/-- `f : α → β` is called **locally Lipschitz continuous** iff every point `x`
has a neighbourhood on which `f` is Lipschitz. -/
def LocallyLipschitz (f : α → β) : Prop := ∀ x, ∃ K, ∃ t ∈ 𝓝 x, LipschitzOnWith K f t

/-- `f : α → β` is called **locally Lipschitz continuous** on `s` iff every point `x` of `s`
has a neighbourhood within `s` on which `f` is Lipschitz. -/
def LocallyLipschitzOn (s : Set α) (f : α → β) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∃ K, ∃ t ∈ 𝓝[s] x, LipschitzOnWith K f t

/-- Every function is Lipschitz on the empty set (with any Lipschitz constant). -/
@[simp]
theorem lipschitzOnWith_empty (K : ℝ≥0) (f : α → β) : LipschitzOnWith K f ∅ := fun _ => False.elim

@[simp] lemma locallyLipschitzOn_empty (f : α → β) : LocallyLipschitzOn ∅ f := fun _ ↦ False.elim

/-- Being Lipschitz on a set is monotone w.r.t. that set. -/
theorem LipschitzOnWith.mono (hf : LipschitzOnWith K f t) (h : s ⊆ t) : LipschitzOnWith K f s :=
  fun _x x_in _y y_in => hf (h x_in) (h y_in)

lemma LocallyLipschitzOn.mono (hf : LocallyLipschitzOn t f) (h : s ⊆ t) : LocallyLipschitzOn s f :=
  fun x hx ↦ by obtain ⟨K, u, hu, hfu⟩ := hf (h hx); exact ⟨K, u, nhdsWithin_mono _ h hu, hfu⟩

/-- `f` is Lipschitz iff it is Lipschitz on the entire space. -/
@[simp] lemma lipschitzOnWith_univ : LipschitzOnWith K f univ ↔ LipschitzWith K f := by
  simp [LipschitzOnWith, LipschitzWith]

@[simp] lemma locallyLipschitzOn_univ : LocallyLipschitzOn univ f ↔ LocallyLipschitz f := by
  simp [LocallyLipschitzOn, LocallyLipschitz]

protected lemma LocallyLipschitz.locallyLipschitzOn (h : LocallyLipschitz f) :
    LocallyLipschitzOn s f := (locallyLipschitzOn_univ.2 h).mono s.subset_univ

theorem lipschitzOnWith_iff_restrict : LipschitzOnWith K f s ↔ LipschitzWith K (s.restrict f) := by
  simp [LipschitzOnWith, LipschitzWith]

lemma lipschitzOnWith_restrict {t : Set s} :
    LipschitzOnWith K (s.restrict f) t ↔ LipschitzOnWith K f (s ∩ Subtype.val '' t) := by
  simp [LipschitzOnWith]

lemma locallyLipschitzOn_iff_restrict :
    LocallyLipschitzOn s f ↔ LocallyLipschitz (s.restrict f) := by
  simp only [LocallyLipschitzOn, LocallyLipschitz, SetCoe.forall',
    lipschitzOnWith_restrict,
    nhds_subtype_eq_comap_nhdsWithin, mem_comap]
  congr! with x K
  constructor
  · rintro ⟨t, ht, hft⟩
    exact ⟨_, ⟨t, ht, Subset.rfl⟩, hft.mono <| inter_subset_right.trans <| image_preimage_subset ..⟩
  · rintro ⟨t, ⟨u, hu, hut⟩, hft⟩
    exact ⟨s ∩ u, Filter.inter_mem self_mem_nhdsWithin hu,
      hft.mono fun x hx ↦ ⟨hx.1, ⟨x, hx.1⟩, hut hx.2, rfl⟩⟩

alias ⟨LipschitzOnWith.to_restrict, _⟩ := lipschitzOnWith_iff_restrict
alias ⟨LocallyLipschitzOn.restrict, _⟩ := locallyLipschitzOn_iff_restrict

lemma Set.MapsTo.lipschitzOnWith_iff_restrict {t : Set β} (h : MapsTo f s t) :
    LipschitzOnWith K f s ↔ LipschitzWith K (h.restrict f s t) :=
  _root_.lipschitzOnWith_iff_restrict

alias ⟨LipschitzOnWith.mapsToRestrict, _⟩ := Set.MapsTo.lipschitzOnWith_iff_restrict

@[deprecated (since := "2025-09-05")]
alias LipschitzOnWith.to_restric_mapsTo := LipschitzOnWith.mapsToRestrict

end PseudoEMetricSpace

namespace LipschitzWith

open Metric

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : ℝ≥0} {f : α → β} {x y : α} {r : ℝ≥0∞} {s : Set α}

protected theorem lipschitzOnWith (h : LipschitzWith K f) : LipschitzOnWith K f s :=
  fun x _ y _ => h x y

theorem edist_le_mul (h : LipschitzWith K f) (x y : α) : edist (f x) (f y) ≤ K * edist x y :=
  h x y

theorem edist_le_mul_of_le (h : LipschitzWith K f) (hr : edist x y ≤ r) :
    edist (f x) (f y) ≤ K * r :=
  (h x y).trans <| mul_right_mono hr

theorem edist_lt_mul_of_lt (h : LipschitzWith K f) (hK : K ≠ 0) (hr : edist x y < r) :
    edist (f x) (f y) < K * r := by grw [h x y]; gcongr; simp

theorem mapsTo_closedEBall (h : LipschitzWith K f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (closedEBall x r) (closedEBall (f x) (K * r)) := fun _y hy => h.edist_le_mul_of_le hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

theorem mapsTo_eball (h : LipschitzWith K f) (hK : K ≠ 0) (x : α) (r : ℝ≥0∞) :
    MapsTo f (eball x r) (eball (f x) (K * r)) := fun _y hy => h.edist_lt_mul_of_lt hK hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

theorem edist_lt_top (hf : LipschitzWith K f) {x y : α} (h : edist x y ≠ ⊤) :
    edist (f x) (f y) < ⊤ :=
  (hf x y).trans_lt (by finiteness)

theorem mul_edist_le (h : LipschitzWith K f) (x y : α) :
    (K⁻¹ : ℝ≥0∞) * edist (f x) (f y) ≤ edist x y := by
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (h x y)

protected theorem of_edist_le (h : ∀ x y, edist (f x) (f y) ≤ edist x y) : LipschitzWith 1 f :=
  fun x y => by simp only [ENNReal.coe_one, one_mul, h]

protected theorem weaken (hf : LipschitzWith K f) {K' : ℝ≥0} (h : K ≤ K') : LipschitzWith K' f :=
  fun x y => le_trans (hf x y) <| mul_left_mono (ENNReal.coe_le_coe.2 h)

theorem ediam_image_le (hf : LipschitzWith K f) (s : Set α) :
    Metric.ediam (f '' s) ≤ K * Metric.ediam s := by
  apply Metric.ediam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.edist_le_mul_of_le (Metric.edist_le_ediam_of_mem hx hy)

theorem edist_lt_of_edist_lt_div (hf : LipschitzWith K f) {x y : α} {d : ℝ≥0∞}
    (h : edist x y < d / K) : edist (f x) (f y) < d :=
  calc
    edist (f x) (f y) ≤ K * edist x y := hf x y
    _ < d := ENNReal.mul_lt_of_lt_div' h

/-- A Lipschitz function is uniformly continuous. -/
protected theorem uniformContinuous (hf : LipschitzWith K f) : UniformContinuous f :=
  EMetric.uniformContinuous_iff.2 fun ε εpos =>
    ⟨ε / K, ENNReal.div_pos_iff.2 ⟨ne_of_gt εpos, ENNReal.coe_ne_top⟩, hf.edist_lt_of_edist_lt_div⟩

/-- A Lipschitz function is continuous. -/
protected theorem continuous (hf : LipschitzWith K f) : Continuous f :=
  hf.uniformContinuous.continuous

/-- Constant functions are Lipschitz (with any constant). -/
protected theorem const (b : β) : LipschitzWith 0 fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]

protected theorem const' (b : β) {K : ℝ≥0} : LipschitzWith K fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]

@[simp]
lemma zero_iff {β : Type*} [EMetricSpace β] (f : α → β) : LipschitzWith 0 f ↔ ∀ x y, f x = f y := by
  simp [LipschitzWith]

/-- The identity is 1-Lipschitz. -/
protected theorem id : LipschitzWith 1 (@id α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl

/-- The inclusion of a subset is 1-Lipschitz. -/
protected theorem subtype_val (s : Set α) : LipschitzWith 1 (Subtype.val : s → α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl

theorem subtype_mk (hf : LipschitzWith K f) {p : β → Prop} (hp : ∀ x, p (f x)) :
    LipschitzWith K (fun x => ⟨f x, hp x⟩ : α → { y // p y }) :=
  hf

protected theorem eval {α : ι → Type u} [∀ i, PseudoEMetricSpace (α i)] [Fintype ι] (i : ι) :
    LipschitzWith 1 (Function.eval i : (∀ i, α i) → α i) :=
  LipschitzWith.of_edist_le fun f g => by convert edist_le_pi_edist f g i

/-- The restriction of a `K`-Lipschitz function is `K`-Lipschitz. -/
protected theorem restrict (hf : LipschitzWith K f) (s : Set α) : LipschitzWith K (s.restrict f) :=
  fun x y => hf x y

/-- The composition of Lipschitz functions is Lipschitz. -/
protected theorem comp {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f ∘ g) := fun x y =>
  calc
    edist (f (g x)) (f (g y)) ≤ Kf * edist (g x) (g y) := hf _ _
    _ ≤ Kf * (Kg * edist x y) := mul_right_mono (hg _ _)
    _ = (Kf * Kg : ℝ≥0) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]

theorem comp_lipschitzOnWith {Kf Kg : ℝ≥0} {f : β → γ} {g : α → β} {s : Set α}
    (hf : LipschitzWith Kf f) (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf * Kg) (f ∘ g) s :=
  lipschitzOnWith_iff_restrict.mpr <| hf.comp hg.to_restrict

protected theorem prod_fst : LipschitzWith 1 (@Prod.fst α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_left _ _

protected theorem prod_snd : LipschitzWith 1 (@Prod.snd α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_right _ _

/-- If `f` and `g` are Lipschitz functions, so is the induced map `f × g` to the product type. -/
protected theorem prodMk {f : α → β} {Kf : ℝ≥0} (hf : LipschitzWith Kf f) {g : α → γ} {Kg : ℝ≥0}
    (hg : LipschitzWith Kg g) : LipschitzWith (max Kf Kg) fun x => (f x, g x) := by
  intro x y
  rw [ENNReal.coe_mono.map_max, Prod.edist_eq, max_mul]
  exact max_le_max (hf x y) (hg x y)

protected theorem prodMk_left (a : α) : LipschitzWith 1 (Prod.mk a : β → α × β) := by
  simpa only [max_eq_right zero_le_one] using (LipschitzWith.const a).prodMk LipschitzWith.id

protected theorem prodMk_right (b : β) : LipschitzWith 1 fun a : α => (a, b) := by
  simpa only [max_eq_left zero_le_one] using LipschitzWith.id.prodMk (LipschitzWith.const b)

protected theorem uncurry {f : α → β → γ} {Kα Kβ : ℝ≥0} (hα : ∀ b, LipschitzWith Kα fun a => f a b)
    (hβ : ∀ a, LipschitzWith Kβ (f a)) : LipschitzWith (Kα + Kβ) (Function.uncurry f) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [Function.uncurry, ENNReal.coe_add, add_mul]
  apply le_trans (edist_triangle _ (f a₂ b₁) _)
  exact
    add_le_add (le_trans (hα _ _ _) <| mul_right_mono <| le_max_left _ _)
      (le_trans (hβ _ _ _) <| mul_right_mono <| le_max_right _ _)

/-- Iterates of a Lipschitz function are Lipschitz. -/
protected theorem iterate {f : α → α} (hf : LipschitzWith K f) : ∀ n, LipschitzWith (K ^ n) f^[n]
  | 0 => by simpa only [pow_zero] using LipschitzWith.id
  | n + 1 => by rw [pow_succ]; exact (LipschitzWith.iterate hf n).comp hf

theorem edist_iterate_succ_le_geometric {f : α → α} (hf : LipschitzWith K f) (x n) :
    edist (f^[n] x) (f^[n + 1] x) ≤ edist x (f x) * (K : ℝ≥0∞) ^ n := by
  rw [iterate_succ, mul_comm]
  simpa only [ENNReal.coe_pow] using (hf.iterate n) x (f x)

protected theorem mul_end {f g : Function.End α} {Kf Kg} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f * g : Function.End α) :=
  hf.comp hg

/-- The product of a list of Lipschitz continuous endomorphisms is a Lipschitz continuous
endomorphism. -/
protected theorem list_prod (f : ι → Function.End α) (K : ι → ℝ≥0)
    (h : ∀ i, LipschitzWith (K i) (f i)) : ∀ l : List ι, LipschitzWith (l.map K).prod (l.map f).prod
  | [] => by simpa using LipschitzWith.id
  | i::l => by
    simp only [List.map_cons, List.prod_cons]
    exact (h i).mul_end (LipschitzWith.list_prod f K h l)

protected theorem pow_end {f : Function.End α} {K} (h : LipschitzWith K f) :
    ∀ n : ℕ, LipschitzWith (K ^ n) (f ^ n : Function.End α)
  | 0 => by simpa only [pow_zero] using LipschitzWith.id
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (LipschitzWith.pow_end h n).mul_end h

end LipschitzWith

namespace LipschitzOnWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : ℝ≥0} {s : Set α} {f : α → β}

@[simp]
lemma zero_iff {β : Type*} [EMetricSpace β] (f : α → β) :
    LipschitzOnWith 0 f s ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y := by
  simp [LipschitzOnWith]

protected theorem uniformContinuousOn (hf : LipschitzOnWith K f s) : UniformContinuousOn f s :=
  uniformContinuousOn_iff_restrict.mpr hf.to_restrict.uniformContinuous

protected theorem continuousOn (hf : LipschitzOnWith K f s) : ContinuousOn f s :=
  hf.uniformContinuousOn.continuousOn

protected theorem weaken (hf : LipschitzOnWith K f s) {K' : ℝ≥0} (h : K ≤ K') :
    LipschitzOnWith K' f s :=
  fun _ hx _ hy => (hf hx hy).trans <| mul_left_mono (ENNReal.coe_le_coe.2 h)

theorem edist_le_mul_of_le (h : LipschitzOnWith K f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    {r : ℝ≥0∞} (hr : edist x y ≤ r) :
    edist (f x) (f y) ≤ K * r :=
  (h hx hy).trans <| mul_right_mono hr

theorem edist_lt_of_edist_lt_div (hf : LipschitzOnWith K f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    {d : ℝ≥0∞} (hd : edist x y < d / K) : edist (f x) (f y) < d :=
  hf.to_restrict.edist_lt_of_edist_lt_div <| show edist (⟨x, hx⟩ : s) ⟨y, hy⟩ < d / K from hd

protected theorem comp {g : β → γ} {t : Set β} {Kg : ℝ≥0} (hg : LipschitzOnWith Kg g t)
    (hf : LipschitzOnWith K f s) (hmaps : MapsTo f s t) : LipschitzOnWith (Kg * K) (g ∘ f) s :=
  lipschitzOnWith_iff_restrict.mpr <| hg.to_restrict.comp (hf.mapsToRestrict hmaps)

/-- If `f` and `g` are Lipschitz on `s`, so is the induced map `f × g` to the product type. -/
protected theorem prodMk {g : α → γ} {Kf Kg : ℝ≥0} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (max Kf Kg) (fun x => (f x, g x)) s := by
  intro _ hx _ hy
  rw [ENNReal.coe_mono.map_max, Prod.edist_eq, max_mul]
  exact max_le_max (hf hx hy) (hg hx hy)

theorem ediam_image2_le (f : α → β → γ) {K₁ K₂ : ℝ≥0} (s : Set α) (t : Set β)
    (hf₁ : ∀ b ∈ t, LipschitzOnWith K₁ (f · b) s) (hf₂ : ∀ a ∈ s, LipschitzOnWith K₂ (f a) t) :
    Metric.ediam (Set.image2 f s t) ≤ ↑K₁ * Metric.ediam s + ↑K₂ * Metric.ediam t := by
  simp only [Metric.ediam_le_iff, forall_mem_image2]
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
  refine (edist_triangle _ (f a₂ b₁) _).trans ?_
  exact
    add_le_add
      ((hf₁ b₁ hb₁ ha₁ ha₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem ha₁ ha₂)
      ((hf₂ a₂ ha₂ hb₁ hb₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem hb₁ hb₂)

end LipschitzOnWith

namespace LocallyLipschitz
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : α → β}

/-- A Lipschitz function is locally Lipschitz. -/
protected lemma _root_.LipschitzWith.locallyLipschitz {K : ℝ≥0} (hf : LipschitzWith K f) :
    LocallyLipschitz f :=
  fun _ ↦ ⟨K, univ, Filter.univ_mem, lipschitzOnWith_univ.mpr hf⟩

/-- The identity function is locally Lipschitz. -/
protected lemma id : LocallyLipschitz (@id α) := LipschitzWith.id.locallyLipschitz

/-- Constant functions are locally Lipschitz. -/
protected lemma const (b : β) : LocallyLipschitz (fun _ : α ↦ b) :=
  (LipschitzWith.const b).locallyLipschitz

/-- A locally Lipschitz function is continuous. (The converse is false: for example,
$x ↦ \sqrt{x}$ is continuous, but not locally Lipschitz at 0.) -/
protected theorem continuous {f : α → β} (hf : LocallyLipschitz f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases (hf x) with ⟨K, t, ht, hK⟩
  exact (hK.continuousOn).continuousAt ht

/-- The composition of locally Lipschitz functions is locally Lipschitz. -/
protected lemma comp {f : β → γ} {g : α → β}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f ∘ g) := by
  intro x
  -- g is Lipschitz on t ∋ x, f is Lipschitz on u ∋ g(x)
  rcases hg x with ⟨Kg, t, ht, hgL⟩
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  refine ⟨Kf * Kg, t ∩ g⁻¹' u, inter_mem ht (hg.continuous.continuousAt hu), ?_⟩
  exact hfL.comp (hgL.mono inter_subset_left)
    ((mapsTo_preimage g u).mono_left inter_subset_right)

/-- If `f` and `g` are locally Lipschitz, so is the induced map `f × g` to the product type. -/
protected lemma prodMk {f : α → β} (hf : LocallyLipschitz f) {g : α → γ} (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => (f x, g x) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  refine ⟨max Kf Kg, t₁ ∩ t₂, Filter.inter_mem h₁t h₂t, ?_⟩
  exact (hfL.mono inter_subset_left).prodMk (hgL.mono inter_subset_right)

protected theorem prodMk_left (a : α) : LocallyLipschitz (Prod.mk a : β → α × β) :=
  (LipschitzWith.prodMk_left a).locallyLipschitz

protected theorem prodMk_right (b : β) : LocallyLipschitz (fun a : α => (a, b)) :=
  (LipschitzWith.prodMk_right b).locallyLipschitz

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
    exact (h.pow_end n).mul_end h

end LocallyLipschitz

namespace LocallyLipschitzOn
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {f : α → β} {s : Set α}

protected lemma continuousOn (hf : LocallyLipschitzOn s f) : ContinuousOn f s :=
  continuousOn_iff_continuous_restrict.2 hf.restrict.continuous

end LocallyLipschitzOn

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
  refine Metric.nhds_basis_closedEBall.tendsto_right_iff.2 fun ε (ε0 : 0 < ε) => ?_
  replace ε0 : 0 < ε / 2 := ENNReal.half_pos ε0.ne'
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ : ℝ≥0, 0 < δ ∧ (δ : ℝ≥0∞) * ↑(3 * K) < ε / 2 :=
    ENNReal.exists_nnreal_pos_mul_lt ENNReal.coe_ne_top ε0.ne'
  rw [← ENNReal.coe_pos] at δpos
  rcases EMetric.mem_closure_iff.1 (hss' hx) δ δpos with ⟨x', hx', hxx'⟩
  have A : s ∩ Metric.eball x δ ∈ 𝓝[s] x :=
    inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ δpos)
  have B : t ∩ { b | edist (f (x', b)) (f (x', y)) ≤ ε / 2 } ∈ 𝓝[t] y :=
    inter_mem self_mem_nhdsWithin (ha x' hx' y hy (Metric.closedEBall_mem_nhds (f (x', y)) ε0))
  filter_upwards [nhdsWithin_prod A B] with ⟨a, b⟩ ⟨⟨has, hax⟩, ⟨hbt, hby⟩⟩
  calc
    edist (f (a, b)) (f (x, y)) ≤ edist (f (a, b)) (f (x', b)) + edist (f (x', b)) (f (x', y)) +
        edist (f (x', y)) (f (x, y)) := edist_triangle4 _ _ _ _
    _ ≤ K * (δ + δ) + ε / 2 + K * δ := by
      gcongr
      · refine (hb b hbt).edist_le_mul_of_le has (hs' hx') ?_
        exact (edist_triangle _ _ _).trans (add_le_add (le_of_lt hax) hxx'.le)
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
  simp only [← continuousOn_univ, ← univ_prod_univ, ← lipschitzOnWith_univ] at *
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

theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s : Set α} {t t' : Set β}
    (ht' : t' ⊆ t) (htt' : t ⊆ closure t') (K : ℝ≥0)
    (ha : ∀ a ∈ s, LipschitzOnWith K (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t', ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith _ ht' htt' K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

theorem continuousOn_prod_of_continuousOn_lipschitzOnWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) {s : Set α} {t : Set β} (K : ℝ≥0)
    (ha : ∀ a ∈ s, LipschitzOnWith K (fun y => f (a, y)) t)
    (hb : ∀ b ∈ t, ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

theorem continuous_prod_of_dense_continuous_lipschitzWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) {t : Set β}
    (ht : Dense t) (ha : ∀ a, LipschitzWith K fun y => f (a, y))
    (hb : ∀ b ∈ t, Continuous fun x => f (x, b)) : Continuous f :=
  have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_dense_continuous_lipschitzWith _ K ht hb ha
  this.comp continuous_swap

theorem continuous_prod_of_continuous_lipschitzWith' [TopologicalSpace α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] (f : α × β → γ) (K : ℝ≥0) (ha : ∀ a, LipschitzWith K fun y => f (a, y))
    (hb : ∀ b, Continuous fun x => f (x, b)) : Continuous f :=
  have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_continuous_lipschitzWith _ K hb ha
  this.comp continuous_swap
