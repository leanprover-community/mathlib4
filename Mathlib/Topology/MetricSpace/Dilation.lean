/-
Copyright (c) 2022 Hanting Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hanting Zhang
-/
module

public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Data.FunLike.Basic

/-!
# Dilations

We define dilations, i.e., maps between types with an extended distance that satisfy
`edist (f x) (f y) = r * edist x y` for some `r ∉ {0, ∞}`.

The value `r = 0` is not allowed because we want dilations of (e)metric spaces to be automatically
injective. The value `r = ∞` is not allowed because this way we can define `Dilation.ratio f : ℝ≥0`,
not `Dilation.ratio f : ℝ≥0∞`. Also, we do not often need maps sending distinct points to points at
infinite distance.

## Main definitions

* `Dilation.ratio f : ℝ≥0`: the value of `r` in the relation above, defaulting to 1 in the case
  where it is not well-defined.

## Notation

- `α →ᵈ β`: notation for `Dilation α β`.

## Implementation notes

The type of dilations defined in this file are also referred to as "similarities" or "similitudes"
by other authors. The name `Dilation` was chosen to match the Wikipedia name.

The definition only requires `EDist`. We add weak pseudoemetric, pseudoemetric, or metric space
assumptions when they are needed.

## TODO

- Introduce dilation equivs.
- Refactor the `Isometry` API to match the `*HomClass` API below.

## References

- https://en.wikipedia.org/wiki/Dilation_(metric_space)
- [Marcel Berger, *Geometry*][berger1987]
-/

@[expose] public section

noncomputable section

open Bornology Function Set Topology Metric
open scoped ENNReal NNReal

section Defs

variable (α : Type*) (β : Type*) [EDist α] [EDist β]

/-- A dilation is a map that uniformly scales the edistance between any two points. -/
structure Dilation where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : α → β
  edist_eq' : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, edist (toFun x) (toFun y) = r * edist x y

@[inherit_doc] infixl:25 " →ᵈ " => Dilation

/-- `DilationClass F α β r` states that `F` is a type of `r`-dilations.
You should extend this typeclass when you extend `Dilation`. -/
class DilationClass (F : Type*) (α β : outParam Type*) [EDist α] [EDist β]
    [FunLike F α β] : Prop where
  edist_eq' : ∀ f : F, ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, edist (f x) (f y) = r * edist x y

end Defs

namespace Dilation

variable {F G H I J : Type*} {X Y Z : Type*} {α β γ κ : Type*} {δ τ ζ : Type*}

section Setup

variable [EDist X] [EDist Y]
variable [TopologicalSpace α] [WeakPseudoEMetricSpace α]
variable [FunLike G α Y]

instance funLike : FunLike (X →ᵈ Y) X Y where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr

instance toDilationClass : DilationClass (X →ᵈ Y) X Y where
  edist_eq' f := edist_eq' f

@[simp]
theorem toFun_eq_coe {f : X →ᵈ Y} : f.toFun = (f : X → Y) :=
  rfl

@[simp]
theorem coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : X →ᵈ Y) = f :=
  rfl

protected theorem congr_fun {f g : X →ᵈ Y} (h : f = g) (x : X) : f x = g x :=
  DFunLike.congr_fun h x

protected theorem congr_arg (f : X →ᵈ Y) {x y : X} (h : x = y) : f x = f y :=
  DFunLike.congr_arg f h

@[ext]
theorem ext {f g : X →ᵈ Y} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[simp]
theorem mk_coe (f : X →ᵈ Y) (h) : Dilation.mk f h = f :=
  ext fun _ => rfl

/-- Copy of a `Dilation` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[simps -fullyApplied]
protected def copy (f : X →ᵈ Y) (f' : X → Y) (h : f' = ⇑f) : X →ᵈ Y where
  toFun := f'
  edist_eq' := h.symm ▸ f.edist_eq'

theorem copy_eq_self (f : X →ᵈ Y) {f' : X → Y} (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable [FunLike F X Y]

open scoped Classical in
/-- The ratio of a dilation `f`. If the ratio is undefined (i.e., the distance between any two
points in `X` is either zero or infinity), then we choose one as the ratio. -/
def ratio [DilationClass F X Y] (f : F) : ℝ≥0 :=
  if ∀ x y : X, edist x y = 0 ∨ edist x y = ⊤ then 1 else (DilationClass.edist_eq' f).choose

theorem ratio_of_trivial [DilationClass F X Y] (f : F)
    (h : ∀ x y : X, edist x y = 0 ∨ edist x y = ∞) : ratio f = 1 :=
  ite_eq_left h

@[nontriviality]
theorem ratio_of_subsingleton [Subsingleton α] [DilationClass G α Y] (f : G) : ratio f = 1 :=
  ite_eq_left fun x y ↦ by simp [Subsingleton.elim x y]

theorem ratio_ne_zero [DilationClass F X Y] (f : F) : ratio f ≠ 0 := by
  rw [ratio]; split_ifs
  · exact one_ne_zero
  exact (DilationClass.edist_eq' f).choose_spec.1

theorem ratio_pos [DilationClass F X Y] (f : F) : 0 < ratio f :=
  (ratio_ne_zero f).bot_lt

@[simp]
theorem edist_eq [DilationClass F X Y] (f : F) (x y : X) :
    edist (f x) (f y) = ratio f * edist x y := by
  rw [ratio]; split_ifs with key
  · rcases DilationClass.edist_eq' f with ⟨r, hne, hr⟩
    replace hr := hr x y
    rcases key x y with h | h
    · simp only [hr, h, mul_zero]
    · simp [hr, h, hne]
  exact (DilationClass.edist_eq' f).choose_spec.2 x y

@[simp]
theorem nndist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    nndist (f x) (f y) = ratio f * nndist x y := by
  simp only [← ENNReal.coe_inj, ← edist_nndist, ENNReal.coe_mul, edist_eq]

@[simp]
theorem dist_eq {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β]
    [DilationClass F α β] (f : F) (x y : α) :
    dist (f x) (f y) = ratio f * dist x y := by
  simp only [dist_nndist, nndist_eq, NNReal.coe_mul]

/-- The `ratio` is equal to the distance ratio for any two points with nonzero finite distance.
`dist` and `nndist` versions below -/
theorem ratio_unique [DilationClass F X Y] {f : F} {x y : X} {r : ℝ≥0} (h₀ : edist x y ≠ 0)
    (htop : edist x y ≠ ⊤) (hr : edist (f x) (f y) = r * edist x y) : r = ratio f := by
  simpa only [hr, ENNReal.mul_left_inj h₀ htop, ENNReal.coe_inj] using edist_eq f x y

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `nndist` version -/
theorem ratio_unique_of_nndist_ne_zero {α β F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (hxy : nndist x y ≠ 0)
    (hr : nndist (f x) (f y) = r * nndist x y) : r = ratio f :=
  ratio_unique (by rwa [edist_nndist, ENNReal.coe_ne_zero]) (edist_ne_top x y)
    (by rw [edist_nndist, edist_nndist, hr, ENNReal.coe_mul])

/-- The `ratio` is equal to the distance ratio for any two points
with nonzero finite distance; `dist` version -/
theorem ratio_unique_of_dist_ne_zero {α β} {F : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    [FunLike F α β] [DilationClass F α β] {f : F} {x y : α} {r : ℝ≥0} (hxy : dist x y ≠ 0)
    (hr : dist (f x) (f y) = r * dist x y) : r = ratio f :=
  ratio_unique_of_nndist_ne_zero (NNReal.coe_ne_zero.1 hxy) <|
    NNReal.eq <| by rw [coe_nndist, hr, NNReal.coe_mul, coe_nndist]

/-- Alternative `Dilation` constructor when the distance hypothesis is over `nndist` -/
def mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
    (h : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, nndist (f x) (f y) = r * nndist x y) : α →ᵈ β where
  toFun := f
  edist_eq' := by
    rcases h with ⟨r, hne, h⟩
    refine ⟨r, hne, fun x y => ?_⟩
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_mul, h x y]

@[simp]
theorem coe_mkOfNNDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (h) :
    ⇑(mkOfNNDistEq f h : α →ᵈ β) = f :=
  rfl

@[simp]
theorem mk_coe_of_nndist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α →ᵈ β)
    (h) : Dilation.mkOfNNDistEq f h = f :=
  ext fun _ => rfl

/-- Alternative `Dilation` constructor when the distance hypothesis is over `dist` -/
def mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β)
    (h : ∃ r : ℝ≥0, r ≠ 0 ∧ ∀ x y : α, dist (f x) (f y) = r * dist x y) : α →ᵈ β :=
  mkOfNNDistEq f <|
    h.imp fun r hr =>
      ⟨hr.1, fun x y => NNReal.eq <| by rw [coe_nndist, hr.2, NNReal.coe_mul, coe_nndist]⟩

@[simp]
theorem coe_mkOfDistEq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α → β) (h) :
    ⇑(mkOfDistEq f h : α →ᵈ β) = f :=
  rfl

@[simp]
theorem mk_coe_of_dist_eq {α β} [PseudoMetricSpace α] [PseudoMetricSpace β] (f : α →ᵈ β) (h) :
    Dilation.mkOfDistEq f h = f :=
  ext fun _ => rfl

end Setup

section PseudoEMetricDilation

variable [EDist X] [EDist Y] [EDist Z]
variable [TopologicalSpace α] [WeakPseudoEMetricSpace α]
  [TopologicalSpace β] [WeakPseudoEMetricSpace β]
variable [TopologicalSpace κ] [WeakEMetricSpace κ]
variable [PseudoEMetricSpace δ] [PseudoEMetricSpace τ]
variable [FunLike F X Y] [DilationClass F X Y]
variable [FunLike G α β] [DilationClass G α β]
variable [FunLike H κ β] [DilationClass H κ β]
variable [FunLike I δ τ] [DilationClass I δ τ]
variable [FunLike J δ β] [DilationClass J δ β]
variable (f : F)

/-- Every isometry is a dilation of ratio `1`. -/
@[simps]
def _root_.Isometry.toDilation (f : X → Y) (hf : Isometry f) : X →ᵈ Y where
  toFun := f
  edist_eq' := ⟨1, one_ne_zero, by simpa using! hf⟩

@[simp]
lemma _root_.Isometry.toDilation_ratio {f : X → Y} {hf : Isometry f} :
    ratio hf.toDilation = 1 := by
  by_cases! h : ∀ x y : X, edist x y = 0 ∨ edist x y = ⊤
  · exact ratio_of_trivial hf.toDilation h
  · obtain ⟨x, y, h₁, h₂⟩ := h
    exact ratio_unique h₁ h₂ (by simp [hf x y]) |>.symm

theorem lipschitz : LipschitzWith (ratio f) (f : X → Y) := fun x y => (edist_eq f x y).le

theorem antilipschitz : AntilipschitzWith (ratio f)⁻¹ (f : X → Y) := fun x y => by
  have hr : ratio f ≠ 0 := ratio_ne_zero f
  exact mod_cast
    (ENNReal.mul_le_iff_le_inv (ENNReal.coe_ne_zero.2 hr) ENNReal.coe_ne_top).1 (edist_eq f x y).ge

/-- A dilation from a weak emetric space is injective. -/
protected theorem injective (f : H) : Injective f := fun x y hxy => by
  apply eq_of_edist_eq_zero
  have h := edist_eq f x y
  rw [hxy, edist_self] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (ENNReal.coe_ne_zero.2 (ratio_ne_zero f))

/-- The identity is a dilation -/
protected def id (X) [EDist X] : X →ᵈ X where
  toFun := id
  edist_eq' := ⟨1, one_ne_zero, fun x y => by simp only [id, ENNReal.coe_one, one_mul]⟩

instance : Inhabited (X →ᵈ X) :=
  ⟨Dilation.id X⟩

@[simp]
protected theorem coe_id : ⇑(Dilation.id X) = id :=
  rfl

theorem ratio_id : ratio (Dilation.id X) = 1 := by
  by_cases! h : ∀ x y : X, edist x y = 0 ∨ edist x y = ∞
  · rw [ratio, ite_eq_left h]
  · rcases h with ⟨x, y, hne⟩
    refine (ratio_unique hne.1 hne.2 ?_).symm
    simp

/-- The composition of dilations is a dilation -/
def comp (g : Y →ᵈ Z) (f : X →ᵈ Y) : X →ᵈ Z where
  toFun := g ∘ f
  edist_eq' := ⟨ratio g * ratio f, mul_ne_zero (ratio_ne_zero g) (ratio_ne_zero f),
    fun x y => by simp_rw [Function.comp, edist_eq, ENNReal.coe_mul, mul_assoc]⟩

theorem comp_assoc {W : Type*} [EDist W] (f : X →ᵈ Y) (g : Y →ᵈ Z)
    (h : Z →ᵈ W) : (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (g : Y →ᵈ Z) (f : X →ᵈ Y) : (g.comp f : X → Z) = g ∘ f :=
  rfl

theorem comp_apply (g : Y →ᵈ Z) (f : X →ᵈ Y) (x : X) : (g.comp f : X → Z) x = g (f x) :=
  rfl

/-- Ratio of the composition `g.comp f` of two dilations is the product of their ratios. We assume
that there exist two points in `X` at extended distance neither `0` nor `∞` because otherwise
`Dilation.ratio (g.comp f) = Dilation.ratio f = 1` while `Dilation.ratio g` can be any number. This
version works for most general spaces, see also `Dilation.ratio_comp` for a version assuming that
`X` is a nontrivial metric space. -/
theorem ratio_comp' {g : Y →ᵈ Z} {f : X →ᵈ Y}
    (hne : ∃ x y : X, edist x y ≠ 0 ∧ edist x y ≠ ⊤) :
    ratio (g.comp f) = ratio g * ratio f := by
  rcases hne with ⟨x, y, hα⟩
  have hgf := (edist_eq (g.comp f) x y).symm
  simp_rw [coe_comp, Function.comp, edist_eq, ← mul_assoc, ENNReal.mul_left_inj hα.1 hα.2]
    at hgf
  rwa [← ENNReal.coe_inj, ENNReal.coe_mul]

@[simp]
theorem comp_id (f : X →ᵈ Y) : f.comp (Dilation.id X) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : X →ᵈ Y) : (Dilation.id Y).comp f = f :=
  ext fun _ => rfl

instance : Monoid (X →ᵈ X) where
  one := Dilation.id X
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc _ _ _ := comp_assoc _ _ _

theorem one_def : (1 : X →ᵈ X) = Dilation.id X :=
  rfl

theorem mul_def (f g : X →ᵈ X) : f * g = f.comp g :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : X →ᵈ X) = id :=
  rfl

@[simp]
theorem coe_mul (f g : X →ᵈ X) : ⇑(f * g) = f ∘ g :=
  rfl

@[simp] theorem ratio_one : ratio (1 : X →ᵈ X) = 1 := ratio_id

@[simp]
theorem ratio_mul (f g : X →ᵈ X) : ratio (f * g) = ratio f * ratio g := by
  by_cases! h : ∀ x y : X, edist x y = 0 ∨ edist x y = ∞
  · simp [ratio_of_trivial, h]
  exact ratio_comp' h

/-- `Dilation.ratio` as a monoid homomorphism from `X →ᵈ X` to `ℝ≥0`. -/
@[simps]
def ratioHom : (X →ᵈ X) →* ℝ≥0 := ⟨⟨ratio, ratio_one⟩, ratio_mul⟩

@[simp]
theorem ratio_pow (f : X →ᵈ X) (n : ℕ) : ratio (f ^ n) = ratio f ^ n :=
  ratioHom.map_pow _ _

@[simp]
theorem cancel_right {g₁ g₂ : Y →ᵈ Z} {f : X →ᵈ Y} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => Dilation.ext <| hf.forall.2 (Dilation.ext_iff.1 h), fun h => h ▸ rfl⟩

@[simp]
theorem cancel_left {g : Y →ᵈ Z} {f₁ f₂ : X →ᵈ Y} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => Dilation.ext fun x => hg <| by rw [← comp_apply, h, comp_apply], fun h => h ▸ rfl⟩

/-- A dilation from a metric space is a uniform inducing map -/
theorem isUniformInducing (f : I) : IsUniformInducing (f : δ → τ) :=
  (antilipschitz f).isUniformInducing (lipschitz f).uniformContinuous

theorem tendsto_nhds_iff (f : I) {ι : Type*} {g : ι → δ} {a : Filter ι} {b : δ} :
    Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto ((f : δ → τ) ∘ g) a (𝓝 (f b)) :=
  (Dilation.isUniformInducing f).isInducing.tendsto_nhds_iff

/-- A dilation is continuous. -/
theorem toContinuous (f : J) : Continuous (f : δ → β) :=
  (lipschitz f).continuous

/-- Dilations scale the diameter by `ratio f` in pseudoemetric spaces. -/
theorem ediam_image (f : G) (s : Set α) :
    ediam ((f : α → β) '' s) = ratio f * ediam s := by
  refine ((lipschitz f).ediam_image_le s).antisymm ?_
  apply ENNReal.mul_le_of_le_div'
  rw [div_eq_mul_inv, mul_comm, ← ENNReal.coe_inv]
  exacts [(antilipschitz f).le_mul_ediam_image s, ratio_ne_zero f]

/-- A dilation scales the diameter of the range by `ratio f`. -/
theorem ediam_range (f : G) :
    ediam (range (f : α → β)) = ratio f * ediam (univ : Set α) := by
  rw [← image_univ]; exact ediam_image f univ

/-- A dilation maps balls to balls and scales the radius by `ratio f`. -/
theorem mapsTo_eball (f : G) (x : α) (r : ℝ≥0∞) :
    MapsTo (f : α → β) (Metric.eball x r) (Metric.eball (f x) (ratio f * r)) :=
  fun y (hy : _ < r) ↦ by rw [Metric.mem_eball, edist_eq f y x]; gcongr <;> simp [ratio_ne_zero, *]

/-- A dilation maps closed balls to closed balls and scales the radius by `ratio f`. -/
theorem mapsTo_closedEBall (f : G) (x : α) (r' : ℝ≥0∞) :
    MapsTo (f : α → β) (Metric.closedEBall x r') (Metric.closedEBall (f x) (ratio f * r')) :=
  fun y hy => (edist_eq f y x).trans_le <| by gcongr; exact hy

theorem comp_continuousOn_iff (f : I) {σ} [TopologicalSpace σ] {g : σ → δ} {s : Set σ} :
    ContinuousOn ((f : δ → τ) ∘ g) s ↔ ContinuousOn g s :=
  (Dilation.isUniformInducing f).isInducing.continuousOn_iff.symm

theorem comp_continuous_iff (f : I) {σ} [TopologicalSpace σ] {g : σ → δ} :
    Continuous ((f : δ → τ) ∘ g) ↔ Continuous g :=
  (Dilation.isUniformInducing f).isInducing.continuous_iff.symm

end PseudoEMetricDilation

section EMetricDilation

variable [EMetricSpace δ]
variable [FunLike I δ τ]

/-- A dilation from a metric space is a uniform embedding -/
lemma isUniformEmbedding [PseudoEMetricSpace τ] [DilationClass I δ τ] (f : I) :
    IsUniformEmbedding f :=
  (antilipschitz f).isUniformEmbedding (lipschitz f).uniformContinuous

/-- A dilation from a metric space is an embedding -/
theorem isEmbedding [PseudoEMetricSpace τ] [DilationClass I δ τ] (f : I) :
    IsEmbedding (f : δ → τ) :=
  (Dilation.isUniformEmbedding f).isEmbedding

/-- A dilation from a complete emetric space is a closed embedding -/
lemma isClosedEmbedding [CompleteSpace δ] [EMetricSpace τ] [DilationClass I δ τ] (f : I) :
    IsClosedEmbedding f :=
  (antilipschitz f).isClosedEmbedding (lipschitz f).uniformContinuous

end EMetricDilation

/-- Ratio of the composition `g.comp f` of two dilations is the product of their ratios. We assume
that the domain `δ` of `f` is a nontrivial metric space, otherwise
`Dilation.ratio f = Dilation.ratio (g.comp f) = 1` but `Dilation.ratio g` may have any value.

See also `Dilation.ratio_comp'` for a version that works for more general spaces. -/
@[simp]
theorem ratio_comp [MetricSpace δ] [Nontrivial δ] [EDist Y] [EDist Z]
    {g : Y →ᵈ Z} {f : δ →ᵈ Y} : ratio (g.comp f) = ratio g * ratio f :=
  ratio_comp' <|
    let ⟨x, y, hne⟩ := exists_pair_ne δ; ⟨x, y, mt edist_eq_zero.1 hne, edist_ne_top _ _⟩

section PseudoMetricDilation

variable [PseudoMetricSpace α] [PseudoMetricSpace β] [FunLike F α β] [DilationClass F α β] (f : F)

/-- A dilation scales the diameter by `ratio f` in pseudometric spaces. -/
theorem diam_image (s : Set α) : diam ((f : α → β) '' s) = ratio f * diam s := by
  simp [diam, ediam_image, ENNReal.toReal_mul]

theorem diam_range : diam (range (f : α → β)) = ratio f * diam (univ : Set α) := by
  rw [← image_univ, diam_image]

/-- A dilation maps balls to balls and scales the radius by `ratio f`. -/
theorem mapsTo_ball (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.ball x r') (Metric.ball (f x) (ratio f * r')) :=
  fun y hy => (dist_eq f y x).trans_lt <| by gcongr; exacts [ratio_pos _, hy]

/-- A dilation maps spheres to spheres and scales the radius by `ratio f`. -/
theorem mapsTo_sphere (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.sphere x r') (Metric.sphere (f x) (ratio f * r')) :=
  fun y hy => Metric.mem_sphere.mp hy ▸ dist_eq f y x

/-- A dilation maps closed balls to closed balls and scales the radius by `ratio f`. -/
theorem mapsTo_closedBall (x : α) (r' : ℝ) :
    MapsTo (f : α → β) (Metric.closedBall x r') (Metric.closedBall (f x) (ratio f * r')) :=
  fun y hy => (dist_eq f y x).trans_le <| mul_le_mul_of_nonneg_left hy (NNReal.coe_nonneg _)

lemma tendsto_cobounded : Filter.Tendsto f (cobounded α) (cobounded β) :=
  (Dilation.antilipschitz f).tendsto_cobounded

@[simp]
lemma comap_cobounded : Filter.comap f (cobounded β) = cobounded α :=
  le_antisymm (lipschitz f).comap_cobounded_le (tendsto_cobounded f).le_comap

end PseudoMetricDilation

end Dilation
