/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Isometries of emetric and metric spaces
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.Antilipschitz

#align_import topology.metric_space.isometry from "leanprover-community/mathlib"@"b1859b6d4636fdbb78c5d5cefd24530653cfd3eb"

/-!
# Isometries

We define isometries, i.e., maps between emetric spaces that preserve
the edistance (on metric spaces, these are exactly the maps that preserve distances),
and prove their basic properties. We also introduce isometric bijections.

Since a lot of elementary properties don't require `eq_of_dist_eq_zero` we start setting up the
theory for `PseudoMetricSpace` and we specialize to `MetricSpace` when needed.
-/


noncomputable section

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w}

open Function Set

open scoped Topology ENNReal

/-- An isometry (also known as isometric embedding) is a map preserving the edistance
between pseudoemetric spaces, or equivalently the distance between pseudometric space.  -/
def Isometry [PseudoEMetricSpace α] [PseudoEMetricSpace β] (f : α → β) : Prop :=
  ∀ x1 x2 : α, edist (f x1) (f x2) = edist x1 x2
#align isometry Isometry

/-- On pseudometric spaces, a map is an isometry if and only if it preserves nonnegative
distances. -/
theorem isometry_iff_nndist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, nndist (f x) (f y) = nndist x y := by
  simp only [Isometry, edist_nndist, ENNReal.coe_eq_coe]
  -- 🎉 no goals
#align isometry_iff_nndist_eq isometry_iff_nndist_eq

/-- On pseudometric spaces, a map is an isometry if and only if it preserves distances. -/
theorem isometry_iff_dist_eq [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β} :
    Isometry f ↔ ∀ x y, dist (f x) (f y) = dist x y := by
  simp only [isometry_iff_nndist_eq, ← coe_nndist, NNReal.coe_eq]
  -- 🎉 no goals
#align isometry_iff_dist_eq isometry_iff_dist_eq

/-- An isometry preserves distances. -/
alias ⟨Isometry.dist_eq, _⟩ := isometry_iff_dist_eq
#align isometry.dist_eq Isometry.dist_eq

/-- A map that preserves distances is an isometry -/
alias ⟨_, Isometry.of_dist_eq⟩ := isometry_iff_dist_eq
#align isometry.of_dist_eq Isometry.of_dist_eq

/-- An isometry preserves non-negative distances. -/
alias ⟨Isometry.nndist_eq, _⟩ := isometry_iff_nndist_eq
#align isometry.nndist_eq Isometry.nndist_eq

/-- A map that preserves non-negative distances is an isometry. -/
alias ⟨_, Isometry.of_nndist_eq⟩ := isometry_iff_nndist_eq
#align isometry.of_nndist_eq Isometry.of_nndist_eq

namespace Isometry

section PseudoEmetricIsometry

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

variable {f : α → β} {x y z : α} {s : Set α}

/-- An isometry preserves edistances. -/
theorem edist_eq (hf : Isometry f) (x y : α) : edist (f x) (f y) = edist x y :=
  hf x y
#align isometry.edist_eq Isometry.edist_eq

theorem lipschitz (h : Isometry f) : LipschitzWith 1 f :=
  LipschitzWith.of_edist_le fun x y => (h x y).le
#align isometry.lipschitz Isometry.lipschitz

theorem antilipschitz (h : Isometry f) : AntilipschitzWith 1 f := fun x y => by
  simp only [h x y, ENNReal.coe_one, one_mul, le_refl]
  -- 🎉 no goals
#align isometry.antilipschitz Isometry.antilipschitz

/-- Any map on a subsingleton is an isometry -/
@[nontriviality]
theorem _root_.isometry_subsingleton [Subsingleton α] : Isometry f := fun x y => by
  rw [Subsingleton.elim x y]; simp
  -- ⊢ edist (f y) (f y) = edist y y
                              -- 🎉 no goals
#align isometry_subsingleton isometry_subsingleton

/-- The identity is an isometry -/
theorem _root_.isometry_id : Isometry (id : α → α) := fun _ _ => rfl
#align isometry_id isometry_id

theorem prod_map {δ} [PseudoEMetricSpace δ] {f : α → β} {g : γ → δ} (hf : Isometry f)
    (hg : Isometry g) : Isometry (Prod.map f g) := fun x y => by
  simp only [Prod.edist_eq, hf.edist_eq, hg.edist_eq, Prod_map]
  -- 🎉 no goals
#align isometry.prod_map Isometry.prod_map

theorem _root_.isometry_dcomp {ι} [Fintype ι] {α β : ι → Type*} [∀ i, PseudoEMetricSpace (α i)]
    [∀ i, PseudoEMetricSpace (β i)] (f : ∀ i, α i → β i) (hf : ∀ i, Isometry (f i)) :
    Isometry (fun g : (i : ι) → α i => fun i => f i (g i)) := fun x y => by
  simp only [edist_pi_def, (hf _).edist_eq]
  -- 🎉 no goals
#align isometry_dcomp isometry_dcomp

/-- The composition of isometries is an isometry. -/
theorem comp {g : β → γ} {f : α → β} (hg : Isometry g) (hf : Isometry f) : Isometry (g ∘ f) :=
  fun _ _ => (hg _ _).trans (hf _ _)
#align isometry.comp Isometry.comp

/-- An isometry from a metric space is a uniform continuous map -/
protected theorem uniformContinuous (hf : Isometry f) : UniformContinuous f :=
  hf.lipschitz.uniformContinuous
#align isometry.uniform_continuous Isometry.uniformContinuous

/-- An isometry from a metric space is a uniform inducing map -/
protected theorem uniformInducing (hf : Isometry f) : UniformInducing f :=
  hf.antilipschitz.uniformInducing hf.uniformContinuous
#align isometry.uniform_inducing Isometry.uniformInducing

theorem tendsto_nhds_iff {ι : Type*} {f : α → β} {g : ι → α} {a : Filter ι} {b : α}
    (hf : Isometry f) : Filter.Tendsto g a (𝓝 b) ↔ Filter.Tendsto (f ∘ g) a (𝓝 (f b)) :=
  hf.uniformInducing.inducing.tendsto_nhds_iff
#align isometry.tendsto_nhds_iff Isometry.tendsto_nhds_iff

/-- An isometry is continuous. -/
protected theorem continuous (hf : Isometry f) : Continuous f :=
  hf.lipschitz.continuous
#align isometry.continuous Isometry.continuous

/-- The right inverse of an isometry is an isometry. -/
theorem right_inv {f : α → β} {g : β → α} (h : Isometry f) (hg : RightInverse g f) : Isometry g :=
  fun x y => by rw [← h, hg _, hg _]
                -- 🎉 no goals
#align isometry.right_inv Isometry.right_inv

theorem preimage_emetric_closedBall (h : Isometry f) (x : α) (r : ℝ≥0∞) :
    f ⁻¹' EMetric.closedBall (f x) r = EMetric.closedBall x r := by
  ext y
  -- ⊢ y ∈ f ⁻¹' EMetric.closedBall (f x) r ↔ y ∈ EMetric.closedBall x r
  simp [h.edist_eq]
  -- 🎉 no goals
#align isometry.preimage_emetric_closed_ball Isometry.preimage_emetric_closedBall

theorem preimage_emetric_ball (h : Isometry f) (x : α) (r : ℝ≥0∞) :
    f ⁻¹' EMetric.ball (f x) r = EMetric.ball x r := by
  ext y
  -- ⊢ y ∈ f ⁻¹' EMetric.ball (f x) r ↔ y ∈ EMetric.ball x r
  simp [h.edist_eq]
  -- 🎉 no goals
#align isometry.preimage_emetric_ball Isometry.preimage_emetric_ball

/-- Isometries preserve the diameter in pseudoemetric spaces. -/
theorem ediam_image (hf : Isometry f) (s : Set α) : EMetric.diam (f '' s) = EMetric.diam s :=
  eq_of_forall_ge_iff fun d => by simp only [EMetric.diam_le_iff, ball_image_iff, hf.edist_eq]
                                  -- 🎉 no goals
#align isometry.ediam_image Isometry.ediam_image

theorem ediam_range (hf : Isometry f) : EMetric.diam (range f) = EMetric.diam (univ : Set α) := by
  rw [← image_univ]
  -- ⊢ EMetric.diam (f '' univ) = EMetric.diam univ
  exact hf.ediam_image univ
  -- 🎉 no goals
#align isometry.ediam_range Isometry.ediam_range

theorem mapsTo_emetric_ball (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (EMetric.ball x r) (EMetric.ball (f x) r) :=
  (hf.preimage_emetric_ball x r).ge
#align isometry.maps_to_emetric_ball Isometry.mapsTo_emetric_ball

theorem mapsTo_emetric_closedBall (hf : Isometry f) (x : α) (r : ℝ≥0∞) :
    MapsTo f (EMetric.closedBall x r) (EMetric.closedBall (f x) r) :=
  (hf.preimage_emetric_closedBall x r).ge
#align isometry.maps_to_emetric_closed_ball Isometry.mapsTo_emetric_closedBall

/-- The injection from a subtype is an isometry -/
theorem _root_.isometry_subtype_coe {s : Set α} : Isometry ((↑) : s → α) := fun _ _ => rfl
#align isometry_subtype_coe isometry_subtype_coe

theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} {s : Set γ} :
    ContinuousOn (f ∘ g) s ↔ ContinuousOn g s :=
  hf.uniformInducing.inducing.continuousOn_iff.symm
#align isometry.comp_continuous_on_iff Isometry.comp_continuousOn_iff

theorem comp_continuous_iff {γ} [TopologicalSpace γ] (hf : Isometry f) {g : γ → α} :
    Continuous (f ∘ g) ↔ Continuous g :=
  hf.uniformInducing.inducing.continuous_iff.symm
#align isometry.comp_continuous_iff Isometry.comp_continuous_iff

end PseudoEmetricIsometry

--section
section EmetricIsometry

variable [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}

/-- An isometry from an emetric space is injective -/
protected theorem injective (h : Isometry f) : Injective f :=
  h.antilipschitz.injective
#align isometry.injective Isometry.injective

/-- An isometry from an emetric space is a uniform embedding -/
protected theorem uniformEmbedding (hf : Isometry f) : UniformEmbedding f :=
  hf.antilipschitz.uniformEmbedding hf.lipschitz.uniformContinuous
#align isometry.uniform_embedding Isometry.uniformEmbedding

/-- An isometry from an emetric space is an embedding -/
protected theorem embedding (hf : Isometry f) : Embedding f :=
  hf.uniformEmbedding.embedding
#align isometry.embedding Isometry.embedding

/-- An isometry from a complete emetric space is a closed embedding -/
theorem closedEmbedding [CompleteSpace α] [EMetricSpace γ] {f : α → γ} (hf : Isometry f) :
    ClosedEmbedding f :=
  hf.antilipschitz.closedEmbedding hf.lipschitz.uniformContinuous
#align isometry.closed_embedding Isometry.closedEmbedding

end EmetricIsometry

--section
section PseudoMetricIsometry

variable [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β}

/-- An isometry preserves the diameter in pseudometric spaces. -/
theorem diam_image (hf : Isometry f) (s : Set α) : Metric.diam (f '' s) = Metric.diam s := by
  rw [Metric.diam, Metric.diam, hf.ediam_image]
  -- 🎉 no goals
#align isometry.diam_image Isometry.diam_image

theorem diam_range (hf : Isometry f) : Metric.diam (range f) = Metric.diam (univ : Set α) := by
  rw [← image_univ]
  -- ⊢ Metric.diam (f '' univ) = Metric.diam univ
  exact hf.diam_image univ
  -- 🎉 no goals
#align isometry.diam_range Isometry.diam_range

theorem preimage_setOf_dist (hf : Isometry f) (x : α) (p : ℝ → Prop) :
    f ⁻¹' { y | p (dist y (f x)) } = { y | p (dist y x) } := by
  ext y
  -- ⊢ y ∈ f ⁻¹' {y | p (dist y (f x))} ↔ y ∈ {y | p (dist y x)}
  simp [hf.dist_eq]
  -- 🎉 no goals
#align isometry.preimage_set_of_dist Isometry.preimage_setOf_dist

theorem preimage_closedBall (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.closedBall (f x) r = Metric.closedBall x r :=
  hf.preimage_setOf_dist x (· ≤ r)
#align isometry.preimage_closed_ball Isometry.preimage_closedBall

theorem preimage_ball (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.ball (f x) r = Metric.ball x r :=
  hf.preimage_setOf_dist x (· < r)
#align isometry.preimage_ball Isometry.preimage_ball

theorem preimage_sphere (hf : Isometry f) (x : α) (r : ℝ) :
    f ⁻¹' Metric.sphere (f x) r = Metric.sphere x r :=
  hf.preimage_setOf_dist x (· = r)
#align isometry.preimage_sphere Isometry.preimage_sphere

theorem mapsTo_ball (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.ball x r) (Metric.ball (f x) r) :=
  (hf.preimage_ball x r).ge
#align isometry.maps_to_ball Isometry.mapsTo_ball

theorem mapsTo_sphere (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.sphere x r) (Metric.sphere (f x) r) :=
  (hf.preimage_sphere x r).ge
#align isometry.maps_to_sphere Isometry.mapsTo_sphere

theorem mapsTo_closedBall (hf : Isometry f) (x : α) (r : ℝ) :
    MapsTo f (Metric.closedBall x r) (Metric.closedBall (f x) r) :=
  (hf.preimage_closedBall x r).ge
#align isometry.maps_to_closed_ball Isometry.mapsTo_closedBall

end PseudoMetricIsometry

-- section
end Isometry

-- namespace
/-- A uniform embedding from a uniform space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
theorem UniformEmbedding.to_isometry {α β} [UniformSpace α] [MetricSpace β] {f : α → β}
    (h : UniformEmbedding f) : (letI := h.comapMetricSpace f; Isometry f) :=
  let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl
#align uniform_embedding.to_isometry UniformEmbedding.to_isometry

/-- An embedding from a topological space to a metric space is an isometry with respect to the
induced metric space structure on the source space. -/
theorem Embedding.to_isometry {α β} [TopologicalSpace α] [MetricSpace β] {f : α → β}
    (h : Embedding f) : (letI := h.comapMetricSpace f; Isometry f) :=
  let _ := h.comapMetricSpace f
  Isometry.of_dist_eq fun _ _ => rfl
#align embedding.to_isometry Embedding.to_isometry

-- such a bijection need not exist
/-- `α` and `β` are isometric if there is an isometric bijection between them. -/
-- porting note: was @[nolint has_nonempty_instance]
structure IsometryEquiv (α β : Type _) [PseudoEMetricSpace α] [PseudoEMetricSpace β] extends
  α ≃ β where
  isometry_toFun : Isometry toFun
#align isometry_equiv IsometryEquiv

@[inherit_doc]
infixl:25 " ≃ᵢ " => IsometryEquiv

namespace IsometryEquiv

section PseudoEMetricSpace

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]

-- Porting note: TODO: add `IsometryEquivClass`

theorem toEquiv_injective : Injective (toEquiv : (α ≃ᵢ β) → (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl
#align isometry_equiv.to_equiv_inj IsometryEquiv.toEquiv_injective

@[simp] theorem toEquiv_inj {e₁ e₂ : α ≃ᵢ β} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

instance : EquivLike (α ≃ᵢ β) α β where
  coe e := e.toEquiv
  inv e := e.toEquiv.symm
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| FunLike.ext' h

theorem coe_eq_toEquiv (h : α ≃ᵢ β) (a : α) : h a = h.toEquiv a := rfl
#align isometry_equiv.coe_eq_to_equiv IsometryEquiv.coe_eq_toEquiv

@[simp] theorem coe_toEquiv (h : α ≃ᵢ β) : ⇑h.toEquiv = h := rfl
#align isometry_equiv.coe_to_equiv IsometryEquiv.coe_toEquiv

@[simp] theorem coe_mk (e : α ≃ β) (h) : ⇑(mk e h) = e := rfl

protected theorem isometry (h : α ≃ᵢ β) : Isometry h :=
  h.isometry_toFun
#align isometry_equiv.isometry IsometryEquiv.isometry

protected theorem bijective (h : α ≃ᵢ β) : Bijective h :=
  h.toEquiv.bijective
#align isometry_equiv.bijective IsometryEquiv.bijective

protected theorem injective (h : α ≃ᵢ β) : Injective h :=
  h.toEquiv.injective
#align isometry_equiv.injective IsometryEquiv.injective

protected theorem surjective (h : α ≃ᵢ β) : Surjective h :=
  h.toEquiv.surjective
#align isometry_equiv.surjective IsometryEquiv.surjective

protected theorem edist_eq (h : α ≃ᵢ β) (x y : α) : edist (h x) (h y) = edist x y :=
  h.isometry.edist_eq x y
#align isometry_equiv.edist_eq IsometryEquiv.edist_eq

protected theorem dist_eq {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : dist (h x) (h y) = dist x y :=
  h.isometry.dist_eq x y
#align isometry_equiv.dist_eq IsometryEquiv.dist_eq

protected theorem nndist_eq {α β : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)
    (x y : α) : nndist (h x) (h y) = nndist x y :=
  h.isometry.nndist_eq x y
#align isometry_equiv.nndist_eq IsometryEquiv.nndist_eq

protected theorem continuous (h : α ≃ᵢ β) : Continuous h :=
  h.isometry.continuous
#align isometry_equiv.continuous IsometryEquiv.continuous

@[simp]
theorem ediam_image (h : α ≃ᵢ β) (s : Set α) : EMetric.diam (h '' s) = EMetric.diam s :=
  h.isometry.ediam_image s
#align isometry_equiv.ediam_image IsometryEquiv.ediam_image

@[ext]
theorem ext ⦃h₁ h₂ : α ≃ᵢ β⦄ (H : ∀ x, h₁ x = h₂ x) : h₁ = h₂ :=
  FunLike.ext _ _ H
#align isometry_equiv.ext IsometryEquiv.ext

/-- Alternative constructor for isometric bijections,
taking as input an isometry, and a right inverse. -/
def mk' {α : Type u} [EMetricSpace α] (f : α → β) (g : β → α) (hfg : ∀ x, f (g x) = x)
    (hf : Isometry f) : α ≃ᵢ β where
  toFun := f
  invFun := g
  left_inv _ := hf.injective <| hfg _
  right_inv := hfg
  isometry_toFun := hf
#align isometry_equiv.mk' IsometryEquiv.mk'

/-- The identity isometry of a space. -/
protected def refl (α : Type*) [PseudoEMetricSpace α] : α ≃ᵢ α :=
  { Equiv.refl α with isometry_toFun := isometry_id }
#align isometry_equiv.refl IsometryEquiv.refl

/-- The composition of two isometric isomorphisms, as an isometric isomorphism. -/
protected def trans (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) : α ≃ᵢ γ :=
  { Equiv.trans h₁.toEquiv h₂.toEquiv with
    isometry_toFun := h₂.isometry_toFun.comp h₁.isometry_toFun }
#align isometry_equiv.trans IsometryEquiv.trans

@[simp]
theorem trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : α) : h₁.trans h₂ x = h₂ (h₁ x) :=
  rfl
#align isometry_equiv.trans_apply IsometryEquiv.trans_apply

/-- The inverse of an isometric isomorphism, as an isometric isomorphism. -/
protected def symm (h : α ≃ᵢ β) : β ≃ᵢ α where
  isometry_toFun := h.isometry.right_inv h.right_inv
  toEquiv := h.toEquiv.symm
#align isometry_equiv.symm IsometryEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵢ β) : α → β := h
#align isometry_equiv.simps.apply IsometryEquiv.Simps.apply

/-- See Note [custom simps projection] -/
def Simps.symm_apply (h : α ≃ᵢ β) : β → α :=
  h.symm
#align isometry_equiv.simps.symm_apply IsometryEquiv.Simps.symm_apply

initialize_simps_projections IsometryEquiv (toEquiv_toFun → apply, toEquiv_invFun → symm_apply)

@[simp]
theorem symm_symm (h : α ≃ᵢ β) : h.symm.symm = h := rfl
#align isometry_equiv.symm_symm IsometryEquiv.symm_symm

@[simp]
theorem apply_symm_apply (h : α ≃ᵢ β) (y : β) : h (h.symm y) = y :=
  h.toEquiv.apply_symm_apply y
#align isometry_equiv.apply_symm_apply IsometryEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (h : α ≃ᵢ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x
#align isometry_equiv.symm_apply_apply IsometryEquiv.symm_apply_apply

theorem symm_apply_eq (h : α ≃ᵢ β) {x : α} {y : β} : h.symm y = x ↔ y = h x :=
  h.toEquiv.symm_apply_eq
#align isometry_equiv.symm_apply_eq IsometryEquiv.symm_apply_eq

theorem eq_symm_apply (h : α ≃ᵢ β) {x : α} {y : β} : x = h.symm y ↔ h x = y :=
  h.toEquiv.eq_symm_apply
#align isometry_equiv.eq_symm_apply IsometryEquiv.eq_symm_apply

theorem symm_comp_self (h : α ≃ᵢ β) : (h.symm : β → α) ∘ h = id := funext h.left_inv
#align isometry_equiv.symm_comp_self IsometryEquiv.symm_comp_self

theorem self_comp_symm (h : α ≃ᵢ β) : (h : α → β) ∘ h.symm = id := funext h.right_inv
#align isometry_equiv.self_comp_symm IsometryEquiv.self_comp_symm

@[simp]
theorem range_eq_univ (h : α ≃ᵢ β) : range h = univ :=
  h.toEquiv.range_eq_univ
#align isometry_equiv.range_eq_univ IsometryEquiv.range_eq_univ

theorem image_symm (h : α ≃ᵢ β) : image h.symm = preimage h :=
  image_eq_preimage_of_inverse h.symm.toEquiv.left_inv h.symm.toEquiv.right_inv
#align isometry_equiv.image_symm IsometryEquiv.image_symm

theorem preimage_symm (h : α ≃ᵢ β) : preimage h.symm = image h :=
  (image_eq_preimage_of_inverse h.toEquiv.left_inv h.toEquiv.right_inv).symm
#align isometry_equiv.preimage_symm IsometryEquiv.preimage_symm

@[simp]
theorem symm_trans_apply (h₁ : α ≃ᵢ β) (h₂ : β ≃ᵢ γ) (x : γ) :
    (h₁.trans h₂).symm x = h₁.symm (h₂.symm x) :=
  rfl
#align isometry_equiv.symm_trans_apply IsometryEquiv.symm_trans_apply

theorem ediam_univ (h : α ≃ᵢ β) : EMetric.diam (univ : Set α) = EMetric.diam (univ : Set β) := by
  rw [← h.range_eq_univ, h.isometry.ediam_range]
  -- 🎉 no goals
#align isometry_equiv.ediam_univ IsometryEquiv.ediam_univ

@[simp]
theorem ediam_preimage (h : α ≃ᵢ β) (s : Set β) : EMetric.diam (h ⁻¹' s) = EMetric.diam s := by
  rw [← image_symm, ediam_image]
  -- 🎉 no goals
#align isometry_equiv.ediam_preimage IsometryEquiv.ediam_preimage

@[simp]
theorem preimage_emetric_ball (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
    h ⁻¹' EMetric.ball x r = EMetric.ball (h.symm x) r := by
  rw [← h.isometry.preimage_emetric_ball (h.symm x) r, h.apply_symm_apply]
  -- 🎉 no goals
#align isometry_equiv.preimage_emetric_ball IsometryEquiv.preimage_emetric_ball

@[simp]
theorem preimage_emetric_closedBall (h : α ≃ᵢ β) (x : β) (r : ℝ≥0∞) :
    h ⁻¹' EMetric.closedBall x r = EMetric.closedBall (h.symm x) r := by
  rw [← h.isometry.preimage_emetric_closedBall (h.symm x) r, h.apply_symm_apply]
  -- 🎉 no goals
#align isometry_equiv.preimage_emetric_closed_ball IsometryEquiv.preimage_emetric_closedBall

@[simp]
theorem image_emetric_ball (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
    h '' EMetric.ball x r = EMetric.ball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_emetric_ball, symm_symm]
  -- 🎉 no goals
#align isometry_equiv.image_emetric_ball IsometryEquiv.image_emetric_ball

@[simp]
theorem image_emetric_closedBall (h : α ≃ᵢ β) (x : α) (r : ℝ≥0∞) :
    h '' EMetric.closedBall x r = EMetric.closedBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_emetric_closedBall, symm_symm]
  -- 🎉 no goals
#align isometry_equiv.image_emetric_closed_ball IsometryEquiv.image_emetric_closedBall

/-- The (bundled) homeomorphism associated to an isometric isomorphism. -/
@[simps toEquiv]
protected def toHomeomorph (h : α ≃ᵢ β) : α ≃ₜ β where
  continuous_toFun := h.continuous
  continuous_invFun := h.symm.continuous
  toEquiv := h.toEquiv
#align isometry_equiv.to_homeomorph IsometryEquiv.toHomeomorph
#align isometry_equiv.to_homeomorph_to_equiv IsometryEquiv.toHomeomorph_toEquiv

@[simp]
theorem coe_toHomeomorph (h : α ≃ᵢ β) : ⇑h.toHomeomorph = h :=
  rfl
#align isometry_equiv.coe_to_homeomorph IsometryEquiv.coe_toHomeomorph

@[simp]
theorem coe_toHomeomorph_symm (h : α ≃ᵢ β) : ⇑h.toHomeomorph.symm = h.symm :=
  rfl
#align isometry_equiv.coe_to_homeomorph_symm IsometryEquiv.coe_toHomeomorph_symm

@[simp]
theorem comp_continuousOn_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} {s : Set γ} :
    ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.toHomeomorph.comp_continuousOn_iff _ _
#align isometry_equiv.comp_continuous_on_iff IsometryEquiv.comp_continuousOn_iff

@[simp]
theorem comp_continuous_iff {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : γ → α} :
    Continuous (h ∘ f) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff
#align isometry_equiv.comp_continuous_iff IsometryEquiv.comp_continuous_iff

@[simp]
theorem comp_continuous_iff' {γ} [TopologicalSpace γ] (h : α ≃ᵢ β) {f : β → γ} :
    Continuous (f ∘ h) ↔ Continuous f :=
  h.toHomeomorph.comp_continuous_iff'
#align isometry_equiv.comp_continuous_iff' IsometryEquiv.comp_continuous_iff'

/-- The group of isometries. -/
instance : Group (α ≃ᵢ α) where
  one := IsometryEquiv.refl _
  mul e₁ e₂ := e₂.trans e₁
  inv := IsometryEquiv.symm
  mul_assoc e₁ e₂ e₃ := rfl
  one_mul e := ext fun _ => rfl
  mul_one e := ext fun _ => rfl
  mul_left_inv e := ext e.symm_apply_apply

@[simp] theorem coe_one : ⇑(1 : α ≃ᵢ α) = id := rfl
#align isometry_equiv.coe_one IsometryEquiv.coe_one

@[simp] theorem coe_mul (e₁ e₂ : α ≃ᵢ α) : ⇑(e₁ * e₂) = e₁ ∘ e₂ := rfl
#align isometry_equiv.coe_mul IsometryEquiv.coe_mul

theorem mul_apply (e₁ e₂ : α ≃ᵢ α) (x : α) : (e₁ * e₂) x = e₁ (e₂ x) := rfl
#align isometry_equiv.mul_apply IsometryEquiv.mul_apply

@[simp] theorem inv_apply_self (e : α ≃ᵢ α) (x : α) : e⁻¹ (e x) = x := e.symm_apply_apply x
#align isometry_equiv.inv_apply_self IsometryEquiv.inv_apply_self

@[simp] theorem apply_inv_self (e : α ≃ᵢ α) (x : α) : e (e⁻¹ x) = x := e.apply_symm_apply x
#align isometry_equiv.apply_inv_self IsometryEquiv.apply_inv_self

theorem completeSpace_iff (e : α ≃ᵢ β) : CompleteSpace α ↔ CompleteSpace β := by
  simp only [completeSpace_iff_isComplete_univ, ← e.range_eq_univ, ← image_univ,
    isComplete_image_iff e.isometry.uniformInducing]
#align isometry_equiv.complete_space_iff IsometryEquiv.completeSpace_iff

protected theorem completeSpace [CompleteSpace β] (e : α ≃ᵢ β) : CompleteSpace α :=
  e.completeSpace_iff.2 ‹_›
#align isometry_equiv.complete_space IsometryEquiv.completeSpace

variable (ι α)

/-- `Equiv.funUnique` as an `IsometryEquiv`. -/
@[simps!]
def funUnique [Unique ι] [Fintype ι] : (ι → α) ≃ᵢ α where
  toEquiv := Equiv.funUnique ι α
  isometry_toFun x hx := by simp [edist_pi_def, Finset.univ_unique, Finset.sup_singleton]
                            -- 🎉 no goals
#align isometry_equiv.fun_unique IsometryEquiv.funUnique

/-- `piFinTwoEquiv` as an `IsometryEquiv`. -/
@[simps!]
def piFinTwo (α : Fin 2 → Type*) [∀ i, PseudoEMetricSpace (α i)] : (∀ i, α i) ≃ᵢ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  isometry_toFun x hx := by simp [edist_pi_def, Fin.univ_succ, Prod.edist_eq]
                            -- 🎉 no goals
#align isometry_equiv.pi_fin_two IsometryEquiv.piFinTwo

end PseudoEMetricSpace

section PseudoMetricSpace

variable [PseudoMetricSpace α] [PseudoMetricSpace β] (h : α ≃ᵢ β)

@[simp]
theorem diam_image (s : Set α) : Metric.diam (h '' s) = Metric.diam s :=
  h.isometry.diam_image s
#align isometry_equiv.diam_image IsometryEquiv.diam_image

@[simp]
theorem diam_preimage (s : Set β) : Metric.diam (h ⁻¹' s) = Metric.diam s := by
  rw [← image_symm, diam_image]
  -- 🎉 no goals
#align isometry_equiv.diam_preimage IsometryEquiv.diam_preimage

theorem diam_univ : Metric.diam (univ : Set α) = Metric.diam (univ : Set β) :=
  congr_arg ENNReal.toReal h.ediam_univ
#align isometry_equiv.diam_univ IsometryEquiv.diam_univ

@[simp]
theorem preimage_ball (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.ball x r = Metric.ball (h.symm x) r := by
  rw [← h.isometry.preimage_ball (h.symm x) r, h.apply_symm_apply]
  -- 🎉 no goals
#align isometry_equiv.preimage_ball IsometryEquiv.preimage_ball

@[simp]
theorem preimage_sphere (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.sphere x r = Metric.sphere (h.symm x) r := by
  rw [← h.isometry.preimage_sphere (h.symm x) r, h.apply_symm_apply]
  -- 🎉 no goals
#align isometry_equiv.preimage_sphere IsometryEquiv.preimage_sphere

@[simp]
theorem preimage_closedBall (h : α ≃ᵢ β) (x : β) (r : ℝ) :
    h ⁻¹' Metric.closedBall x r = Metric.closedBall (h.symm x) r := by
  rw [← h.isometry.preimage_closedBall (h.symm x) r, h.apply_symm_apply]
  -- 🎉 no goals
#align isometry_equiv.preimage_closed_ball IsometryEquiv.preimage_closedBall

@[simp]
theorem image_ball (h : α ≃ᵢ β) (x : α) (r : ℝ) : h '' Metric.ball x r = Metric.ball (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_ball, symm_symm]
  -- 🎉 no goals
#align isometry_equiv.image_ball IsometryEquiv.image_ball

@[simp]
theorem image_sphere (h : α ≃ᵢ β) (x : α) (r : ℝ) :
    h '' Metric.sphere x r = Metric.sphere (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_sphere, symm_symm]
  -- 🎉 no goals
#align isometry_equiv.image_sphere IsometryEquiv.image_sphere

@[simp]
theorem image_closedBall (h : α ≃ᵢ β) (x : α) (r : ℝ) :
    h '' Metric.closedBall x r = Metric.closedBall (h x) r := by
  rw [← h.preimage_symm, h.symm.preimage_closedBall, symm_symm]
  -- 🎉 no goals
#align isometry_equiv.image_closed_ball IsometryEquiv.image_closedBall

end PseudoMetricSpace

end IsometryEquiv

/-- An isometry induces an isometric isomorphism between the source space and the
range of the isometry. -/
@[simps! (config := { simpRhs := true }) toEquiv apply]
def Isometry.isometryEquivOnRange [EMetricSpace α] [PseudoEMetricSpace β] {f : α → β}
    (h : Isometry f) : α ≃ᵢ range f where
  isometry_toFun := h
  toEquiv := Equiv.ofInjective f h.injective
#align isometry.isometry_equiv_on_range Isometry.isometryEquivOnRange
#align isometry.isometry_equiv_on_range_to_equiv Isometry.isometryEquivOnRange_toEquiv
#align isometry.isometry_equiv_on_range_apply Isometry.isometryEquivOnRange_apply
