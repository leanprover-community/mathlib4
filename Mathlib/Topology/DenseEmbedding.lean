/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Regular

/-!
# Dense embeddings

This file defines three properties of functions:

* `DenseRange f`       means `f` has dense image;
* `IsDenseInducing i`  means `i` is also inducing, namely it induces the topology on its codomain;
* `IsDenseEmbedding e` means `e` is further an embedding, namely it is injective and `Inducing`.

The main theorem `continuous_extend` gives a criterion for a function
`f : X → Z` to a T₃ space Z to extend along a dense embedding
`i : X → Y` to a continuous function `g : Y → Z`. Actually `i` only
has to be `IsDenseInducing` (not necessarily injective).

-/


noncomputable section

open Filter Set Topology

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- `i : α → β` is "dense inducing" if it has dense range and the topology on `α`
  is the one induced by `i` from the topology on `β`. -/
structure IsDenseInducing [TopologicalSpace α] [TopologicalSpace β] (i : α → β) : Prop
    extends IsInducing i where
  /-- The range of a dense inducing map is a dense set. -/
  protected dense : DenseRange i

namespace IsDenseInducing

variable [TopologicalSpace α] [TopologicalSpace β]

theorem _root_.Dense.isDenseInducing_val {s : Set α} (hs : Dense s) :
    IsDenseInducing (@Subtype.val α s) := ⟨IsInducing.subtypeVal, hs.denseRange_val⟩

variable {i : α → β}

lemma isInducing (di : IsDenseInducing i) : IsInducing i := di.toIsInducing

theorem nhds_eq_comap (di : IsDenseInducing i) : ∀ a : α, 𝓝 a = comap i (𝓝 <| i a) :=
  di.isInducing.nhds_eq_comap

protected theorem continuous (di : IsDenseInducing i) : Continuous i :=
  di.isInducing.continuous

theorem closure_range (di : IsDenseInducing i) : closure (range i) = univ :=
  di.dense.closure_range

protected theorem preconnectedSpace [PreconnectedSpace α] (di : IsDenseInducing i) :
    PreconnectedSpace β :=
  di.dense.preconnectedSpace di.continuous

theorem closure_image_mem_nhds {s : Set α} {a : α} (di : IsDenseInducing i) (hs : s ∈ 𝓝 a) :
    closure (i '' s) ∈ 𝓝 (i a) := by
  rw [di.nhds_eq_comap a, ((nhds_basis_opens _).comap _).mem_iff] at hs
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U ⊆ s⟩
  refine mem_of_superset (hUo.mem_nhds haU) ?_
  calc
    U ⊆ closure (i '' (i ⁻¹' U)) := di.dense.subset_closure_image_preimage_of_isOpen hUo
    _ ⊆ closure (i '' s) := closure_mono (image_subset i sub)

theorem dense_image (di : IsDenseInducing i) {s : Set α} : Dense (i '' s) ↔ Dense s := by
  refine ⟨fun H x => ?_, di.dense.dense_image di.continuous⟩
  rw [di.isInducing.closure_eq_preimage_closure_image, H.closure_eq, preimage_univ]
  trivial

/-- If `i : α → β` is a dense embedding with dense complement of the range, then any compact set in
`α` has empty interior. -/
theorem interior_compact_eq_empty [T2Space β] (di : IsDenseInducing i) (hd : Dense (range i)ᶜ)
    {s : Set α} (hs : IsCompact s) : interior s = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun x hx => ?_
  rw [mem_interior_iff_mem_nhds] at hx
  have := di.closure_image_mem_nhds hx
  rw [(hs.image di.continuous).isClosed.closure_eq] at this
  rcases hd.inter_nhds_nonempty this with ⟨y, hyi, hys⟩
  exact hyi (image_subset_range _ _ hys)

/-- The product of two dense inducings is a dense inducing -/
protected theorem prodMap [TopologicalSpace γ] [TopologicalSpace δ] {e₁ : α → β} {e₂ : γ → δ}
    (de₁ : IsDenseInducing e₁) (de₂ : IsDenseInducing e₂) :
    IsDenseInducing (Prod.map e₁ e₂) where
  toIsInducing := de₁.isInducing.prodMap de₂.isInducing
  dense := de₁.dense.prodMap de₂.dense

open TopologicalSpace

/-- If the domain of a `IsDenseInducing` map is a separable space, then so is the codomain. -/
protected theorem separableSpace [SeparableSpace α] (di : IsDenseInducing i) : SeparableSpace β :=
  di.dense.separableSpace di.continuous

variable [TopologicalSpace δ] {f : γ → α} {g : γ → δ} {h : δ → β}

/--
```
 γ -f→ α
g↓     ↓e
 δ -h→ β
```
-/
theorem tendsto_comap_nhds_nhds {d : δ} {a : α} (di : IsDenseInducing i)
    (H : Tendsto h (𝓝 d) (𝓝 (i a))) (comm : h ∘ g = i ∘ f) : Tendsto f (comap g (𝓝 d)) (𝓝 a) := by
  have lim1 : map g (comap g (𝓝 d)) ≤ 𝓝 d := map_comap_le
  replace lim1 : map h (map g (comap g (𝓝 d))) ≤ map h (𝓝 d) := map_mono lim1
  rw [Filter.map_map, comm, ← Filter.map_map, map_le_iff_le_comap] at lim1
  have lim2 : comap i (map h (𝓝 d)) ≤ comap i (𝓝 (i a)) := comap_mono H
  rw [← di.nhds_eq_comap] at lim2
  exact le_trans lim1 lim2

protected theorem nhdsWithin_neBot (di : IsDenseInducing i) (b : β) : NeBot (𝓝[range i] b) :=
  di.dense.nhdsWithin_neBot b

theorem comap_nhds_neBot (di : IsDenseInducing i) (b : β) : NeBot (comap i (𝓝 b)) :=
  comap_neBot fun s hs => by
    rcases mem_closure_iff_nhds.1 (di.dense b) s hs with ⟨_, ⟨ha, a, rfl⟩⟩
    exact ⟨a, ha⟩

variable [TopologicalSpace γ]

/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends" to a function `g =
  IsDenseInducing.extend di f : β → γ`. If `γ` is Hausdorff and `f` has a continuous extension, then
  `g` is the unique such extension. In general, `g` might not be continuous or even extend `f`. -/
def extend (di : IsDenseInducing i) (f : α → γ) (b : β) : γ :=
  @limUnder _ _ _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f

theorem extend_eq_of_tendsto [T2Space γ] (di : IsDenseInducing i) {b : β} {c : γ} {f : α → γ}
    (hf : Tendsto f (comap i (𝓝 b)) (𝓝 c)) : di.extend f b = c :=
  haveI := di.comap_nhds_neBot
  hf.limUnder_eq

theorem extend_eq_at [T2Space γ] (di : IsDenseInducing i) {f : α → γ} {a : α}
    (hf : ContinuousAt f a) : di.extend f (i a) = f a :=
  extend_eq_of_tendsto _ <| di.nhds_eq_comap a ▸ hf

theorem extend_eq_at' [T2Space γ] (di : IsDenseInducing i) {f : α → γ} {a : α} (c : γ)
    (hf : Tendsto f (𝓝 a) (𝓝 c)) : di.extend f (i a) = f a :=
  di.extend_eq_at (continuousAt_of_tendsto_nhds hf)

theorem extend_eq [T2Space γ] (di : IsDenseInducing i) {f : α → γ} (hf : Continuous f) (a : α) :
    di.extend f (i a) = f a :=
  di.extend_eq_at hf.continuousAt

/-- Variation of `extend_eq` where we ask that `f` has a limit along `comap i (𝓝 b)` for each
`b : β`. This is a strictly stronger assumption than continuity of `f`, but in a lot of cases
you'd have to prove it anyway to use `continuous_extend`, so this avoids doing the work twice. -/
theorem extend_eq' [T2Space γ] {f : α → γ} (di : IsDenseInducing i)
    (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) (a : α) : di.extend f (i a) = f a := by
  rcases hf (i a) with ⟨b, hb⟩
  refine di.extend_eq_at' b ?_
  rwa [← di.isInducing.nhds_eq_comap] at hb

theorem extend_unique_at [T2Space γ] {b : β} {f : α → γ} {g : β → γ} (di : IsDenseInducing i)
    (hf : ∀ᶠ x in comap i (𝓝 b), g (i x) = f x) (hg : ContinuousAt g b) : di.extend f b = g b := by
  refine di.extend_eq_of_tendsto fun s hs => mem_map.2 ?_
  suffices ∀ᶠ x : α in comap i (𝓝 b), g (i x) ∈ s from
    hf.mp (this.mono fun x hgx hfx => hfx ▸ hgx)
  clear hf f
  refine eventually_comap.2 ((hg.eventually hs).mono ?_)
  rintro _ hxs x rfl
  exact hxs

theorem extend_unique [T2Space γ] {f : α → γ} {g : β → γ} (di : IsDenseInducing i)
    (hf : ∀ x, g (i x) = f x) (hg : Continuous g) : di.extend f = g :=
  funext fun _ => extend_unique_at di (Eventually.of_forall hf) hg.continuousAt

theorem continuousAt_extend [T3Space γ] {b : β} {f : α → γ} (di : IsDenseInducing i)
    (hf : ∀ᶠ x in 𝓝 b, ∃ c, Tendsto f (comap i <| 𝓝 x) (𝓝 c)) : ContinuousAt (di.extend f) b := by
  set φ := di.extend f
  haveI := di.comap_nhds_neBot
  suffices ∀ V' ∈ 𝓝 (φ b), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 b by
    simpa [ContinuousAt, (closed_nhds_basis (φ b)).tendsto_right_iff]
  intro V' V'_in V'_closed
  set V₁ := { x | Tendsto f (comap i <| 𝓝 x) (𝓝 <| φ x) }
  have V₁_in : V₁ ∈ 𝓝 b := by
    filter_upwards [hf]
    rintro x ⟨c, hc⟩
    rwa [← di.extend_eq_of_tendsto hc] at hc
  obtain ⟨V₂, V₂_in, V₂_op, hV₂⟩ : ∃ V₂ ∈ 𝓝 b, IsOpen V₂ ∧ ∀ x ∈ i ⁻¹' V₂, f x ∈ V' := by
    simpa [and_assoc] using
      ((nhds_basis_opens' b).comap i).tendsto_left_iff.mp (mem_of_mem_nhds V₁_in : b ∈ V₁) V' V'_in
  suffices ∀ x ∈ V₁ ∩ V₂, φ x ∈ V' by filter_upwards [inter_mem V₁_in V₂_in] using this
  rintro x ⟨x_in₁, x_in₂⟩
  have hV₂x : V₂ ∈ 𝓝 x := IsOpen.mem_nhds V₂_op x_in₂
  apply V'_closed.mem_of_tendsto x_in₁
  use V₂
  tauto

theorem continuous_extend [T3Space γ] {f : α → γ} (di : IsDenseInducing i)
    (hf : ∀ b, ∃ c, Tendsto f (comap i (𝓝 b)) (𝓝 c)) : Continuous (di.extend f) :=
  continuous_iff_continuousAt.mpr fun _ => di.continuousAt_extend <| univ_mem' hf

theorem mk' (i : α → β) (c : Continuous i) (dense : ∀ x, x ∈ closure (range i))
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∃ t ∈ 𝓝 (i a), ∀ b, i b ∈ t → b ∈ s) : IsDenseInducing i where
  toIsInducing := isInducing_iff_nhds.2 fun a =>
      le_antisymm (c.tendsto _).le_comap (by simpa [Filter.le_def] using H a)
  dense := dense

end IsDenseInducing

namespace Dense

variable [TopologicalSpace α] [TopologicalSpace β] {s : Set α}

/-- This is a shortcut for `hs.isDenseInducing_val.extend f`. It is useful because if `s : Set α`
is dense then the coercion `(↑) : s → α` automatically satisfies `IsUniformInducing` and
`IsDenseInducing` so this gives access to the theorems satisfied by a uniform extension by simply
mentioning the density hypothesis. -/
noncomputable def extend (hs : Dense s) (f : s → β) : α → β :=
    hs.isDenseInducing_val.extend f

variable {f : s → β}

theorem extend_eq_of_tendsto [T2Space β] (hs : Dense s) {a : α} {b : β}
    (hf : Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)) : hs.extend f a = b :=
  hs.isDenseInducing_val.extend_eq_of_tendsto hf

theorem extend_eq_at [T2Space β] (hs : Dense s) {f : s → β} {x : s}
    (hf : ContinuousAt f x) : hs.extend f x = f x :=
  hs.isDenseInducing_val.extend_eq_at hf

theorem extend_eq [T2Space β] (hs : Dense s) (hf : Continuous f) (x : s) :
    hs.extend f x = f x :=
  hs.extend_eq_at hf.continuousAt

theorem extend_unique_at [T2Space β] {a : α} {g : α → β} (hs : Dense s)
    (hf : ∀ᶠ x : s in comap (↑) (𝓝 a), g x = f x) (hg : ContinuousAt g a) :
    hs.extend f a = g a :=
  hs.isDenseInducing_val.extend_unique_at hf hg

theorem extend_unique [T2Space β] {g : α → β} (hs : Dense s)
    (hf : ∀ x : s, g x = f x) (hg : Continuous g) : hs.extend f = g :=
  hs.isDenseInducing_val.extend_unique hf hg

theorem continuousAt_extend [T3Space β] {a : α} (hs : Dense s)
    (hf : ∀ᶠ x in 𝓝 a, ∃ b, Tendsto f (comap (↑) <| 𝓝 x) (𝓝 b)) :
    ContinuousAt (hs.extend f) a :=
  hs.isDenseInducing_val.continuousAt_extend hf

theorem continuous_extend [T3Space β] (hs : Dense s)
    (hf : ∀ a : α, ∃ b, Tendsto f (comap (↑) (𝓝 a)) (𝓝 b)) : Continuous (hs.extend f) :=
  hs.isDenseInducing_val.continuous_extend hf

end Dense

/-- A dense embedding is an embedding with dense image. -/
structure IsDenseEmbedding [TopologicalSpace α] [TopologicalSpace β] (e : α → β) : Prop
    extends IsDenseInducing e where
  /-- A dense embedding is injective. -/
  injective : Function.Injective e

lemma IsDenseEmbedding.mk' [TopologicalSpace α] [TopologicalSpace β] (e : α → β) (c : Continuous e)
    (dense : DenseRange e) (injective : Function.Injective e)
    (H : ∀ (a : α), ∀ s ∈ 𝓝 a, ∃ t ∈ 𝓝 (e a), ∀ b, e b ∈ t → b ∈ s) : IsDenseEmbedding e :=
  { IsDenseInducing.mk' e c dense H with injective }

namespace IsDenseEmbedding

open TopologicalSpace

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]
variable {e : α → β}

lemma isDenseInducing (de : IsDenseEmbedding e) : IsDenseInducing e := de.toIsDenseInducing

theorem inj_iff (de : IsDenseEmbedding e) {x y} : e x = e y ↔ x = y :=
  de.injective.eq_iff

theorem isEmbedding (de : IsDenseEmbedding e) : IsEmbedding e where __ := de

@[deprecated (since := "2024-10-26")]
alias to_embedding := isEmbedding

/-- If the domain of a `IsDenseEmbedding` is a separable space, then so is its codomain. -/
protected theorem separableSpace [SeparableSpace α] (de : IsDenseEmbedding e) : SeparableSpace β :=
  de.isDenseInducing.separableSpace

/-- The product of two dense embeddings is a dense embedding. -/
protected theorem prodMap {e₁ : α → β} {e₂ : γ → δ} (de₁ : IsDenseEmbedding e₁)
    (de₂ : IsDenseEmbedding e₂) : IsDenseEmbedding fun p : α × γ => (e₁ p.1, e₂ p.2) where
  toIsDenseInducing := de₁.isDenseInducing.prodMap de₂.isDenseInducing
  injective := de₁.injective.prodMap de₂.injective

/-- The dense embedding of a subtype inside its closure. -/
@[simps]
def subtypeEmb {α : Type*} (p : α → Prop) (e : α → β) (x : { x // p x }) :
    { x // x ∈ closure (e '' { x | p x }) } :=
  ⟨e x, subset_closure <| mem_image_of_mem e x.prop⟩

protected theorem subtype (de : IsDenseEmbedding e) (p : α → Prop) :
    IsDenseEmbedding (subtypeEmb p e) where
  dense :=
    dense_iff_closure_eq.2 <| by
      ext ⟨x, hx⟩
      rw [image_eq_range] at hx
      simpa [closure_subtype, ← range_comp, (· ∘ ·)]
  injective := (de.injective.comp Subtype.coe_injective).codRestrict _
  eq_induced :=
    (induced_iff_nhds_eq _).2 fun ⟨x, hx⟩ => by
      simp [subtypeEmb, nhds_subtype_eq_comap, de.isInducing.nhds_eq_comap, comap_comap,
        Function.comp_def]

theorem dense_image (de : IsDenseEmbedding e) {s : Set α} : Dense (e '' s) ↔ Dense s :=
  de.isDenseInducing.dense_image

protected lemma id {α : Type*} [TopologicalSpace α] : IsDenseEmbedding (id : α → α) :=
  { IsEmbedding.id with dense := denseRange_id }

end IsDenseEmbedding

theorem Dense.isDenseEmbedding_val [TopologicalSpace α] {s : Set α} (hs : Dense s) :
    IsDenseEmbedding ((↑) : s → α) :=
  { IsEmbedding.subtypeVal with dense := hs.denseRange_val }

theorem isClosed_property [TopologicalSpace β] {e : α → β} {p : β → Prop} (he : DenseRange e)
    (hp : IsClosed { x | p x }) (h : ∀ a, p (e a)) : ∀ b, p b := by
  have : univ ⊆ { b | p b } :=
    calc
      univ = closure (range e) := he.closure_range.symm
      _ ⊆ closure { b | p b } := closure_mono <| range_subset_iff.mpr h
      _ = _ := hp.closure_eq
  simpa only [univ_subset_iff, eq_univ_iff_forall, mem_setOf]

theorem isClosed_property2 [TopologicalSpace β] {e : α → β} {p : β → β → Prop} (he : DenseRange e)
    (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂)) : ∀ b₁ b₂, p b₁ b₂ :=
  have : ∀ q : β × β, p q.1 q.2 := isClosed_property (he.prodMap he) hp fun _ => h _ _
  fun b₁ b₂ => this ⟨b₁, b₂⟩

theorem isClosed_property3 [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) : ∀ b₁ b₂ b₃, p b₁ b₂ b₃ :=
  have : ∀ q : β × β × β, p q.1 q.2.1 q.2.2 :=
    isClosed_property (he.prodMap <| he.prodMap he) hp fun _ => h _ _ _
  fun b₁ b₂ b₃ => this ⟨b₁, b₂, b₃⟩

@[elab_as_elim]
theorem DenseRange.induction_on [TopologicalSpace β] {e : α → β} (he : DenseRange e) {p : β → Prop}
    (b₀ : β) (hp : IsClosed { b | p b }) (ih : ∀ a : α, p <| e a) : p b₀ :=
  isClosed_property he hp ih b₀

@[elab_as_elim]
theorem DenseRange.induction_on₂ [TopologicalSpace β] {e : α → β} {p : β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β | p q.1 q.2 }) (h : ∀ a₁ a₂, p (e a₁) (e a₂))
    (b₁ b₂ : β) : p b₁ b₂ :=
  isClosed_property2 he hp h _ _

@[elab_as_elim]
theorem DenseRange.induction_on₃ [TopologicalSpace β] {e : α → β} {p : β → β → β → Prop}
    (he : DenseRange e) (hp : IsClosed { q : β × β × β | p q.1 q.2.1 q.2.2 })
    (h : ∀ a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) (b₁ b₂ b₃ : β) : p b₁ b₂ b₃ :=
  isClosed_property3 he hp h _ _ _

section

variable [TopologicalSpace β] [TopologicalSpace γ] [T2Space γ]
variable {f : α → β}

/-- Two continuous functions to a t2-space that agree on the dense range of a function are equal. -/
theorem DenseRange.equalizer (hfd : DenseRange f) {g h : β → γ} (hg : Continuous g)
    (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h :=
  funext fun y => hfd.induction_on y (isClosed_eq hg hh) <| congr_fun H

end

-- Bourbaki GT III §3 no.4 Proposition 7 (generalised to any dense-inducing map to a regular space)
theorem Filter.HasBasis.hasBasis_of_isDenseInducing [TopologicalSpace α] [TopologicalSpace β]
    [RegularSpace β] {ι : Type*} {s : ι → Set α} {p : ι → Prop} {x : α} (h : (𝓝 x).HasBasis p s)
    {f : α → β} (hf : IsDenseInducing f) : (𝓝 (f x)).HasBasis p fun i => closure <| f '' s i := by
  rw [Filter.hasBasis_iff] at h ⊢
  intro T
  refine ⟨fun hT => ?_, fun hT => ?_⟩
  · obtain ⟨T', hT₁, hT₂, hT₃⟩ := exists_mem_nhds_isClosed_subset hT
    have hT₄ : f ⁻¹' T' ∈ 𝓝 x := by
      rw [hf.isInducing.nhds_eq_comap x]
      exact ⟨T', hT₁, Subset.rfl⟩
    obtain ⟨i, hi, hi'⟩ := (h _).mp hT₄
    exact
      ⟨i, hi,
        (closure_mono (image_subset f hi')).trans
          (Subset.trans (closure_minimal (image_preimage_subset _ _) hT₂) hT₃)⟩
  · obtain ⟨i, hi, hi'⟩ := hT
    suffices closure (f '' s i) ∈ 𝓝 (f x) by filter_upwards [this] using hi'
    replace h := (h (s i)).mpr ⟨i, hi, Subset.rfl⟩
    exact hf.closure_image_mem_nhds h
