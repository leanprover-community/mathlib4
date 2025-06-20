/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Maps.Basic

/-!
# Disjoint unions and products of topological spaces

This file constructs sums (disjoint unions) and products of topological spaces
and sets up their basic theory, such as criteria for maps into or out of these
constructions to be continuous; descriptions of the open sets, neighborhood filters,
and generators of these constructions; and their behavior with respect to embeddings
and other specific classes of maps.

We also provide basic homeomorphisms, to show that sums and products are commutative, associative
and distributive (up to homeomorphism).

## Implementation note

The constructed topologies are defined using induced and coinduced topologies
along with the complete lattice structure on topologies. Their universal properties
(for example, a map `X → Y × Z` is continuous if and only if both projections
`X → Y`, `X → Z` are) follow easily using order-theoretic descriptions of
continuity. With more work we can also extract descriptions of the open sets,
neighborhood filters and so on.

## Tags

product, sum, disjoint union

-/

noncomputable section

open Topology TopologicalSpace Set Filter Function

universe u v u' v'

variable {X : Type u} {Y : Type v} {W Z ε ζ : Type*}

instance instTopologicalSpaceSum [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X ⊕ Y) :=
  coinduced Sum.inl t₁ ⊔ coinduced Sum.inr t₂

instance instTopologicalSpaceProd [t₁ : TopologicalSpace X] [t₂ : TopologicalSpace Y] :
    TopologicalSpace (X × Y) :=
  induced Prod.fst t₁ ⊓ induced Prod.snd t₂

section Prod

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace W]
  [TopologicalSpace ε] [TopologicalSpace ζ]

@[simp]
theorem continuous_prodMk {f : X → Y} {g : X → Z} :
    (Continuous fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g :=
  continuous_inf_rng.trans <| continuous_induced_rng.and continuous_induced_rng

@[deprecated (since := "2025-03-10")]
alias continuous_prod_mk := continuous_prodMk

@[continuity]
theorem continuous_fst : Continuous (@Prod.fst X Y) :=
  (continuous_prodMk.1 continuous_id).1

/-- Postcomposing `f` with `Prod.fst` is continuous -/
@[fun_prop]
theorem Continuous.fst {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).1 :=
  continuous_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is continuous -/
theorem Continuous.fst' {f : X → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.fst :=
  hf.comp continuous_fst

theorem continuousAt_fst {p : X × Y} : ContinuousAt Prod.fst p :=
  continuous_fst.continuousAt

/-- Postcomposing `f` with `Prod.fst` is continuous at `x` -/
@[fun_prop]
theorem ContinuousAt.fst {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).1) x :=
  continuousAt_fst.comp hf

/-- Precomposing `f` with `Prod.fst` is continuous at `(x, y)` -/
theorem ContinuousAt.fst' {f : X → Z} {x : X} {y : Y} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X × Y => f x.fst) (x, y) :=
  ContinuousAt.comp hf continuousAt_fst

/-- Precomposing `f` with `Prod.fst` is continuous at `x : X × Y` -/
theorem ContinuousAt.fst'' {f : X → Z} {x : X × Y} (hf : ContinuousAt f x.fst) :
    ContinuousAt (fun x : X × Y => f x.fst) x :=
  hf.comp continuousAt_fst

theorem Filter.Tendsto.fst_nhds {X} {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).1) l (𝓝 <| p.1) :=
  continuousAt_fst.tendsto.comp h

@[continuity]
theorem continuous_snd : Continuous (@Prod.snd X Y) :=
  (continuous_prodMk.1 continuous_id).2

/-- Postcomposing `f` with `Prod.snd` is continuous -/
@[fun_prop]
theorem Continuous.snd {f : X → Y × Z} (hf : Continuous f) : Continuous fun x : X => (f x).2 :=
  continuous_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is continuous -/
theorem Continuous.snd' {f : Y → Z} (hf : Continuous f) : Continuous fun x : X × Y => f x.snd :=
  hf.comp continuous_snd

theorem continuousAt_snd {p : X × Y} : ContinuousAt Prod.snd p :=
  continuous_snd.continuousAt

/-- Postcomposing `f` with `Prod.snd` is continuous at `x` -/
@[fun_prop]
theorem ContinuousAt.snd {f : X → Y × Z} {x : X} (hf : ContinuousAt f x) :
    ContinuousAt (fun x : X => (f x).2) x :=
  continuousAt_snd.comp hf

/-- Precomposing `f` with `Prod.snd` is continuous at `(x, y)` -/
theorem ContinuousAt.snd' {f : Y → Z} {x : X} {y : Y} (hf : ContinuousAt f y) :
    ContinuousAt (fun x : X × Y => f x.snd) (x, y) :=
  ContinuousAt.comp hf continuousAt_snd

/-- Precomposing `f` with `Prod.snd` is continuous at `x : X × Y` -/
theorem ContinuousAt.snd'' {f : Y → Z} {x : X × Y} (hf : ContinuousAt f x.snd) :
    ContinuousAt (fun x : X × Y => f x.snd) x :=
  hf.comp continuousAt_snd

theorem Filter.Tendsto.snd_nhds {X} {l : Filter X} {f : X → Y × Z} {p : Y × Z}
    (h : Tendsto f l (𝓝 p)) : Tendsto (fun a ↦ (f a).2) l (𝓝 <| p.2) :=
  continuousAt_snd.tendsto.comp h

@[continuity, fun_prop]
theorem Continuous.prodMk {f : Z → X} {g : Z → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => (f x, g x) :=
  continuous_prodMk.2 ⟨hf, hg⟩

@[deprecated (since := "2025-03-10")]
alias Continuous.prod_mk := Continuous.prodMk

@[continuity]
theorem Continuous.prodMk_right (x : X) : Continuous fun y : Y => (x, y) := by fun_prop

@[deprecated (since := "2025-03-10")]
alias Continuous.Prod.mk := Continuous.prodMk_right

@[continuity]
theorem Continuous.prodMk_left (y : Y) : Continuous fun x : X => (x, y) := by fun_prop

@[deprecated (since := "2025-03-10")]
alias Continuous.Prod.mk_left := Continuous.prodMk_left

/-- If `f x y` is continuous in `x` for all `y ∈ s`,
then the set of `x` such that `f x` maps `s` to `t` is closed. -/
lemma IsClosed.setOf_mapsTo {α : Type*} {f : X → α → Z} {s : Set α} {t : Set Z} (ht : IsClosed t)
    (hf : ∀ a ∈ s, Continuous (f · a)) : IsClosed {x | MapsTo (f x) s t} := by
  simpa only [MapsTo, setOf_forall] using isClosed_biInter fun y hy ↦ ht.preimage (hf y hy)

theorem Continuous.comp₂ {g : X × Y → Z} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) : Continuous fun w => g (e w, f w) :=
  hg.comp <| he.prodMk hf

theorem Continuous.comp₃ {g : X × Y × Z → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) :
    Continuous fun w => g (e w, f w, k w) :=
  hg.comp₂ he <| hf.prodMk hk

theorem Continuous.comp₄ {g : X × Y × Z × ζ → ε} (hg : Continuous g) {e : W → X} (he : Continuous e)
    {f : W → Y} (hf : Continuous f) {k : W → Z} (hk : Continuous k) {l : W → ζ}
    (hl : Continuous l) : Continuous fun w => g (e w, f w, k w, l w) :=
  hg.comp₃ he hf <| hk.prodMk hl

@[continuity, fun_prop]
theorem Continuous.prodMap {f : Z → X} {g : W → Y} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Prod.map f g) :=
  hf.fst'.prodMk hg.snd'

/-- A version of `continuous_inf_dom_left` for binary functions -/
theorem continuous_inf_dom_left₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta1; haveI := tb1; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_left _ _ id ta1 ta2 ta1 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_left _ _ id tb1 tb2 tb1 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta1 tb1 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_inf_dom_right` for binary functions -/
theorem continuous_inf_dom_right₂ {X Y Z} {f : X → Y → Z} {ta1 ta2 : TopologicalSpace X}
    {tb1 tb2 : TopologicalSpace Y} {tc1 : TopologicalSpace Z}
    (h : by haveI := ta2; haveI := tb2; exact Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := ta1 ⊓ ta2; haveI := tb1 ⊓ tb2; exact Continuous fun p : X × Y => f p.1 p.2 := by
  have ha := @continuous_inf_dom_right _ _ id ta1 ta2 ta2 (@continuous_id _ (id _))
  have hb := @continuous_inf_dom_right _ _ id tb1 tb2 tb2 (@continuous_id _ (id _))
  have h_continuous_id := @Continuous.prodMap _ _ _ _ ta2 tb2 (ta1 ⊓ ta2) (tb1 ⊓ tb2) _ _ ha hb
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ h h_continuous_id

/-- A version of `continuous_sInf_dom` for binary functions -/
theorem continuous_sInf_dom₂ {X Y Z} {f : X → Y → Z} {tas : Set (TopologicalSpace X)}
    {tbs : Set (TopologicalSpace Y)} {tX : TopologicalSpace X} {tY : TopologicalSpace Y}
    {tc : TopologicalSpace Z} (hX : tX ∈ tas) (hY : tY ∈ tbs)
    (hf : Continuous fun p : X × Y => f p.1 p.2) : by
    haveI := sInf tas; haveI := sInf tbs
    exact @Continuous _ _ _ tc fun p : X × Y => f p.1 p.2 := by
  have hX := continuous_sInf_dom hX continuous_id
  have hY := continuous_sInf_dom hY continuous_id
  have h_continuous_id := @Continuous.prodMap _ _ _ _ tX tY (sInf tas) (sInf tbs) _ _ hX hY
  exact @Continuous.comp _ _ _ (id _) (id _) _ _ _ hf h_continuous_id

theorem Filter.Eventually.prod_inl_nhds {p : X → Prop} {x : X} (h : ∀ᶠ x in 𝓝 x, p x) (y : Y) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).1 :=
  continuousAt_fst h

theorem Filter.Eventually.prod_inr_nhds {p : Y → Prop} {y : Y} (h : ∀ᶠ x in 𝓝 y, p x) (x : X) :
    ∀ᶠ x in 𝓝 (x, y), p (x : X × Y).2 :=
  continuousAt_snd h

theorem Filter.Eventually.prodMk_nhds {px : X → Prop} {x} (hx : ∀ᶠ x in 𝓝 x, px x) {py : Y → Prop}
    {y} (hy : ∀ᶠ y in 𝓝 y, py y) : ∀ᶠ p in 𝓝 (x, y), px (p : X × Y).1 ∧ py p.2 :=
  (hx.prod_inl_nhds y).and (hy.prod_inr_nhds x)

@[deprecated (since := "2025-03-10")]
alias Filter.Eventually.prod_mk_nhds := Filter.Eventually.prodMk_nhds

theorem continuous_swap : Continuous (Prod.swap : X × Y → Y × X) :=
  continuous_snd.prodMk continuous_fst

lemma isClosedMap_swap : IsClosedMap (Prod.swap : X × Y → Y × X) := fun s hs ↦ by
  rw [image_swap_eq_preimage_swap]
  exact hs.preimage continuous_swap

theorem Continuous.uncurry_left {f : X → Y → Z} (x : X) (h : Continuous (uncurry f)) :
    Continuous (f x) :=
  h.comp (.prodMk_right _)

theorem Continuous.uncurry_right {f : X → Y → Z} (y : Y) (h : Continuous (uncurry f)) :
    Continuous fun a => f a y :=
  h.comp (.prodMk_left _)

theorem continuous_curry {g : X × Y → Z} (x : X) (h : Continuous g) : Continuous (curry g x) :=
  Continuous.uncurry_left x h

theorem IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ˢ t) :=
  (hs.preimage continuous_fst).inter (ht.preimage continuous_snd)

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: Lean fails to find `t₁` and `t₂` by unification
theorem nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y := by
  rw [prod_eq_inf, instTopologicalSpaceProd, nhds_inf (t₁ := TopologicalSpace.induced Prod.fst _)
    (t₂ := TopologicalSpace.induced Prod.snd _), nhds_induced, nhds_induced]

theorem nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : Set Y) :
    𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y := by
  simp only [nhdsWithin, nhds_prod_eq, ← prod_inf_prod, prod_principal_principal]

instance Prod.instNeBotNhdsWithinIio [Preorder X] [Preorder Y] {x : X × Y}
    [hx₁ : (𝓝[<] x.1).NeBot] [hx₂ : (𝓝[<] x.2).NeBot] : (𝓝[<] x).NeBot := by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
  exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ ↦ Prod.lt_iff.2 <| .inl ⟨h₁, h₂.le⟩

instance Prod.instNeBotNhdsWithinIoi [Preorder X] [Preorder Y] {x : X × Y}
    [hx₁ : (𝓝[>] x.1).NeBot] [hx₂ : (𝓝[>] x.2).NeBot] : (𝓝[>] x).NeBot := by
  refine (hx₁.prod hx₂).mono ?_
  rw [← nhdsWithin_prod_eq]
  exact nhdsWithin_mono _ fun _ ⟨h₁, h₂⟩ ↦ Prod.lt_iff.2 <| .inl ⟨h₁, h₂.le⟩

theorem mem_nhds_prod_iff {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u ∈ 𝓝 x, ∃ v ∈ 𝓝 y, u ×ˢ v ⊆ s := by rw [nhds_prod_eq, mem_prod_iff]

theorem mem_nhdsWithin_prod_iff {x : X} {y : Y} {s : Set (X × Y)} {tx : Set X} {ty : Set Y} :
    s ∈ 𝓝[tx ×ˢ ty] (x, y) ↔ ∃ u ∈ 𝓝[tx] x, ∃ v ∈ 𝓝[ty] y, u ×ˢ v ⊆ s := by
  rw [nhdsWithin_prod_eq, mem_prod_iff]

theorem Filter.HasBasis.prod_nhds {ιX ιY : Type*} {px : ιX → Prop} {py : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {x : X} {y : Y} (hx : (𝓝 x).HasBasis px sx)
    (hy : (𝓝 y).HasBasis py sy) :
    (𝓝 (x, y)).HasBasis (fun i : ιX × ιY => px i.1 ∧ py i.2) fun i => sx i.1 ×ˢ sy i.2 := by
  rw [nhds_prod_eq]
  exact hx.prod hy

theorem Filter.HasBasis.prod_nhds' {ιX ιY : Type*} {pX : ιX → Prop} {pY : ιY → Prop}
    {sx : ιX → Set X} {sy : ιY → Set Y} {p : X × Y} (hx : (𝓝 p.1).HasBasis pX sx)
    (hy : (𝓝 p.2).HasBasis pY sy) :
    (𝓝 p).HasBasis (fun i : ιX × ιY => pX i.1 ∧ pY i.2) fun i => sx i.1 ×ˢ sy i.2 :=
  hx.prod_nhds hy

theorem mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)} :
    s ∈ 𝓝 (x, y) ↔ ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧ u ×ˢ v ⊆ s :=
  ((nhds_basis_opens x).prod_nhds (nhds_basis_opens y)).mem_iff.trans <| by
    simp only [Prod.exists, and_comm, and_assoc, and_left_comm]

theorem Prod.tendsto_iff {X} (seq : X → Y × Z) {f : Filter X} (p : Y × Z) :
    Tendsto seq f (𝓝 p) ↔
      Tendsto (fun n => (seq n).fst) f (𝓝 p.fst) ∧ Tendsto (fun n => (seq n).snd) f (𝓝 p.snd) := by
  rw [nhds_prod_eq, Filter.tendsto_prod_iff']

instance [DiscreteTopology X] [DiscreteTopology Y] : DiscreteTopology (X × Y) :=
  discreteTopology_iff_nhds.2 fun (a, b) => by
    rw [nhds_prod_eq, nhds_discrete X, nhds_discrete Y, prod_pure_pure]

theorem prod_mem_nhds_iff {s : Set X} {t : Set Y} {x : X} {y : Y} :
    s ×ˢ t ∈ 𝓝 (x, y) ↔ s ∈ 𝓝 x ∧ t ∈ 𝓝 y := by rw [nhds_prod_eq, prod_mem_prod_iff]

theorem prod_mem_nhds {s : Set X} {t : Set Y} {x : X} {y : Y} (hx : s ∈ 𝓝 x) (hy : t ∈ 𝓝 y) :
    s ×ˢ t ∈ 𝓝 (x, y) :=
  prod_mem_nhds_iff.2 ⟨hx, hy⟩

theorem isOpen_setOf_disjoint_nhds_nhds : IsOpen { p : X × X | Disjoint (𝓝 p.1) (𝓝 p.2) } := by
  simp only [isOpen_iff_mem_nhds, Prod.forall, mem_setOf_eq]
  intro x y h
  obtain ⟨U, hU, V, hV, hd⟩ := ((nhds_basis_opens x).disjoint_iff (nhds_basis_opens y)).mp h
  exact mem_nhds_prod_iff'.mpr ⟨U, V, hU.2, hU.1, hV.2, hV.1, fun ⟨x', y'⟩ ⟨hx', hy'⟩ =>
    disjoint_of_disjoint_of_mem hd (hU.2.mem_nhds hx') (hV.2.mem_nhds hy')⟩

theorem Filter.Eventually.prod_nhds {p : X → Prop} {q : Y → Prop} {x : X} {y : Y}
    (hx : ∀ᶠ x in 𝓝 x, p x) (hy : ∀ᶠ y in 𝓝 y, q y) : ∀ᶠ z : X × Y in 𝓝 (x, y), p z.1 ∧ q z.2 :=
  prod_mem_nhds hx hy

theorem Filter.EventuallyEq.prodMap_nhds {α β : Type*} {f₁ f₂ : X → α} {g₁ g₂ : Y → β}
    {x : X} {y : Y} (hf : f₁ =ᶠ[𝓝 x] f₂) (hg : g₁ =ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ =ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

theorem Filter.EventuallyLE.prodMap_nhds {α β : Type*} [LE α] [LE β] {f₁ f₂ : X → α} {g₁ g₂ : Y → β}
    {x : X} {y : Y} (hf : f₁ ≤ᶠ[𝓝 x] f₂) (hg : g₁ ≤ᶠ[𝓝 y] g₂) :
    Prod.map f₁ g₁ ≤ᶠ[𝓝 (x, y)] Prod.map f₂ g₂ := by
  rw [nhds_prod_eq]
  exact hf.prodMap hg

theorem nhds_swap (x : X) (y : Y) : 𝓝 (x, y) = (𝓝 (y, x)).map Prod.swap := by
  rw [nhds_prod_eq, Filter.prod_comm, nhds_prod_eq]; rfl

theorem Filter.Tendsto.prodMk_nhds {γ} {x : X} {y : Y} {f : Filter γ} {mx : γ → X} {my : γ → Y}
    (hx : Tendsto mx f (𝓝 x)) (hy : Tendsto my f (𝓝 y)) :
    Tendsto (fun c => (mx c, my c)) f (𝓝 (x, y)) := by
  rw [nhds_prod_eq]
  exact hx.prodMk hy

@[deprecated (since := "2025-03-10")]
alias Filter.Tendsto.prod_mk_nhds := Filter.Tendsto.prodMk_nhds

theorem Filter.Tendsto.prodMap_nhds {x : X} {y : Y} {z : Z} {w : W} {f : X → Y} {g : Z → W}
    (hf : Tendsto f (𝓝 x) (𝓝 y)) (hg : Tendsto g (𝓝 z) (𝓝 w)) :
    Tendsto (Prod.map f g) (𝓝 (x, z)) (𝓝 (y, w)) := by
  rw [nhds_prod_eq, nhds_prod_eq]
  exact hf.prodMap hg

theorem Filter.Eventually.curry_nhds {p : X × Y → Prop} {x : X} {y : Y}
    (h : ∀ᶠ x in 𝓝 (x, y), p x) : ∀ᶠ x' in 𝓝 x, ∀ᶠ y' in 𝓝 y, p (x', y') := by
  rw [nhds_prod_eq] at h
  exact h.curry

@[fun_prop]
theorem ContinuousAt.prodMk {f : X → Y} {g : X → Z} {x : X} (hf : ContinuousAt f x)
    (hg : ContinuousAt g x) : ContinuousAt (fun x => (f x, g x)) x :=
  hf.prodMk_nhds hg

@[deprecated (since := "2025-03-10")]
alias ContinuousAt.prod := ContinuousAt.prodMk

theorem ContinuousAt.prodMap {f : X → Z} {g : Y → W} {p : X × Y} (hf : ContinuousAt f p.fst)
    (hg : ContinuousAt g p.snd) : ContinuousAt (Prod.map f g) p :=
  hf.fst''.prodMk hg.snd''

/-- A version of `ContinuousAt.prodMap` that avoids `Prod.fst`/`Prod.snd`
by assuming that the point is `(x, y)`. -/
theorem ContinuousAt.prodMap' {f : X → Z} {g : Y → W} {x : X} {y : Y} (hf : ContinuousAt f x)
    (hg : ContinuousAt g y) : ContinuousAt (Prod.map f g) (x, y) :=
  hf.prodMap hg

theorem ContinuousAt.comp₂ {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X}
    (hf : ContinuousAt f (g x, h x)) (hg : ContinuousAt g x) (hh : ContinuousAt h x) :
    ContinuousAt (fun x ↦ f (g x, h x)) x :=
  ContinuousAt.comp hf (hg.prodMk hh)

theorem ContinuousAt.comp₂_of_eq {f : Y × Z → W} {g : X → Y} {h : X → Z} {x : X} {y : Y × Z}
    (hf : ContinuousAt f y) (hg : ContinuousAt g x) (hh : ContinuousAt h x) (e : (g x, h x) = y) :
    ContinuousAt (fun x ↦ f (g x, h x)) x := by
  rw [← e] at hf
  exact hf.comp₂ hg hh

/-- Continuous functions on products are continuous in their first argument -/
theorem Continuous.curry_left {f : X × Y → Z} (hf : Continuous f) {y : Y} :
    Continuous fun x ↦ f (x, y) :=
  hf.comp (.prodMk_left _)
alias Continuous.along_fst := Continuous.curry_left

/-- Continuous functions on products are continuous in their second argument -/
theorem Continuous.curry_right {f : X × Y → Z} (hf : Continuous f) {x : X} :
    Continuous fun y ↦ f (x, y) :=
  hf.comp (.prodMk_right _)
alias Continuous.along_snd := Continuous.curry_right

-- todo: prove a version of `generateFrom_union` with `image2 (∩) s t` in the LHS and use it here
theorem prod_generateFrom_generateFrom_eq {X Y : Type*} {s : Set (Set X)} {t : Set (Set Y)}
    (hs : ⋃₀ s = univ) (ht : ⋃₀ t = univ) :
    @instTopologicalSpaceProd X Y (generateFrom s) (generateFrom t) =
      generateFrom (image2 (·  ×ˢ ·) s t) :=
  let G := generateFrom (image2  (·  ×ˢ ·) s t)
  le_antisymm
    (le_generateFrom fun _ ⟨_, hu, _, hv, g_eq⟩ =>
      g_eq.symm ▸
        @IsOpen.prod _ _ (generateFrom s) (generateFrom t) _ _ (GenerateOpen.basic _ hu)
          (GenerateOpen.basic _ hv))
    (le_inf
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun u hu =>
          have : ⋃ v ∈ t, u ×ˢ v = Prod.fst ⁻¹' u := by
            simp_rw [← prod_iUnion, ← sUnion_eq_biUnion, ht, prod_univ]
          show G.IsOpen (Prod.fst ⁻¹' u) by
            rw [← this]
            exact
              isOpen_iUnion fun v =>
                isOpen_iUnion fun hv => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩)
      (coinduced_le_iff_le_induced.mp <|
        le_generateFrom fun v hv =>
          have : ⋃ u ∈ s, u ×ˢ v = Prod.snd ⁻¹' v := by
            simp_rw [← iUnion_prod_const, ← sUnion_eq_biUnion, hs, univ_prod]
          show G.IsOpen (Prod.snd ⁻¹' v) by
            rw [← this]
            exact
              isOpen_iUnion fun u =>
                isOpen_iUnion fun hu => GenerateOpen.basic _ ⟨_, hu, _, hv, rfl⟩))

theorem prod_eq_generateFrom :
    instTopologicalSpaceProd =
      generateFrom { g | ∃ (s : Set X) (t : Set Y), IsOpen s ∧ IsOpen t ∧ g = s ×ˢ t } :=
  le_antisymm (le_generateFrom fun _ ⟨_, _, hs, ht, g_eq⟩ => g_eq.symm ▸ hs.prod ht)
    (le_inf
      (forall_mem_image.2 fun t ht =>
        GenerateOpen.basic _ ⟨t, univ, by simpa [Set.prod_eq] using ht⟩)
      (forall_mem_image.2 fun t ht =>
        GenerateOpen.basic _ ⟨univ, t, by simpa [Set.prod_eq] using ht⟩))

-- TODO: align with `mem_nhds_prod_iff'`
theorem isOpen_prod_iff {s : Set (X × Y)} :
    IsOpen s ↔ ∀ a b, (a, b) ∈ s →
      ∃ u v, IsOpen u ∧ IsOpen v ∧ a ∈ u ∧ b ∈ v ∧ u ×ˢ v ⊆ s :=
  isOpen_iff_mem_nhds.trans <| by simp_rw [Prod.forall, mem_nhds_prod_iff', and_left_comm]

/-- A product of induced topologies is induced by the product map -/
theorem prod_induced_induced {X Z} (f : X → Y) (g : Z → W) :
    @instTopologicalSpaceProd X Z (induced f ‹_›) (induced g ‹_›) =
      induced (fun p => (f p.1, g p.2)) instTopologicalSpaceProd := by
  delta instTopologicalSpaceProd
  simp_rw [induced_inf, induced_compose]
  rfl

/-- Given a neighborhood `s` of `(x, x)`, then `(x, x)` has a square open neighborhood
  that is a subset of `s`. -/
theorem exists_nhds_square {s : Set (X × X)} {x : X} (hx : s ∈ 𝓝 (x, x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ U ⊆ s := by
  simpa [nhds_prod_eq, (nhds_basis_opens x).prod_self.mem_iff, and_assoc, and_left_comm] using hx

/-- `Prod.fst` maps neighborhood of `x : X × Y` within the section `Prod.snd ⁻¹' {x.2}`
to `𝓝 x.1`. -/
theorem map_fst_nhdsWithin (x : X × Y) : map Prod.fst (𝓝[Prod.snd ⁻¹' {x.2}] x) = 𝓝 x.1 := by
  refine le_antisymm (continuousAt_fst.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_setOf_eq, mem_preimage] at H
  exact mem_of_superset hu fun z hz => H _ hz _ (mem_of_mem_nhds hv) rfl

@[simp]
theorem map_fst_nhds (x : X × Y) : map Prod.fst (𝓝 x) = 𝓝 x.1 :=
  le_antisymm continuousAt_fst <| (map_fst_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/-- The first projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_fst : IsOpenMap (@Prod.fst X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_fst_nhds x).ge

/-- `Prod.snd` maps neighborhood of `x : X × Y` within the section `Prod.fst ⁻¹' {x.1}`
to `𝓝 x.2`. -/
theorem map_snd_nhdsWithin (x : X × Y) : map Prod.snd (𝓝[Prod.fst ⁻¹' {x.1}] x) = 𝓝 x.2 := by
  refine le_antisymm (continuousAt_snd.mono_left inf_le_left) fun s hs => ?_
  rcases x with ⟨x, y⟩
  rw [mem_map, nhdsWithin, mem_inf_principal, mem_nhds_prod_iff] at hs
  rcases hs with ⟨u, hu, v, hv, H⟩
  simp only [prod_subset_iff, mem_singleton_iff, mem_setOf_eq, mem_preimage] at H
  exact mem_of_superset hv fun z hz => H _ (mem_of_mem_nhds hu) _ hz rfl

@[simp]
theorem map_snd_nhds (x : X × Y) : map Prod.snd (𝓝 x) = 𝓝 x.2 :=
  le_antisymm continuousAt_snd <| (map_snd_nhdsWithin x).symm.trans_le (map_mono inf_le_left)

/-- The second projection in a product of topological spaces sends open sets to open sets. -/
theorem isOpenMap_snd : IsOpenMap (@Prod.snd X Y) :=
  isOpenMap_iff_nhds_le.2 fun x => (map_snd_nhds x).ge

/-- A product set is open in a product space if and only if each factor is open, or one of them is
empty -/
theorem isOpen_prod_iff' {s : Set X} {t : Set Y} :
    IsOpen (s ×ˢ t) ↔ IsOpen s ∧ IsOpen t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.1 h]
  · have st : s.Nonempty ∧ t.Nonempty := prod_nonempty_iff.1 h
    constructor
    · intro (H : IsOpen (s ×ˢ t))
      refine Or.inl ⟨?_, ?_⟩
      · simpa only [fst_image_prod _ st.2] using isOpenMap_fst _ H
      · simpa only [snd_image_prod st.1 t] using isOpenMap_snd _ H
    · intro H
      simp only [st.1.ne_empty, st.2.ne_empty, not_false_iff, or_false] at H
      exact H.1.prod H.2

theorem isQuotientMap_fst [Nonempty Y] : IsQuotientMap (Prod.fst : X × Y → X) :=
  isOpenMap_fst.isQuotientMap continuous_fst Prod.fst_surjective

@[deprecated (since := "2024-10-22")]
alias quotientMap_fst := isQuotientMap_fst

theorem isQuotientMap_snd [Nonempty X] : IsQuotientMap (Prod.snd : X × Y → Y) :=
  isOpenMap_snd.isQuotientMap continuous_snd Prod.snd_surjective

@[deprecated (since := "2024-10-22")]
alias quotientMap_snd := isQuotientMap_snd

theorem closure_prod_eq {s : Set X} {t : Set Y} : closure (s ×ˢ t) = closure s ×ˢ closure t :=
  ext fun ⟨a, b⟩ => by
    simp_rw [mem_prod, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_prod_eq, prod_neBot]

theorem interior_prod_eq (s : Set X) (t : Set Y) : interior (s ×ˢ t) = interior s ×ˢ interior t :=
  ext fun ⟨a, b⟩ => by simp only [mem_interior_iff_mem_nhds, mem_prod, prod_mem_nhds_iff]

theorem frontier_prod_eq (s : Set X) (t : Set Y) :
    frontier (s ×ˢ t) = closure s ×ˢ frontier t ∪ frontier s ×ˢ closure t := by
  simp only [frontier, closure_prod_eq, interior_prod_eq, prod_diff_prod]

@[simp]
theorem frontier_prod_univ_eq (s : Set X) :
    frontier (s ×ˢ (univ : Set Y)) = frontier s ×ˢ univ := by
  simp [frontier_prod_eq]

@[simp]
theorem frontier_univ_prod_eq (s : Set Y) :
    frontier ((univ : Set X) ×ˢ s) = univ ×ˢ frontier s := by
  simp [frontier_prod_eq]

theorem map_mem_closure₂ {f : X → Y → Z} {x : X} {y : Y} {s : Set X} {t : Set Y} {u : Set Z}
    (hf : Continuous (uncurry f)) (hx : x ∈ closure s) (hy : y ∈ closure t)
    (h : ∀ a ∈ s, ∀ b ∈ t, f a b ∈ u) : f x y ∈ closure u :=
  have H₁ : (x, y) ∈ closure (s ×ˢ t) := by simpa only [closure_prod_eq] using mk_mem_prod hx hy
  have H₂ : MapsTo (uncurry f) (s ×ˢ t) u := forall_prod_set.2 h
  H₂.closure hf H₁

theorem IsClosed.prod {s₁ : Set X} {s₂ : Set Y} (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) :
    IsClosed (s₁ ×ˢ s₂) :=
  closure_eq_iff_isClosed.mp <| by simp only [h₁.closure_eq, h₂.closure_eq, closure_prod_eq]

/-- The product of two dense sets is a dense set. -/
theorem Dense.prod {s : Set X} {t : Set Y} (hs : Dense s) (ht : Dense t) : Dense (s ×ˢ t) :=
  fun x => by
  rw [closure_prod_eq]
  exact ⟨hs x.1, ht x.2⟩

/-- If `f` and `g` are maps with dense range, then `Prod.map f g` has dense range. -/
theorem DenseRange.prodMap {ι : Type*} {κ : Type*} {f : ι → Y} {g : κ → Z} (hf : DenseRange f)
    (hg : DenseRange g) : DenseRange (Prod.map f g) := by
  simpa only [DenseRange, prod_range_range_eq] using hf.prod hg

lemma Topology.IsInducing.prodMap {f : X → Y} {g : Z → W} (hf : IsInducing f) (hg : IsInducing g) :
    IsInducing (Prod.map f g) :=
  isInducing_iff_nhds.2 fun (x, z) => by simp_rw [Prod.map_def, nhds_prod_eq, hf.nhds_eq_comap,
    hg.nhds_eq_comap, prod_comap_comap_eq]

@[deprecated (since := "2024-10-28")] alias Inducing.prodMap := IsInducing.prodMap

@[simp]
lemma Topology.isInducing_const_prod {x : X} {f : Y → Z} :
    IsInducing (fun x' => (x, f x')) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, top_inf_eq]

@[deprecated (since := "2024-10-28")] alias inducing_const_prod := isInducing_const_prod

@[simp]
lemma Topology.isInducing_prod_const {y : Y} {f : X → Z} :
    IsInducing (fun x => (f x, y)) ↔ IsInducing f := by
  simp_rw [isInducing_iff, instTopologicalSpaceProd, induced_inf, induced_compose,
    Function.comp_def, induced_const, inf_top_eq]

@[deprecated (since := "2024-10-28")] alias inducing_prod_const := isInducing_prod_const

lemma isInducing_prodMkLeft (y : Y) : IsInducing (fun x : X ↦ (x, y)) :=
  .of_comp (.prodMk_left y) continuous_fst .id

lemma isInducing_prodMkRight (x : X) : IsInducing (Prod.mk x : Y → X × Y) :=
  .of_comp (.prodMk_right x) continuous_snd .id

lemma Topology.IsEmbedding.prodMap {f : X → Y} {g : Z → W} (hf : IsEmbedding f)
    (hg : IsEmbedding g) : IsEmbedding (Prod.map f g) where
  toIsInducing := hf.isInducing.prodMap hg.isInducing
  injective := hf.injective.prodMap hg.injective

protected theorem IsOpenMap.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Prod.map f g) := by
  rw [isOpenMap_iff_nhds_le]
  rintro ⟨a, b⟩
  rw [nhds_prod_eq, nhds_prod_eq, ← Filter.prod_map_map_eq']
  exact Filter.prod_mono (hf.nhds_le a) (hg.nhds_le b)

protected lemma Topology.IsOpenEmbedding.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenEmbedding f)
    (hg : IsOpenEmbedding g) : IsOpenEmbedding (Prod.map f g) :=
  .of_isEmbedding_isOpenMap (hf.1.prodMap hg.1) (hf.isOpenMap.prodMap hg.isOpenMap)

lemma isEmbedding_graph {f : X → Y} (hf : Continuous f) : IsEmbedding fun x => (x, f x) :=
  .of_comp (continuous_id.prodMk hf) continuous_fst .id

@[deprecated (since := "2024-10-26")]
alias embedding_graph := isEmbedding_graph

lemma isEmbedding_prodMkLeft (y : Y) : IsEmbedding (fun x : X ↦ (x, y)) :=
  .of_comp (.prodMk_left y) continuous_fst .id

lemma isEmbedding_prodMkRight (x : X) : IsEmbedding (Prod.mk x : Y → X × Y) :=
  .of_comp (.prodMk_right x) continuous_snd .id

@[deprecated (since := "2025-06-12")] alias isEmbedding_prodMk := isEmbedding_prodMkRight
@[deprecated (since := "2024-10-26")] alias embedding_prod_mk := isEmbedding_prodMkRight

theorem IsOpenQuotientMap.prodMap {f : X → Y} {g : Z → W} (hf : IsOpenQuotientMap f)
    (hg : IsOpenQuotientMap g) : IsOpenQuotientMap (Prod.map f g) :=
  ⟨.prodMap hf.1 hg.1, .prodMap hf.2 hg.2, .prodMap hf.3 hg.3⟩

-- Homeomorphisms between the various product: products of two homeomorphisms,
-- as well as commutativity and associativity. See below for the analogous results for sums,
-- as well as distributivity, etc.
namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

/-- Product of two homeomorphisms. -/
def prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X × Y ≃ₜ X' × Y' where
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
theorem prodCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
    (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
theorem coe_prodCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

variable (W X Y Z)

/-- `X × Y` is homeomorphic to `Y × X`. -/
def prodComm : X × Y ≃ₜ Y × X where
  continuous_toFun := continuous_snd.prodMk continuous_fst
  continuous_invFun := continuous_snd.prodMk continuous_fst
  toEquiv := Equiv.prodComm X Y

@[simp]
theorem prodComm_symm : (prodComm X Y).symm = prodComm Y X :=
  rfl

@[simp]
theorem coe_prodComm : ⇑(prodComm X Y) = Prod.swap :=
  rfl

/-- `(X × Y) × Z` is homeomorphic to `X × (Y × Z)`. -/
def prodAssoc : (X × Y) × Z ≃ₜ X × Y × Z where
  continuous_toFun := continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd)
  continuous_invFun := (continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd
  toEquiv := Equiv.prodAssoc X Y Z

@[simp]
lemma prodAssoc_toEquiv : (prodAssoc X Y Z).toEquiv = Equiv.prodAssoc X Y Z := rfl

/-- Four-way commutativity of `prod`. The name matches `mul_mul_mul_comm`. -/
def prodProdProdComm : (X × Y) × W × Z ≃ₜ (X × W) × Y × Z where
  toEquiv := Equiv.prodProdProdComm X Y W Z
  continuous_toFun := by
    unfold Equiv.prodProdProdComm
    dsimp only
    fun_prop
  continuous_invFun := by
    unfold Equiv.prodProdProdComm
    dsimp only
    fun_prop

@[simp]
theorem prodProdProdComm_symm : (prodProdProdComm X Y W Z).symm = prodProdProdComm X W Y Z :=
  rfl

/-- `X × {*}` is homeomorphic to `X`. -/
@[simps! -fullyApplied apply]
def prodPUnit : X × PUnit ≃ₜ X where
  toEquiv := Equiv.prodPUnit X
  continuous_toFun := continuous_fst
  continuous_invFun := .prodMk_left _

/-- `{*} × X` is homeomorphic to `X`. -/
def punitProd : PUnit × X ≃ₜ X :=
  (prodComm _ _).trans (prodPUnit _)

@[simp] theorem coe_punitProd : ⇑(punitProd X) = Prod.snd := rfl

end Homeomorph

end Prod

section Sum

open Sum

variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace W] [TopologicalSpace Z]

theorem continuous_sum_dom {f : X ⊕ Y → Z} :
    Continuous f ↔ Continuous (f ∘ Sum.inl) ∧ Continuous (f ∘ Sum.inr) :=
  (continuous_sup_dom (t₁ := TopologicalSpace.coinduced Sum.inl _)
    (t₂ := TopologicalSpace.coinduced Sum.inr _)).trans <|
    continuous_coinduced_dom.and continuous_coinduced_dom

theorem continuous_sumElim {f : X → Z} {g : Y → Z} :
    Continuous (Sum.elim f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sum_dom

@[deprecated (since := "2025-02-20")] alias continuous_sum_elim := continuous_sumElim

@[continuity, fun_prop]
theorem Continuous.sumElim {f : X → Z} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.elim f g) :=
  continuous_sumElim.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-20")] alias Continuous.sum_elim := Continuous.sumElim

@[continuity, fun_prop]
theorem continuous_isLeft : Continuous (isLeft : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
theorem continuous_isRight : Continuous (isRight : X ⊕ Y → Bool) :=
  continuous_sum_dom.2 ⟨continuous_const, continuous_const⟩

@[continuity, fun_prop]
theorem continuous_inl : Continuous (@inl X Y) := ⟨fun _ => And.left⟩

@[continuity, fun_prop]
theorem continuous_inr : Continuous (@inr X Y) := ⟨fun _ => And.right⟩

@[fun_prop, continuity]
lemma continuous_sum_swap : Continuous (@Sum.swap X Y) :=
  Continuous.sumElim continuous_inr continuous_inl

theorem isOpen_sum_iff {s : Set (X ⊕ Y)} : IsOpen s ↔ IsOpen (inl ⁻¹' s) ∧ IsOpen (inr ⁻¹' s) :=
  Iff.rfl

theorem isClosed_sum_iff {s : Set (X ⊕ Y)} :
    IsClosed s ↔ IsClosed (inl ⁻¹' s) ∧ IsClosed (inr ⁻¹' s) := by
  simp only [← isOpen_compl_iff, isOpen_sum_iff, preimage_compl]

theorem isOpenMap_inl : IsOpenMap (@inl X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inl_injective]

theorem isOpenMap_inr : IsOpenMap (@inr X Y) := fun u hu => by
  simpa [isOpen_sum_iff, preimage_image_eq u Sum.inr_injective]

theorem isClosedMap_inl : IsClosedMap (@inl X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inl_injective]

theorem isClosedMap_inr : IsClosedMap (@inr X Y) := fun u hu ↦ by
  simpa [isClosed_sum_iff, preimage_image_eq u Sum.inr_injective]

protected lemma Topology.IsOpenEmbedding.inl : IsOpenEmbedding (@inl X Y) :=
  .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_inl := IsOpenEmbedding.inl

protected lemma Topology.IsOpenEmbedding.inr : IsOpenEmbedding (@inr X Y) :=
  .of_continuous_injective_isOpenMap continuous_inr inr_injective isOpenMap_inr

@[deprecated (since := "2024-10-30")] alias isOpenEmbedding_inr := IsOpenEmbedding.inr

protected lemma Topology.IsEmbedding.inl : IsEmbedding (@inl X Y) := IsOpenEmbedding.inl.1
protected lemma Topology.IsEmbedding.inr : IsEmbedding (@inr X Y) := IsOpenEmbedding.inr.1

@[deprecated (since := "2024-10-26")]
alias embedding_inr := IsEmbedding.inr

lemma isOpen_range_inl : IsOpen (range (inl : X → X ⊕ Y)) := IsOpenEmbedding.inl.2
lemma isOpen_range_inr : IsOpen (range (inr : Y → X ⊕ Y)) := IsOpenEmbedding.inr.2

theorem isClosed_range_inl : IsClosed (range (inl : X → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inl]
  exact isOpen_range_inr

theorem isClosed_range_inr : IsClosed (range (inr : Y → X ⊕ Y)) := by
  rw [← isOpen_compl_iff, compl_range_inr]
  exact isOpen_range_inl

theorem Topology.IsClosedEmbedding.inl : IsClosedEmbedding (inl : X → X ⊕ Y) :=
  ⟨.inl, isClosed_range_inl⟩

@[deprecated (since := "2024-10-30")] alias isClosedEmbedding_inl := IsClosedEmbedding.inl

theorem Topology.IsClosedEmbedding.inr : IsClosedEmbedding (inr : Y → X ⊕ Y) :=
  ⟨.inr, isClosed_range_inr⟩

@[deprecated (since := "2024-10-30")] alias isClosedEmbedding_inr := IsClosedEmbedding.inr

theorem nhds_inl (x : X) : 𝓝 (inl x : X ⊕ Y) = map inl (𝓝 x) :=
  (IsOpenEmbedding.inl.map_nhds_eq _).symm

theorem nhds_inr (y : Y) : 𝓝 (inr y : X ⊕ Y) = map inr (𝓝 y) :=
  (IsOpenEmbedding.inr.map_nhds_eq _).symm

@[simp]
theorem continuous_sumMap {f : X → Y} {g : Z → W} :
    Continuous (Sum.map f g) ↔ Continuous f ∧ Continuous g :=
  continuous_sumElim.trans <|
    IsEmbedding.inl.continuous_iff.symm.and IsEmbedding.inr.continuous_iff.symm

@[deprecated (since := "2025-02-21")] alias continuous_sum_map := continuous_sumMap

@[continuity, fun_prop]
theorem Continuous.sumMap {f : X → Y} {g : Z → W} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Sum.map f g) :=
  continuous_sumMap.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-21")] alias Continuous.sum_map := Continuous.sumMap

theorem isOpenMap_sum {f : X ⊕ Y → Z} :
    IsOpenMap f ↔ (IsOpenMap fun a => f (inl a)) ∧ IsOpenMap fun b => f (inr b) := by
  simp only [isOpenMap_iff_nhds_le, Sum.forall, nhds_inl, nhds_inr, Filter.map_map, comp_def]

theorem IsOpenMap.sumMap {f : X → Y} {g : Z → W} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.map f g) :=
  isOpenMap_sum.2 ⟨isOpenMap_inl.comp hf, isOpenMap_inr.comp hg⟩

@[simp]
theorem isOpenMap_sumElim {f : X → Z} {g : Y → Z} :
    IsOpenMap (Sum.elim f g) ↔ IsOpenMap f ∧ IsOpenMap g := by
  simp only [isOpenMap_sum, elim_inl, elim_inr]

@[deprecated (since := "2025-02-20")] alias isOpenMap_sum_elim := isOpenMap_sumElim

theorem IsOpenMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsOpenMap f) (hg : IsOpenMap g) :
    IsOpenMap (Sum.elim f g) :=
  isOpenMap_sumElim.2 ⟨hf, hg⟩

@[deprecated (since := "2025-02-20")] alias IsOpenMap.sum_elim := IsOpenMap.sumElim

lemma IsOpenEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsOpenEmbedding f) (hg : IsOpenEmbedding g) (h : Injective (Sum.elim f g)) :
    IsOpenEmbedding (Sum.elim f g) := by
  rw [isOpenEmbedding_iff_continuous_injective_isOpenMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

theorem isClosedMap_sum {f : X ⊕ Y → Z} :
    IsClosedMap f ↔ (IsClosedMap fun a => f (.inl a)) ∧ IsClosedMap fun b => f (.inr b) := by
  constructor
  · intro h
    exact ⟨h.comp IsClosedEmbedding.inl.isClosedMap, h.comp IsClosedEmbedding.inr.isClosedMap⟩
  · rintro h Z hZ
    rw [isClosed_sum_iff] at hZ
    convert (h.1 _ hZ.1).union (h.2 _ hZ.2)
    ext
    simp only [mem_image, Sum.exists, mem_union, mem_preimage]

theorem IsClosedMap.sumMap {f : X → Y} {g : Z → W} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.map f g) :=
  isClosedMap_sum.2 ⟨isClosedMap_inl.comp hf, isClosedMap_inr.comp hg⟩

@[simp]
theorem isClosedMap_sumElim {f : X → Z} {g : Y → Z} :
    IsClosedMap (Sum.elim f g) ↔ IsClosedMap f ∧ IsClosedMap g := by
  simp only [isClosedMap_sum, Sum.elim_inl, Sum.elim_inr]

theorem IsClosedMap.sumElim {f : X → Z} {g : Y → Z} (hf : IsClosedMap f) (hg : IsClosedMap g) :
    IsClosedMap (Sum.elim f g) :=
  isClosedMap_sumElim.2 ⟨hf, hg⟩

lemma IsClosedEmbedding.sumElim {f : X → Z} {g : Y → Z}
    (hf : IsClosedEmbedding f) (hg : IsClosedEmbedding g) (h : Injective (Sum.elim f g)) :
    IsClosedEmbedding (Sum.elim f g) := by
  rw [IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap] at hf hg ⊢
  exact ⟨hf.1.sumElim hg.1, h, hf.2.2.sumElim hg.2.2⟩

-- Homeomorphisms between the various constructions: sums of two homeomorphisms,
-- as well as commutativity, associativity and distributivity with products.
namespace Homeomorph

variable {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']

/-- Sum of two homeomorphisms. -/
def sumCongr (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') : X ⊕ Y ≃ₜ X' ⊕ Y' where
  continuous_toFun := h₁.continuous.sumMap h₂.continuous
  continuous_invFun := h₁.symm.continuous.sumMap h₂.symm.continuous
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv

@[simp]
lemma sumCongr_symm (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') :
  (sumCongr h₁ h₂).symm = sumCongr h₁.symm h₂.symm := rfl

@[simp]
theorem sumCongr_refl : sumCongr (.refl X) (.refl Y) = .refl (X ⊕ Y) := by
  ext i
  cases i <;> rfl

@[simp]
theorem sumCongr_trans {X'' Y'' : Type*} [TopologicalSpace X''] [TopologicalSpace Y'']
    (h₁ : X ≃ₜ X') (h₂ : Y ≃ₜ Y') (h₃ : X' ≃ₜ X'') (h₄ : Y' ≃ₜ Y'') :
    (sumCongr h₁ h₂).trans (sumCongr h₃ h₄) = sumCongr (h₁.trans h₃) (h₂.trans h₄) := by
  ext i
  cases i <;> rfl

variable (W X Y Z)

/-- `X ⊕ Y` is homeomorphic to `Y ⊕ X`. -/
def sumComm : X ⊕ Y ≃ₜ Y ⊕ X where
  toEquiv := Equiv.sumComm X Y
  continuous_toFun := continuous_sum_swap
  continuous_invFun := continuous_sum_swap

@[simp]
theorem sumComm_symm : (sumComm X Y).symm = sumComm Y X :=
  rfl

@[simp]
theorem coe_sumComm : ⇑(sumComm X Y) = Sum.swap :=
  rfl

@[continuity, fun_prop]
lemma continuous_sumAssoc : Continuous (Equiv.sumAssoc X Y Z) :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

@[continuity, fun_prop]
lemma continuous_sumAssoc_symm : Continuous (Equiv.sumAssoc X Y Z).symm :=
  Continuous.sumElim (by fun_prop) (by fun_prop)

/-- `(X ⊕ Y) ⊕ Z` is homeomorphic to `X ⊕ (Y ⊕ Z)`. -/
def sumAssoc : (X ⊕ Y) ⊕ Z ≃ₜ X ⊕ Y ⊕ Z where
  toEquiv := Equiv.sumAssoc X Y Z
  continuous_toFun := continuous_sumAssoc X Y Z
  continuous_invFun := continuous_sumAssoc_symm X Y Z

@[simp]
lemma sumAssoc_toEquiv : (sumAssoc X Y Z).toEquiv = Equiv.sumAssoc X Y Z := rfl

/-- Four-way commutativity of the disjoint union. The name matches `add_add_add_comm`. -/
def sumSumSumComm : (X ⊕ Y) ⊕ W ⊕ Z ≃ₜ (X ⊕ W) ⊕ Y ⊕ Z where
  toEquiv := Equiv.sumSumSumComm X Y W Z
  continuous_toFun := by
    unfold Equiv.sumSumSumComm
    dsimp only
    have : Continuous (Sum.map (Sum.map (@id X) ⇑(Equiv.sumComm Y W)) (@id Z)) := by continuity
    fun_prop
  continuous_invFun := by
    unfold Equiv.sumSumSumComm
    dsimp only
    have : Continuous (Sum.map (Sum.map (@id X) (Equiv.sumComm Y W).symm) (@id Z)) := by continuity
    fun_prop

@[simp]
lemma sumSumSumComm_toEquiv : (sumSumSumComm W X Y Z).toEquiv = (Equiv.sumSumSumComm W X Y Z) := rfl

@[simp]
lemma sumSumSumComm_symm : (sumSumSumComm X Y W Z).symm = (sumSumSumComm X W Y Z) := rfl

/-- The sum of `X` with any empty topological space is homeomorphic to `X`. -/
@[simps! -fullyApplied apply]
def sumEmpty [IsEmpty Y] : X ⊕ Y ≃ₜ X where
  toEquiv := Equiv.sumEmpty X Y
  continuous_toFun := Continuous.sumElim continuous_id (by fun_prop)
  continuous_invFun := continuous_inl

/-- The sum of `X` with any empty topological space is homeomorphic to `X`. -/
def emptySum [IsEmpty Y] : Y ⊕ X ≃ₜ X := (sumComm Y X).trans (sumEmpty X Y)

@[simp] theorem coe_emptySum [IsEmpty Y] : (emptySum X Y).toEquiv = Equiv.emptySum Y X := rfl

variable {W X Y Z}

/-- `(X ⊕ Y) × Z` is homeomorphic to `X × Z ⊕ Y × Z`. -/
@[simps!]
def sumProdDistrib : (X ⊕ Y) × Z ≃ₜ (X × Z) ⊕ (Y × Z) :=
  Homeomorph.symm <|
    (Equiv.sumProdDistrib X Y Z).symm.toHomeomorphOfContinuousOpen
        ((continuous_inl.prodMap continuous_id).sumElim
          (continuous_inr.prodMap continuous_id)) <|
      (isOpenMap_inl.prodMap IsOpenMap.id).sumElim (isOpenMap_inr.prodMap IsOpenMap.id)

/-- `X × (Y ⊕ Z)` is homeomorphic to `X × Y ⊕ X × Z`. -/
def prodSumDistrib : X × (Y ⊕ Z) ≃ₜ (X × Y) ⊕ (X × Z) :=
  (prodComm _ _).trans <| sumProdDistrib.trans <| sumCongr (prodComm _ _) (prodComm _ _)

end Homeomorph

end Sum
