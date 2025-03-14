/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Topology.Constructions
import Mathlib.Topology.ContinuousOn

/-!
# Blabla

-/


open Set Filter Function Topology Filter

variable {α β γ δ : Type*}
variable [TopologicalSpace α]

theorem preimage_nhdsWithin_coinduced' {π : α → β} {s : Set β} {t : Set α} {a : α} (h : a ∈ t)
    (hs : s ∈ @nhds β (.coinduced (fun x : t => π x) inferInstance) (π a)) :
    π ⁻¹' s ∈ 𝓝[t] a := by
  lift a to t using h
  replace hs : (fun x : t => π x) ⁻¹' s ∈ 𝓝 a := preimage_nhds_coinduced hs
  rwa [← map_nhds_subtype_val, mem_map]


theorem nhdsWithin_prod [TopologicalSpace β]
    {s u : Set α} {t v : Set β} {a : α} {b : β} (hu : u ∈ 𝓝[s] a) (hv : v ∈ 𝓝[t] b) :
    u ×ˢ v ∈ 𝓝[s ×ˢ t] (a, b) := by
  rw [nhdsWithin_prod_eq]
  exact prod_mem_prod hu hv


section Pi

variable {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]

theorem nhdsWithin_pi_eq' {I : Set ι} (hI : I.Finite) (s : ∀ i, Set (π i)) (x : ∀ i, π i) :
    𝓝[pi I s] x = ⨅ i, comap (fun x => x i) (𝓝 (x i) ⊓ ⨅ (_ : i ∈ I), 𝓟 (s i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, comap_inf, comap_iInf, pi_def, comap_principal, ←
    iInf_principal_finite hI, ← iInf_inf_eq]

theorem nhdsWithin_pi_eq {I : Set ι} (hI : I.Finite) (s : ∀ i, Set (π i)) (x : ∀ i, π i) :
    𝓝[pi I s] x =
      (⨅ i ∈ I, comap (fun x => x i) (𝓝[s i] x i)) ⊓
        ⨅ (i) (_ : i ∉ I), comap (fun x => x i) (𝓝 (x i)) := by
  simp only [nhdsWithin, nhds_pi, Filter.pi, pi_def, ← iInf_principal_finite hI, comap_inf,
    comap_principal, eval]
  rw [iInf_split _ fun i => i ∈ I, inf_right_comm]
  simp only [iInf_inf_eq]

theorem nhdsWithin_pi_univ_eq [Finite ι] (s : ∀ i, Set (π i)) (x : ∀ i, π i) :
    𝓝[pi univ s] x = ⨅ i, comap (fun x => x i) (𝓝[s i] x i) := by
  simpa [nhdsWithin] using nhdsWithin_pi_eq finite_univ s x

theorem nhdsWithin_pi_eq_bot {I : Set ι} {s : ∀ i, Set (π i)} {x : ∀ i, π i} :
    𝓝[pi I s] x = ⊥ ↔ ∃ i ∈ I, 𝓝[s i] x i = ⊥ := by
  simp only [nhdsWithin, nhds_pi, pi_inf_principal_pi_eq_bot]

theorem nhdsWithin_pi_neBot {I : Set ι} {s : ∀ i, Set (π i)} {x : ∀ i, π i} :
    (𝓝[pi I s] x).NeBot ↔ ∀ i ∈ I, (𝓝[s i] x i).NeBot := by
  simp [neBot_iff, nhdsWithin_pi_eq_bot]

instance instNeBotNhdsWithinUnivPi {s : ∀ i, Set (π i)} {x : ∀ i, π i}
    [∀ i, (𝓝[s i] x i).NeBot] : (𝓝[pi univ s] x).NeBot := by
  simpa [nhdsWithin_pi_neBot]

instance Pi.instNeBotNhdsWithinIio [Nonempty ι] [∀ i, Preorder (π i)] {x : ∀ i, π i}
    [∀ i, (𝓝[<] x i).NeBot] : (𝓝[<] x).NeBot :=
  have : (𝓝[pi univ fun i ↦ Iio (x i)] x).NeBot := inferInstance
  this.mono <| nhdsWithin_mono _ fun _y hy ↦ lt_of_strongLT fun i ↦ hy i trivial

instance Pi.instNeBotNhdsWithinIoi [Nonempty ι] [∀ i, Preorder (π i)] {x : ∀ i, π i}
    [∀ i, (𝓝[>] x i).NeBot] : (𝓝[>] x).NeBot :=
  Pi.instNeBotNhdsWithinIio (π := fun i ↦ (π i)ᵒᵈ) (x := fun i ↦ OrderDual.toDual (x i))

end Pi


theorem mem_closure_pi {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {I : Set ι}
    {s : ∀ i, Set (α i)} {x : ∀ i, α i} : x ∈ closure (pi I s) ↔ ∀ i ∈ I, x i ∈ closure (s i) := by
  simp only [mem_closure_iff_nhdsWithin_neBot, nhdsWithin_pi_neBot]

theorem closure_pi_set {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] (I : Set ι)
    (s : ∀ i, Set (α i)) : closure (pi I s) = pi I fun i => closure (s i) :=
  Set.ext fun _ => mem_closure_pi

theorem dense_pi {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : ∀ i, Set (α i)}
    (I : Set ι) (hs : ∀ i ∈ I, Dense (s i)) : Dense (pi I s) := by
  simp only [dense_iff_closure_eq, closure_pi_set, pi_congr rfl fun i hi => (hs i hi).closure_eq,
    pi_univ]

theorem DenseRange.piMap {ι : Type*} {X Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {f : (i : ι) → (X i) → (Y i)} (hf : ∀ i, DenseRange (f i)):
    DenseRange (Pi.map f) := by
  rw [DenseRange, Set.range_piMap]
  exact dense_pi Set.univ (fun i _ => hf i)

variable {f : α → β} {s : Set α} [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

theorem ContinuousOn.restrict_mapsTo {t : Set β} (hf : ContinuousOn f s) (ht : MapsTo f s t) :
    Continuous (ht.restrict f s t) :=
  hf.restrict.codRestrict _


theorem ContinuousAt.comp₂_continuousWithinAt {f : β × γ → δ} {g : α → β} {h : α → γ} {x : α}
    {s : Set α} (hf : ContinuousAt f (g x, h x)) (hg : ContinuousWithinAt g s x)
    (hh : ContinuousWithinAt h s x) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x :=
  ContinuousAt.comp_continuousWithinAt hf (hg.prod_mk_nhds hh)

theorem ContinuousAt.comp₂_continuousWithinAt_of_eq {f : β × γ → δ} {g : α → β}
    {h : α → γ} {x : α} {s : Set α} {y : β × γ} (hf : ContinuousAt f y)
    (hg : ContinuousWithinAt g s x) (hh : ContinuousWithinAt h s x) (e : (g x, h x) = y) :
    ContinuousWithinAt (fun x ↦ f (g x, h x)) s x := by
  rw [← e] at hf
  exact hf.comp₂_continuousWithinAt hg hh


/-!
### Product
-/

theorem ContinuousWithinAt.prod_map {f : α → γ} {g : β → δ} {s : Set α} {t : Set β} {x : α} {y : β}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g t y) :
    ContinuousWithinAt (Prod.map f g) (s ×ˢ t) (x, y) := by
  unfold ContinuousWithinAt at *
  rw [nhdsWithin_prod_eq, Prod.map, nhds_prod_eq]
  exact hf.prod_map hg

theorem continuousWithinAt_prod_of_discrete_left [DiscreteTopology α]
    {f : α × β → γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨x.1, ·⟩) {b | (x.1, b) ∈ s} x.2 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, pure_prod,
    ← map_inf_principal_preimage]; rfl

theorem continuousWithinAt_prod_of_discrete_right [DiscreteTopology β]
    {f : α × β → γ} {s : Set (α × β)} {x : α × β} :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ⟨·, x.2⟩) {a | (a, x.2) ∈ s} x.1 := by
  rw [← x.eta]; simp_rw [ContinuousWithinAt, nhdsWithin, nhds_prod_eq, nhds_discrete, prod_pure,
    ← map_inf_principal_preimage]; rfl

theorem continuousAt_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨x.1, ·⟩) x.2 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_left

theorem continuousAt_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {x : α × β} :
    ContinuousAt f x ↔ ContinuousAt (f ⟨·, x.2⟩) x.1 := by
  simp_rw [← continuousWithinAt_univ]; exact continuousWithinAt_prod_of_discrete_right

theorem continuousOn_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ ∀ a, ContinuousOn (f ⟨a, ·⟩) {b | (a, b) ∈ s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_left]; rfl

theorem continuousOn_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} {s : Set (α × β)} :
    ContinuousOn f s ↔ ∀ b, ContinuousOn (f ⟨·, b⟩) {a | (a, b) ∈ s} := by
  simp_rw [ContinuousOn, Prod.forall, continuousWithinAt_prod_of_discrete_right]; apply forall_swap

/-- If a function `f a b` is such that `y ↦ f a b` is continuous for all `a`, and `a` lives in a
discrete space, then `f` is continuous, and vice versa. -/
theorem continuous_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} :
    Continuous f ↔ ∀ a, Continuous (f ⟨a, ·⟩) := by
  simp_rw [continuous_iff_continuousOn_univ]; exact continuousOn_prod_of_discrete_left

theorem continuous_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} :
    Continuous f ↔ ∀ b, Continuous (f ⟨·, b⟩) := by
  simp_rw [continuous_iff_continuousOn_univ]; exact continuousOn_prod_of_discrete_right

theorem isOpenMap_prod_of_discrete_left [DiscreteTopology α] {f : α × β → γ} :
    IsOpenMap f ↔ ∀ a, IsOpenMap (f ⟨a, ·⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, nhds_prod_eq, nhds_discrete, pure_prod, map_map]
  rfl

theorem isOpenMap_prod_of_discrete_right [DiscreteTopology β] {f : α × β → γ} :
    IsOpenMap f ↔ ∀ b, IsOpenMap (f ⟨·, b⟩) := by
  simp_rw [isOpenMap_iff_nhds_le, Prod.forall, forall_swap (α := α) (β := β), nhds_prod_eq,
    nhds_discrete, prod_pure, map_map]; rfl

theorem ContinuousOn.prod_map {f : α → γ} {g : β → δ} {s : Set α} {t : Set β}
    (hf : ContinuousOn f s) (hg : ContinuousOn g t) : ContinuousOn (Prod.map f g) (s ×ˢ t) :=
  fun ⟨x, y⟩ ⟨hx, hy⟩ => ContinuousWithinAt.prod_map (hf x hx) (hg y hy)

theorem ContinuousWithinAt.prod {f : α → β} {g : α → γ} {s : Set α} {x : α}
    (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun x => (f x, g x)) s x :=
  hf.prod_mk_nhds hg

@[fun_prop]
theorem ContinuousOn.prod {f : α → β} {g : α → γ} {s : Set α} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (f x, g x)) s := fun x hx =>
  ContinuousWithinAt.prod (hf x hx) (hg x hx)

theorem continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod.fst s :=
  continuous_fst.continuousOn

theorem continuousWithinAt_fst {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.fst s p :=
  continuous_fst.continuousWithinAt

@[fun_prop]
theorem ContinuousOn.fst {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).1) s :=
  continuous_fst.comp_continuousOn hf

theorem ContinuousWithinAt.fst {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).fst) s a :=
  continuousAt_fst.comp_continuousWithinAt h

theorem continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod.snd s :=
  continuous_snd.continuousOn

theorem continuousWithinAt_snd {s : Set (α × β)} {p : α × β} : ContinuousWithinAt Prod.snd s p :=
  continuous_snd.continuousWithinAt

@[fun_prop]
theorem ContinuousOn.snd {f : α → β × γ} {s : Set α} (hf : ContinuousOn f s) :
    ContinuousOn (fun x => (f x).2) s :=
  continuous_snd.comp_continuousOn hf

theorem ContinuousWithinAt.snd {f : α → β × γ} {s : Set α} {a : α} (h : ContinuousWithinAt f s a) :
    ContinuousWithinAt (fun x => (f x).snd) s a :=
  continuousAt_snd.comp_continuousWithinAt h

theorem continuousWithinAt_prod_iff {f : α → β × γ} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔
      ContinuousWithinAt (Prod.fst ∘ f) s x ∧ ContinuousWithinAt (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun ⟨h1, h2⟩ => h1.prod h2⟩

/-!
### Pi
-/

theorem continuousWithinAt_pi {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    {f : α → ∀ i, π i} {s : Set α} {x : α} :
    ContinuousWithinAt f s x ↔ ∀ i, ContinuousWithinAt (fun y => f y i) s x :=
  tendsto_pi_nhds

theorem continuousOn_pi {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    {f : α → ∀ i, π i} {s : Set α} : ContinuousOn f s ↔ ∀ i, ContinuousOn (fun y => f y i) s :=
  ⟨fun h i x hx => tendsto_pi_nhds.1 (h x hx) i, fun h x hx => tendsto_pi_nhds.2 fun i => h i x hx⟩

@[fun_prop]
theorem continuousOn_pi' {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    {f : α → ∀ i, π i} {s : Set α} (hf : ∀ i, ContinuousOn (fun y => f y i) s) :
    ContinuousOn f s :=
  continuousOn_pi.2 hf

@[fun_prop]
theorem continuousOn_apply {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    (i : ι) (s) : ContinuousOn (fun p : ∀ i, π i => p i) s :=
  Continuous.continuousOn (continuous_apply i)


section Fin
variable {n : ℕ} {π : Fin (n + 1) → Type*} [∀ i, TopologicalSpace (π i)]

theorem ContinuousWithinAt.finCons
    {f : α → π 0} {g : α → ∀ j : Fin n, π (Fin.succ j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.cons (f a) (g a)) s a :=
  hf.tendsto.finCons hg

theorem ContinuousOn.finCons {f : α → π 0} {s : Set α} {g : α → ∀ j : Fin n, π (Fin.succ j)}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.cons (f a) (g a)) s := fun a ha =>
  (hf a ha).finCons (hg a ha)

theorem ContinuousWithinAt.matrixVecCons {f : α → β} {g : α → Fin n → β} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Matrix.vecCons (f a) (g a)) s a :=
  hf.tendsto.matrixVecCons hg

theorem ContinuousOn.matrixVecCons {f : α → β} {g : α → Fin n → β} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Matrix.vecCons (f a) (g a)) s := fun a ha =>
  (hf a ha).matrixVecCons (hg a ha)

theorem ContinuousWithinAt.finSnoc
    {f : α → ∀ j : Fin n, π (Fin.castSucc j)} {g : α → π (Fin.last _)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => Fin.snoc (f a) (g a)) s a :=
  hf.tendsto.finSnoc hg

theorem ContinuousOn.finSnoc
    {f : α → ∀ j : Fin n, π (Fin.castSucc j)} {g : α → π (Fin.last _)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => Fin.snoc (f a) (g a)) s := fun a ha =>
  (hf a ha).finSnoc (hg a ha)

theorem ContinuousWithinAt.finInsertNth
    (i : Fin (n + 1)) {f : α → π i} {g : α → ∀ j : Fin n, π (i.succAbove j)} {a : α} {s : Set α}
    (hf : ContinuousWithinAt f s a) (hg : ContinuousWithinAt g s a) :
    ContinuousWithinAt (fun a => i.insertNth (f a) (g a)) s a :=
  hf.tendsto.finInsertNth i hg

@[deprecated (since := "2025-01-02")]
alias ContinuousWithinAt.fin_insertNth := ContinuousWithinAt.finInsertNth

theorem ContinuousOn.finInsertNth
    (i : Fin (n + 1)) {f : α → π i} {g : α → ∀ j : Fin n, π (i.succAbove j)} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => i.insertNth (f a) (g a)) s := fun a ha =>
  (hf a ha).finInsertNth i (hg a ha)

@[deprecated (since := "2025-01-02")]
alias ContinuousOn.fin_insertNth := ContinuousOn.finInsertNth

end Fin


theorem Topology.IsQuotientMap.continuousOn_isOpen_iff {f : α → β} {g : β → γ} (h : IsQuotientMap f)
    {s : Set β} (hs : IsOpen s) : ContinuousOn g s ↔ ContinuousOn (g ∘ f) (f ⁻¹' s) := by
  simp only [continuousOn_iff_continuous_restrict, (h.restrictPreimage_isOpen hs).continuous_iff]
  rfl

@[deprecated (since := "2024-10-22")]
alias QuotientMap.continuousOn_isOpen_iff := IsQuotientMap.continuousOn_isOpen_iff

theorem IsOpenMap.continuousOn_image_of_leftInvOn {f : α → β} {s : Set α}
    (h : IsOpenMap (s.restrict f)) {finv : β → α} (hleft : LeftInvOn finv f s) :
    ContinuousOn finv (f '' s) := by
  refine continuousOn_iff'.2 fun t ht => ⟨f '' (t ∩ s), ?_, ?_⟩
  · rw [← image_restrict]
    exact h _ (ht.preimage continuous_subtype_val)
  · rw [inter_eq_self_of_subset_left (image_subset f inter_subset_right), hleft.image_inter']

theorem IsOpenMap.continuousOn_range_of_leftInverse {f : α → β} (hf : IsOpenMap f) {finv : β → α}
    (hleft : Function.LeftInverse finv f) : ContinuousOn finv (range f) := by
  rw [← image_univ]
  exact (hf.restrict isOpen_univ).continuousOn_image_of_leftInvOn fun x _ => hleft x


/-!
### `nhdsWithin` and subtypes
-/

theorem mem_nhdsWithin_subtype {s : Set α} {a : { x // x ∈ s }} {t u : Set { x // x ∈ s }} :
    t ∈ 𝓝[u] a ↔ t ∈ comap ((↑) : s → α) (𝓝[(↑) '' u] a) := by
  rw [nhdsWithin, nhds_subtype, principal_subtype, ← comap_inf, ← nhdsWithin]

theorem nhdsWithin_subtype (s : Set α) (a : { x // x ∈ s }) (t : Set { x // x ∈ s }) :
    𝓝[t] a = comap ((↑) : s → α) (𝓝[(↑) '' t] a) :=
  Filter.ext fun _ => mem_nhdsWithin_subtype

theorem mem_nhds_subtype_iff_nhdsWithin {s : Set α} {a : s} {t : Set s} :
    t ∈ 𝓝 a ↔ (↑) '' t ∈ 𝓝[s] (a : α) := by
  rw [← map_nhds_subtype_val, image_mem_map_iff Subtype.val_injective]

theorem preimage_coe_mem_nhds_subtype {s t : Set α} {a : s} : (↑) ⁻¹' t ∈ 𝓝 a ↔ t ∈ 𝓝[s] ↑a := by
  rw [← map_nhds_subtype_val, mem_map]

theorem eventually_nhds_subtype_iff (s : Set α) (a : s) (P : α → Prop) :
    (∀ᶠ x : s in 𝓝 a, P x) ↔ ∀ᶠ x in 𝓝[s] a, P x :=
  preimage_coe_mem_nhds_subtype

theorem frequently_nhds_subtype_iff (s : Set α) (a : s) (P : α → Prop) :
    (∃ᶠ x : s in 𝓝 a, P x) ↔ ∃ᶠ x in 𝓝[s] a, P x :=
  eventually_nhds_subtype_iff s a (¬ P ·) |>.not
