/-
Copyright (c) 2022 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov, Kevin H. Wilson, Heather Macbeth
-/
module

public import Mathlib.Order.Filter.Tendsto

/-!
# Product and coproduct filters

In this file we prove some basic properties of `f ×ˢ g` and `Filter.coprod f g`. The product
of two filters is the largest filter `l` such that `Filter.Tendsto Prod.fst l f` and
`Filter.Tendsto Prod.snd l g`.

## Implementation details

The product filter cannot be defined using the monad structure on filters. For example:

```lean
F := do {x ← seq, y ← top, return (x, y)}
G := do {y ← top, x ← seq, return (x, y)}
```
hence:
```lean
s ∈ F  ↔  ∃ n, [n..∞] × univ ⊆ s
s ∈ G  ↔  ∀ i:ℕ, ∃ n, [n..∞] × {i} ⊆ s
```
Now `⋃ i, [i..∞] × {i}` is in `G` but not in `F`.
As product filter we want to have `F` as result.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open Set

open Filter

namespace Filter

variable {α β γ δ : Type*} {ι : Sort*}

section Prod

variable {s : Set α} {t : Set β} {f : Filter α} {g : Filter β}

theorem prod_mem_prod (hs : s ∈ f) (ht : t ∈ g) : s ×ˢ t ∈ f ×ˢ g :=
  inter_mem_inf (preimage_mem_comap hs) (preimage_mem_comap ht)

theorem mem_prod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f ×ˢ g ↔ ∃ t₁ ∈ f, ∃ t₂ ∈ g, t₁ ×ˢ t₂ ⊆ s := by
  constructor
  · rintro ⟨t₁, ⟨s₁, hs₁, hts₁⟩, t₂, ⟨s₂, hs₂, hts₂⟩, rfl⟩
    exact ⟨s₁, hs₁, s₂, hs₂, fun p ⟨h, h'⟩ => ⟨hts₁ h, hts₂ h'⟩⟩
  · rintro ⟨t₁, ht₁, t₂, ht₂, h⟩
    exact mem_inf_of_inter (preimage_mem_comap ht₁) (preimage_mem_comap ht₂) h

@[simp]
theorem compl_diagonal_mem_prod {l₁ l₂ : Filter α} : (diagonal α)ᶜ ∈ l₁ ×ˢ l₂ ↔ Disjoint l₁ l₂ := by
  simp only [mem_prod_iff, Filter.disjoint_iff, prod_subset_compl_diagonal_iff_disjoint]

@[simp]
theorem prod_mem_prod_iff [f.NeBot] [g.NeBot] : s ×ˢ t ∈ f ×ˢ g ↔ s ∈ f ∧ t ∈ g :=
  ⟨fun h =>
    let ⟨_s', hs', _t', ht', H⟩ := mem_prod_iff.1 h
    (prod_subset_prod_iff.1 H).elim
      (fun ⟨hs's, ht't⟩ => ⟨mem_of_superset hs' hs's, mem_of_superset ht' ht't⟩) fun h =>
      h.elim (fun hs'e => absurd hs'e (nonempty_of_mem hs').ne_empty) fun ht'e =>
        absurd ht'e (nonempty_of_mem ht').ne_empty,
    fun h => prod_mem_prod h.1 h.2⟩

theorem mem_prod_principal {s : Set (α × β)} :
    s ∈ f ×ˢ 𝓟 t ↔ { a | ∀ b ∈ t, (a, b) ∈ s } ∈ f := by
  rw [← @exists_mem_subset_iff _ f, mem_prod_iff]
  refine exists_congr fun u => Iff.rfl.and ⟨?_, fun h => ⟨t, mem_principal_self t, ?_⟩⟩
  · rintro ⟨v, v_in, hv⟩ a a_in b b_in
    exact hv (mk_mem_prod a_in <| v_in b_in)
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact h hx y hy

theorem mem_prod_top {s : Set (α × β)} :
    s ∈ f ×ˢ (⊤ : Filter β) ↔ { a | ∀ b, (a, b) ∈ s } ∈ f := by
  rw [← principal_univ, mem_prod_principal]
  simp only [mem_univ, forall_true_left]

theorem eventually_prod_principal_iff {p : α × β → Prop} {s : Set β} :
    (∀ᶠ x : α × β in f ×ˢ 𝓟 s, p x) ↔ ∀ᶠ x : α in f, ∀ y : β, y ∈ s → p (x, y) := by
  rw [eventually_iff, eventually_iff, mem_prod_principal]
  simp only [mem_setOf_eq]

theorem comap_prod (f : α → β × γ) (b : Filter β) (c : Filter γ) :
    comap f (b ×ˢ c) = comap (Prod.fst ∘ f) b ⊓ comap (Prod.snd ∘ f) c := by
  rw [prod_eq_inf, comap_inf, Filter.comap_comap, Filter.comap_comap]

theorem comap_prodMap_prod (f : α → β) (g : γ → δ) (lb : Filter β) (ld : Filter δ) :
    comap (Prod.map f g) (lb ×ˢ ld) = comap f lb ×ˢ comap g ld := by
  simp [prod_eq_inf, comap_comap, Function.comp_def]

theorem prod_top : f ×ˢ (⊤ : Filter β) = f.comap Prod.fst := by
  rw [prod_eq_inf, comap_top, inf_top_eq]

theorem top_prod : (⊤ : Filter α) ×ˢ g = g.comap Prod.snd := by
  rw [prod_eq_inf, comap_top, top_inf_eq]

theorem sup_prod (f₁ f₂ : Filter α) (g : Filter β) : (f₁ ⊔ f₂) ×ˢ g = (f₁ ×ˢ g) ⊔ (f₂ ×ˢ g) := by
  simp only [prod_eq_inf, comap_sup, inf_sup_right]

theorem prod_sup (f : Filter α) (g₁ g₂ : Filter β) : f ×ˢ (g₁ ⊔ g₂) = (f ×ˢ g₁) ⊔ (f ×ˢ g₂) := by
  simp only [prod_eq_inf, comap_sup, inf_sup_left]

theorem eventually_prod_iff {p : α × β → Prop} :
    (∀ᶠ x in f ×ˢ g, p x) ↔
      ∃ pa : α → Prop, (∀ᶠ x in f, pa x) ∧ ∃ pb : β → Prop, (∀ᶠ y in g, pb y) ∧
        ∀ {x}, pa x → ∀ {y}, pb y → p (x, y) := by
  simpa only [Set.prod_subset_iff] using @mem_prod_iff α β p f g

theorem tendsto_fst : Tendsto Prod.fst (f ×ˢ g) f :=
  tendsto_inf_left tendsto_comap

theorem tendsto_snd : Tendsto Prod.snd (f ×ˢ g) g :=
  tendsto_inf_right tendsto_comap

/-- If a function tends to a product `g ×ˢ h` of filters, then its first component tends to
`g`. See also `Filter.Tendsto.fst_nhds` for the special case of converging to a point in a
product of two topological spaces. -/
theorem Tendsto.fst {h : Filter γ} {m : α → β × γ} (H : Tendsto m f (g ×ˢ h)) :
    Tendsto (fun a ↦ (m a).1) f g :=
  tendsto_fst.comp H

/-- If a function tends to a product `g ×ˢ h` of filters, then its second component tends to
`h`. See also `Filter.Tendsto.snd_nhds` for the special case of converging to a point in a
product of two topological spaces. -/
theorem Tendsto.snd {h : Filter γ} {m : α → β × γ} (H : Tendsto m f (g ×ˢ h)) :
    Tendsto (fun a ↦ (m a).2) f h :=
  tendsto_snd.comp H

theorem Tendsto.prodMk {h : Filter γ} {m₁ : α → β} {m₂ : α → γ}
    (h₁ : Tendsto m₁ f g) (h₂ : Tendsto m₂ f h) : Tendsto (fun x => (m₁ x, m₂ x)) f (g ×ˢ h) :=
  tendsto_inf.2 ⟨tendsto_comap_iff.2 h₁, tendsto_comap_iff.2 h₂⟩

theorem tendsto_prod_swap : Tendsto (Prod.swap : α × β → β × α) (f ×ˢ g) (g ×ˢ f) :=
  tendsto_snd.prodMk tendsto_fst

theorem Eventually.prod_inl {la : Filter α} {p : α → Prop} (h : ∀ᶠ x in la, p x) (lb : Filter β) :
    ∀ᶠ x in la ×ˢ lb, p (x : α × β).1 :=
  tendsto_fst.eventually h

theorem Eventually.prod_inr {lb : Filter β} {p : β → Prop} (h : ∀ᶠ x in lb, p x) (la : Filter α) :
    ∀ᶠ x in la ×ˢ lb, p (x : α × β).2 :=
  tendsto_snd.eventually h

theorem Eventually.prod_mk {la : Filter α} {pa : α → Prop} (ha : ∀ᶠ x in la, pa x) {lb : Filter β}
    {pb : β → Prop} (hb : ∀ᶠ y in lb, pb y) : ∀ᶠ p in la ×ˢ lb, pa (p : α × β).1 ∧ pb p.2 :=
  (ha.prod_inl lb).and (hb.prod_inr la)

theorem EventuallyEq.prodMap {δ} {la : Filter α} {fa ga : α → γ} (ha : fa =ᶠ[la] ga)
    {lb : Filter β} {fb gb : β → δ} (hb : fb =ᶠ[lb] gb) :
    Prod.map fa fb =ᶠ[la ×ˢ lb] Prod.map ga gb :=
  (Eventually.prod_mk ha hb).mono fun _ h => Prod.ext h.1 h.2

theorem EventuallyLE.prodMap {δ} [LE γ] [LE δ] {la : Filter α} {fa ga : α → γ} (ha : fa ≤ᶠ[la] ga)
    {lb : Filter β} {fb gb : β → δ} (hb : fb ≤ᶠ[lb] gb) :
    Prod.map fa fb ≤ᶠ[la ×ˢ lb] Prod.map ga gb :=
  Eventually.prod_mk ha hb

theorem Eventually.curry {la : Filter α} {lb : Filter β} {p : α × β → Prop}
    (h : ∀ᶠ x in la ×ˢ lb, p x) : ∀ᶠ x in la, ∀ᶠ y in lb, p (x, y) := by
  rcases eventually_prod_iff.1 h with ⟨pa, ha, pb, hb, h⟩
  exact ha.mono fun a ha => hb.mono fun b hb => h ha hb

protected lemma Frequently.uncurry {la : Filter α} {lb : Filter β} {p : α → β → Prop}
    (h : ∃ᶠ x in la, ∃ᶠ y in lb, p x y) : ∃ᶠ xy in la ×ˢ lb, p xy.1 xy.2 := by
  contrapose! h
  exact h.curry

lemma Frequently.of_curry {la : Filter α} {lb : Filter β} {p : α × β → Prop}
    (h : ∃ᶠ x in la, ∃ᶠ y in lb, p (x, y)) : ∃ᶠ xy in la ×ˢ lb, p xy :=
  h.uncurry

theorem Eventually.image_of_prod {y : α → β} {r : α → β → Prop}
    (hy : Tendsto y f g) (hr : ∀ᶠ p in f ×ˢ g, r p.1 p.2) : ∀ᶠ x in f, r x (y x) := by
  obtain ⟨p, hp, q, hq, hr⟩ := eventually_prod_iff.mp hr
  filter_upwards [hp, hy.eventually hq] with _ hp hq using hr hp hq

/-- A fact that is eventually true about all pairs `l ×ˢ l` is eventually true about
all diagonal pairs `(i, i)` -/
theorem Eventually.diag_of_prod {p : α × α → Prop} (h : ∀ᶠ i in f ×ˢ f, p i) :
    ∀ᶠ i in f, p (i, i) :=
  h.image_of_prod (r := p.curry) tendsto_id

theorem Eventually.diag_of_prod_left {f : Filter α} {g : Filter γ} {p : (α × α) × γ → Prop} :
    (∀ᶠ x in (f ×ˢ f) ×ˢ g, p x) → ∀ᶠ x : α × γ in f ×ˢ g, p ((x.1, x.1), x.2) := by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.diag_of_prod.prod_mk hs).mono fun x hx => by simp only [hst hx.1 hx.2]

theorem Eventually.diag_of_prod_right {f : Filter α} {g : Filter γ} {p : α × γ × γ → Prop} :
    (∀ᶠ x in f ×ˢ (g ×ˢ g), p x) → ∀ᶠ x : α × γ in f ×ˢ g, p (x.1, x.2, x.2) := by
  intro h
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h
  exact (ht.prod_mk hs.diag_of_prod).mono fun x hx => by simp only [hst hx.1 hx.2]

theorem tendsto_diag : Tendsto (fun i => (i, i)) f (f ×ˢ f) :=
  tendsto_iff_eventually.mpr fun _ hpr => hpr.diag_of_prod

theorem prod_iInf_left [Nonempty ι] {f : ι → Filter α} {g : Filter β} :
    (⨅ i, f i) ×ˢ g = ⨅ i, f i ×ˢ g := by
  simp only [prod_eq_inf, comap_iInf, iInf_inf]

theorem prod_iInf_right [Nonempty ι] {f : Filter α} {g : ι → Filter β} :
    (f ×ˢ ⨅ i, g i) = ⨅ i, f ×ˢ g i := by
  simp only [prod_eq_inf, comap_iInf, inf_iInf]

@[mono, gcongr]
theorem prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁ ×ˢ g₁ ≤ f₂ ×ˢ g₂ :=
  inf_le_inf (comap_mono hf) (comap_mono hg)

theorem prod_mono_left (g : Filter β) {f₁ f₂ : Filter α} (hf : f₁ ≤ f₂) : f₁ ×ˢ g ≤ f₂ ×ˢ g :=
  Filter.prod_mono hf rfl.le

theorem prod_mono_right (f : Filter α) {g₁ g₂ : Filter β} (hf : g₁ ≤ g₂) : f ×ˢ g₁ ≤ f ×ˢ g₂ :=
  Filter.prod_mono rfl.le hf

theorem prod_comap_comap_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : β₁ → α₁} {m₂ : β₂ → α₂} :
    comap m₁ f₁ ×ˢ comap m₂ f₂ = comap (fun p : β₁ × β₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ˢ f₂) := by
  simp only [prod_eq_inf, comap_comap, comap_inf, Function.comp_def]

theorem prod_comm' : f ×ˢ g = comap Prod.swap (g ×ˢ f) := by
  simp only [prod_eq_inf, comap_comap, Function.comp_def, inf_comm, Prod.swap, comap_inf]

theorem prod_comm : f ×ˢ g = map Prod.swap (g ×ˢ f) := by
  rw [prod_comm', ← map_swap_eq_comap_swap]

theorem mem_prod_iff_left {s : Set (α × β)} :
    s ∈ f ×ˢ g ↔ ∃ t ∈ f, ∀ᶠ y in g, ∀ x ∈ t, (x, y) ∈ s := by
  simp only [mem_prod_iff, prod_subset_iff]
  refine exists_congr fun _ => Iff.rfl.and <| Iff.trans ?_ exists_mem_subset_iff
  exact exists_congr fun _ => Iff.rfl.and forall₂_comm

theorem mem_prod_iff_right {s : Set (α × β)} :
    s ∈ f ×ˢ g ↔ ∃ t ∈ g, ∀ᶠ x in f, ∀ y ∈ t, (x, y) ∈ s := by
  rw [prod_comm, mem_map, mem_prod_iff_left]; rfl

@[simp]
theorem map_fst_prod (f : Filter α) (g : Filter β) [NeBot g] : map Prod.fst (f ×ˢ g) = f := by
  ext s
  simp only [mem_map, mem_prod_iff_left, mem_preimage, eventually_const, ← subset_def,
    exists_mem_subset_iff]

@[simp]
theorem map_snd_prod (f : Filter α) (g : Filter β) [NeBot f] : map Prod.snd (f ×ˢ g) = g := by
  rw [prod_comm, map_map]; apply map_fst_prod

@[simp]
theorem prod_le_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ˢ g₁ ≤ f₂ ×ˢ g₂ ↔ f₁ ≤ f₂ ∧ g₁ ≤ g₂ :=
  ⟨fun h =>
    ⟨map_fst_prod f₁ g₁ ▸ tendsto_fst.mono_left h, map_snd_prod f₁ g₁ ▸ tendsto_snd.mono_left h⟩,
    fun h => prod_mono h.1 h.2⟩

@[simp]
theorem prod_inj {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} [NeBot f₁] [NeBot g₁] :
    f₁ ×ˢ g₁ = f₂ ×ˢ g₂ ↔ f₁ = f₂ ∧ g₁ = g₂ := by
  refine ⟨fun h => ?_, fun h => h.1 ▸ h.2 ▸ rfl⟩
  have hle : f₁ ≤ f₂ ∧ g₁ ≤ g₂ := prod_le_prod.1 h.le
  haveI := neBot_of_le hle.1; haveI := neBot_of_le hle.2
  exact ⟨hle.1.antisymm <| (prod_le_prod.1 h.ge).1, hle.2.antisymm <| (prod_le_prod.1 h.ge).2⟩

theorem eventually_swap_iff {p : α × β → Prop} :
    (∀ᶠ x : α × β in f ×ˢ g, p x) ↔ ∀ᶠ y : β × α in g ×ˢ f, p y.swap := by
  rw [prod_comm]; rfl

/-- A technical lemma which is a generalization of `Filter.Eventually.trans_prod`. -/
lemma Eventually.eventually_prod_of_eventually_swap {h : Filter γ}
    [NeBot g] {p : α → β → Prop} {q : β → γ → Prop} {r : α → γ → Prop}
    (hp : ∀ᶠ x in f, ∀ᶠ y in g, p x y) (hq : ∀ᶠ z in h, ∀ᶠ y in g, q y z)
    (hpqr : ∀ x y z, p x y → q y z → r x z) :
    ∀ᶠ xz in f ×ˢ h, r xz.1 xz.2 := by
  refine eventually_prod_iff.mpr ⟨_, hp, _, hq, fun {x} hx {z} hz ↦ ?_⟩
  rcases (hx.and hz).exists with ⟨y, hpy, hqy⟩
  exact hpqr x y z hpy hqy

lemma Eventually.trans_prod {h : Filter γ}
    [NeBot g] {p : α → β → Prop} {q : β → γ → Prop} {r : α → γ → Prop}
    (hp : ∀ᶠ xy in f ×ˢ g, p xy.1 xy.2) (hq : ∀ᶠ yz in g ×ˢ h, q yz.1 yz.2)
    (hpqr : ∀ x y z, p x y → q y z → r x z) :
    ∀ᶠ xz in f ×ˢ h, r xz.1 xz.2 :=
  hp.curry.eventually_prod_of_eventually_swap (eventually_swap_iff.mp hq |>.curry) hpqr

theorem prod_assoc (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) = f ×ˢ (g ×ˢ h) := by
  simp_rw [← comap_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_symm_apply]

theorem prod_assoc_symm (f : Filter α) (g : Filter β) (h : Filter γ) :
    map (Equiv.prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) = (f ×ˢ g) ×ˢ h := by
  simp_rw [map_equiv_symm, prod_eq_inf, comap_inf, comap_comap, inf_assoc,
    Function.comp_def, Equiv.prodAssoc_apply]

theorem tendsto_prodAssoc {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ) ((f ×ˢ g) ×ˢ h) (f ×ˢ (g ×ˢ h)) :=
  (prod_assoc f g h).le

theorem tendsto_prodAssoc_symm {h : Filter γ} :
    Tendsto (Equiv.prodAssoc α β γ).symm (f ×ˢ (g ×ˢ h)) ((f ×ˢ g) ×ˢ h) :=
  (prod_assoc_symm f g h).le

/-- A useful lemma when dealing with uniformities. -/
theorem map_swap4_prod {h : Filter γ} {k : Filter δ} :
    map (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k)) =
      (f ×ˢ h) ×ˢ (g ×ˢ k) := by
  simp_rw [map_swap4_eq_comap, prod_eq_inf, comap_inf, comap_comap]; ac_rfl

theorem tendsto_swap4_prod {h : Filter γ} {k : Filter δ} :
    Tendsto (fun p : (α × β) × γ × δ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ((f ×ˢ g) ×ˢ (h ×ˢ k))
      ((f ×ˢ h) ×ˢ (g ×ˢ k)) :=
  map_swap4_prod.le

theorem prod_map_map_eq.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
    map m₁ f₁ ×ˢ map m₂ f₂ = map (fun p : α₁ × α₂ => (m₁ p.1, m₂ p.2)) (f₁ ×ˢ f₂) :=
  le_antisymm
    (fun s hs =>
      let ⟨s₁, hs₁, s₂, hs₂, h⟩ := mem_prod_iff.mp hs
      mem_of_superset (prod_mem_prod (image_mem_map hs₁) (image_mem_map hs₂)) <|
        by rwa [prod_image_image_eq, image_subset_iff])
    ((tendsto_map.comp tendsto_fst).prodMk (tendsto_map.comp tendsto_snd))

theorem prod_map_map_eq' {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*} (f : α₁ → α₂)
    (g : β₁ → β₂) (F : Filter α₁) (G : Filter β₁) :
    map f F ×ˢ map g G = map (Prod.map f g) (F ×ˢ G) :=
  prod_map_map_eq

theorem prod_map_left (f : α → β) (F : Filter α) (G : Filter γ) :
    map f F ×ˢ G = map (Prod.map f id) (F ×ˢ G) := by
  rw [← prod_map_map_eq', map_id]

theorem prod_map_right (f : β → γ) (F : Filter α) (G : Filter β) :
    F ×ˢ map f G = map (Prod.map id f) (F ×ˢ G) := by
  rw [← prod_map_map_eq', map_id]

theorem le_prod_map_fst_snd {f : Filter (α × β)} : f ≤ map Prod.fst f ×ˢ map Prod.snd f :=
  le_inf le_comap_map le_comap_map

theorem Tendsto.prodMap {δ : Type*} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a ×ˢ b) (c ×ˢ d) := by
  rw [Tendsto, Prod.map_def, ← prod_map_map_eq]
  exact Filter.prod_mono hf hg

protected theorem map_prod (m : α × β → γ) (f : Filter α) (g : Filter β) :
    map m (f ×ˢ g) = (f.map fun a b => m (a, b)).seq g := by
  simp only [Filter.ext_iff, mem_map, mem_prod_iff, mem_map_seq_iff, exists_and_left]
  intro s
  constructor
  · exact fun ⟨t, ht, s, hs, h⟩ => ⟨s, hs, t, ht, fun x hx y hy => @h ⟨x, y⟩ ⟨hx, hy⟩⟩
  · exact fun ⟨s, hs, t, ht, h⟩ => ⟨t, ht, s, hs, fun ⟨x, y⟩ ⟨hx, hy⟩ => h x hx y hy⟩

theorem prod_eq : f ×ˢ g = (f.map Prod.mk).seq g := f.map_prod id g

theorem prod_inf_prod {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} :
    (f₁ ×ˢ g₁) ⊓ (f₂ ×ˢ g₂) = (f₁ ⊓ f₂) ×ˢ (g₁ ⊓ g₂) := by
  simp only [prod_eq_inf, comap_inf, inf_comm, inf_assoc, inf_left_comm]

theorem inf_prod {f₁ f₂ : Filter α} : (f₁ ⊓ f₂) ×ˢ g = (f₁ ×ˢ g) ⊓ (f₂ ×ˢ g) := by
  rw [prod_inf_prod, inf_idem]

theorem prod_inf {g₁ g₂ : Filter β} : f ×ˢ (g₁ ⊓ g₂) = (f ×ˢ g₁) ⊓ (f ×ˢ g₂) := by
  rw [prod_inf_prod, inf_idem]

@[simp]
theorem prod_principal_principal {s : Set α} {t : Set β} : 𝓟 s ×ˢ 𝓟 t = 𝓟 (s ×ˢ t) := by
  simp only [prod_eq_inf, comap_principal, principal_eq_iff_eq, comap_principal, inf_principal]; rfl

@[simp]
theorem pure_prod {a : α} {f : Filter β} : pure a ×ˢ f = map (Prod.mk a) f := by
  rw [prod_eq, map_pure, pure_seq_eq_map]

theorem map_pure_prod (f : α → β → γ) (a : α) (B : Filter β) :
    map (Function.uncurry f) (pure a ×ˢ B) = map (f a) B := by
  rw [Filter.pure_prod]; rfl

@[simp]
theorem prod_pure {b : β} : f ×ˢ pure b = map (fun a => (a, b)) f := by
  rw [prod_eq, seq_pure, map_map]; rfl

theorem prod_pure_pure {a : α} {b : β} :
    (pure a : Filter α) ×ˢ (pure b : Filter β) = pure (a, b) := by simp

@[simp]
theorem prod_eq_bot : f ×ˢ g = ⊥ ↔ f = ⊥ ∨ g = ⊥ := by
  simp_rw [← empty_mem_iff_bot, mem_prod_iff, subset_empty_iff, prod_eq_empty_iff, ← exists_prop,
    Subtype.exists', exists_or, exists_const, Subtype.exists, exists_prop, exists_eq_right]

@[simp] theorem prod_bot : f ×ˢ (⊥ : Filter β) = ⊥ := prod_eq_bot.2 <| Or.inr rfl

@[simp] theorem bot_prod : (⊥ : Filter α) ×ˢ g = ⊥ := prod_eq_bot.2 <| Or.inl rfl

theorem prod_neBot : NeBot (f ×ˢ g) ↔ NeBot f ∧ NeBot g := by
  simp only [neBot_iff, Ne, prod_eq_bot, not_or]

protected theorem NeBot.prod (hf : NeBot f) (hg : NeBot g) : NeBot (f ×ˢ g) := prod_neBot.2 ⟨hf, hg⟩

instance prod.instNeBot [hf : NeBot f] [hg : NeBot g] : NeBot (f ×ˢ g) := hf.prod hg

@[simp]
lemma disjoint_prod {f' : Filter α} {g' : Filter β} :
    Disjoint (f ×ˢ g) (f' ×ˢ g') ↔ Disjoint f f' ∨ Disjoint g g' := by
  simp only [disjoint_iff, prod_inf_prod, prod_eq_bot]

/-- `p ∧ q` occurs frequently along the product of two filters
iff both `p` and `q` occur frequently along the corresponding filters. -/
theorem frequently_prod_and {p : α → Prop} {q : β → Prop} :
    (∃ᶠ x in f ×ˢ g, p x.1 ∧ q x.2) ↔ (∃ᶠ a in f, p a) ∧ ∃ᶠ b in g, q b := by
  simp only [frequently_iff_neBot, ← prod_neBot, ← prod_inf_prod, prod_principal_principal]
  rfl

theorem tendsto_prod_iff {f : α × β → γ} {x : Filter α} {y : Filter β} {z : Filter γ} :
    Tendsto f (x ×ˢ y) z ↔ ∀ W ∈ z, ∃ U ∈ x, ∃ V ∈ y, ∀ x y, x ∈ U → y ∈ V → f (x, y) ∈ W := by
  simp only [tendsto_def, mem_prod_iff, prod_sub_preimage_iff]

theorem tendsto_prod_iff' {g' : Filter γ} {s : α → β × γ} :
    Tendsto s f (g ×ˢ g') ↔ Tendsto (fun n => (s n).1) f g ∧ Tendsto (fun n => (s n).2) f g' := by
  simp only [prod_eq_inf, tendsto_inf, tendsto_comap_iff, Function.comp_def]

theorem le_prod {f : Filter (α × β)} {g : Filter α} {g' : Filter β} :
    (f ≤ g ×ˢ g') ↔ Tendsto Prod.fst f g ∧ Tendsto Prod.snd f g' :=
  tendsto_prod_iff'

end Prod

/-! ### Coproducts of filters -/

section Coprod

variable {f : Filter α} {g : Filter β}

theorem coprod_eq_prod_top_sup_top_prod (f : Filter α) (g : Filter β) :
    Filter.coprod f g = f ×ˢ ⊤ ⊔ ⊤ ×ˢ g := by
  rw [prod_top, top_prod]
  rfl

theorem mem_coprod_iff {s : Set (α × β)} {f : Filter α} {g : Filter β} :
    s ∈ f.coprod g ↔ (∃ t₁ ∈ f, Prod.fst ⁻¹' t₁ ⊆ s) ∧ ∃ t₂ ∈ g, Prod.snd ⁻¹' t₂ ⊆ s := by
  simp [Filter.coprod]

@[simp]
theorem bot_coprod (l : Filter β) : (⊥ : Filter α).coprod l = comap Prod.snd l := by
  simp [Filter.coprod]

@[simp]
theorem coprod_bot (l : Filter α) : l.coprod (⊥ : Filter β) = comap Prod.fst l := by
  simp [Filter.coprod]

theorem bot_coprod_bot : (⊥ : Filter α).coprod (⊥ : Filter β) = ⊥ := by simp

theorem compl_mem_coprod {s : Set (α × β)} {la : Filter α} {lb : Filter β} :
    sᶜ ∈ la.coprod lb ↔ (Prod.fst '' s)ᶜ ∈ la ∧ (Prod.snd '' s)ᶜ ∈ lb := by
  simp only [Filter.coprod, mem_sup, compl_mem_comap]

@[mono]
theorem coprod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : f₁ ≤ f₂) (hg : g₁ ≤ g₂) :
    f₁.coprod g₁ ≤ f₂.coprod g₂ :=
  sup_le_sup (comap_mono hf) (comap_mono hg)

theorem coprod_neBot_iff : (f.coprod g).NeBot ↔ f.NeBot ∧ Nonempty β ∨ Nonempty α ∧ g.NeBot := by
  simp [Filter.coprod]

@[instance]
theorem coprod_neBot_left [NeBot f] [Nonempty β] : (f.coprod g).NeBot :=
  coprod_neBot_iff.2 (Or.inl ⟨‹_›, ‹_›⟩)

@[instance]
theorem coprod_neBot_right [NeBot g] [Nonempty α] : (f.coprod g).NeBot :=
  coprod_neBot_iff.2 (Or.inr ⟨‹_›, ‹_›⟩)

set_option linter.style.whitespace false in -- manual alignment is not recognised
theorem coprod_inf_prod_le (f₁ f₂ : Filter α) (g₁ g₂ : Filter β) :
    f₁.coprod g₁ ⊓ f₂ ×ˢ g₂ ≤ f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁ := calc
  f₁.coprod g₁ ⊓ f₂ ×ˢ g₂
  _ = (f₁ ×ˢ ⊤ ⊔ ⊤ ×ˢ g₁) ⊓ f₂ ×ˢ g₂            := by rw [coprod_eq_prod_top_sup_top_prod]
  _ = f₁ ×ˢ ⊤ ⊓ f₂ ×ˢ g₂ ⊔ ⊤ ×ˢ g₁ ⊓ f₂ ×ˢ g₂   := inf_sup_right _ _ _
  _ = (f₁ ⊓ f₂) ×ˢ g₂ ⊔ f₂ ×ˢ (g₁ ⊓ g₂)         := by simp [prod_inf_prod]
  _ ≤ f₁ ×ˢ g₂ ⊔ f₂ ×ˢ g₁                       :=
    sup_le_sup (prod_mono inf_le_left le_rfl) (prod_mono le_rfl inf_le_left)

theorem principal_coprod_principal (s : Set α) (t : Set β) :
    (𝓟 s).coprod (𝓟 t) = 𝓟 (sᶜ ×ˢ tᶜ)ᶜ := by
  rw [Filter.coprod, comap_principal, comap_principal, sup_principal, Set.prod_eq, compl_inter,
    preimage_compl, preimage_compl, compl_compl, compl_compl]

-- this inequality can be strict; see `map_const_principal_coprod_map_id_principal` and
-- `map_prodMap_const_id_principal_coprod_principal` below.
theorem map_prodMap_coprod_le.{u, v, w, x} {α₁ : Type u} {α₂ : Type v} {β₁ : Type w} {β₂ : Type x}
    {f₁ : Filter α₁} {f₂ : Filter α₂} {m₁ : α₁ → β₁} {m₂ : α₂ → β₂} :
    map (Prod.map m₁ m₂) (f₁.coprod f₂) ≤ (map m₁ f₁).coprod (map m₂ f₂) := by
  intro s
  simp only [mem_map, mem_coprod_iff]
  rintro ⟨⟨u₁, hu₁, h₁⟩, u₂, hu₂, h₂⟩
  refine ⟨⟨m₁ ⁻¹' u₁, hu₁, fun _ hx => h₁ ?_⟩, ⟨m₂ ⁻¹' u₂, hu₂, fun _ hx => h₂ ?_⟩⟩ <;> convert hx

/-- Characterization of the coproduct of the `Filter.map`s of two principal filters `𝓟 {a}` and
`𝓟 {i}`, the first under the constant function `fun a => b` and the second under the identity
function. Together with the next lemma, `map_prodMap_const_id_principal_coprod_principal`, this
provides an example showing that the inequality in the lemma `map_prodMap_coprod_le` can be strict.
-/
theorem map_const_principal_coprod_map_id_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
    (map (fun _ => b) (𝓟 {a})).coprod (map id (𝓟 {i})) =
      𝓟 ((({b} : Set β) ×ˢ univ) ∪ (univ ×ˢ ({i} : Set ι))) := by
  simp only [map_principal, Filter.coprod, comap_principal, sup_principal, image_singleton,
    prod_univ, univ_prod, id]

/-- Characterization of the `Filter.map` of the coproduct of two principal filters `𝓟 {a}` and
`𝓟 {i}`, under the `Prod.map` of two functions, respectively the constant function `fun a => b` and
the identity function.  Together with the previous lemma,
`map_const_principal_coprod_map_id_principal`, this provides an example showing that the inequality
in the lemma `map_prodMap_coprod_le` can be strict. -/
theorem map_prodMap_const_id_principal_coprod_principal {α β ι : Type*} (a : α) (b : β) (i : ι) :
    map (Prod.map (fun _ : α => b) id) ((𝓟 {a}).coprod (𝓟 {i})) =
      𝓟 (({b} : Set β) ×ˢ (univ : Set ι)) := by
  rw [principal_coprod_principal, map_principal]
  congr
  ext ⟨b', i'⟩
  constructor
  · rintro ⟨⟨a'', i''⟩, _, h₂, h₃⟩
    simp
  · rintro ⟨h₁, _⟩
    use (a, i')
    simpa using h₁.symm

theorem Tendsto.prodMap_coprod {δ : Type*} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}
    {c : Filter γ} {d : Filter δ} (hf : Tendsto f a c) (hg : Tendsto g b d) :
    Tendsto (Prod.map f g) (a.coprod b) (c.coprod d) :=
  map_prodMap_coprod_le.trans (coprod_mono hf hg)

lemma Tendsto.coprod_of_prod_top_right {f : α × β → γ} {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (h₁ : ∀ s : Set α, s ∈ la → Tendsto f (𝓟 sᶜ ×ˢ lb) lc)
    (h₂ : Tendsto f (la ×ˢ ⊤) lc) :
    Tendsto f (la.coprod lb) lc := by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

lemma Tendsto.coprod_of_prod_top_left {f : α × β → γ} {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (h₁ : ∀ s : Set β, s ∈ lb → Tendsto f (la ×ˢ 𝓟 sᶜ) lc)
    (h₂ : Tendsto f (⊤ ×ˢ lb) lc) :
    Tendsto f (la.coprod lb) lc := by
  simp_all [tendsto_prod_iff, coprod_eq_prod_top_sup_top_prod]
  grind

end Coprod

end Filter
