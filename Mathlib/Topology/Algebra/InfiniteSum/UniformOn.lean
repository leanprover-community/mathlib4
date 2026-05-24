/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler, Andrew Yang
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Infinite sum and products that converge uniformly

## Main definitions
- `HasProdUniformlyOn f g s` : `∏ i, f i b` converges uniformly on `s` to `g`.
- `HasProdLocallyUniformlyOn f g s` : `∏ i, f i b` converges locally uniformly on `s` to `g`.
- `HasProdUniformly f g` : `∏ i, f i b` converges uniformly to `g`.
- `HasProdLocallyUniformly f g` : `∏ i, f i b` converges locally uniformly to `g`.
-/

@[expose] public section

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*} [CommMonoid α] {f : ι → β → α} {g : β → α}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α]

/-!
## Uniform convergence of sums and products
-/

section UniformlyOn

variable (f g s) in
/-- `HasProdUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges uniformly on `s` to `g`. -/
@[to_additive /-- `HasSumUniformlyOn f g s` means that the (potentially infinite) sum `∑' i, f i b`
for `b : β` converges uniformly on `s` to `g`. -/]
def HasProdUniformlyOn : Prop := HasProd (UniformOnFun.ofFun {s} ∘ f) (UniformOnFun.ofFun {s} g)

variable (f g s) in
/-- `MultipliableUniformlyOn f s` means that there is some infinite product to which
`f` converges uniformly on `s`. Use `fun x ↦ ∏' i, f i x` to get the product function. -/
@[to_additive /-- `SummableUniformlyOn f s` means that there is some infinite sum to
which `f` converges uniformly on `s`. Use fun x ↦ ∑' i, f i x to get the sum function. -/]
def MultipliableUniformlyOn : Prop := Multipliable (UniformOnFun.ofFun {s} ∘ f)

@[to_additive]
lemma MultipliableUniformlyOn.exists (h : MultipliableUniformlyOn f s) :
    ∃ g, HasProdUniformlyOn f g s :=
  h

@[to_additive]
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g s) :
    MultipliableUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
lemma hasProdUniformlyOn_iff_tendstoUniformlyOn :
    HasProdUniformlyOn f g s ↔ TendstoUniformlyOn (∏ i ∈ ·, f i ·) g atTop s := by
  simpa [HasProdUniformlyOn, HasProd, ← UniformOnFun.ofFun_prod, Finset.prod_fn] using
    UniformOnFun.tendsto_iff_tendstoUniformlyOn (𝔖 := {s})

@[to_additive]
alias ⟨HasProdUniformlyOn.tendstoUniformlyOn, _⟩ := hasProdUniformlyOn_iff_tendstoUniformlyOn

@[to_additive]
lemma HasProdUniformlyOn.congr {f' : ι → β → α}
    (h : HasProdUniformlyOn f g s)
    (hff' : ∀ᶠ (n : Finset ι) in atTop, s.EqOn (∏ i ∈ n, f i ·) (∏ i ∈ n, f' i ·)) :
    HasProdUniformlyOn f' g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr hff')

@[to_additive]
lemma HasProdUniformlyOn.congr_right {g' : β → α}
    (h : HasProdUniformlyOn f g s) (hgg' : s.EqOn g g') :
    HasProdUniformlyOn f g' s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr (h.tendstoUniformlyOn.congr_right hgg')

@[to_additive]
lemma HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
    {f : ℕ → β → α} (h : HasProdUniformlyOn f g s) :
    TendstoUniformlyOn (∏ i ∈ .range ·, f i ·) g atTop s :=
  (tendsto_finset_range.eventually <| h.tendstoUniformlyOn · ·)

@[to_additive]
theorem HasProdUniformlyOn.hasProd (h : HasProdUniformlyOn f g s) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  h.tendstoUniformlyOn.tendsto_at hx

@[to_additive]
theorem HasProdUniformlyOn.tprod_eqOn [T2Space α] (h : HasProdUniformlyOn f g s) :
    s.EqOn (∏' b, f b ·) g :=
  fun _ hx ↦ (h.hasProd hx).tprod_eq

@[deprecated (since := "2025-11-23")]
alias HasProdUniformlyOn.tprod_eq := HasProdUniformlyOn.tprod_eqOn

@[deprecated (since := "2025-11-23")]
alias HasSumUniformlyOn.tsum_eq := HasSumUniformlyOn.tsum_eqOn

@[to_additive]
theorem MultipliableUniformlyOn.multipliable (h : MultipliableUniformlyOn f s) (hx : x ∈ s) :
    Multipliable (f · x) :=
  (h.exists.choose_spec.hasProd hx).multipliable

@[to_additive]
theorem MultipliableUniformlyOn.hasProdUniformlyOn (h : MultipliableUniformlyOn f s) :
    HasProdUniformlyOn f (∏' i, f i ·) s := by
  obtain ⟨g, hg⟩ := h.exists
  have hp := hg
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at hg ⊢
  exact hg.congr_inseparable_right fun x hx =>
    tendsto_nhds_unique_inseparable (hp.hasProd hx) (hp.hasProd hx).multipliable.hasProd

@[to_additive]
theorem multipliableUniformlyOn_iff_hasProdUniformlyOn :
    MultipliableUniformlyOn f s ↔ HasProdUniformlyOn f (∏' i, f i ·) s :=
  ⟨MultipliableUniformlyOn.hasProdUniformlyOn, HasProdUniformlyOn.multipliableUniformlyOn⟩

@[to_additive]
lemma HasProdUniformlyOn.mono {t : Set β}
    (h : HasProdUniformlyOn f g t) (hst : s ⊆ t) : HasProdUniformlyOn f g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr <| h.tendstoUniformlyOn.mono hst

@[to_additive]
lemma MultipliableUniformlyOn.mono {t : Set β}
    (h : MultipliableUniformlyOn f t) (hst : s ⊆ t) : MultipliableUniformlyOn f s :=
  (h.exists.choose_spec.mono hst).multipliableUniformlyOn

end UniformlyOn

section LocallyUniformlyOn
/-!
## Locally uniform convergence of sums and products
-/

variable [TopologicalSpace β]

variable (f g s) in
/-- `HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/
@[to_additive /-- `HasSumLocallyUniformlyOn f g s` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/]
def HasProdLocallyUniformlyOn : Prop := TendstoLocallyUniformlyOn (∏ i ∈ ·, f i ·) g atTop s

variable (f g s) in
/-- `MultipliableLocallyUniformlyOn f s` means that the product `∏' i, f i b` converges locally
uniformly on `s` to something. -/
@[to_additive /-- `SummableLocallyUniformlyOn f s` means that `∑' i, f i b` converges locally
uniformly on `s` to something. -/]
def MultipliableLocallyUniformlyOn : Prop := ∃ g, HasProdLocallyUniformlyOn f g s

@[to_additive]
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn :
    HasProdLocallyUniformlyOn f g s ↔ TendstoLocallyUniformlyOn (∏ i ∈ ·, f i ·) g atTop s :=
  Iff.rfl

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly on `s` to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly to `g`, then the sum converges locally uniformly. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/]
lemma hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g t) : HasProdLocallyUniformlyOn f g s :=
  tendstoLocallyUniformlyOn_of_forall_exists_nhds <| by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

lemma HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact
    (h : HasProdLocallyUniformlyOn f g s) (hs : IsCompact s) : HasProdUniformlyOn f g s := by
  rwa [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    ← tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hs]

lemma HasProdLocallyUniformlyOn.exists_hasProdUniformlyOn [LocallyCompactSpace β]
    (h : HasProdLocallyUniformlyOn f g s) (hx : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g t := by
  obtain ⟨K, ⟨hK1, hK2⟩, hK3⟩ := (compact_basis_nhds x).mem_iff.mp hx
  exact ⟨K, nhdsWithin_le_nhds hK1,
    HasProdLocallyUniformlyOn.hasProdUniformlyOn_of_isCompact (h.mono hK3) hK2⟩

@[to_additive]
lemma HasProdUniformlyOn.hasProdLocallyUniformlyOn (h : HasProdUniformlyOn f g s) :
    HasProdLocallyUniformlyOn f g s := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn, HasProdLocallyUniformlyOn] at *
  exact h.tendstoLocallyUniformlyOn

@[to_additive]
lemma hasProdLocallyUniformlyOn_of_forall_compact (hs : IsOpen s) [LocallyCompactSpace β]
    (h : ∀ K ⊆ s, IsCompact K → HasProdUniformlyOn f g K) : HasProdLocallyUniformlyOn f g s := by
  rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
lemma HasProdLocallyUniformlyOn.mono {t : Set β}
    (h : HasProdLocallyUniformlyOn f g t) (hst : s ⊆ t) : HasProdLocallyUniformlyOn f g s :=
  TendstoLocallyUniformlyOn.mono h hst

@[to_additive]
lemma MultipliableLocallyUniformlyOn.mono {t : Set β}
    (h : MultipliableLocallyUniformlyOn f t) (hst : s ⊆ t) : MultipliableLocallyUniformlyOn f s :=
  (h.choose_spec.mono hst).multipliableLocallyUniformlyOn

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly,
then the product converges locally uniformly on `s`. Note that this is not a tautology, and the
converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly, then the sum converges locally uniformly. Note that this is not a tautology,
and the converse is only true if the domain is locally compact. -/]
lemma multipliableLocallyUniformlyOn_of_of_forall_exists_nhds
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, MultipliableUniformlyOn f t) :
    MultipliableLocallyUniformlyOn f s :=
  (hasProdLocallyUniformlyOn_of_of_forall_exists_nhds <| fun x hx ↦ match h x hx with
  | ⟨t, ht, htr⟩ => ⟨t, ht, htr.hasProdUniformlyOn⟩).multipliableLocallyUniformlyOn

lemma MultipliableLocallyUniformlyOn.multipliableUniformlyOn_of_isCompact
    (h : MultipliableLocallyUniformlyOn f s) (hs : IsCompact s) : MultipliableUniformlyOn f s :=
  (h.choose_spec.hasProdUniformlyOn_of_isCompact hs).multipliableUniformlyOn

lemma MultipliableLocallyUniformlyOn.exists_multipliableUniformlyOn [LocallyCompactSpace β]
    (h : MultipliableLocallyUniformlyOn f s) (hx : s ∈ 𝓝 x) :
    ∃ t ∈ 𝓝[s] x, MultipliableUniformlyOn f t :=
  let H := (h.choose_spec.exists_hasProdUniformlyOn hx).choose_spec
  ⟨_, H.1, H.2.multipliableUniformlyOn⟩

@[to_additive]
theorem HasProdLocallyUniformlyOn.hasProd (h : HasProdLocallyUniformlyOn f g s) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  h.tendsto_at hx

@[to_additive]
theorem MultipliableLocallyUniformlyOn.multipliable
    (h : MultipliableLocallyUniformlyOn f s) (hx : x ∈ s) : Multipliable (f · x) :=
  match h with | ⟨_, hg⟩ => (hg.hasProd hx).multipliable

@[to_additive]
theorem MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn
    (h : MultipliableLocallyUniformlyOn f s) :
    HasProdLocallyUniformlyOn f (∏' i, f i ·) s :=
  h.elim fun _ hg => hg.congr_inseparable_right fun _ hx =>
    tendsto_nhds_unique_inseparable (hg.hasProd hx) (hg.hasProd hx).multipliable.hasProd

@[to_additive]
theorem HasProdLocallyUniformlyOn.tprod_eqOn [T2Space α]
    (h : HasProdLocallyUniformlyOn f g s) : Set.EqOn (∏' i, f i ·) g s :=
  fun _ hx ↦ (h.hasProd hx).tprod_eq

@[to_additive]
lemma MultipliableLocallyUniformlyOn_congr
    {f f' : ι → β → α} (h : ∀ i, s.EqOn (f i) (f' i))
    (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLocallyUniformlyOn f' s := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  exact (h2.hasProdLocallyUniformlyOn).congr fun v ↦ eqOn_fun_finsetProd h v

@[to_additive]
theorem HasProdLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
    (h : HasProdLocallyUniformlyOn f g s) (h' : γ → β) (hh : Set.MapsTo h' t s)
    (chh : ContinuousOn h' t) :
    HasProdLocallyUniformlyOn (fun i y ↦ f i (h' y)) (g ∘ h') t :=
  TendstoLocallyUniformlyOn.comp h h' hh chh

@[to_additive]
theorem MultipliableLocallyUniformlyOn.comp {γ : Type*} [TopologicalSpace γ] {t : Set γ}
    (h : MultipliableLocallyUniformlyOn f s) (h' : γ → β) (hh : Set.MapsTo h' t s)
    (chh : ContinuousOn h' t) : MultipliableLocallyUniformlyOn (fun i y ↦ f i (h' y)) t :=
  (h.hasProdLocallyUniformlyOn.comp h' hh chh).multipliableLocallyUniformlyOn

@[to_additive]
lemma HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
    {f : ℕ → β → α} (h : HasProdLocallyUniformlyOn f g s) :
    TendstoLocallyUniformlyOn (fun N b ↦ ∏ i ∈ Finset.range N, f i b) g atTop s := by
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  intro v hv r hr
  obtain ⟨t, ht, htr⟩ := h v hv r hr
  exact ⟨t, ht, Filter.tendsto_finset_range.eventually htr⟩

@[to_additive]
theorem multipliableLocallyUniformlyOn_iff_hasProdLocallyUniformlyOn :
    MultipliableLocallyUniformlyOn f s ↔ HasProdLocallyUniformlyOn f (∏' i, f i ·) s :=
  ⟨MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn,
    HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn⟩

end LocallyUniformlyOn

section Uniformly

variable (f g) in
/-- `HasProdUniformly f g` means that
the product `∏ i, f i b` converges uniformly (wrt `b`) to `g`. -/
@[to_additive /-- `HasSumUniformly f g` means that
the sum `∑ i, f i b` converges uniformly (wrt `b`) to `g`. -/]
def HasProdUniformly : Prop := HasProd (UniformFun.ofFun ∘ f) (UniformFun.ofFun g)

variable (f g) in
/-- `MultipliableUniformly f` means that there is some infinite product to which
`f` converges uniformly. Use `fun x ↦ ∏' i, f i x` to get the product function. -/
@[to_additive /-- `SummableUniformly f` means that there is some infinite sum to which
`f` converges uniformly. Use `fun x ↦ ∑' i, f i x` to get the product function. -/]
def MultipliableUniformly : Prop := Multipliable (UniformFun.ofFun ∘ f)

@[to_additive]
lemma MultipliableUniformly.exists (h : MultipliableUniformly f) :
    ∃ g, HasProdUniformly f g :=
  h

@[to_additive]
theorem HasProdUniformly.multipliableUniformly (h : HasProdUniformly f g) :
    MultipliableUniformly f :=
  ⟨g, h⟩

@[to_additive]
lemma hasProdUniformly_iff_tendstoUniformly :
    HasProdUniformly f g ↔ TendstoUniformly (∏ i ∈ ·, f i ·) g atTop := by
  simpa [HasProdUniformly, HasProd, ← UniformFun.ofFun_prod, Finset.prod_fn] using
    UniformFun.tendsto_iff_tendstoUniformly

@[to_additive]
alias ⟨HasProdUniformly.tendstoUniformly, _⟩ := hasProdUniformly_iff_tendstoUniformly

@[to_additive]
theorem HasProdUniformly.hasProdUniformlyOn (h : HasProdUniformly f g) :
    HasProdUniformlyOn f g s :=
  hasProdUniformlyOn_iff_tendstoUniformlyOn.mpr h.tendstoUniformly.tendstoUniformlyOn

@[to_additive]
lemma hasProdUniformlyOn_univ_iff :
    HasProdUniformlyOn f g .univ ↔ HasProdUniformly f g := by
  simp [hasProdUniformly_iff_tendstoUniformly, hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_univ]

@[to_additive]
theorem MultipliableUniformly.multipliableUniformlyOn (h : MultipliableUniformly f) :
    MultipliableUniformlyOn f s :=
  h.exists.choose_spec.hasProdUniformlyOn.multipliableUniformlyOn

@[to_additive]
lemma multipliableUniformlyOn_univ_iff :
    MultipliableUniformlyOn f .univ ↔ MultipliableUniformly f :=
  ⟨fun h ↦ (hasProdUniformlyOn_univ_iff.mp h.exists.choose_spec).multipliableUniformly,
    MultipliableUniformly.multipliableUniformlyOn⟩

@[to_additive]
lemma HasProdUniformly.congr {f' : ι → β → α}
    (h : HasProdUniformly f g)
    (hff' : ∀ᶠ (n : Finset ι) in atTop, ∀ b, ∏ i ∈ n, f i b = ∏ i ∈ n, f' i b) :
    HasProdUniformly f' g := by
  rw [hasProdUniformly_iff_tendstoUniformly] at *
  exact (tendstoUniformly_congr (by simpa only [EventuallyEq, funext_iff])).mp h

@[to_additive]
lemma HasProdUniformly.tendstoUniformlyOn_finsetRange {f : ℕ → β → α} (h : HasProdUniformly f g) :
    TendstoUniformly (∏ i ∈ Finset.range ·, f i ·) g atTop :=
  (tendsto_finset_range.eventually <| h.tendstoUniformly · ·)

@[to_additive]
theorem HasProdUniformly.hasProd (h : HasProdUniformly f g) : HasProd (f · x) (g x) :=
  h.tendstoUniformly.tendsto_at _

@[to_additive]
theorem MultipliableUniformly.multipliable (h : MultipliableUniformly f) : Multipliable (f · x) :=
  h.exists.choose_spec.hasProd.multipliable

@[to_additive]
theorem MultipliableUniformly.hasProdUniformly (h : MultipliableUniformly f) :
    HasProdUniformly f (∏' i, f i ·) :=
  hasProdUniformlyOn_univ_iff.1 (multipliableUniformlyOn_univ_iff.2 h).hasProdUniformlyOn

@[to_additive]
theorem multipliableUniformly_iff_hasProdUniformly :
    MultipliableUniformly f ↔ HasProdUniformly f (∏' i, f i ·) :=
  ⟨MultipliableUniformly.hasProdUniformly, HasProdUniformly.multipliableUniformly⟩

end Uniformly

section LocallyUniformly
/-!
## Locally uniform convergence of sums and products
-/

variable [TopologicalSpace β]

variable (f g) in
/-- `HasProdLocallyUniformly f g` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly to `g b` (in the sense of
`TendstoLocallyUniformly`). -/
@[to_additive /-- `HasSumLocallyUniformly f g` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly to `g b` (in the sense of
`TendstoLocallyUniformly`). -/]
def HasProdLocallyUniformly : Prop := TendstoLocallyUniformly (∏ i ∈ ·, f i ·) g atTop

variable (f g) in
/-- `MultipliableLocallyUniformly f` means that the product `∏' i, f i b` converges locally
uniformly to something. -/
@[to_additive /-- `SummableLocallyUniformly f` means that `∑' i, f i b` converges locally
uniformly to something. -/]
def MultipliableLocallyUniformly : Prop := ∃ g, HasProdLocallyUniformly f g

@[to_additive]
lemma MultipliableLocallyUniformly.exists (h : MultipliableLocallyUniformly f) :
    ∃ g, HasProdLocallyUniformly f g := h

@[to_additive]
theorem HasProdLocallyUniformly.multipliableLocallyUniformly
    (h : HasProdLocallyUniformly f g) : MultipliableLocallyUniformly f :=
  ⟨g, h⟩

@[to_additive]
lemma hasProdLocallyUniformly_iff_tendstoLocallyUniformly :
    HasProdLocallyUniformly f g ↔ TendstoLocallyUniformly (∏ i ∈ ·, f i ·) g atTop :=
  .rfl

@[to_additive]
theorem HasProdLocallyUniformly.hasProdLocallyUniformlyOn (h : HasProdLocallyUniformly f g) :
    HasProdLocallyUniformlyOn f g s :=
  h.tendstoLocallyUniformlyOn

@[to_additive]
theorem MultipliableLocallyUniformly.multipliableLocallyUniformlyOn
    (h : MultipliableLocallyUniformly f) :
    MultipliableLocallyUniformlyOn f s :=
  h.exists.choose_spec.hasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn

/-- If every `x` has a neighbourhood on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x` has a neighbourhood on which `b ↦ ∑' i, f i b`
converges uniformly to `g`, then the sum converges locally uniformly. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/]
lemma hasProdLocallyUniformly_of_of_forall_exists_nhds
    (h : ∀ x, ∃ t ∈ 𝓝 x, HasProdUniformlyOn f g t) : HasProdLocallyUniformly f g :=
  tendstoLocallyUniformly_of_forall_exists_nhds <| by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
lemma HasProdUniformly.hasProdLocallyUniformly (h : HasProdUniformly f g) :
    HasProdLocallyUniformly f g := by
  simp only [hasProdUniformly_iff_tendstoUniformly, HasProdLocallyUniformly] at *
  exact TendstoUniformly.tendstoLocallyUniformly h

@[to_additive]
lemma hasProdLocallyUniformly_of_forall_compact [LocallyCompactSpace β]
    (h : ∀ K, IsCompact K → HasProdUniformlyOn f g K) : HasProdLocallyUniformly f g := by
  rw [HasProdLocallyUniformly, tendstoLocallyUniformly_iff_forall_isCompact]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
lemma multipliableLocallyUniformly_of_of_forall_exists_nhds
    (h : ∀ x, ∃ t ∈ 𝓝 x, MultipliableUniformlyOn f t) :
    MultipliableLocallyUniformly f :=
  hasProdLocallyUniformly_of_of_forall_exists_nhds
    (fun x => (h x).imp fun _ ht => ⟨ht.1, ht.2.hasProdUniformlyOn⟩)
    |>.multipliableLocallyUniformly

@[to_additive]
theorem HasProdLocallyUniformly.hasProd (h : HasProdLocallyUniformly f g) : HasProd (f · x) (g x) :=
  h.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ x)

@[to_additive]
theorem MultipliableLocallyUniformly.multipliable
    (h : MultipliableLocallyUniformly f) : Multipliable (f · x) :=
  h.choose_spec.hasProd.multipliable

@[to_additive]
theorem MultipliableLocallyUniformly.hasProdLocallyUniformly
    (h : MultipliableLocallyUniformly f) :
    HasProdLocallyUniformly f (∏' i, f i ·) :=
  h.elim fun _ hg => hg.congr_inseparable_right fun _ =>
    tendsto_nhds_unique_inseparable hg.hasProd hg.hasProd.multipliable.hasProd

@[to_additive]
theorem multipliableLocallyUniformly_iff_hasProdLocallyUniformly :
    MultipliableLocallyUniformly f ↔ HasProdLocallyUniformly f (∏' i, f i ·) :=
  ⟨MultipliableLocallyUniformly.hasProdLocallyUniformly,
    HasProdLocallyUniformly.multipliableLocallyUniformly⟩

@[to_additive]
lemma HasProdLocallyUniformly.tendstoLocallyUniformly_finsetRange
    {f : ℕ → β → α} (h : HasProdLocallyUniformly f g) :
    TendstoLocallyUniformly (∏ i ∈ Finset.range ·, f i ·) g atTop := by
  simpa only [tendstoLocallyUniformlyOn_univ] using
    (h.hasProdLocallyUniformlyOn (s := .univ)).tendstoLocallyUniformlyOn_finsetRange

end LocallyUniformly
