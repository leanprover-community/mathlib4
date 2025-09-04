/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Infinite sum and products that converge uniformly on a set

This file defines the notion of uniform convergence of infinite sums and products of functions,
on a given family of subsets of their domain.

It also defines the notion of local uniform convergence of infinite sums and products of functions
on a set.
-/

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*} [CommMonoid α] {f : ι → β → α} {g : β → α} {𝔖 : Set (Set β)}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α]

/-!
## Uniform convergence of sums and products
-/

section UniformlyOn

variable (f g 𝔖) in
/-- `HasProdUniformlyOn f g 𝔖` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges uniformly on each `s ∈ 𝔖` to `g`. -/
@[to_additive /-- `HasSumUniformlyOn f g 𝔖` means that the (potentially infinite) sum `∑' i, f i b`
for `b : β` converges uniformly on each `s ∈ 𝔖` to `g`. -/]
def HasProdUniformlyOn : Prop :=
  HasProd (fun i ↦ UniformOnFun.ofFun 𝔖 (f i)) (UniformOnFun.ofFun 𝔖 g)

variable (f g 𝔖) in
/-- `MultipliableUniformlyOn f 𝔖` means that there is some infinite product to which
`f` converges uniformly on every `s ∈ 𝔖`. Use `fun x ↦ ∏' i, f i x` to get the product function. -/
@[to_additive /-- `SummableUniformlyOn f s` means that there is some infinite sum to
which `f` converges uniformly on every `s ∈ 𝔖`. Use fun x ↦ ∑' i, f i x to get the sum function. -/]
def MultipliableUniformlyOn : Prop :=
  Multipliable (fun i ↦ UniformOnFun.ofFun 𝔖 (f i))

@[to_additive]
lemma MultipliableUniformlyOn.exists (h : MultipliableUniformlyOn f 𝔖) :
    ∃ g, HasProdUniformlyOn f g 𝔖 :=
  h

@[to_additive]
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g 𝔖) :
    MultipliableUniformlyOn f 𝔖 :=
  ⟨g, h⟩

@[to_additive]
lemma hasProdUniformlyOn_iff_tendstoUniformlyOn : HasProdUniformlyOn f g 𝔖 ↔
    ∀ s ∈ 𝔖, TendstoUniformlyOn (fun I b ↦ ∏ i ∈ I, f i b) g atTop s := by
  simpa [HasProdUniformlyOn, HasProd, ← UniformOnFun.ofFun_prod, Finset.prod_fn] using
    UniformOnFun.tendsto_iff_tendstoUniformlyOn

@[to_additive]
lemma HasProdUniformlyOn.congr {f' : ι → β → α}
    (h : HasProdUniformlyOn f g 𝔖)
    (hff' : ∀ s ∈ 𝔖, ∀ᶠ (n : Finset ι) in atTop,
      Set.EqOn (fun b ↦ ∏ i ∈ n, f i b) (fun b ↦ ∏ i ∈ n, f' i b) s) :
    HasProdUniformlyOn f' g 𝔖 := by
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at *
  exact fun s hs ↦ TendstoUniformlyOn.congr (h s hs) (hff' s hs)

@[to_additive]
lemma HasProdUniformlyOn.congr_right {g' : β → α}
    (h : HasProdUniformlyOn f g 𝔖) (hgg' : ∀ s ∈ 𝔖, Set.EqOn g g' s) :
    HasProdUniformlyOn f g' 𝔖 := by
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at *
  exact fun s hs ↦ TendstoUniformlyOn.congr_right (h s hs) (hgg' s hs)

@[to_additive]
lemma HasProdUniformlyOn.tendstoUniformlyOn_finsetRange
    {f : ℕ → β → α} (h : HasProdUniformlyOn f g 𝔖) (hs : s ∈ 𝔖) :
    TendstoUniformlyOn (fun N b ↦ ∏ i ∈ Finset.range N, f i b) g atTop s := by
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at h
  exact fun v hv => Filter.tendsto_finset_range.eventually (h s hs v hv)

@[to_additive]
theorem HasProdUniformlyOn.hasProd (h : HasProdUniformlyOn f g 𝔖) (hs : s ∈ 𝔖) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  (hasProdUniformlyOn_iff_tendstoUniformlyOn.mp h s hs).tendsto_at hx

@[to_additive]
theorem HasProdUniformlyOn.tprod_eqOn [T2Space α] (h : HasProdUniformlyOn f g 𝔖) (hs : s ∈ 𝔖) :
    s.EqOn (∏' b, f b ·) g :=
  fun _ hx ↦ (h.hasProd hs hx).tprod_eq

@[to_additive]
theorem HasProdUniformlyOn.tprod_eq [T2Space α] (h : HasProdUniformlyOn f g 𝔖)
    (hs : ⋃₀ 𝔖 = Set.univ) : (∏' b, f b ·) = g := by
  ext x
  obtain ⟨s, hs, hx⟩ := by simpa [← hs] using Set.mem_univ x
  exact h.tprod_eqOn hs hx

@[to_additive]
theorem MultipliableUniformlyOn.multipliable (h : MultipliableUniformlyOn f 𝔖)
    (hs : s ∈ 𝔖) (hx : x ∈ s) : Multipliable (f · x) :=
  match h.exists with | ⟨_, hg⟩ => (hg.hasProd hs hx).multipliable

@[to_additive]
theorem MultipliableUniformlyOn.hasProdUniformlyOn [T2Space α] (h : MultipliableUniformlyOn f 𝔖) :
    HasProdUniformlyOn f (∏' i, f i ·) 𝔖 := by
  obtain ⟨g, hg⟩ := h.exists
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  intro s hs
  exact (hasProdUniformlyOn_iff_tendstoUniformlyOn.mp hg s hs).congr_right (hg.tprod_eqOn hs).symm

end UniformlyOn

section LocallyUniformlyOn
/-!
## Locally uniform convergence of sums and products
-/

variable [TopologicalSpace β]

variable (f g s) in
/-- `HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/
@[to_additive /-- `HasSumLocallyUniformlyOn f g s` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/]
def HasProdLocallyUniformlyOn : Prop :=
  TendstoLocallyUniformlyOn (fun I b ↦ ∏ i ∈ I, f i b) g atTop s

variable (f g s) in
/-- `MultipliableLocallyUniformlyOn f s` means that the product `∏' i, f i b` converges locally
uniformly on `s` to something. -/
@[to_additive /-- `SummableLocallyUniformlyOn f s` means that `∑' i, f i b` converges locally
uniformly on `s` to something. -/]
def MultipliableLocallyUniformlyOn : Prop := ∃ g, HasProdLocallyUniformlyOn f g s

@[to_additive]
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn :
    HasProdLocallyUniformlyOn f g s ↔
      TendstoLocallyUniformlyOn (fun I b ↦ ∏ i ∈ I, f i b) g atTop s :=
  Iff.rfl

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly on `s` to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly to `g`, then the sum converges locally uniformly. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/]
lemma hasProdLocallyUniformlyOn_of_of_forall_exists_nhds
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g {t}) : HasProdLocallyUniformlyOn f g s :=
  tendstoLocallyUniformlyOn_of_forall_exists_nhds <| by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
lemma HasProdUniformlyOn.hasProdLocallyUniformlyOn (h : HasProdUniformlyOn f g {s}) :
    HasProdLocallyUniformlyOn f g s := by
  simp [HasProdLocallyUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn] at *
  exact TendstoUniformlyOn.tendstoLocallyUniformlyOn h

@[to_additive]
lemma hasProdLocallyUniformlyOn_of_forall_compact (hs : IsOpen s) [LocallyCompactSpace β]
    (h : ∀ K ⊆ s, IsCompact K → HasProdUniformlyOn f g {K}) : HasProdLocallyUniformlyOn f g s := by
  rw [HasProdLocallyUniformlyOn, tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s :=
  ⟨g, h⟩

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly,
then the product converges locally uniformly on `s`. Note that this is not a tautology, and the
converse is only true if the domain is locally compact. -/
@[to_additive /-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b`
converges uniformly, then the sum converges locally uniformly. Note that this is not a tautology,
and the converse is only true if the domain is locally compact. -/]
lemma multipliableLocallyUniformlyOn_of_of_forall_exists_nhds [T2Space α]
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, MultipliableUniformlyOn f {t}) :
    MultipliableLocallyUniformlyOn f s :=
  (hasProdLocallyUniformlyOn_of_of_forall_exists_nhds <| fun x hx ↦ match h x hx with
  | ⟨t, ht, htr⟩ => ⟨t, ht, htr.hasProdUniformlyOn⟩).multipliableLocallyUniformlyOn

@[to_additive]
theorem HasProdLocallyUniformlyOn.hasProd (h : HasProdLocallyUniformlyOn f g s) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  h.tendsto_at hx

@[to_additive]
theorem MultipliableLocallyUniformlyOn.multipliable
    (h : MultipliableLocallyUniformlyOn f s) (hx : x ∈ s) : Multipliable (f · x) :=
  match h with | ⟨_, hg⟩ => (hg.hasProd hx).multipliable

@[to_additive]
theorem MultipliableLocallyUniformlyOn.hasProdLocallyUniformlyOn [T2Space α]
    (h : MultipliableLocallyUniformlyOn f s) :
    HasProdLocallyUniformlyOn f (∏' i, f i ·) s :=
  match h with | ⟨_, hg⟩ => hg.congr_right fun _ hb ↦ (hg.hasProd hb).tprod_eq.symm

@[to_additive]
theorem HasProdLocallyUniformlyOn.tprod_eqOn [T2Space α]
    (h : HasProdLocallyUniformlyOn f g s) : Set.EqOn (∏' i, f i ·) g s :=
  fun _ hx ↦ (h.hasProd hx).tprod_eq

@[to_additive]
lemma MultipliableLocallyUniformlyOn_congr [T2Space α]
    {f f' : ι → β → α} (h : ∀ i, s.EqOn (f i) (f' i))
    (h2 : MultipliableLocallyUniformlyOn f s) : MultipliableLocallyUniformlyOn f' s := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  exact (h2.hasProdLocallyUniformlyOn).congr fun v ↦ eqOn_fun_finsetProd h v

@[to_additive]
lemma HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
    {f : ℕ → β → α} (h : HasProdLocallyUniformlyOn f g s) :
    TendstoLocallyUniformlyOn (fun N b ↦ ∏ i ∈ Finset.range N, f i b) g atTop s := by
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn] at h
  intro v hv r hr
  obtain ⟨t, ht, htr⟩ := h v hv r hr
  exact ⟨t, ht, Filter.tendsto_finset_range.eventually htr⟩

end LocallyUniformlyOn
