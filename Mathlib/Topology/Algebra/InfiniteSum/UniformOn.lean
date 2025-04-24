/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic

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

variable {α β ι : Type*} [CommMonoid α]  {f : ι → β → α} {g : β → α} {𝔖 : Set (Set β)}
  {x : β} {s : Set β} {I : Finset ι}

section prelim

variable (F I) in
@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_prod : ∏ i ∈ I, ofFun 𝔖 (f i) = ofFun 𝔖 (∏ i ∈ I, f i) :=
  rfl

end prelim

variable [UniformSpace α]

section UniformlyOn

variable (f g 𝔖)

/-- `HasProdUniformlyOn f g 𝔖` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges uniformly on `s ∈ 𝔖` to `g`. -/
@[to_additive "`HasSumUniformlyOn f g 𝔖` means that the (potentially infinite) sum `∑' i, f i b`
for `b : β` converges uniformly on `s ∈ 𝔖` to `g`."]
def HasProdUniformlyOn : Prop :=
  HasProd (fun i ↦ UniformOnFun.ofFun 𝔖 (f i)) (UniformOnFun.ofFun 𝔖 g)

/-- `MultipliableUniformlyOn f 𝔖` means that `f` converges uniformly on `s` to some infinite
product. -/
@[to_additive "`SummableUniformlyOn f s` means that `f` converges uniformly on `s` to some
infinite sum."]
def MultipliableUniformlyOn (f : ι → β → α) (𝔖 : Set (Set β)) : Prop :=
  ∃ g, HasProdUniformlyOn f g 𝔖

variable {f g 𝔖}

@[to_additive]
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g 𝔖) :
    MultipliableUniformlyOn f 𝔖 := ⟨g, h⟩

@[to_additive]
lemma hasProdUniformlyOn_iff_tendstoUniformlyOn : HasProdUniformlyOn f g 𝔖 ↔
    ∀ s ∈ 𝔖, TendstoUniformlyOn (fun (I : Finset ι) b ↦ ∏ i ∈ I, f i b) g atTop s := by
  simpa [HasProdUniformlyOn, HasProd, UniformOnFun.ofFun_prod, Finset.prod_fn] using
    UniformOnFun.tendsto_iff_tendstoUniformlyOn

@[to_additive]
theorem HasProdUniformlyOn.hasProd (h : HasProdUniformlyOn f g 𝔖) (hs : s ∈ 𝔖) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  (hasProdUniformlyOn_iff_tendstoUniformlyOn.mp h s hs).tendsto_at hx

@[to_additive]
theorem HasProdUniformlyOn.tprod_eqOn [T2Space α] (h : HasProdUniformlyOn f g 𝔖) (hs : s ∈ 𝔖) :
    s.EqOn (∏' b, f b ·) g :=
  fun _ hx ↦ (h.hasProd hs hx).tprod_eq

@[to_additive]
theorem MultipliableUniformlyOn.multipliable (h : MultipliableUniformlyOn f 𝔖)
    (hs : s ∈ 𝔖) (hx : x ∈ s) : Multipliable (f · x) :=
  match h with | ⟨_, hg⟩ => (hg.hasProd hs hx).multipliable

end UniformlyOn

section LocallyUniformlyOn

variable (f g s) [TopologicalSpace β]

/-- `HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly on `s` to `g b`. -/
@[to_additive "`HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly on `s` to `g b`."]
def HasProdLocallyUniformlyOn : Prop := ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g {t}

/-- `MultipliableLocallyUniformlyOn f s` means that the product `∏' i, f i b` converges locally
uniformly on `s` to something. -/
@[to_additive "`SummableUniformlyOn f s` means that `∑' i, f i b` converges locally uniformly on
`s` to something."]
def MultipliableLocallyUniformlyOn : Prop := ∃ g, HasProdLocallyUniformlyOn f g s

variable {f g s}

@[to_additive]
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s :=
  ⟨g, h⟩

@[to_additive]
theorem HasProdLocallyUniformlyOn.hasProd (h : HasProdLocallyUniformlyOn f g s) (hx : x ∈ s) :
    HasProd (f · x) (g x) :=
  match h x hx with | ⟨_, ht, hft⟩ => hft.hasProd rfl (mem_of_mem_nhdsWithin hx ht)

@[to_additive]
theorem MultipliableLocallyUniformlyOn.multipliable
    (h : MultipliableLocallyUniformlyOn f s) (hx : x ∈ s) : Multipliable (f · x) :=
  match h with | ⟨_, hg⟩ => (hg.hasProd hx).multipliable

@[to_additive]
theorem HasProdLocallyUniformlyOn.tprod_eqOn [T2Space α]
    (h : HasProdLocallyUniformlyOn f g s) : Set.EqOn (∏' i, f i ·) g s :=
  fun _ hx ↦ (h.hasProd hx).tprod_eq

lemma tendstoLocallyUniformlyOn_of_forall_exists_nhd
    {ι α β : Type*} [UniformSpace α] [TopologicalSpace β] {f : ι → β → α} {g : β → α}
    {l : Filter ι} {s : Set β} (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, TendstoUniformlyOn f g l t) :
    TendstoLocallyUniformlyOn f g l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  obtain ⟨t, ht, htr⟩ := h x hx
  simp only [tendstoUniformlyOn_iff_tendsto] at htr
  exact htr.mono_left (prod_mono_right _ (le_principal_iff.mpr ht))

@[to_additive]
lemma HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn
    (h : HasProdLocallyUniformlyOn f g s) :
    TendstoLocallyUniformlyOn (fun (I : Finset ι) b ↦ ∏ i ∈ I, f i b) g atTop s := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhd
  simpa [HasProdLocallyUniformlyOn, hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn [LocallyCompactSpace β]
    (hs : IsOpen s) : HasProdLocallyUniformlyOn f g s ↔
    TendstoLocallyUniformlyOn (fun (I : Finset ι) b ↦ ∏ i ∈ I, f i b) g atTop s := by
  simp [(tendstoLocallyUniformlyOn_TFAE _ g _ hs).out 0 2, HasProdLocallyUniformlyOn,
    hasProdUniformlyOn_iff_tendstoUniformlyOn]

end LocallyUniformlyOn

open Complex

/- This is just a test of the defns -/
theorem derivWithin_tsum {α : Type*} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    (hf : ∀ y ∈ s, Summable fun n : α ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z ↦ ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z ↦ f n z) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (IsOpen.uniqueDiffWithinAt hs hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ Summable.hasSum (hf y hy)) hx
  · exact fun n a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a
  · obtain ⟨g, hg⟩ := h
    apply hg.tendstoLocallyUniformlyOn.congr_right
    intro b hb
    have hB := HasSumLocallyUniformlyOn.tsum_eqOn hg hb
    apply hB.symm
  · filter_upwards
    intro t r hr
    apply HasDerivAt.sum
    intro q hq
    apply HasDerivWithinAt.hasDerivAt
    · apply DifferentiableWithinAt.hasDerivWithinAt
      apply (hf2 q r hr).differentiableWithinAt
    · exact IsOpen.mem_nhds hs hr
