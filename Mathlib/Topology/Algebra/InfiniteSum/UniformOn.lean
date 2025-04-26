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

-- XXX move this to `Topology.UniformSpace.UniformConvergenceTopology`
variable (F I) in
@[to_additive (attr := simp)]
lemma UniformOnFun.ofFun_prod : ∏ i ∈ I, ofFun 𝔖 (f i) = ofFun 𝔖 (∏ i ∈ I, f i) :=
  rfl

-- XXX move this to `Topology.UniformSpace.LocallyUniformConvergence`
/-- If every `x ∈ s` has a neighbourhood within `s` on which `f i` tends uniformly to `g`, then
`f i` tends locally uniformly on `s` to `g`.

Note this is **not** a tautology, since our definition of `TendstoLocallyUniformlyOn` is slightly
more general (although the conditions are equivalent if `β` is locally compact and `s` is open). -/
lemma tendstoLocallyUniformlyOn_of_forall_exists_nhd
    {ι α β : Type*} [UniformSpace α] [TopologicalSpace β] {f : ι → β → α} {g : β → α}
    {l : Filter ι} {s : Set β} (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, TendstoUniformlyOn f g l t) :
    TendstoLocallyUniformlyOn f g l s := by
  rw [tendstoLocallyUniformlyOn_iff_forall_tendsto]
  intro x hx
  obtain ⟨t, ht, htr⟩ := h x hx
  simp only [tendstoUniformlyOn_iff_tendsto] at htr
  exact htr.mono_left (prod_mono_right _ (le_principal_iff.mpr ht))

end prelim

variable [UniformSpace α]

/-!
## Uniform convergence of sums and products
-/

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
  Multipliable (fun i ↦ UniformOnFun.ofFun 𝔖 (f i))

variable {f g 𝔖}

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

variable (f g s) [TopologicalSpace β]

/-- `HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`). -/
@[to_additive "`HasProdLocallyUniformlyOn f g s` means that the (potentially infinite) sum
`∑' i, f i b` for `b : β` converges locally uniformly on `s` to `g b` (in the sense of
`TendstoLocallyUniformlyOn`)."]
def HasProdLocallyUniformlyOn : Prop :=
  TendstoLocallyUniformlyOn (fun I b ↦ ∏ i ∈ I, f i b) g atTop s

/-- `MultipliableLocallyUniformlyOn f s` means that the product `∏' i, f i b` converges locally
uniformly on `s` to something. -/
@[to_additive "`SummableUniformlyOn f s` means that `∑' i, f i b` converges locally uniformly on
`s` to something."]
def MultipliableLocallyUniformlyOn : Prop := ∃ g, HasProdLocallyUniformlyOn f g s

variable {f g s}

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly
to `g`, then the product converges locally uniformly on `s` to `g`. Note that this is not a
tautology, and the converse is only true if the domain is locally compact. -/
@[to_additive "If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b` converges
uniformly to `g`, then the product converges locally uniformly. Note that this is not a tautology,
and the converse is only true if the domain is locally compact."]
lemma hasProdLocallyUniformlyOn_of_of_forall_exists_nhd
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g {t}) : HasProdLocallyUniformlyOn f g s :=
  tendstoLocallyUniformlyOn_of_forall_exists_nhd <| by
    simpa [hasProdUniformlyOn_iff_tendstoUniformlyOn] using h

@[to_additive]
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn :
    HasProdLocallyUniformlyOn f g s ↔
      TendstoLocallyUniformlyOn (fun I b ↦ ∏ i ∈ I, f i b) g atTop s :=
  Iff.rfl

@[to_additive]
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s :=
  ⟨g, h⟩

/-- If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∏' i, f i b` converges uniformly,
then the product converges locally uniformly on `s`. Note that this is not a tautology, and the
converse is only true if the domain is locally compact. -/
@[to_additive "If every `x ∈ s` has a neighbourhood within `s` on which `b ↦ ∑' i, f i b` converges
uniformly, then the product converges locally uniformly. Note that this is not a tautology, and the
converse is only true if the domain is locally compact."]
lemma multipliableLocallyUniformlyOn_of_of_forall_exists_nhd [T2Space α]
    (h : ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, MultipliableUniformlyOn f {t}) :
    MultipliableLocallyUniformlyOn f s :=
  (hasProdLocallyUniformlyOn_of_of_forall_exists_nhd <| fun x hx ↦ match h x hx with
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
    apply hg.congr_right
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
