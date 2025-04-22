/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Topology.Sets.Compacts
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Infinite sum and products that converge uniformly on a set

This file defines the notion of uniform convergence of infinite sums and products of functions
on a family of sets of `β`.
It also defines the notion of local uniform convergence of infinite sums and products of functions
on a set.

-/

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*}

section HasProdUniformlyOn

variable [CommMonoid α] {𝔖 : Set (Set β)}

@[to_additive, simp]
lemma UniformOnFun.ofFun_prod (f : ι → β → α) (i : Finset ι) :
    ∏ b ∈ i, (UniformOnFun.ofFun 𝔖) (f b) = (UniformOnFun.ofFun 𝔖) (∏ b ∈ i, f b) := rfl

variable  {f : ι → β → α} {g : β → α}

variable [UniformSpace α]

/-- `HasProdUniformlyOn f g 𝔖` means that the (potentially infinite) product `∏' i, f i b`
for `b : β` converges uniformly on `s ∈ 𝔖` to `g`. -/
@[to_additive "`HasSumUniformlyOn f g 𝔖` means that the (potentially infinite) sum `∑' i, f i b`
for `b : β` converges uniformly on `s ∈ 𝔖` to `g`."]
def HasProdUniformlyOn (f : ι → β → α) (g : β → α) (𝔖 : Set (Set β)) : Prop :=
  HasProd (fun i ↦ UniformOnFun.ofFun 𝔖 (f i)) (UniformOnFun.ofFun 𝔖 g)

/-- `HasProdLocallyUniformlyOn f g` means that the (potentially infinite) product
the `∏' i, f i b` for `b : β` converges locally uniformly on `s` to `g b`. -/
@[to_additive "`HasProdLocallyUniformlyOn f g` means that the (potentially infinite) sum
the `∑' i, f i b` for `b : β` converges locally uniformly on `s` to `g b`."]
def HasProdLocallyUniformlyOn (f : ι → β → α) (g : β → α) (s : Set β) [TopologicalSpace β] : Prop :=
  ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g {t}

/-- `MultipliableUniformlyOn f 𝔖` means that `f` converges uniformly on `s` to some infinite
product. -/
@[to_additive "`SummableUniformlyOn f s` means that `f` converges uniformly on `s` to some
infinite sum."]
def MultipliableUniformlyOn (f : ι → β → α) (𝔖 : Set (Set β)) : Prop :=
  ∃ g, HasProdUniformlyOn f g 𝔖

/-- `MultipliableLocallyUniformlyOn f s` means that `f` converges locally uniformly on `s` to some
infinite product. -/
@[to_additive "`SummableUniformlyOn f s` means that `f` converges locally uniformly on `s` to some
infinite sum. "]
def MultipliableLocallyUniformlyOn (f : ι → β → α) (s : Set β) [TopologicalSpace β] : Prop :=
  ∃ g, HasProdLocallyUniformlyOn f g s

@[to_additive]
theorem HasProdUniformlyOn.multipliable (h : HasProdUniformlyOn f g 𝔖) :
    Multipliable (fun i ↦ UniformOnFun.ofFun 𝔖 (f i)) :=
  ⟨(UniformOnFun.ofFun 𝔖 g), h⟩

@[to_additive]
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g 𝔖) :
    MultipliableUniformlyOn f 𝔖 := ⟨g, h⟩

@[to_additive]
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn [TopologicalSpace β] (s : Set β)
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s := ⟨g, h⟩

@[to_additive]
lemma hasProdUniformlyOn_iff_tendstoUniformlyOn  : HasProdUniformlyOn f g 𝔖 ↔
    ∀ s ∈ 𝔖, TendstoUniformlyOn (fun (s : Finset ι) b ↦ ∏ i ∈ s, f i b) g atTop s := by
  rw [HasProdUniformlyOn, HasProd] at *
  have H := UniformOnFun.tendsto_iff_tendstoUniformlyOn
    (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun 𝔖) (f b)))
    (f:= (UniformOnFun.ofFun 𝔖 g)) (p := atTop)
  simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, forall_eq] at H
  convert H
  simp

@[to_additive]
theorem HasProdUniformlyOn.tprod_eqOn [T2Space α]
  (h : HasProdUniformlyOn f g 𝔖) : ∀ s ∈ 𝔖, Set.EqOn (fun x ↦ ∏' b, f b x) g s := by
  intro s hs x hx
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at h
  apply HasProd.tprod_eq
  apply (h s hs).tendsto_at hx

@[to_additive]
theorem HasProdUniformlyOn.pointwise_multipliable
  (h : HasProdUniformlyOn f g 𝔖) : ∀ s ∈ 𝔖, ∀ x ∈ s, Multipliable (fun i ↦ f i x) := by
  intro s hs x hx
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at h
  apply HasProd.multipliable (a := g x)
  exact (h s hs).tendsto_at hx

@[to_additive]
theorem MultipliableUniformlyOn.pointwise_multipliable
  (h : MultipliableUniformlyOn f 𝔖) : ∀ s ∈ 𝔖, ∀ x ∈ s, Multipliable (fun i ↦ f i x) := by
  obtain ⟨g, hg⟩ := h
  apply hg.pointwise_multipliable

@[to_additive]
lemma HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn [TopologicalSpace β] (s : Set β)
   (h : HasProdLocallyUniformlyOn f g s) :
   TendstoLocallyUniformlyOn (fun (v : Finset ι) b ↦ ∏ i ∈ v, f i b) g atTop s := by
  simp_rw [HasProdLocallyUniformlyOn, HasProdUniformlyOn, HasProd,
    tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  obtain ⟨t, ht, htr⟩ := h x hx
  have H := UniformOnFun.tendsto_iff_tendstoUniformlyOn
        (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun {t}) (f b)))
          (f:= (UniformOnFun.ofFun {t} g)) (p := atTop)
  simp only [UniformOnFun.ofFun_prod, Set.mem_singleton_iff, UniformOnFun.toFun_ofFun,
    forall_eq] at *
  rw [H, tendstoUniformlyOn_iff_tendsto] at htr
  simp only [comp_apply, UniformOnFun.toFun_ofFun, Finset.prod_apply] at *
  apply htr.mono_left (prod_mono (fun ⦃U⦄ a ↦ a) (le_principal_iff.mpr ht))

@[to_additive]
lemma hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn [TopologicalSpace β] {s : Set β}
    [LocallyCompactSpace β] (hs : IsOpen s) : HasProdLocallyUniformlyOn f g s ↔
    TendstoLocallyUniformlyOn (fun (v : Finset ι) b ↦ ∏ i ∈ v, f i b) g atTop s := by
  refine ⟨fun h ↦ HasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn s h, ?_⟩
  simp_rw [HasProdLocallyUniformlyOn, HasProdUniformlyOn, HasProd] at *
  have H := (tendstoLocallyUniformlyOn_TFAE (fun s b ↦ ∏ i ∈ s, f i b) g atTop hs).out 2 0
  rw [← H]
  intro h x hx
  obtain ⟨r, hr, htr⟩ := h x hx
  refine ⟨r, hr, ?_ ⟩
  have H2 := UniformOnFun.tendsto_iff_tendstoUniformlyOn
      (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun {r}) (f b)))
        (f:= (UniformOnFun.ofFun {r} g)) (p := atTop)
  simp only [UniformOnFun.ofFun_prod, Set.mem_singleton_iff, UniformOnFun.toFun_ofFun,
    forall_eq] at *
  rw [H2]
  apply htr.congr
  filter_upwards with v x hx
  simp

@[to_additive]
theorem HasProdLocallyUniformlyOn.pointwise_multipliable [TopologicalSpace β]
    [LocallyCompactSpace β] {s : Set β} (hs : IsOpen s) (h : HasProdLocallyUniformlyOn f g s) :
    ∀ x ∈ s, Multipliable (fun i ↦ f i x) := by
  intro x hx
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn hs] at h
  apply HasProd.multipliable (a := g x)
  exact h.tendsto_at hx

@[to_additive]
theorem MultipliableLocallyUniformlyOn.pointwise_multipliable [TopologicalSpace β]
    [LocallyCompactSpace β] {s : Set β} (hs : IsOpen s) (h : MultipliableLocallyUniformlyOn f s) :
    ∀ x ∈ s, Multipliable (fun i ↦ f i x) := by
  obtain ⟨g, hg⟩ := h
  apply hg.pointwise_multipliable hs

@[to_additive]
theorem HasProdLocallyUniformlyOn.tprod_eqOn [T2Space α]
    [TopologicalSpace β] [LocallyCompactSpace β] {s : Set β} (hs : IsOpen s)
    (h : HasProdLocallyUniformlyOn f g s) : Set.EqOn (fun x ↦ ∏' b, f b x) g s := by
  intro x hx
  rw [hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn hs] at h
  apply HasProd.tprod_eq
  exact h.tendsto_at hx

open Complex

/-This is just a test of the defns -/
theorem derivWithin_tsum {α : Type*} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) {x : ℂ} (hx : x ∈ s)
    (hf : ∀ y ∈ s, Summable fun n : α ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z ↦ ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z ↦ f n z) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (IsOpen.uniqueDiffWithinAt hs hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ Summable.hasSum (hf y hy)) hx
  · use fun n : Finset α ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a
  · obtain ⟨g, hg⟩ := h
    have ho := hg
    rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn hs] at hg
    apply hg.congr_right
    intro b hb
    have hB := HasSumLocallyUniformlyOn.tsum_eqOn hs ho hb
    apply hB.symm
  · filter_upwards
    intro t r hr
    apply HasDerivAt.sum
    intro q hq
    apply HasDerivWithinAt.hasDerivAt
    · apply DifferentiableWithinAt.hasDerivWithinAt
      apply (hf2 q r hr).differentiableWithinAt
    · exact IsOpen.mem_nhds hs hr

end HasProdUniformlyOn
