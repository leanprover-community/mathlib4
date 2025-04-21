/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Topology.Algebra.UniformConvergence


/-!
# Infinite sum and products that converge uniformly on a set

This file defines the notion of uniform convergence of infinite sums and products on a set
`s : Set β`. It also defines the notion of local uniform convergence of infinite sums and products
on a set.

-/

noncomputable section

open Filter Function

open scoped Topology

variable {α β ι : Type*}

section HasProdUniformlyOn

variable [CommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}

@[simp]
lemma ofFun_prod (f : ι → β → α) (g : β → α) (s : Set β) (i : Finset ι) :
    ∏ b ∈ i, (UniformOnFun.ofFun {s}) (f b) = (UniformOnFun.ofFun {s}) (∏ b ∈ i, f b) := rfl

variable [UniformSpace α]

/-- `HasProdUniformlyOn f g` means that the (potentially infinite) product of the `f b` for `b : β`
converges uniformly on `s` to `g`. -/
@[to_additive]
def HasProdUniformlyOn (f : ι → β → α) (g : β → α) (s : Set β) : Prop :=
  HasProd (fun i ↦ UniformOnFun.ofFun {s} (f i)) (UniformOnFun.ofFun {s} g)

/-- `HasProdLocallyUniformlyOn f g` means that the (potentially infinite) product of
the `f b` for `b : β` converges locally uniformly on `s` to `g`. -/
@[to_additive]
def HasProdLocallyUniformlyOn (f : ι → β → α) (g : β → α) (s : Set β) [TopologicalSpace β] : Prop :=
  ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, HasProdUniformlyOn f g t

/-- `MultipliableUniformlyOn f` means that `f` converges uniformly on `s` to some infinite product.
Use `tprodUniformlyOn` to get the value. -/
@[to_additive "`SummableUniformlyOn f` means that `f` converges uniformly on `s` to some
infinite product. Use `tsumUniformlyOn` to get the value."]
def MultipliableUniformlyOn (f : ι → β → α) (s : Set β) : Prop :=
  ∃ g, HasProdUniformlyOn f g s

/-- `MultipliableLOcallyUniformlyOn f` means that `f` converges locally uniformly on `s` to some
infinite product. Use `tprodUniformlyOn` to get the value. -/
@[to_additive "`SummableUniformlyOn f` means that `f` converges uniformly on `s` to some
infinite product. Use `tsumUniformlyOn` to get the value."]
def MultipliableLocallyUniformlyOn (f : ι → β → α) (s : Set β) [TopologicalSpace β] : Prop :=
  ∃ g, HasProdLocallyUniformlyOn f g s

open scoped Classical in
/-- `∏ᵘ i, f i` is the product of `f` if it exists and is unconditionally uniformly convergent on
a set `s`, or 1 otherwise. -/
@[to_additive "`∑ᵘ i, f i` is the sum of `f` if it exists and is unconditionally uniformly
convergent on a set `s`, or 0 otherwise."]
noncomputable irreducible_def tprodUniformlyOn (f : ι → β → α) (s : Set β) :=
  if h : MultipliableUniformlyOn f s then
  /- Note that the product might not be uniquely defined if the topology is not separated.
  When the multiplicative support of `f` is finite, we make the most reasonable choice to use the
  product over the multiplicative support. Otherwise, we choose arbitrarily an `a` satisfying
  `HasProdUniformlyOn f g s`. -/
    if (mulSupport f).Finite then finprod f
    else h.choose
  else 1

open scoped Classical in
/-- `∏ˡᵘ i, f i` is the product of `f` if it exists and is unconditionally uniformly convergent on
a set `s`, or 1 otherwise. -/
@[to_additive "`∑ˡᵘ i, f i` is the sum of `f` if it exists and is unconditionally uniformly
convergent on a set `s`, or 0 otherwise."]
noncomputable irreducible_def tprodLocallyUniformlyOn (f : ι → β → α) (s : Set β)
  [TopologicalSpace β] :=
  if h : MultipliableLocallyUniformlyOn f s then
  /- Note that the product might not be uniquely defined if the topology is not separated.
  When the multiplicative support of `f` is finite, we make the most reasonable choice to use the
  product over the multiplicative support. Otherwise, we choose arbitrarily an `a` satisfying
  `HasProdLocallyUniformlyOn f g s`. -/
    if (mulSupport f).Finite then finprod f
    else h.choose
  else 1

@[inherit_doc tprodUniformlyOn]
notation3 "∏ᵘ["s"] "(...)", "r:67:(scoped f => tprodUniformlyOn f s) => r
@[inherit_doc tsumUniformlyOn]
notation3 "∑ᵘ["s"] "(...)", "r:67:(scoped f => tsumUniformlyOn f s) => r
@[inherit_doc tprodUniformlyOn]
notation3 "∏ˡᵘ["s"] "(...)", "r:67:(scoped f => tprodLocallyUniformlyOn f s) => r
@[inherit_doc tsumUniformlyOn]
notation3 "∑ˡᵘ["s"] "(...)", "r:67:(scoped f => tsumLocallyUniformlyOn f s) => r

@[to_additive]
theorem HasProdUniformlyOn.multipliable (h : HasProdUniformlyOn f g s) :
    Multipliable (fun i ↦ UniformOnFun.ofFun {s} (f i)) :=
  ⟨(UniformOnFun.ofFun {s} g), h⟩

@[to_additive]
theorem HasProdLocallyUniformlyOn.multipliable [TopologicalSpace β]
    (h : HasProdLocallyUniformlyOn f g s) :
    ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, Multipliable (fun i ↦ UniformOnFun.ofFun {t} (f i)) := by
  intro x hx
  obtain ⟨t, ht, htr⟩ := h x hx
  refine ⟨t, ht, ⟨(UniformOnFun.ofFun {t} g), htr⟩⟩

@[to_additive]
theorem HasProdUniformlyOn.multipliableUniformlyOn (h : HasProdUniformlyOn f g s) :
    MultipliableUniformlyOn f s := ⟨g, h⟩

@[to_additive]
theorem HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn [TopologicalSpace β]
    (h : HasProdLocallyUniformlyOn f g s) : MultipliableLocallyUniformlyOn f s := ⟨g, h⟩

@[to_additive]
theorem tprodUniformlyOn_eq_one_of_not_multipliableUniformlyOn (h : ¬MultipliableUniformlyOn f s) :
    ∏ᵘ[s] b, f b = 1 := by
  simp [tprodUniformlyOn_def, h]

@[to_additive]
theorem tprodLocallyUniformlyOn_eq_one_of_not_multipliableLocallyUniformlyOn [TopologicalSpace β]
    (h : ¬MultipliableLocallyUniformlyOn f s) :∏ˡᵘ[s] b, f b = 1 := by
  simp [tprodLocallyUniformlyOn_def, h]

@[to_additive]
lemma HasProdUniformlyOn_iff_TendstoUniformlyOn : HasProdUniformlyOn f g s ↔
    TendstoUniformlyOn (fun (s : Finset ι) b ↦ ∏ i ∈ s, f i b) g atTop s := by
  rw [HasProdUniformlyOn, HasProd] at *
  have H := UniformOnFun.tendsto_iff_tendstoUniformlyOn
    (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun {s}) (f b)))
    (f:= (UniformOnFun.ofFun {s} g)) (p := atTop)
  simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, forall_eq] at H
  convert H
  simp

@[to_additive]
lemma HasProdLocallyUniformlyOn.TendstoLocallyUniformlyOn [TopologicalSpace β]
   (h : HasProdLocallyUniformlyOn f g s) :
   TendstoLocallyUniformlyOn (fun (s : Finset ι) b ↦ ∏ i ∈ s, f i b) g atTop s := by
  simp_rw [HasProdLocallyUniformlyOn, HasProdUniformlyOn, HasProd,
    tendstoLocallyUniformlyOn_iff_forall_tendsto] at *
  intro x hx
  obtain ⟨t, ht, htr⟩ := h x hx
  have H := UniformOnFun.tendsto_iff_tendstoUniformlyOn
        (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun {t}) (f b)))
          (f:= (UniformOnFun.ofFun {t} g)) (p := atTop)
  simp only [ofFun_prod, Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, forall_eq] at *
  rw [H, tendstoUniformlyOn_iff_tendsto] at htr
  simp only [comp_apply, UniformOnFun.toFun_ofFun, Finset.prod_apply] at *
  apply htr.mono_left (prod_mono (fun ⦃U⦄ a ↦ a) (le_principal_iff.mpr ht))

@[to_additive]
lemma HasProdLocallyUniformlyOn_iff_TendstoLocallyUniformlyOn [TopologicalSpace β]
    [LocallyCompactSpace β] (hs : IsOpen s) : HasProdLocallyUniformlyOn f g s ↔
    TendstoLocallyUniformlyOn (fun (s : Finset ι) b ↦ ∏ i ∈ s, f i b) g atTop s := by
  refine ⟨fun h ↦ HasProdLocallyUniformlyOn.TendstoLocallyUniformlyOn h, ?_⟩
  simp_rw [HasProdLocallyUniformlyOn, HasProdUniformlyOn, HasProd] at *
  have H := (tendstoLocallyUniformlyOn_TFAE (fun s b ↦ ∏ i ∈ s, f i b) g atTop hs).out 2 0
  rw [← H]
  intro h x hx
  obtain ⟨r, hr, htr⟩ := h x hx
  refine ⟨r, hr, ?_ ⟩
  have H2 := UniformOnFun.tendsto_iff_tendstoUniformlyOn
      (F := (fun s_1 ↦ ∏ b ∈ s_1, (UniformOnFun.ofFun {r}) (f b)))
        (f:= (UniformOnFun.ofFun {r} g)) (p := atTop)
  simp only [ofFun_prod, Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, forall_eq] at *
  rw [H2]
  apply htr.congr
  filter_upwards with v x hx
  simp

end HasProdUniformlyOn
