/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Bases.Finite

/-!
# Convergence of intervals

## Motivation

If a function tends to infinity somewhere, then its derivative is not integrable around this place.
One should be careful about this statement: "somewhere" could mean a point, but also convergence
from the left or from the right, or it could also be infinity, and "around this place" will refer
to these directed neighborhoods. Therefore, the above theorem has many variants. Instead of stating
all these variants, one can look for the common abstraction and have a single version. One has to
be careful: if one considers convergence along a sequence, then the function may tend to infinity
but have a derivative which is small along the sequence (with big jumps in between), so in the end
the derivative may be integrable on a neighborhood of the sequence. What really matters for such
calculus issues in terms of derivatives is that whole intervals are included in the sets we
consider.

The right common abstraction is provided in this file, as the `TendstoIxxClass` typeclass.
It takes as parameters a class of bounded intervals and two real filters `l₁` and `l₂`.
An instance `TendstoIxxClass Icc l₁ l₂` registers that, if `aₙ` and `bₙ` are converging towards
the filter `l₁`, then the intervals `Icc aₙ bₙ` are eventually contained in any given set
belonging to `l₂`. For instance, for `l₁ = 𝓝[>] x` and `l₂ = 𝓝[≥] x`, the strict and large right
neighborhoods of `x` respectively, then given any large right neighborhood `s ∈ 𝓝[≥] x` and any two
sequences `xₙ` and `yₙ` converging strictly to the right of `x`,
then the interval `[xₙ, yₙ]` is eventually contained in `s`. Therefore, the instance
`TendstoIxxClass Icc (𝓝[>] x) (𝓝[≥] x)` holds. Note that one could have taken as
well `l₂ = 𝓝[>] x`, but that `l₁ = 𝓝[≥] x` and `l₂ = 𝓝[>] x` wouldn't work.

With this formalism, the above theorem would read: if `TendstoIxxClass Icc l l` and `f` tends
to infinity along `l`, then its derivative is not integrable on any element of `l`.
Beyond this simple example, this typeclass plays a prominent role in generic formulations of
the fundamental theorem of calculus.

## Main definition

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.smallSets`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`. Here and below
`Ixx` is one of `Set.Icc`, `Set.Ico`, `Set.Ioc`, and `Set.Ioo`.
We define `Filter.TendstoIxxClass Ixx l₁ l₂` to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove
`Filter.TendstoIxxClass Set.Ico (𝓟 (Set.Iic a)) (𝓟 (Set.Iio a))`, i.e., if `u₁ n` and `u₂ n` belong
eventually to `Set.Iic a`, then the interval `Set.Ico (u₁ n) (u₂ n)` is eventually included in
`Set.Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `Mathlib/Topology/Algebra/Ordered`.

|     Input filter | `Ixx = Set.Icc`  | `Ixx = Set.Ico`  | `Ixx = Set.Ioc`  | `Ixx = Set.Ioo`  |
|-----------------:|:----------------:|:----------------:|:----------------:|:----------------:|
|   `Filter.atTop` | `Filter.atTop`   | `Filter.atTop`   | `Filter.atTop`   | `Filter.atTop`   |
|   `Filter.atBot` | `Filter.atBot`   | `Filter.atBot`   | `Filter.atBot`   | `Filter.atBot`   |
|         `pure a` | `pure a`         | `⊥`              | `⊥`              | `⊥`              |
|  `𝓟 (Set.Iic a)` | `𝓟 (Set.Iic a)`  | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iic a)`  | `𝓟 (Set.Iio a)`  |
|  `𝓟 (Set.Ici a)` | `𝓟 (Set.Ici a)`  | `𝓟 (Set.Ici a)`  | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  |
|  `𝓟 (Set.Ioi a)` | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  | `𝓟 (Set.Ioi a)`  |
|  `𝓟 (Set.Iio a)` | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iio a)`  | `𝓟 (Set.Iio a)`  |
|            `𝓝 a` | `𝓝 a`            | `𝓝 a`            | `𝓝 a`            | `𝓝 a`            |
| `𝓝[Set.Iic a] b` | `𝓝[Set.Iic a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iic a] b` | `𝓝[Set.Iio a] b` |
| `𝓝[Set.Ici a] b` | `𝓝[Set.Ici a] b` | `𝓝[Set.Ici a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` |
| `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` | `𝓝[Set.Ioi a] b` |
| `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` | `𝓝[Set.Iio a] b` |

-/

public section


variable {α β : Type*}

open Filter Set Function

namespace Filter

section Preorder

/-- A pair of filters `l₁`, `l₂` has `TendstoIxxClass Ixx` property if `Ixx a b` tends to
`l₂.small_sets` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `Set.Icc`, `Set.Ico`,
`Set.Ioc`, or `Set.Ioo`. The instances provide the best `l₂` for a given `l₁`. In many cases
`l₁ = l₂` but sometimes we can drop an endpoint from an interval: e.g., we prove
`TendstoIxxClass Set.Ico (𝓟 (Set.Iic a)) (𝓟 (Set.Iio a))`, i.e., if `u₁ n` and `u₂ n` belong
eventually to `Set.Iic a`, then the interval `Set.Ico (u₁ n) (u₂ n)` is eventually included in
`Set.Iio a`.

We mark `l₂` as an `outParam` so that Lean can automatically find an appropriate `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying explicitly `l₂`. -/
class TendstoIxxClass (Ixx : α → α → Set α) (l₁ : Filter α) (l₂ : outParam <| Filter α) : Prop where
  /-- `Function.uncurry Ixx` tends to `l₂.smallSets` along `l₁ ×ˢ l₁`. In other words, for any
  `s ∈ l₂` there exists `t ∈ l₁` such that `Ixx x y ⊆ s` whenever `x ∈ t` and `y ∈ t`.

  Use lemmas like `Filter.Tendsto.Icc` instead. -/
  tendsto_Ixx : Tendsto (fun p : α × α => Ixx p.1 p.2) (l₁ ×ˢ l₁) l₂.smallSets

theorem tendstoIxxClass_principal {s t : Set α} {Ixx : α → α → Set α} :
    TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ ∀ᵉ (x ∈ s) (y ∈ s), Ixx x y ⊆ t :=
  Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ <| by
    simp only [smallSets_principal, prod_principal_principal, tendsto_principal_principal,
      forall_prod_set, mem_powerset_iff]

theorem tendstoIxxClass_inf {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : TendstoIxxClass Ixx l₁ l₂]
    [h' : TendstoIxxClass Ixx l₁' l₂'] : TendstoIxxClass Ixx (l₁ ⊓ l₁') (l₂ ⊓ l₂') :=
  ⟨by simpa only [prod_inf_prod, smallSets_inf] using h.1.inf h'.1⟩

theorem tendstoIxxClass_of_subset {l₁ l₂ : Filter α} {Ixx Ixx' : α → α → Set α}
    (h : ∀ a b, Ixx a b ⊆ Ixx' a b) [h' : TendstoIxxClass Ixx' l₁ l₂] : TendstoIxxClass Ixx l₁ l₂ :=
  ⟨h'.1.smallSets_mono <| Eventually.of_forall <| Prod.forall.2 h⟩

theorem HasBasis.tendstoIxxClass {ι : Type*} {p : ι → Prop} {s} {l : Filter α}
    (hl : l.HasBasis p s) {Ixx : α → α → Set α}
    (H : ∀ i, p i → ∀ x ∈ s i, ∀ y ∈ s i, Ixx x y ⊆ s i) : TendstoIxxClass Ixx l l :=
  ⟨(hl.prod_self.tendsto_iff hl.smallSets).2 fun i hi => ⟨i, hi, fun _ h => H i hi _ h.1 _ h.2⟩⟩

variable [Preorder α]

protected theorem Tendsto.Icc {l₁ l₂ : Filter α} [TendstoIxxClass Icc l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Icc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Icc _ _ _).comp <| h₁.prodMk h₂

protected theorem Tendsto.Ioc {l₁ l₂ : Filter α} [TendstoIxxClass Ioc l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Ioc _ _ _).comp <| h₁.prodMk h₂

protected theorem Tendsto.Ico {l₁ l₂ : Filter α} [TendstoIxxClass Ico l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ico (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Ico _ _ _).comp <| h₁.prodMk h₂

protected theorem Tendsto.Ioo {l₁ l₂ : Filter α} [TendstoIxxClass Ioo l₁ l₂] {lb : Filter β}
    {u₁ u₂ : β → α} (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioo (u₁ x) (u₂ x)) lb l₂.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.Ioo _ _ _).comp <| h₁.prodMk h₂


instance tendsto_Icc_atTop_atTop : TendstoIxxClass Icc (atTop : Filter α) atTop :=
  (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
    Set.OrdConnected.out <| ordConnected_biInter fun _ _ => ordConnected_Ici

instance tendsto_Ico_atTop_atTop : TendstoIxxClass Ico (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_atTop_atTop : TendstoIxxClass Ioc (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_atTop_atTop : TendstoIxxClass Ioo (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

instance tendsto_Icc_atBot_atBot : TendstoIxxClass Icc (atBot : Filter α) atBot :=
  (hasBasis_iInf_principal_finite _).tendstoIxxClass fun _ _ =>
    Set.OrdConnected.out <| ordConnected_biInter fun _ _ => ordConnected_Iic

instance tendsto_Ico_atBot_atBot : TendstoIxxClass Ico (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_atBot_atBot : TendstoIxxClass Ioc (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_atBot_atBot : TendstoIxxClass Ioo (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self

instance OrdConnected.tendsto_Icc {s : Set α} [hs : OrdConnected s] :
    TendstoIxxClass Icc (𝓟 s) (𝓟 s) :=
  tendstoIxxClass_principal.2 hs.out

instance tendsto_Ico_Ici_Ici {a : α} : TendstoIxxClass Ico (𝓟 (Ici a)) (𝓟 (Ici a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ico_Ioi_Ioi {a : α} : TendstoIxxClass Ico (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ico_Iic_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_principal.2 fun _ _ _ h₁ _ h₂ => lt_of_lt_of_le h₂.2 h₁

instance tendsto_Ico_Iio_Iio {a : α} : TendstoIxxClass Ico (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self

instance tendsto_Ioc_Ici_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_principal.2 fun _ h₁ _ _ _ h₂ => lt_of_le_of_lt h₁ h₂.1

instance tendsto_Ioc_Iic_Iic {a : α} : TendstoIxxClass Ioc (𝓟 (Iic a)) (𝓟 (Iic a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioc_Iio_Iio {a : α} : TendstoIxxClass Ioc (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioc_Ioi_Ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

instance tendsto_Ioo_Ici_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Ioo_Iic_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ico_self

instance tendsto_Ioo_Ioi_Ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Ioo_Iio_Iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self

instance tendsto_Icc_Icc_Icc {a b : α} : TendstoIxxClass Icc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendstoIxxClass_principal.mpr fun _x hx _y hy => Icc_subset_Icc hx.1 hy.2

instance tendsto_Ioc_Icc_Icc {a b : α} : TendstoIxxClass Ioc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self

end Preorder

section PartialOrder

variable [PartialOrder α]

instance tendsto_Icc_pure_pure {a : α} : TendstoIxxClass Icc (pure a) (pure a : Filter α) := by
  rw [← principal_singleton]
  exact tendstoIxxClass_principal.2 ordConnected_singleton.out

instance tendsto_Ico_pure_bot {a : α} : TendstoIxxClass Ico (pure a) ⊥ :=
  ⟨by simp⟩

instance tendsto_Ioc_pure_bot {a : α} : TendstoIxxClass Ioc (pure a) ⊥ :=
  ⟨by simp⟩

instance tendsto_Ioo_pure_bot {a : α} : TendstoIxxClass Ioo (pure a) ⊥ :=
  ⟨by simp⟩

end PartialOrder

section LinearOrder

open Interval

variable [LinearOrder α]

instance tendsto_Icc_uIcc_uIcc {a b : α} : TendstoIxxClass Icc (𝓟 [[a, b]]) (𝓟 [[a, b]]) :=
  Filter.tendsto_Icc_Icc_Icc

instance tendsto_Ioc_uIcc_uIcc {a b : α} : TendstoIxxClass Ioc (𝓟 [[a, b]]) (𝓟 [[a, b]]) :=
  Filter.tendsto_Ioc_Icc_Icc

instance tendsto_uIcc_of_Icc {l : Filter α} [TendstoIxxClass Icc l l] :
    TendstoIxxClass uIcc l l := by
  refine ⟨fun s hs => mem_map.2 <| mem_prod_self_iff.2 ?_⟩
  obtain ⟨t, htl, hts⟩ : ∃ t ∈ l, ∀ p ∈ (t : Set α) ×ˢ t, Icc (p : α × α).1 p.2 ∈ s :=
    mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs))
  refine ⟨t, htl, fun p hp => ?_⟩
  rcases le_total p.1 p.2 with h | h
  · rw [mem_preimage, uIcc_of_le h]
    exact hts p hp
  · rw [mem_preimage, uIcc_of_ge h]
    exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩

protected theorem Tendsto.uIcc {l : Filter α} [TendstoIxxClass Icc l l] {f g : β → α}
    {lb : Filter β} (hf : Tendsto f lb l) (hg : Tendsto g lb l) :
    Tendsto (fun x => [[f x, g x]]) lb l.smallSets :=
  (@TendstoIxxClass.tendsto_Ixx α Set.uIcc _ _ _).comp <| hf.prodMk hg

end LinearOrder

end Filter
