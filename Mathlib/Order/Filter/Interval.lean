/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov

! This file was ported from Lean 3 source module order.filter.interval
! leanprover-community/mathlib commit 8631e2d5ea77f6c13054d9151d82b83069680cb1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.OrdConnected
import Mathbin.Order.Filter.SmallSets
import Mathbin.Order.Filter.AtTopBot

/-!
# Convergence of intervals

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.small_sets`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`.  Here and
below `Ixx` is one of `Icc`, `Ico`, `Ioc`, and `Ioo`. We define `filter.tendsto_Ixx_class Ixx l₁ l₂`
to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic a) (𝓟 $ Iio a)`,
i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁ n) (u₂ n)` is
eventually included in `Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `topology/algebra/ordered`.

| Input filter |  `Ixx = Icc`  |  `Ixx = Ico`  |  `Ixx = Ioc`  |  `Ixx = Ioo`  |
| -----------: | :-----------: | :-----------: | :-----------: | :-----------: |
|     `at_top` |    `at_top`   |    `at_top`   |    `at_top`   |    `at_top`   |
|     `at_bot` |    `at_bot`   |    `at_bot`   |    `at_bot`   |    `at_bot`   |
|     `pure a` |    `pure a`   |      `⊥`      |      `⊥`      |      `⊥`      |
|  `𝓟 (Iic a)` |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |
|  `𝓟 (Ici a)` |  `𝓟 (Ici a)`  |  `𝓟 (Ici a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Ioi a)` |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Iio a)` |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |
|        `𝓝 a` |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |
| `𝓝[Iic a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |
| `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |

-/


variable {α β : Type _}

open Classical Filter Interval

open Set Function

namespace Filter

section Preorder

variable [Preorder α]

/-- A pair of filters `l₁`, `l₂` has `tendsto_Ixx_class Ixx` property if `Ixx a b` tends to
`l₂.small_sets` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `Icc`, `Ico`, `Ioc`,
or `Ioo`. The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but
sometimes we can drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic
a) (𝓟 $ Iio a)`, i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁
n) (u₂ n)` is eventually included in `Iio a`.

We mark `l₂` as an `out_param` so that Lean can automatically find an appropriate `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying explicitly `l₂`. -/
class TendstoIxxClass (Ixx : α → α → Set α) (l₁ : Filter α) (l₂ : outParam <| Filter α) : Prop where
  tendsto_Ixx : Tendsto (fun p : α × α => Ixx p.1 p.2) (l₁ ×ᶠ l₁) l₂.smallSets
#align filter.tendsto_Ixx_class Filter.TendstoIxxClass

theorem Tendsto.icc {l₁ l₂ : Filter α} [TendstoIxxClass Icc l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Icc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂
#align filter.tendsto.Icc Filter.Tendsto.icc

theorem Tendsto.ioc {l₁ l₂ : Filter α} [TendstoIxxClass Ioc l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioc (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂
#align filter.tendsto.Ioc Filter.Tendsto.ioc

theorem Tendsto.ico {l₁ l₂ : Filter α} [TendstoIxxClass Ico l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ico (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂
#align filter.tendsto.Ico Filter.Tendsto.ico

theorem Tendsto.ioo {l₁ l₂ : Filter α} [TendstoIxxClass Ioo l₁ l₂] {lb : Filter β} {u₁ u₂ : β → α}
    (h₁ : Tendsto u₁ lb l₁) (h₂ : Tendsto u₂ lb l₁) :
    Tendsto (fun x => Ioo (u₁ x) (u₂ x)) lb l₂.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| h₁.prod_mk h₂
#align filter.tendsto.Ioo Filter.Tendsto.ioo

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » s) -/
theorem tendstoIxxClass_principal {s t : Set α} {Ixx : α → α → Set α} :
    TendstoIxxClass Ixx (𝓟 s) (𝓟 t) ↔ ∀ (x) (_ : x ∈ s) (y) (_ : y ∈ s), Ixx x y ⊆ t :=
  Iff.trans ⟨fun h => h.1, fun h => ⟨h⟩⟩ <| by
    simp only [small_sets_principal, prod_principal_principal, tendsto_principal_principal,
      forall_prod_set, mem_powerset_iff, mem_principal]
#align filter.tendsto_Ixx_class_principal Filter.tendstoIxxClass_principal

theorem tendstoIxxClass_inf {l₁ l₁' l₂ l₂' : Filter α} {Ixx} [h : TendstoIxxClass Ixx l₁ l₂]
    [h' : TendstoIxxClass Ixx l₁' l₂'] : TendstoIxxClass Ixx (l₁ ⊓ l₁') (l₂ ⊓ l₂') :=
  ⟨by simpa only [prod_inf_prod, small_sets_inf] using h.1.inf h'.1⟩
#align filter.tendsto_Ixx_class_inf Filter.tendstoIxxClass_inf

theorem tendstoIxxClass_of_subset {l₁ l₂ : Filter α} {Ixx Ixx' : α → α → Set α}
    (h : ∀ a b, Ixx a b ⊆ Ixx' a b) [h' : TendstoIxxClass Ixx' l₁ l₂] : TendstoIxxClass Ixx l₁ l₂ :=
  ⟨h'.1.small_sets_mono <| eventually_of_forall <| Prod.forall.2 h⟩
#align filter.tendsto_Ixx_class_of_subset Filter.tendstoIxxClass_of_subset

theorem HasBasis.tendstoIxxClass {ι : Type _} {p : ι → Prop} {s} {l : Filter α}
    (hl : l.HasBasis p s) {Ixx : α → α → Set α}
    (H : ∀ i, p i → ∀ x ∈ s i, ∀ y ∈ s i, Ixx x y ⊆ s i) : TendstoIxxClass Ixx l l :=
  ⟨(hl.prod_self.tendsto_iff hl.smallSets).2 fun i hi => ⟨i, hi, fun x hx => H i hi _ hx.1 _ hx.2⟩⟩
#align filter.has_basis.tendsto_Ixx_class Filter.HasBasis.tendstoIxxClass

instance tendsto_icc_atTop_atTop : TendstoIxxClass Icc (atTop : Filter α) atTop :=
  (hasBasis_infᵢ_principal_finite _).TendstoIxxClass fun s hs =>
    Set.OrdConnected.out <| ord_connected_bInter fun i hi => ordConnected_Ici
#align filter.tendsto_Icc_at_top_at_top Filter.tendsto_icc_atTop_atTop

instance tendsto_ico_atTop_atTop : TendstoIxxClass Ico (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
#align filter.tendsto_Ico_at_top_at_top Filter.tendsto_ico_atTop_atTop

instance tendsto_ioc_atTop_atTop : TendstoIxxClass Ioc (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
#align filter.tendsto_Ioc_at_top_at_top Filter.tendsto_ioc_atTop_atTop

instance tendsto_ioo_atTop_atTop : TendstoIxxClass Ioo (atTop : Filter α) atTop :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self
#align filter.tendsto_Ioo_at_top_at_top Filter.tendsto_ioo_atTop_atTop

instance tendsto_icc_atBot_atBot : TendstoIxxClass Icc (atBot : Filter α) atBot :=
  (hasBasis_infᵢ_principal_finite _).TendstoIxxClass fun s hs =>
    Set.OrdConnected.out <| ord_connected_bInter fun i hi => ordConnected_Iic
#align filter.tendsto_Icc_at_bot_at_bot Filter.tendsto_icc_atBot_atBot

instance tendsto_ico_atBot_atBot : TendstoIxxClass Ico (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
#align filter.tendsto_Ico_at_bot_at_bot Filter.tendsto_ico_atBot_atBot

instance tendsto_ioc_atBot_atBot : TendstoIxxClass Ioc (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
#align filter.tendsto_Ioc_at_bot_at_bot Filter.tendsto_ioc_atBot_atBot

instance tendsto_ioo_atBot_atBot : TendstoIxxClass Ioo (atBot : Filter α) atBot :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Icc_self
#align filter.tendsto_Ioo_at_bot_at_bot Filter.tendsto_ioo_atBot_atBot

instance OrdConnected.tendsto_icc {s : Set α} [hs : OrdConnected s] :
    TendstoIxxClass Icc (𝓟 s) (𝓟 s) :=
  tendstoIxxClass_principal.2 hs.out
#align filter.ord_connected.tendsto_Icc Filter.OrdConnected.tendsto_icc

instance tendsto_ico_ici_ici {a : α} : TendstoIxxClass Ico (𝓟 (Ici a)) (𝓟 (Ici a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
#align filter.tendsto_Ico_Ici_Ici Filter.tendsto_ico_ici_ici

instance tendsto_ico_ioi_ioi {a : α} : TendstoIxxClass Ico (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
#align filter.tendsto_Ico_Ioi_Ioi Filter.tendsto_ico_ioi_ioi

instance tendsto_ico_iic_iio {a : α} : TendstoIxxClass Ico (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_principal.2 fun a ha b hb x hx => lt_of_lt_of_le hx.2 hb
#align filter.tendsto_Ico_Iic_Iio Filter.tendsto_ico_iic_iio

instance tendsto_ico_iio_iio {a : α} : TendstoIxxClass Ico (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ico_subset_Icc_self
#align filter.tendsto_Ico_Iio_Iio Filter.tendsto_ico_iio_iio

instance tendsto_ioc_ici_ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_principal.2 fun x hx y hy t ht => lt_of_le_of_lt hx ht.1
#align filter.tendsto_Ioc_Ici_Ioi Filter.tendsto_ioc_ici_ioi

instance tendsto_ioc_iic_iic {a : α} : TendstoIxxClass Ioc (𝓟 (Iic a)) (𝓟 (Iic a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
#align filter.tendsto_Ioc_Iic_Iic Filter.tendsto_ioc_iic_iic

instance tendsto_ioc_iio_iio {a : α} : TendstoIxxClass Ioc (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
#align filter.tendsto_Ioc_Iio_Iio Filter.tendsto_ioc_iio_iio

instance tendsto_ioc_ioi_ioi {a : α} : TendstoIxxClass Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioc_subset_Icc_self
#align filter.tendsto_Ioc_Ioi_Ioi Filter.tendsto_ioc_ioi_ioi

instance tendsto_ioo_ici_ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self
#align filter.tendsto_Ioo_Ici_Ioi Filter.tendsto_ioo_ici_ioi

instance tendsto_ioo_iic_iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iic a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ico_self
#align filter.tendsto_Ioo_Iic_Iio Filter.tendsto_ioo_iic_iio

instance tendsto_ioo_ioi_ioi {a : α} : TendstoIxxClass Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self
#align filter.tendsto_Ioo_Ioi_Ioi Filter.tendsto_ioo_ioi_ioi

instance tendsto_ioo_iio_iio {a : α} : TendstoIxxClass Ioo (𝓟 (Iio a)) (𝓟 (Iio a)) :=
  tendstoIxxClass_of_subset fun _ _ => Ioo_subset_Ioc_self
#align filter.tendsto_Ioo_Iio_Iio Filter.tendsto_ioo_iio_iio

instance tendsto_icc_icc_icc {a b : α} : TendstoIxxClass Icc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendstoIxxClass_principal.mpr fun x hx y hy => Icc_subset_Icc hx.1 hy.2
#align filter.tendsto_Icc_Icc_Icc Filter.tendsto_icc_icc_icc

instance tendsto_ioc_icc_icc {a b : α} : TendstoIxxClass Ioc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
  tendsto_Ixx_class_of_subset fun _ _ => Ioc_subset_Icc_self
#align filter.tendsto_Ioc_Icc_Icc Filter.tendsto_ioc_icc_icc

end Preorder

section PartialOrder

variable [PartialOrder α]

instance tendsto_icc_pure_pure {a : α} : TendstoIxxClass Icc (pure a) (pure a : Filter α) :=
  by
  rw [← principal_singleton]
  exact tendsto_Ixx_class_principal.2 ord_connected_singleton.out
#align filter.tendsto_Icc_pure_pure Filter.tendsto_icc_pure_pure

instance tendsto_ico_pure_bot {a : α} : TendstoIxxClass Ico (pure a) ⊥ :=
  ⟨by simp⟩
#align filter.tendsto_Ico_pure_bot Filter.tendsto_ico_pure_bot

instance tendsto_ioc_pure_bot {a : α} : TendstoIxxClass Ioc (pure a) ⊥ :=
  ⟨by simp⟩
#align filter.tendsto_Ioc_pure_bot Filter.tendsto_ioc_pure_bot

instance tendsto_ioo_pure_bot {a : α} : TendstoIxxClass Ioo (pure a) ⊥ :=
  ⟨by simp⟩
#align filter.tendsto_Ioo_pure_bot Filter.tendsto_ioo_pure_bot

end PartialOrder

section LinearOrder

variable [LinearOrder α]

instance tendsto_icc_uIcc_uIcc {a b : α} : TendstoIxxClass Icc (𝓟 [a, b]) (𝓟 [a, b]) :=
  Filter.tendsto_icc_icc_icc
#align filter.tendsto_Icc_uIcc_uIcc Filter.tendsto_icc_uIcc_uIcc

instance tendsto_ioc_uIcc_uIcc {a b : α} : TendstoIxxClass Ioc (𝓟 [a, b]) (𝓟 [a, b]) :=
  Filter.tendsto_ioc_icc_icc
#align filter.tendsto_Ioc_uIcc_uIcc Filter.tendsto_ioc_uIcc_uIcc

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
instance tendsto_uIcc_of_icc {l : Filter α} [TendstoIxxClass Icc l l] : TendstoIxxClass uIcc l l :=
  by
  refine' ⟨fun s hs => mem_map.2 <| mem_prod_self_iff.2 _⟩
  obtain ⟨t, htl, hts⟩ : ∃ t ∈ l, ∀ p ∈ (t : Set α) ×ˢ t, Icc (p : α × α).1 p.2 ∈ s
  exact mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs))
  refine' ⟨t, htl, fun p hp => _⟩
  cases le_total p.1 p.2
  · rw [mem_preimage, uIcc_of_le h]
    exact hts p hp
  · rw [mem_preimage, uIcc_of_ge h]
    exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩
#align filter.tendsto_uIcc_of_Icc Filter.tendsto_uIcc_of_icc

theorem Tendsto.uIcc {l : Filter α} [TendstoIxxClass Icc l l] {f g : β → α} {lb : Filter β}
    (hf : Tendsto f lb l) (hg : Tendsto g lb l) : Tendsto (fun x => [f x, g x]) lb l.smallSets :=
  TendstoIxxClass.tendsto_Ixx.comp <| hf.prod_mk hg
#align filter.tendsto.uIcc Filter.Tendsto.uIcc

end LinearOrder

end Filter

