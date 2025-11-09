/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.Prod
import Mathlib.Order.Interval.Finset.Defs

/-!
# Limits of intervals along filters

This file contains some lemmas about how filters `Ixx` behave as the endpoints tend to `±∞`.

-/

namespace Finset

open Filter

section Asymmetric

variable {α : Type*} [Preorder α] [LocallyFiniteOrder α]

lemma tendsto_Icc_atBot_prod_atTop :
    Tendsto (fun p : α × α ↦ Icc p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_le_atBot i).prod_mk (eventually_ge_atTop i)

lemma tendsto_Ioc_atBot_prod_atTop [NoBotOrder α] :
    Tendsto (fun p : α × α ↦ Ioc p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_lt_atBot i).prod_mk (eventually_ge_atTop i)

lemma tendsto_Ico_atBot_prod_atTop [NoTopOrder α] :
    Tendsto (fun p : α × α ↦ Finset.Ico p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_le_atBot i).prod_mk (eventually_gt_atTop i)

lemma tendsto_Ioo_atBot_prod_atTop [NoBotOrder α] [NoTopOrder α] :
    Tendsto (fun p : α × α ↦ Finset.Ioo p.1 p.2) (atBot ×ˢ atTop) atTop := by
  simpa [tendsto_atTop, ← coe_subset, Set.subset_def, -eventually_and]
    using fun b i _ ↦ (eventually_lt_atBot i).prod_mk (eventually_gt_atTop i)

end Asymmetric

section Symmetric

variable {α : Type*} [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]
  [LocallyFiniteOrder α]

lemma tendsto_Icc_neg_atTop_atTop :
    Tendsto (fun a : α ↦ Icc (-a) a) atTop atTop :=
  tendsto_Icc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

lemma tendsto_Ioc_neg_atTop_atTop [NoBotOrder α] :
    Tendsto (fun a : α ↦ Ioc (-a) a) atTop atTop :=
  tendsto_Ioc_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

lemma tendsto_Ico_neg_atTop_atTop [NoTopOrder α] :
    Tendsto (fun a : α ↦ Ico (-a) a) atTop atTop :=
  tendsto_Ico_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

lemma tendsto_Ioo_neg_atTop_atTop [NoBotOrder α] [NoTopOrder α] :
    Tendsto (fun a : α ↦ Ioo (-a) a) atTop atTop :=
  tendsto_Ioo_atBot_prod_atTop.comp (tendsto_neg_atTop_atBot.prodMk tendsto_id)

end Symmetric

section NatCast

variable {R : Type*} [Ring R] [PartialOrder R] [IsOrderedRing R] [LocallyFiniteOrder R]
  [Archimedean R]

lemma tendsto_Icc_neg :
    Tendsto (fun n : ℕ ↦ Icc (-n : R) n) atTop atTop :=
  tendsto_Icc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

variable [Nontrivial R]

lemma tendsto_Ioc_neg : Tendsto (fun n : ℕ ↦ Ioc (-n : R) n) atTop atTop :=
  tendsto_Ioc_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_Ico_neg : Tendsto (fun n : ℕ ↦ Ico (-n : R) n) atTop atTop :=
  tendsto_Ico_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_Ioo_neg : Tendsto (fun n : ℕ ↦ Ioo (-n : R) n) atTop atTop :=
  tendsto_Ioo_neg_atTop_atTop.comp tendsto_natCast_atTop_atTop

end NatCast

end Finset
