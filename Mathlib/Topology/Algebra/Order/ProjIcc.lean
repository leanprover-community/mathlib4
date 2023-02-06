/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.order.proj_Icc
! leanprover-community/mathlib commit 4c19a16e4b705bf135cf9a80ac18fcc99c438514
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Intervals.ProjIcc
import Mathbin.Topology.Order.Basic

/-!
# Projection onto a closed interval

In this file we prove that the projection `set.proj_Icc f a b h` is a quotient map, and use it
to show that `Icc_extend h f` is continuous if and only if `f` is continuous.
-/


open Set Filter

open Filter Topology

variable {α β γ : Type _} [LinearOrder α] [TopologicalSpace γ] {a b c : α} {h : a ≤ b}

theorem Filter.Tendsto.iccExtend (f : γ → Icc a b → β) {z : γ} {l : Filter α} {l' : Filter β}
    (hf : Tendsto (↿f) (𝓝 z ×ᶠ l.map (projIcc a b h)) l') :
    Tendsto (↿(IccExtend h ∘ f)) (𝓝 z ×ᶠ l) l' :=
  show Tendsto (↿f ∘ Prod.map id (projIcc a b h)) (𝓝 z ×ᶠ l) l' from
    hf.comp <| tendsto_id.Prod_map tendsto_map
#align filter.tendsto.Icc_extend Filter.Tendsto.iccExtend

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β]

@[continuity]
theorem continuous_projIcc : Continuous (projIcc a b h) :=
  (continuous_const.max <| continuous_const.min continuous_id).subtype_mk _
#align continuous_proj_Icc continuous_projIcc

theorem quotientMap_projIcc : QuotientMap (projIcc a b h) :=
  quotientMap_iff.2
    ⟨projIcc_surjective h, fun s =>
      ⟨fun hs => hs.Preimage continuous_projIcc, fun hs =>
        ⟨_, hs, by
          ext
          simp⟩⟩⟩
#align quotient_map_proj_Icc quotientMap_projIcc

@[simp]
theorem continuous_iccExtend_iff {f : Icc a b → β} : Continuous (IccExtend h f) ↔ Continuous f :=
  quotientMap_projIcc.continuous_iff.symm
#align continuous_Icc_extend_iff continuous_iccExtend_iff

/-- See Note [continuity lemma statement]. -/
theorem Continuous.iccExtend {f : γ → Icc a b → β} {g : γ → α} (hf : Continuous ↿f)
    (hg : Continuous g) : Continuous fun a => IccExtend h (f a) (g a) :=
  hf.comp <| continuous_id.prod_mk <| continuous_projIcc.comp hg
#align continuous.Icc_extend Continuous.iccExtend

/-- A useful special case of `continuous.Icc_extend`. -/
@[continuity]
theorem Continuous.Icc_extend' {f : Icc a b → β} (hf : Continuous f) : Continuous (IccExtend h f) :=
  hf.comp continuous_projIcc
#align continuous.Icc_extend' Continuous.Icc_extend'

theorem ContinuousAt.iccExtend {x : γ} (f : γ → Icc a b → β) {g : γ → α}
    (hf : ContinuousAt (↿f) (x, projIcc a b h (g x))) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => IccExtend h (f a) (g a)) x :=
  show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
    ContinuousAt.comp hf <| continuousAt_id.Prod <| continuous_projIcc.ContinuousAt.comp hg
#align continuous_at.Icc_extend ContinuousAt.iccExtend

