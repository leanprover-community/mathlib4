/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Topology.Order.Basic

#align_import topology.algebra.order.proj_Icc from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

/-!
# Projection onto a closed interval

In this file we prove that the projection `Set.projIcc f a b h` is a quotient map, and use it
to show that `Set.IccExtend h f` is continuous if and only if `f` is continuous.
-/


open Set Filter Topology

variable {α β γ : Type*} [LinearOrder α] [TopologicalSpace γ] {a b c : α} {h : a ≤ b}

protected theorem Filter.Tendsto.IccExtend (f : γ → Icc a b → β) {la : Filter α} {lb : Filter β}
    {lc : Filter γ} (hf : Tendsto (↿f) (lc ×ˢ la.map (projIcc a b h)) lb) :
    Tendsto (↿(IccExtend h ∘ f)) (lc ×ˢ la) lb :=
  hf.comp <| tendsto_id.prod_map tendsto_map
#align filter.tendsto.Icc_extend Filter.Tendsto.IccExtendₓ

variable [TopologicalSpace α] [OrderTopology α] [TopologicalSpace β]

@[continuity]
theorem continuous_projIcc : Continuous (projIcc a b h) :=
  (continuous_const.max <| continuous_const.min continuous_id).subtype_mk _
#align continuous_proj_Icc continuous_projIcc

theorem quotientMap_projIcc : QuotientMap (projIcc a b h) :=
  quotientMap_iff.2 ⟨projIcc_surjective h, fun s =>
    ⟨fun hs => hs.preimage continuous_projIcc, fun hs => ⟨_, hs, by ext; simp⟩⟩⟩
#align quotient_map_proj_Icc quotientMap_projIcc

@[simp]
theorem continuous_IccExtend_iff {f : Icc a b → β} : Continuous (IccExtend h f) ↔ Continuous f :=
  quotientMap_projIcc.continuous_iff.symm
#align continuous_Icc_extend_iff continuous_IccExtend_iff

/-- See Note [continuity lemma statement]. -/
protected theorem Continuous.IccExtend {f : γ → Icc a b → β} {g : γ → α} (hf : Continuous ↿f)
    (hg : Continuous g) : Continuous fun a => IccExtend h (f a) (g a) :=
  show Continuous (↿f ∘ fun x => (x, projIcc a b h (g x)))
  from hf.comp <| continuous_id.prod_mk <| continuous_projIcc.comp hg
#align continuous.Icc_extend Continuous.IccExtend

/-- A useful special case of `Continuous.IccExtend`. -/
@[continuity]
protected theorem Continuous.Icc_extend' {f : Icc a b → β} (hf : Continuous f) :
    Continuous (IccExtend h f) :=
  hf.comp continuous_projIcc
#align continuous.Icc_extend' Continuous.Icc_extend'

theorem ContinuousAt.IccExtend {x : γ} (f : γ → Icc a b → β) {g : γ → α}
    (hf : ContinuousAt (↿f) (x, projIcc a b h (g x))) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => IccExtend h (f a) (g a)) x :=
  show ContinuousAt (↿f ∘ fun x => (x, projIcc a b h (g x))) x from
    ContinuousAt.comp hf <| continuousAt_id.prod <| continuous_projIcc.continuousAt.comp hg
#align continuous_at.Icc_extend ContinuousAt.IccExtend
