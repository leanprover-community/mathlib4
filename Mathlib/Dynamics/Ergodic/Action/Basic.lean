/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Group.AEStabilizer
import Mathlib.Dynamics.Ergodic.Ergodic

/-!
# Ergodic group actions

A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/

open Set Filter MeasureTheory MulAction
open scoped Pointwise

/--
An additive group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar addition `(g +ᵥ ·)`, `g : G`,
then it is either null or conull.
-/
class ErgodicVAdd (G α : Type*) [VAdd G α] {_ : MeasurableSpace α} (μ : Measure α) : Prop
    extends VAddInvariantMeasure G α μ where
  aeconst_of_forall_preimage_vadd_ae_eq {s : Set α} : MeasurableSet s →
    (∀ g : G, (g +ᵥ ·) ⁻¹' s =ᵐ[μ] s) → EventuallyConst s (ae μ)

/--
A group action of `G` on a space `α` with measure `μ` is called *ergodic*,
if for any (null) measurable set `s`,
if it is a.e.-invariant under each scalar multiplication `(g • ·)`, `g : G`,
then it is either null or conull.
-/
@[to_additive, mk_iff]
class ErgodicSMul (G α : Type*) [SMul G α] {_ : MeasurableSpace α} (μ : Measure α) : Prop
    extends SMulInvariantMeasure G α μ where
  aeconst_of_forall_preimage_smul_ae_eq {s : Set α} : MeasurableSet s →
    (∀ g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) → EventuallyConst s (ae μ)

attribute [to_additive] ergodicSMul_iff

namespace MeasureTheory

variable (G : Type*) {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

@[to_additive]
theorem aeconst_of_forall_preimage_smul_ae_eq [SMul G α] [ErgodicSMul G α μ] {s : Set α}
    (hm : NullMeasurableSet s μ) (h : ∀ g : G, (g • ·) ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) := by
  rcases hm with ⟨t, htm, hst⟩
  refine .congr ?_ hst.symm
  refine ErgodicSMul.aeconst_of_forall_preimage_smul_ae_eq htm fun g : G ↦ ?_
  refine .trans (.trans ?_ (h g)) hst
  exact tendsto_smul_ae _ _ hst.symm

section Group

variable [Group G] [MulAction G α] [ErgodicSMul G α μ] {s : Set α}

@[to_additive]
theorem aeconst_of_forall_smul_ae_eq (hm : NullMeasurableSet s μ) (h : ∀ g : G, g • s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  aeconst_of_forall_preimage_smul_ae_eq G hm fun g ↦ by
    simpa only [preimage_smul] using h g⁻¹

@[to_additive]
theorem _root_.MulAction.aeconst_of_aestabilizer_eq_top
    (hm : NullMeasurableSet s μ) (h : aestabilizer G μ s = ⊤) : EventuallyConst s (ae μ) :=
  aeconst_of_forall_smul_ae_eq G hm <| (Subgroup.eq_top_iff' _).1 h

end Group

theorem _root_.ErgodicSMul.of_aestabilizer [Group G] [MulAction G α] [SMulInvariantMeasure G α μ]
    (h : ∀ s, MeasurableSet s → aestabilizer G μ s = ⊤ → EventuallyConst s (ae μ)) :
    ErgodicSMul G α μ :=
  ⟨fun hm hs ↦ h _ hm <| (Subgroup.eq_top_iff' _).2 fun g ↦ by
    simpa only [preimage_smul_inv] using hs g⁻¹⟩

theorem ergodicSMul_iterateMulAct {f : α → α} (hf : Measurable f) :
    ErgodicSMul (IterateMulAct f) α μ ↔ Ergodic f μ := by
  simp only [ergodicSMul_iff, smulInvariantMeasure_iterateMulAct, hf]
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ⟨?_⟩⟩, fun h ↦ ⟨h.1, ?_⟩⟩
  · intro s hm hs
    refine h₂ hm fun n ↦ ?_
    nth_rewrite 2 [← Function.IsFixedPt.preimage_iterate hs n.val]
    rfl
  · intro s hm hs
    exact h.quasiErgodic.aeconst_set₀ hm.nullMeasurableSet <| hs (.mk 1)

end MeasureTheory
