/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Topology.Order.IsLUB

/-!
# Monotone functions on an order topology

This file contains lemmas about limits and continuity for monotone / antitone functions on
linearly-ordered sets (with the order topology). For example, we prove that a monotone function
has left and right limits at any point (`Monotone.tendsto_nhdsWithin_Iio`,
`Monotone.tendsto_nhdsWithin_Ioi`).

-/

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β γ : Type*}

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] [Nonempty γ]

/-- A monotone function continuous at the supremum of a nonempty set sends this supremum to
the supremum of the image of this set. -/
theorem Monotone.map_sSup_of_continuousAt' {f : α → β} {A : Set α} (Cf : ContinuousAt f (sSup A))
    (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sSup (f '' A) :=
  --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
  .symm <| ((isLUB_csSup A_nonemp A_bdd).isLUB_of_tendsto (Mf.monotoneOn _) A_nonemp <|
    Cf.mono_left inf_le_left).csSup_eq (A_nonemp.image f)
#align monotone.map_Sup_of_continuous_at' Monotone.map_sSup_of_continuousAt'

/-- A monotone function continuous at the indexed supremum over a nonempty `Sort` sends this indexed
supremum to the indexed supremum of the composition. -/
theorem Monotone.map_iSup_of_continuousAt' {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup, Monotone.map_sSup_of_continuousAt' Cf Mf (range_nonempty g) bdd, ← range_comp, iSup]
  rfl
#align monotone.map_supr_of_continuous_at' Monotone.map_iSup_of_continuousAt'

/-- A monotone function continuous at the infimum of a nonempty set sends this infimum to
the infimum of the image of this set. -/
theorem Monotone.map_sInf_of_continuousAt' {f : α → β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sInf (f '' A) :=
  Monotone.map_sSup_of_continuousAt' (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd
#align monotone.map_Inf_of_continuous_at' Monotone.map_sInf_of_continuousAt'

/-- A monotone function continuous at the indexed infimum over a nonempty `Sort` sends this indexed
infimum to the indexed infimum of the composition. -/
theorem Monotone.map_iInf_of_continuousAt' {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  rw [iInf, Monotone.map_sInf_of_continuousAt' Cf Mf (range_nonempty g) bdd, ← range_comp, iInf]
  rfl
#align monotone.map_infi_of_continuous_at' Monotone.map_iInf_of_continuousAt'

/-- An antitone function continuous at the infimum of a nonempty set sends this infimum to
the supremum of the image of this set. -/
theorem Antitone.map_sInf_of_continuousAt' {f : α → β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) :=
  Monotone.map_sInf_of_continuousAt' (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd
#align antitone.map_Inf_of_continuous_at' Antitone.map_sInf_of_continuousAt'

/-- An antitone function continuous at the indexed infimum over a nonempty `Sort` sends this indexed
infimum to the indexed supremum of the composition. -/
theorem Antitone.map_iInf_of_continuousAt' {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨆ i, f (g i) := by
  rw [iInf, Antitone.map_sInf_of_continuousAt' Cf Af (range_nonempty g) bdd, ← range_comp, iSup]
  rfl
#align antitone.map_infi_of_continuous_at' Antitone.map_iInf_of_continuousAt'

/-- An antitone function continuous at the supremum of a nonempty set sends this supremum to
the infimum of the image of this set. -/
theorem Antitone.map_sSup_of_continuousAt' {f : α → β} {A : Set α} (Cf : ContinuousAt f (sSup A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sInf (f '' A) :=
  Monotone.map_sSup_of_continuousAt' (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd
#align antitone.map_Sup_of_continuous_at' Antitone.map_sSup_of_continuousAt'

/-- An antitone function continuous at the indexed supremum over a nonempty `Sort` sends this
indexed supremum to the indexed infimum of the composition. -/
theorem Antitone.map_iSup_of_continuousAt' {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨅ i, f (g i) := by
  rw [iSup, Antitone.map_sSup_of_continuousAt' Cf Af (range_nonempty g) bdd, ← range_comp, iInf]
  rfl
#align antitone.map_supr_of_continuous_at' Antitone.map_iSup_of_continuousAt'

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [CompleteLinearOrder β]
  [TopologicalSpace β] [OrderClosedTopology β] [Nonempty γ]

theorem sSup_mem_closure {s : Set α} (hs : s.Nonempty) : sSup s ∈ closure s :=
  (isLUB_sSup s).mem_closure hs
#align Sup_mem_closure sSup_mem_closure

theorem sInf_mem_closure {s : Set α} (hs : s.Nonempty) : sInf s ∈ closure s :=
  (isGLB_sInf s).mem_closure hs
#align Inf_mem_closure sInf_mem_closure

theorem IsClosed.sSup_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sSup s ∈ s :=
  (isLUB_sSup s).mem_of_isClosed hs hc
#align is_closed.Sup_mem IsClosed.sSup_mem

theorem IsClosed.sInf_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sInf s ∈ s :=
  (isGLB_sInf s).mem_of_isClosed hs hc
#align is_closed.Inf_mem IsClosed.sInf_mem

/-- A monotone function `f` sending `bot` to `bot` and continuous at the supremum of a set sends
this supremum to the supremum of the image of this set. -/
theorem Monotone.map_sSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Mf : Monotone f) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s) := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h, fbot]
  · exact Mf.map_sSup_of_continuousAt' Cf h
#align monotone.map_Sup_of_continuous_at Monotone.map_sSup_of_continuousAt

/-- If a monotone function sending `bot` to `bot` is continuous at the indexed supremum over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the composition. -/
theorem Monotone.map_iSup_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f) (fbot : f ⊥ = ⊥) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup, Mf.map_sSup_of_continuousAt Cf fbot, ← range_comp, iSup]; rfl
#align monotone.map_supr_of_continuous_at Monotone.map_iSup_of_continuousAt

/-- A monotone function `f` sending `top` to `top` and continuous at the infimum of a set sends
this infimum to the infimum of the image of this set. -/
theorem Monotone.map_sInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (sInf s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop
#align monotone.map_Inf_of_continuous_at Monotone.map_sInf_of_continuousAt

/-- If a monotone function sending `top` to `top` is continuous at the indexed infimum over
a `Sort`, then it sends this indexed infimum to the indexed infimum of the composition. -/
theorem Monotone.map_iInf_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (iInf g) = iInf (f ∘ g) :=
  Monotone.map_iSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop
#align monotone.map_infi_of_continuous_at Monotone.map_iInf_of_continuousAt

/-- An antitone function `f` sending `bot` to `top` and continuous at the supremum of a set sends
this supremum to the infimum of the image of this set. -/
theorem Antitone.map_sSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Af : Antitone f) (fbot : f ⊥ = ⊤) : f (sSup s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sSup s) from Cf) Af
    fbot
#align antitone.map_Sup_of_continuous_at Antitone.map_sSup_of_continuousAt

/-- An antitone function sending `bot` to `top` is continuous at the indexed supremum over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the composition. -/
theorem Antitone.map_iSup_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f) (fbot : f ⊥ = ⊤) :
    f (⨆ i, g i) = ⨅ i, f (g i) :=
  Monotone.map_iSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iSup g) from Cf) Af
    fbot
#align antitone.map_supr_of_continuous_at Antitone.map_iSup_of_continuousAt

/-- An antitone function `f` sending `top` to `bot` and continuous at the infimum of a set sends
this infimum to the supremum of the image of this set. -/
theorem Antitone.map_sInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (sInf s) = sSup (f '' s) :=
  Monotone.map_sInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sInf s) from Cf) Af
    ftop
#align antitone.map_Inf_of_continuous_at Antitone.map_sInf_of_continuousAt

/-- If an antitone function sending `top` to `bot` is continuous at the indexed infimum over
a `Sort`, then it sends this indexed infimum to the indexed supremum of the composition. -/
theorem Antitone.map_iInf_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (iInf g) = iSup (f ∘ g) :=
  Monotone.map_iInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iInf g) from Cf) Af
    ftop
#align antitone.map_infi_of_continuous_at Antitone.map_iInf_of_continuousAt

end CompleteLinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] [Nonempty γ]

theorem csSup_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddAbove s) : sSup s ∈ closure s :=
  (isLUB_csSup hs B).mem_closure hs
#align cSup_mem_closure csSup_mem_closure

theorem csInf_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddBelow s) : sInf s ∈ closure s :=
  (isGLB_csInf hs B).mem_closure hs
#align cInf_mem_closure csInf_mem_closure

theorem IsClosed.csSup_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    sSup s ∈ s :=
  (isLUB_csSup hs B).mem_of_isClosed hs hc
#align is_closed.cSup_mem IsClosed.csSup_mem

theorem IsClosed.csInf_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    sInf s ∈ s :=
  (isGLB_csInf hs B).mem_of_isClosed hs hc
#align is_closed.cInf_mem IsClosed.csInf_mem

theorem IsClosed.isLeast_csInf {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    IsLeast s (sInf s) :=
  ⟨hc.csInf_mem hs B, (isGLB_csInf hs B).1⟩

theorem IsClosed.isGreatest_csSup {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    IsGreatest s (sSup s) :=
  IsClosed.isLeast_csInf (α := αᵒᵈ) hc hs B

/-- If a monotone function is continuous at the supremum of a nonempty bounded above set `s`,
then it sends this supremum to the supremum of the image of `s`. -/
theorem Monotone.map_csSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Mf : Monotone f) (ne : s.Nonempty) (H : BddAbove s) : f (sSup s) = sSup (f '' s) := by
  refine ((isLUB_csSup (ne.image f) (Mf.map_bddAbove H)).unique ?_).symm
  refine (isLUB_csSup ne H).isLUB_of_tendsto (fun x _ y _ xy => Mf xy) ne ?_
  exact Cf.mono_left inf_le_left
#align monotone.map_cSup_of_continuous_at Monotone.map_csSup_of_continuousAt

/-- If a monotone function is continuous at the indexed supremum of a bounded function on
a nonempty `Sort`, then it sends this supremum to the supremum of the composition. -/
theorem Monotone.map_ciSup_of_continuousAt {f : α → β} {g : γ → α} (Cf : ContinuousAt f (⨆ i, g i))
    (Mf : Monotone f) (H : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup, Mf.map_csSup_of_continuousAt Cf (range_nonempty _) H, ← range_comp, iSup]; rfl
#align monotone.map_csupr_of_continuous_at Monotone.map_ciSup_of_continuousAt

/-- If a monotone function is continuous at the infimum of a nonempty bounded below set `s`,
then it sends this infimum to the infimum of the image of `s`. -/
theorem Monotone.map_csInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Mf : Monotone f) (ne : s.Nonempty) (H : BddBelow s) : f (sInf s) = sInf (f '' s) :=
  Monotone.map_csSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ne H
#align monotone.map_cInf_of_continuous_at Monotone.map_csInf_of_continuousAt

/-- A continuous monotone function sends indexed infimum to indexed infimum in conditionally
complete linear order, under a boundedness assumption. -/
theorem Monotone.map_ciInf_of_continuousAt {f : α → β} {g : γ → α} (Cf : ContinuousAt f (⨅ i, g i))
    (Mf : Monotone f) (H : BddBelow (range g)) : f (⨅ i, g i) = ⨅ i, f (g i) :=
  Monotone.map_ciSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual H
#align monotone.map_cinfi_of_continuous_at Monotone.map_ciInf_of_continuousAt

/-- If an antitone function is continuous at the supremum of a nonempty bounded above set `s`,
then it sends this supremum to the infimum of the image of `s`. -/
theorem Antitone.map_csSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Af : Antitone f) (ne : s.Nonempty) (H : BddAbove s) : f (sSup s) = sInf (f '' s) :=
  Monotone.map_csSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sSup s) from Cf) Af
    ne H
#align antitone.map_cSup_of_continuous_at Antitone.map_csSup_of_continuousAt

/-- If an antitone function is continuous at the indexed supremum of a bounded function on
a nonempty `Sort`, then it sends this supremum to the infimum of the composition. -/
theorem Antitone.map_ciSup_of_continuousAt {f : α → β} {g : γ → α} (Cf : ContinuousAt f (⨆ i, g i))
    (Af : Antitone f) (H : BddAbove (range g)) : f (⨆ i, g i) = ⨅ i, f (g i) :=
  Monotone.map_ciSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (⨆ i, g i) from Cf)
    Af H
#align antitone.map_csupr_of_continuous_at Antitone.map_ciSup_of_continuousAt

/-- If an antitone function is continuous at the infimum of a nonempty bounded below set `s`,
then it sends this infimum to the supremum of the image of `s`. -/
theorem Antitone.map_csInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Af : Antitone f) (ne : s.Nonempty) (H : BddBelow s) : f (sInf s) = sSup (f '' s) :=
  Monotone.map_csInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sInf s) from Cf) Af
    ne H
#align antitone.map_cInf_of_continuous_at Antitone.map_csInf_of_continuousAt

/-- A continuous antitone function sends indexed infimum to indexed supremum in conditionally
complete linear order, under a boundedness assumption. -/
theorem Antitone.map_ciInf_of_continuousAt {f : α → β} {g : γ → α} (Cf : ContinuousAt f (⨅ i, g i))
    (Af : Antitone f) (H : BddBelow (range g)) : f (⨅ i, g i) = ⨆ i, f (g i) :=
  Monotone.map_ciInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (⨅ i, g i) from Cf)
    Af H
#align antitone.map_cinfi_of_continuous_at Antitone.map_ciInf_of_continuousAt

/-- A monotone map has a limit to the left of any point `x`, equal to `sSup (f '' (Iio x))`. -/
theorem Monotone.tendsto_nhdsWithin_Iio {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) := by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : ∃ a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h.image _) hl
    exact mem_of_superset (Ioo_mem_nhdsWithin_Iio' zx) fun y hy => lz.trans_le (Mf hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun _ hy => lt_of_le_of_lt ?_ hm
    exact le_csSup (Mf.map_bddAbove bddAbove_Iio) (mem_image_of_mem _ hy)
#align monotone.tendsto_nhds_within_Iio Monotone.tendsto_nhdsWithin_Iio

/-- A monotone map has a limit to the right of any point `x`, equal to `sInf (f '' (Ioi x))`. -/
theorem Monotone.tendsto_nhdsWithin_Ioi {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  Monotone.tendsto_nhdsWithin_Iio (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual x
#align monotone.tendsto_nhds_within_Ioi Monotone.tendsto_nhdsWithin_Ioi

end ConditionallyCompleteLinearOrder
