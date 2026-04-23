/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Monotone
import Mathlib.Init
import Mathlib.Order.Filter.Tendsto
meta import Mathlib.Tactic.Attr.Register
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Nontriviality.Core
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Order
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LeftRight

/-!
# Monotone functions on an order topology

This file contains lemmas about limits and continuity for monotone / antitone functions on
linearly-ordered sets (with the order topology). For example, we prove that a monotone function
has left and right limits at any point (`Monotone.tendsto_nhdsLT`, `Monotone.tendsto_nhdsGT`).

-/

public section

open Set Filter TopologicalSpace Topology Function

open OrderDual (toDual ofDual)

variable {α β : Type*}

section LinearOrder

variable [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [LinearOrder β]
  {s : Set α} {x : α} {f : α → β}

lemma MonotoneOn.insert_of_continuousWithinAt [TopologicalSpace β] [OrderClosedTopology β]
    (hf : MonotoneOn f s) (hx : ClusterPt x (𝓟 s)) (h'x : ContinuousWithinAt f s x) :
    MonotoneOn f (insert x s) := by
  have : (𝓝[s] x).NeBot := hx
  apply monotoneOn_insert_iff.2 ⟨fun b hb hbx ↦ ?_, fun b hb hxb ↦ ?_, hf⟩
  · rcases hbx.eq_or_lt with rfl | hbx
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply ge_of_tendsto h'x
    have : s ∩ Ioi b ∈ 𝓝[s] x := inter_mem_nhdsWithin _ (Ioi_mem_nhds hbx)
    filter_upwards [this] with y hy using hf hb hy.1 (le_of_lt hy.2)
  · rcases hxb.eq_or_lt with rfl | hxb
    · exact le_rfl
    simp only [ContinuousWithinAt] at h'x
    apply le_of_tendsto h'x
    have : s ∩ Iio b ∈ 𝓝[s] x := inter_mem_nhdsWithin _ (Iio_mem_nhds hxb)
    filter_upwards [this] with y hy
    exact hf hy.1 hb (le_of_lt hy.2)

/-- If a function is monotone on a set in a second countable topological space, then there
are only countably many points that have several preimages. -/
lemma MonotoneOn.countable_setOf_two_preimages [SecondCountableTopology α]
    (hf : MonotoneOn f s) :
    Set.Countable {c | ∃ x y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c} := by
  nontriviality α
  let t := {c | ∃ x, ∃ y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c}
  have : ∀ c ∈ t, ∃ x, ∃ y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c := fun c hc ↦ hc
  choose! x y hxs hys hxy hfx hfy using this
  let u := x '' t
  suffices H : Set.Countable (x '' t) by
    have : Set.InjOn x t := by
      intro c hc d hd hcd
      have : f (x c) = f (x d) := by simp [hcd]
      rwa [hfx _ hc, hfx _ hd] at this
    exact countable_of_injective_of_countable_image this H
  apply Set.PairwiseDisjoint.countable_of_Ioo (y := fun a ↦ y (f a)); swap
  · rintro a ⟨c, hc, rfl⟩
    rw [hfx _ hc]
    exact hxy _ hc
  simp only [PairwiseDisjoint, Set.Pairwise, mem_image, onFun, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  intro c hc d hd hcd
  wlog H : c < d generalizing c d with h
  · apply (h d hd c hc hcd.symm ?_).symm
    have : c ≠ d := fun h ↦ hcd (congrArg x h)
    order
  simp only [disjoint_iff_forall_ne, mem_Ioo, ne_eq, and_imp]
  rintro a xca ayc b xda ayd rfl
  rw [hfx _ hc] at ayc
  have : x d ≤ y c := (xda.trans ayc).le
  have : f (x d) ≤ f (y c) := hf (hxs _ hd) (hys _ hc) this
  rw [hfx _ hd, hfy _ hc] at this
  exact not_le.2 H this

/-- If a function is monotone in a second countable topological space, then there
are only countably many points that have several preimages. -/
lemma Monotone.countable_setOf_two_preimages [SecondCountableTopology α]
    (hf : Monotone f) :
    Set.Countable {c | ∃ x y, x < y ∧ f x = c ∧ f y = c} := by
  rw [← monotoneOn_univ] at hf
  simpa using hf.countable_setOf_two_preimages

/-- If a function is antitone on a set in a second countable topological space, then there
are only countably many points that have several preimages. -/
lemma AntitoneOn.countable_setOf_two_preimages [SecondCountableTopology α]
    (hf : AntitoneOn f s) :
    Set.Countable {c | ∃ x y, x ∈ s ∧ y ∈ s ∧ x < y ∧ f x = c ∧ f y = c} :=
  (MonotoneOn.countable_setOf_two_preimages hf.dual_right :)

/-- If a function is antitone in a second countable topological space, then there
are only countably many points that have several preimages. -/
lemma Antitone.countable_setOf_two_preimages [SecondCountableTopology α]
    (hf : Antitone f) :
    Set.Countable {c | ∃ x y, x < y ∧ f x = c ∧ f y = c} :=
  (Monotone.countable_setOf_two_preimages hf.dual_right :)

section Continuity

variable [TopologicalSpace β] [OrderTopology β] [SecondCountableTopology β]

/-- In a second countable space, the set of points where a monotone function is not right-continuous
within a set is at most countable. Superseded by `MonotoneOn.countable_not_continuousWithinAt`
which gives the two-sided version. -/
theorem MonotoneOn.countable_not_continuousWithinAt_Ioi (hf : MonotoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f (s ∩ Ioi x) x} := by
  apply (countable_image_lt_image_Ioi_within s f).mono
  rintro x ⟨xs, hx : ¬ContinuousWithinAt f (s ∩ Ioi x) x⟩
  dsimp only [mem_setOf_eq]
  contrapose! hx
  refine tendsto_order.2 ⟨fun m hm => ?_, fun u hu => ?_⟩
  · filter_upwards [@self_mem_nhdsWithin _ _ x (s ∩ Ioi x)] with y hy
    exact hm.trans_le (hf xs hy.1 (le_of_lt hy.2))
  rcases hx xs u hu with ⟨v, vs, xv, fvu⟩
  have : s ∩ Ioo x v ∈ 𝓝[s ∩ Ioi x] x := by simp [nhdsWithin_inter, mem_inf_of_left,
    self_mem_nhdsWithin, mem_inf_of_right, Ioo_mem_nhdsGT xv]
  filter_upwards [this] with y hy
  exact (hf hy.1 vs hy.2.2.le).trans_lt fvu

/-- In a second countable space, the set of points where a monotone function is not left-continuous
within a set is at most countable. Superseded by `MonotoneOn.countable_not_continuousWithinAt`
which gives the two-sided version. -/
theorem MonotoneOn.countable_not_continuousWithinAt_Iio (hf : MonotoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f (s ∩ Iio x) x} :=
  hf.dual.countable_not_continuousWithinAt_Ioi

/-- In a second countable space, the set of points where a monotone function is not continuous
within a set is at most countable. -/
theorem MonotoneOn.countable_not_continuousWithinAt (hf : MonotoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f s x} := by
  apply (hf.countable_not_continuousWithinAt_Ioi.union hf.countable_not_continuousWithinAt_Iio).mono
  refine compl_subset_compl.1 ?_
  simp only [compl_union]
  rintro x ⟨hx, h'x⟩
  simp only [mem_compl_iff, mem_setOf_eq, not_and, not_not] at hx h'x ⊢
  intro xs
  exact continuousWithinAt_iff_continuous_left'_right'.2 ⟨h'x xs, hx xs⟩

/-- In a second countable space, the set of points where a monotone function is not continuous
is at most countable. -/
theorem Monotone.countable_not_continuousAt (hf : Monotone f) :
    Set.Countable {x | ¬ContinuousAt f x} := by
  simpa [continuousWithinAt_univ] using (hf.monotoneOn univ).countable_not_continuousWithinAt

/-- In a second countable space, the set of points where an antitone function is not continuous
within a set is at most countable. -/
theorem _root_.AntitoneOn.countable_not_continuousWithinAt
    {s : Set α} (hf : AntitoneOn f s) :
    Set.Countable {x ∈ s | ¬ContinuousWithinAt f s x} :=
  hf.dual_right.countable_not_continuousWithinAt

/-- In a second countable space, the set of points where an antitone function is not continuous
is at most countable. -/
theorem Antitone.countable_not_continuousAt (hf : Antitone f) :
    Set.Countable {x | ¬ContinuousAt f x} :=
  hf.dual_right.countable_not_continuousAt

end Continuity

end LinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]

/-- A monotone function continuous at the supremum of a nonempty set sends this supremum to
the supremum of the image of this set. -/
theorem MonotoneOn.map_csSup_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sSup A))
    (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sSup (f '' A) :=
  --This is a particular case of the more general `IsLUB.isLUB_of_tendsto`
  .symm <| ((isLUB_csSup A_nonemp A_bdd).isLUB_of_tendsto Mf A_nonemp <|
    Cf.mono_left fun ⦃_⦄ a ↦ a).csSup_eq (A_nonemp.image f)

/-- A monotone function continuous at the supremum of a nonempty set sends this supremum to
the supremum of the image of this set. -/
theorem Monotone.map_csSup_of_continuousAt {f : α → β} {A : Set α}
    (Cf : ContinuousAt f (sSup A)) (Mf : Monotone f) (A_nonemp : A.Nonempty)
    (A_bdd : BddAbove A := by bddDefault) : f (sSup A) = sSup (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt Cf.continuousWithinAt
    (Mf.monotoneOn _) A_nonemp A_bdd

/-- A monotone function continuous at the indexed supremum over a nonempty `Sort` sends this indexed
supremum to the indexed supremum of the composition. -/
theorem Monotone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup, Monotone.map_csSup_of_continuousAt Cf Mf (range_nonempty g) bdd, ← range_comp, iSup,
    comp_def]

/-- A monotone function continuous at the infimum of a nonempty set sends this infimum to
the infimum of the image of this set. -/
theorem MonotoneOn.map_csInf_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sInf A))
    (Mf : MonotoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sInf (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

/-- A monotone function continuous at the infimum of a nonempty set sends this infimum to
the infimum of the image of this set. -/
theorem Monotone.map_csInf_of_continuousAt {f : α → β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Mf : Monotone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sInf (f '' A) :=
  Monotone.map_csSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual A_nonemp A_bdd

/-- A monotone function continuous at the indexed infimum over a nonempty `Sort` sends this indexed
infimum to the indexed infimum of the composition. -/
theorem Monotone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  rw [iInf, Monotone.map_csInf_of_continuousAt Cf Mf (range_nonempty g) bdd, ← range_comp, iInf,
    comp_def]

/-- An antitone function continuous at the infimum of a nonempty set sends this infimum to
the supremum of the image of this set. -/
theorem AntitoneOn.map_csInf_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sInf A))
    (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) :=
  MonotoneOn.map_csInf_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the infimum of a nonempty set sends this infimum to
the supremum of the image of this set. -/
theorem Antitone.map_csInf_of_continuousAt {f : α → β} {A : Set α} (Cf : ContinuousAt f (sInf A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddBelow A := by bddDefault) :
    f (sInf A) = sSup (f '' A) :=
  Monotone.map_csInf_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the indexed infimum over a nonempty `Sort` sends this indexed
infimum to the indexed supremum of the composition. -/
theorem Antitone.map_ciInf_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f)
    (bdd : BddBelow (range g) := by bddDefault) : f (⨅ i, g i) = ⨆ i, f (g i) := by
  rw [iInf, Antitone.map_csInf_of_continuousAt Cf Af (range_nonempty g) bdd, ← range_comp, iSup,
    comp_def]

/-- An antitone function continuous at the supremum of a nonempty set sends this supremum to
the infimum of the image of this set. -/
theorem AntitoneOn.map_csSup_of_continuousWithinAt {f : α → β} {A : Set α}
    (Cf : ContinuousWithinAt f A (sSup A))
    (Af : AntitoneOn f A) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sInf (f '' A) :=
  MonotoneOn.map_csSup_of_continuousWithinAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the supremum of a nonempty set sends this supremum to
the infimum of the image of this set. -/
theorem Antitone.map_csSup_of_continuousAt {f : α → β} {A : Set α} (Cf : ContinuousAt f (sSup A))
    (Af : Antitone f) (A_nonemp : A.Nonempty) (A_bdd : BddAbove A := by bddDefault) :
    f (sSup A) = sInf (f '' A) :=
  Monotone.map_csSup_of_continuousAt (β := βᵒᵈ) Cf Af.dual_right A_nonemp A_bdd

/-- An antitone function continuous at the indexed supremum over a nonempty `Sort` sends this
indexed supremum to the indexed infimum of the composition. -/
theorem Antitone.map_ciSup_of_continuousAt {ι : Sort*} [Nonempty ι] {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f)
    (bdd : BddAbove (range g) := by bddDefault) : f (⨆ i, g i) = ⨅ i, f (g i) := by
  rw [iSup, Antitone.map_csSup_of_continuousAt Cf Af (range_nonempty g) bdd, ← range_comp, iInf,
    comp_def]

end ConditionallyCompleteLinearOrder

section CompleteLinearOrder

variable [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [CompleteLinearOrder β]
  [TopologicalSpace β] [OrderClosedTopology β]

theorem sSup_mem_closure {s : Set α} (hs : s.Nonempty) : sSup s ∈ closure s :=
  (isLUB_sSup s).mem_closure hs

theorem sInf_mem_closure {s : Set α} (hs : s.Nonempty) : sInf s ∈ closure s :=
  (isGLB_sInf s).mem_closure hs

theorem IsClosed.sSup_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sSup s ∈ s :=
  (isLUB_sSup s).mem_of_isClosed hs hc

theorem IsClosed.sInf_mem {s : Set α} (hs : s.Nonempty) (hc : IsClosed s) : sInf s ∈ s :=
  (isGLB_sInf s).mem_of_isClosed hs hc

/-- A monotone function `f` sending `bot` to `bot` and continuous at the supremum of a set sends
this supremum to the supremum of the image of this set. -/
theorem MonotoneOn.map_sSup_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sSup s))
    (Mf : MonotoneOn f s) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s) := by
  rcases s.eq_empty_or_nonempty with h | h
  · simp [h, fbot]
  · exact Mf.map_csSup_of_continuousWithinAt Cf h

/-- A monotone function `f` sending `bot` to `bot` and continuous at the supremum of a set sends
this supremum to the supremum of the image of this set. -/
theorem Monotone.map_sSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Mf : Monotone f) (fbot : f ⊥ = ⊥) : f (sSup s) = sSup (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt Cf.continuousWithinAt (Mf.monotoneOn _) fbot

/-- If a monotone function sending `bot` to `bot` is continuous at the indexed supremum over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the composition. -/
theorem Monotone.map_iSup_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Mf : Monotone f) (fbot : f ⊥ = ⊥) :
    f (⨆ i, g i) = ⨆ i, f (g i) := by
  rw [iSup, Mf.map_sSup_of_continuousAt Cf fbot, ← range_comp, iSup, comp_def]

/-- A monotone function `f` sending `top` to `top` and continuous at the infimum of a set sends
this infimum to the infimum of the image of this set. -/
theorem MonotoneOn.map_sInf_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sInf s)) (Mf : MonotoneOn f s) (ftop : f ⊤ = ⊤) :
    f (sInf s) = sInf (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/-- A monotone function `f` sending `top` to `top` and continuous at the infimum of a set sends
this infimum to the infimum of the image of this set. -/
theorem Monotone.map_sInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (sInf s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/-- If a monotone function sending `top` to `top` is continuous at the indexed infimum over
a `Sort`, then it sends this indexed infimum to the indexed infimum of the composition. -/
theorem Monotone.map_iInf_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Mf : Monotone f) (ftop : f ⊤ = ⊤) : f (iInf g) = iInf (f ∘ g) :=
  Monotone.map_iSup_of_continuousAt (α := αᵒᵈ) (β := βᵒᵈ) Cf Mf.dual ftop

/-- An antitone function `f` sending `bot` to `top` and continuous at the supremum of a set sends
this supremum to the infimum of the image of this set. -/
theorem AntitoneOn.map_sSup_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sSup s)) (Af : AntitoneOn f s) (fbot : f ⊥ = ⊤) :
    f (sSup s) = sInf (f '' s) :=
  MonotoneOn.map_sSup_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sSup s) from Cf) Af fbot

/-- An antitone function `f` sending `bot` to `top` and continuous at the supremum of a set sends
this supremum to the infimum of the image of this set. -/
theorem Antitone.map_sSup_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sSup s))
    (Af : Antitone f) (fbot : f ⊥ = ⊤) : f (sSup s) = sInf (f '' s) :=
  Monotone.map_sSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sSup s) from Cf) Af
    fbot

/-- An antitone function sending `bot` to `top` is continuous at the indexed supremum over
a `Sort`, then it sends this indexed supremum to the indexed supremum of the composition. -/
theorem Antitone.map_iSup_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iSup g)) (Af : Antitone f) (fbot : f ⊥ = ⊤) :
    f (⨆ i, g i) = ⨅ i, f (g i) :=
  Monotone.map_iSup_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iSup g) from Cf) Af
    fbot

/-- An antitone function `f` sending `top` to `bot` and continuous at the infimum of a set sends
this infimum to the supremum of the image of this set. -/
theorem AntitoneOn.map_sInf_of_continuousWithinAt {f : α → β} {s : Set α}
    (Cf : ContinuousWithinAt f s (sInf s)) (Af : AntitoneOn f s) (ftop : f ⊤ = ⊥) :
    f (sInf s) = sSup (f '' s) :=
  MonotoneOn.map_sInf_of_continuousWithinAt
    (show ContinuousWithinAt (OrderDual.toDual ∘ f) s (sInf s) from Cf) Af ftop

/-- An antitone function `f` sending `top` to `bot` and continuous at the infimum of a set sends
this infimum to the supremum of the image of this set. -/
theorem Antitone.map_sInf_of_continuousAt {f : α → β} {s : Set α} (Cf : ContinuousAt f (sInf s))
    (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (sInf s) = sSup (f '' s) :=
  Monotone.map_sInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (sInf s) from Cf) Af
    ftop

/-- If an antitone function sending `top` to `bot` is continuous at the indexed infimum over
a `Sort`, then it sends this indexed infimum to the indexed supremum of the composition. -/
theorem Antitone.map_iInf_of_continuousAt {ι : Sort*} {f : α → β} {g : ι → α}
    (Cf : ContinuousAt f (iInf g)) (Af : Antitone f) (ftop : f ⊤ = ⊥) : f (iInf g) = iSup (f ∘ g) :=
  Monotone.map_iInf_of_continuousAt (show ContinuousAt (OrderDual.toDual ∘ f) (iInf g) from Cf) Af
    ftop

end CompleteLinearOrder

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]

theorem csSup_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddAbove s) : sSup s ∈ closure s :=
  (isLUB_csSup hs B).mem_closure hs

theorem csInf_mem_closure {s : Set α} (hs : s.Nonempty) (B : BddBelow s) : sInf s ∈ closure s :=
  (isGLB_csInf hs B).mem_closure hs

theorem IsClosed.csSup_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    sSup s ∈ s :=
  (isLUB_csSup hs B).mem_of_isClosed hs hc

theorem IsClosed.csInf_mem {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    sInf s ∈ s :=
  (isGLB_csInf hs B).mem_of_isClosed hs hc

theorem IsClosed.isLeast_csInf {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddBelow s) :
    IsLeast s (sInf s) :=
  ⟨hc.csInf_mem hs B, (isGLB_csInf hs B).1⟩

theorem IsClosed.isGreatest_csSup {s : Set α} (hc : IsClosed s) (hs : s.Nonempty) (B : BddAbove s) :
    IsGreatest s (sSup s) :=
  IsClosed.isLeast_csInf (α := αᵒᵈ) hc hs B

lemma MonotoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Mf : MonotoneOn f (Ioo y x))
    (h_bdd : BddAbove (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Ioo y x))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, ⟨yz, zx⟩, lz⟩ : ∃ a : α, a ∈ Ioo y x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h_nonempty.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with w hw
    exact lz.trans_le <| Mf ⟨yz, zx⟩ ⟨yz.trans_le hw.1.le, hw.2⟩ hw.1.le
  · rcases h_nonempty with ⟨_, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsLT (hy.trans hx)] with w hw
    exact (le_csSup h_bdd (mem_image_of_mem _ hw)).trans_lt hm

lemma MonotoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo x y).Nonempty) (Mf : MonotoneOn f (Ioo x y))
    (h_bdd : BddBelow (f '' Ioo x y)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioo x y))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · rcases h_nonempty with ⟨p, hy, hx⟩
    filter_upwards [Ioo_mem_nhdsGT (hy.trans hx)] with w hw
    exact hl.trans_le <| csInf_le h_bdd (mem_image_of_mem _ hw)
  · obtain ⟨z, ⟨xz, zy⟩, zm⟩ : ∃ a : α, a ∈ Ioo x y ∧ f a < m := by
      simpa [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_csInf_lt (h_nonempty.image _) hm
    filter_upwards [Ioo_mem_nhdsGT xz] with w hw
    exact (Mf ⟨hw.1, hw.2.trans zy⟩ ⟨xz, zy⟩ hw.2.le).trans_lt zm

lemma MonotoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Mf : MonotoneOn f (Iio x)) (h_bdd : BddAbove (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) := by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : ∃ a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h.image _) hl
    filter_upwards [Ioo_mem_nhdsLT zx] with y hy using lz.trans_le (Mf zx hy.2 hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hy)

lemma MonotoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Mf : MonotoneOn f (Ioi x)) (h_bdd : BddBelow (f '' Ioi x)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  MonotoneOn.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual h_bdd

/-- A monotone map has a limit to the left of any point `x`, equal to `sSup (f '' (Iio x))`. -/
theorem Monotone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsLT (Mf.monotoneOn _) (Mf.map_bddAbove bddAbove_Iio)

/-- A monotone map has a limit to the right of any point `x`, equal to `sInf (f '' (Ioi x))`. -/
theorem Monotone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Mf : Monotone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  Monotone.tendsto_nhdsLT (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual x

lemma AntitoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Af : AntitoneOn f (Ioo y x))
    (h_bdd : BddBelow (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Ioo y x))) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_left h_nonempty Af.dual_right h_bdd

lemma AntitoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo x y).Nonempty) (Af : AntitoneOn f (Ioo x y))
    (h_bdd : BddAbove (f '' Ioo x y)) :
    Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioo x y))) :=
  MonotoneOn.tendsto_nhdsWithin_Ioo_right h_nonempty Af.dual_right h_bdd

lemma AntitoneOn.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Af : AntitoneOn f (Iio x)) (h_bdd : BddBelow (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsLT Af.dual_right h_bdd

lemma AntitoneOn.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β} {x : α}
    (Af : AntitoneOn f (Ioi x)) (h_bdd : BddAbove (f '' Ioi x)) :
    Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioi x))) :=
  MonotoneOn.tendsto_nhdsGT Af.dual_right h_bdd

/-- An antitone map has a limit to the left of any point `x`, equal to `sInf (f '' (Iio x))`. -/
theorem Antitone.tendsto_nhdsLT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Af : Antitone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sInf (f '' Iio x))) :=
  Monotone.tendsto_nhdsLT Af.dual_right x

/-- An antitone map has a limit to the right of any point `x`, equal to `sSup (f '' (Ioi x))`. -/
theorem Antitone.tendsto_nhdsGT {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β] {f : α → β}
    (Af : Antitone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sSup (f '' Ioi x))) :=
  Monotone.tendsto_nhdsGT Af.dual_right x

end ConditionallyCompleteLinearOrder
