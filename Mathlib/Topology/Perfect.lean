/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher, Emilie Burgun
-/

import Mathlib.Topology.Separation

#align_import topology.perfect from "leanprover-community/mathlib"@"3905fa80e62c0898131285baab35559fbc4e5cda"

/-!
# Perfect Sets

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `Perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.
* `PerfectSpace X`: A topological space `X` is perfect if its universe is a perfect set.

## Main Statements

* `Perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_isClosed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.

## Implementation Notes

We do not require perfect sets to be nonempty.

We define a nonstandard predicate, `Preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## See also

`Mathlib.Topology.MetricSpace.Perfect`, for properties of perfect sets in metric spaces,
namely Polish spaces.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, cantor-bendixson.

-/


open Topology Filter Set
open TopologicalSpace (IsTopologicalBasis)
variable {α : Type*} [TopologicalSpace α] {s t : Set α}

section Defs

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `C` is nonempty and `α` is a T1 space, this is equivalent to the closure of `C` being perfect.
See `preperfect_iff_perfect_closure`.-/
def Preperfect (C : Set α) : Prop :=
  ∀ ⦃x⦄, x ∈ C → AccPt x (𝓟 C)
#align preperfect Preperfect

/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty.-/
structure Perfect (C : Set α) : Prop where
  closed : IsClosed C
  acc : Preperfect C
#align perfect Perfect

theorem preperfect_iff_nhds : Preperfect s ↔ ∀ x ∈ s, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ s, y ≠ x := by
  simp only [Preperfect, accPt_iff_nhds]
#align preperfect_iff_nhds preperfect_iff_nhds

/--
A topological space `X` is said to be perfect if its universe is a perfect set.
Equivalently, this means that `𝓝[≠] x ≠ ⊥` for every point `x : X`.
-/
class PerfectSpace (X : Type*) [TopologicalSpace X]: Prop :=
  univ_perfect' : Perfect (Set.univ : Set X)

variable [PerfectSpace α] in
variable (α) in
theorem PerfectSpace.univ_perfect : Perfect (Set.univ : Set α) := PerfectSpace.univ_perfect'

end Defs

section Preperfect

/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
theorem accPt_principal_iff_inter_of_mem_nhds {x : α} (t_nhds : t ∈ 𝓝 x) :
    AccPt x (𝓟 s) ↔ AccPt x (𝓟 (s ∩ t)) := by
  refine ⟨fun h_acc => ?acc_inter,
    fun h_acc => AccPt.mono h_acc <| Filter.principal_mono.mpr <| Set.inter_subset_left _ _⟩
  have : 𝓝[≠] x ≤ 𝓟 t := le_principal_iff.mpr <| mem_nhdsWithin_of_mem_nhds t_nhds
  rw [AccPt, ← inf_principal, inf_comm (a := 𝓟 s), ← inf_assoc, inf_of_le_left this]
  exact h_acc

/-- The intersection of a preperfect set and an open set is preperfect. -/
theorem Preperfect.open_inter (s_prePerfect : Preperfect s) (t_open : IsOpen t) :
    Preperfect (s ∩ t) := fun _ ⟨x_in_s, x_in_t⟩ =>
  (accPt_principal_iff_inter_of_mem_nhds <| t_open.mem_nhds x_in_t).mp (s_prePerfect x_in_s)

#align preperfect.open_inter Preperfect.open_inter

/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`. -/
theorem Preperfect.perfect_closure (s_prePerfect : Preperfect s) : Perfect (closure s) := by
  constructor; · exact isClosed_closure
  intro x hx
  by_cases h : x ∈ s <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  · exact s_prePerfect h
  have : {x}ᶜ ∩ s = s := by simp [h]
  rw [AccPt, nhdsWithin, inf_assoc, inf_principal, this]
  rw [closure_eq_cluster_pts] at hx
  exact hx
#align preperfect.perfect_closure Preperfect.perfect_closure

/-- In a T1 space, being preperfect is equivalent to having perfect closure.-/
theorem preperfect_iff_perfect_closure [T1Space α] : Preperfect s ↔ Perfect (closure s) := by
  constructor <;> intro h
  · exact h.perfect_closure
  intro x xC
  have H : AccPt x (𝓟 (closure s)) := h.acc (subset_closure xC)
  rw [accPt_iff_frequently] at *
  have : ∀ y, y ≠ x ∧ y ∈ closure s → ∃ᶠ z in 𝓝 y, z ≠ x ∧ z ∈ s := by
    rintro y ⟨hyx, yC⟩
    simp only [← mem_compl_singleton_iff, and_comm, ← frequently_nhdsWithin_iff,
      hyx.nhdsWithin_compl_singleton, ← mem_closure_iff_frequently]
    exact yC
  rw [← frequently_frequently_nhds]
  exact H.mono this
#align preperfect_iff_perfect_closure preperfect_iff_perfect_closure

end Preperfect

section Splitting

theorem Perfect.closure_nhds_inter (s_perfect : Perfect s) (x : α) (x_in_s : x ∈ s) (x_in_t : x ∈ t)
    (t_open : IsOpen t) : Perfect (closure (t ∩ s)) ∧ (closure (t ∩ s)).Nonempty := ⟨
  Preperfect.perfect_closure <| Set.inter_comm _ _ ▸ s_perfect.acc.open_inter t_open,
  ⟨x, subset_closure ⟨x_in_t, x_in_s⟩⟩⟩
#align perfect.closure_nhds_inter Perfect.closure_nhds_inter

/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets.
This is the main inductive step in the proof of the Cantor-Bendixson Theorem. -/
theorem Perfect.splitting [T25Space α] (hC : Perfect s) (hnonempty : s.Nonempty) :
    ∃ C₀ C₁ : Set α,
    (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ s) ∧ (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ s) ∧ Disjoint C₀ C₁ := by
  cases' hnonempty with y yC
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ s, x ≠ y := by
    have := hC.acc yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  use closure (U ∩ s), closure (V ∩ s)
  constructor <;> rw [← and_assoc]
  · refine' ⟨hC.closure_nhds_inter x xC xU Uop, _⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right _ _
  constructor
  · refine' ⟨hC.closure_nhds_inter y yC yV Vop, _⟩
    rw [hC.closed.closure_subset_iff]
    exact inter_subset_right _ _
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left _ _
#align perfect.splitting Perfect.splitting

end Splitting

section Kernel

/-- The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.-/
theorem exists_countable_union_perfect_of_isClosed [SecondCountableTopology α]
    (hclosed : IsClosed s) : ∃ V D : Set α, V.Countable ∧ Perfect D ∧ s = V ∪ D := by
  obtain ⟨b, bct, _, bbasis⟩ := TopologicalSpace.exists_countable_basis α
  let v := { U ∈ b | (U ∩ s).Countable }
  let V := ⋃ U ∈ v, U
  let D := s \ V
  have Vct : (V ∩ s).Countable := by
    simp only [iUnion_inter, mem_sep_iff]
    apply Countable.biUnion
    · exact Countable.mono (inter_subset_left _ _) bct
    · exact inter_subset_right _ _
  refine' ⟨V ∩ s, D, Vct, ⟨_, _⟩, _⟩
  · refine' hclosed.sdiff (isOpen_biUnion fun _ ↦ _)
    exact fun ⟨Ub, _⟩ ↦ IsTopologicalBasis.isOpen bbasis Ub
  · rw [preperfect_iff_nhds]
    intro x xD E xE
    have : ¬(E ∩ D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E :=
        (IsTopologicalBasis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U ∩ s).Countable := by
        apply @Countable.mono _ _ (E ∩ D ∪ V ∩ s)
        · rintro y ⟨yU, yC⟩
          by_cases h : y ∈ V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact Countable.union h Vct
      have : U ∈ v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_biUnion this xU
    by_contra! h
    exact absurd (Countable.mono h (Set.countable_singleton _)) this
  · rw [inter_comm, inter_union_diff]
#align exists_countable_union_perfect_of_is_closed exists_countable_union_perfect_of_isClosed

/-- Any uncountable closed set in a second countable space contains a nonempty perfect subset.-/
theorem exists_perfect_nonempty_of_isClosed_of_not_countable [SecondCountableTopology α]
    (hclosed : IsClosed s) (hunc : ¬s.Countable) : ∃ D : Set α, Perfect D ∧ D.Nonempty ∧ D ⊆ s := by
  rcases exists_countable_union_perfect_of_isClosed hclosed with ⟨V, D, Vct, Dperf, VD⟩
  refine' ⟨D, ⟨Dperf, _⟩⟩
  constructor
  · rw [nonempty_iff_ne_empty]
    by_contra h
    rw [h, union_empty] at VD
    rw [VD] at hunc
    contradiction
  rw [VD]
  exact subset_union_right _ _
#align exists_perfect_nonempty_of_is_closed_of_not_countable exists_perfect_nonempty_of_isClosed_of_not_countable

end Kernel

section PerfectSpace

theorem perfectSpace_of_forall_not_isolated (h_forall : ∀ x : α, Filter.NeBot (𝓝[≠] x)) :
    PerfectSpace α := ⟨⟨isClosed_univ, fun x _ => by
  rw [AccPt, Filter.principal_univ, inf_top_eq]
  exact h_forall x⟩⟩

variable [PerfectSpace α]

instance PerfectSpace.not_isolated (x : α): Filter.NeBot (𝓝[≠] x) := by
  have := (PerfectSpace.univ_perfect α).acc (Set.mem_univ x)
  rwa [AccPt, Filter.principal_univ, inf_top_eq] at this

end PerfectSpace

section PerfectSpace.Prod

variable {β : Type*} [TopologicalSpace β]

theorem nhdsWithin_punctured_prod_neBot_iff' {p : α} {q : β} : Filter.NeBot (𝓝[≠] (p, q)) ↔
    Filter.NeBot (𝓝[≠] p) ∨ Filter.NeBot (𝓝[≠] q) := by
  simp_rw [← Set.singleton_prod_singleton, Set.compl_prod_eq_union, nhdsWithin_union,
    nhdsWithin_prod_eq, nhdsWithin_univ, Filter.neBot_iff, ne_eq, sup_eq_bot_iff,
    Filter.prod_eq_bot, Filter.NeBot.ne <| nhds_neBot, or_false, false_or, not_and_or]

variable (α β) in
instance PerfectSpace.prod_left [PerfectSpace α] : PerfectSpace (α × β) :=
  perfectSpace_of_forall_not_isolated fun ⟨p, q⟩ => by
    rw [nhdsWithin_punctured_prod_neBot_iff]
    left
    exact PerfectSpace.not_isolated p

variable (α β) in
instance PerfectSpace.prod_right [PerfectSpace β] : PerfectSpace (α × β) :=
  perfectSpace_of_forall_not_isolated fun ⟨p, q⟩ => by
    rw [nhdsWithin_punctured_prod_neBot_iff]
    right
    exact PerfectSpace.not_isolated q

end PerfectSpace.Prod

@[deprecated accPt_principal_iff_inter_of_mem_nhds]
theorem AccPt.nhds_inter {x : α} (h_acc : AccPt x (𝓟 s)) (t_nhds : t ∈ 𝓝 x) :
    AccPt x (𝓟 (t ∩ s)) :=
  Set.inter_comm _ _ ▸ (accPt_principal_iff_inter_of_mem_nhds t_nhds).mp h_acc
#align acc_pt.nhds_inter AccPt.nhds_inter
