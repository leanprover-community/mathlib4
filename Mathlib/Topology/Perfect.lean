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
* `ConnectedSpace.perfectSpace_of_nontrivial_of_t1space`: A T1, connected, nontrivial space is
  perfect.
* `set_infinite_of_perfectSpace`: In a T1 `PerfectSpace`, every nonempty open set must be infinite.

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
variable {X : Type*} [TopologicalSpace X] {s t : Set X}

section Defs

/-- A set `s` is preperfect if all of its points are accumulation points of itself.
If `s` is nonempty and `X` is a T1 space, this is equivalent to the closure of `s` being perfect.
See `preperfect_iff_perfect_closure`.-/
def Preperfect (s : Set X) : Prop :=
  ∀ ⦃x⦄, x ∈ s → AccPt x (𝓟 s)
#align preperfect Preperfect

/-- A set `s` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `s` to be nonempty.-/
structure Perfect (s : Set X) : Prop where
  closed : IsClosed s
  acc : Preperfect s
#align perfect Perfect

variable (X) in
/--
A topological space `X` is said to be perfect if its universe is a perfect set.
Equivalently, this means that `𝓝[≠] x ≠ ⊥` for every point `x : X`.
-/
class PerfectSpace : Prop :=
  univ_perfect' : Perfect (Set.univ : Set X)

variable (X) in
variable [PerfectSpace X] in
theorem PerfectSpace.univ_perfect : Perfect (Set.univ : Set X) := PerfectSpace.univ_perfect'

end Defs

section Preperfect

theorem preperfect_iff_nhds : Preperfect s ↔ ∀ x ∈ s, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ s, y ≠ x := by
  simp only [Preperfect, accPt_iff_nhds]
#align preperfect_iff_nhds preperfect_iff_nhds

theorem Preperfect.nhdsWithin_neBot (s_preperfect : Preperfect s) {x : X} (x_in_s : x ∈ s) :
    Filter.NeBot (𝓝[≠] x) := ⟨fun eq_bot => by
  simpa [AccPt, Filter.neBot_iff, eq_bot, bot_inf_eq] using s_preperfect x_in_s⟩

/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
theorem accPt_principal_iff_inter_of_mem_nhds {x : X} (t_nhds : t ∈ 𝓝 x) :
    AccPt x (𝓟 s) ↔ AccPt x (𝓟 (s ∩ t)) := by
  refine ⟨fun h_acc => ?acc_inter,
    fun h_acc => AccPt.mono h_acc <| Filter.principal_mono.mpr <| Set.inter_subset_left _ _⟩
  have : 𝓝[≠] x ≤ 𝓟 t := le_principal_iff.mpr <| mem_nhdsWithin_of_mem_nhds t_nhds
  rw [AccPt, ← inf_principal, inf_comm (a := 𝓟 s), ← inf_assoc, inf_of_le_left this]
  exact h_acc

/-- The intersection of a preperfect set and an open set is preperfect. -/
theorem Preperfect.open_inter (s_preperfect : Preperfect s) (t_open : IsOpen t) :
    Preperfect (s ∩ t) := fun _ ⟨x_in_s, x_in_t⟩ =>
  (accPt_principal_iff_inter_of_mem_nhds <| t_open.mem_nhds x_in_t).mp (s_preperfect x_in_s)

#align preperfect.open_inter Preperfect.open_inter

/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`. -/
theorem Preperfect.perfect_closure (s_preperfect : Preperfect s) : Perfect (closure s) := by
  constructor; · exact isClosed_closure
  intro x hx
  by_cases h : x ∈ s <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  · exact s_preperfect h
  have : {x}ᶜ ∩ s = s := by simp [h]
  rw [AccPt, nhdsWithin, inf_assoc, inf_principal, this]
  rw [closure_eq_cluster_pts] at hx
  exact hx
#align preperfect.perfect_closure Preperfect.perfect_closure

/-- In a T1 space, being preperfect is equivalent to having perfect closure.-/
theorem preperfect_iff_perfect_closure [T1Space X] : Preperfect s ↔ Perfect (closure s) := by
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

theorem Perfect.closure_nhds_inter (s_perfect : Perfect s) (x : X) (x_in_s : x ∈ s) (x_in_t : x ∈ t)
    (t_open : IsOpen t) : Perfect (closure (t ∩ s)) ∧ (closure (t ∩ s)).Nonempty := ⟨
  Preperfect.perfect_closure <| Set.inter_comm _ _ ▸ s_perfect.acc.open_inter t_open,
  ⟨x, subset_closure ⟨x_in_t, x_in_s⟩⟩⟩
#align perfect.closure_nhds_inter Perfect.closure_nhds_inter

/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets.
This is the main inductive step in the proof of the Cantor-Bendixson Theorem. -/
theorem Perfect.splitting [T25Space X] (s_perfect : Perfect s) (hnonempty : s.Nonempty) :
    ∃ C₀ C₁ : Set X,
    (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ s) ∧ (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ s) ∧ Disjoint C₀ C₁ := by
  cases' hnonempty with y yC
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ s, x ≠ y := by
    have := s_perfect.acc yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  use closure (U ∩ s), closure (V ∩ s)
  constructor <;> rw [← and_assoc]
  · refine' ⟨s_perfect.closure_nhds_inter x xC xU Uop, _⟩
    rw [s_perfect.closed.closure_subset_iff]
    exact inter_subset_right _ _
  constructor
  · refine' ⟨s_perfect.closure_nhds_inter y yC yV Vop, _⟩
    rw [s_perfect.closed.closure_subset_iff]
    exact inter_subset_right _ _
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left _ _
#align perfect.splitting Perfect.splitting

end Splitting

section Kernel

/-- The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.-/
theorem exists_countable_union_perfect_of_isClosed [SecondCountableTopology X]
    (hclosed : IsClosed s) : ∃ V D : Set X, V.Countable ∧ Perfect D ∧ s = V ∪ D := by
  obtain ⟨b, bct, _, bbasis⟩ := TopologicalSpace.exists_countable_basis X
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
theorem exists_perfect_nonempty_of_isClosed_of_not_countable [SecondCountableTopology X]
    (hclosed : IsClosed s) (hunc : ¬s.Countable) : ∃ D : Set X, Perfect D ∧ D.Nonempty ∧ D ⊆ s := by
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

variable [PerfectSpace X] in
instance PerfectSpace.not_isolated (x : X): Filter.NeBot (𝓝[≠] x) := by
  have := (PerfectSpace.univ_perfect X).acc (Set.mem_univ x)
  rwa [AccPt, Filter.principal_univ, inf_top_eq] at this

theorem perfectSpace_iff_forall_not_isolated : PerfectSpace X ↔ ∀ x : X, Filter.NeBot (𝓝[≠] x) :=
  ⟨fun perfect x => perfect.not_isolated x, fun h_forall => ⟨⟨isClosed_univ, fun x _ => by
    rw [AccPt, Filter.principal_univ, inf_top_eq]
    exact h_forall x⟩⟩⟩

variable [PerfectSpace X]

theorem PerfectSpace.preperfect_of_isOpen {s : Set X} (s_open : IsOpen s) : Preperfect s :=
  Set.univ_inter s ▸ (PerfectSpace.univ_perfect X).acc.open_inter s_open

end PerfectSpace

section PerfectSpace.Constructions

/-!
### Constructions of perfect spaces

The product topological space `α × β` is perfect if `α` or `β` is perfect.
-/

variable {β : Type*} [TopologicalSpace β]

theorem nhdsWithin_punctured_prod_neBot_iff {p : X} {q : β} : Filter.NeBot (𝓝[≠] (p, q)) ↔
    Filter.NeBot (𝓝[≠] p) ∨ Filter.NeBot (𝓝[≠] q) := by
  simp_rw [← Set.singleton_prod_singleton, Set.compl_prod_eq_union, nhdsWithin_union,
    nhdsWithin_prod_eq, nhdsWithin_univ, Filter.neBot_iff, ne_eq, sup_eq_bot_iff,
    Filter.prod_eq_bot, Filter.NeBot.ne <| nhds_neBot, or_false, false_or, not_and_or]

variable (α β) in
instance PerfectSpace.prod_left [PerfectSpace X] : PerfectSpace (X × β) :=
  perfectSpace_iff_forall_not_isolated.mpr fun ⟨p, q⟩ => by
    rw [nhdsWithin_punctured_prod_neBot_iff]
    left
    exact PerfectSpace.not_isolated p

variable (α β) in
instance PerfectSpace.prod_right [PerfectSpace β] : PerfectSpace (X × β) :=
  perfectSpace_iff_forall_not_isolated.mpr fun ⟨p, q⟩ => by
    rw [nhdsWithin_punctured_prod_neBot_iff]
    right
    exact PerfectSpace.not_isolated q

/-- A non-trivial connected T1 space has no isolated points. -/
instance (priority := 100) ConnectedSpace.perfectSpace_of_nontrivial_of_t1space
    [PreconnectedSpace X] [Nontrivial X] [T1Space X] : PerfectSpace X := by
  rw [perfectSpace_iff_forall_not_isolated]
  intro x
  by_contra contra
  rw [not_neBot, ← isOpen_singleton_iff_punctured_nhds] at contra
  replace contra := nonempty_inter isOpen_compl_singleton
    contra (compl_union_self _) (Set.nonempty_compl_of_nontrivial _) (singleton_nonempty _)
  simp [compl_inter_self {x}] at contra

end PerfectSpace.Constructions

section PerfectSpace.Infinite
/-!
### Preperfect sets are infinite

Any open pre-perfect set must be infinite.
As a corollary, a perfect space must be infinite (`infinite_of_perfectSpace`) and every nonempty,
open set must be infinite (`set_infinite_of_perfectSpace`).
-/

/--
In a T1 space, nonempty open pre-perfect sets are infinite.
-/
theorem set_infinite_of_preperfect [T1Space X] {s : Set X} (s_preperfect : Preperfect s)
    (s_open : IsOpen s) (s_nonempty : s.Nonempty) : s.Infinite := by
  let ⟨p, p_in_s⟩ := s_nonempty
  have := s_preperfect.nhdsWithin_neBot p_in_s
  apply infinite_of_mem_nhds p
  exact IsOpen.mem_nhds s_open p_in_s

/--
In a T1, perfect space, nonempty open sets are infinite.
-/
theorem set_infinite_of_perfectSpace [T1Space X] [PerfectSpace X] {s : Set X} (s_open : IsOpen s)
    (s_nonempty : s.Nonempty) : s.Infinite :=
  set_infinite_of_preperfect (PerfectSpace.preperfect_of_isOpen s_open) s_open s_nonempty

variable (α) in
/--
If a topological space is perfect, T1 and nonempty, then it is infinite.
-/
theorem PerfectSpace.infinite [T1Space X] [PerfectSpace X] [Nonempty X] : Infinite X :=
  Set.infinite_univ_iff.mp (set_infinite_of_perfectSpace isOpen_univ univ_nonempty)

end PerfectSpace.Infinite

@[deprecated accPt_principal_iff_inter_of_mem_nhds]
theorem AccPt.nhds_inter {x : X} (h_acc : AccPt x (𝓟 s)) (t_nhds : t ∈ 𝓝 x) :
    AccPt x (𝓟 (t ∩ s)) :=
  Set.inter_comm _ _ ▸ (accPt_principal_iff_inter_of_mem_nhds t_nhds).mp h_acc
#align acc_pt.nhds_inter AccPt.nhds_inter
