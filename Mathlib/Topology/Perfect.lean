/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.CantorScheme

#align_import topology.perfect from "leanprover-community/mathlib"@"3905fa80e62c0898131285baab35559fbc4e5cda"

/-!
# Perfect Sets

In this file we define perfect subsets of a topological space, and prove some basic properties,
including a version of the Cantor-Bendixson Theorem.

## Main Definitions

* `Perfect C`: A set `C` is perfect, meaning it is closed and every point of it
  is an accumulation point of itself.

## Main Statements

* `Perfect.splitting`: A perfect nonempty set contains two disjoint perfect nonempty subsets.
  The main inductive step in the construction of an embedding from the Cantor space to a
  perfect nonempty complete metric space.
* `exists_countable_union_perfect_of_isClosed`: One version of the **Cantor-Bendixson Theorem**:
  A closed set in a second countable space can be written as the union of a countable set and a
  perfect set.
* `Perfect.exists_nat_bool_injection`: A perfect nonempty set in a complete metric space
  admits an embedding from the Cantor space.

## Implementation Notes

We do not require perfect sets to be nonempty.

We define a nonstandard predicate, `Preperfect`, which drops the closed-ness requirement
from the definition of perfect. In T1 spaces, this is equivalent to having a perfect closure,
see `preperfect_iff_perfect_closure`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, cantor-bendixson.

-/


open Topology Filter

open TopologicalSpace Filter Set

section Basic

variable {α : Type*} [TopologicalSpace α] {C : Set α}

/-- If `x` is an accumulation point of a set `C` and `U` is a neighborhood of `x`,
then `x` is an accumulation point of `U ∩ C`. -/
theorem AccPt.nhds_inter {x : α} {U : Set α} (h_acc : AccPt x (𝓟 C)) (hU : U ∈ 𝓝 x) :
    AccPt x (𝓟 (U ∩ C)) := by
  have : 𝓝[≠] x ≤ 𝓟 U := by
    rw [le_principal_iff]
    exact mem_nhdsWithin_of_mem_nhds hU
  rw [AccPt, ← inf_principal, ← inf_assoc, inf_of_le_left this]
  -- ⊢ NeBot (𝓝[{x}ᶜ] x ⊓ 𝓟 C)
  exact h_acc
  -- 🎉 no goals
#align acc_pt.nhds_inter AccPt.nhds_inter

/-- A set `C` is preperfect if all of its points are accumulation points of itself.
If `C` is nonempty and `α` is a T1 space, this is equivalent to the closure of `C` being perfect.
See `preperfect_iff_perfect_closure`.-/
def Preperfect (C : Set α) : Prop :=
  ∀ x ∈ C, AccPt x (𝓟 C)
#align preperfect Preperfect

/-- A set `C` is called perfect if it is closed and all of its
points are accumulation points of itself.
Note that we do not require `C` to be nonempty.-/
structure Perfect (C : Set α) : Prop where
  closed : IsClosed C
  acc : Preperfect C
#align perfect Perfect

theorem preperfect_iff_nhds : Preperfect C ↔ ∀ x ∈ C, ∀ U ∈ 𝓝 x, ∃ y ∈ U ∩ C, y ≠ x := by
  simp only [Preperfect, accPt_iff_nhds]
  -- 🎉 no goals
#align preperfect_iff_nhds preperfect_iff_nhds

/-- The intersection of a preperfect set and an open set is preperfect. -/
theorem Preperfect.open_inter {U : Set α} (hC : Preperfect C) (hU : IsOpen U) :
    Preperfect (U ∩ C) := by
  rintro x ⟨xU, xC⟩
  -- ⊢ AccPt x (𝓟 (U ∩ C))
  apply (hC _ xC).nhds_inter
  -- ⊢ U ∈ 𝓝 x
  exact hU.mem_nhds xU
  -- 🎉 no goals
#align preperfect.open_inter Preperfect.open_inter

/-- The closure of a preperfect set is perfect.
For a converse, see `preperfect_iff_perfect_closure`. -/
theorem Preperfect.perfect_closure (hC : Preperfect C) : Perfect (closure C) := by
  constructor; · exact isClosed_closure
  -- ⊢ IsClosed (closure C)
                 -- 🎉 no goals
  intro x hx
  -- ⊢ AccPt x (𝓟 (closure C))
  by_cases h : x ∈ C <;> apply AccPt.mono _ (principal_mono.mpr subset_closure)
  -- ⊢ AccPt x (𝓟 (closure C))
                         -- ⊢ AccPt x (𝓟 C)
                         -- ⊢ AccPt x (𝓟 C)
  · exact hC _ h
    -- 🎉 no goals
  have : {x}ᶜ ∩ C = C := by simp [h]
  -- ⊢ AccPt x (𝓟 C)
  rw [AccPt, nhdsWithin, inf_assoc, inf_principal, this]
  -- ⊢ NeBot (𝓝 x ⊓ 𝓟 C)
  rw [closure_eq_cluster_pts] at hx
  -- ⊢ NeBot (𝓝 x ⊓ 𝓟 C)
  exact hx
  -- 🎉 no goals
#align preperfect.perfect_closure Preperfect.perfect_closure

/-- In a T1 space, being preperfect is equivalent to having perfect closure.-/
theorem preperfect_iff_perfect_closure [T1Space α] : Preperfect C ↔ Perfect (closure C) := by
  constructor <;> intro h
  -- ⊢ Preperfect C → Perfect (closure C)
                  -- ⊢ Perfect (closure C)
                  -- ⊢ Preperfect C
  · exact h.perfect_closure
    -- 🎉 no goals
  intro x xC
  -- ⊢ AccPt x (𝓟 C)
  have H : AccPt x (𝓟 (closure C)) := h.acc _ (subset_closure xC)
  -- ⊢ AccPt x (𝓟 C)
  rw [accPt_iff_frequently] at *
  -- ⊢ ∃ᶠ (y : α) in 𝓝 x, y ≠ x ∧ y ∈ C
  have : ∀ y, y ≠ x ∧ y ∈ closure C → ∃ᶠ z in 𝓝 y, z ≠ x ∧ z ∈ C := by
    rintro y ⟨hyx, yC⟩
    simp only [← mem_compl_singleton_iff, and_comm, ← frequently_nhdsWithin_iff,
      hyx.nhdsWithin_compl_singleton, ← mem_closure_iff_frequently]
    exact yC
  rw [← frequently_frequently_nhds]
  -- ⊢ ∃ᶠ (y : α) in 𝓝 x, ∃ᶠ (x_1 : α) in 𝓝 y, x_1 ≠ x ∧ x_1 ∈ C
  exact H.mono this
  -- 🎉 no goals
#align preperfect_iff_perfect_closure preperfect_iff_perfect_closure

theorem Perfect.closure_nhds_inter {U : Set α} (hC : Perfect C) (x : α) (xC : x ∈ C) (xU : x ∈ U)
    (Uop : IsOpen U) : Perfect (closure (U ∩ C)) ∧ (closure (U ∩ C)).Nonempty := by
  constructor
  -- ⊢ Perfect (closure (U ∩ C))
  · apply Preperfect.perfect_closure
    -- ⊢ Preperfect (U ∩ C)
    exact hC.acc.open_inter Uop
    -- 🎉 no goals
  apply Nonempty.closure
  -- ⊢ Set.Nonempty (U ∩ C)
  exact ⟨x, ⟨xU, xC⟩⟩
  -- 🎉 no goals
#align perfect.closure_nhds_inter Perfect.closure_nhds_inter

/-- Given a perfect nonempty set in a T2.5 space, we can find two disjoint perfect subsets.
This is the main inductive step in the proof of the Cantor-Bendixson Theorem. -/
theorem Perfect.splitting [T25Space α] (hC : Perfect C) (hnonempty : C.Nonempty) :
    ∃ C₀ C₁ : Set α,
    (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ C) ∧ (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ C) ∧ Disjoint C₀ C₁ := by
  cases' hnonempty with y yC
  -- ⊢ ∃ C₀ C₁, (Perfect C₀ ∧ Set.Nonempty C₀ ∧ C₀ ⊆ C) ∧ (Perfect C₁ ∧ Set.Nonempt …
  obtain ⟨x, xC, hxy⟩ : ∃ x ∈ C, x ≠ y := by
    have := hC.acc _ yC
    rw [accPt_iff_nhds] at this
    rcases this univ univ_mem with ⟨x, xC, hxy⟩
    exact ⟨x, xC.2, hxy⟩
  obtain ⟨U, xU, Uop, V, yV, Vop, hUV⟩ := exists_open_nhds_disjoint_closure hxy
  -- ⊢ ∃ C₀ C₁, (Perfect C₀ ∧ Set.Nonempty C₀ ∧ C₀ ⊆ C) ∧ (Perfect C₁ ∧ Set.Nonempt …
  use closure (U ∩ C), closure (V ∩ C)
  -- ⊢ (Perfect (closure (U ∩ C)) ∧ Set.Nonempty (closure (U ∩ C)) ∧ closure (U ∩ C …
  constructor <;> rw [← and_assoc]
  -- ⊢ Perfect (closure (U ∩ C)) ∧ Set.Nonempty (closure (U ∩ C)) ∧ closure (U ∩ C) …
                  -- ⊢ (Perfect (closure (U ∩ C)) ∧ Set.Nonempty (closure (U ∩ C))) ∧ closure (U ∩  …
                  -- ⊢ ((Perfect (closure (V ∩ C)) ∧ Set.Nonempty (closure (V ∩ C))) ∧ closure (V ∩ …
  · refine' ⟨hC.closure_nhds_inter x xC xU Uop, _⟩
    -- ⊢ closure (U ∩ C) ⊆ C
    rw [hC.closed.closure_subset_iff]
    -- ⊢ U ∩ C ⊆ C
    exact inter_subset_right _ _
    -- 🎉 no goals
  constructor
  -- ⊢ (Perfect (closure (V ∩ C)) ∧ Set.Nonempty (closure (V ∩ C))) ∧ closure (V ∩  …
  · refine' ⟨hC.closure_nhds_inter y yC yV Vop, _⟩
    -- ⊢ closure (V ∩ C) ⊆ C
    rw [hC.closed.closure_subset_iff]
    -- ⊢ V ∩ C ⊆ C
    exact inter_subset_right _ _
    -- 🎉 no goals
  apply Disjoint.mono _ _ hUV <;> apply closure_mono <;> exact inter_subset_left _ _
  -- ⊢ closure (U ∩ C) ≤ closure U
                                  -- ⊢ U ∩ C ⊆ U
                                  -- ⊢ V ∩ C ⊆ V
                                                         -- 🎉 no goals
                                                         -- 🎉 no goals
#align perfect.splitting Perfect.splitting

section Kernel

/-- The **Cantor-Bendixson Theorem**: Any closed subset of a second countable space
can be written as the union of a countable set and a perfect set.-/
theorem exists_countable_union_perfect_of_isClosed [SecondCountableTopology α]
    (hclosed : IsClosed C) : ∃ V D : Set α, V.Countable ∧ Perfect D ∧ C = V ∪ D := by
  obtain ⟨b, bct, _, bbasis⟩ := TopologicalSpace.exists_countable_basis α
  -- ⊢ ∃ V D, Set.Countable V ∧ Perfect D ∧ C = V ∪ D
  let v := { U ∈ b | (U ∩ C).Countable }
  -- ⊢ ∃ V D, Set.Countable V ∧ Perfect D ∧ C = V ∪ D
  let V := ⋃ U ∈ v, U
  -- ⊢ ∃ V D, Set.Countable V ∧ Perfect D ∧ C = V ∪ D
  let D := C \ V
  -- ⊢ ∃ V D, Set.Countable V ∧ Perfect D ∧ C = V ∪ D
  have Vct : (V ∩ C).Countable := by
    simp only [iUnion_inter, mem_sep_iff]
    apply Countable.biUnion
    · exact Countable.mono (inter_subset_left _ _) bct
    · exact inter_subset_right _ _
  refine' ⟨V ∩ C, D, Vct, ⟨_, _⟩, _⟩
  · refine' hclosed.sdiff (isOpen_biUnion fun _ ↦ _)
    -- ⊢ x✝ ∈ v → IsOpen x✝
    exact fun ⟨Ub, _⟩ ↦ IsTopologicalBasis.isOpen bbasis Ub
    -- 🎉 no goals
  · rw [preperfect_iff_nhds]
    -- ⊢ ∀ (x : α), x ∈ D → ∀ (U : Set α), U ∈ 𝓝 x → ∃ y, y ∈ U ∩ D ∧ y ≠ x
    intro x xD E xE
    -- ⊢ ∃ y, y ∈ E ∩ D ∧ y ≠ x
    have : ¬(E ∩ D).Countable := by
      intro h
      obtain ⟨U, hUb, xU, hU⟩ : ∃ U ∈ b, x ∈ U ∧ U ⊆ E :=
        (IsTopologicalBasis.mem_nhds_iff bbasis).mp xE
      have hU_cnt : (U ∩ C).Countable := by
        apply @Countable.mono _ _ (E ∩ D ∪ V ∩ C)
        · rintro y ⟨yU, yC⟩
          by_cases h : y ∈ V
          · exact mem_union_right _ (mem_inter h yC)
          · exact mem_union_left _ (mem_inter (hU yU) ⟨yC, h⟩)
        exact Countable.union h Vct
      have : U ∈ v := ⟨hUb, hU_cnt⟩
      apply xD.2
      exact mem_biUnion this xU
    by_contra' h
    -- ⊢ False
    exact absurd (Countable.mono h (Set.countable_singleton _)) this
    -- 🎉 no goals
  · rw [inter_comm, inter_union_diff]
    -- 🎉 no goals
#align exists_countable_union_perfect_of_is_closed exists_countable_union_perfect_of_isClosed

/-- Any uncountable closed set in a second countable space contains a nonempty perfect subset.-/
theorem exists_perfect_nonempty_of_isClosed_of_not_countable [SecondCountableTopology α]
    (hclosed : IsClosed C) (hunc : ¬C.Countable) : ∃ D : Set α, Perfect D ∧ D.Nonempty ∧ D ⊆ C := by
  rcases exists_countable_union_perfect_of_isClosed hclosed with ⟨V, D, Vct, Dperf, VD⟩
  -- ⊢ ∃ D, Perfect D ∧ Set.Nonempty D ∧ D ⊆ C
  refine' ⟨D, ⟨Dperf, _⟩⟩
  -- ⊢ Set.Nonempty D ∧ D ⊆ C
  constructor
  -- ⊢ Set.Nonempty D
  · rw [nonempty_iff_ne_empty]
    -- ⊢ D ≠ ∅
    by_contra h
    -- ⊢ False
    rw [h, union_empty] at VD
    -- ⊢ False
    rw [VD] at hunc
    -- ⊢ False
    contradiction
    -- 🎉 no goals
  rw [VD]
  -- ⊢ D ⊆ V ∪ D
  exact subset_union_right _ _
  -- 🎉 no goals
#align exists_perfect_nonempty_of_is_closed_of_not_countable exists_perfect_nonempty_of_isClosed_of_not_countable

end Kernel

end Basic

section CantorInjMetric

open Function ENNReal

variable {α : Type*} [MetricSpace α] {C : Set α} (hC : Perfect C) {ε : ℝ≥0∞}

private theorem Perfect.small_diam_aux (ε_pos : 0 < ε) {x : α} (xC : x ∈ C) :
    let D := closure (EMetric.ball x (ε / 2) ∩ C)
    Perfect D ∧ D.Nonempty ∧ D ⊆ C ∧ EMetric.diam D ≤ ε := by
  have : x ∈ EMetric.ball x (ε / 2) := by
    apply EMetric.mem_ball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt ε_pos, by norm_num⟩
  have := hC.closure_nhds_inter x xC this EMetric.isOpen_ball
  -- ⊢ let D := closure (EMetric.ball x (ε / 2) ∩ C);
  refine' ⟨this.1, this.2, _, _⟩
  -- ⊢ closure (EMetric.ball x (ε / 2) ∩ C) ⊆ C
  · rw [IsClosed.closure_subset_iff hC.closed]
    -- ⊢ EMetric.ball x (ε / 2) ∩ C ⊆ C
    apply inter_subset_right
    -- 🎉 no goals
  rw [EMetric.diam_closure]
  -- ⊢ EMetric.diam (EMetric.ball x (ε / 2) ∩ C) ≤ ε
  apply le_trans (EMetric.diam_mono (inter_subset_left _ _))
  -- ⊢ EMetric.diam (EMetric.ball x (ε / 2)) ≤ ε
  convert EMetric.diam_ball (x := x)
  -- ⊢ ε = 2 * (ε / 2)
  rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num
  -- ⊢ 2 ≠ 0
                                            -- 🎉 no goals
                                            -- 🎉 no goals

variable (hnonempty : C.Nonempty)

/-- A refinement of `Perfect.splitting` for metric spaces, where we also control
the diameter of the new perfect sets. -/
theorem Perfect.small_diam_splitting (ε_pos : 0 < ε) :
    ∃ C₀ C₁ : Set α, (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧
    (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ C ∧ EMetric.diam C₁ ≤ ε) ∧ Disjoint C₀ C₁ := by
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩
  -- ⊢ ∃ C₀ C₁, (Perfect C₀ ∧ Set.Nonempty C₀ ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧ (Pe …
  cases' non0 with x₀ hx₀
  -- ⊢ ∃ C₀ C₁, (Perfect C₀ ∧ Set.Nonempty C₀ ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧ (Pe …
  cases' non1 with x₁ hx₁
  -- ⊢ ∃ C₀ C₁, (Perfect C₀ ∧ Set.Nonempty C₀ ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧ (Pe …
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩
  -- ⊢ ∃ C₀ C₁, (Perfect C₀ ∧ Set.Nonempty C₀ ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧ (Pe …
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1⟩
  -- ⊢ ∃ C₀ C₁, (Perfect C₀ ∧ Set.Nonempty C₀ ∧ C₀ ⊆ C ∧ EMetric.diam C₀ ≤ ε) ∧ (Pe …
  refine'
    ⟨closure (EMetric.ball x₀ (ε / 2) ∩ D₀), closure (EMetric.ball x₁ (ε / 2) ∩ D₁),
      ⟨perf0', non0', sub0'.trans sub0, diam0⟩, ⟨perf1', non1', sub1'.trans sub1, diam1⟩, _⟩
  apply Disjoint.mono _ _ hdisj <;> assumption
  -- ⊢ closure (EMetric.ball x₀ (ε / 2) ∩ D₀) ≤ D₀
                                    -- 🎉 no goals
                                    -- 🎉 no goals
#align perfect.small_diam_splitting Perfect.small_diam_splitting

open CantorScheme

/-- Any nonempty perfect set in a complete metric space admits a continuous injection
from the Cantor space, `ℕ → Bool`. -/
theorem Perfect.exists_nat_bool_injection [CompleteSpace α] :
    ∃ f : (ℕ → Bool) → α, range f ⊆ C ∧ Continuous f ∧ Injective f := by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  -- ⊢ ∃ f, range f ⊆ C ∧ Continuous f ∧ Injective f
  have upos := fun n => (upos' n).1
  -- ⊢ ∃ f, range f ⊆ C ∧ Continuous f ∧ Injective f
  let P := Subtype fun E : Set α => Perfect E ∧ E.Nonempty
  -- ⊢ ∃ f, range f ⊆ C ∧ Continuous f ∧ Injective f
  choose C0 C1 h0 h1 hdisj using
    fun {C : Set α} (hC : Perfect C) (hnonempty : C.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) =>
    hC.small_diam_splitting hnonempty hε
  let DP : List Bool → P := fun l => by
    induction' l with a l ih; · exact ⟨C, ⟨hC, hnonempty⟩⟩
    cases a
    · use C0 ih.property.1 ih.property.2 (upos l.length.succ)
      exact ⟨(h0 _ _ _).1, (h0 _ _ _).2.1⟩
    use C1 ih.property.1 ih.property.2 (upos l.length.succ)
    exact ⟨(h1 _ _ _).1, (h1 _ _ _).2.1⟩
  let D : List Bool → Set α := fun l => (DP l).val
  -- ⊢ ∃ f, range f ⊆ C ∧ Continuous f ∧ Injective f
  have hanti : ClosureAntitone D := by
    refine' Antitone.closureAntitone _ fun l => (DP l).property.1.closed
    intro l a
    cases a
    · exact (h0 _ _ _).2.2.1
    exact (h1 _ _ _).2.2.1
  have hdiam : VanishingDiam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_atTop]
    refine' ⟨1, fun m (hm : 1 ≤ m) => _⟩
    rw [Nat.one_le_iff_ne_zero] at hm
    rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
    dsimp
    cases x n
    · convert(h0 _ _ _).2.2.2
      rw [PiNat.res_length]
    convert(h1 _ _ _).2.2.2
    rw [PiNat.res_length]
  have hdisj' : CantorScheme.Disjoint D := by
    rintro l (a | a) (b | b) hab <;> try contradiction
    · exact hdisj _ _ _
    exact (hdisj _ _ _).symm
  have hdom : ∀ {x : ℕ → Bool}, x ∈ (inducedMap D).1 := fun {x} => by
    rw [hanti.map_of_vanishingDiam hdiam fun l => (DP l).property.2]
    apply mem_univ
  refine' ⟨fun x => (inducedMap D).2 ⟨x, hdom⟩, _, _, _⟩
  · rintro y ⟨x, rfl⟩
    -- ⊢ (fun x => Sigma.snd (inducedMap D) { val := x, property := (_ : x ∈ (induced …
    exact map_mem ⟨_, hdom⟩ 0
    -- 🎉 no goals
  · apply hdiam.map_continuous.comp
    -- ⊢ Continuous fun x => { val := x, property := (_ : x ∈ (inducedMap D).fst) }
    continuity
    -- 🎉 no goals
  intro x y hxy
  -- ⊢ x = y
  simpa only [← Subtype.val_inj] using hdisj'.map_injective hxy
  -- 🎉 no goals
#align perfect.exists_nat_bool_injection Perfect.exists_nat_bool_injection

end CantorInjMetric

/-- Any closed uncountable subset of a Polish space admits a continuous injection
from the Cantor space `ℕ → Bool`.-/
theorem IsClosed.exists_nat_bool_injection_of_not_countable {α : Type*} [TopologicalSpace α]
    [PolishSpace α] {C : Set α} (hC : IsClosed C) (hunc : ¬C.Countable) :
    ∃ f : (ℕ → Bool) → α, range f ⊆ C ∧ Continuous f ∧ Function.Injective f := by
  letI := upgradePolishSpace α
  -- ⊢ ∃ f, range f ⊆ C ∧ Continuous f ∧ Function.Injective f
  obtain ⟨D, hD, Dnonempty, hDC⟩ := exists_perfect_nonempty_of_isClosed_of_not_countable hC hunc
  -- ⊢ ∃ f, range f ⊆ C ∧ Continuous f ∧ Function.Injective f
  obtain ⟨f, hfD, hf⟩ := hD.exists_nat_bool_injection Dnonempty
  -- ⊢ ∃ f, range f ⊆ C ∧ Continuous f ∧ Function.Injective f
  exact ⟨f, hfD.trans hDC, hf⟩
  -- 🎉 no goals
#align is_closed.exists_nat_bool_injection_of_not_countable IsClosed.exists_nat_bool_injection_of_not_countable
