/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.GDelta.Basic

/-!
# Separation properties of topological spaces.

## Main definitions

* `PerfectlyNormalSpace`: A perfectly normal space is a normal space such that
  closed sets are Gδ.
* `T6Space`: A T₆ space is a perfectly normal T₀ space. T₆ implies T₅.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u

variable {X : Type*} [TopologicalSpace X]

section Separation

/-- Urysohn's lemma: a topological space `X` is normal if for any two disjoint closed sets `s` and
`t` there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`.
-/
lemma NormalSpace.of_separating {X} [TopologicalSpace X]
    (sep : {U V : Set X} → IsClosed U → IsClosed V → Disjoint U V →
      { f : C(X, ℝ) // EqOn f 0 U ∧ EqOn f 1 V }) : NormalSpace X where
  normal {s t} sC tC disj := by
    obtain ⟨f, hf₀, hf₁⟩ := sep sC tC disj
    use f ⁻¹' (Iio 0.5), f ⁻¹' (Ioi 0.5), isOpen_Iio.preimage f.continuous,
      isOpen_Ioi.preimage f.continuous
    split_ands
    · intro x hxs; simp [hf₀ hxs]; linarith
    · intro x hxt; simp [hf₁ hxt]; linarith
    · apply Disjoint.preimage; simp

theorem IsGδ.compl_singleton (x : X) [T1Space X] : IsGδ ({x}ᶜ : Set X) :=
  isOpen_compl_singleton.isGδ

lemma IsGδ.preimage {X Y} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ContinuousMap X Y) {s : Set Y} (hs : IsGδ s) : IsGδ (f ⁻¹' s) := by
  rcases hs with ⟨T, To, cardT, hsT⟩
  use Set.preimage f '' T
  split_ands
  · rintro _ ⟨t, ht, rfl⟩; exact (To t ht).preimage f.continuous
  · exact Countable.image cardT (Set.preimage ⇑f)
  · simp [hsT]

theorem Set.Countable.isGδ_compl {s : Set X} [T1Space X] (hs : s.Countable) : IsGδ sᶜ := by
  rw [← biUnion_of_singleton s, compl_iUnion₂]
  exact .biInter hs fun x _ => .compl_singleton x

theorem Set.Finite.isGδ_compl {s : Set X} [T1Space X] (hs : s.Finite) : IsGδ sᶜ :=
  hs.countable.isGδ_compl

theorem Set.Subsingleton.isGδ_compl {s : Set X} [T1Space X] (hs : s.Subsingleton) : IsGδ sᶜ :=
  hs.finite.isGδ_compl

theorem Finset.isGδ_compl [T1Space X] (s : Finset X) : IsGδ (sᶜ : Set X) :=
  s.finite_toSet.isGδ_compl

protected theorem IsGδ.singleton [FirstCountableTopology X] [T1Space X] (x : X) :
    IsGδ ({x} : Set X) := by
  rcases (nhds_basis_opens x).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  exact .biInter (to_countable _) fun n _ => (hU n).2.isGδ


theorem Set.Finite.isGδ [FirstCountableTopology X] {s : Set X} [T1Space X] (hs : s.Finite) :
    IsGδ s :=
  Finite.induction_on _ hs .empty fun _ _ ↦ .union (.singleton _)


section PerfectlyNormal

/-- A topological space `X` is a *perfectly normal space* provided it is normal and
closed sets are Gδ. -/
class PerfectlyNormalSpace (X : Type u) [TopologicalSpace X] : Prop extends NormalSpace X where
    closed_gdelta : ∀ ⦃h : Set X⦄, IsClosed h → IsGδ h

/-- Lemma that allows the easy conclusion that perfectly normal spaces are completely normal. -/
theorem Disjoint.hasSeparatingCover_closed_gdelta_right {s t : Set X} [NormalSpace X]
    (st_dis : Disjoint s t) (t_cl : IsClosed t) (t_gd : IsGδ t) : HasSeparatingCover s t := by
  obtain ⟨T, T_open, T_count, T_int⟩ := t_gd
  rcases T.eq_empty_or_nonempty with rfl | T_nonempty
  · rw [T_int, sInter_empty] at st_dis
    rw [(s.disjoint_univ).mp st_dis]
    exact t.hasSeparatingCover_empty_left
  obtain ⟨g, g_surj⟩ := T_count.exists_surjective T_nonempty
  choose g' g'_open clt_sub_g' clg'_sub_g using fun n ↦ by
    apply normal_exists_closure_subset t_cl (T_open (g n).1 (g n).2)
    rw [T_int]
    exact sInter_subset_of_mem (g n).2
  have clg'_int : t = ⋂ i, closure (g' i) := by
    apply (subset_iInter fun n ↦ (clt_sub_g' n).trans subset_closure).antisymm
    rw [T_int]
    refine subset_sInter fun t tinT ↦ ?_
    obtain ⟨n, gn⟩ := g_surj ⟨t, tinT⟩
    refine iInter_subset_of_subset n <| (clg'_sub_g n).trans ?_
    rw [gn]
  use fun n ↦ (closure (g' n))ᶜ
  constructor
  · rw [← compl_iInter, subset_compl_comm, ← clg'_int]
    exact st_dis.subset_compl_left
  · refine fun n ↦ ⟨isOpen_compl_iff.mpr isClosed_closure, ?_⟩
    simp only [closure_compl, disjoint_compl_left_iff_subset]
    rw [← closure_eq_iff_isClosed.mpr t_cl] at clt_sub_g'
    exact subset_closure.trans <| (clt_sub_g' n).trans <| (g'_open n).subset_interior_closure

/-- Alternative definition of perfectly normal spaces: for any two disjoint closed sets `s` and `t`,
if there exists a continuous function `δ : X → ℝ` such that `δ ⁻¹' {0} = s` and `δ ⁻¹' {1} = t`,
then `X` is perfectly normal. -/
lemma of_precise_separating
    (sep : {s t : Set X} → IsClosed s → IsClosed t → Disjoint s t →
      {δ : C(X, ℝ) // δ ⁻¹' {0} = s ∧ δ ⁻¹' {1} = t}) : PerfectlyNormalSpace X where
  __ := NormalSpace.of_separating fun {s t} sC tC disj ↦ (sep sC tC disj).map id
      (fun _ ↦ And.imp (fun h₀ x hx ↦ h₀.symm.subset hx) fun h₁ x hx ↦ h₁.symm.subset hx)
  closed_gdelta ⦃s⦄ sC := by
    have Gδ₀ : IsGδ ({0} : Set ℝ) := IsGδ.singleton 0
    let ⟨δ, hδ₀, hδ₁⟩ := sep sC isClosed_empty (disjoint_empty s)
    rw [← hδ₀]
    apply Gδ₀.preimage

instance (priority := 100) PerfectlyNormalSpace.toCompletelyNormalSpace
    [PerfectlyNormalSpace X] : CompletelyNormalSpace X where
  completely_normal _ _ hd₁ hd₂ := separatedNhds_iff_disjoint.mp <|
    hasSeparatingCovers_iff_separatedNhds.mp
      ⟨(hd₂.hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a ↦ a) subset_closure,
       ((Disjoint.symm hd₁).hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a ↦ a) subset_closure⟩

/-- In a perfectly normal space, all closed sets are Gδ. -/
theorem IsClosed.isGδ [PerfectlyNormalSpace X] {s : Set X} (hs : IsClosed s) : IsGδ s :=
  PerfectlyNormalSpace.closed_gdelta hs

instance (priority := 100) [PerfectlyNormalSpace X] : R0Space X where
  specializes_symmetric x y hxy := by
    rw [specializes_iff_forall_closed]
    intro K hK hyK
    apply IsClosed.isGδ at hK
    obtain ⟨Ts, hoTs, -, rfl⟩ := hK
    rw [mem_sInter] at hyK ⊢
    intros
    solve_by_elim [hxy.mem_open]

/-- A T₆ space is a perfectly normal T₀ space. -/
class T6Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, PerfectlyNormalSpace X

-- see Note [lower instance priority]
/-- A `T₆` space is a `T₅` space. -/
instance (priority := 100) T6Space.toT5Space [T6Space X] : T5Space X where

end PerfectlyNormal

end Separation
