/-
Copyright (c) 2024 Shreyas Srinivas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shreyas Srinivas
-/

import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring.Basic


namespace Mathlib

namespace DiscreteFairDivision

variable {Agents Goods : Type}
variable [Fintype Agents] [Fintype Goods]
variable [DecidableEq Agents]
variable [DecidableEq Goods] -- Indivisible goods only



structure Alloc where
  assign : Agents → Finset Goods
  disjoint : ∀ a b : Agents, a ≠ b → assign a ∩ assign b = ∅

structure Val where
  val : Agents → Finset Goods → ℝ
  empty : ∀ a : Agents, val a ∅ = 0
  pos : ∀ a : Agents, ∀ s : Finset Goods, val a s ≥ 0
  mono : ∀ a : Agents, ∀ s t : Finset Goods,
    s ⊆ t → val a s ≤ val a t


variable (alloc : @Alloc Agents Goods _)
variable (v : @Val Agents Goods)

def valSingle (a : Agents) (g : Goods) :=
  v.val a {g}

def isEmpty (a : Agents):=
  alloc.assign a = ∅

abbrev unAllocated (g : Goods) := ∀ a, g ∉ alloc.assign a

def allocate (g : Goods) (a : Agents) (h : unAllocated alloc g): @Alloc Agents Goods _ := {
  assign := fun (x : Agents) => if x = a then (alloc.assign x) ∪ {g} else alloc.assign x
  disjoint := by
    intro arb_a arb_b hneq
    simp
    by_cases ha : arb_a = a
    case pos =>
      have hneqb : arb_b ≠ a := by
        by_contra heqarb_a
        simp_all only [ne_eq, not_true_eq_false]
      simp [ha, hneqb, Finset.union_inter_distrib_right]
      rw [←ha, alloc.disjoint]
      simp [h]
      exact hneq
    case neg =>
      by_cases hb : arb_b = a <;>
        simp[hb, ha, alloc.disjoint, hneq]
      rw[←hb]
      simp[Finset.inter_union_distrib_left, hneq, alloc.disjoint]
      simp [h]
}

def isEmptyAlloc  :=
  ∀ a : Agents, alloc.assign a = ∅

def complete : Prop :=
  ∀ g : Goods, ∃ a : Agents, g ∈ alloc.assign a

def additive : Prop :=
  ∀ a : Agents, ∀ G : Finset Goods,
    v.val a G = ∑ g ∈ G, v.val a {g}

def EF_agents (a b : Agents) : Prop :=
      v.val a (alloc.assign a) ≥ v.val a (alloc.assign b)

def EF : Prop :=
    ∀ (a b : Agents), EF_agents alloc v a b

def EF1_agents (a b : Agents) : Prop :=
     isEmpty alloc b ∨ (∃ g ∈ alloc.assign b,
        v.val a (alloc.assign a) ≥ v.val a ((alloc.assign b).erase g))

def EF1 : Prop :=
    ∀ (a b : Agents), EF1_agents alloc v a b

def EFX_agents (a b : Agents) : Prop :=
    ∀ g ∈ alloc.assign b,
      v.val a (alloc.assign a) ≥ v.val a ((alloc.assign b).erase g)

def EFX : Prop :=
    ∀ (a b : Agents), EFX_agents alloc v a b


lemma empty_alloc_is_EF : isEmptyAlloc alloc → EF alloc v := by
  simp [isEmptyAlloc, EF, EF_agents]
  intro hempty a b
  have ha := hempty a
  have hb := hempty b
  rw [ha, hb]

lemma EF_implies_EFX :
  EF alloc v → EFX alloc v := by
  intro hEF
  unfold EFX EFX_agents
  intro a b g _
  by_cases hemp_a : (isEmpty alloc a)
    <;> by_cases hemp_b : (isEmpty alloc b)
    <;> simp[isEmptyAlloc, EF, isEmpty] at hemp_a hemp_b <;> tauto
    <;> simp [EF, EF_agents] at hEF
    <;> specialize hEF a b
    <;> have mono_ineq : v.val a ((alloc.assign b).erase g) ≤ v.val a (alloc.assign b) := by
            simp[Finset.erase_subset, v.mono]
  all_goals
    simp[Finset.erase_subset]
    linarith

lemma EFX_implies_EF1 :
  EFX alloc v → EF1 alloc v := by
  intro hEFX
  simp_all [EFX, EFX_agents, EF1, EF1_agents]
  intro a b
  by_cases h : isEmpty alloc b <;> simp [h]
  simp [isEmpty] at h
  specialize hEFX a b
  apply Finset.nonempty_iff_ne_empty.mpr at h
  apply Finset.Nonempty.exists_mem at h
  cases h with
  | intro g h =>
      use g
      tauto

lemma EF_implies_EF1 :
  EF alloc v → EF1 alloc v := by
  solve_by_elim [EF_implies_EFX, EFX_implies_EF1]


end DiscreteFairDivision
end Mathlib
