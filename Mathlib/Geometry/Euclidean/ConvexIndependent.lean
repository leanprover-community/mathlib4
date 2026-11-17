/-
Copyright (c) 2026 David Iach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Iach
-/
module

public import Mathlib.Analysis.Convex.IndependentBetween
public import Mathlib.Analysis.Convex.Side
public import Mathlib.Geometry.Euclidean.PerpBisector

import Mathlib.Data.Finset.Card

/-!
# Equidistant points in convex independent planar sets

In a Euclidean space of dimension at most two, a convex independent set has at most two points
equidistant from a fixed pair of distinct points. If the base endpoints also belong to the set,
two such points straddle the base midpoint and lie on opposite sides of its line. Consequently,
each specified open side contains at most one equidistant point.

The base endpoints need not belong to the set for the bound of two. The one-sided bounds require
both endpoints to belong to the set.
-/

@[expose] public section

open AffineSubspace Set

namespace ConvexIndependent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
/-- There are at most two equidistant apices for any distinct base in a planar convex independent
set. The base endpoints need not themselves belong to the set. -/
theorem card_equidistant_le_two (hdim : Module.finrank ℝ E ≤ 2)
    (s : Finset E) (hs : ConvexIndependent ℝ (fun p : (s : Set E) ↦ p.val))
    {a b : E} (hab : a ≠ b) :
    (s.filter fun p ↦ dist p a = dist p b).card ≤ 2 := by
  classical
  by_contra h
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp (by omega :
    2 < (s.filter fun p ↦ dist p a = dist p b).card)
  simp only [Finset.mem_filter] at hp hq hr
  apply not_collinear hs hp.1 hq.1 hr.1 hpq hpr hqr
  apply (collinear_perpBisector hdim hab).subset
  simp only [insert_subset_iff, singleton_subset_iff]
  exact ⟨mem_perpBisector_iff_dist_eq.mpr hp.2,
    mem_perpBisector_iff_dist_eq.mpr hq.2, mem_perpBisector_iff_dist_eq.mpr hr.2⟩

/-- Distinct equidistant apices in a convex independent planar set straddle the base midpoint. -/
theorem sbtw_midpoint_of_equidistant (hdim : Module.finrank ℝ E ≤ 2)
    {s : Set E} (hs : ConvexIndependent ℝ ((↑) : s → E))
    {a b p q : E} (ha : a ∈ s) (hb : b ∈ s) (hp : p ∈ s) (hq : q ∈ s)
    (hab : a ≠ b) (hpq : p ≠ q)
    (hpa : dist p a = dist p b) (hqa : dist q a = dist q b) :
    Sbtw ℝ p (midpoint ℝ a b) q := by
  have hpn : p ≠ a ∧ p ≠ b := by
    constructor <;> intro h <;> subst p <;> simp_all [dist_eq_zero]
  have hqn : q ≠ a ∧ q ≠ b := by
    constructor <;> intro h <;> subst q <;> simp_all [dist_eq_zero]
  have hcol : Collinear ℝ ({p, midpoint ℝ a b, q} : Set E) := by
    apply (collinear_perpBisector hdim hab).subset
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨mem_perpBisector_iff_dist_eq.mpr hpa,
      midpoint_mem_perpBisector a b, mem_perpBisector_iff_dist_eq.mpr hqa⟩
  exact hs.sbtw_midpoint_of_collinear ha hb hp hq hab hpq hpn.1 hpn.2 hqn.1 hqn.2 hcol

/-- Distinct equidistant apices lie on opposite sides of the base line. -/
theorem sOppSide_of_equidistant (hdim : Module.finrank ℝ E ≤ 2)
    {s : Set E} (hs : ConvexIndependent ℝ ((↑) : s → E))
    {a b p q : E} (ha : a ∈ s) (hb : b ∈ s) (hp : p ∈ s) (hq : q ∈ s)
    (hab : a ≠ b) (hpq : p ≠ q)
    (hpa : dist p a = dist p b) (hqa : dist q a = dist q b) :
    (line[ℝ, a, b]).SOppSide p q := by
  have hpn : p ≠ a ∧ p ≠ b := by
    constructor <;> intro h <;> subst p <;> simp_all [dist_eq_zero]
  apply (sbtw_midpoint_of_equidistant hdim hs ha hb hp hq hab hpq hpa hqa).sOppSide_of_notMem_of_mem
  · intro h
    exact not_collinear hs hp ha hb hpn.1 hpn.2 hab
      (collinear_insert_of_mem_affineSpan_pair h)
  · exact (wbtw_midpoint ℝ a b).mem_affineSpan

/-- On either fixed side of a base line, a convex independent planar set has at most one apex. -/
theorem eq_of_equidistant_of_sSameSide (hdim : Module.finrank ℝ E ≤ 2)
    {s : Set E} (hs : ConvexIndependent ℝ ((↑) : s → E))
    {a b p q : E} (ha : a ∈ s) (hb : b ∈ s) (hp : p ∈ s) (hq : q ∈ s)
    (hab : a ≠ b) (hpa : dist p a = dist p b) (hqa : dist q a = dist q b)
    (hside : (line[ℝ, a, b]).SSameSide p q) : p = q := by
  by_contra hpq
  exact hside.not_sOppSide (sOppSide_of_equidistant hdim hs ha hb hp hq hab hpq hpa hqa)

open Classical in
/-- A specified open side of a base line contains at most one equidistant vertex. -/
theorem card_equidistant_on_side_le_one (hdim : Module.finrank ℝ E ≤ 2)
    (s : Finset E) (hs : ConvexIndependent ℝ (fun p : (s : Set E) ↦ p.val))
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (z : E) :
    (s.filter fun p ↦ dist p a = dist p b ∧ (line[ℝ, a, b]).SSameSide p z).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  exact eq_of_equidistant_of_sSameSide hdim hs ha hb hp.1 hq.1 hab hp.2.1 hq.2.1
    (hp.2.2.trans hq.2.2.symm)

open Classical in
/-- A supporting base, with every other vertex on one specified open side, has at most one apex. -/
theorem card_equidistant_le_one_of_supporting_line (hdim : Module.finrank ℝ E ≤ 2)
    (s : Finset E) (hs : ConvexIndependent ℝ (fun p : (s : Set E) ↦ p.val))
    {a b z : E} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b)
    (hside : ∀ p ∈ s, p ≠ a → p ≠ b → (line[ℝ, a, b]).SSameSide p z) :
    (s.filter fun p ↦ dist p a = dist p b).card ≤ 1 := by
  classical
  apply le_trans (Finset.card_le_card (t := s.filter fun p ↦
    dist p a = dist p b ∧ (line[ℝ, a, b]).SSameSide p z) ?_)
    (card_equidistant_on_side_le_one hdim s hs ha hb hab z)
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  have hpn : p ≠ a ∧ p ≠ b := by
    constructor <;> intro h <;> subst p <;> simp_all [dist_eq_zero]
  exact ⟨hp.1, hp.2, hside p hp.1 hpn.1 hpn.2⟩

end ConvexIndependent
