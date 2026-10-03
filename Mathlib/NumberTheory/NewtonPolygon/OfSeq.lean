/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/

module

public import Mathlib.NumberTheory.NewtonPolygon.Convexity

/-!
This file is split into two parts:

# The Newton polygon as a lower convex hull: the geometric specification

`IsNewtonPolygonOf v P` says the one-sided polygon `P` is *the* Newton polygon of the point
sequence `(k, v k)`: it is anchored at the first finite point, lies on/below every point, and is
the greatest polygon with that anchor lying below the points — the textbook "lower boundary of
the convex hull" (blueprint, `blueprint/src/chapter/NP.tex`, Definition 1), stated through the
`height` API and with no reference to the construction algorithm.

Main results:
* `IsNewtonPolygonOf.height_eq` — **uniqueness**: two Newton polygons of the same sequence have
  equal heights everywhere. (Uniqueness of the underlying `NewtonPolygon₀` *structure* is false:
  a segment can be split into two collinear segments, since `slopes_increasing` is non-strict.
  Height equality is the geometrically meaningful statement.)

# Uniqueness
-/

@[expose] public section

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]

/-- The height of the `k`-th point `(k, v k)` in the codomain of `NewtonPolygon₀.height`:
`⊤` for an infinite valuation (no point), and the real image of `v k` otherwise. -/
noncomputable def pointHeight (v : ℕ → WithTop Γ) (k : ℕ) : WithBotTop ℝ :=
  match v k with
  | ⊤ => ⊤
  | (a : Γ) => ((algebraMap Γ ℝ a : ℝ) : WithBotTop ℝ)

lemma pointHeight_eq_top_iff {v : ℕ → WithTop Γ} {k : ℕ} :
    pointHeight v k = ⊤ ↔ v k = ⊤ := by
  cases hv : v k <;> simp only [pointHeight, hv, WithBotTop.coe_ne_top, WithTop.coe_ne_top]

lemma pointHeight_coe {v : ℕ → WithTop Γ} {k : ℕ} {a : Γ} (h : v k = (a : WithTop Γ)) :
    pointHeight v k = ((algebraMap Γ ℝ a : ℝ) : WithBotTop ℝ) := by
  simp only [pointHeight, h]

/-- **The geometric specification of the Newton polygon** (blueprint Definition 1: "the lower
boundary of the convex hull of the set of points `(i, ν aᵢ)`"). A one-sided polygon `P` is the
Newton polygon of the sequence `v` when:

* (`start_le`, `start_mem`) it is anchored at the first finite point of `v`;
* (`height_le`) it lies on/below every point of `v`;
* (`isGreatest`) it is the greatest polygon with that anchor lying on/below the points.

Convexity is built into the `NewtonPolygon₀` structure (`slopes_increasing`), so these fields
say exactly "greatest convex minorant through the anchor", i.e. the lower convex hull.

The competitor class in `isGreatest` is anchored at the same starting `x`-coordinate: a
competitor starting further left is unconstrained on indices where `v` is `⊤` and could stand
arbitrarily high there, so maximality over unanchored competitors is unsatisfiable. -/
structure IsNewtonPolygonOf (v : ℕ → WithTop Γ) (P : NewtonPolygon₀ (Γ := Γ)) : Prop where
  /-- Strictly left of the starting vertex there are no points. -/
  start_le : ∀ k : ℕ, (k : ℤ) < P.starting_point.1 → v k = ⊤
  /-- The starting vertex is a point of the sequence. -/
  start_mem : ∃ k : ℕ, (k : ℤ) = P.starting_point.1 ∧
    v k = (P.starting_point.2 : WithTop Γ)
  /-- The polygon lies on/below every point. -/
  height_le : ∀ k : ℕ, P.height k ≤ pointHeight v k
  /-- Any polygon with the same starting `x`-coordinate lying on/below the points lies on/below
  `P`. -/
  isGreatest : ∀ Q : NewtonPolygon₀ (Γ := Γ), Q.starting_point.1 = P.starting_point.1 →
    (∀ k : ℕ, Q.height k ≤ pointHeight v k) → Q.IsBelow P

namespace IsNewtonPolygonOf

variable {v : ℕ → WithTop Γ} {P P₁ P₂ : NewtonPolygon₀ (Γ := Γ)}

lemma starting_point_fst_le (h : IsNewtonPolygonOf v P) {k : ℕ} (hv : v k ≠ ⊤) :
    P.starting_point.1 ≤ (k : ℤ) :=
  not_lt.1 fun hlt => hv (h.start_le k hlt)

lemma starting_point_fst_eq (h₁ : IsNewtonPolygonOf v P₁) (h₂ : IsNewtonPolygonOf v P₂) :
    P₁.starting_point.1 = P₂.starting_point.1 := by
  obtain ⟨k₁, hk₁, hv₁⟩ := h₁.start_mem
  obtain ⟨k₂, hk₂, hv₂⟩ := h₂.start_mem
  exact le_antisymm (hk₂ ▸ h₁.starting_point_fst_le (hv₂.trans_ne WithTop.coe_ne_top))
    (hk₁ ▸ h₂.starting_point_fst_le (hv₁.trans_ne WithTop.coe_ne_top))

lemma isBelow (h₁ : IsNewtonPolygonOf v P₁) (h₂ : IsNewtonPolygonOf v P₂) :
    P₁.IsBelow P₂ :=
  h₂.isGreatest P₁ (starting_point_fst_eq h₁ h₂) h₁.height_le

/-- **Uniqueness of the Newton polygon**: two Newton polygons of the same sequence have the same
height at every integer. (The `NewtonPolygon₀` structures themselves may differ by splitting a
segment into collinear pieces; the height function is the invariant content.) -/
theorem height_eq (h₁ : IsNewtonPolygonOf v P₁) (h₂ : IsNewtonPolygonOf v P₂) (x : ℤ) :
    P₁.height x = P₂.height x :=
  le_antisymm (NewtonPolygon₀.isBelow_iff_height.1 (h₁.isBelow h₂) x)
    (NewtonPolygon₀.isBelow_iff_height.1 (h₂.isBelow h₁) x)

/-- **Points lie on/above the first-slope line**: for every point `(k, a)` of the sequence right
of the starting vertex, `s₀ · (k - x₀) ≤ a - y₀`, where `s₀` is the first unit slope and
`(x₀, y₀)` the starting vertex. -/
theorem unitSlope_zero_mul_le (h : IsNewtonPolygonOf v P) {k : ℕ} {a : Γ}
    (hk : P.starting_point.1 < (k : ℤ)) (ha : v k = (a : WithTop Γ)) :
    WithBotTop.toReal (P.unitSlope 0) * ((k : ℝ) - (P.starting_point.1 : ℝ)) ≤
      algebraMap Γ ℝ a - algebraMap Γ ℝ P.starting_point.2 := by
  have hle : P.height (k : ℤ) ≤ ((algebraMap Γ ℝ a : ℝ) : WithBotTop ℝ) :=
    pointHeight_coe ha ▸ h.height_le k
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (k : ℤ) = P.starting_point.1 + (d : ℤ) :=
    ⟨((k : ℤ) - P.starting_point.1).toNat, by omega⟩
  rw [hd] at hle
  have htop : P.height (P.starting_point.1 + (d : ℤ)) ≠ ⊤ := fun hcon =>
    WithBotTop.coe_ne_top _ (top_le_iff.1 (hcon ▸ hle))
  rw [P.height_eq_heightFun d htop, WithBotTop.coe_le_coe] at hle
  -- the height at `d` is at least the line of slope `unitSlope 0` through the starting vertex
  have hlow := P.heightFun_zero ▸ P.le_heightFun d htop
  have hdeq : (d : ℝ) = (k : ℝ) - (P.starting_point.1 : ℝ) := by
    have hz : (d : ℤ) = (k : ℤ) - P.starting_point.1 := by omega
    exact_mod_cast hz
  rw [hdeq] at hlow
  linarith

end IsNewtonPolygonOf

namespace NewtonPolygon₀

/-- A one-sided Newton polygon is *pure of slope `m`* when it consists of a single segment of
slope `m`. -/
def IsPure (P : NewtonPolygon₀ (Γ := Γ)) (m : ℝ) : Prop :=
  P.slopes 0 = (m : WithBotTop ℝ) ∧ P.slopes 1 = ⊤

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- A pure polygon has exactly one segment. -/
lemma IsPure.support_eq_one {P : NewtonPolygon₀ (Γ := Γ)} {m : ℝ} (h : P.IsPure m) :
    P.support = 1 := by
  obtain ⟨hm, htop⟩ := h
  -- The second slope is `⊤`, hence not a non-final slope: there are at most two segments.
  have hle : ¬ ((1 : ℕ) : WithTop ℕ) + 1 < P.support := fun hlt => by
    obtain ⟨a, ha⟩ := P.slopes_nonFinal 1 hlt
    exact WithBotTop.coe_ne_top a (ha.symm.trans htop)
  -- The first slope is real, hence not junk: there is at least one segment.
  have h0 : ¬ P.support ≤ ((0 : ℕ) : WithTop ℕ) := fun hs =>
    WithBotTop.coe_ne_top m (hm.symm.trans (P.slopes_junk 0 hs))
  cases hs : P.support with
  | top => simp only [Nat.cast_one, hs, WithTop.add_lt_top, WithTop.one_lt_top, and_self,
      not_true_eq_false] at hle
  | coe s =>
    rw [hs] at hle h0
    norm_num at hle h0
    obtain rfl | rfl : s = 1 ∨ s = 2 := by omega
    · rfl
    · -- with two segments the `⊤` second slope is final, which forces a single segment
      exact hs ▸ (P.slopes_final 1 ⟨hs ▸ rfl, Or.inl htop⟩).1

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- A single-segment polygon with real first slope is pure. -/
lemma isPure_of_support_eq_one {P : NewtonPolygon₀ (Γ := Γ)} {m : ℝ}
    (hs : P.support = 1) (hm : P.slopes 0 = (m : WithBotTop ℝ)) : P.IsPure m :=
  ⟨hm, P.slopes_junk 1 hs.le⟩

end NewtonPolygon₀
