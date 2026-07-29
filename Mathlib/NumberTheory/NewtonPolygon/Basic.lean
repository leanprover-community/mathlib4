/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Order.WithBotTop

/-!
# Newton Polygons

This file defines Newton polygons as a pair of functions that index's the segments of a Newton
polygons slopes and lengths.

# Main Definitions:

`NewtonPolygon` is a doubly infinite version where we allow infinite slopes in both directions.

`NewtonPolygon₀` is one sided version that fixes the start point at the first vertex and has
segments in only one direction.

-/

@[expose] public section

section ToMove

def ofRight : WithTop ℕ → WithBotTop ℤ
  | ⊤ => ⊤
  | (k : ℕ) => ((k : ℤ) : WithBotTop ℤ)

lemma ofRight_le_coe {s : WithTop ℕ} {n : ℤ} (h : ofRight s ≤ (n : WithBotTop ℤ)) :
    0 ≤ n ∧ s ≤ (n.toNat : WithTop ℕ) := by
  rcases s with _ | k
  · exact absurd (top_le_iff.mp h) (WithBotTop.coe_ne_top n)
  · have := WithBotTop.coe_le_coe.mp h
    exact ⟨by grind, WithTop.coe_le_coe.mpr (show k ≤ n.toNat by omega)⟩

lemma coe_add_one_lt_ofRight {s : WithTop ℕ} {n : ℤ} (h0 : 0 ≤ n)
    (h : (n : WithBotTop ℤ) + 1 < ofRight s) : (n.toNat : WithTop ℕ) + 1 < s := by
  rcases s with _ | k
  · exact WithTop.coe_lt_top (n.toNat + 1)
  · have hk : n + 1 < (k : ℤ) := WithBotTop.coe_lt_coe.mp h
    exact WithTop.coe_lt_coe.mpr (show n.toNat + 1 < k by omega)

lemma ofRight_le_natCast {s : WithTop ℕ} {m : ℕ} (h : s ≤ (m : WithTop ℕ)) :
    ofRight s ≤ ((m : ℤ) : WithBotTop ℤ) := by
  rcases s with _ | k
  · exact absurd (top_le_iff.mp h) WithTop.coe_ne_top
  · have hk : k ≤ m := WithTop.coe_le_coe.mp h
    exact WithBotTop.coe_le_coe.mpr (show (k : ℤ) ≤ (m : ℤ) by omega)

lemma natCast_add_one_lt_ofRight {s : WithTop ℕ} {m : ℕ} (h : (m : WithTop ℕ) + 1 < s) :
    ((m : ℤ) : WithBotTop ℤ) + 1 < ofRight s := by
  rcases s with _ | k
  · exact (WithBotTop.coe_ne_top ((m : ℤ) + 1)).lt_top
  · have hk : m + 1 < k := WithTop.coe_lt_coe.mp h
    exact WithBotTop.coe_lt_coe.mpr (show (m : ℤ) + 1 < (k : ℤ) by omega)

end ToMove

variable {Γ : Type*} -- Γ will be 'y'-values of the Newton polygon; the defintions only make sense
  -- when it is contained in ℝ

/-- A doubly-infinite Newton polygon. Where we either have infinite segments on the left or none. -/
structure NewtonPolygon where
  /-- Support indexing how many segments we have; `support.1` gives number of segments to the right
    and `support.2` indicates if there are 0 or infinitely many segments to the left. -/
  support : WithTop ℕ × ({0, ⊥} : Set (WithBotTop ℤ))
  /-- A function indexing the slopes of the segment. -/
  slopes : ℤ → WithBotTop ℝ
  /-- Past the right end the slopes are junk, fixed to `⊤`. -/
  slopes_junkRight : ∀ n : ℤ, ofRight support.1 ≤ n → slopes n = ⊤
  /-- Past the left end the slopes are junk, fixed to `⊥`. -/
  slopes_junkLeft : ∀ n : ℤ, n < (support.2 : WithBotTop ℤ) → slopes n = ⊥
  /-- Any non final slope is finite -/
  slopes_nonFinal : ∀ n : ℤ, (support.2 : WithBotTop ℤ) ≤ n ∧ n + 1 < ofRight support.1 →
    ∃ a : ℝ, slopes n = some (some a)
  /-- Final slopes are only ⊤/⊥ if the support is (1,0). -/
  slopes_final : ∀ n : ℕ, n + 1 = support.1 ∧ (slopes n = ⊤ ∨ slopes n = ⊥) → support.1 = 1 ∧
    (support.2 : WithBotTop ℤ) = 0
  /-- Slopes are increasing. -/
  slopes_increasing : ∀ n, slopes n ≤ slopes (n + 1)
  /-- A function indexing the lengths of the segments. -/
  lengths : ℤ → WithTop ℕ
  /-- Past the right end the lengths are junk; fixed to be 0. -/
  lengths_junkRight : ∀ n : ℤ, ofRight support.1 ≤ n → lengths n = 0
  /-- Past the left end the lengths are junk; fixed to be 0. -/
  lengths_junkLeft : ∀ n : ℤ, n < (support.2 : WithBotTop ℤ) → lengths n = 0
  /-- Any non final length is finite and non-zero. -/
  lengths_nonFinal : ∀ n : ℤ, (support.2 : WithBotTop ℤ) ≤ n ∧ n + 1 < ofRight support.1 →
    ∃ a : ℕ, a ≠ 0 ∧ lengths n = some a
  /-- Final lengths are only 0 if the support is (1,0). -/
  lengths_final : ∀ n : ℕ, n + 1 = support.1 ∧ lengths n = 0 → support.1 = 1 ∧
    (support.2 : WithBotTop ℤ) = 0
  /-- Starting point of the Newton polygon. -/
  starting_point : ℤ × Γ

/-- A one-sided Newton Polygon. -/
structure NewtonPolygon₀ where
  /-- Number of segments we have. -/
  support : WithTop ℕ
  /-- A function indexing the slopes of the segments, we care about the indexes < support. -/
  slopes : ℕ → WithBotTop ℝ
  /-- Outside the support the slopes are fixed to be ⊤ -/
  slopes_junk : ∀ n : ℕ, support ≤ n → slopes n = ⊤
  /-- Any non final slope is finite -/
  slopes_nonFinal : ∀ n : ℕ, n + 1 < support → ∃ a : ℝ, slopes n = some (some a)
  /-- Final slopes are only ⊤/⊥ if the support is 1 -/
  slopes_final : ∀ n : ℕ, n + 1 = support ∧ (slopes n = ⊤ ∨ slopes n = ⊥) → support = 1
  /-- Slopes are increasing. -/
  slopes_increasing : ∀ n : ℕ, slopes n ≤ slopes (n + 1)
  /-- A function indexing the lengths of the segments. -/
  lengths : ℕ → WithTop ℕ
  /-- Outside the support the slopes are fixed to be 0. -/
  lengths_junk : ∀ n : ℕ, support ≤ n → lengths n = 0
  /-- Any non final length is finite and non-zero. -/
  lengths_nonFinal : ∀ n : ℕ, n + 1 < support → ∃ a : ℕ, a ≠ 0 ∧ lengths n = some a
  /-- Final lengths are only 0 if the support is 1. -/
  lengths_final : ∀ n : ℕ, n + 1 = support ∧ lengths n = 0 → support = 1
  /-- Starting point of the Newton polygon. -/
  starting_point : ℤ × Γ

namespace NewtonPolygon

@[ext]
lemma ext {NP₁ NP₂ : NewtonPolygon (Γ := Γ)} (hsupport : NP₁.support = NP₂.support)
    (hslopes : NP₁.slopes = NP₂.slopes) (hlengths : NP₁.lengths = NP₂.lengths)
    (hstart : NP₁.starting_point = NP₂.starting_point) : NP₁ = NP₂ := by
  obtain ⟨s₁, sl₁, _, _, _, _, _, l₁, _, _, _, _, sp₁⟩ := NP₁
  obtain ⟨s₂, sl₂, _, _, _, _, _, l₂, _, _, _, _, sp₂⟩ := NP₂
  grind

/-- A Newton polygon is one sided when it only has segments in one direction. -/
def IsOneSided (NP : NewtonPolygon (Γ := Γ)) : Prop := (NP.support.2 : WithBotTop ℤ) = 0

/-- A one sided Newton polygon can be represented as a `NewtonPolygon₀`. -/
def isOneSided_toNewtonPolygon₀ {NP : NewtonPolygon (Γ := Γ)} (h : NP.IsOneSided) :
    NewtonPolygon₀ (Γ := Γ) where
  support := NP.support.1
  slopes n := NP.slopes n
  slopes_junk n hn := NP.slopes_junkRight n (ofRight_le_natCast hn)
  slopes_nonFinal n hn := by
    refine NP.slopes_nonFinal n ⟨?_, natCast_add_one_lt_ofRight hn⟩
    rw [h]
    exact WithBotTop.coe_le_coe.mpr (Int.natCast_nonneg n)
  slopes_final n hn := (NP.slopes_final n hn).1
  slopes_increasing n:= NP.slopes_increasing n
  lengths n := NP.lengths n
  lengths_junk n hn := NP.lengths_junkRight n (ofRight_le_natCast hn)
  lengths_nonFinal n hn := by
    refine NP.lengths_nonFinal n ⟨?_, natCast_add_one_lt_ofRight hn⟩
    rw [h]
    exact WithBotTop.coe_le_coe.mpr (Int.natCast_nonneg n)
  lengths_final n hn := (NP.lengths_final n hn).1
  starting_point := NP.starting_point

lemma isOneSided_slopes_of_neg {NP : NewtonPolygon (Γ := Γ)} (h : NP.IsOneSided) {x : ℤ}
    (hx : x < 0) : NP.slopes x = ⊥ := by
  refine (NP.slopes_junkLeft x) ?_
  rw [h]
  exact WithBotTop.coe_lt_coe.mpr hx

lemma isOneSided_lengths_of_neg {NP : NewtonPolygon (Γ := Γ)} (h : NP.IsOneSided) {x : ℤ}
    (hx : x < 0) : NP.lengths x = 0 := by
  refine (NP.lengths_junkLeft x) ?_
  rw [h]
  exact WithBotTop.coe_lt_coe.mpr hx

/-- A `NewtonPolygon` with finite segments. -/
def IsFinite (NP : NewtonPolygon (Γ := Γ)) : Prop :=
  NP.IsOneSided ∧ NP.support.1 ≠ ⊤

end NewtonPolygon

namespace NewtonPolygon₀

@[ext]
lemma ext {P₁ P₂ : NewtonPolygon₀ (Γ := Γ)} (hsupport : P₁.support = P₂.support)
    (hslopes : P₁.slopes = P₂.slopes) (hlengths : P₁.lengths = P₂.lengths)
    (hstart : P₁.starting_point = P₂.starting_point) : P₁ = P₂ := by
  obtain ⟨s₁, sl₁, _, _, _, _, l₁, _, _, _, sp₁⟩ := P₁
  obtain ⟨s₂, sl₂, _, _, _, _, l₂, _, _, _, sp₂⟩ := P₂
  grind

variable (P : NewtonPolygon₀ (Γ := Γ))

/-- A `NewtonPolygon₀` extends to a `NewtonPolygon`. -/
def toNewtonPolygon : NewtonPolygon (Γ := Γ) where
  support := (P.support, ⟨0, Set.mem_insert 0 {⊥}⟩)
  slopes n := if n < 0 then ⊥ else P.slopes n.toNat
  slopes_junkRight n hn := by
    obtain ⟨h0, hs⟩ := ofRight_le_coe hn
    simpa [if_neg (not_lt.2 h0)] using P.slopes_junk _ hs
  slopes_junkLeft n hn := if_pos (WithBotTop.coe_lt_coe.mp hn)
  slopes_nonFinal := by
    rintro n ⟨h1, h2⟩
    simpa [if_neg (not_lt.2 (WithBotTop.coe_le_coe.mp h1))] using P.slopes_nonFinal _
      (coe_add_one_lt_ofRight (WithBotTop.coe_le_coe.mp h1) h2)
  slopes_final := by
    rintro n ⟨h1, h2⟩
    rw [if_neg (not_lt.2 (Int.natCast_nonneg n)), Int.toNat_natCast] at h2
    exact ⟨P.slopes_final n ⟨h1, h2⟩, rfl⟩
  slopes_increasing n := by
    by_cases hn : n < 0
    · simp [if_pos hn]
    · simp only [if_neg hn]
      convert P.slopes_increasing n.toNat
      grind
  lengths n := if n < 0 then 0 else P.lengths n.toNat
  lengths_junkRight n hn := by
    obtain ⟨h0, hs⟩ := ofRight_le_coe hn
    simpa [if_neg (not_lt.2 h0)] using P.lengths_junk _ hs
  lengths_junkLeft n hn := if_pos (WithBotTop.coe_lt_coe.mp hn)
  lengths_nonFinal := by
    rintro n ⟨h1, h2⟩
    simpa [if_neg (not_lt.2 (WithBotTop.coe_le_coe.mp h1))] using P.lengths_nonFinal _
      (coe_add_one_lt_ofRight (WithBotTop.coe_le_coe.mp h1) h2)
  lengths_final := by
    rintro n ⟨h1, h2⟩
    rw [if_neg (not_lt.2 (Int.natCast_nonneg n)), Int.toNat_natCast] at h2
    exact ⟨P.lengths_final n ⟨h1, h2⟩, rfl⟩
  starting_point := P.starting_point

@[simp]
lemma toNewtonPolygon_support_fst : P.toNewtonPolygon.support.1 = P.support := rfl

@[simp]
lemma toNewtonPolygon_startingPoint : P.toNewtonPolygon.starting_point = P.starting_point := rfl

lemma toNewtonPolygon_slopes_natCast (n : ℕ) : P.toNewtonPolygon.slopes (n : ℤ) = P.slopes n := by
  change (if (n : ℤ) < 0 then ⊥ else P.slopes (n : ℤ).toNat) = P.slopes n
  grind

lemma toNewtonPolygon_slopes_of_neg {x : ℤ} (hx : x < 0) : P.toNewtonPolygon.slopes x = ⊥ :=
  if_pos hx

lemma toNewtonPolygon_lengths_natCast (n : ℕ) :
    P.toNewtonPolygon.lengths (n : ℤ) = P.lengths n := by
  change (if (n : ℤ) < 0 then 0 else P.lengths (n : ℤ).toNat) = P.lengths n
  grind

lemma toNewtonPolygon_lengths_of_neg {x : ℤ} (hx : x < 0) : P.toNewtonPolygon.lengths x = 0 :=
  if_pos hx

lemma toNewtonPolygon_isOneSided : NewtonPolygon.IsOneSided (toNewtonPolygon P) := rfl

/-- A `NewtonPolygon₀` with finite segments. -/
def IsFinite (P : NewtonPolygon₀ (Γ := Γ)) : Prop := P.support ≠ ⊤

end NewtonPolygon₀

lemma NewtonPolygon.isOneSided_toNewtonPolygon₀_toNewtonPolygon {NP : NewtonPolygon (Γ := Γ)}
    (h : NP.IsOneSided) : NewtonPolygon₀.toNewtonPolygon (isOneSided_toNewtonPolygon₀ h) = NP := by
  refine NewtonPolygon.ext (Prod.ext rfl (Subtype.ext h.symm)) ?_ ?_ rfl
  · funext x
    by_cases hx : x < 0
    · simp [NewtonPolygon₀.toNewtonPolygon_slopes_of_neg (isOneSided_toNewtonPolygon₀ h) hx,
        isOneSided_slopes_of_neg h hx]
    · rw [← Int.toNat_of_nonneg (not_lt.mp hx), NewtonPolygon₀.toNewtonPolygon_slopes_natCast
        (isOneSided_toNewtonPolygon₀ h)]
      rfl
  · funext x
    by_cases hx : x < 0
    · simp [NewtonPolygon₀.toNewtonPolygon_lengths_of_neg (isOneSided_toNewtonPolygon₀ h) hx,
        isOneSided_lengths_of_neg h hx]
    · rw [← Int.toNat_of_nonneg (not_lt.mp hx), NewtonPolygon₀.toNewtonPolygon_lengths_natCast
        (isOneSided_toNewtonPolygon₀ h)]
      rfl

lemma NewtonPolygon₀.toNewtonPolygon_toNewtonPolygon₀ (P : NewtonPolygon₀ (Γ := Γ)) :
    NewtonPolygon.isOneSided_toNewtonPolygon₀ (toNewtonPolygon_isOneSided P) = P := by
  refine NewtonPolygon₀.ext rfl ?_ ?_ rfl
  <;> funext n
  · exact P.toNewtonPolygon_slopes_natCast n
  · exact P.toNewtonPolygon_lengths_natCast n

lemma NewtonPolygon.isOneSided_exists_newtonPolygon₀ {NP : NewtonPolygon (Γ := Γ)}
    (h : NP.IsOneSided) : ∃ P : NewtonPolygon₀ (Γ := Γ), P.toNewtonPolygon = NP :=
  ⟨NewtonPolygon.isOneSided_toNewtonPolygon₀ h ,
    NewtonPolygon.isOneSided_toNewtonPolygon₀_toNewtonPolygon h⟩

section IsFinite

lemma NewtonPolygon₀.toNewtonPolygon_isFinite {P : NewtonPolygon₀ (Γ := Γ)} :
    P.toNewtonPolygon.IsFinite ↔ P.IsFinite :=
  ⟨fun h => h.2, fun h => ⟨P.toNewtonPolygon_isOneSided, h⟩⟩

lemma NewtonPolygon.isFinite_exists_newtonPolygon₀ {NP : NewtonPolygon (Γ := Γ)}
    (h : NP.IsFinite) : ∃ P : NewtonPolygon₀ (Γ := Γ), P.IsFinite ∧ P.toNewtonPolygon = NP :=
  ⟨NewtonPolygon.isOneSided_toNewtonPolygon₀ h.1, h.2,
    NewtonPolygon.isOneSided_toNewtonPolygon₀_toNewtonPolygon h.1⟩

end IsFinite
