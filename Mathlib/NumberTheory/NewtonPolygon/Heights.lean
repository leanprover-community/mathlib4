/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.NumberTheory.NewtonPolygon.Basic

/-!
# Heights

In this file we define the height of Newton polygons, by which we mean explicit `y`-values of points
on the graph.

# Main Definitions:

`NewtonPolygon.rightEnd` and `NewtonPolygon.leftEnd` record how far the `n`-th vertex to the right
(resp. left) of the starting vertex sits from it, as the partial sums of `lengths`.

`NewtonPolygon.rightSlope` is the slope carried by the unit interval `j` steps to the right of the
starting vertex: the slope of the unique segment whose span contains that interval, and the junk
value `⊤` when there is no such segment. `NewtonPolygon.leftSlope` mirrors it, with junk `⊥`.

`NewtonPolygon.height` is a function that maps every integer `x` to the `y`-value of the Newton
polygon at `x`. Outside the support we set it to be `⊤` to the right and `⊥` to the left. Its
honest real-valued content to the right of the starting vertex is
`NewtonPolygon.rightHeightReal`, the starting height plus the accumulated unit slopes; the
`WithBotTop`-valued `height` guards that sum with the junk values.

`NewtonPolygon.IsBelow` is a predicate saying that a Newton polygon `P₁` lies below `P₂` when for
all integers `x`, `P₁.height x ≤ P₂.height x`.

We also mimic these for `NewtonPolygon₀`, where the walk to the right is the only one that carries
information: `NewtonPolygon₀.unitSlope`, `NewtonPolygon₀.vertexOffset`, `NewtonPolygon₀.vertexX`,
`NewtonPolygon₀.heightFun` and `NewtonPolygon₀.height`.

Convexity of the polygon — monotonicity of the unit slopes, and the resulting chord bounds — is
developed in `Mathlib/NumberTheory/NewtonPolygon/Convexity.lean`.

-/

@[expose] public section

section ToMove

namespace WithBotTop

/-- The real number carried by a `WithBotTop ℝ`, with both `⊤` and `⊥` sent to the junk value
`0`. -/
def toReal (x : WithBotTop ℝ) : ℝ := WithBotTop.rec (motive := fun _ => ℝ) 0 (fun a => a) 0 x

@[simp]
lemma toReal_coe (r : ℝ) : toReal (r : WithBotTop ℝ) = r := rfl

@[simp]
lemma toReal_top : toReal (⊤ : WithBotTop ℝ) = 0 := rfl

@[simp]
lemma toReal_bot : toReal (⊥ : WithBotTop ℝ) = 0 := rfl

end WithBotTop

end ToMove

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ] (NP : NewtonPolygon (Γ := Γ))

namespace NewtonPolygon

/-! ### Vertex positions -/

section
omit [CommSemiring Γ] [Algebra Γ ℝ]

/-- The distance from the starting vertex to the `n`-th vertex to its right: the sum of the
lengths of the first `n` segments. `⊤` once an infinite segment has been passed. -/
def rightEnd (n : ℕ) : WithTop ℕ := ∑ i ∈ Finset.range n, NP.lengths (i : ℤ)

/-- Mirror of `rightEnd`, walking to the left: the distance from the starting vertex to the `n`-th
vertex to its left. -/
def leftEnd (n : ℕ) : WithTop ℕ := ∑ i ∈ Finset.range n, NP.lengths (-1 - (i : ℤ))

@[simp] lemma rightEnd_zero : NP.rightEnd 0 = 0 := rfl

@[simp] lemma leftEnd_zero : NP.leftEnd 0 = 0 := rfl

/-- Passing segment `n` moves the right-hand vertex on by that segment's length. -/
lemma rightEnd_succ (n : ℕ) : NP.rightEnd (n + 1) = NP.rightEnd n + NP.lengths (n : ℤ) :=
  Finset.sum_range_succ _ n

/-- Passing segment `-1 - n` moves the left-hand vertex on by that segment's length. -/
lemma leftEnd_succ (n : ℕ) : NP.leftEnd (n + 1) = NP.leftEnd n + NP.lengths (-1 - (n : ℤ)) :=
  Finset.sum_range_succ _ n

/-- The vertices march away from the starting vertex. -/
lemma rightEnd_mono : Monotone NP.rightEnd :=
  monotone_nat_of_le_succ fun n => (NP.rightEnd_succ n).symm ▸ le_self_add

lemma leftEnd_mono : Monotone NP.leftEnd :=
  monotone_nat_of_le_succ fun n => (NP.leftEnd_succ n).symm ▸ le_self_add

/-- The segment slopes are monotone: the polygon is convex. -/
lemma slopes_mono : Monotone NP.slopes := monotone_int_of_le_succ NP.slopes_increasing

/-- A one-sided polygon has no segments to the left, so every left-hand vertex sits on the
starting vertex. -/
lemma isOneSided_leftEnd (h : NP.IsOneSided) (n : ℕ) : NP.leftEnd n = 0 :=
  Finset.sum_eq_zero fun i _ => isOneSided_lengths_of_neg h (by omega)

/-! ### Unit slopes -/

open scoped Classical in
/-- The slope of the polygon on the unit interval `[x₀ + j, x₀ + j + 1]`, `j` steps to the right
of the starting vertex `x₀`: the slope of the first segment reaching strictly past `x₀ + j`,
equivalently the slope of the unique segment `n` with `rightEnd n ≤ j < rightEnd (n + 1)`
(`rightSlope_eq_slopes`). In the junk region to the right of the support no segment reaches that
far and the value is `⊤`. -/
noncomputable def rightSlope (j : ℕ) : WithBotTop ℝ :=
  if h : ∃ n : ℕ, (j : WithTop ℕ) < NP.rightEnd (n + 1) then NP.slopes (Nat.find h) else ⊤

open scoped Classical in
/-- Mirror of `rightSlope`, walking to the left: the slope of the polygon on the unit interval
`[x₀ - j - 1, x₀ - j]`, `j` steps to the left of the starting vertex (so `leftSlope 0` is the
slope of segment `-1`). In the junk region to the left of the support the value is `⊥`. -/
noncomputable def leftSlope (j : ℕ) : WithBotTop ℝ :=
  if h : ∃ n : ℕ, (j : WithTop ℕ) < NP.leftEnd (n + 1) then NP.slopes (-1 - (Nat.find h : ℤ))
  else ⊥

/-- **The unit slopes read off the segment slopes**: on the unit intervals of segment `n` — those
offsets `j` with `rightEnd n ≤ j < rightEnd (n + 1)` — the unit slope is the slope of segment
`n`. -/
lemma rightSlope_eq_slopes {n j : ℕ} (h1 : NP.rightEnd n ≤ (j : WithTop ℕ))
    (h2 : (j : WithTop ℕ) < NP.rightEnd (n + 1)) : NP.rightSlope j = NP.slopes (n : ℤ) := by
  classical
  have hex : ∃ m : ℕ, (j : WithTop ℕ) < NP.rightEnd (m + 1) := ⟨n, h2⟩
  have hfind : Nat.find hex = n := by
    refine le_antisymm (Nat.find_min' hex h2) (not_lt.1 fun hlt => ?_)
    exact absurd ((NP.rightEnd_mono hlt).trans h1) (not_le.2 (Nat.find_spec hex))
  rw [rightSlope, dif_pos hex, hfind]

/-- Past the right end of the polygon no segment reaches the unit interval and the slope is the
junk value `⊤`. -/
lemma rightSlope_eq_top {j : ℕ} (h : ∀ n : ℕ, NP.rightEnd (n + 1) ≤ (j : WithTop ℕ)) :
    NP.rightSlope j = ⊤ := by
  classical
  exact dif_neg (not_exists.2 fun n => not_lt.2 (h n))

/-- **Convexity of the polygon**: the unit slopes to the right of the starting vertex are
monotone. -/
lemma rightSlope_mono : Monotone NP.rightSlope := by
  classical
  intro j j' hjj
  have hcast : (j : WithTop ℕ) ≤ (j' : WithTop ℕ) := by exact_mod_cast hjj
  by_cases h' : ∃ n : ℕ, (j' : WithTop ℕ) < NP.rightEnd (n + 1)
  · have h : ∃ n : ℕ, (j : WithTop ℕ) < NP.rightEnd (n + 1) :=
      h'.imp fun _ hn => lt_of_le_of_lt hcast hn
    simp only [rightSlope, dif_pos h, dif_pos h']
    exact NP.slopes_mono (by
      exact_mod_cast Nat.find_min' h (lt_of_le_of_lt hcast (Nat.find_spec h')))
  · rw [NP.rightSlope_eq_top fun n => not_lt.1 fun hlt => h' ⟨n, hlt⟩]
    exact le_top

/-- A one-sided polygon carries no information to the left: every left unit slope is `⊥`. -/
lemma isOneSided_leftSlope (h : NP.IsOneSided) (j : ℕ) : NP.leftSlope j = ⊥ := by
  classical
  refine dif_neg (not_exists.2 fun n => not_lt.2 ?_)
  rw [NP.isOneSided_leftEnd h (n + 1)]
  simp

end

/-! ### Heights -/

/-- The height of the starting vertex, its `Γ`-valued `y`-coordinate pushed into `ℝ`. -/
def startHeight : ℝ := algebraMap Γ ℝ NP.starting_point.2

/-- The real-valued `y`-value `k` integer steps to the right of the starting vertex: the starting
height plus the accumulated unit slopes. On the honest region this is the value carried by
`rightHeight`; past the right end of the polygon it is junk. -/
noncomputable def rightHeightReal (k : ℕ) : ℝ :=
  NP.startHeight + ∑ i ∈ Finset.range k, WithBotTop.toReal (NP.rightSlope i)

@[simp]
lemma rightHeightReal_zero : NP.rightHeightReal 0 = NP.startHeight := by simp [rightHeightReal]

/-- One step to the right adds the unit slope crossed. -/
lemma rightHeightReal_succ (k : ℕ) :
    NP.rightHeightReal (k + 1) = NP.rightHeightReal k + WithBotTop.toReal (NP.rightSlope k) := by
  rw [rightHeightReal, rightHeightReal, Finset.sum_range_succ, add_assoc]

/-- Mirror of `rightHeightReal`, walking to the left. -/
noncomputable def leftHeightReal (k : ℕ) : ℝ :=
  NP.startHeight - ∑ i ∈ Finset.range k, WithBotTop.toReal (NP.leftSlope i)

/-- The `y`-value `k` integer steps to the right of the starting vertex: the real value
`rightHeightReal k`, guarded by `⊤` once the polygon has run out. -/
noncomputable def rightHeight (k : ℕ) : WithBotTop ℝ :=
  if 1 ≤ k ∧ NP.rightSlope (k - 1) = ⊤ then ⊤ else ((NP.rightHeightReal k : ℝ) : WithBotTop ℝ)

/-- The `y`-value `k` integer steps to the left of the starting vertex. -/
noncomputable def leftHeight (k : ℕ) : WithBotTop ℝ :=
  if 1 ≤ k ∧ NP.leftSlope (k - 1) = ⊥ then ⊥ else ((NP.leftHeightReal k : ℝ) : WithBotTop ℝ)

/-- To the right of the starting vertex the height is never `⊥`. -/
lemma rightHeight_ne_bot (k : ℕ) : NP.rightHeight k ≠ ⊥ := by
  rw [rightHeight]
  split
  · exact WithBotTop.top_ne_bot
  · exact WithBotTop.coe_ne_bot _

lemma isOneSided_leftHeight (h : NP.IsOneSided) {k : ℕ} (hk : k ≠ 0) : NP.leftHeight k = ⊥ :=
  if_pos ⟨Nat.one_le_iff_ne_zero.mpr hk, NP.isOneSided_leftSlope h _⟩

/-- The `y`-value of the Newton polygon at the integer `x`-coordinate `x`. -/
noncomputable def height (x : ℤ) : WithBotTop ℝ :=
  if 0 ≤ x - NP.starting_point.1 then NP.rightHeight (x - NP.starting_point.1).toNat
  else NP.leftHeight (NP.starting_point.1 - x).toNat

/-- At or right of the starting vertex the height is the right-hand walk. -/
lemma height_eq_rightHeight {x : ℤ} (hx : NP.starting_point.1 ≤ x) :
    NP.height x = NP.rightHeight (x - NP.starting_point.1).toNat :=
  if_pos (by omega)

/-- Strictly left of the starting vertex the height is the left-hand walk. -/
lemma height_eq_leftHeight {x : ℤ} (hx : x < NP.starting_point.1) :
    NP.height x = NP.leftHeight (NP.starting_point.1 - x).toNat :=
  if_neg (by omega)

lemma isOneSided_height_of_lt (h : NP.IsOneSided) {x : ℤ} (hx : x < NP.starting_point.1) :
    NP.height x = ⊥ :=
  (NP.height_eq_leftHeight hx).trans (NP.isOneSided_leftHeight h (by omega))

@[simp]
lemma height_startingPoint :
    NP.height NP.starting_point.1 = (NP.startHeight : WithBotTop ℝ) := by
  simp [height, rightHeight]

/-- `IsBelow NP₁ NP₂` says the polygon `NP₁` lies (weakly) below `NP₂`: at every integer
`x`-coordinate its height is `≤` that of `NP₂`, measured in `WithBotTop ℝ`. -/
def IsBelow (NP₁ NP₂ : NewtonPolygon (Γ := Γ)) : Prop := ∀ x : ℤ, NP₁.height x ≤ NP₂.height x

@[refl]
lemma IsBelow.refl (NP : NewtonPolygon (Γ := Γ)) : IsBelow NP NP := fun _ => le_refl _

lemma IsBelow.trans {NP₁ NP₂ NP₃ : NewtonPolygon (Γ := Γ)}
    (h₁ : IsBelow NP₁ NP₂) (h₂ : IsBelow NP₂ NP₃) : IsBelow NP₁ NP₃ :=
  fun x => (h₁ x).trans (h₂ x)

end NewtonPolygon

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := Γ))

/-! ### Vertex positions of a one-sided polygon -/

section
omit [CommSemiring Γ] [Algebra Γ ℝ]

/-- The distance from the starting vertex to the `n`-th vertex: the sum of the first `n` segment
lengths. `⊤` once an infinite segment has been passed. -/
def vertexOffset (n : ℕ) : WithTop ℕ := ∑ i ∈ Finset.range n, P.lengths i

/-- The `x`-coordinate of the `n`-th vertex of a one-sided polygon: the starting `x`-coordinate
plus the first `n` segment lengths. `⊤` once an infinite segment has been passed. -/
def vertexX (n : ℕ) : WithTop ℤ :=
  (P.starting_point.1 : WithTop ℤ) + (P.vertexOffset n).map (fun l : ℕ => (l : ℤ))

@[simp]
lemma toNewtonPolygon_rightEnd (n : ℕ) : P.toNewtonPolygon.rightEnd n = P.vertexOffset n :=
  Finset.sum_congr rfl fun i _ => P.toNewtonPolygon_lengths_natCast i

@[simp] lemma vertexOffset_zero : P.vertexOffset 0 = 0 := rfl

/-- Passing segment `n` moves the vertex to the right by that segment's length. -/
lemma vertexOffset_succ (n : ℕ) : P.vertexOffset (n + 1) = P.vertexOffset n + P.lengths n :=
  Finset.sum_range_succ _ n

lemma vertexOffset_mono : Monotone P.vertexOffset :=
  monotone_nat_of_le_succ fun n => (P.vertexOffset_succ n).symm ▸ le_self_add

/-- The `0`-th vertex is the starting vertex. -/
@[simp] lemma vertexX_zero : P.vertexX 0 = (P.starting_point.1 : WithTop ℤ) := by
  simp [vertexX]

/-- Passing segment `n` moves the vertex to the right by that segment's length. -/
lemma vertexX_succ (n : ℕ) :
    P.vertexX (n + 1) = P.vertexX n + (P.lengths n).map (fun l : ℕ => (l : ℤ)) := by
  rw [vertexX, vertexX, vertexOffset_succ, add_assoc]
  congr 1
  exact WithTop.map_add (Nat.castAddMonoidHom ℤ) _ _

/-- The vertices march to the right. -/
lemma vertexX_mono : Monotone P.vertexX :=
  monotone_nat_of_le_succ fun n => by
    rw [vertexX_succ]
    exact le_add_of_nonneg_right (by cases h : P.lengths n <;> simp)

/-- A vertex sits at or left of the offset `j` exactly when it does so measured from the starting
vertex. -/
lemma vertexX_le_iff {n j : ℕ} :
    P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) ↔
      P.vertexOffset n ≤ (j : WithTop ℕ) := by
  cases h : P.vertexOffset n with
  | top => simp [vertexX, h]
  | coe w =>
    rw [vertexX, h]
    simp only [WithTop.map_coe, ← WithTop.coe_add, WithTop.coe_le_coe, add_le_add_iff_left,
      Nat.cast_le]
    exact Nat.cast_le.symm

/-- Dual of `vertexX_le_iff`. -/
lemma lt_vertexX_iff {n j : ℕ} :
    ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX n ↔
      (j : WithTop ℕ) < P.vertexOffset n :=
  lt_iff_lt_of_le_iff_le P.vertexX_le_iff

end

/-! ### Slopes and heights of a one-sided polygon -/

/-- The slope of the polygon on the unit interval `[x₀ + j, x₀ + j + 1]`, `j` steps to the right
of the starting vertex: `rightSlope` of the embedded doubly-infinite polygon. -/
noncomputable def unitSlope (j : ℕ) : WithBotTop ℝ := P.toNewtonPolygon.rightSlope j

omit [CommSemiring Γ] [Algebra Γ ℝ] in
@[simp]
lemma toNewtonPolygon_rightSlope (j : ℕ) : P.toNewtonPolygon.rightSlope j = P.unitSlope j := rfl

/-- The real-valued height of the polygon `k` integer steps to the right of the starting vertex:
starting height plus the accumulated unit slopes. On the honest (non-junk) region this is the
value carried by `height`; past the right end it is junk. -/
noncomputable def heightFun (k : ℕ) : ℝ := P.toNewtonPolygon.rightHeightReal k

/-- At the starting vertex the height is the starting height. -/
@[simp] lemma heightFun_zero : P.heightFun 0 = algebraMap Γ ℝ P.starting_point.2 :=
  P.toNewtonPolygon.rightHeightReal_zero

/-- One step to the right adds the unit slope crossed. -/
lemma heightFun_succ (k : ℕ) :
    P.heightFun (k + 1) = P.heightFun k + WithBotTop.toReal (P.unitSlope k) :=
  P.toNewtonPolygon.rightHeightReal_succ k

/-- The height of a one-sided Newton polygon at an integer `x`, through the embedding into
doubly-infinite polygons. -/
noncomputable def height (x : ℤ) : WithBotTop ℝ := (toNewtonPolygon P).height x

@[simp]
lemma height_toNewtonPolygon (x : ℤ) : P.toNewtonPolygon.height x = P.height x := rfl

lemma height_left_of_start (x : ℤ) (hx : x < P.starting_point.1) : P.height x = ⊥ :=
  NewtonPolygon.isOneSided_height_of_lt _ P.toNewtonPolygon_isOneSided hx

/-- At or right of the starting vertex the height is the right-hand walk. -/
lemma height_eq_rightHeight {x : ℤ} (hx : P.starting_point.1 ≤ x) :
    P.height x = P.toNewtonPolygon.rightHeight (x - P.starting_point.1).toNat :=
  P.toNewtonPolygon.height_eq_rightHeight hx

/-- The height at a natural offset from the starting vertex is the right-hand walk at that
offset. -/
lemma height_add_natCast (k : ℕ) :
    P.height (P.starting_point.1 + k) = P.toNewtonPolygon.rightHeight k := by
  rw [P.height_eq_rightHeight (by omega)]
  congr 1
  omega

/-- The height is `⊥` exactly strictly left of the starting vertex. -/
lemma height_eq_bot_iff (x : ℤ) : P.height x = ⊥ ↔ x < P.starting_point.1 := by
  refine ⟨fun h => not_le.1 fun hx => ?_, P.height_left_of_start x⟩
  rw [P.height_eq_rightHeight hx] at h
  exact P.toNewtonPolygon.rightHeight_ne_bot _ h

/-- On the honest region the height is the real value `heightFun`. -/
lemma height_eq_heightFun (k : ℕ) (h : P.height (P.starting_point.1 + k) ≠ ⊤) :
    P.height (P.starting_point.1 + k) = (P.heightFun k : WithBotTop ℝ) := by
  rw [P.height_add_natCast k, NewtonPolygon.rightHeight] at h ⊢
  rw [if_neg fun hc => h (by rw [if_pos hc])]
  rfl

/-- The height is `⊤` exactly when the right-hand walk has run out of segments. -/
lemma height_add_natCast_eq_top_iff {k : ℕ} :
    P.height (P.starting_point.1 + k) = ⊤ ↔ 1 ≤ k ∧ P.unitSlope (k - 1) = ⊤ := by
  rw [P.height_add_natCast k, NewtonPolygon.rightHeight, toNewtonPolygon_rightSlope]
  refine ⟨fun h => ?_, fun h => if_pos h⟩
  by_contra hc
  rw [if_neg hc] at h
  exact absurd h (by simp)

/-- `IsBelow P₁ P₂` says the one-sided polygon `P₁` lies (weakly) below `P₂` at every integer
`x`-coordinate. -/
def IsBelow (P₁ P₂ : NewtonPolygon₀ (Γ := Γ)) : Prop :=
  NewtonPolygon.IsBelow P₁.toNewtonPolygon P₂.toNewtonPolygon

lemma isBelow_iff {P₁ P₂ : NewtonPolygon₀ (Γ := Γ)} :
    IsBelow P₁ P₂ ↔ NewtonPolygon.IsBelow P₁.toNewtonPolygon P₂.toNewtonPolygon := Iff.rfl

lemma isBelow_iff_height {P₁ P₂ : NewtonPolygon₀ (Γ := Γ)} :
    IsBelow P₁ P₂ ↔ ∀ x : ℤ, P₁.height x ≤ P₂.height x := Iff.rfl

@[refl]
lemma IsBelow.refl (P : NewtonPolygon₀ (Γ := Γ)) : IsBelow P P := NewtonPolygon.IsBelow.refl _

lemma IsBelow.trans {P₁ P₂ P₃ : NewtonPolygon₀ (Γ := Γ)} (h₁ : IsBelow P₁ P₂)
    (h₂ : IsBelow P₂ P₃) : IsBelow P₁ P₃ :=
  NewtonPolygon.IsBelow.trans h₁ h₂

/-! ### The unit slopes read off the segment slopes -/

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- On the unit intervals of segment `n` — that is, at offsets `j` with
`vertexX n ≤ x₀ + j < vertexX (n + 1)` — the unit slope is the slope of segment `n`.
This is the correspondence between `unitSlope` and the structure field `slopes`. -/
lemma unitSlope_eq_slopes {n j : ℕ}
    (h1 : P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ))
    (h2 : ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)) :
    P.unitSlope j = P.slopes n := by
  rw [P.vertexX_le_iff] at h1
  rw [P.lt_vertexX_iff] at h2
  rw [unitSlope, P.toNewtonPolygon.rightSlope_eq_slopes (by rwa [toNewtonPolygon_rightEnd])
    (by rwa [toNewtonPolygon_rightEnd]), toNewtonPolygon_slopes_natCast]

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- Every unit interval either sits inside a genuine segment or lies past the right end of the
polygon, where the slope is the junk value `⊤`. -/
lemma unitSlope_cases (j : ℕ) :
    (∃ n : ℕ, P.vertexX n ≤ ((P.starting_point.1 + j : ℤ) : WithTop ℤ) ∧
      ((P.starting_point.1 + j : ℤ) : WithTop ℤ) < P.vertexX (n + 1)) ∨
    P.unitSlope j = ⊤ := by
  classical
  by_cases h : ∃ n : ℕ, (j : WithTop ℕ) < P.vertexOffset (n + 1)
  · refine Or.inl ⟨Nat.find h, ?_, ?_⟩
    · rw [P.vertexX_le_iff]
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h0
      · simp [h0]
      · obtain ⟨m, hm⟩ : ∃ m, Nat.find h = m + 1 := ⟨Nat.find h - 1, by omega⟩
        exact hm ▸ not_lt.1 (fun hlt => Nat.find_min h (by omega) hlt)
    · rw [P.lt_vertexX_iff]
      exact Nat.find_spec h
  · refine Or.inr (P.toNewtonPolygon.rightSlope_eq_top fun n => ?_)
    rw [toNewtonPolygon_rightEnd]
    exact not_lt.1 fun hlt => h ⟨n, hlt⟩

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- A unit slope is never `⊥`: a junk `⊥` slope can only decorate a zero-width segment
(`slopes_final`), and a zero-width segment carries no unit interval. -/
lemma unitSlope_ne_bot (j : ℕ) : P.unitSlope j ≠ ⊥ := by
  rcases P.unitSlope_cases j with ⟨n, h1, h2⟩ | htop
  · rw [P.unitSlope_eq_slopes h1 h2]
    intro hbot
    -- the bracketing segment has positive length, so its slope cannot be the junk `⊥`
    have hlen : P.lengths n ≠ 0 := by
      rw [P.vertexX_le_iff] at h1
      rw [P.lt_vertexX_iff, P.vertexOffset_succ] at h2
      intro h0
      rw [h0, add_zero] at h2
      exact absurd h1 (not_le.2 h2)
    have hlt : (n : WithTop ℕ) < P.support := by
      by_contra hcon
      exact absurd ((P.slopes_junk n (not_lt.1 hcon)) ▸ hbot) (by simp)
    have hnf : ¬ (n : WithTop ℕ) + 1 < P.support := fun hcon => by
      obtain ⟨a, ha⟩ := P.slopes_nonFinal n hcon
      exact absurd (ha ▸ hbot) (by simp)
    have hle : (n : WithTop ℕ) + 1 ≤ P.support := by
      cases hs : P.support with
      | top => exact le_top
      | coe s =>
        rw [hs] at hlt
        rw [show ((n : WithTop ℕ) + 1) = ((n + 1 : ℕ) : WithTop ℕ) by push_cast; ring]
        exact WithTop.coe_le_coe.2 (WithTop.coe_lt_coe.1 hlt)
    exact hlen (P.slopes_final n ⟨le_antisymm hle (not_lt.1 hnf), Or.inr hbot⟩).2
  · rw [htop]; simp

end NewtonPolygon₀
