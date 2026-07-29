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

`NewtonPolygon.Height` is a function that maps every integer `x` to the `y`-value of the Newton
polygon at `x`. Outside the support we set it to be `⊤` to the right and `⊥` to the left.

`NewtonPolygon.IsBelow` is a predicate saying that a Newton polygon `P₁` lies below `P₂` when for
all integers `x`, `P₁.Height x ≤ P₂.Height.`

We also mimic these for `NewtonPolygon₀`.

-/

@[expose] public section

section ToMove

/-- The real number carried by a `WithBotTop ℝ`, with both `⊤` and `⊥` sent to the junk value
`0`. -/
def toReal (x : WithBotTop ℝ) : ℝ := WithBotTop.rec (motive := fun _ => ℝ) 0 (fun a => a) 0 x

@[simp]
lemma toReal_coe (r : ℝ) : toReal (r : WithBotTop ℝ) = r := rfl

@[simp]
lemma toReal_top : toReal (⊤ : WithBotTop ℝ) = 0 := rfl

@[simp]
lemma toReal_bot : toReal (⊥ : WithBotTop ℝ) = 0 := rfl

end ToMove

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ] (NP : NewtonPolygon (Γ := Γ))

namespace NewtonPolygon

/-- An auxillary function outputting what slope of a segment you are on.

Picture you are standing on the polygon and stepping right in unit intervals. At every moment you
are on some segment, and the arguments record your state:
* `n` — the index of the segment you currently in;
* `r` — how many further unit intervals of segment `n` still lie to the *right* of you, so
  `r = 0` means you are on the last unit of segment `n`, about to cross a vertex;
* `j` — how many unit steps you must take to reach your target.

`rightSlopeAux NP n r j` is then the slope of whichever segment you land on after `j` steps.

It is started by `rightSlope` at `n = 0` and `r = (length of segment 0) - 1`.
-/
def rightSlopeAux (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) (r : ℕ) : ℕ → WithBotTop ℝ
  | 0 => NP.slopes n
  | j + 1 =>
    match r with
    | r + 1 => rightSlopeAux NP n r j
    | 0 =>
      match NP.lengths (n + 1) with
      | ⊤ => NP.slopes (n + 1)
      | (w + 1 : ℕ) => rightSlopeAux NP (n + 1) w j
      | (0 : ℕ) => rightSlopeAux NP (n + 1) 0 j

/-- The slope of the polygon on the unit interval `[x₀ + j, x₀ + j + 1]`, `j` steps to the right
of the starting vertex `x₀`. In the junk region to the right of the support this is `⊤`. -/
def rightSlope (j : ℕ) : WithBotTop ℝ :=
  match NP.lengths 0 with
  | ⊤ => NP.slopes 0
  | (w + 1 : ℕ) => NP.rightSlopeAux 0 w j
  | (0 : ℕ) => NP.rightSlopeAux 0 0 j

/-- Mirror of rightSlopeAux, but now walking to the left. -/
def leftSlopeAux (NP : NewtonPolygon (Γ := Γ)) (n : ℤ) (r : ℕ) : ℕ → WithBotTop ℝ
  | 0 => NP.slopes n
  | j + 1 =>
    match r with
    | r + 1 => leftSlopeAux NP n r j
    | 0 =>
      match NP.lengths (n - 1) with
      | ⊤ => NP.slopes (n - 1)
      | (w + 1 : ℕ) => leftSlopeAux NP (n - 1) w j
      | (0 : ℕ) => leftSlopeAux NP (n - 1) 0 j

/-- The slope of the polygon on the unit interval `[x₀ - j - 1, x₀ - j]`, `j` steps to the left of
the starting vertex `x₀` (so `leftSlope 0` is the slope of segment `-1`). In the junk region to
the left of the support this is `⊥`. -/
def leftSlope (j : ℕ) : WithBotTop ℝ :=
  match NP.lengths (-1) with
  | ⊤ => NP.slopes (-1)
  | (w + 1 : ℕ) => NP.leftSlopeAux (-1) w j
  | (0 : ℕ) => NP.leftSlopeAux (-1) 0 j

omit [CommSemiring Γ] [Algebra Γ ℝ] in
lemma isOneSided_leftSlopeAux_of_neg (h : NP.IsOneSided) (j : ℕ) :
    ∀ (n : ℤ) (r : ℕ), n < 0 → NP.leftSlopeAux n r j = ⊥ := by
  induction j with
  | zero => exact fun n r hn => isOneSided_slopes_of_neg h hn
  | succ j ih =>
    rintro n (_ | r) hn
    · rw [leftSlopeAux.eq_3, isOneSided_lengths_of_neg h (show n - 1 < 0 by omega)]
      exact ih (n - 1) 0 (by omega)
    · rw [leftSlopeAux.eq_2]
      exact ih n r hn

omit [CommSemiring Γ] [Algebra Γ ℝ] in
lemma isOneSided_leftSlope (h : NP.IsOneSided) (j : ℕ) : NP.leftSlope j = ⊥ := by
  rw [leftSlope.eq_def, isOneSided_lengths_of_neg h (show (-1 : ℤ) < 0 by norm_num)]
  exact NP.isOneSided_leftSlopeAux_of_neg h j (-1) 0 (by norm_num)

/-- The height of the starting vertex, its `Γ`-valued `y`-coordinate pushed into `ℝ`. -/
def startHeight : ℝ := algebraMap Γ ℝ NP.starting_point.2

/-- The `y`-value `k` integer steps to the right of the starting vertex. -/
noncomputable
def rightHeight (k : ℕ) : WithBotTop ℝ :=
  if 1 ≤ k ∧ NP.rightSlope (k - 1) = ⊤ then ⊤
  else ((NP.startHeight + ∑ i ∈ Finset.range k, toReal (NP.rightSlope i) : ℝ) : WithBotTop ℝ)

/-- The `y`-value `k` integer steps to the left of the starting vertex. -/
noncomputable
def leftHeight (k : ℕ) : WithBotTop ℝ :=
  if 1 ≤ k ∧ NP.leftSlope (k - 1) = ⊥ then ⊥
  else ((NP.startHeight - ∑ i ∈ Finset.range k, toReal (NP.leftSlope i) : ℝ) : WithBotTop ℝ)

lemma isOneSided_leftHeight (h : NP.IsOneSided) {k : ℕ} (hk : k ≠ 0) : NP.leftHeight k = ⊥ :=
  if_pos ⟨Nat.one_le_iff_ne_zero.mpr hk, NP.isOneSided_leftSlope h _⟩

/-- The `y`-value of the Newton polygon at the integer `x`-coordinate `x`. -/
noncomputable
def height (x : ℤ) : WithBotTop ℝ :=
  if 0 ≤ x - NP.starting_point.1 then NP.rightHeight (x - NP.starting_point.1).toNat
  else NP.leftHeight (NP.starting_point.1 - x).toNat

lemma isOneSided_height_of_lt (h : NP.IsOneSided) {x : ℤ} (hx : x < NP.starting_point.1) :
    NP.height x = ⊥ := by
  rw [height, if_neg (by omega)]
  exact NP.isOneSided_leftHeight h (by omega)

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

/-- The height of a one-sided Newton polygon at an integer `x`, through the embedding into
doubly-infinite polygons. -/
noncomputable
def height (x : ℤ) : WithBotTop ℝ := (toNewtonPolygon P).height x

lemma height_left_of_start (x : ℤ) (hx : x < P.starting_point.1) : P.height x = ⊥ :=
  NewtonPolygon.isOneSided_height_of_lt _ P.toNewtonPolygon_isOneSided hx

@[simp]
lemma height_toNewtonPolygon (x : ℤ) : P.toNewtonPolygon.height x = P.height x := rfl

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

end NewtonPolygon₀
