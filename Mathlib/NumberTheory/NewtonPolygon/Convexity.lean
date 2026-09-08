/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.NumberTheory.NewtonPolygon.Heights

/-!
# Convexity of one-sided Newton polygons

Discrete convexity infrastructure for `NewtonPolygon₀.height`, with no reference to any
construction algorithm.

## Main results

* `NewtonPolygon₀.unitSlope_mono` — unit slopes are monotone: the polygon is convex.
* `NewtonPolygon₀.height_eq_top_mono` — once the height is `⊤` (the junk region to the right of
  the polygon) it stays `⊤`.
* `NewtonPolygon₀.heightFun_chord`, `NewtonPolygon₀.height_le_chord` — a convex polygon lies
  on/below each of its chords (discrete Jensen).
* `NewtonPolygon₀.le_heightFun` — the first unit slope bounds the average slope from below.

These are the workhorses for the lower-convex-hull specification of
`Mathlib/NumberTheory/NewtonPolygon/OfSeq.lean`: both the "polygon below the points" and the
"greatest such polygon" halves reduce to chord comparisons.
-/

@[expose] public section

variable {Γ : Type*} [CommSemiring Γ] [Algebra Γ ℝ]

namespace NewtonPolygon₀

variable (P : NewtonPolygon₀ (Γ := Γ))

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- **Convexity of the polygon**: the unit slopes are monotone. -/
lemma unitSlope_mono : Monotone P.unitSlope := P.toNewtonPolygon.rightSlope_mono

/-! ### The junk region to the right

Right of the polygon the height is the junk value `⊤`. Since the unit slopes are monotone, the
guard `unitSlope (k - 1) = ⊤` that switches the height to `⊤` is itself monotone in `k`, so the
junk region is an up-set. -/

/-- Once the height is `⊤` (right-hand junk region) it stays `⊤`. -/
lemma height_eq_top_mono {x y : ℤ} (hx : P.height x = ⊤) (hxy : x ≤ y) : P.height y = ⊤ := by
  have hxs : P.starting_point.1 ≤ x := by
    by_contra hc
    rw [(P.height_eq_bot_iff x).2 (by omega)] at hx
    exact absurd hx (by simp)
  obtain ⟨kx, rfl⟩ : ∃ k : ℕ, x = P.starting_point.1 + (k : ℤ) :=
    ⟨(x - P.starting_point.1).toNat, by omega⟩
  obtain ⟨ky, rfl⟩ : ∃ k : ℕ, y = P.starting_point.1 + (k : ℤ) :=
    ⟨(y - P.starting_point.1).toNat, by omega⟩
  obtain ⟨h1, h2⟩ := P.height_add_natCast_eq_top_iff.1 hx
  refine P.height_add_natCast_eq_top_iff.2 ⟨by omega, top_le_iff.1 (h2 ▸ ?_)⟩
  exact P.unitSlope_mono (show kx - 1 ≤ ky - 1 by omega)

/-- Left of a non-`⊤` height all unit slopes are non-`⊤`. -/
lemma unitSlope_ne_top_of_height_ne_top {c : ℕ}
    (h : P.height (P.starting_point.1 + c) ≠ ⊤) {i : ℕ} (hic : i < c) : P.unitSlope i ≠ ⊤ :=
  fun hi => h (P.height_add_natCast_eq_top_iff.2
    ⟨by omega, top_le_iff.1 (hi ▸ P.unitSlope_mono (show i ≤ c - 1 by omega))⟩)

/-! ### Chords -/

/-- A `WithBotTop ℝ` which is neither `⊥` nor `⊤` carries a real number. -/
private lemma exists_coe {v : WithBotTop ℝ} (hb : v ≠ ⊥) (ht : v ≠ ⊤) :
    ∃ r : ℝ, v = (r : WithBotTop ℝ) := by
  induction v using WithBotTop.rec with
  | bot => exact absurd rfl hb
  | coe r => exact ⟨r, rfl⟩
  | top => exact absurd rfl ht

omit [CommSemiring Γ] [Algebra Γ ℝ] in
/-- Below the right-hand junk region the real-valued unit slopes are monotone: a unit slope is
never `⊥` (`unitSlope_ne_bot`), so `toReal` is order-preserving there. -/
private lemma toReal_unitSlope_le {i j : ℕ} (hij : i ≤ j) (hj : P.unitSlope j ≠ ⊤) :
    WithBotTop.toReal (P.unitSlope i) ≤ WithBotTop.toReal (P.unitSlope j) := by
  have hmono := P.unitSlope_mono hij
  have hi : P.unitSlope i ≠ ⊤ := fun hcon => hj (top_le_iff.1 (hcon ▸ hmono))
  obtain ⟨r, hr⟩ := exists_coe (P.unitSlope_ne_bot i) hi
  obtain ⟨s, hs⟩ := exists_coe (P.unitSlope_ne_bot j) hj
  rw [hr, hs] at hmono ⊢
  simpa using WithBotTop.coe_le_coe.1 hmono

/-- The increment of `heightFun` over `[m, n)` is the sum of the unit slopes there. -/
private lemma heightFun_sub {m n : ℕ} (hmn : m ≤ n) :
    P.heightFun n - P.heightFun m =
      ∑ i ∈ Finset.Ico m n, WithBotTop.toReal (P.unitSlope i) := by
  rw [heightFun, heightFun, NewtonPolygon.rightHeightReal, NewtonPolygon.rightHeightReal,
    Finset.sum_Ico_eq_sub _ hmn]
  simp only [toNewtonPolygon_rightSlope]
  ring

/-- **Chord inequality (discrete Jensen), division-free form**: on the honest region, for
`a ≤ b ≤ c` the height at `b` lies on/below the chord from `(a, heightFun a)` to
`(c, heightFun c)`. -/
lemma heightFun_chord {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    (hc : P.height (P.starting_point.1 + c) ≠ ⊤) :
    ((c : ℝ) - a) * P.heightFun b ≤
      ((c : ℝ) - b) * P.heightFun a + ((b : ℝ) - a) * P.heightFun c := by
  rcases eq_or_lt_of_le hbc with rfl | hbc'
  · linarith
  have hne : ∀ i, i < c → P.unitSlope i ≠ ⊤ := fun _ hi =>
    P.unitSlope_ne_top_of_height_ne_top hc hi
  have hcasta : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hcastb : (b : ℝ) ≤ c := by exact_mod_cast hbc
  have h1 : ∑ i ∈ Finset.Ico a b, WithBotTop.toReal (P.unitSlope i)
      ≤ ((b : ℝ) - a) * WithBotTop.toReal (P.unitSlope b) := by
    have hsum := Finset.sum_le_card_nsmul (Finset.Ico a b)
      (fun i => WithBotTop.toReal (P.unitSlope i)) (WithBotTop.toReal (P.unitSlope b))
      (fun i hi => P.toReal_unitSlope_le (le_of_lt (Finset.mem_Ico.1 hi).2) (hne b hbc'))
    rwa [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hab] at hsum
  have h2 : ((c : ℝ) - b) * WithBotTop.toReal (P.unitSlope b)
      ≤ ∑ i ∈ Finset.Ico b c, WithBotTop.toReal (P.unitSlope i) := by
    have hsum := Finset.card_nsmul_le_sum (Finset.Ico b c)
      (fun i => WithBotTop.toReal (P.unitSlope i)) (WithBotTop.toReal (P.unitSlope b))
      (fun i hi => P.toReal_unitSlope_le (Finset.mem_Ico.1 hi).1 (hne i (Finset.mem_Ico.1 hi).2))
    rwa [Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hbc] at hsum
  rw [← P.heightFun_sub hab] at h1
  rw [← P.heightFun_sub hbc] at h2
  have k1 : ((c : ℝ) - b) * (P.heightFun b - P.heightFun a)
      ≤ ((c : ℝ) - b) * (((b : ℝ) - a) * WithBotTop.toReal (P.unitSlope b)) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have k2 : ((b : ℝ) - a) * (((c : ℝ) - b) * WithBotTop.toReal (P.unitSlope b))
      ≤ ((b : ℝ) - a) * (P.heightFun c - P.heightFun b) :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  linarith [k1, k2]

/-- The first unit slope bounds the average slope from below: the height at `k` is at least the
line of slope `unitSlope 0` through the starting vertex. -/
lemma le_heightFun (k : ℕ) (hk : P.height (P.starting_point.1 + k) ≠ ⊤) :
    (k : ℝ) * WithBotTop.toReal (P.unitSlope 0) ≤ P.heightFun k - P.heightFun 0 := by
  rw [P.heightFun_sub (Nat.zero_le k)]
  have hsum := Finset.card_nsmul_le_sum (Finset.Ico 0 k)
    (fun i => WithBotTop.toReal (P.unitSlope i)) (WithBotTop.toReal (P.unitSlope 0))
    (fun i hi => P.toReal_unitSlope_le (Nat.zero_le i)
      (P.unitSlope_ne_top_of_height_ne_top hk (Finset.mem_Ico.1 hi).2))
  rwa [Nat.card_Ico, nsmul_eq_mul, Nat.sub_zero] at hsum

/-- **Chord comparison for `height`**: if the height at `x` and `z` is bounded by reals `a` and
`c`, then at any `y` between them it is bounded by the chord through `(x, a)` and `(z, c)`.

The left endpoint must lie at or right of the starting vertex: strictly left of it the height is
`⊥`, so `hx` carries no information there while the chord through `(x, a)` can be dragged
arbitrarily low (for the horizontal polygon starting at `(0, 0)`, taking `x = -1`, `a = -100`,
`z = 2`, `c = 0` the chord at `y = 0` is `-200/3 < 0 = height 0`). -/
lemma height_le_chord {x y z : ℤ} (hxs : P.starting_point.1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    {a c : ℝ} (hx : P.height x ≤ (a : WithBotTop ℝ)) (hz : P.height z ≤ (c : WithBotTop ℝ)) :
    P.height y ≤
      ((a + (c - a) / ((z : ℝ) - (x : ℝ)) * ((y : ℝ) - (x : ℝ)) : ℝ) : WithBotTop ℝ) := by
  obtain ⟨kx, rfl⟩ : ∃ kx : ℕ, x = P.starting_point.1 + (kx : ℤ) :=
    ⟨(x - P.starting_point.1).toNat, by omega⟩
  obtain ⟨ky, rfl⟩ : ∃ ky : ℕ, y = P.starting_point.1 + (ky : ℤ) :=
    ⟨(y - P.starting_point.1).toNat, by omega⟩
  obtain ⟨kz, rfl⟩ : ∃ kz : ℕ, z = P.starting_point.1 + (kz : ℤ) :=
    ⟨(z - P.starting_point.1).toNat, by omega⟩
  have hkxy : kx ≤ ky := by omega
  have hkyz : ky ≤ kz := by omega
  have hztop : P.height (P.starting_point.1 + (kz : ℤ)) ≠ ⊤ := by
    intro hcon
    rw [hcon] at hz
    exact absurd (top_le_iff.1 hz) (by simp)
  have hytop : P.height (P.starting_point.1 + (ky : ℤ)) ≠ ⊤ := fun hcon =>
    hztop (P.height_eq_top_mono hcon (by omega))
  have hxtop : P.height (P.starting_point.1 + (kx : ℤ)) ≠ ⊤ := fun hcon =>
    hztop (P.height_eq_top_mono hcon (by omega))
  rw [P.height_eq_heightFun kx hxtop, WithBotTop.coe_le_coe] at hx
  rw [P.height_eq_heightFun kz hztop, WithBotTop.coe_le_coe] at hz
  rw [P.height_eq_heightFun ky hytop, WithBotTop.coe_le_coe]
  have hDeq : ((P.starting_point.1 + (kz : ℤ) : ℤ) : ℝ) - ((P.starting_point.1 + (kx : ℤ) : ℤ) : ℝ)
      = (kz : ℝ) - (kx : ℝ) := by push_cast; ring
  have hYeq : ((P.starting_point.1 + (ky : ℤ) : ℤ) : ℝ) - ((P.starting_point.1 + (kx : ℤ) : ℤ) : ℝ)
      = (ky : ℝ) - (kx : ℝ) := by push_cast; ring
  rw [hDeq, hYeq]
  rcases eq_or_lt_of_le (hkxy.trans hkyz) with heq | hlt
  · obtain rfl : ky = kx := by omega
    simpa using hx
  · have hD : (0 : ℝ) < (kz : ℝ) - kx := by
      have : (kx : ℝ) < kz := by exact_mod_cast hlt
      linarith
    have hcast1 : (kx : ℝ) ≤ ky := by exact_mod_cast hkxy
    have hcast2 : (ky : ℝ) ≤ kz := by exact_mod_cast hkyz
    have chord := P.heightFun_chord hkxy hkyz hztop
    have b1 : ((kz : ℝ) - ky) * P.heightFun kx ≤ ((kz : ℝ) - ky) * a :=
      mul_le_mul_of_nonneg_left hx (by linarith)
    have b2 : ((ky : ℝ) - kx) * P.heightFun kz ≤ ((ky : ℝ) - kx) * c :=
      mul_le_mul_of_nonneg_left hz (by linarith)
    have key : P.heightFun ky * ((kz : ℝ) - kx)
        ≤ a * ((kz : ℝ) - kx) + (c - a) * ((ky : ℝ) - kx) := by linarith [chord, b1, b2]
    calc P.heightFun ky ≤ (a * ((kz : ℝ) - kx) + (c - a) * ((ky : ℝ) - kx)) / ((kz : ℝ) - kx) :=
          (le_div_iff₀ hD).2 key
      _ = a + (c - a) / ((kz : ℝ) - kx) * ((ky : ℝ) - kx) := by field_simp

end NewtonPolygon₀
