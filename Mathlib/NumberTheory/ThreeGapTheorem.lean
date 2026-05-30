/-
Copyright (c) 2026 Saar Shai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Saar Shai
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Push

/-!
# The three-gap (Steinhaus / three-distance) theorem

For irrational `α` and any `N`, the points `{0·α}, …, {(N-1)·α}` on the circle `ℝ ⧸ ℤ` split it
into arcs taking at most **three** distinct lengths (`ThreeGap.three_gap`).

## Main results

* `ThreeGap.three_gap` : `(Finset.univ.image (gap hα)).card ≤ 3`.

## Implementation notes

We use the concrete representatives `x α k = Int.fract (k·α) ∈ [0,1)`; `[0,1)` is a `LinearOrder`,
so the sorted point set and its consecutive "gaps" are available via `Finset.orderEmbOfFin` (which
is unavailable on the quotient `AddCircle 1`, only a `CircularOrder`). The proof is Liang's
rigid-gap argument re-cast through the *oriented forward distance*
`fwdDist a c = Int.fract ((c-a)·α)`: every arc length is `fwdDist` of an orbit-index jump, and a
strong induction shows the jump always
lies in `{p, -q, p-q}` for the two closest one-sided return times `p`, `q`.

## References

* J. H. Liang, *A short proof of the 3d distance theorem*, Discrete Math. 28 (1979) 325–326.
* Previously formalized in Coq: M. Mayero, *The Three Gap Theorem (Steinhaus Conjecture)*,
  TYPES'99 (2000); arXiv:cs/0609124.
-/

@[expose] public section

namespace ThreeGap

/-- The `k`-th orbit point `{k·α}` as a representative in `[0,1)`. -/
noncomputable def x (α : ℝ) (k : ℕ) : ℝ := Int.fract ((k : ℝ) * α)

lemma x_mem_Ico (α : ℝ) (k : ℕ) : x α k ∈ Set.Ico (0 : ℝ) 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- **L1.** For irrational `α` the orbit `k ↦ {k·α}` is injective: the points are distinct.
(`fract (i·α) = fract (j·α)` gives `(i - j)·α ∈ ℤ`, forcing `α` rational unless `i = j`.) -/
theorem x_injective {α : ℝ} (hα : Irrational α) : Function.Injective (x α) := by
  intro i j hij
  rw [x, x, Int.fract_eq_fract] at hij
  obtain ⟨z, hz⟩ := hij
  by_contra hne
  have hd : ((i : ℝ) - j) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
  apply hα
  refine ⟨(z : ℚ) / ((i : ℚ) - (j : ℚ)), ?_⟩
  push_cast
  rw [div_eq_iff hd, ← hz]
  ring

/-- The set of the first `N` orbit points. -/
noncomputable def P (α : ℝ) (N : ℕ) : Finset ℝ := (Finset.range N).image (x α)

/-- For irrational `α`, the point set has exactly `N` elements. -/
lemma card_P {α : ℝ} (hα : Irrational α) (N : ℕ) : (P α N).card = N := by
  rw [P, Finset.card_image_of_injective _ (x_injective hα), Finset.card_range]

/-- Existence of the **closest one-sided return from the right**: for `2 ≤ N` there is an index
`p ∈ [1, N)` minimizing `{p·α}`. One of the two generators of the three-gap structure. -/
lemma exists_return_right (α : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ p ∈ Finset.Ico 1 N, ∀ i ∈ Finset.Ico 1 N, x α p ≤ x α i :=
  Finset.exists_min_image _ _ ⟨1, by simp only [Finset.mem_Ico]; omega⟩

/-- Existence of the **closest one-sided return from the left**: for `2 ≤ N` there is an index
`q ∈ [1, N)` maximizing `{q·α}` (minimizing the gap `1 - {q·α}` up to wraparound). The companion
generator. -/
lemma exists_return_left (α : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ q ∈ Finset.Ico 1 N, ∀ i ∈ Finset.Ico 1 N, x α i ≤ x α q :=
  Finset.exists_max_image _ _ ⟨1, by simp only [Finset.mem_Ico]; omega⟩

/-- **L2 (shift).** The orbit advances under the shift `+α`: `x α (k+1) = {x α k + α}`. Hence the
`N` points form a single `+α` shift-orbit on the circle — the structural engine of Liang's
rigid-gap argument. -/
lemma x_succ (α : ℝ) (k : ℕ) : x α (k + 1) = Int.fract (x α k + α) := by
  simp only [x]
  rw [Int.fract_eq_fract]
  refine ⟨⌊(k : ℝ) * α⌋, ?_⟩
  push_cast
  linear_combination Int.self_sub_fract ((k : ℝ) * α)

/-- The **sorted enumeration** of the `N` orbit points as an order embedding `Fin N ↪o ℝ`
(well-defined since the point set has exactly `N` elements for irrational `α`). `e hα N i` is the
`i`-th smallest point; consecutive differences will be the gaps. -/
noncomputable def e {α : ℝ} (hα : Irrational α) (N : ℕ) : Fin N ↪o ℝ :=
  (P α N).orderEmbOfFin (card_P hα N)

/-- Each sorted orbit point lies in `[0,1)`. -/
lemma e_mem_Ico {α : ℝ} (hα : Irrational α) (N : ℕ) (i : Fin N) :
    e hα N i ∈ Set.Ico (0 : ℝ) 1 := by
  have hmem : e hα N i ∈ P α N := by unfold e; exact Finset.orderEmbOfFin_mem _ _ _
  rw [P, Finset.mem_image] at hmem
  obtain ⟨k, _, hk⟩ := hmem
  rw [← hk]
  exact x_mem_Ico α k

/-- The **gap** (arc length) at sorted index `i`: the distance to the next point, or — at the last
index — the wraparound arc `1 + e 0 - e (N-1)`. The dependent `if` makes this correct for *all*
`N ≥ 1` (in particular the single arc of length `1` when `N = 1`). -/
noncomputable def gap {α : ℝ} (hα : Irrational α) {N : ℕ} (i : Fin N) : ℝ :=
  if h : (i : ℕ) + 1 < N then e hα N ⟨(i : ℕ) + 1, h⟩ - e hα N i
  else 1 + e hα N ⟨0, (Nat.zero_le _).trans_lt i.isLt⟩ - e hα N i

/-- **L3a.** Every gap is strictly positive. -/
lemma gap_pos {α : ℝ} (hα : Irrational α) {N : ℕ} (i : Fin N) : 0 < gap hα i := by
  unfold gap
  split
  · rename_i h
    have hlt : (i : Fin N) < ⟨(i : ℕ) + 1, h⟩ := by rw [Fin.lt_def]; exact Nat.lt_succ_self _
    have := (e hα N).strictMono hlt
    linarith
  · have hi := (e_mem_Ico hα N i).2
    have h0 := (e_mem_Ico hα N ⟨0, (Nat.zero_le _).trans_lt i.isLt⟩).1
    linarith

/-- **Key Fact A (length = jump).** The oriented arc length between two orbit points depends only
on the *index difference*: `{x_b − x_a} = {(b−a)·α}`. The structural reason the gaps cluster. -/
lemma fract_x_sub (α : ℝ) (a b : ℕ) :
    Int.fract (x α b - x α a) = Int.fract (((b : ℝ) - (a : ℝ)) * α) := by
  rw [Int.fract_eq_fract]
  exact ⟨⌊(a : ℝ) * α⌋ - ⌊(b : ℝ) * α⌋, by simp only [x, Int.fract]; push_cast; ring⟩

/-- The **cyclic successor** on sorted indices: `i ↦ i+1`, wrapping the last index back to `0`.
Matches the case split in `gap`. -/
def succIdx {N : ℕ} (i : Fin N) : Fin N :=
  if h : (i : ℕ) + 1 < N then ⟨(i : ℕ) + 1, h⟩
  else ⟨0, (Nat.zero_le _).trans_lt i.isLt⟩

/-- **Gap as a fractional part.** For `N ≥ 2`, the gap at sorted index `i` is the fractional part of
the oriented step to the cyclic successor: `gap i = {e (succIdx i) − e i}`. (Uniform across the
wraparound; this is where the `N = 1` single-arc-of-length-1 case is excluded.) -/
lemma gap_eq_fract {α : ℝ} (hα : Irrational α) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    gap hα i = Int.fract (e hα N (succIdx i) - e hα N i) := by
  unfold gap succIdx
  split_ifs with h
  · -- interior: `0 ≤ e⟨i+1⟩ − e i < 1`, so `fract` is the identity
    have hlt : (i : Fin N) < ⟨(i : ℕ) + 1, h⟩ := by rw [Fin.lt_def]; exact Nat.lt_succ_self _
    have hmono := (e hα N).strictMono hlt
    have h1 := (e_mem_Ico hα N ⟨(i : ℕ) + 1, h⟩).2
    have h0 := (e_mem_Ico hα N i).1
    rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
  · -- wraparound: `e 0 − e i ∈ (−1, 0)`, so `fract (e 0 − e i) = 1 + e 0 − e i`
    have hlt : (⟨0, (Nat.zero_le _).trans_lt i.isLt⟩ : Fin N) < i := by
      rw [Fin.lt_def]; change 0 < (i : ℕ); have := i.isLt; omega
    have hmono := (e hα N).strictMono hlt
    have h0 := (e_mem_Ico hα N ⟨0, (Nat.zero_le _).trans_lt i.isLt⟩).1
    have hi := (e_mem_Ico hα N i).2
    rw [← Int.fract_add_one (e hα N ⟨0, (Nat.zero_le _).trans_lt i.isLt⟩ - e hα N i),
        Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    ring

/-- Every sorted point is an orbit point: recover its orbit index `a < N`. -/
lemma exists_orbit_index {α : ℝ} (hα : Irrational α) {N : ℕ} (i : Fin N) :
    ∃ a, a < N ∧ x α a = e hα N i := by
  have hmem : e hα N i ∈ P α N := by unfold e; exact Finset.orderEmbOfFin_mem _ _ _
  rw [P, Finset.mem_image] at hmem
  obtain ⟨a, ha, hax⟩ := hmem
  rw [Finset.mem_range] at ha
  exact ⟨a, ha, hax⟩

/-- **The bridge.** For `N ≥ 2` every gap length is `{(b−a)·α}` for the orbit indices `a, b` of the
two consecutive sorted points it spans. Combines `gap_eq_fract` with Key Fact A. -/
lemma gap_eq_fract_jump {α : ℝ} (hα : Irrational α) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    ∃ a b, a < N ∧ b < N ∧ gap hα i = Int.fract (((b : ℝ) - (a : ℝ)) * α) := by
  obtain ⟨a, ha, hae⟩ := exists_orbit_index hα i
  obtain ⟨b, hb, hbe⟩ := exists_orbit_index hα (succIdx i)
  exact ⟨a, b, ha, hb, by rw [gap_eq_fract hα hN, ← hae, ← hbe, fract_x_sub]⟩

/-- **Oriented forward distance** from `x_a` to `x_c` on the circle: `{(c−a)·α}`. The sorting of the
orbit by this distance is what drives Liang's descent. -/
noncomputable def fwdDist (α : ℝ) (a c : ℕ) : ℝ := Int.fract (((c : ℝ) - (a : ℝ)) * α)

/-- Forward distance to a *different* orbit point is strictly positive (irrationality). -/
lemma fwdDist_pos {α : ℝ} (hα : Irrational α) {a c : ℕ} (h : a ≠ c) : 0 < fwdDist α a c := by
  rw [fwdDist, ← fract_x_sub]
  refine (Int.fract_nonneg _).lt_of_ne (fun heq => h ?_)
  have h1 : x α c - x α a = (⌊x α c - x α a⌋ : ℝ) := by
    have h2 := Int.fract_add_floor (x α c - x α a); rw [← heq] at h2; linarith
  have hc := x_mem_Ico α c; have ha := x_mem_Ico α a
  rw [Set.mem_Ico] at hc ha
  have hfloor : ⌊x α c - x α a⌋ = 0 := by
    have hlt : (⌊x α c - x α a⌋ : ℝ) < 1 := by rw [← h1]; linarith
    have hgt : (-1 : ℝ) < (⌊x α c - x α a⌋ : ℝ) := by rw [← h1]; linarith
    have h3 : ⌊x α c - x α a⌋ < 1 := by exact_mod_cast hlt
    have h4 : (-1 : ℤ) < ⌊x α c - x α a⌋ := by exact_mod_cast hgt
    omega
  rw [hfloor, Int.cast_zero] at h1
  exact (x_injective hα (by linarith : x α c = x α a)).symm

/-- `(a, b)` is a **gap** of the `N`-point orbit: `x_b` is the closest orbit point strictly forward
of `x_a` (no orbit point lies in the open arc from `x_a` to `x_b`). -/
def IsGap (α : ℝ) (N a b : ℕ) : Prop :=
  a < N ∧ b < N ∧ a ≠ b ∧ ∀ c, c < N → c ≠ a → fwdDist α a b ≤ fwdDist α a c

/-- The cyclic-sorted **successor minimizes forward distance**: among all other sorted points `e j`,
the immediate cyclic successor `e (succIdx i)` is closest going forward from `e i`. (Case split on
whether `i` is the last index and on `j ≷ i`; `fract` handles the wraparound uniformly.) -/
lemma fract_succ_le {α : ℝ} (hα : Irrational α) {N : ℕ} (i j : Fin N) (hj : j ≠ i) :
    Int.fract (e hα N (succIdx i) - e hα N i) ≤ Int.fract (e hα N j - e hα N i) := by
  have hei := e_mem_Ico hα N i; rw [Set.mem_Ico] at hei
  have hej := e_mem_Ico hα N j; rw [Set.mem_Ico] at hej
  by_cases hlast : (i : ℕ) + 1 < N
  · -- `i` is not the last index: `succIdx i = ⟨i+1⟩`, sitting just above `e i`
    have hsucc : succIdx i = (⟨(i : ℕ) + 1, hlast⟩ : Fin N) := by rw [succIdx, dif_pos hlast]
    rw [hsucc]
    have hes := e_mem_Ico hα N (⟨(i : ℕ) + 1, hlast⟩ : Fin N); rw [Set.mem_Ico] at hes
    have hii1 : (i : Fin N) < ⟨(i : ℕ) + 1, hlast⟩ := by rw [Fin.lt_def]; exact Nat.lt_succ_self _
    have hmono1 := (e hα N).strictMono hii1
    rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    rcases lt_trichotomy j i with hji | hji | hji
    · -- `j < i`: `e j < e i`, forward distance wraps to `e j - e i + 1`
      have hmono2 := (e hα N).strictMono hji
      rw [← Int.fract_add_one (e hα N j - e hα N i), Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
      linarith [hes.2, hej.1]
    · exact absurd hji hj
    · -- `j > i`: then `j ≥ i+1`, so `e j ≥ e⟨i+1⟩`
      have hmono2 := (e hα N).strictMono hji
      rw [Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
      have hle : (⟨(i : ℕ) + 1, hlast⟩ : Fin N) ≤ j := by
        rw [Fin.le_def]; change (i : ℕ) + 1 ≤ (j : ℕ); rw [Fin.lt_def] at hji; omega
      have := (e hα N).monotone hle
      linarith
  · -- `i` is the last index: `succIdx i = ⟨0⟩`, the minimum; every `j ≠ i` has `j < i`
    have hsucc : succIdx i = (⟨0, (Nat.zero_le _).trans_lt i.isLt⟩ : Fin N) := by
      rw [succIdx, dif_neg hlast]
    rw [hsucc]
    set u : Fin N := ⟨0, (Nat.zero_le _).trans_lt i.isLt⟩ with hu
    have heu := e_mem_Ico hα N u; rw [Set.mem_Ico] at heu
    have hji : j < i := by
      rcases lt_trichotomy j i with h | h | h
      · exact h
      · exact absurd h hj
      · exfalso; rw [Fin.lt_def] at h; have := i.isLt; have := j.isLt; omega
    have h0j : u ≤ j := by rw [hu, Fin.le_def]; exact Nat.zero_le _
    have hmono0 := (e hα N).monotone h0j
    have hmonoji := (e hα N).strictMono hji
    rw [← Int.fract_add_one (e hα N u - e hα N i), Int.fract_eq_self.2 ⟨by linarith, by linarith⟩,
        ← Int.fract_add_one (e hα N j - e hα N i), Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    linarith

/-- For `N ≥ 2` the cyclic successor is never a fixed point. -/
lemma succIdx_ne {N : ℕ} (hN : 2 ≤ N) (i : Fin N) : succIdx i ≠ i := by
  intro heq
  rw [succIdx] at heq
  split_ifs at heq with h
  · have : (i : ℕ) + 1 = (i : ℕ) := congrArg Fin.val heq
    omega
  · have h0 : (0 : ℕ) = (i : ℕ) := congrArg Fin.val heq
    have := i.isLt; omega

/-- Every orbit point `x_c` (for `c < N`) appears as some sorted point `e j`. -/
lemma exists_sorted_index {α : ℝ} (hα : Irrational α) {N : ℕ} {c : ℕ} (hc : c < N) :
    ∃ j : Fin N, e hα N j = x α c := by
  have hmem : x α c ∈ P α N := by
    rw [P, Finset.mem_image]; exact ⟨c, Finset.mem_range.2 hc, rfl⟩
  have hr : x α c ∈ Set.range (e hα N) := by
    rw [e, Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hmem
  obtain ⟨j, hj⟩ := hr
  exact ⟨j, hj⟩

/-- **The bridge.** The orbit indices `a, b` of two cyclic-consecutive sorted points `e i`,
`e (succIdx i)` form a gap `IsGap α N a b`: combine `fract_succ_le` (successor closest forward)
with surjectivity, transported through Key Fact A. -/
lemma isGap_of_succ {α : ℝ} (hα : Irrational α) {N : ℕ} (hN : 2 ≤ N) (i : Fin N)
    {a b : ℕ} (ha : a < N) (hae : x α a = e hα N i)
    (hb : b < N) (hbe : x α b = e hα N (succIdx i)) :
    IsGap α N a b := by
  refine ⟨ha, hb, ?_, ?_⟩
  · intro hab
    refine succIdx_ne hN i ((e hα N).injective ?_)
    rw [← hbe, ← hae, hab]
  · intro c hc hca
    obtain ⟨jc, hjc⟩ := exists_sorted_index hα hc
    have e1 : fwdDist α a b = Int.fract (e hα N (succIdx i) - e hα N i) := by
      rw [fwdDist, ← fract_x_sub, hae, hbe]
    have e2 : fwdDist α a c = Int.fract (e hα N jc - e hα N i) := by
      rw [fwdDist, ← fract_x_sub, hae, hjc]
    rw [e1, e2]
    refine fract_succ_le hα i jc ?_
    intro hjci
    refine hca (x_injective hα ?_)
    rw [hjci] at hjc
    rw [← hjc, hae]

/-- Forward distance from the base point `x_0` is just the orbit point itself. -/
lemma fwdDist_zero_left (α : ℝ) (k : ℕ) : fwdDist α 0 k = x α k := by
  rw [fwdDist, x, Nat.cast_zero, sub_zero]

/-- Nonzero orbit points are strictly positive. -/
lemma x_pos {α : ℝ} (hα : Irrational α) {k : ℕ} (hk : k ≠ 0) : 0 < x α k := by
  rw [← fwdDist_zero_left]; exact fwdDist_pos hα (Ne.symm hk)

/-- **R1.** The gap to the right of the base point `x_0` jumps by `p`: if `IsGap α N 0 b` then
`b = p` (`p` = closest return from the right). -/
lemma isGap_zero {α : ℝ} (hα : Irrational α) {N : ℕ}
    {p : ℕ} (hp_mem : p ∈ Finset.Ico 1 N) (hp : ∀ i ∈ Finset.Ico 1 N, x α p ≤ x α i)
    {b : ℕ} (hgap : IsGap α N 0 b) : b = p := by
  obtain ⟨_, hbN, hb0, hmin⟩ := hgap
  rw [Finset.mem_Ico] at hp_mem
  have hb1 : b ∈ Finset.Ico 1 N := by rw [Finset.mem_Ico]; exact ⟨by omega, hbN⟩
  have hbp : fwdDist α 0 b ≤ fwdDist α 0 p := hmin p hp_mem.2 (by omega)
  rw [fwdDist_zero_left, fwdDist_zero_left] at hbp
  exact x_injective hα (le_antisymm hbp (hp b hb1))

/-- **Descent step.** A gap `(a, b)` with both endpoints `≥ 1` whose forward arc does *not* reach
the next orbit point `x_N` (`fwdDist a b ≤ fwdDist a N`) pulls back under the shift `T⁻¹` to a gap
`(a−1, b−1)` of the *same* jump. The engine of Liang's descent. -/
lemma descent_step {α : ℝ} {N a b : ℕ} (hgap : IsGap α N a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hN' : fwdDist α a b ≤ fwdDist α a N) :
    IsGap α N (a - 1) (b - 1) := by
  obtain ⟨haN, hbN, hab, hmin⟩ := hgap
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro c hc hca
  have key : fwdDist α (a - 1) (b - 1) = fwdDist α a b := by
    rw [fwdDist, fwdDist]; congr 1; rw [Nat.cast_sub ha, Nat.cast_sub hb]; push_cast; ring
  have key2 : fwdDist α (a - 1) c = fwdDist α a (c + 1) := by
    rw [fwdDist, fwdDist]; congr 1; rw [Nat.cast_sub ha]; push_cast; ring
  rw [key, key2]
  by_cases hcN : c + 1 < N
  · exact hmin (c + 1) hcN (by omega)
  · rw [show c + 1 = N by omega]; exact hN'

/-- The base orbit point is `0`. -/
@[simp] lemma x_zero (α : ℝ) : x α 0 = 0 := by rw [x, Nat.cast_zero, zero_mul, Int.fract_zero]

/-- Forward distances from a common base point determine the target: `fwdDist a c = fwdDist a c'`
forces `c = c'`. -/
lemma fwdDist_inj {α : ℝ} (hα : Irrational α) {a c c' : ℕ}
    (h : fwdDist α a c = fwdDist α a c') : c = c' := by
  apply x_injective hα
  rw [fwdDist, fwdDist, ← fract_x_sub, ← fract_x_sub, Int.fract_eq_fract] at h
  obtain ⟨z, hz⟩ := h
  have hcc : x α c - x α c' = (z : ℝ) := by linarith
  have hc := x_mem_Ico α c; rw [Set.mem_Ico] at hc
  have hc' := x_mem_Ico α c'; rw [Set.mem_Ico] at hc'
  have hz0 : z = 0 := by
    have h1 : (z : ℝ) < 1 := by rw [← hcc]; linarith
    have h2 : (-1 : ℝ) < (z : ℝ) := by rw [← hcc]; linarith
    have h3 : z < 1 := by exact_mod_cast h1
    have h4 : (-1 : ℤ) < z := by exact_mod_cast h2
    omega
  rw [hz0, Int.cast_zero] at hcc; linarith

/-- A *backward* forward-distance (`c < a`) evaluates to `1 − x_{a−c}` (the wraparound
complement). -/
lemma fwdDist_eq_one_sub {α : ℝ} (hα : Irrational α) {a c : ℕ} (h : c < a) :
    fwdDist α a c = 1 - x α (a - c) := by
  have hac : a - c ≠ 0 := by omega
  have hne : Int.fract (((a - c : ℕ) : ℝ) * α) ≠ 0 := by
    have hp := x_pos hα hac; rw [x] at hp; exact ne_of_gt hp
  have h1 : ((c : ℝ) - (a : ℝ)) * α = -(((a - c : ℕ) : ℝ) * α) := by
    rw [Nat.cast_sub (le_of_lt h)]; ring
  rw [fwdDist, h1, Int.fract_neg hne, x]

/-- **R2.** The gap landing on the base point `x_0` comes from the maximum `x_q`: if `IsGap α N a 0`
then `a = q` (`q` = closest return from the left), so its jump is `−q`. -/
lemma isGap_to_zero {α : ℝ} (hα : Irrational α) {N : ℕ}
    {q : ℕ} (hq_mem : q ∈ Finset.Ico 1 N) (hq : ∀ i ∈ Finset.Ico 1 N, x α i ≤ x α q)
    {a : ℕ} (hgap : IsGap α N a 0) : a = q := by
  obtain ⟨haN, _, ha0, hmin⟩ := hgap
  rw [Finset.mem_Ico] at hq_mem
  have ha1 : a ∈ Finset.Ico 1 N := by rw [Finset.mem_Ico]; exact ⟨by omega, haN⟩
  have hxa1 := x_mem_Ico α a; rw [Set.mem_Ico] at hxa1
  have hxa_pos := x_pos hα (show a ≠ 0 by omega)
  have hmax : ∀ c, c < N → x α c ≤ x α a := by
    intro c hc
    by_cases hca : c = a
    · rw [hca]
    · have hm := hmin c hc hca
      rw [fwdDist, fwdDist, ← fract_x_sub, ← fract_x_sub, x_zero] at hm
      have hxc1 := x_mem_Ico α c; rw [Set.mem_Ico] at hxc1
      by_contra hlt; push Not at hlt
      have hfa : Int.fract (0 - x α a) = 1 - x α a := by
        rw [zero_sub, ← Int.fract_add_one (-x α a),
            Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]; ring
      have hfc : Int.fract (x α c - x α a) = x α c - x α a :=
        Int.fract_eq_self.2 ⟨by linarith, by linarith⟩
      rw [hfa, hfc] at hm; linarith
  exact x_injective hα (le_antisymm (hq a ha1) (hmax q hq_mem.2))

/-- **The successor of the last point `x_{N−1}` jumps by `−q`.** Since every other point lies
*backward* of `x_{N−1}`, its forward successor minimizes `{−d·α}` over `d ∈ [1, N−1]`, attained
at the maximum `d = q`. (One-sided window — this direction is clean.) -/
lemma isGap_last {α : ℝ} (hα : Irrational α) {N : ℕ}
    {q : ℕ} (hq_mem : q ∈ Finset.Ico 1 N) (hq : ∀ i ∈ Finset.Ico 1 N, x α i ≤ x α q)
    {c : ℕ} (hgap : IsGap α N (N - 1) c) : c = N - 1 - q := by
  obtain ⟨_, hcN, hcne, hmin⟩ := hgap
  rw [Finset.mem_Ico] at hq_mem
  set cq := N - 1 - q with hcq
  have hcqN : cq < N := by omega
  have hcqne : cq ≠ N - 1 := by omega
  refine fwdDist_inj hα (le_antisymm (hmin cq hcqN hcqne) ?_)
  have hc_lt : c < N - 1 := by omega
  rw [fwdDist_eq_one_sub hα hc_lt, fwdDist_eq_one_sub hα (show cq < N - 1 by omega),
      show N - 1 - cq = q by omega]
  have hle : x α (N - 1 - c) ≤ x α q := hq (N - 1 - c) (by rw [Finset.mem_Ico]; omega)
  linarith

/-- Forward distance to a point *ahead* of the base is the orbit point at the index gap. -/
lemma fwdDist_eq_x {α : ℝ} {a c : ℕ} (h : a ≤ c) : fwdDist α a c = x α (c - a) := by
  rw [fwdDist, x, Nat.cast_sub h]

/-- The shift `T⁻¹` preserves forward distance between two shifted endpoints. -/
lemma fwdDist_shift {α : ℝ} {k c : ℕ} (hk : 1 ≤ k) (hc : 1 ≤ c) :
    fwdDist α (k - 1) (c - 1) = fwdDist α k c := by
  rw [fwdDist, fwdDist]; congr 1; rw [Nat.cast_sub hk, Nat.cast_sub hc]; ring

/-- Shifting only the base advances the target index by one. -/
lemma fwdDist_shift' {α : ℝ} {k c : ℕ} (hk : 1 ≤ k) :
    fwdDist α (k - 1) c = fwdDist α k (c + 1) := by
  rw [fwdDist, fwdDist]; congr 1; rw [Nat.cast_sub hk]; push_cast; ring

/-- **Re-basing forward distance at `x_N`.** When `x_N` lies forward of `x_a` but no closer than
`x_d` (i.e. `fwdDist a N ≤ fwdDist a d`), the distance from `x_N` to `x_d` is the plain difference
`fwdDist a d − fwdDist a N`. This is what lets the R3 split reduce to inequalities at base `a`. -/
lemma fwdDist_sub {α : ℝ} {a d N : ℕ} (h : fwdDist α a N ≤ fwdDist α a d) :
    fwdDist α N d = fwdDist α a d - fwdDist α a N := by
  have h1 : fwdDist α a d < 1 := by rw [fwdDist]; exact Int.fract_lt_one _
  have h2 : (0 : ℝ) ≤ fwdDist α a N := by rw [fwdDist]; exact Int.fract_nonneg _
  have hge : 0 ≤ fwdDist α a d - fwdDist α a N := by linarith
  have hlt : fwdDist α a d - fwdDist α a N < 1 := by linarith
  rw [fwdDist, show ((d : ℝ) - (N : ℝ)) * α
      = (fwdDist α a d - fwdDist α a N)
        + ((⌊((d : ℝ) - (a : ℝ)) * α⌋ - ⌊((N : ℝ) - (a : ℝ)) * α⌋ : ℤ) : ℝ) from ?_]
  · rw [Int.fract_add_intCast, Int.fract_eq_self.2 ⟨hge, hlt⟩]
  · rw [fwdDist, fwdDist, Int.fract, Int.fract]; push_cast; ring

/-- **R3 split.** If the forward arc of a gap `(a, b)` (both endpoints `≥ 1`) reaches past the
next orbit point `x_N` (`fwdDist a N < fwdDist a b`), then `x_{N−1}` falls in the pulled-back
arc, splitting it into two genuine gaps: `(a−1, N−1)` (ending at the last point) and
`(N−1, b−1)` (starting there). -/
lemma isGap_split {α : ℝ} (hα : Irrational α) {N a b : ℕ} (hgap : IsGap α N a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hR3 : fwdDist α a N < fwdDist α a b) :
    IsGap α N (a - 1) (N - 1) ∧ IsGap α N (N - 1) (b - 1) := by
  obtain ⟨haN, hbN, hab, hmin⟩ := hgap
  have hN1 : 1 ≤ N := by omega
  refine ⟨⟨by omega, by omega, by omega, ?_⟩, ⟨by omega, by omega, by omega, ?_⟩⟩
  · -- `IsGap (a−1) (N−1)`: every competitor is at least as far as `x_N`
    intro c hc hca
    rw [fwdDist_shift ha hN1, fwdDist_shift' ha]
    by_cases hcN : c + 1 < N
    · exact le_of_lt (lt_of_lt_of_le hR3 (hmin (c + 1) hcN (by omega)))
    · exact le_of_eq (congrArg (fwdDist α a) (by omega : N = c + 1))
  · -- `IsGap (N−1) (b−1)`: re-base at `x_N`, then it is the base-`a` inequality
    intro c hc hca
    rw [fwdDist_shift hN1 hb, fwdDist_shift' hN1]
    have hc1 : c + 1 < N := by omega
    have hfb : fwdDist α N b = fwdDist α a b - fwdDist α a N := fwdDist_sub (le_of_lt hR3)
    by_cases hc1a : c + 1 = a
    · -- competitor wraps to `x_a` itself: distance `1 − fwdDist a N`, and `fwdDist a b < 1`
      rw [hc1a, show fwdDist α N a = 1 - fwdDist α a N by
            rw [fwdDist_eq_one_sub hα haN, fwdDist_eq_x (le_of_lt haN)], hfb]
      have : fwdDist α a b < 1 := by rw [fwdDist]; exact Int.fract_lt_one _
      linarith
    · have hge : fwdDist α a N ≤ fwdDist α a (c + 1) :=
        le_of_lt (lt_of_lt_of_le hR3 (hmin (c + 1) hc1 hc1a))
      rw [fwdDist_sub hge, hfb]
      linarith [hmin (c + 1) hc1 hc1a]

/-- `{ {p} + {q} } = {p + q}`: combining fractional parts. -/
lemma fract_fract_add (p q : ℝ) :
    Int.fract (Int.fract p + Int.fract q) = Int.fract (p + q) := by
  rw [show Int.fract p + Int.fract q = (p + q) - ((⌊p⌋ + ⌊q⌋ : ℤ) : ℝ) by
        rw [Int.fract, Int.fract]; push_cast; ring, Int.fract_sub_intCast]

/-- **Succ ⇒ pred form.** If `x_b` is the closest point forward of `x_a`, then `x_a` is the closest
point backward of `x_b`: `fwdDist a b ≤ fwdDist d b` for every `d`. (No point lies in the open arc,
read from either end.) -/
lemma succ_to_pred {α : ℝ} (hα : Irrational α) {N a b : ℕ} (hgap : IsGap α N a b) :
    ∀ d, d < N → d ≠ b → fwdDist α a b ≤ fwdDist α d b := by
  obtain ⟨haN, hbN, hab, hmin⟩ := hgap
  intro d hd hdb
  by_cases hda : d = a
  · rw [hda]
  · by_contra hlt; push Not at hlt
    have hcomb : fwdDist α a b = Int.fract (fwdDist α d b + fwdDist α a d) := by
      rw [fwdDist, fwdDist, fwdDist, fract_fract_add]; congr 1; ring
    have pdb : 0 < fwdDist α d b := fwdDist_pos hα hdb
    have pad : 0 < fwdDist α a d := fwdDist_pos hα (Ne.symm hda)
    have hadlt : fwdDist α a d < 1 := by rw [fwdDist]; exact Int.fract_lt_one _
    have hm := hmin d hd hda
    by_cases hsum : fwdDist α d b + fwdDist α a d < 1
    · rw [Int.fract_eq_self.2 ⟨by linarith, hsum⟩] at hcomb; linarith
    · push Not at hsum
      rw [show fwdDist α d b + fwdDist α a d = (fwdDist α d b + fwdDist α a d - 1) + 1 by ring,
          Int.fract_add_one, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩] at hcomb
      linarith

/-- **Reflection.** Reflecting the orbit through `k ↦ N−1−k` reverses orientation and carries a gap
`(a, b)` to the gap `(N−1−b, N−1−a)`. -/
lemma reflection_lemma {α : ℝ} (hα : Irrational α) {N a b : ℕ} (hgap : IsGap α N a b) :
    IsGap α N (N - 1 - b) (N - 1 - a) := by
  have hbnd := hgap
  obtain ⟨haN, hbN, hab, hmin⟩ := hbnd
  have e1 : fwdDist α (N - 1 - b) (N - 1 - a) = fwdDist α a b := by
    rw [fwdDist, fwdDist]; congr 1
    rw [Nat.cast_sub (by omega : a ≤ N - 1), Nat.cast_sub (by omega : b ≤ N - 1)]; ring
  refine ⟨by omega, by omega, by omega, ?_⟩
  intro c hc hcne
  have e2 : fwdDist α (N - 1 - b) c = fwdDist α (N - 1 - c) b := by
    rw [fwdDist, fwdDist]; congr 1
    rw [Nat.cast_sub (by omega : b ≤ N - 1), Nat.cast_sub (by omega : c ≤ N - 1)]; ring
  rw [e1, e2]
  exact succ_to_pred hα hgap (N - 1 - c) (by omega) (by omega)

/-- **The gap ending at the last point `x_{N−1}` jumps by `p`.** Mirror image of `isGap_zero` (R1)
under the orbit reflection `k ↦ N−1−k`: the reflected gap starts at `x_0`, so it jumps by `p`. -/
lemma isGap_pred_last {α : ℝ} (hα : Irrational α) {N : ℕ}
    {p : ℕ} (hp_mem : p ∈ Finset.Ico 1 N) (hp : ∀ i ∈ Finset.Ico 1 N, x α p ≤ x α i)
    {a : ℕ} (hgap : IsGap α N a (N - 1)) : ((N - 1 : ℕ) : ℤ) - (a : ℤ) = (p : ℤ) := by
  have hbnd := hgap
  obtain ⟨haN, _, hab, _⟩ := hbnd
  have hrefl := reflection_lemma hα hgap
  rw [Nat.sub_self] at hrefl
  have hp_eq := isGap_zero hα hp_mem hp hrefl
  omega

/-- **L7 — the crux (jump trichotomy), integer form.** Every gap `(a, b)` has jump
`b − a ∈ {p, −q, p − q}`. Strong induction on the left index `a`: base cases `a = 0` (R1) and
`b = 0` (R2); for an interior gap either the backward shift descends (jump preserved, `IH`) or
`x_N` is swallowed and the gap splits at `x_{N−1}` into a `+p` part and a `−q` part (R3). -/
lemma isGap_trichotomy {α : ℝ} (hα : Irrational α) {N : ℕ}
    {p : ℕ} (hp_mem : p ∈ Finset.Ico 1 N) (hp : ∀ i ∈ Finset.Ico 1 N, x α p ≤ x α i)
    {q : ℕ} (hq_mem : q ∈ Finset.Ico 1 N) (hq : ∀ i ∈ Finset.Ico 1 N, x α i ≤ x α q) :
    ∀ a b, IsGap α N a b →
      (b : ℤ) - a = p ∨ (b : ℤ) - a = -q ∨ (b : ℤ) - a = (p : ℤ) - q := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a IH =>
    intro b hgap
    obtain ⟨haN, hbN, hab, hmin⟩ := hgap
    rcases Nat.eq_zero_or_pos a with ha0 | ha1
    · subst ha0
      left
      have hb := isGap_zero hα hp_mem hp ⟨haN, hbN, hab, hmin⟩
      subst hb; simp
    · rcases Nat.eq_zero_or_pos b with hb0 | hb1
      · subst hb0
        right; left
        have ha := isGap_to_zero hα hq_mem hq ⟨haN, hbN, hab, hmin⟩
        subst ha; simp
      · by_cases hdesc : fwdDist α a b ≤ fwdDist α a N
        · -- descent: jump preserved, recurse on `a − 1`
          have hsub := descent_step ⟨haN, hbN, hab, hmin⟩ ha1 hb1 hdesc
          have hIH := IH (a - 1) (by omega) (b - 1) hsub
          have hcast : ((b - 1 : ℕ) : ℤ) - ((a - 1 : ℕ) : ℤ) = (b : ℤ) - a := by
            rw [Nat.cast_sub ha1, Nat.cast_sub hb1]; push_cast; ring
          rwa [hcast] at hIH
        · -- R3: split at `x_{N−1}`
          push Not at hdesc
          obtain ⟨hg1, hg2⟩ := isGap_split hα ⟨haN, hbN, hab, hmin⟩ ha1 hb1 hdesc
          have hpa := isGap_pred_last hα hp_mem hp hg1
          have hqb := isGap_last hα hq_mem hq hg2
          right; right
          have ha_eq : (a : ℤ) = (N : ℤ) - p := by
            rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_sub ha1] at hpa
            push_cast at hpa; omega
          have hb_eq : (b : ℤ) = (N : ℤ) - q := by
            rw [Finset.mem_Ico] at hq_mem
            have : b = N - q := by omega
            rw [this, Nat.cast_sub (by omega : q ≤ N)]
          rw [ha_eq, hb_eq]; ring

/-- **L7 — the crux (jump trichotomy).** Every gap length is one of the three return lengths
`{p·α}`, `{−q·α}`, `{(p−q)·α}`, where `p` (closest right return) and `q` (closest left return) are
the two generators. This is the heart of the three-gap theorem (Liang's rigid-gap argument). -/
lemma gap_mem_three {α : ℝ} (hα : Irrational α) {N : ℕ} (hN : 2 ≤ N)
    {p : ℕ} (hp_mem : p ∈ Finset.Ico 1 N) (hp : ∀ i ∈ Finset.Ico 1 N, x α p ≤ x α i)
    {q : ℕ} (hq_mem : q ∈ Finset.Ico 1 N) (hq : ∀ i ∈ Finset.Ico 1 N, x α i ≤ x α q)
    (i : Fin N) :
    gap hα i ∈ ({Int.fract ((p : ℝ) * α), Int.fract (-(q : ℝ) * α),
      Int.fract (((p : ℝ) - (q : ℝ)) * α)} : Finset ℝ) := by
  obtain ⟨a, ha, hae⟩ := exists_orbit_index hα i
  obtain ⟨b, hb, hbe⟩ := exists_orbit_index hα (succIdx i)
  have hgap : IsGap α N a b := isGap_of_succ hα hN i ha hae hb hbe
  have hge : gap hα i = fwdDist α a b := by
    rw [gap_eq_fract hα hN, ← hae, ← hbe, fract_x_sub, fwdDist]
  rcases isGap_trichotomy hα hp_mem hp hq_mem hq a b hgap with h | h | h
  · have : gap hα i = Int.fract ((p : ℝ) * α) := by
      rw [hge, fwdDist, show ((b : ℝ) - (a : ℝ)) = (p : ℝ) by exact_mod_cast h]
    rw [this]; simp
  · have : gap hα i = Int.fract (-(q : ℝ) * α) := by
      rw [hge, fwdDist, show ((b : ℝ) - (a : ℝ)) = -(q : ℝ) by exact_mod_cast h]
    rw [this]; simp
  · have : gap hα i = Int.fract (((p : ℝ) - (q : ℝ)) * α) := by
      rw [hge, fwdDist, show ((b : ℝ) - (a : ℝ)) = (p : ℝ) - (q : ℝ) by exact_mod_cast h]
    rw [this]; simp

/-- **The three-gap (Steinhaus / three-distance) theorem.** For irrational `α` and `N ≥ 1`, the
`N` points `{0·α}, …, {(N−1)·α}` cut the circle `ℝ ⧸ ℤ` into arcs taking at most **three** distinct
lengths. (First formalization in Lean; cf. Mayero's Coq proof, TYPES 2000.) -/
theorem three_gap {α : ℝ} (hα : Irrational α) (N : ℕ) :
    ((Finset.univ : Finset (Fin N)).image (gap hα)).card ≤ 3 := by
  by_cases h3 : N ≤ 3
  · -- `N ≤ 3`: at most `N` gaps, so trivially at most 3 lengths
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_univ, Fintype.card_fin]; exact h3
  · -- `N ≥ 4`: the genuine three-gap argument
    have hN2 : 2 ≤ N := by omega
    obtain ⟨p, hp_mem, hp⟩ := exists_return_right α hN2
    obtain ⟨q, hq_mem, hq⟩ := exists_return_left α hN2
    have hsub : (Finset.univ : Finset (Fin N)).image (gap hα) ⊆
        ({Int.fract ((p : ℝ) * α), Int.fract (-(q : ℝ) * α),
          Int.fract (((p : ℝ) - (q : ℝ)) * α)} : Finset ℝ) := by
      intro y hy
      rw [Finset.mem_image] at hy
      obtain ⟨i, _, rfl⟩ := hy
      exact gap_mem_three hα hN2 hp_mem hp hq_mem hq i
    exact le_trans (Finset.card_le_card hsub) Finset.card_le_three


end ThreeGap
