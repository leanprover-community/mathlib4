/-
Copyright (c) 2026 Felix Pernegger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Pernegger
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Functions of bounded r-variation

We study the `r`-variation, a generalisation of the usual bounded variation.

## Main definitions and results

* `rRVariationOn r f s` is the total `r`-variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `BoundedrVariationOn r f s` registers that the variation of `f` on `s` is finite.
* `LocallyBoundedrVariationOn r f s` registers that `f` has finite `r`-variation on any compact
  subinterval of `s`.
* `mono'` : `fun r ↦ rRVariationOn r f s` is antitone.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/

@[expose] public section

open scoped NNReal ENNReal Topology UniformConvergence
open Set Filter OrderDual Function

variable (r : ℝ≥0∞) {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The (extended-real-valued) variation of a function `f` on a set `s` inside a linear order is
the supremum of the sum of `edist (f (u (i+1))) (f (u i)) ^ r` over all finite increasing
sequences `u` in `s`. -/
noncomputable def rEVariationOn (r : ENNReal) (f : α → E) (s : Set α) : ℝ≥0∞ :=
  if r = 0 then ⨆ p : { t // Monotone t ∧ ∀ (i : ℕ), t i ∈ s },
    ↑(support fun i ↦ edist (f (p.val (↑i + 1))) (f (p.val ↑i))).encard else
  if r = ⊤ then ⨆ j : s × s, edist (f j.1) (f j.2) else
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    (∑ i ∈ Finset.range p.1,
    edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal) ^ r.toReal ⁻¹

/-- A function has bounded `r`-variation on a set `s` if its total `r`-variation there is finite. -/
def BoundedrVariationOn (f : α → E) (s : Set α) :=
  rEVariationOn r f s ≠ ∞

/-- A function has locally bounded `r`-variation on a set `s` if, given any interval `[a, b]` with
endpoints in `s`, then the function has finite `r`-variation on `s ∩ [a, b]`. -/
def LocallyBoundedrVariationOn (f : α → E) (s : Set α) :=
  ∀ a b, a ∈ s → b ∈ s → BoundedrVariationOn r f (s ∩ Icc a b)

/-! ### Basic computations of variation -/

namespace rEVariationOn

theorem rEVariationOn_zero (f : α → E) (s : Set α) :
    rEVariationOn 0 f s = ⨆ p : { t // Monotone t ∧ ∀ (i : ℕ), t i ∈ s },
    ↑(support fun i ↦ edist (f (p.val (↑i + 1))) (f (p.val ↑i))).encard := by
  simp only [rEVariationOn, ↓reduceIte]

theorem rEVariationOn_top (f : α → E) (s : Set α) :
    rEVariationOn ⊤ f s = ⨆ j : s × s, edist (f j.1) (f j.2) := by
  simp only [rEVariationOn, ENNReal.top_ne_zero, ↓reduceIte]

theorem rEVariationOn_ne_zero_ne_top {r : ℝ≥0∞} (hr : r ≠ 0) (hr' : r ≠ ⊤) (f : α → E) (s : Set α) :
    rEVariationOn r f s = ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
      (∑ i ∈ Finset.range p.1,
        edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal) ^ r.toReal ⁻¹ := by
  simp only [rEVariationOn, hr, hr', ↓reduceIte]

/-- The `r`-variation with `r = 1` is the usual `r`-variation of a function. -/
theorem eVariationOn' (f : α → E) (s : Set α) :
    rEVariationOn 1 f s = eVariationOn f s := by

  simp only [rEVariationOn, eVariationOn, one_ne_zero, ENNReal.one_ne_top, ↓reduceIte, ENNReal.toReal_one,
    inv_one, ENNReal.rpow_one]

--TODO: redefine `eVariationOn` with above equalility

theorem eq_of_edist_zero_on {f f' : α → E} {s : Set α} (h : ∀ ⦃x⦄, x ∈ s → edist (f x) (f' x) = 0) :
    rEVariationOn r f s = rEVariationOn r f' s := by
  by_cases h0 : r = 0
  · rw [h0, rEVariationOn_zero, rEVariationOn_zero]
    congr! 6 with p i
    rw [edist_congr_right (h <| p.prop.2 (i + 1)), edist_congr_left (h <| p.prop.2 i)]
  by_cases h1 : r = ⊤
  · rw [h1, rEVariationOn_top, rEVariationOn_top]
    congr! 2 with x
    rw [edist_congr_right <| h x.1.prop, edist_congr_left <| h x.2.prop]
  simp only [rEVariationOn, h0, ↓reduceIte, h1]
  congr! 5 with p i hi
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1)), edist_congr_left (h <| p.snd.prop.2 i)]

theorem eq_of_eqOn {f f' : α → E} {s : Set α} (h : EqOn f f' s) :
    rEVariationOn r f s = rEVariationOn r f' s := by
  apply eq_of_edist_zero_on r <| fun {x} hx ↦ by rw [h hx, edist_self]

variable {r}

theorem sum_le (hr : r ≠ 0) (hr' : r ≠ ⊤) {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    (∑ i ∈ Finset.range n,
    edist (f (u (i + 1))) (f (u i)) ^ r.toReal) ^ r.toReal ⁻¹ ≤ rEVariationOn r f s := by
  rw [rEVariationOn_ne_zero_ne_top hr hr']
  apply le_iSup_of_le ⟨n, u, hu, us⟩
  rfl

theorem sum_le' (hr : r ≠ 0) (hr' : r ≠ ⊤) {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    ∑ i ∈ Finset.range n,
    edist (f (u (i + 1))) (f (u i)) ^ r.toReal ≤ rEVariationOn r f s ^ r.toReal := by
  calc
    _ = ((∑ i ∈ Finset.range n,
        edist (f (u (i + 1))) (f (u i)) ^ r.toReal) ^ r.toReal ⁻¹) ^ r.toReal := by
      rw [ENNReal.rpow_inv_rpow]
      exact ENNReal.toReal_ne_zero.mpr ⟨hr, hr'⟩
    _ ≤ _ := by gcongr; exact sum_le hr hr' hu us

theorem edist_le (hr : r ≠ 0) (f : α → E) {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ rEVariationOn r f s := by
  by_cases hr' : r = ⊤
  · rw [hr', rEVariationOn_top]
    apply le_iSup_of_le ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    rfl
  wlog hxy : y ≤ x generalizing x y
  · rw [edist_comm]
    exact this hy hx (le_of_not_ge hxy)
  let u : ℕ → α := fun n => if n = 0 then y else x
  have hu : Monotone u := monotone_nat_of_le_succ fun
  | 0 => hxy
  | (_ + 1) => le_rfl
  have us : ∀ i, u i ∈ s := fun
  | 0 => hy
  | (_ + 1) => hx
  have := ENNReal.rpow_rpow_inv (ENNReal.toReal_ne_zero.mpr ⟨hr, hr'⟩) (edist (f x) (f y))
  simpa [u, Finset.sum_range_one, zero_add, this] using sum_le hr hr' (f := f) (n := 1) hu us

theorem sum_le_of_monotoneOn_Icc (hr : r ≠ 0) (hr' : r ≠ ⊤) {f : α → E} {s : Set α}
    {m n : ℕ} {u : ℕ → α} (hu : MonotoneOn u (Icc m n)) (us : ∀ i ∈ Icc m n, u i ∈ s) :
    (∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i)) ^ r.toReal) ^ r.toReal ⁻¹
      ≤ rEVariationOn r f s := by
  rcases le_total n m with hnm | hmn
  · simp only [Finset.Ico_eq_empty_of_le hnm,
      ENNReal.zero_rpow_of_pos <| inv_pos.mpr <| ENNReal.toReal_pos hr hr', Finset.sum_empty,
      zero_le]
  let π := projIcc m n hmn
  let v i := u (π i)
  calc
    (∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i)) ^ r.toReal) ^ r.toReal ⁻¹
        = (∑ i ∈ Finset.Ico m n, edist (f (v (i + 1))) (f (v i)) ^ r.toReal) ^ r.toReal ⁻¹ := by
      congr! 2 with i hi
      rw [Finset.mem_Ico] at hi
      simp only [v, π, projIcc_of_mem hmn ⟨hi.1, hi.2.le⟩,
        projIcc_of_mem hmn ⟨hi.1.trans i.le_succ, hi.2⟩]
    _ ≤ (∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) ^ r.toReal) ^ r.toReal ⁻¹ := by
      gcongr 1
      apply Finset.sum_mono_set
      intro
      simp
    _ ≤ rEVariationOn r f s :=
      sum_le hr hr' (fun i j h ↦ hu (π i).2 (π j).2 (monotone_projIcc hmn h)) fun i ↦ us _ (π i).2

theorem sum_le_of_monotoneOn_Iic (hr : r ≠ 0) (hr' : r ≠ ⊤) {f : α → E} {s : Set α} {n : ℕ}
    {u : ℕ → α} (hu : MonotoneOn u (Iic n)) (us : ∀ i ≤ n, u i ∈ s) :
    ((∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i))) ^ r.toReal)) ^ r.toReal ⁻¹
      ≤ rEVariationOn r f s := by
  simpa using sum_le_of_monotoneOn_Icc hr hr'
    (m := 0) (hu.mono Icc_subset_Iic_self) fun i hi ↦ us i hi.2

lemma iSup_rpow_eq_rpow_iSup {α : Type*} (f : α → ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p)
    (h : p ≠ 0 ∨ Nonempty α) :
    ⨆ x : α, f x ^ p = (⨆ x : α, f x) ^ p := by
  by_cases hα : Nonempty α
  · exact (Monotone.map_ciSup_of_continuousAt
      (Continuous.continuousAt ENNReal.continuous_rpow_const)
      (ENNReal.monotone_rpow_of_nonneg hp)).symm
  · have : IsEmpty α := not_nonempty_iff.mp hα
    simp only [iSup_of_empty', sSup_empty, bot_eq_zero',
      ENNReal.zero_rpow_of_pos (lt_of_le_of_ne hp (Ne.symm (h.resolve_right hα)))]

/-- One may push out the exponent `r` out of the definition of `r`-variation. -/
theorem rEVariationOn_eq_iSup_rpow (f : α → E) (s : Set α) (hr : r ≠ 0) (hr' : r ≠ ⊤) :
  rEVariationOn r f s = (⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    (∑ i ∈ Finset.range p.1,
    edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal)) ^ r.toReal ⁻¹ := by
  rw [rEVariationOn_ne_zero_ne_top hr hr', iSup_rpow_eq_rpow_iSup]
  · exact inv_nonneg.mpr ENNReal.toReal_nonneg
  · exact Or.inl (inv_ne_zero (ENNReal.toReal_ne_zero.mpr ⟨hr, hr'⟩))

theorem mono (f : α → E) {s t : Set α} (hst : t ⊆ s) :
    rEVariationOn r f t ≤ rEVariationOn r f s := by
  by_cases hr : r = 0
  · simp only [hr, rEVariationOn_zero, iSup_le_iff, Subtype.forall, and_imp]
    intro u u_mono u_mem
    apply le_iSup_of_le ⟨u, u_mono, fun i ↦ hst (u_mem i)⟩
    rfl
  by_cases hr' : r = ⊤
  · simp only [hr', rEVariationOn_top, iSup_le_iff, Prod.forall, Subtype.forall]
    intro a ha b hb
    simpa [hr'] using edist_le hr f (hst ha) (hst hb)
  rw [rEVariationOn_ne_zero_ne_top hr hr']
  simp only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp]
  intro n u hu ut
  exact sum_le hr hr' hu fun i => hst (ut i)

theorem rEVariationOn_of_empty (r : ℝ≥0∞) (f : α → E) : rEVariationOn r f ∅ = 0 := by
  unfold rEVariationOn; split_ifs <;> simp

theorem rEVariationOn_top_inv (h : r ≠ 0) (h' : r ≠ ∞) (f : α → E) (s : Set α)
    (hL : ∀ L : ℝ≥0, ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    L < ((∑ i ∈ Finset.range p.1,
    edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal)) ^ (r.toReal ⁻¹)) :
    rEVariationOn r f s = ∞ := by
  rw [rEVariationOn_ne_zero_ne_top h h']
  apply ENNReal.eq_top_of_forall_nnreal_le
  intro L
  obtain ⟨p, hp⟩ := hL L
  exact le_iSup_of_le p hp.le

theorem eVariationOn_top {f : α → E} {s : Set α}
    (h : r ≠ 0) (h' : r ≠ ∞) (hv : rEVariationOn r f s = ∞) (L : ℝ≥0) :
    ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    L < (∑ i ∈ Finset.range p.1,
    edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal) ^ (r.toReal ⁻¹) := by
  rw[rEVariationOn_ne_zero_ne_top h h' f s] at hv
  refine lt_iSup_iff.mp ?_
  rw[hv]
  simp only [ENNReal.coe_lt_top]

theorem eVariationOn_top' {f : α → E} {s : Set α}
    (h : r ≠ 0) (h' : r ≠ ∞) (hv : rEVariationOn r f s = ∞) (L : ℝ≥0) :
    ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    L < (∑ i ∈ Finset.range p.1,
    edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal) := by
  obtain ⟨p, hp⟩ := eVariationOn_top h h' hv (L^ (r.toReal) ⁻¹)
  use p
  apply (ENNReal.rpow_lt_rpow_iff (z := r.toReal ⁻¹) ?_).mp
  · have : (↑L : ℝ≥0∞) ^ r.toReal ⁻¹ = (↑(L ^ r.toReal ⁻¹) : ℝ≥0∞) := by
      apply ENNReal.rpow_ofNNReal
      simp only [inv_nonneg, ENNReal.toReal_nonneg]
    rw[this]
    exact hp
  simp only [inv_pos, ENNReal.toReal_pos h h']

theorem eVariationOn_top'' {f : α → E} {s : Set α}
    (h : r ≠ 0) (h' : r ≠ ∞) (hv : rEVariationOn r f s = ∞) (L : ℝ≥0) :
    ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    L < (∑ i ∈ Finset.range p.1,
    edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal) ^ r.toReal ⁻¹ :=
  eVariationOn_top h h' hv L

lemma ennreal_sum_rpow_le_rpow_sum (m : ℕ) (u : ℕ → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p) :
    ∑ n ∈ Finset.range m, (u n) ^ p ≤ (∑ n ∈ Finset.range m, u n) ^ p := by
  induction m with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_le]
  | succ m mh =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    calc
      ∑ x ∈ Finset.range m, u x ^ p + u m ^ p
        ≤ (∑ x ∈ Finset.range m, u x) ^ p + u m ^ p := by gcongr
      _ ≤ (∑ x ∈ Finset.range m, u x + u m) ^ p :=
        ENNReal.add_rpow_le_rpow_add (∑ x ∈ Finset.range m, u x) (u m) hp

lemma sum_lp_mono_p (m : ℕ) (u : ℕ → ℝ≥0∞) {p q : ℝ} (hp : 0 < p) (pq : p ≤ q) :
    (∑ n ∈ Finset.range m, (u n) ^ q) ^ q ⁻¹ ≤ (∑ n ∈ Finset.range m, (u n) ^ p) ^ p⁻¹ := by
  have hq := hp.trans_le pq
  have hrw : ∀ n, (u n) ^ q = ((u n) ^ p) ^ (q / p) := fun n ↦ by
    rw [← ENNReal.rpow_mul]; congr 1; field_simp
  have hinv : (p : ℝ) ⁻¹ = q / p * q ⁻¹ := by field_simp
  simp_rw [hrw]
  rw [hinv, ENNReal.rpow_mul]
  exact ENNReal.rpow_le_rpow
    (ennreal_sum_rpow_le_rpow_sum _ _ ((one_le_div₀ hp).mpr pq)) (inv_nonneg.mpr hq.le)

lemma ENNReal_sup_lt_top
    {α : Type*} [Inhabited α] {f : α → ℝ≥0∞}
    (h : ⨆ x : α, f x ≠ ∞) {ε : NNReal} (hε : 0 < ε) :
    ∃ b : α, ⨆ x : α, f x < f b + ε := by
  by_cases h0 : ⨆ x, f x = 0
  · exact ⟨default, h0 ▸ lt_of_lt_of_le (ENNReal.coe_pos.mpr hε) le_add_self⟩
  obtain ⟨b, hb⟩ := lt_iSup_iff.mp
    (ENNReal.sub_lt_self h h0 (ENNReal.coe_pos.mpr hε).ne')
  refine ⟨b, ?_⟩
  by_cases hle : (ε : ℝ≥0∞) ≤ ⨆ x, f x
  · rwa [ENNReal.sub_lt_iff_lt_right ENNReal.coe_ne_top hle] at hb
  · calc ⨆ x, f x < ε := not_le.mp hle
         _ ≤ f b + ε := le_add_self

theorem eVariationOn_lt_top {f : α → E} {s : Set α} (h : r ≠ 0) (h' : r ≠ ∞)
    (hv : rEVariationOn r f s ≠ ∞) {ε : NNReal} (hε : 0 < ε) (hI : s.Nonempty) :
    ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s }, rEVariationOn r f s <
    (∑ i ∈ Finset.range p.1,
    edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) ^ r.toReal) ^ (r.toReal ⁻¹) + ε := by
  rw[rEVariationOn_ne_zero_ne_top h h'] at *
  have : Inhabited (ℕ × { u // Monotone u ∧ ∀ (i : ℕ), u i ∈ s }) := by
    have := eVariationOn.nonempty_monotone_mem hI
    apply Classical.inhabited_of_nonempty instNonemptyProd
  exact ENNReal_sup_lt_top (h := hv) (hε := hε)

/-- The `r`-variation of a function is antitone on the exponent.
TODO : This also works for `r = ⊤`. -/
theorem mono' {r t : ℝ≥0∞} (f : α → E) (s : Set α) (hr : r ≠ 0) (ht : t ≠ ⊤) (rt : r ≤ t) :
    rEVariationOn t f s ≤ rEVariationOn r f s := by
  have hr' : r ≠ ∞ := ne_top_of_le_ne_top ht rt
  have ht' : t ≠ 0 := fun h ↦ hr (nonpos_iff_eq_zero.mp (h ▸ rt))
  by_cases hI : s.Nonempty
  swap
  · simp only [not_nonempty_iff_eq_empty.mp hI, rEVariationOn_of_empty, zero_le]
  have hrt := (ENNReal.toReal_le_toReal hr' ht).mpr rt
  have hpr := ENNReal.toReal_pos hr hr'
  refine ENNReal.le_of_forall_pos_le_add fun ε hε fin ↦ ?_
  have fin' : rEVariationOn t f s ≠ ⊤ := by
    intro htop
    apply fin.ne
    apply rEVariationOn_top_inv hr hr'
    intro L
    obtain ⟨p, hp⟩ := eVariationOn_top ht' ht htop L
    exact ⟨p, hp.trans_le (sum_lp_mono_p _ _ hpr hrt)⟩
  obtain ⟨p, ph⟩ := eVariationOn_lt_top ht' ht fin' hε hI
  apply le_of_lt at ph
  apply le_trans ph
  gcongr
  exact (sum_lp_mono_p _ _ hpr hrt).trans (sum_le hr hr' p.2.2.1 p.2.2.2)

-- TODO : This also holds for `r, t ∈ {0, ⊤}`
theorem boundedRVarationOn_mono {r t : ℝ≥0∞} (f : α → E) (s : Set α) (hr : r ≠ 0) (ht : t ≠ ⊤)
    (rt : r ≤ t) (h : BoundedrVariationOn r f s) :
    BoundedrVariationOn t f s :=
  ne_top_of_le_ne_top h <| mono' f s hr ht rt

theorem locallyBoundedRVarationOn_mono {r t : ℝ≥0∞} (f : α → E) (s : Set α) (hr : r ≠ 0)
    (ht : t ≠ ⊤) (rt : r ≤ t) (h : LocallyBoundedrVariationOn r f s) :
    LocallyBoundedrVariationOn t f s :=
  fun a b as bs ↦ boundedRVarationOn_mono f (s ∩ Icc a b) hr ht rt (h a b as bs)

theorem one_le_rEVariationOn_zero {f : α → E} {s : Set α}
      (h : ∃ᵉ (x ∈ s) (y ∈ s), edist (f x) (f y) ≠ 0) :
    1 ≤ rEVariationOn 0 f s := by
  rw [rEVariationOn_zero]
  obtain ⟨x, hx, y, hy, xy⟩ := h
  wlog hxy : y ≤ x
  · exact this (f := f) (s := s) y hy x hx (edist_comm (f x) (f y) ▸ xy) (le_of_not_ge hxy)
  let u : ℕ → α := fun n => if n = 0 then y else x
  have hu : Monotone u := monotone_nat_of_le_succ fun
  | 0 => hxy
  | (_ + 1) => le_rfl
  have us : ∀ i, u i ∈ s := fun
  | 0 => hy
  | (_ + 1) => hx
  apply le_iSup_of_le ⟨u, hu, us⟩
  rw [← ENat.toENNReal_one]
  apply ENat.toENNReal_mono
  apply Set.one_le_encard_iff_nonempty.mpr
  use 0
  simp [u, xy]

theorem eq_zero_iff (f : α → E) {s : Set α} :
    rEVariationOn r f s = 0 ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) = 0 := by
  constructor
  · by_cases hr : r = 0
    · rw [hr]
      contrapose!
      exact fun h ↦ (ne_of_lt <| lt_of_lt_of_le one_pos <| one_le_rEVariationOn_zero h).symm
    rintro h x xs y ys
    rw [← nonpos_iff_eq_zero, ← h]
    exact edist_le hr f xs ys
  · rintro h
    by_cases hr : r = 0
    · rw [hr, rEVariationOn_zero]
      simp only [ENNReal.iSup_eq_zero, Subtype.forall, and_imp]
      intro u u_mono u_mem
      have : (fun i ↦ edist (f (u (i + 1))) (f (u i))) = 0 := by
        ext n
        apply h
        · exact (u_mem (n + 1))
        · exact mem_preimage.mp (u_mem n)
      simp [this]
    by_cases hr' : r = ⊤
    · rw [hr', rEVariationOn_top]
      simpa
    rw [rEVariationOn_ne_zero_ne_top hr hr', ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    refine ENNReal.rpow_eq_zero_iff.mpr <| Or.inl ⟨?_, inv_pos.mpr <| ENNReal.toReal_pos hr hr'⟩
    exact Finset.sum_eq_zero <| fun i _ ↦ ENNReal.rpow_eq_zero_iff.mpr
      <| Or.inl ⟨h _ (us i.succ) _ (us i), ENNReal.toReal_pos hr hr'⟩

theorem constant_on {f : α → E} {s : Set α} (hf : (f '' s).Subsingleton) :
    rEVariationOn r f s = 0 := by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩, edist_self]

@[simp]
protected theorem subsingleton (f : α → E) {s : Set α} (hs : s.Subsingleton) :
    rEVariationOn r f s = 0 :=
  constant_on (hs.image f)

end rEVariationOn

-- TODO : (Semi-)Continuity, limits, superadditivity, connections with Hölder functions
