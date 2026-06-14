/-
Copyright (c) 2026 Mai Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mai Zhang
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
/-!
# Shapley-Folkman Lemma

The Shapley-Folkman lemma states that for a finite family of nonempty subsets `Sᵢ ⊆ ℝᵈ`,
any `x ∈ convexHull ℝ (∑ Sᵢ)` can be written as `x = ∑ fᵢ` with `fᵢ ∈ convexHull ℝ (Sᵢ)`
where `fᵢ ∉ Sᵢ` for at most `d` indices.

The lemma originated in the study of approximate equilibria in non-convex economies
[Anderson, Khan and Rashid, *Approximate equilibria with bounds independent of
preferences*][anderson1982]; see also [Geller, *An improved bound for approximate
equilibria*][geller1986] and [Starr, *Quasi-equilibria in markets with non-convex
preferences*][starr1969].

## References

* [Anderson, Khan and Rashid, *Approximate equilibria with bounds independent of
  preferences*][anderson1982]
* [Geller, *An improved bound for approximate equilibria*][geller1986]
* [Starr, *Quasi-equilibria in markets with non-convex preferences*][starr1969]
-/
@[expose] public section
open Finset
open scoped Pointwise
namespace ShapleyFolkman
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- If `x ∈ convexHull ℝ s` but `x ∉ s`, then `x` can be written as a convex combination
of at least two points of `s`. This is the key observation that starts the depth argument. -/
theorem convexHull_not_mem_requires_two {s : Set E} {x : E}
    (hx_hull : x ∈ convexHull ℝ s) (hx_not : x ∉ s) :
    ∃ (n : ℕ) (f : Fin n → E) (w : Fin n → ℝ),
      2 ≤ n ∧ (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧
      ∑ i, w i = 1 ∧ ∑ i, w i • f i = x := by
  obtain ⟨ι, hFin, z, w, hz_range, _, hw_pos, hw_sum, hx_eq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx_hull
  letI : Fintype ι := hFin
  have hn : 2 ≤ Fintype.card ι := by
    by_contra h_lt; push Not at h_lt
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
    · haveI h_empty : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
      simp at hw_sum
    · have h1 : Fintype.card ι = 1 := Nat.le_antisymm (by omega) hpos
      obtain ⟨i₀, hi₀⟩ := Fintype.card_eq_one_iff.mp h1
      have huniq : (Finset.univ : Finset ι) = {i₀} := by ext i; simp [hi₀ i]
      have hw_one : w i₀ = 1 := by
        calc
          w i₀ = (∑ x : ι, w x) := by rw [huniq, Finset.sum_singleton]
          _ = 1 := hw_sum
      have hx_in_s : x = z i₀ := by
        calc
          x = (∑ i : ι, w i • z i) := hx_eq.symm
          _ = w i₀ • z i₀ := by rw [huniq, Finset.sum_singleton]
          _ = z i₀ := by rw [hw_one, one_smul]
      exact hx_not (hx_in_s ▸ hz_range (Set.mem_range.mpr ⟨i₀, rfl⟩))
  letI e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, z ∘ e, w ∘ e, hn,
    fun i => hz_range (Set.mem_range.mpr ⟨e i, rfl⟩),
    fun i => hw_pos (e i),
    (Equiv.sum_comp e w).trans hw_sum, ?_⟩
  calc
    ∑ i : Fin (Fintype.card ι), (w ∘ e) i • (z ∘ e) i
        = ∑ j : ι, w j • z j := Equiv.sum_comp e (fun j => w j • z j)
    _ = x := hx_eq

/-- If `x ∈ convexHull ℝ s \ s`, then `x = t·a + (1-t)·b` with `a ∈ s`, `b ∈ convexHull ℝ s`,
and `0 < t < 1`. This binary representation is used to reduce depth. -/
lemma binary_repr_of_mem_convexHull_not_mem {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) :
    ∃ (a b : E) (t : ℝ), a ∈ s ∧ b ∈ convexHull ℝ s ∧ 0 < t ∧ t < 1 ∧
      x = t • a + (1 - t) • b := by
  obtain ⟨n, f, w, hn, hf_mem, hw_pos, hw_sum, hx_eq⟩ :=
    convexHull_not_mem_requires_two hx hxs
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hr_pos : 0 < ∑ i : Fin (m + 1), w i.succ :=
    Finset.sum_pos (fun i _ => hw_pos i.succ) ⟨0, Finset.mem_univ _⟩
  have hwsum : w 0 + (∑ i : Fin (m + 1), w i.succ) = 1 := by
    rw [← Fin.sum_univ_succ w, hw_sum]
  set r := ∑ i : Fin (m + 1), w i.succ with hr_def
  have hr_eq : r = 1 - w 0 := by linarith
  have hw0_lt1 : w 0 < 1 := by linarith
  let a := f 0
  set b := r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ with hb_def
  have hb_mem : b ∈ convexHull ℝ s := by
    have hcm : b = (Finset.univ : Finset (Fin (m + 1))).centerMass
        (fun i => w i.succ) (fun i => f i.succ) := by
      simp [hb_def, Finset.centerMass, hr_def]
    rw [hcm]
    apply Finset.centerMass_mem_convexHull
    · intro i _; exact le_of_lt (hw_pos i.succ)
    · simpa [hr_def] using hr_pos
    · intro i _; exact hf_mem i.succ
  refine ⟨a, b, w 0, hf_mem 0, hb_mem, hw_pos 0, hw0_lt1, ?_⟩
  calc
    x = ∑ i : Fin (m + 2), w i • f i := hx_eq.symm
    _ = w 0 • f 0 + ∑ i : Fin (m + 1), w i.succ • f i.succ := by
      rw [Fin.sum_univ_succ (fun i => w i • f i)]
    _ = w 0 • a + r • (r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ) := by
      rw [smul_inv_smul₀ (ne_of_gt hr_pos)]
    _ = w 0 • a + (1 - w 0) • (r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ) := by rw [hr_eq]
    _ = w 0 • a + (1 - w 0) • b := by rw [hb_def]

/--
A `Decomposition` of a point `x` over a family of sets `S` indexed by `t` is a choice of
points `fᵢ ∈ convexHull ℝ (S i)` for each `i ∈ t` such that `∑ i ∈ t, fᵢ = x`.
-/
structure Decomposition {ι : Type*} (S : ι → Set E) (t : Finset ι) (x : E) where
  /-- The chosen point `fᵢ` for each index `i`. -/
  point : ι → E
  /-- Each `fᵢ` belongs to `convexHull ℝ (S i)` for `i ∈ t`. -/
  mem_convexHull : ∀ i ∈ t, point i ∈ convexHull ℝ (S i)
  /-- The points sum to `x`. -/
  sum_eq : ∑ i ∈ t, point i = x

/--
The set of indices `i ∈ t` where `d.point i` lies outside `S i`. These are the "bad" indices
that require a nontrivial convex combination.
-/
noncomputable def Decomposition.excessIndices {ι : Type*} {S : ι → Set E}
    {t : Finset ι} {x : E} (d : Decomposition S t x) : Finset ι := by
  classical
    exact t.filter (fun i => d.point i ∉ S i)

/--
The Carathéodory depth of `x` with respect to `s` is the minimum number `n` such that
`x` can be written as a convex combination of `n` points of `s` with strictly positive weights.
-/
noncomputable def caraDepth (s : Set E) (x : E) : ℕ :=
  sInf {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
    (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x}

/-- A witness of depth `n` gives `caraDepth s x ≤ n`. -/
lemma caraDepth_le {s : Set E} {x : E} {n : ℕ}
    (f : Fin n → E) (w : Fin n → ℝ)
    (hf : ∀ i, f i ∈ s) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) (heq : ∑ i, w i • f i = x) :
    caraDepth s x ≤ n :=
  Nat.sInf_le ⟨f, w, hf, hw, hsum, heq⟩

/-- If `x ∈ convexHull ℝ s` but `x ∉ s`, then `caraDepth s x ≥ 2`. -/
lemma caraDepth_ge_two {s : Set E} {x : E}
    (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) : 2 ≤ caraDepth s x := by
  classical
  by_contra h
  have hle : caraDepth s x ≤ 1 := by omega
  have h_nonempty : {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
      (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x}.Nonempty := by
    obtain ⟨n, f, w, _, hf, hw, hws, hxe⟩ := convexHull_not_mem_requires_two hx hxs
    exact ⟨n, f, w, hf, hw, hws, hxe⟩
  have hcases : caraDepth s x = 0 ∨ caraDepth s x = 1 := by omega
  have hmem := Nat.sInf_mem h_nonempty
  rcases hcases with h0 | h1
  · -- caraDepth = 0: empty sum can't equal 1
    have hmem0 : ∃ (f : Fin 0 → E) (w : Fin 0 → ℝ),
        (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x := by
      have : 0 ∈ {n | ∃ (f : Fin n → E) (w : Fin n → ℝ),
          (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x} := h0 ▸ hmem
      exact this
    obtain ⟨f, w, _, _, hws, _⟩ := hmem0
    simp at hws
  · -- caraDepth = 1: single vertex means x ∈ s
    have hmem1 : ∃ (f : Fin 1 → E) (w : Fin 1 → ℝ),
        (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x := by
      have hmem1' : 1 ∈ {n | ∃ (f : Fin n → E) (w : Fin n → ℝ),
          (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x} := h1 ▸ hmem
      exact hmem1'
    obtain ⟨f, w, hf, _, hws, hxe⟩ := hmem1
    have hw0 : w 0 = 1 := by simpa [Fin.sum_univ_one] using hws
    have hx0 : x = f 0 := by
      simpa [Fin.sum_univ_one, hw0] using hxe.symm
    exact hxs (hx0 ▸ hf 0)

/-- If `x ∈ convexHull ℝ s` and `x ∉ s`, then there exists `a ∈ s` and
`b ∈ convexHull ℝ s` with `caraDepth s b ≤ caraDepth s x - 1` and `x = t·a + (1-t)·b`
for some `0 < t < 1`. This is the key depth-reduction step. -/
lemma caraDepth_decr {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) (hxs : x ∉ s) :
    ∃ (a b : E) (t : ℝ), a ∈ s ∧ b ∈ convexHull ℝ s ∧ 0 < t ∧ t < 1 ∧
    x = t • a + (1 - t) • b ∧ caraDepth s b ≤ caraDepth s x - 1 := by
  have h_nonempty : {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
      (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x}.Nonempty := by
    obtain ⟨n, f, w, _, hf, hw, hws, hxe⟩ := convexHull_not_mem_requires_two hx hxs
    exact ⟨n, f, w, hf, hw, hws, hxe⟩
  have hN_ge2 : 2 ≤ caraDepth s x := caraDepth_ge_two hx hxs
  obtain ⟨m, hm⟩ : ∃ m, caraDepth s x = m + 2 := ⟨caraDepth s x - 2, by omega⟩
  have hmem := Nat.sInf_mem h_nonempty
  have hmem_val : ∃ (f : Fin (m + 2) → E) (w : Fin (m + 2) → ℝ),
      (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x := by
    have hmem' : (m + 2 : ℕ) ∈ {n | ∃ (f : Fin n → E) (w : Fin n → ℝ),
        (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = x} := hm ▸ hmem
    simpa using hmem'
  obtain ⟨f, w, hf, hw, hws, hxe⟩ := hmem_val
  have hr_pos : 0 < ∑ i : Fin (m + 1), w i.succ :=
    Finset.sum_pos (fun i _ => hw i.succ) ⟨0, Finset.mem_univ _⟩
  set r := ∑ i : Fin (m + 1), w i.succ with hr_def
  have h_total : w 0 + r = 1 := by rw [hr_def, ← Fin.sum_univ_succ w, hws]
  have hr_eq : r = 1 - w 0 := by linarith
  have hw0_lt1 : w 0 < 1 := by linarith
  let a := f 0
  set b := r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ with hb_def
  have hb_mem : b ∈ convexHull ℝ s := by
    have hcm : b = (Finset.univ : Finset (Fin (m + 1))).centerMass
        (fun i => w i.succ) (fun i => f i.succ) := by
      simp [hb_def, Finset.centerMass, hr_def]
    rw [hcm]
    apply Finset.centerMass_mem_convexHull
    · intro i _; exact le_of_lt (hw i.succ)
    · simpa [hr_def] using hr_pos
    · intro i _; exact hf i.succ
  have hx_eq' : x = w 0 • a + (1 - w 0) • b := by
    calc
      x = ∑ i : Fin (m + 2), w i • f i := hxe.symm
      _ = w 0 • f 0 + ∑ i : Fin (m + 1), w i.succ • f i.succ := by
        rw [Fin.sum_univ_succ (fun i => w i • f i)]
      _ = w 0 • a + r • (r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ) := by
        rw [smul_inv_smul₀ (ne_of_gt hr_pos)]
      _ = w 0 • a + (1 - w 0) • (r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ) := by rw [hr_eq]
      _ = w 0 • a + (1 - w 0) • b := by rw [hb_def]
  have htemp : caraDepth s b ≤ m + 1 :=
    caraDepth_le (fun i : Fin (m + 1) => f i.succ) (fun i => w i.succ / r)
      (fun i => hf i.succ)
      (fun i => div_pos (hw i.succ) hr_pos)
      (calc
        ∑ i : Fin (m + 1), (w i.succ / r)
            = (∑ i : Fin (m + 1), w i.succ) / r := by simp [Finset.sum_div]
        _ = r / r := by rw [hr_def]
        _ = 1 := div_self (ne_of_gt hr_pos))
      (calc
        ∑ i : Fin (m + 1), (w i.succ / r) • f i.succ
            = ∑ i : Fin (m + 1), (r⁻¹ * w i.succ) • f i.succ := by
          simp [div_eq_inv_mul]
        _ = ∑ i : Fin (m + 1), r⁻¹ • (w i.succ • f i.succ) := by
          simp [mul_smul]
        _ = r⁻¹ • ∑ i : Fin (m + 1), w i.succ • f i.succ := by
          simp [Finset.smul_sum]
        _ = b := hb_def.symm)
  have hb_depth : caraDepth s b ≤ caraDepth s x - 1 := by
    rw [hm]
    omega
  exact ⟨a, b, w 0, hf 0, hb_mem, hw 0, hw0_lt1, hx_eq', hb_depth⟩

/-- In a finite-dimensional vector space, any family of more than `d = finrank ℝ E` vectors
is linearly dependent. Returns nontrivial coefficients `cᵢ` such that `∑ cᵢ • vᵢ = 0`. -/
lemma exists_relation_finset [FiniteDimensional ℝ E]
    {ι : Type*} (L : Finset ι) (v : ι → E) (hcard : Module.finrank ℝ E < L.card) :
    ∃ (c : ι → ℝ), (∃ i ∈ L, c i ≠ 0) ∧ ∑ i ∈ L, c i • v i = 0 := by
  classical
  let S := {x // x ∈ L}
  letI : Fintype S := Finset.fintypeCoeSort L
  have hcardS : Fintype.card S = L.card := Fintype.card_coe L
  have h_not_li : ¬ LinearIndependent ℝ (fun (x : S) => v x.val) := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [hcardS] at hle
    omega
  rw [Fintype.not_linearIndependent_iff] at h_not_li
  obtain ⟨c_sub, hsum, x₀, hx₀⟩ := h_not_li
  -- Extend c_sub to all of ι, zero outside L
  let c : ι → ℝ := fun i => if h : i ∈ L then c_sub ⟨i, h⟩ else 0
  have hsum' : ∑ x : S, c_sub x • v x.val = 0 := hsum
  have h_attach_eq : L.attach = (Finset.univ : Finset S) := by
    ext x; simp [S]
  refine ⟨c, ?_, ?_⟩
  · -- non-trivial coefficient
    refine ⟨x₀.val, x₀.property, ?_⟩
    dsimp [c]
    simp [x₀.property, hx₀]
  · -- sum equals zero
    dsimp [c]
    calc
      ∑ i ∈ L, (if h : i ∈ L then c_sub ⟨i, h⟩ else 0) • v i
          = ∑ x ∈ L.attach, (if h : (x : ι) ∈ L then c_sub ⟨x, h⟩ else 0) • v x := by
        let f : ι → E := fun i => (if h : i ∈ L then c_sub ⟨i, h⟩ else 0) • v i
        rw [← Finset.sum_attach (s := L) (f := f)]
      _ = ∑ x ∈ L.attach, c_sub x • v x.val := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        simp [x.property]
      _ = ∑ x ∈ (Finset.univ : Finset S), c_sub x • v x.val := by rw [h_attach_eq]
      _ = ∑ x : S, c_sub x • v x.val := rfl
      _ = 0 := hsum'

/-- Taking a convex combination of an S-point `a` and a point `y` of depth `k`
yields depth at most `k + 1`. -/
lemma caraDepth_le_add_one_of_S {s : Set E} {a y : E} (ha : a ∈ s)
    (hy : y ∈ convexHull ℝ s) (t' : ℝ) (ht : 0 ≤ t') (ht' : t' ≤ 1) :
    caraDepth s (t' • a + (1 - t') • y) ≤ 1 + caraDepth s y := by
  set k := caraDepth s y
  -- Handle boundary cases where weights can be zero
  by_cases ht0 : t' = 0
  · have h0 : (0 : ℝ) • a + ((1 : ℝ) - (0 : ℝ)) • y = y := by simp
    rw [ht0, h0]; omega
  by_cases ht1 : t' = 1
  · have h1 : (1 : ℝ) • a + ((1 : ℝ) - (1 : ℝ)) • y = a := by simp
    rw [ht1, h1]
    have ha_cara : caraDepth s a ≤ 1 :=
      caraDepth_le (fun (_ : Fin 1) => a) (fun _ => 1) (fun _ => ha)
        (by intro i; exact by norm_num) (by simp) (by simp)
    omega
  have ht_pos : 0 < t' := by
    by_contra! h
    apply ht0; linarith
  have ht_lt1 : t' < 1 := by
    by_contra! h
    apply ht1; linarith
  have h_one_minus_pos : 0 < 1 - t' := by linarith
  -- Extract minimal representation of y with k vertices
  have hk_mem : k ∈ {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
      (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = y} := by
    have h_nonempty : {n : ℕ | ∃ (f : Fin n → E) (w : Fin n → ℝ),
        (∀ i, f i ∈ s) ∧ (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • f i = y}.Nonempty := by
      obtain ⟨ι, hFin, z, w, hz_range, _, hw_pos, hw_sum, hy_eq⟩ :=
        eq_pos_convex_span_of_mem_convexHull hy
      letI : Fintype ι := hFin
      letI e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
      refine ⟨Fintype.card ι, z ∘ e, w ∘ e,
        fun i => hz_range (Set.mem_range.mpr ⟨e i, rfl⟩),
        fun i => hw_pos (e i),
        (Equiv.sum_comp e w).trans hw_sum, ?_⟩
      calc
        ∑ i : Fin (Fintype.card ι), (w ∘ e) i • (z ∘ e) i
            = ∑ j : ι, w j • z j := Equiv.sum_comp e (fun j => w j • z j)
        _ = y := hy_eq
    exact Nat.sInf_mem h_nonempty
  obtain ⟨f, w, hf, hw, hws, hy_eq⟩ := hk_mem
  -- Construct 1+k vertex representation of t'·a + (1-t')·y
  let f' : Fin (k + 1) → E := fun i => Fin.cases a f i
  let w' : Fin (k + 1) → ℝ := fun i => Fin.cases t' (fun j => (1 - t') * w j) i
  have hf'_mem : ∀ i, f' i ∈ s := by
    intro i; refine Fin.cases ?_ ?_ i
    · exact ha
    · exact fun j => hf j
  have hw'_pos : ∀ i, 0 < w' i := by
    intro i; refine Fin.cases ?_ ?_ i
    · exact ht_pos
    · intro j; exact mul_pos h_one_minus_pos (hw j)
  have hws' : ∑ i : Fin (k + 1), w' i = 1 := by
    calc
      ∑ i : Fin (k + 1), w' i = w' 0 + ∑ i : Fin k, w' (Fin.succ i) := Fin.sum_univ_succ _
      _ = t' + ∑ i : Fin k, ((1 - t') * w i) := by simp [w']
      _ = t' + (1 - t') * (∑ i : Fin k, w i) := by rw [Finset.mul_sum]
      _ = t' + (1 - t') * 1 := by rw [hws]
      _ = 1 := by ring
  have h_eq' : ∑ i : Fin (k + 1), w' i • f' i = t' • a + (1 - t') • y := by
    calc
      ∑ i : Fin (k + 1), w' i • f' i
          = w' 0 • f' 0 + ∑ i : Fin k, w' (Fin.succ i) • f' (Fin.succ i) := Fin.sum_univ_succ _
      _ = t' • a + ∑ i : Fin k, ((1 - t') * w i) • f i := by simp [w', f']
      _ = t' • a + ∑ i : Fin k, (1 - t') • (w i • f i) := by simp [mul_smul]
      _ = t' • a + (1 - t') • (∑ i : Fin k, w i • f i) := by rw [Finset.smul_sum]
      _ = t' • a + (1 - t') • y := by rw [hy_eq]
  have hle := caraDepth_le f' w' hf'_mem hw'_pos hws' h_eq'
  omega

-- Step 6: Flat representation (Lemma 1.3)

/-- A flat representation of `x` over the family `S` indexed by `t`: for each `i ∈ t` we
have a finite vertex set `Vᵢ ⊆ S i`, a distinguished anchor vertex `aᵢ ∈ Vᵢ`, and
strictly positive weights `w_{i,e} > 0` with `Σ_{e ∈ Vᵢ} w_{i,e} = 1` such that
`x = Σ_i Σ_{e ∈ Vᵢ} w_{i,e}·e`.

The *excess* of vertex set `Vᵢ` is `|Vᵢ| - 1`. The anchor is used to absorb the
perturbation when we find a linear dependence among the excess vectors `e - aᵢ`. -/
structure FlatRepr {ι : Type*} (S : ι → Set E) (t : Finset ι) (x : E) where
  /-- Finite vertex set `Vᵢ ⊆ S i` for each `i ∈ t`. -/
  verts : (i : t) → Finset E
  /-- Each vertex in `verts i` belongs to `S i.val`. -/
  h_verts_sub : ∀ (i : t), ↑(verts i) ⊆ S i.val
  /-- Distinguished anchor vertex `aᵢ ∈ Vᵢ`. -/
  anchor : (i : t) → E
  /-- The anchor belongs to its vertex set. -/
  h_anchor : ∀ (i : t), anchor i ∈ verts i
  /-- Strictly positive convex weights `w_{i,e} > 0`. -/
  w : (i : t) → E → ℝ
  /-- All weights are strictly positive on the vertex set. -/
  hw_pos : ∀ (i : t) e, e ∈ verts i → 0 < w i e
  /-- The weights sum to 1 over each vertex set. -/
  hw_sum : ∀ (i : t), ∑ e ∈ verts i, w i e = 1
  /-- The weighted sum of vertices equals `x`. -/
  h_sum : ∑ i : t, ∑ e ∈ verts i, w i e • e = x

namespace FlatRepr

/-- Total excess = cardinality of the sigma set of excess pairs (i, e ≠ anchor_i).
    Defined as sigma cardinality so that EIdx.card = totalExcess is definitional. -/
noncomputable def totalExcess {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) : ℕ := ∑ i : t, ((d.verts i).card - 1)

open Classical in
/-- Each point in the final decomposition: f_i = Σ_{e∈V_i} w_{i,e}·e ∈ conv(S_i) -/
noncomputable def toDecomposition {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) : Decomposition S t x where
  point i :=
    if hi : i ∈ t then
      ∑ e ∈ d.verts ⟨i, hi⟩, d.w ⟨i, hi⟩ e • e
    else 0
  mem_convexHull i hi := by
    suffices (∑ e ∈ d.verts ⟨i, hi⟩, d.w ⟨i, hi⟩ e • e) ∈ convexHull ℝ (S i) by
      simpa [hi]
    have hsum1 : ∑ e ∈ d.verts ⟨i, hi⟩, d.w ⟨i, hi⟩ e = 1 := d.hw_sum ⟨i, hi⟩
    have hpos : 0 < ∑ e ∈ d.verts ⟨i, hi⟩, d.w ⟨i, hi⟩ e := by rw [hsum1]; norm_num
    have h_eq : (d.verts ⟨i, hi⟩).centerMass (d.w ⟨i, hi⟩) id
        = ∑ e ∈ d.verts ⟨i, hi⟩, d.w ⟨i, hi⟩ e • e := by
      simp [Finset.centerMass, hsum1]
    rw [← h_eq]
    exact Finset.centerMass_mem_convexHull (t := d.verts ⟨i, hi⟩) (w := d.w ⟨i, hi⟩)
      (fun e he => le_of_lt (d.hw_pos ⟨i, hi⟩ e he)) hpos
      (fun e he => d.h_verts_sub ⟨i, hi⟩ (by simpa using he))
  sum_eq :=
    -- Same calc as in the main theorem's hf_sum
    calc
      ∑ i ∈ t, (if hi : i ∈ t then
          ∑ e ∈ d.verts ⟨i, hi⟩, d.w ⟨i, hi⟩ e • e else 0)
        = ∑ i : t, (if hi : (i : ι) ∈ t then
            ∑ e ∈ d.verts ⟨(i : ι), hi⟩, d.w ⟨(i : ι), hi⟩ e • e else 0) :=
          (Finset.sum_attach (s := t) (f := fun i =>
            (if hi : i ∈ t then
              ∑ e ∈ d.verts ⟨i, hi⟩, d.w ⟨i, hi⟩ e • e else 0))).symm
      _ = ∑ i : t, ∑ e ∈ d.verts ⟨(i : ι), i.property⟩,
          d.w ⟨(i : ι), i.property⟩ e • e := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [i.property]
      _ = ∑ i : t, ∑ e ∈ d.verts i, d.w i e • e := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rcases i with ⟨i_val, hi_val⟩
        rfl
      _ = x := d.h_sum

end FlatRepr

open Classical in
/-- Given a linear relation `c` on the excess set of `d`, construct perturbation coefficients
`β_{i,e}` satisfying `Σ_e β_{i,e} = 0` for each `i` and `Σ_{i,e} β_{i,e}·e = 0`.

Used in `flatRepr_reduce` to perturb weights while preserving the sum. -/
noncomputable def betaPerturbation {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) (c : (Σ (_ : t), E) → ℝ) (i : t) (e : E) : ℝ :=
  if e = d.anchor i then
    -(∑ e' ∈ (d.verts i).erase (d.anchor i), c ⟨i, e'⟩)
  else if e ∈ (d.verts i).erase (d.anchor i) then c ⟨i, e⟩ else 0

open scoped Classical in
lemma betaPerturbation_anchor {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) (c : (Σ (_ : t), E) → ℝ) (i : t) :
    betaPerturbation d c i (d.anchor i) =
      -(∑ e' ∈ (d.verts i).erase (d.anchor i), c ⟨i, e'⟩) := by
  dsimp [betaPerturbation]; rw [if_pos rfl]

open scoped Classical in
lemma betaPerturbation_erase {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) (c : (Σ (_ : t), E) → ℝ) (i : t) (e : E)
    (he : e ∈ (d.verts i).erase (d.anchor i)) : betaPerturbation d c i e = c ⟨i, e⟩ := by
  dsimp [betaPerturbation]; rw [if_neg (Finset.ne_of_mem_erase he), if_pos he]

open scoped Classical in
/-- The perturbation coefficients have zero sum over each vertex set: `Σ_{e∈Vᵢ} β_{i,e} = 0`. -/
lemma betaPerturbation_sum_zero {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) (c : (Σ (_ : t), E) → ℝ) (i : t) :
    ∑ e ∈ d.verts i, betaPerturbation d c i e = 0 := by
  rw [← Finset.insert_erase (d.h_anchor i),
    Finset.sum_insert (Finset.notMem_erase _ _), betaPerturbation_anchor d c i]
  have h_erase : ∑ e ∈ (d.verts i).erase (d.anchor i), betaPerturbation d c i e =
      ∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ :=
    Finset.sum_congr rfl (fun e he => betaPerturbation_erase d c i e he)
  rw [h_erase]; ring

open scoped Classical in
/-- The perturbation coefficients have zero weighted sum:
`Σ_{i∈t} Σ_{e∈Vᵢ} β_{i,e}·e = 0`, assuming `c` is a linear relation on `e - aᵢ`. -/
lemma betaPerturbation_smul_zero {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) (c : (Σ (_ : t), E) → ℝ)
    (hc : ∑ i : t, ∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • (e - d.anchor i) = 0) :
    ∑ i : t, ∑ e ∈ d.verts i, betaPerturbation d c i e • e = 0 := by
  have h_perturbation_zero : (∑ i : t, ∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • e)
      - (∑ i : t, (∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩) • d.anchor i) = 0 := by
    calc
      (∑ i : t, ∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • e)
          - (∑ i : t, (∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩) • d.anchor i)
        = ∑ i : t, ((∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • e)
            - (∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩) • d.anchor i) := by
          rw [Finset.sum_sub_distrib]
      _ = ∑ i : t, ((∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • e)
            - (∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • d.anchor i)) := by
          simp [Finset.sum_smul]
      _ = ∑ i : t, ∑ e ∈ (d.verts i).erase (d.anchor i),
          (c ⟨i, e⟩ • e - c ⟨i, e⟩ • d.anchor i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_sub_distrib]
      _ = ∑ i : t, ∑ e ∈ (d.verts i).erase (d.anchor i),
          c ⟨i, e⟩ • (e - d.anchor i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          refine Finset.sum_congr rfl (fun e _ => ?_); rw [smul_sub]
      _ = 0 := hc
  have key (i : t) : ∑ e ∈ d.verts i, betaPerturbation d c i e • e =
      (∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • e)
        - (∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩) • d.anchor i := by
    rw [← Finset.insert_erase (d.h_anchor i),
      Finset.sum_insert (Finset.notMem_erase _ _), betaPerturbation_anchor d c i]
    have h_erase : ∑ e ∈ (d.verts i).erase (d.anchor i), betaPerturbation d c i e • e =
        ∑ e ∈ (d.verts i).erase (d.anchor i), c ⟨i, e⟩ • e :=
      Finset.sum_congr rfl (fun e he => by rw [betaPerturbation_erase d c i e he])
    rw [h_erase]
    simp [neg_smul, add_comm, sub_eq_add_neg]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib]
  exact h_perturbation_zero

omit [Module ℝ E] in
open scoped Classical in
/-- If `y ∈ ∑ i ∈ t, S i` (Minkowski sum), then `y` can be written as `∑ p i` where each
`p i ∈ S i`. -/
lemma mem_finset_sum_sets {ι : Type*} {S : ι → Set E} (t : Finset ι) (y : E)
    (hy : y ∈ ∑ i ∈ t, S i) : ∃ p : ι → E, (∀ i ∈ t, p i ∈ S i) ∧ y = ∑ i ∈ t, p i := by
  induction t using Finset.induction_on generalizing y with
  | empty =>
      rw [Finset.sum_empty, Set.mem_zero] at hy
      exact ⟨fun _ => 0, by simp, by simp [hy]⟩
  | insert k t' hk ih =>
      rw [Finset.sum_insert hk] at hy
      have hmem := Set.mem_add.mp hy
      rcases hmem with ⟨a, ha, b, hb, hab⟩
      obtain ⟨p, hp, hpb⟩ := ih b hb
      refine ⟨fun i => if i = k then a else p i, ?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with (rfl | hi')
        · simp [ha]
        · have hne : i ≠ k := by rintro rfl; exact hk hi'
          simp [hne, hp i hi']
      · calc
          y = a + b := hab.symm
          _ = a + (∑ i ∈ t', p i) := by rw [hpb]
          _ = a + (∑ i ∈ t', (if i = k then a else p i)) := by
            refine congrArg (a + ·) (Finset.sum_congr rfl (fun i hi => ?_))
            have hne : i ≠ k := by rintro rfl; exact hk hi
            simp [hne]
          _ = (if k = k then a else p k) + ∑ i ∈ t', (if i = k then a else p i) := by simp
          _ = ∑ i ∈ insert k t', (if i = k then a else p i) := by rw [Finset.sum_insert hk]

section Construction

variable [FiniteDimensional ℝ E] {ι : Type*}

omit [FiniteDimensional ℝ E] in
/-- Given `x ∈ convexHull ℝ (∑ S i)`, construct an initial `FlatRepr` for `x`.
This uses Carathéodory's theorem to write `x` as a convex combination of summands,
then expands each summand via `mem_finset_sum_sets`. -/
lemma exists_flatRepr_of_mem {S : ι → Set E} {t : Finset ι} {x : E}
    (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ (_ : FlatRepr S t x), True := by
  classical
  obtain ⟨J, hFinJ, zc, wc, hz_range, _, hwc_pos, hwc_sum, hx_eq⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype J := hFinJ
  have hdec (j : J) : ∃ p : ι → E, (∀ i ∈ t, p i ∈ S i) ∧ zc j = ∑ i ∈ t, p i :=
    mem_finset_sum_sets t (zc j) (hz_range (Set.mem_range_self j))
  choose p hp hpz using hdec
  have hJne : Nonempty J := by
    rcases isEmpty_or_nonempty J with (h | h)
    · haveI : IsEmpty J := h
      have hsum0 : (∑ j : J, wc j) = 0 := by simp
      rw [hsum0] at hwc_sum
      linarith
    · exact h
  obtain ⟨j₀⟩ := hJne
  let verts : (i : t) → Finset E :=
    fun i => (Finset.univ : Finset J).image (fun j => p j i.val)
  let anchor : (i : t) → E := fun i => p j₀ i.val
  let w : (i : t) → E → ℝ :=
    fun i e => ∑ j ∈ (Finset.univ : Finset J), (if p j i.val = e then wc j else 0)
  have h_verts_sub : ∀ (i : t), ↑(verts i) ⊆ S i.val := by
    intro i e he
    rcases Finset.mem_image.mp he with ⟨j, _, rfl⟩
    exact hp j i.val i.property
  have h_anchor : ∀ (i : t), anchor i ∈ verts i := by
    intro i; apply Finset.mem_image.mpr; exact ⟨j₀, Finset.mem_univ _, rfl⟩
  have hw_pos : ∀ (i : t) e, e ∈ verts i → 0 < w i e := by
    intro i e he
    rcases Finset.mem_image.mp he with ⟨j, hj, rfl⟩
    dsimp [w]
    have hterm : (if p j i.val = p j i.val then wc j else 0) = wc j := by simp
    have h_nonneg : ∀ k, 0 ≤ (if p k i.val = p j i.val then wc k else 0) := by
      intro k; split <;> simp [le_of_lt (hwc_pos k)]
    have h_single : (if p j i.val = p j i.val then wc j else 0) ≤
        ∑ k ∈ Finset.univ, (if p k i.val = p j i.val then wc k else 0) :=
      Finset.single_le_sum (fun k _ => h_nonneg k) (Finset.mem_univ j)
    rw [hterm] at h_single
    exact lt_of_lt_of_le (hwc_pos j) h_single
  have hw_sum : ∀ (i : t), ∑ e ∈ verts i, w i e = 1 := by
    intro i; dsimp [w, verts]
    calc
      ∑ e ∈ (Finset.univ.image (fun j => p j i.val)),
          (∑ j ∈ Finset.univ, (if p j i.val = e then wc j else 0))
        = ∑ j ∈ Finset.univ, ∑ e ∈ (Finset.univ.image (fun j => p j i.val)),
            (if p j i.val = e then wc j else 0) := by rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.univ, wc j := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.sum_eq_single (p j i.val)]
        · simp
        · intro e he hne; simp [hne.symm]
        · intro h; exfalso; apply h; exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      _ = 1 := hwc_sum
  have h_sum : (∑ i : t, ∑ e ∈ verts i, w i e • e) = x := by
    dsimp [w, verts]
    calc
      (∑ i : t, ∑ e ∈ (Finset.univ.image (fun j => p j i.val)),
          (∑ j ∈ Finset.univ, (if p j i.val = e then wc j else 0)) • e)
        = (∑ i : t, ∑ e ∈ (Finset.univ.image (fun j => p j i.val)),
            ∑ j ∈ Finset.univ, ((if p j i.val = e then wc j else 0) • e)) := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun e _ => ?_))
          rw [Finset.sum_smul]
      _ = (∑ i : t, ∑ j ∈ Finset.univ,
            ∑ e ∈ (Finset.univ.image (fun j => p j i.val)),
              ((if p j i.val = e then wc j else 0) • e)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_comm]
      _ = (∑ i : t, ∑ j ∈ Finset.univ, wc j • p j i.val) := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j hj => ?_))
        rw [Finset.sum_eq_single (p j i.val)]
        · simp
        · intro e he hne; simp [hne.symm]
        · intro h; exfalso; apply h; exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      _ = (∑ j ∈ Finset.univ, ∑ i : t, wc j • p j i.val) := by rw [Finset.sum_comm]
      _ = (∑ j ∈ Finset.univ, wc j • (∑ i : t, p j i.val)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [← Finset.smul_sum]
      _ = (∑ j ∈ Finset.univ, wc j • (∑ i ∈ t, p j i)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        have hsub : (∑ i : t, p j i.val) = (∑ i ∈ t, p j i) := by
          simpa using (Finset.sum_attach (s := t) (f := p j))
        rw [hsub]
      _ = (∑ j ∈ Finset.univ, wc j • zc j) := by
        refine Finset.sum_congr rfl (fun j _ => ?_); rw [hpz j]
      _ = x := hx_eq
  refine ⟨{
    verts := verts
    h_verts_sub := h_verts_sub
    anchor := anchor
    h_anchor := h_anchor
    w := w
    hw_pos := hw_pos
    hw_sum := hw_sum
    h_sum := h_sum
  }, trivial⟩

end Construction

open scoped Classical in
/-- The cardinality of the sigma set of excess pairs `(i, e ≠ aᵢ)` equals `totalExcess`.
This lemma is a technical bridge between the sigma-based construction and the sum formula. -/
lemma card_sigma_totalExcess {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) :
    (Finset.sigma Finset.univ (fun (i : t) => (d.verts i).erase (d.anchor i))).card
    = d.totalExcess := by
  classical
    have h_sigma_raw := Finset.card_sigma (s := t.attach)
      (t := fun i => (d.verts i).erase (d.anchor i))
    calc
      (Finset.sigma Finset.univ (fun (i : t) => (d.verts i).erase (d.anchor i))).card
          = (t.attach.sigma (fun i => (d.verts i).erase (d.anchor i))).card := by simp
      _ = ∑ i ∈ t.attach, ((d.verts i).erase (d.anchor i)).card := h_sigma_raw
      _ = ∑ i ∈ t.attach, ((d.verts i).card - 1) := by
            induction t.attach using Finset.induction_on with
            | empty => simp
            | insert a s ha IH =>
                rw [Finset.sum_insert ha, Finset.sum_insert ha]
                rw [IH, Finset.card_erase_of_mem (d.h_anchor a)]
      _ = (∑ i : t, ((d.verts i).card - 1)) := by simp
      _ = d.totalExcess := rfl

section Reduction

variable [FiniteDimensional ℝ E] {ι : Type*}

/-- **Core reduction**: if `totalExcess > finrank ℝ E`, we can perturb the flat representation
to strictly decrease `totalExcess`. The construction uses a linear dependence among the vectors
`e - aᵢ` (for `e ∈ Vᵢ \ {aᵢ}`) to define perturbation coefficients `β_{i,e}`, then picks
the maximal feasible scaling `tmax` so that one weight hits zero and the excess decreases. -/
lemma flatRepr_reduce {S : ι → Set E} {t : Finset ι} {x : E}
    (d : FlatRepr S t x) (h_exceed : Module.finrank ℝ E < d.totalExcess) :
    ∃ (d' : FlatRepr S t x), d'.totalExcess < d.totalExcess := by
  classical
  let EIdx : Finset (Σ (i : t), E) :=
    Finset.sigma Finset.univ (fun (i : t) => (d.verts i).erase (d.anchor i))
  -- Both sides count the same pairs: |{(i,e) | e ∈ V_i, e ≠ a_i}| = Σ(|V_i|-1)
  have hEIdx_card : EIdx.card = d.totalExcess := by
    dsimp [EIdx]; exact card_sigma_totalExcess d
  have hEIdx_exceed : Module.finrank ℝ E < EIdx.card := by
    rw [hEIdx_card]; exact h_exceed
  let v : (Σ (i : t), E) → E := fun p => p.2 - d.anchor p.1
  obtain ⟨c, ⟨p₀, hp₀, hc_ne⟩, hc_sum⟩ :=
    exists_relation_finset EIdx v hEIdx_exceed
  have hc_nested : ∑ i : t, ∑ e ∈ (d.verts i).erase (d.anchor i),
      c ⟨i, e⟩ • (e - d.anchor i) = 0 := by
    simpa [EIdx, Finset.sum_sigma, v] using hc_sum
  have hβ_sum_zero (i : t) : ∑ e ∈ d.verts i, betaPerturbation d c i e = 0 :=
    betaPerturbation_sum_zero d c i
  have hβ_smul_zero : ∑ i : t, ∑ e ∈ d.verts i, betaPerturbation d c i e • e = 0 :=
    betaPerturbation_smul_zero d c hc_nested
  -- Step B: Some betaPerturbation d c is negative
  let AllIdx : Finset (Σ i : t, E) := Finset.sigma Finset.univ (fun i => d.verts i)
  let Neg : Finset (Σ i : t, E) := AllIdx.filter (fun idx => betaPerturbation d c idx.1 idx.2 < 0)
  have hNeg_ne : Neg.Nonempty := by
    -- hc_ne gives a specific p₀ where c p₀ ≠ 0, via `hp₀ : p₀ ∈ EIdx`
    have he₁ : p₀.2 ∈ (d.verts p₀.1).erase (d.anchor p₀.1) := (Finset.mem_sigma.mp hp₀).2
    by_cases hsign : ∃ idx ∈ EIdx, c idx < 0
    · obtain ⟨idx₀, hidx₀_mem, hlt₀⟩ := hsign
      have he₀ : idx₀.2 ∈ (d.verts idx₀.1).erase (d.anchor idx₀.1) :=
        (Finset.mem_sigma.mp hidx₀_mem).2
      refine ⟨idx₀, Finset.mem_filter.mpr ⟨
        Finset.mem_sigma.mpr ⟨Finset.mem_univ _, Finset.mem_of_mem_erase he₀⟩, ?_⟩⟩
      rw [betaPerturbation_erase d c idx₀.1 idx₀.2 he₀]; exact hlt₀
    · -- No c < 0 exists. Then c p₀ ≥ 0, and since c p₀ ≠ 0, we have c p₀ > 0.
      -- This makes Σ c > 0, so β(anchor) = -Σ c < 0, giving a negative β witness.
      have h_nonneg_c : ∀ idx ∈ EIdx, 0 ≤ c idx := by
        intro idx hidx
        by_contra! hneg
        exact hsign ⟨idx, hidx, hneg⟩
      have hc_nonneg : 0 ≤ c p₀ := h_nonneg_c p₀ (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, he₁⟩)
      have hc_pos : 0 < c p₀ := hc_nonneg.lt_of_ne hc_ne.symm
      have h_sum_pos : 0 < ∑ e' ∈ (d.verts p₀.1).erase (d.anchor p₀.1), c ⟨p₀.1, e'⟩ := by
        have h_single : c ⟨p₀.1, p₀.2⟩ ≤
            ∑ e' ∈ (d.verts p₀.1).erase (d.anchor p₀.1), c ⟨p₀.1, e'⟩ :=
          Finset.single_le_sum (fun e' he' =>
            h_nonneg_c ⟨p₀.1, e'⟩ (Finset.mem_sigma.mpr ⟨Finset.mem_univ _, he'⟩)) he₁
        have : c p₀ = c ⟨p₀.1, p₀.2⟩ := rfl
        rw [this] at hc_pos
        linarith
      refine ⟨⟨p₀.1, d.anchor p₀.1⟩, Finset.mem_filter.mpr ⟨
        Finset.mem_sigma.mpr ⟨Finset.mem_univ _, d.h_anchor p₀.1⟩, ?_⟩⟩
      rw [betaPerturbation_anchor d c p₀.1]
      linarith
  -- Steps C-E: t_max, feasibility, boundary
  obtain ⟨idxM, hidxM_mem, hidxM_min⟩ :=
    Finset.exists_min_image Neg
      (fun idx => d.w idx.1 idx.2 / (-betaPerturbation d c idx.1 idx.2)) hNeg_ne
  have hβM : betaPerturbation d c idxM.1 idxM.2 < 0 := (Finset.mem_filter.mp hidxM_mem).2
  have hidxM_verts : idxM.2 ∈ d.verts idxM.1 :=
    (Finset.mem_sigma.mp (Finset.mem_filter.mp hidxM_mem).1).2
  let tmax : ℝ := d.w idxM.1 idxM.2 / (-betaPerturbation d c idxM.1 idxM.2)
  -- Step D: feasibility
  have feasible (i : t) (e : E) (he : e ∈ d.verts i) :
      0 ≤ d.w i e + tmax * betaPerturbation d c i e := by
    rcases lt_or_ge (betaPerturbation d c i e) 0 with (hb | hb)
    · have hmem : (⟨i, e⟩ : Σ i : t, E) ∈ Neg :=
        Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨Finset.mem_univ _, he⟩, hb⟩
      have hmin := hidxM_min ⟨i, e⟩ hmem
      dsimp only [] at hmin
      have hnegβ : 0 < -betaPerturbation d c i e := by linarith
      rw [le_div_iff₀ hnegβ] at hmin
      -- hmin: tmax * (-betaPerturbation d c i e) ≤ d.w i e
      have hkey : tmax * betaPerturbation d c i e = -(tmax * (-betaPerturbation d c i e)) := by ring
      rw [hkey]
      exact sub_nonneg.mpr hmin
    · have htpos : 0 ≤ tmax := by
        apply div_nonneg (le_of_lt (d.hw_pos idxM.1 idxM.2 hidxM_verts)); linarith
      have hmul : 0 ≤ tmax * betaPerturbation d c i e := mul_nonneg htpos hb
      nlinarith [d.hw_pos i e he, hmul]
  -- Step E: boundary
  have hboundary : d.w idxM.1 idxM.2 + tmax * betaPerturbation d c idxM.1 idxM.2 = 0 := by
    dsimp [tmax]
    have hβne : betaPerturbation d c idxM.1 idxM.2 ≠ 0 := by linarith
    field_simp [hβne]
    ring
  -- Step F: construct new FlatRepr d' and prove totalExcess < d.totalExcess
  set w' := (fun (i : t) (e : E) => d.w i e + tmax * betaPerturbation d c i e) with hw'_def
  set verts' := (fun (i : t) => (d.verts i).filter (fun e => 0 < w' i e)) with hverts'_def
  have hw'_nonneg : ∀ (i : t) e, e ∈ d.verts i → 0 ≤ w' i e := by
    intro i e he; dsimp [w']; exact feasible i e he
  have hverts'_sub : ∀ (i : t), verts' i ⊆ d.verts i := by
    intro i; dsimp [verts']; exact Finset.filter_subset _ _
  have hestar_not_mem_verts' : idxM.2 ∉ verts' idxM.1 := by
    dsimp [verts', w']; rw [Finset.mem_filter, hboundary]; simp
  have hsum_w'_over_verts : ∀ (i : t), ∑ e ∈ d.verts i, w' i e = 1 := by
    intro i; dsimp [w']
    rw [Finset.sum_add_distrib, d.hw_sum i, ← Finset.mul_sum, hβ_sum_zero i, mul_zero, add_zero]
  have hverts'_nonempty : ∀ (i : t), (verts' i).Nonempty := by
    intro i; by_contra h_empty
    have h_all_zero : ∀ e ∈ d.verts i, w' i e = 0 := by
      intro e he
      have h_notpos : ¬ 0 < w' i e := by
        intro hpos; apply h_empty; dsimp [verts']
        refine ⟨e, Finset.mem_filter.mpr ⟨he, hpos⟩⟩
      linarith [hw'_nonneg i e he, h_notpos]
    have hsum_zero : ∑ e ∈ d.verts i, w' i e = 0 :=
      Finset.sum_eq_zero (fun e he => h_all_zero e he)
    rw [hsum_w'_over_verts i] at hsum_zero; linarith
  have hsum_w'_filter : ∀ (i : t), ∑ e ∈ verts' i, w' i e = ∑ e ∈ d.verts i, w' i e := by
    intro i; rw [hverts'_def]; rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    have hn := hw'_nonneg i e he
    by_cases hpos : 0 < w' i e
    · simp [hpos]
    · have hz : w' i e = 0 := by linarith
      simp [hz]
  have hsum_w'_smul_filter : ∀ (i : t),
      ∑ e ∈ verts' i, w' i e • e = ∑ e ∈ d.verts i, w' i e • e := by
    intro i; rw [hverts'_def]; rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e he
    have hn := hw'_nonneg i e he
    by_cases hpos : 0 < w' i e
    · simp [hpos]
    · have hz : w' i e = 0 := by linarith
      simp [hz, zero_smul]
  have hw_pos' : ∀ (i : t) e, e ∈ verts' i → 0 < w' i e := by
    intro i e he; rw [hverts'_def] at he; exact (Finset.mem_filter.mp he).2
  have hw_sum' : ∀ (i : t), ∑ e ∈ verts' i, w' i e = 1 := by
    intro i; rw [hsum_w'_filter i, hsum_w'_over_verts i]
  have h_sum' : ∑ i : t, ∑ e ∈ verts' i, w' i e • e = x := by
    calc
      ∑ i : t, ∑ e ∈ verts' i, w' i e • e
          = ∑ i : t, ∑ e ∈ d.verts i, w' i e • e := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [hsum_w'_smul_filter i]
      _ = ∑ i : t, ∑ e ∈ d.verts i, (d.w i e + tmax * betaPerturbation d c i e) • e := rfl
      _ = ∑ i : t, ∑ e ∈ d.verts i, (d.w i e • e + (tmax * betaPerturbation d c i e) • e) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [add_smul]
      _ = ∑ i : t, ((∑ e ∈ d.verts i, d.w i e • e) +
                     (∑ e ∈ d.verts i, (tmax * betaPerturbation d c i e) • e)) := by
        refine Finset.sum_congr rfl (fun i _ => ?_); rw [Finset.sum_add_distrib]
      _ = (∑ i : t, ∑ e ∈ d.verts i, d.w i e • e) +
          (∑ i : t, ∑ e ∈ d.verts i, (tmax * betaPerturbation d c i e) • e) :=
          by rw [Finset.sum_add_distrib]
      _ = x + (∑ i : t, ∑ e ∈ d.verts i, (tmax * betaPerturbation d c i e) • e) := by rw [d.h_sum]
      _ = x + (∑ i : t, ∑ e ∈ d.verts i, tmax • (betaPerturbation d c i e • e)) := by
        refine congrArg (fun s => x + s) (Finset.sum_congr rfl (fun i _ => ?_))
        refine Finset.sum_congr rfl (fun e _ => ?_); rw [mul_smul]
      _ = x + (∑ i : t, tmax • (∑ e ∈ d.verts i, betaPerturbation d c i e • e)) := by
        refine congrArg (fun s => x + s) (Finset.sum_congr rfl (fun i _ => ?_))
        rw [← Finset.smul_sum]
      _ = x + tmax • (∑ i : t, ∑ e ∈ d.verts i, betaPerturbation d c i e • e) := by
        rw [← Finset.smul_sum]
      _ = x + tmax • (0 : E) := by rw [hβ_smul_zero]
      _ = x := by simp
  have h_verts_sub' : ∀ (i : t), ↑(verts' i) ⊆ S i.val := by
    intro i; exact Set.Subset.trans (Finset.coe_subset.mpr (hverts'_sub i)) (d.h_verts_sub i)
  let anchor' (i : t) : E :=
    if h : d.anchor i ∈ verts' i then d.anchor i
    else Classical.choose (hverts'_nonempty i)
  have hanchor'_mem : ∀ (i : t), anchor' i ∈ verts' i := by
    intro i; dsimp [anchor']
    by_cases h : d.anchor i ∈ verts' i
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact Classical.choose_spec (hverts'_nonempty i)
  have h_ssubset_istar : verts' idxM.1 ⊂ d.verts idxM.1 := by
    refine ⟨hverts'_sub idxM.1, ?_⟩
    intro h; apply hestar_not_mem_verts'; apply h; exact hidxM_verts
  have h_card_lt_istar : (verts' idxM.1).card < (d.verts idxM.1).card :=
    Finset.card_lt_card h_ssubset_istar
  let d' : FlatRepr S t x := {
    verts := verts'
    h_verts_sub := h_verts_sub'
    anchor := anchor'
    h_anchor := hanchor'_mem
    w := w'
    hw_pos := hw_pos'
    hw_sum := hw_sum'
    h_sum := h_sum'
  }
  have h_totalExcess_lt : d'.totalExcess < d.totalExcess := by
    dsimp [FlatRepr.totalExcess, d']
    refine Finset.sum_lt_sum (fun i _ => ?_) ⟨idxM.1, Finset.mem_univ _, ?_⟩
    · exact Nat.sub_le_sub_right (Finset.card_le_card (hverts'_sub i)) 1
    · have hcp : 0 < (verts' idxM.1).card := Finset.card_pos.mpr (hverts'_nonempty idxM.1)
      omega
  exact ⟨d', h_totalExcess_lt⟩

end Reduction

open Classical in
/-- **Shapley-Folkman Lemma**: For a finite family of nonempty subsets `Sᵢ ⊆ ℝᵈ`, any point
in the convex hull of the Minkowski sum `∑ Sᵢ` can be written as `∑ fᵢ` where each
`fᵢ ∈ convexHull ℝ (S i)`, and the number of indices with `fᵢ ∉ S i` is at most `d`.

The proof uses Carathéodory's theorem to build an initial flat representation, then
iteratively reduces the excess via linear dependence among the excess vectors, following
the standard proof (see e.g. Anderson, Khan and Rashid [anderson1982]). -/
theorem shapley_folkman [FiniteDimensional ℝ E] {ι : Type*}
    {S : ι → Set E} (t : Finset ι) (x : E)
    (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ (f : ι → E), (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧ (∑ i ∈ t, f i = x) ∧
      (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E := by
  classical
  obtain ⟨d, _⟩ := exists_flatRepr_of_mem hx
  let P (n : ℕ) : Prop := ∀ (d' : FlatRepr S t x), d'.totalExcess = n →
    ∃ d₀ : FlatRepr S t x, d₀.totalExcess ≤ Module.finrank ℝ E
  have h_step : ∀ n, (∀ m < n, P m) → P n := by
    intro n IH d' hn
    by_cases hle : n ≤ Module.finrank ℝ E
    · have : d'.totalExcess ≤ Module.finrank ℝ E := by rw [hn]; exact hle
      exact ⟨d', this⟩
    · have hgt : Module.finrank ℝ E < n := by omega
      have hgt' : Module.finrank ℝ E < d'.totalExcess := by simpa [hn] using hgt
      obtain ⟨d'', h_lt⟩ := flatRepr_reduce d' hgt'
      have hm : d''.totalExcess < n := h_lt.trans_eq hn
      exact IH (d''.totalExcess) hm d'' rfl
  have h_all : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n IH => exact h_step n IH
  obtain ⟨d₀, h_le⟩ := h_all d.totalExcess d rfl
  let f (i : ι) : E :=
    if hi : i ∈ t then
      ∑ e ∈ d₀.verts ⟨i, hi⟩, d₀.w ⟨i, hi⟩ e • e
    else 0
  have hf_conv : ∀ i ∈ t, f i ∈ convexHull ℝ (S i) := by
    intro i hi
    suffices (∑ e ∈ d₀.verts ⟨i, hi⟩, d₀.w ⟨i, hi⟩ e • e) ∈ convexHull ℝ (S i) by
      simpa [f, hi]
    have hsum1 : ∑ e ∈ d₀.verts ⟨i, hi⟩, d₀.w ⟨i, hi⟩ e = 1 := d₀.hw_sum ⟨i, hi⟩
    have hpos : 0 < ∑ e ∈ d₀.verts ⟨i, hi⟩, d₀.w ⟨i, hi⟩ e := by rw [hsum1]; norm_num
    have h_eq : (d₀.verts ⟨i, hi⟩).centerMass (d₀.w ⟨i, hi⟩) id
        = ∑ e ∈ d₀.verts ⟨i, hi⟩, d₀.w ⟨i, hi⟩ e • e := by
      simp [Finset.centerMass, hsum1]
    rw [← h_eq]
    exact Finset.centerMass_mem_convexHull (t := d₀.verts ⟨i, hi⟩) (w := d₀.w ⟨i, hi⟩)
      (fun e he => le_of_lt (d₀.hw_pos ⟨i, hi⟩ e he)) hpos
      (fun e he => d₀.h_verts_sub ⟨i, hi⟩ he)
  have hf_sum : ∑ i ∈ t, f i = x := by
    calc
      ∑ i ∈ t, f i = ∑ i : t, f i := (Finset.sum_attach (s := t) (f := f)).symm
      _ = ∑ i : t, (if hi : (i : ι) ∈ t then
          ∑ e ∈ d₀.verts ⟨(i : ι), hi⟩, d₀.w ⟨(i : ι), hi⟩ e • e else 0) := rfl
      _ = ∑ i : t, ∑ e ∈ d₀.verts ⟨(i : ι), i.property⟩,
          d₀.w ⟨(i : ι), i.property⟩ e • e := by
        refine Finset.sum_congr rfl (fun i _ => ?_); simp [i.property]
      _ = ∑ i : t, ∑ e ∈ d₀.verts i, d₀.w i e • e := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rcases i with ⟨i_val, hi_val⟩; rfl
      _ = x := d₀.h_sum
  have hf_count : (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E := by
    have h_single : ∀ (i : t), (d₀.verts i).card = 1 → f i.val ∈ S i.val := by
      intro i hcard
      obtain ⟨a, ha⟩ := ((Finset.card_eq_one (s := d₀.verts i)).mp hcard)
      have ha_eq : a = d₀.anchor i := by
        have hm : d₀.anchor i ∈ d₀.verts i := d₀.h_anchor i
        rw [ha] at hm; simp at hm; exact hm.symm
      have hf_i : f i.val = ∑ e ∈ d₀.verts i, d₀.w i e • e := by
        dsimp [f]; simp [i.property]
      rw [hf_i, ha, Finset.sum_singleton]
      have hw1 : d₀.w i a = 1 := by
        have hs := d₀.hw_sum i; rw [ha, Finset.sum_singleton] at hs; exact hs
      rw [hw1, one_smul, ha_eq]
      have hm : d₀.anchor i ∈ d₀.verts i := d₀.h_anchor i
      have hm' : d₀.anchor i ∈ (d₀.verts i : Set E) := Finset.mem_coe.mpr hm
      exact d₀.h_verts_sub i hm'
    have hcard_sum : (t.filter (fun i => f i ∉ S i)).card
        = (∑ i : t, (if f i.val ∉ S i.val then (1 : ℕ) else 0)) := by
      calc
        (t.filter (fun i => f i ∉ S i)).card
            = (∑ x ∈ t.filter (fun i => f i ∉ S i), (1 : ℕ)) := by simp
          _ = (∑ x ∈ t, (if f x ∉ S x then (1 : ℕ) else 0)) := by rw [Finset.sum_filter]
          _ = (∑ i : t, (if f i.val ∉ S i.val then (1 : ℕ) else 0)) :=
            (Finset.sum_attach (s := t) (f := fun i => if f i ∉ S i then (1 : ℕ) else 0)).symm
    rw [hcard_sum]
    have h_indicator : ∀ (i : t), (if f i.val ∉ S i.val then (1 : ℕ) else 0)
        ≤ ((d₀.verts i).card - 1) := by
      intro i
      by_cases hbad : f i.val ∉ S i.val
      · simp [hbad]
        have hcard_ge2 : 2 ≤ (d₀.verts i).card := by
          by_contra! hlt
          have hpos : 1 ≤ (d₀.verts i).card := by
            have hne : (d₀.verts i).Nonempty := ⟨d₀.anchor i, d₀.h_anchor i⟩
            have hpos' : 0 < (d₀.verts i).card := Finset.card_pos.mpr hne
            omega
          have h1 : (d₀.verts i).card = 1 := by omega
          exact hbad (h_single i h1)
        omega
      · simp [hbad]
    have hAB : (∑ i : t, (if f i.val ∉ S i.val then (1 : ℕ) else 0))
        ≤ (∑ i : t, ((d₀.verts i).card - 1)) :=
      Finset.sum_le_sum (fun i _ => h_indicator i)
    have h_total : (∑ i : t, ((d₀.verts i).card - 1)) = d₀.totalExcess := rfl
    rw [h_total] at hAB
    exact le_trans hAB h_le
  exact ⟨f, hf_conv, hf_sum, hf_count⟩

end ShapleyFolkman
