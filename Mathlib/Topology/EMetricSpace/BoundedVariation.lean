/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Tactic.Finiteness
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Tactic.Bound

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `eVariationOn f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `BoundedVariationOn f s` registers that the variation of `f` on `s` is finite.
* `LocallyBoundedVariationOn f s` registers that `f` has finite variation on any compact
  subinterval of `s`.
* `variationOnFromTo f s a b` is the signed variation of `f` on `s ∩ Icc a b`, converted to `ℝ`.

* `eVariationOn.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `LipschitzWith.locallyBoundedVariationOn` shows that a Lipschitz function has locally
  bounded variation.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/

@[expose] public section


open scoped NNReal ENNReal Topology UniformConvergence
open Set Filter OrderDual

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/-- The (extended-real-valued) variation of a function `f` on a set `s` inside a linear order is
the supremum of the sum of `edist (f (u (i+1))) (f (u i))` over all finite increasing
sequences `u` in `s`. -/
noncomputable def eVariationOn (f : α → E) (s : Set α) : ℝ≥0∞ :=
  ⨆ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
    ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))

/-- A function has bounded variation on a set `s` if its total variation there is finite. -/
def BoundedVariationOn (f : α → E) (s : Set α) :=
  eVariationOn f s ≠ ∞

/-- A function has locally bounded variation on a set `s` if, given any interval `[a, b]` with
endpoints in `s`, then the function has finite variation on `s ∩ [a, b]`. -/
def LocallyBoundedVariationOn (f : α → E) (s : Set α) :=
  ∀ a b, a ∈ s → b ∈ s → BoundedVariationOn f (s ∩ Icc a b)

/-! ### Basic computations of variation -/

namespace eVariationOn

theorem nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩

theorem eq_of_edist_zero_on {f f' : α → E} {s : Set α} (h : ∀ ⦃x⦄, x ∈ s → edist (f x) (f' x) = 0) :
    eVariationOn f s = eVariationOn f' s := by
  dsimp only [eVariationOn]
  congr 1 with p : 1
  congr 1 with i : 1
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1)), edist_congr_left (h <| p.snd.prop.2 i)]

theorem eq_of_eqOn {f f' : α → E} {s : Set α} (h : EqOn f f' s) :
    eVariationOn f s = eVariationOn f' s :=
  eq_of_edist_zero_on fun x xs => by rw [h xs, edist_self]

theorem sum_le {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α} (hu : Monotone u) (us : ∀ i, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s :=
  le_iSup_of_le ⟨n, u, hu, us⟩ le_rfl

theorem sum_le_of_monotoneOn_Icc {f : α → E} {s : Set α} {m n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Icc m n)) (us : ∀ i ∈ Icc m n, u i ∈ s) :
    (∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s := by
  rcases le_total n m with hnm | hmn
  · simp [Finset.Ico_eq_empty_of_le hnm]
  let π := projIcc m n hmn
  let v i := u (π i)
  calc
    ∑ i ∈ Finset.Ico m n, edist (f (u (i + 1))) (f (u i))
        = ∑ i ∈ Finset.Ico m n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Finset.mem_Ico] at hi
        simp only [v, π, projIcc_of_mem hmn ⟨hi.1, hi.2.le⟩,
          projIcc_of_mem hmn ⟨hi.1.trans i.le_succ, hi.2⟩]
    _ ≤ ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_mono_set _ (Nat.Iio_eq_range ▸ Finset.Ico_subset_Iio_self)
    _ ≤ eVariationOn f s :=
      sum_le (fun i j h ↦ hu (π i).2 (π j).2 (monotone_projIcc hmn h)) fun i ↦ us _ (π i).2

theorem sum_le_of_monotoneOn_Iic {f : α → E} {s : Set α} {n : ℕ} {u : ℕ → α}
    (hu : MonotoneOn u (Iic n)) (us : ∀ i ≤ n, u i ∈ s) :
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f s := by
  simpa using sum_le_of_monotoneOn_Icc (m := 0) (hu.mono Icc_subset_Iic_self) fun i hi ↦ us i hi.2

/-- The variation can be expressed using strictly monotone functions. This formulation is
often less convenient than the one with monotone functions as it involves dependent types, but
it is sometimes handy. -/
theorem eVariationOn_eq_strictMonoOn (f : α → E) (s : Set α) :
    eVariationOn f s =
      ⨆ p : (n : ℕ) × { u : ℕ → α // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s },
        ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : ∃ p : (n : ℕ) × { u : ℕ → α // StrictMonoOn u (Iic n) ∧ ∀ i ∈ Iic n, u i ∈ s },
        (p.2 : ℕ → α) p.1 = u n ∧
        ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)) =
        ∑ i ∈ Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i)) := by
      induction n with
      | zero => exact ⟨⟨0, ⟨u, by grind [StrictMonoOn], fun i hi ↦ u_mem _⟩⟩, by simp⟩
      | succ n ih =>
        rcases ih with ⟨⟨m, v, v_mono, v_mem⟩, hv, h'v⟩
        simp only [Finset.sum_range_succ, Sigma.exists, Subtype.exists, mem_Iic, exists_and_left,
          exists_prop]
        rcases (u_mono (Nat.le_add_right n 1)).eq_or_lt with hn | hn
        · simp only [← hn, edist_self, add_zero]
          exact ⟨m, v, hv, ⟨v_mono, v_mem⟩, h'v⟩
        · refine ⟨m + 1, fun i ↦ if i ≤ m then v i else u (n + 1), by simp,
            by grind [StrictMonoOn], ?_⟩
          simp only [h'v, ← hv, Order.add_one_le_iff, Finset.sum_range_succ, lt_self_iff_false,
            ↓reduceIte, le_refl]
          congr 1
          exact Finset.sum_congr rfl (by grind)
    rcases this with ⟨p, -, hp⟩
    rw [hp]
    apply le_iSup _ p
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    apply sum_le_of_monotoneOn_Iic (by grind [MonotoneOn, StrictMonoOn]) (by grind)

theorem mono (f : α → E) {s t : Set α} (hst : t ⊆ s) : eVariationOn f t ≤ eVariationOn f s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le hu fun i => hst (ut i)

theorem _root_.BoundedVariationOn.mono {f : α → E} {s : Set α} (h : BoundedVariationOn f s)
    {t : Set α} (ht : t ⊆ s) : BoundedVariationOn f t :=
  ne_top_of_le_ne_top h (eVariationOn.mono f ht)

theorem _root_.BoundedVariationOn.locallyBoundedVariationOn {f : α → E} {s : Set α}
    (h : BoundedVariationOn f s) : LocallyBoundedVariationOn f s := fun _ _ _ _ =>
  h.mono inter_subset_left

theorem congr {f g : α → E} {s : Set α} (h : EqOn f g s) : eVariationOn f s = eVariationOn g s := by
  grind [eVariationOn]

theorem edist_le (f : α → E) {s : Set α} {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    edist (f x) (f y) ≤ eVariationOn f s := by
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
  simpa only [Finset.sum_range_one] using sum_le (n := 1) hu us

theorem eq_zero_iff (f : α → E) {s : Set α} :
    eVariationOn f s = 0 ↔ ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) = 0 := by
  constructor
  · rintro h x xs y ys
    rw [← nonpos_iff_eq_zero, ← h]
    exact edist_le f xs ys
  · rintro h
    dsimp only [eVariationOn]
    rw [ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    exact Finset.sum_eq_zero fun i _ => h _ (us i.succ) _ (us i)

theorem constant_on {f : α → E} {s : Set α} (hf : (f '' s).Subsingleton) :
    eVariationOn f s = 0 := by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩, edist_self]

@[simp]
protected theorem subsingleton (f : α → E) {s : Set α} (hs : s.Subsingleton) :
    eVariationOn f s = 0 :=
  constant_on (hs.image f)

theorem lowerSemicontinuous_aux {ι : Type*} {F : ι → α → E} {p : Filter ι} {f : α → E} {s : Set α}
    (Ffs : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x))) {v : ℝ≥0∞} (hv : v < eVariationOn f s) :
    ∀ᶠ n : ι in p, v < eVariationOn (F n) s := by
  obtain ⟨⟨n, ⟨u, um, us⟩⟩, hlt⟩ :
    ∃ p : ℕ × { u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s },
      v < ∑ i ∈ Finset.range p.1, edist (f ((p.2 : ℕ → α) (i + 1))) (f ((p.2 : ℕ → α) i)) :=
    lt_iSup_iff.mp hv
  have : Tendsto (fun j => ∑ i ∈ Finset.range n, edist (F j (u (i + 1))) (F j (u i))) p
      (𝓝 (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
    apply tendsto_finset_sum
    exact fun i _ => Tendsto.edist (Ffs (u i.succ) (us i.succ)) (Ffs (u i) (us i))
  exact (this.eventually_const_lt hlt).mono fun i h => h.trans_le (sum_le um us)

/-- The map `(eVariationOn · s)` is lower semicontinuous for pointwise convergence *on `s`*.
Pointwise convergence on `s` is encoded here as uniform convergence on the family consisting of the
singletons of elements of `s`.
-/
protected theorem lowerSemicontinuous (s : Set α) :
    LowerSemicontinuous fun f : α →ᵤ[s.image singleton] E => eVariationOn f s := fun f ↦ by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E (s.image singleton)) id (𝓝 f) f s _
  simpa only [UniformOnFun.tendsto_iff_tendstoUniformlyOn, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, tendstoUniformlyOn_singleton_iff_tendsto] using @tendsto_id _ (𝓝 f)

/-- The map `(eVariationOn · s)` is lower semicontinuous for uniform convergence on `s`. -/
theorem lowerSemicontinuous_uniformOn (s : Set α) :
    LowerSemicontinuous fun f : α →ᵤ[{s}] E => eVariationOn f s := fun f ↦ by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E {s}) id (𝓝 f) f s _
  have := @tendsto_id _ (𝓝 f)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at this
  simp_rw [← tendstoUniformlyOn_singleton_iff_tendsto]
  exact fun x xs => (this s rfl).mono (singleton_subset_iff.mpr xs)

theorem _root_.BoundedVariationOn.dist_le {E : Type*} [PseudoMetricSpace E] {f : α → E}
    {s : Set α} (h : BoundedVariationOn f s) {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    dist (f x) (f y) ≤ (eVariationOn f s).toReal := by
  rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal h, ← edist_dist]
  exact edist_le f hx hy

theorem _root_.BoundedVariationOn.sub_le {f : α → ℝ} {s : Set α} (h : BoundedVariationOn f s)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : f x - f y ≤ (eVariationOn f s).toReal := by
  apply (le_abs_self _).trans
  rw [← Real.dist_eq]
  exact h.dist_le hx hy

/-- Consider a monotone function `u` parameterizing some points of a set `s`. Given `x ∈ s`, then
one can find another monotone function `v` parameterizing the same points as `u`, with `x` added.
In particular, the variation of a function along `u` is bounded by its variation along `v`. -/
theorem add_point (f : α → E) {s : Set α} {x : α} (hx : x ∈ s) (u : ℕ → α) (hu : Monotone u)
    (us : ∀ i, u i ∈ s) (n : ℕ) :
    ∃ (v : ℕ → α) (m : ℕ), Monotone v ∧ (∀ i, v i ∈ s) ∧ x ∈ v '' Iio m ∧
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
        ∑ j ∈ Finset.range m, edist (f (v (j + 1))) (f (v j)) := by
  rcases le_or_gt (u n) x with (h | h)
  · let v i := if i ≤ n then u i else x
    refine ⟨v, n + 2, by grind [Monotone], by grind, (mem_image _ _ _).2 ⟨n + 1, by grind⟩, ?_⟩
    calc
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by grind [Finset.sum_congr]
      _ ≤ ∑ j ∈ Finset.range (n + 2), edist (f (v (j + 1))) (f (v j)) := by
        gcongr
        apply Nat.le_add_right
  have exists_N : ∃ N, N ≤ n ∧ x < u N := ⟨n, le_rfl, h⟩
  let N := Nat.find exists_N
  have hN : N ≤ n ∧ x < u N := Nat.find_spec exists_N
  let w : ℕ → α := fun i => if i < N then u i else if i = N then x else u (i - 1)
  have hw : Monotone w := by
    apply monotone_nat_of_le_succ fun i => ?_
    rcases lt_trichotomy (i + 1) N with (hi | hi | hi)
    · grind [Monotone]
    · have A : i < N := hi ▸ i.lt_succ_self
      have := Nat.find_min exists_N A
      grind
    · grind [Monotone]
  refine ⟨w, n + 1, hw, by grind, (mem_image _ _ _).2 ⟨N, by grind⟩, ?_⟩
  rcases eq_or_lt_of_le (zero_le N) with (Npos | Npos)
  · calc
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i ∈ Finset.range n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by grind
      _ = ∑ i ∈ Finset.Ico 1 (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) 0 n 1
      _ ≤ ∑ j ∈ Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.range_eq_Ico]
        gcongr
        exact zero_le_one
  · calc
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ((∑ i ∈ Finset.Ico 0 (N - 1), edist (f (u (i + 1))) (f (u i))) +
              ∑ i ∈ Finset.Ico (N - 1) N, edist (f (u (i + 1))) (f (u i))) +
            ∑ i ∈ Finset.Ico N n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico] <;> grind
      _ = (∑ i ∈ Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (u N)) (f (u (N - 1))) +
            ∑ i ∈ Finset.Ico N n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by
        congr 1
        · congr 1
          · grind [Finset.sum_congr]
          · have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
            have : Finset.Ico (N - 1) N = {N - 1} := by rw [← Nat.Ico_succ_singleton, A]
            simp only [this, A, Finset.sum_singleton]
        · grind [Finset.sum_congr]
      _ = (∑ i ∈ Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (w (N + 1))) (f (w (N - 1))) +
            ∑ i ∈ Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        congr 1
        · grind
        · exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) N n 1
      _ ≤ ((∑ i ∈ Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              ∑ i ∈ Finset.Ico (N - 1) (N + 1), edist (f (w (i + 1))) (f (w i))) +
            ∑ i ∈ Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        refine add_le_add (add_le_add le_rfl ?_) le_rfl
        have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
        have B : N - 1 + 1 < N + 1 := A.symm ▸ N.lt_succ_self
        have C : N - 1 < N + 1 := lt_of_le_of_lt N.pred_le N.lt_succ_self
        rw [Finset.sum_eq_sum_Ico_succ_bot C, Finset.sum_eq_sum_Ico_succ_bot B, A, Finset.Ico_self,
          Finset.sum_empty, add_zero, add_comm (edist _ _)]
        exact edist_triangle _ _ _
      _ = ∑ j ∈ Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.sum_Ico_consecutive, Finset.sum_Ico_consecutive, Finset.range_eq_Ico] <;> grind

/-- The variation of a function on the union of two sets `s` and `t`, with `s` to the left of `t`,
bounds the sum of the variations along `s` and `t`. -/
theorem add_le_union (f : α → E) {s t : Set α} (h : ∀ x ∈ s, ∀ y ∈ t, x ≤ y) :
    eVariationOn f s + eVariationOn f t ≤ eVariationOn f (s ∪ t) := by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ ∀ i : ℕ, u i ∈ t } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 ht)
  refine ENNReal.iSup_add_iSup_le ?_
  /- We start from two sequences `u` and `v` along `s` and `t` respectively, and we build a new
    sequence `w` along `s ∪ t` by juxtaposing them. Its variation is larger than the sum of the
    variations. -/
  rintro ⟨n, ⟨u, hu, us⟩⟩ ⟨m, ⟨v, hv, vt⟩⟩
  let w i := if i ≤ n then u i else v (i - (n + 1))
  calc
    ((∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i ∈ Finset.range m, edist (f (v (i + 1))) (f (v i))) =
        (∑ i ∈ Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i ∈ Finset.range m, edist (f (w (n + 1 + i + 1))) (f (w (n + 1 + i))) := by
      dsimp only [w]
      congr 1
      · grind [Finset.sum_congr]
      · grind
    _ = (∑ i ∈ Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i ∈ Finset.Ico (n + 1) (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      congr 1
      rw [Finset.range_eq_Ico]
      convert Finset.sum_Ico_add (fun i : ℕ => edist (f (w (i + 1))) (f (w i))) 0 m (n + 1)
        using 3 <;> abel
    _ ≤ ∑ i ∈ Finset.range (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      rw [← Finset.sum_union]
      · gcongr; grind
      · exact Finset.disjoint_left.2 (by grind)
    _ ≤ eVariationOn f (s ∪ t) := sum_le (by grind [Monotone]) (by grind)

/-- If a set `s` is to the left of a set `t`, and both contain the boundary point `x`, then
the variation of `f` along `s ∪ t` is the sum of the variations. -/
theorem union (f : α → E) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x) :
    eVariationOn f (s ∪ t) = eVariationOn f s + eVariationOn f t := by
  classical
  apply le_antisymm _ (eVariationOn.add_le_union f fun a ha b hb => le_trans (hs.2 ha) (ht.2 hb))
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ust⟩⟩
  obtain ⟨v, m, hv, vst, xv, huv⟩ : ∃ (v : ℕ → α) (m : ℕ),
    Monotone v ∧ (∀ i, v i ∈ s ∪ t) ∧ x ∈ v '' Iio m ∧
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
        ∑ j ∈ Finset.range m, edist (f (v (j + 1))) (f (v j)) :=
    eVariationOn.add_point f (mem_union_left t hs.1) u hu ust n
  obtain ⟨N, hN, Nx⟩ : ∃ N, N < m ∧ v N = x := xv
  calc
    (∑ j ∈ Finset.range n, edist (f (u (j + 1))) (f (u j))) ≤
        ∑ j ∈ Finset.range m, edist (f (v (j + 1))) (f (v j)) :=
      huv
    _ = (∑ j ∈ Finset.Ico 0 N, edist (f (v (j + 1))) (f (v j))) +
          ∑ j ∈ Finset.Ico N m, edist (f (v (j + 1))) (f (v j)) := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (zero_le _) hN.le]
    _ ≤ eVariationOn f s + eVariationOn f t := by
      refine add_le_add ?_ ?_
      · apply sum_le_of_monotoneOn_Icc (hv.monotoneOn _) fun i hi => ?_
        rcases vst i with (h | h); · exact h
        have : v i = x := by
          apply le_antisymm
          · rw [← Nx]; exact hv hi.2
          · exact ht.2 h
        rw [this]
        exact hs.1
      · apply sum_le_of_monotoneOn_Icc (hv.monotoneOn _) fun i hi => ?_
        rcases vst i with (h | h); swap; · exact h
        have : v i = x := by
          apply le_antisymm
          · exact hs.2 h
          · rw [← Nx]; exact hv hi.1
        rw [this]
        exact ht.1

theorem Icc_add_Icc (f : α → E) {s : Set α} {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) (hb : b ∈ s) :
    eVariationOn f (s ∩ Icc a b) + eVariationOn f (s ∩ Icc b c) = eVariationOn f (s ∩ Icc a c) := by
  have A : IsGreatest (s ∩ Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, inter_subset_right.trans Icc_subset_Iic_self⟩
  have B : IsLeast (s ∩ Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, inter_subset_right.trans Icc_subset_Ici_self⟩
  rw [← eVariationOn.union f A B, ← inter_union_distrib_left, Icc_union_Icc_eq_Icc hab hbc]

theorem sum (f : α → E) {s : Set α} {E : ℕ → α} (hE : Monotone E) {n : ℕ}
    (hn : ∀ i, 0 < i → i < n → E i ∈ s) :
    ∑ i ∈ Finset.range n, eVariationOn f (s ∩ Icc (E i) (E (i + 1))) =
      eVariationOn f (s ∩ Icc (E 0) (E n)) := by
  induction n with
  | zero => simp [eVariationOn.subsingleton f Subsingleton.inter_singleton]
  | succ n ih =>
    by_cases hn₀ : n = 0
    · simp [hn₀]
    rw [← Icc_add_Icc (b := E n)]
    · rw [← ih (by intros; apply hn <;> omega), Finset.sum_range_succ]
    · apply hE; lia
    · apply hE; lia
    · apply hn <;> omega

theorem sum' (f : α → E) {I : ℕ → α} (hI : Monotone I) {n : ℕ} :
    ∑ i ∈ Finset.range n, eVariationOn f (Icc (I i) (I (i + 1)))
     = eVariationOn f (Icc (I 0) (I n)) := by
  convert sum f hI (s := Icc (I 0) (I n)) (n := n)
    (hn := by intros; rw [mem_Icc]; constructor <;> (apply hI; lia)) with i hi
  · simp only [right_eq_inter]
    gcongr <;> (apply hI; rw [Finset.mem_range] at hi; lia)
  · simp

/-! ### Composition of bounded variation functions with monotone functions -/

section Monotone

variable {β : Type*} [LinearOrder β]

theorem comp_le_of_monotoneOn (f : α → E) {s : Set α} {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t)
    (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t ≤ eVariationOn f s :=
  iSup_le fun ⟨n, u, hu, ut⟩ =>
    le_iSup_of_le ⟨n, φ ∘ u, fun x y xy => hφ (ut x) (ut y) (hu xy), fun i => φst (ut i)⟩ le_rfl

theorem comp_le_of_antitoneOn (f : α → E) {s : Set α} {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t)
    (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t ≤ eVariationOn f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
  refine (Finset.sum_congr rfl fun x hx => ?_).trans_le <| le_iSup_of_le
    ⟨n, fun i => φ (u <| n - i), fun x y xy => hφ (ut _) (ut _) (hu <| Nat.sub_le_sub_left xy n),
      fun i => φst (ut _)⟩
    le_rfl
  rw [Finset.mem_range] at hx
  dsimp only [Subtype.coe_mk, Function.comp_apply]
  rw [edist_comm]
  congr 4 <;> lia

theorem comp_eq_of_monotoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t) :
    eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_monotoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · convert zero_le (_ : ℝ≥0∞)
    exact eVariationOn.subsingleton f <|
      (subsingleton_of_subsingleton.image _).anti (surjOn_image φ t)
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts : MapsTo ψ (φ '' t) t := (surjOn_image φ t).mapsTo_invFunOn
  have hψ : MonotoneOn ψ (φ '' t) := Function.monotoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change eVariationOn (f ∘ id) (φ '' t) ≤ eVariationOn (f ∘ φ) t
  rw [← eq_of_eqOn (ψφs.comp_left : EqOn (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_monotoneOn _ ψ hψ ψts

theorem comp_inter_Icc_eq_of_monotoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : MonotoneOn φ t)
    {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    eVariationOn (f ∘ φ) (t ∩ Icc x y) = eVariationOn f (φ '' t ∩ Icc (φ x) (φ y)) := by
  rcases le_total x y with (h | h)
  · convert comp_eq_of_monotoneOn f φ (hφ.mono Set.inter_subset_left)
    apply le_antisymm
    · rintro _ ⟨⟨u, us, rfl⟩, vφx, vφy⟩
      rcases le_total x u with (xu | ux)
      · rcases le_total u y with (uy | yu)
        · exact ⟨u, ⟨us, ⟨xu, uy⟩⟩, rfl⟩
        · rw [le_antisymm vφy (hφ hy us yu)]
          exact ⟨y, ⟨hy, ⟨h, le_rfl⟩⟩, rfl⟩
      · rw [← le_antisymm vφx (hφ us hx ux)]
        exact ⟨x, ⟨hx, ⟨le_rfl, h⟩⟩, rfl⟩
    · rintro _ ⟨u, ⟨⟨hu, xu, uy⟩, rfl⟩⟩
      exact ⟨⟨u, hu, rfl⟩, ⟨hφ hx hu xu, hφ hu hy uy⟩⟩
  · rw [eVariationOn.subsingleton, eVariationOn.subsingleton]
    exacts [(Set.subsingleton_Icc_of_ge (hφ hy hx h)).anti Set.inter_subset_right,
      (Set.subsingleton_Icc_of_ge h).anti Set.inter_subset_right]

theorem comp_eq_of_antitoneOn (f : α → E) {t : Set β} (φ : β → α) (hφ : AntitoneOn φ t) :
    eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_antitoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · convert zero_le (_ : ℝ≥0∞)
    exact eVariationOn.subsingleton f <| (subsingleton_of_subsingleton.image _).anti
      (surjOn_image φ t)
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts := (surjOn_image φ t).mapsTo_invFunOn
  have hψ : AntitoneOn ψ (φ '' t) := Function.antitoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change eVariationOn (f ∘ id) (φ '' t) ≤ eVariationOn (f ∘ φ) t
  rw [← eq_of_eqOn (ψφs.comp_left : EqOn (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_antitoneOn _ ψ hψ ψts

open OrderDual

@[simp] theorem comp_ofDual (f : α → E) (s : Set α) :
    eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) = eVariationOn f s := by
  convert comp_eq_of_antitoneOn f ofDual fun _ _ _ _ => id
  simp only [Equiv.image_preimage]

lemma _root_.BoundedVariationOn.ofDual {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    BoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) := by
  simpa [BoundedVariationOn] using hf

@[simp] lemma boundedVariation_ofDual {f : α → E} {s : Set α} :
    BoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) ↔ BoundedVariationOn f s :=
  ⟨fun h ↦ h.ofDual, fun h ↦ h.ofDual⟩

end Monotone

/-! ### Left and right limits of bounded variation functions -/

/-- If a function is continuous on the left at a point `a`, then its variations on `Iio a` and
on `Iic a` coincide. We give a version relative to a set `s`. -/
lemma eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {a : α}
    (h : (𝓝[s ∩ Iio a] a).NeBot) (h' : ContinuousWithinAt f (s ∩ Iic a) a) :
    eVariationOn f (s ∩ Iio a) = eVariationOn f (s ∩ Iic a) := by
  apply le_antisymm (eVariationOn.mono _ (by grind))
  rw [eVariationOn_eq_strictMonoOn]
  apply iSup_le
  rintro ⟨n, u, u_mono, u_mem⟩
  have : u n ≤ a := (u_mem n (by simp)).2
  rcases this.eq_or_lt with hn | hn; swap
  · exact sum_le_of_monotoneOn_Iic u_mono.monotoneOn (by grind [StrictMonoOn])
  cases n with
  | zero => simp
  | succ n =>
    simp only [Finset.range_add_one, Finset.mem_range, lt_self_iff_false, not_false_eq_true,
      Finset.sum_insert, ge_iff_le]
    have : Tendsto (fun b ↦ edist (f b) (f (u n))
        + ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) (𝓝[s ∩ Iio a] a)
      (𝓝 (edist (f (u (n + 1))) (f (u n))
        + ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
      apply Tendsto.add_const
      apply Tendsto.edist _ tendsto_const_nhds
      rw [hn]
      apply h'.tendsto.mono_left
      exact nhdsWithin_mono _ (by grind)
    apply le_of_tendsto this
    have : s ∩ Ioo (u n) (u (n + 1)) ∈ 𝓝[s ∩ Iio a] a := by
      rw [hn]
      apply inter_mem_nhdsWithin_inter self_mem_nhdsWithin
      exact Ioo_mem_nhdsLT (by grind [StrictMonoOn])
    filter_upwards [this] with b hb
    let v i := if i ≤ n then u i else b
    calc edist (f b) (f (u n)) + ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))
    _ = ∑ i ∈ Finset.range (n + 1), edist (f (v (i + 1))) (f (v i)) := by
      simp only [Finset.range_add_one, Finset.mem_range, lt_self_iff_false, not_false_eq_true,
        Finset.sum_insert]
      congr 1 <;> grind [Finset.sum_congr]
    _ ≤ eVariationOn f (s ∩ Iio a) :=
      sum_le_of_monotoneOn_Iic (by grind [MonotoneOn, StrictMonoOn]) (by grind [StrictMonoOn])

/-- If a function is continuous on the right at a point `a`, then its variations on `Ioi a` and
on `Ici a` coincide. We give a version relative to a set `s`. -/
lemma eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α} {a : α}
    (h : (𝓝[s ∩ Ioi a] a).NeBot) (h' : ContinuousWithinAt f (s ∩ Ici a) a) :
    eVariationOn f (s ∩ Ioi a) = eVariationOn f (s ∩ Ici a) := by
  rw [← comp_ofDual f, ← comp_ofDual f]
  exact eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt h h'

lemma exists_lt_eVariationOn_inter_Icc {f : α → E} {ε : ℝ≥0∞} {s : Set α}
    (h : ε < eVariationOn f s) : ∃ a ∈ s, ∃ b ∈ s, a < b ∧ ε < eVariationOn f (s ∩ Icc a b) := by
  obtain ⟨n, u, ⟨u_mono, u_mem⟩, hu⟩ : ∃ n u, (Monotone u ∧ ∀ (i : ℕ), u i ∈ s) ∧
      ε < ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x)) := by
    simpa [eVariationOn, lt_iSup_iff] using h
  have A : ε < eVariationOn f (s ∩ Icc (u 0) (u n)) := by
    apply hu.trans_le
    simp only [Monotone] at u_mono
    let v (i : ℕ) := min (u i) (u n)
    calc ∑ x ∈ Finset.range n, edist (f (u (x + 1))) (f (u x))
    _ = ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by grind [Finset.sum_congr]
    _ ≤ eVariationOn f (s ∩ Icc (u 0) (u n)) :=
      sum_le_of_monotoneOn_Iic (by grind [MonotoneOn]) (by grind)
  refine ⟨u 0, u_mem _, u n, u_mem _, ?_, A⟩
  by_contra!
  have : Set.Subsingleton (s ∩ Icc (u 0) (u n)) := by
    intro a ha b hb
    simp only [mem_inter_iff, mem_Icc] at ha hb
    order
  simp [this] at A

/-- If a function has bounded variation, then the variation on closed semi-infinite intervals
tends to `0`. We give a version with a generic filter, that applies both to left-neighborhoods of
points and to `atTop`. -/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    (L : Filter α) (hL : ∀ y ∈ s, s ∩ Ici y ∈ L) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ici y)) L (𝓝 0) := by
  rcases eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simpa using tendsto_const_nhds
  /- The variation is monotone, therefore it converges. If the limit were positive, say `ε`,
  then one would get variation `ε` between two points `x₀` and `x₁`. But also between two points
  `x₁` and `x₂`, and so on. Adding up these variations would be arbitrarily large, contradicting
  the finite variation of the function. -/
  apply tendsto_order.2 ⟨by simp, fun ε εpos ↦ ?_⟩
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, δ ∈ Ioo 0 ε := exists_between εpos
  by_contra! H
  have B (y) (hy : y ∈ s) : ∃ y' ∈ s ∩ Ici y, δ ≤ eVariationOn f (s ∩ Icc y y') := by
    obtain ⟨y', hy', y'_mem⟩ : ∃ y', ε ≤ eVariationOn f (s ∩ Ici y') ∧ y' ∈ s ∩ Ici y :=
      (H.and_eventually (hL y hy)).exists
    obtain ⟨a, ha, b, hb, hab, h⟩ : ∃ a ∈ s ∩ Ici y', ∃ b ∈ s ∩ Ici y', a < b ∧
      δ < eVariationOn f ((s ∩ Ici y') ∩ Icc a b) :=
        exists_lt_eVariationOn_inter_Icc (hδ.trans_le hy')
    refine ⟨b, ⟨hb.1, le_trans y'_mem.2 hb.2⟩, ?_⟩
    have : Ici y' ∩ Icc a b = Icc a b := by grind
    rw [inter_assoc, this] at h
    exact h.le.trans (mono _ (by grind))
  choose! y y_mem le_y using B
  let v (n : ℕ) := y^[n] x₀
  have I n : v n ∈ s := by
    induction n with
    | zero => simpa [v] using hx₀
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, v]
      exact (y_mem _ ih).1
  have J (n : ℕ) : n * δ ≤ eVariationOn f s := calc
    n * δ
    _ = ∑ i ∈ Finset.range n, δ := by simp
    _ ≤ ∑ i ∈ Finset.range n, eVariationOn f (s ∩ Icc (v i) (v (i + 1))) := by
      gcongr with i hi
      simp only [Function.iterate_succ', Function.comp_apply, v]
      grind
    _ = eVariationOn f (s ∩ Icc (v 0) (v n)) := by
      apply eVariationOn.sum
      · apply monotone_nat_of_le_succ (fun n ↦ ?_)
        simp only [Function.iterate_succ', Function.comp_apply, v]
        exact (y_mem _ (I n)).2
      · grind
    _ ≤ eVariationOn f s := mono _ inter_subset_left
  have : Tendsto (fun (n : ℕ) ↦ n * δ) atTop (𝓝 (∞ * δ)) :=
    ENNReal.Tendsto.mul_const ENNReal.tendsto_nat_nhds_top (by simp)
  rw [ENNReal.top_mul δpos.ne'] at this
  have : ∞ ≤ eVariationOn f s := le_of_tendsto this (Eventually.of_forall J)
  simp only [BoundedVariationOn] at hf
  order

/-- A bounded variation function has a limit on its left within a set. Version with a general
filter, covering both left neighborhoods of points and `atTop`. -/
theorem _root_.BoundedVariationOn.exists_tendsto_left_of_filter [CompleteSpace E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s)
    (L : Filter α) (hL : ∀ y ∈ s, s ∩ Ici y ∈ L) (hs : s.Nonempty) :
    ∃ l, Tendsto f L (𝓝 l) := by
  rcases hs with ⟨x₀, hx₀⟩
  rcases Filter.eq_or_neBot L with h | h
  · simp only [h, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x₀⟩
  apply CompleteSpace.complete
  apply EMetric.cauchy_iff.2 ⟨by simp [neBot_iff.mp h], fun ε εpos ↦ ?_⟩
  obtain ⟨y, y_mem, hy⟩ : ∃ y ∈ s, eVariationOn f (s ∩ Ici y) < ε := by
    have W := hf.tendsto_eVariationOn_Ici_zero_of_filter L hL
    rcases (((tendsto_order.1 W).2 ε εpos).and (hL x₀ hx₀)).exists with ⟨y, hy, h'y⟩
    exact ⟨y, h'y.1, hy⟩
  refine ⟨f '' (s ∩ Ici y), ?_, ?_⟩
  · simp only [mem_map]
    apply mem_of_superset (hL y y_mem) (subset_preimage_image _ _)
  · rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
    exact (eVariationOn.edist_le _ ha hb).trans_lt hy

/-- If a function has bounded variation, then the variation on small closed-open
intervals to the left of any point tends to `0`. -/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero
    [TopologicalSpace α] [OrderTopology α]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ico y x)) (𝓝[s] x) (𝓝 0) := by
  have A : Tendsto (fun y ↦ eVariationOn f (s ∩ Ico y x)) (𝓝[s ∩ Iio x] x) (𝓝 0) := by
    simp_rw [← Iio_inter_Ici, ← inter_assoc]
    exact (hf.mono inter_subset_left).tendsto_eVariationOn_Ici_zero_of_filter (𝓝[s ∩ Iio x] x)
      (fun y hy ↦ inter_mem_nhdsWithin _ (Ici_mem_nhds hy.2))
  have B : Tendsto (fun y ↦ eVariationOn f (s ∩ Ico y x)) (𝓝[s ∩ Ici x] x) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha using by simp [show Ico a x = ∅ by grind]
  nth_rewrite 2 [show s = (s ∩ Iio x) ∪ (s ∩ Ici x) by grind]
  rw [nhdsWithin_union, tendsto_sup]
  simp [A, B]

/-- If a function has bounded variation, then the variation on small open-closed
intervals to the right of any point tends to `0`. -/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero [TopologicalSpace α]
    [OrderTopology α] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ioc x y)) (𝓝[s] x) (𝓝 0) := by
  have : (fun y ↦ eVariationOn f (s ∩ Ioc x y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Ico (toDual y) (toDual x))) := by
    ext y
    rw [Ico_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ico_zero (toDual x)

/-- If a function has bounded variation and is left-continuous at a point, then the variation on
small closed intervals to the left of this point tends to `0`. -/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) {x : α} (h : ContinuousWithinAt f (s ∩ Iic x) x) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc y x)) (𝓝[s] x) (𝓝 0) := by
  rcases eq_or_neBot (𝓝[s ∩ Iio x] x) with h' | h'
  · apply tendsto_const_nhds.congr'
    have : s = (s ∩ Iio x) ∪ (s ∩ Ici x) := by grind
    nth_rewrite 1 [this]
    simp only [nhdsWithin_union, h', bot_le, sup_of_le_right]
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply (eVariationOn.subsingleton _ (by grind [Set.Subsingleton])).symm
  apply (hf.tendsto_eVariationOn_Ico_zero x).congr (fun y ↦ ?_)
  rcases le_or_gt x y with hy | hy
  · rw [eVariationOn.subsingleton, eVariationOn.subsingleton] <;>
      grind [Set.Subsingleton]
  have W := eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt (f := f)
    (s := s ∩ Icc y x) (a := x) ?_ ?_
  · convert W using 2 <;> grind
  · rwa [show s ∩ Icc y x ∩ Iio x = (s ∩ Iio x) ∩ Ici y by grind, nhdsWithin_inter_of_mem']
    apply mem_nhdsWithin_of_mem_nhds
    exact Ici_mem_nhds hy
  · apply h.mono (by grind)

/-- If a function has bounded variation and is right-continuous at a point, then the variation on
small closed intervals to the right of this point tends to `0`. -/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right
    [TopologicalSpace α] [OrderTopology α] {f : α → E} {s : Set α}
    (hf : BoundedVariationOn f s) (x : α) (h : ContinuousWithinAt f (s ∩ Ici x) x) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Icc x y)) (𝓝[s] x) (𝓝 0) := by
  have : (fun y ↦ eVariationOn f (s ∩ Icc x y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_zero_left h

/-- A bounded variation function has a limit on its left within a set. -/
theorem _root_.BoundedVariationOn.exists_tendsto_left [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    ∃ l, Tendsto f (𝓝[s ∩ Iio x] x) (𝓝 l) := by
  rcases eq_empty_or_nonempty (s ∩ Iio x) with hs | hs
  · simp only [hs, nhdsWithin_empty, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x⟩
  exact BoundedVariationOn.exists_tendsto_left_of_filter (s := s ∩ Iio x)
    (hf.mono inter_subset_left) _ (fun y hy ↦ inter_mem_nhdsWithin _ (Ici_mem_nhds hy.2)) hs

/-- A bounded variation function has a limit on its right within a set. -/
theorem _root_.BoundedVariationOn.exists_tendsto_right [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    ∃ l, Tendsto f (𝓝[s ∩ Ioi x] x) (𝓝 l) :=
  hf.ofDual.exists_tendsto_left (toDual x)

/-- A bounded variation function tends to its left-limit on its left. -/
theorem _root_.BoundedVariationOn.tendsto_leftLim [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} (hf : BoundedVariationOn f univ) (x : α) :
    Tendsto f (𝓝[<] x) (𝓝 (f.leftLim x)) := by
  apply tendsto_leftLim_of_tendsto
  convert hf.exists_tendsto_left x
  simp

/-- A bounded variation function tends to its right-limit on its right. -/
theorem _root_.BoundedVariationOn.tendsto_rightLim [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α → E} (hf : BoundedVariationOn f univ) (x : α) :
    Tendsto f (𝓝[>] x) (𝓝 (f.rightLim x)) :=
  hf.ofDual.tendsto_leftLim x

/-- If a function `g` is at each point `x` a limit of `f` to the left or to the right (or more
generally a cluster point of the values of `f` around `x`) then the variation of `g` is bounded
by that of `f`. -/
private lemma eVariationOn_le_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] {f g : α → E}
    {s : Set α} (hg : ∀ x ∈ s, MapClusterPt (g x) (𝓝[s] x) f) :
    eVariationOn g s ≤ eVariationOn f s := by
  rw [eVariationOn_eq_strictMonoOn]
  apply iSup_le
  rintro ⟨n, u, u_mono, u_mem⟩
  simp only
  have : Nonempty α := ⟨u 0⟩
  apply le_of_forall_lt (fun c hc ↦ ?_)
  have : ∀ᶠ (b : ℕ → E) in 𝓝 (fun i ↦ g (u i)),
      c < ∑ i ∈ Finset.range n, edist (b (i + 1)) (b i) := by
    have : Continuous (fun (v : ℕ → E) ↦ ∑ i ∈ Finset.range n, edist (v (i + 1)) (v i)) := by
      fun_prop
    exact (tendsto_order.1 (this.continuousAt (x := fun i ↦ g (u i))).tendsto).1 c hc
  rw [nhds_pi] at this
  obtain ⟨I, I_fin, t, t_mem, ht⟩ : ∃ (I : Set ℕ), I.Finite ∧ ∃ t, (∀ (i : ℕ), t i ∈ 𝓝 (g (u i))) ∧
      I.pi t ⊆ {b : ℕ → E | c < ∑ i ∈ Finset.range n, edist (b (i + 1)) (b i)} := mem_pi.1 this
  have : ∀ᶠ b in 𝓝 u, ∀ i ∈ ((Finset.Iic n) ×ˢ (Finset.Iic n)).filter
      (fun i ↦ i.1 < i.2), b i.1 < b i.2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    apply IsOpen.mem_nhds ?_ (by grind [StrictMonoOn])
    exact isOpen_lt (by fun_prop) (by fun_prop)
  rw [nhds_pi] at this
  obtain ⟨J, J_fin, k, k_mem, hk⟩ : ∃ (J : Set ℕ), J.Finite ∧ ∃ k, (∀ (i : ℕ), k i ∈ 𝓝 (u i)) ∧
    J.pi k ⊆ _ := mem_pi.1 this
  have A i (hi : i ∈ Iic n) : ∃ x, (f x ∈ t i ∧ x ∈ k i) ∧ x ∈ s :=
    ((((mapClusterPt_iff_frequently.1 (hg (u i) (u_mem i hi)) (t i) (t_mem i))).and_eventually
      (mem_nhdsWithin_of_mem_nhds (k_mem i))).and_eventually self_mem_nhdsWithin).exists
  choose! v hv h'v using A
  have : c < ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) := by
    let f' i := if i ∈ Iic n then f (v i) else g (u i)
    have : ∑ i ∈ Finset.range n, edist (f (v (i + 1))) (f (v i)) =
        ∑ i ∈ Finset.range n, edist (f' (i + 1)) (f' i) :=
      Finset.sum_congr rfl (fun i hi ↦ by grind)
    rw [this]
    suffices H : f' ∈ I.pi t from ht H
    have A i : g (u i) ∈ t i := mem_of_mem_nhds (t_mem i)
    grind
  apply this.trans_le
  have v_mono : StrictMonoOn v (Iic n) := by
    let w i := if i ∈ Iic n then v i else u i
    suffices w ∈ J.pi k by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Iic, and_imp, Prod.forall] at hk
      grind [StrictMonoOn]
    have A i : u i ∈ k i := mem_of_mem_nhds (k_mem i)
    grind
  exact sum_le_of_monotoneOn_Iic v_mono.monotoneOn (by grind)

lemma eVariationOn_leftLim_le [TopologicalSpace α] [OrderTopology α] {f : α → E} :
    eVariationOn f.leftLim univ ≤ eVariationOn f univ := by
  apply eVariationOn_le_of_mapClusterPt (fun x hx ↦ ?_)
  apply (mapClusterPt_leftLim f x).mono (nhdsWithin_mono _ (subset_univ _))

lemma eVariationOn_rightLim_le [TopologicalSpace α] [OrderTopology α] {f : α → E} :
    eVariationOn f.rightLim univ ≤ eVariationOn f univ := by
  apply eVariationOn_le_of_mapClusterPt (fun x hx ↦ ?_)
  apply (mapClusterPt_rightLim f x).mono (nhdsWithin_mono _ (subset_univ _))

lemma _root_.BoundedVariationOn.leftLim [TopologicalSpace α] [OrderTopology α] {f : α → E}
    (hf : BoundedVariationOn f univ) : BoundedVariationOn f.leftLim univ :=
  (eVariationOn_leftLim_le.trans_lt hf.lt_top).ne

lemma _root_.BoundedVariationOn.rightLim [TopologicalSpace α] [OrderTopology α] {f : α → E}
    (hf : BoundedVariationOn f univ) : BoundedVariationOn f.rightLim univ :=
  (eVariationOn_rightLim_le.trans_lt hf.lt_top).ne

lemma _root_.BoundedVariationOn.continuousWithinAt_leftLim [TopologicalSpace α] [OrderTopology α]
    [CompleteSpace E] [T3Space E] {f : α → E} (hf : BoundedVariationOn f univ) {x : α} :
    ContinuousWithinAt f.leftLim (Iic x) x := by
  have : Tendsto f.leftLim (𝓝[<] x) (𝓝 (f.leftLim.leftLim x)) := hf.leftLim.tendsto_leftLim x
  rw [leftLim_leftLim (hf.tendsto_leftLim x)] at this
  exact continuousWithinAt_Iio_iff_Iic.1 this

lemma _root_.BoundedVariationOn.continuousWithinAt_rightLim [TopologicalSpace α] [OrderTopology α]
    [CompleteSpace E] [T3Space E] {f : α → E} (hf : BoundedVariationOn f univ) {x : α} :
    ContinuousWithinAt f.rightLim (Ici x) x :=
  BoundedVariationOn.continuousWithinAt_leftLim hf.ofDual

/-! ### Limits of bounded variation functions as `± ∞` -/

/-- If a function has bounded variation, then the variation on closed semi-infinite
intervals tends to `0` at `+∞`. -/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Ici y)) (𝓟 s ⊓ atTop) (𝓝 0) :=
  hf.tendsto_eVariationOn_Ici_zero_of_filter _
    (fun y _ ↦ inter_mem_inf (mem_principal_self s) (Ici_mem_atTop y))

/-- If a function has bounded variation, then the variation on semi-infinite closed
intervals tends to `0` at `-∞`. -/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    Tendsto (fun y ↦ eVariationOn f (s ∩ Iic y)) (𝓟 s ⊓ atBot) (𝓝 0) := by
  have : (fun y ↦ eVariationOn f (s ∩ Iic y)) =
      (fun y ↦ eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s ∩ Ici (toDual y))) := by
    ext y
    rw [Ici_toDual, ← preimage_inter, comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ici_zero

/-- A bounded variation function has a limit at `+∞`. -/
theorem _root_.BoundedVariationOn.exists_tendsto_atTop [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    ∃ l, Tendsto f (𝓟 s ⊓ atTop) (𝓝 l) := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · simp
  · exact hf.exists_tendsto_left_of_filter _
      (fun y hy ↦ inter_mem_inf (mem_principal_self s) (Ici_mem_atTop _)) hs

/-- A bounded variation function has a limit at `-∞`. -/
theorem _root_.BoundedVariationOn.exists_tendsto_atBot [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} {s : Set α} (hf : BoundedVariationOn f s) :
    ∃ l, Tendsto f (𝓟 s ⊓ atBot) (𝓝 l) :=
  hf.ofDual.exists_tendsto_atTop

theorem _root_.BoundedVariationOn.tendsto_atTop_limUnder [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} (hf : BoundedVariationOn f univ) :
    Tendsto f atTop (𝓝 (limUnder atTop f)) :=
  tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atTop)

theorem _root_.BoundedVariationOn.tendsto_atBot_limUnder [CompleteSpace E] [hE : Nonempty E]
    {f : α → E} (hf : BoundedVariationOn f univ) :
    Tendsto f atBot (𝓝 (limUnder atBot f)) :=
  tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atBot)

end eVariationOn

/-! ### Variation of monotone functions -/

theorem MonotoneOn.eVariationOn_le {f : α → ℝ} {s : Set α} (hf : MonotoneOn f s) {a b : α}
    (as : a ∈ s) (bs : b ∈ s) : eVariationOn f (s ∩ Icc a b) ≤ ENNReal.ofReal (f b - f a) := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) =
        ∑ i ∈ Finset.range n, ENNReal.ofReal (f (u (i + 1)) - f (u i)) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [edist_dist, Real.dist_eq, abs_of_nonneg]
      exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (f (u (i + 1)) - f (u i))) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
    _ = ENNReal.ofReal (f (u n) - f (u 0)) := by rw [Finset.sum_range_sub fun i => f (u i)]
    _ ≤ ENNReal.ofReal (f b - f a) := by
      apply ENNReal.ofReal_le_ofReal
      exact sub_le_sub (hf (us n).1 bs (us n).2.2) (hf as (us 0).1 (us 0).2.1)

theorem MonotoneOn.locallyBoundedVariationOn {f : α → ℝ} {s : Set α} (hf : MonotoneOn f s) :
    LocallyBoundedVariationOn f s := fun _ _ as bs =>
  ((hf.eVariationOn_le as bs).trans_lt ENNReal.ofReal_lt_top).ne

/-- The **signed** variation of `f` on the interval `Icc a b` intersected with the set `s`,
squashed to a real (therefore only really meaningful if the variation is finite)
-/
noncomputable def variationOnFromTo (f : α → E) (s : Set α) (a b : α) : ℝ :=
  if a ≤ b then (eVariationOn f (s ∩ Icc a b)).toReal else -(eVariationOn f (s ∩ Icc b a)).toReal

namespace variationOnFromTo

variable (f : α → E) (s : Set α)

protected theorem self (a : α) : variationOnFromTo f s a a = 0 := by
  dsimp only [variationOnFromTo]
  rw [if_pos le_rfl, Icc_self, eVariationOn.subsingleton, ENNReal.toReal_zero]
  exact fun x hx y hy => hx.2.trans hy.2.symm

protected theorem nonneg_of_le {a b : α} (h : a ≤ b) : 0 ≤ variationOnFromTo f s a b := by
  simp only [variationOnFromTo, if_pos h, ENNReal.toReal_nonneg]

protected theorem eq_neg_swap (a b : α) :
    variationOnFromTo f s a b = -variationOnFromTo f s b a := by
  rcases lt_trichotomy a b with (ab | rfl | ba)
  · simp only [variationOnFromTo, if_pos ab.le, if_neg ab.not_ge, neg_neg]
  · simp only [variationOnFromTo.self, neg_zero]
  · simp only [variationOnFromTo, if_pos ba.le, if_neg ba.not_ge]

protected theorem nonpos_of_ge {a b : α} (h : b ≤ a) : variationOnFromTo f s a b ≤ 0 := by
  rw [variationOnFromTo.eq_neg_swap]
  exact neg_nonpos_of_nonneg (variationOnFromTo.nonneg_of_le f s h)

variable {f s} in
theorem abs_le_eVariationOn (hf : BoundedVariationOn f s) {a b : α} :
    |variationOnFromTo f s a b| ≤ (eVariationOn f s).toReal := by
  by_cases hab : a ≤ b
  · simp only [variationOnFromTo, hab, ↓reduceIte, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)
  · simp only [variationOnFromTo, hab, ↓reduceIte, abs_neg, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)

protected theorem eq_of_le {a b : α} (h : a ≤ b) :
    variationOnFromTo f s a b = (eVariationOn f (s ∩ Icc a b)).toReal :=
  if_pos h

protected theorem eq_of_ge {a b : α} (h : b ≤ a) :
    variationOnFromTo f s a b = -(eVariationOn f (s ∩ Icc b a)).toReal := by
  rw [variationOnFromTo.eq_neg_swap, neg_inj, variationOnFromTo.eq_of_le f s h]

protected theorem add {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b + variationOnFromTo f s b c = variationOnFromTo f s a c := by
  symm
  refine additive_of_total (· ≤ · : α → α → Prop) (variationOnFromTo f s) (· ∈ s) ?_ ?_ ha hb hc
  · rintro x y _xs _ys
    simp only [variationOnFromTo.eq_neg_swap f s y x, add_neg_cancel]
  · rintro x y z xy yz xs ys zs
    rw [variationOnFromTo.eq_of_le f s xy, variationOnFromTo.eq_of_le f s yz,
      variationOnFromTo.eq_of_le f s (xy.trans yz),
      ← ENNReal.toReal_add (hf x y xs ys) (hf y z ys zs), eVariationOn.Icc_add_Icc f xy yz ys]

variable {f s} in
protected theorem edist_zero_of_eq_zero (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (h : variationOnFromTo f s a b = 0) :
    edist (f a) (f b) = 0 := by
  wlog h' : a ≤ b
  · rw [edist_comm]
    apply this hf hb ha _ (le_of_not_ge h')
    rw [variationOnFromTo.eq_neg_swap, h, neg_zero]
  · apply le_antisymm _ (zero_le _)
    rw [← ENNReal.ofReal_zero, ← h, variationOnFromTo.eq_of_le f s h',
      ENNReal.ofReal_toReal (hf a b ha hb)]
    apply eVariationOn.edist_le
    exacts [⟨ha, ⟨le_rfl, h'⟩⟩, ⟨hb, ⟨h', le_rfl⟩⟩]

protected theorem eq_left_iff {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b c : α} (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) :
    variationOnFromTo f s a b = variationOnFromTo f s a c ↔ variationOnFromTo f s b c = 0 := by
  simp only [← variationOnFromTo.add hf ha hb hc, left_eq_add]

protected theorem eq_zero_iff_of_le {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (ab : a ≤ b) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ Icc a b) ⦃y⦄ (_hy : y ∈ s ∩ Icc a b), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_le _ _ ab, ENNReal.toReal_eq_zero_iff, or_iff_left (hf a b ha hb),
    eVariationOn.eq_zero_iff]

protected theorem eq_zero_iff_of_ge {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (ba : b ≤ a) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ Icc b a) ⦃y⦄ (_hy : y ∈ s ∩ Icc b a), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_ge _ _ ba, neg_eq_zero, ENNReal.toReal_eq_zero_iff,
    or_iff_left (hf b a hb ha), eVariationOn.eq_zero_iff]

protected theorem eq_zero_iff {f : α → E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b : α}
    (ha : a ∈ s) (hb : b ∈ s) :
    variationOnFromTo f s a b = 0 ↔
      ∀ ⦃x⦄ (_hx : x ∈ s ∩ uIcc a b) ⦃y⦄ (_hy : y ∈ s ∩ uIcc a b), edist (f x) (f y) = 0 := by
  rcases le_total a b with (ab | ba)
  · rw [uIcc_of_le ab]
    exact variationOnFromTo.eq_zero_iff_of_le hf ha hb ab
  · rw [uIcc_of_ge ba]
    exact variationOnFromTo.eq_zero_iff_of_ge hf ha hb ba

variable {f} {s}

protected theorem monotoneOn (hf : LocallyBoundedVariationOn f s) {a : α} (as : a ∈ s) :
    MonotoneOn (variationOnFromTo f s a) s := by
  rintro b bs c cs bc
  rw [← variationOnFromTo.add hf as bs cs]
  exact le_add_of_nonneg_right (variationOnFromTo.nonneg_of_le f s bc)

protected theorem antitoneOn (hf : LocallyBoundedVariationOn f s) {b : α} (bs : b ∈ s) :
    AntitoneOn (fun a => variationOnFromTo f s a b) s := by
  rintro a as c cs ac
  dsimp only
  rw [← variationOnFromTo.add hf as cs bs]
  exact le_add_of_nonneg_left (variationOnFromTo.nonneg_of_le f s ac)

protected theorem sub_self_monotoneOn {f : α → ℝ} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a : α} (as : a ∈ s) : MonotoneOn (variationOnFromTo f s a - f) s := by
  rintro b bs c cs bc
  rw [Pi.sub_apply, Pi.sub_apply, le_sub_iff_add_le, add_comm_sub, ← le_sub_iff_add_le']
  calc
    f c - f b ≤ |f c - f b| := le_abs_self _
    _ = dist (f b) (f c) := by rw [dist_comm, Real.dist_eq]
    _ ≤ variationOnFromTo f s b c := by
      rw [variationOnFromTo.eq_of_le f s bc, dist_edist]
      apply ENNReal.toReal_mono (hf b c bs cs)
      apply eVariationOn.edist_le f
      exacts [⟨bs, le_rfl, bc⟩, ⟨cs, bc, le_rfl⟩]
    _ = variationOnFromTo f s a c - variationOnFromTo f s a b := by
      rw [← variationOnFromTo.add hf as bs cs, add_sub_cancel_left]

protected theorem comp_eq_of_monotoneOn {β : Type*} [LinearOrder β] (f : α → E) {t : Set β}
    (φ : β → α) (hφ : MonotoneOn φ t) {x y : β} (hx : x ∈ t) (hy : y ∈ t) :
    variationOnFromTo (f ∘ φ) t x y = variationOnFromTo f (φ '' t) (φ x) (φ y) := by
  rcases le_total x y with (h | h)
  · rw [variationOnFromTo.eq_of_le _ _ h, variationOnFromTo.eq_of_le _ _ (hφ hx hy h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hx hy]
  · rw [variationOnFromTo.eq_of_ge _ _ h, variationOnFromTo.eq_of_ge _ _ (hφ hy hx h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hy hx]

theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici
    [TopologicalSpace α] [OrderTopology α] (hf : BoundedVariationOn f univ) {a x : α}
    (hx : ContinuousWithinAt f (Ici x) x) :
    ContinuousWithinAt (variationOnFromTo f univ a) (Ici x) x := by
  have : variationOnFromTo f univ a =
      fun y ↦ variationOnFromTo f univ a x + variationOnFromTo f univ x y := by
    ext y
    rw [variationOnFromTo.add hf.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _)]
  rw [this]
  apply continuousWithinAt_const.add
  suffices H : ContinuousWithinAt (fun y ↦ (eVariationOn f (univ ∩ Icc x y)).toReal) (Ici x) x from
    H.congr_of_mem (fun y hy ↦ by grind [variationOnFromTo]) self_mem_Iic
  simp only [ContinuousWithinAt, Icc_self]
  rw [eVariationOn.subsingleton _ (by grind [Set.Subsingleton])]
  apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
  apply Tendsto.mono_left _ (nhdsWithin_mono _ (subset_univ _))
  exact hf.tendsto_eVariationOn_Icc_zero_right _ (by simpa using hx)

theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici
    [TopologicalSpace α] [OrderTopology α] [T3Space E] [CompleteSpace E]
    (hf : BoundedVariationOn f univ) {a x : α} :
    ContinuousWithinAt (variationOnFromTo f.rightLim univ a) (Ici x) x :=
  hf.rightLim.continuousWithinAt_variationOnFromTo_Ici hf.continuousWithinAt_rightLim

end variationOnFromTo

/-- If a real-valued function has bounded variation on a set, then it is a difference of monotone
functions there. -/
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn {f : α → ℝ} {s : Set α}
    (h : LocallyBoundedVariationOn f s) :
    ∃ p q : α → ℝ, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨c, cs⟩)
  · exact ⟨f, 0, subsingleton_empty.monotoneOn _, subsingleton_empty.monotoneOn _,
      (sub_zero f).symm⟩
  · exact ⟨_, _, variationOnFromTo.monotoneOn h cs, variationOnFromTo.sub_self_monotoneOn h cs,
      (sub_sub_cancel _ _).symm⟩

/-! ### Lipschitz functions and bounded variation -/

section LipschitzOnWith

variable {F : Type*} [PseudoEMetricSpace F]

theorem LipschitzOnWith.comp_eVariationOn_le {f : E → F} {C : ℝ≥0} {t : Set E}
    (h : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t) :
    eVariationOn (f ∘ g) s ≤ C * eVariationOn g s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i)))) ≤
        ∑ i ∈ Finset.range n, C * edist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i _ => h (hg (us _)) (hg (us _))
    _ = C * ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := by rw [Finset.mul_sum]
    _ ≤ C * eVariationOn g s := by grw [eVariationOn.sum_le hu us]

theorem LipschitzOnWith.comp_boundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : BoundedVariationOn g s) : BoundedVariationOn (f ∘ g) s :=
  ne_top_of_le_ne_top (by finiteness) (hf.comp_eVariationOn_le hg)

theorem LipschitzOnWith.comp_locallyBoundedVariationOn {f : E → F} {C : ℝ≥0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α → E} {s : Set α} (hg : MapsTo g s t)
    (h : LocallyBoundedVariationOn g s) : LocallyBoundedVariationOn (f ∘ g) s :=
  fun x y xs ys =>
  hf.comp_boundedVariationOn (hg.mono_left inter_subset_left) (h x y xs ys)

theorem LipschitzWith.comp_boundedVariationOn {f : E → F} {C : ℝ≥0} (hf : LipschitzWith C f)
    {g : α → E} {s : Set α} (h : BoundedVariationOn g s) : BoundedVariationOn (f ∘ g) s :=
  hf.lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) h

theorem LipschitzWith.comp_locallyBoundedVariationOn {f : E → F} {C : ℝ≥0}
    (hf : LipschitzWith C f) {g : α → E} {s : Set α} (h : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f ∘ g) s :=
  hf.lipschitzOnWith.comp_locallyBoundedVariationOn (mapsTo_univ _ _) h

theorem LipschitzOnWith.locallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} {s : Set ℝ}
    (hf : LipschitzOnWith C f s) : LocallyBoundedVariationOn f s :=
  hf.comp_locallyBoundedVariationOn (mapsTo_id _)
    (@monotoneOn_id ℝ _ s).locallyBoundedVariationOn

theorem LipschitzWith.locallyBoundedVariationOn {f : ℝ → E} {C : ℝ≥0} (hf : LipschitzWith C f)
    (s : Set ℝ) : LocallyBoundedVariationOn f s :=
  hf.lipschitzOnWith.locallyBoundedVariationOn

end LipschitzOnWith
