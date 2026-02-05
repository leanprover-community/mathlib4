/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.UniformSpace.Closeds

/-!
# Closed subsets

This file defines the metric and emetric space structure on the types of closed subsets and nonempty
compact subsets of a metric or emetric space.

The Hausdorff distance induces an emetric space structure on the type of closed subsets
of an emetric space, called `Closeds`. Its completeness, resp. compactness, resp.
second-countability, follow from the corresponding properties of the original space.

In a metric space, the type of nonempty compact subsets (called `NonemptyCompacts`) also
inherits a metric space structure from the Hausdorff distance, as the Hausdorff edistance is
always finite in this context.
-/

@[expose] public section

noncomputable section

open Set Function TopologicalSpace Filter Topology ENNReal

namespace Metric

variable {α : Type*} [PseudoEMetricSpace α]

theorem mem_hausdorffEntourage_of_hausdorffEDist_lt {s t : Set α} {δ : ℝ≥0∞}
    (h : hausdorffEDist s t < δ) : (s, t) ∈ hausdorffEntourage {p | edist p.1 p.2 < δ} := by
  rw [hausdorffEDist, max_lt_iff] at h
  rw [hausdorffEntourage, Set.mem_setOf]
  conv => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : ⨆ x ∈ s, infEDist x t < δ) :
      s ⊆ SetRel.preimage {p | edist p.1 p.2 < δ} t := by
    intro x hx
    simpa only [infEDist, iInf_lt_iff, exists_prop] using (le_iSup₂ x hx).trans_lt h
  exact ⟨this h.1, this h.2⟩

theorem hausdorffEDist_le_of_mem_hausdorffEntourage {s t : Set α} {δ : ℝ≥0∞}
    (h : (s, t) ∈ hausdorffEntourage {p | edist p.1 p.2 ≤ δ}) : hausdorffEDist s t ≤ δ := by
  rw [hausdorffEDist, max_le_iff]
  rw [hausdorffEntourage, Set.mem_setOf] at h
  conv at h => enter [2, 2, 1, 1, _]; rw [edist_comm]
  have {s t : Set α} (h : s ⊆ SetRel.preimage {p | edist p.1 p.2 ≤ δ} t) :
      ⨆ x ∈ s, infEDist x t ≤ δ := by
    rw [iSup₂_le_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := h hx
    exact iInf₂_le_of_le y hy hxy
  exact ⟨this h.1, this h.2⟩

/-- The Hausdorff pseudo emetric on the powerset of a pseudo emetric space.
See note [reducible non-instances]. -/
protected abbrev _root_.PseudoEMetricSpace.hausdorff : PseudoEMetricSpace (Set α) where
  edist s t := hausdorffEDist s t
  edist_self _ := hausdorffEDist_self
  edist_comm _ _ := hausdorffEDist_comm
  edist_triangle _ _ _ := hausdorffEDist_triangle
  toUniformSpace := .hausdorff α
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
        Filter.mem_iInf_of_mem ε <| Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEDist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
      with _ h using hδε.trans_le' <| hausdorffEDist_le_of_mem_hausdorffEntourage h

end Metric

namespace TopologicalSpace

open Metric

variable {α β : Type*} [EMetricSpace α] [EMetricSpace β] {s : Set α}

namespace Closeds

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
instance instEMetricSpace : EMetricSpace (Closeds α) where
  __ := PseudoEMetricSpace.hausdorff.induced SetLike.coe
  eq_of_edist_eq_zero {s t} h := Closeds.ext <| (s.isClosed.hausdorffEDist_zero_iff t.isClosed).1 h

/-- The edistance to a closed set depends continuously on the point and the set -/
theorem continuous_infEDist :
    Continuous fun p : α × Closeds α => infEDist p.1 p.2 := by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEDist x s ≤ infEDist x t + hausdorffEDist (t : Set α) s :=
      infEDist_le_infEDist_add_hausdorffEDist
    _ ≤ infEDist y t + edist x y + hausdorffEDist (t : Set α) s := by
      gcongr; apply infEDist_le_infEDist_add_edist
    _ = infEDist y t + (edist x y + hausdorffEDist (s : Set α) t) := by
      rw [add_assoc, hausdorffEDist_comm]
    _ ≤ infEDist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = infEDist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]

/-- By definition, the edistance on `Closeds α` is given by the Hausdorff edistance -/
theorem edist_eq {s t : Closeds α} : edist s t = hausdorffEDist (s : Set α) t :=
  rfl

/-- In a complete space, the type of closed subsets is complete for the Hausdorff edistance. -/
instance instCompleteSpace [CompleteSpace α] : CompleteSpace (Closeds α) := by
  /- We will show that, if a sequence of sets `s n` satisfies
    `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
    completeness, by a standard completeness criterion.
    We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : ℕ → ℝ≥0∞ := fun n => 2⁻¹ ^ n
  have B_pos : ∀ n, (0 : ℝ≥0∞) < B n := by simp [B, ENNReal.pow_pos]
  have B_ne_top : ∀ n, B n ≠ ⊤ := by finiteness
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
    We will show that it converges. The limit set is `t0 = ⋂n, closure (⋃m≥n, s m)`.
    We will have to show that a point in `s n` is close to a point in `t0`, and a point
    in `t0` is close to a point in `s n`. The completeness then follows from a
    standard criterion. -/
  refine EMetric.complete_of_convergent_controlled_sequences B B_pos fun s hs => ?_
  let t0 := ⋂ n, closure (⋃ m ≥ n, s m : Set α)
  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
  use t
  -- The inequality is written this way to agree with `edist_le_of_edist_le_geometric_of_tendsto₀`
  have I1 : ∀ n, ∀ x ∈ s n, ∃ y ∈ t0, edist x y ≤ 2 * B n := by
    /- This is the main difficulty of the proof. Starting from `x ∈ s n`, we want
           to find a point in `t0` which is close to `x`. Define inductively a sequence of
           points `z m` with `z n = x` and `z m ∈ s m` and `edist (z m) (z (m+1)) ≤ B m`. This is
           possible since the Hausdorff distance between `s m` and `s (m+1)` is at most `B m`.
           This sequence is a Cauchy sequence, therefore converging as the space is complete, to
           a limit which satisfies the required properties. -/
    intro n x hx
    obtain ⟨z, hz₀, hz⟩ :
      ∃ z : ∀ l, s (n + l), (z 0 : α) = x ∧ ∀ k, edist (z k : α) (z (k + 1) : α) ≤ B n / 2 ^ k := by
      -- We prove existence of the sequence by induction.
      have : ∀ (l) (z : s (n + l)), ∃ z' : s (n + l + 1), edist (z : α) z' ≤ B n / 2 ^ l := by
        intro l z
        obtain ⟨z', z'_mem, hz'⟩ : ∃ z' ∈ s (n + l + 1), edist (z : α) z' < B n / 2 ^ l := by
          refine exists_edist_lt_of_hausdorffEDist_lt (s := s (n + l)) z.2 ?_
          simp only [ENNReal.inv_pow, div_eq_mul_inv]
          rw [← pow_add]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => (this l z).choose
      simp only [Nat.add_zero, Nat.rec_zero, true_and]
      exact fun k => (this k _).choose_spec
    -- it follows from the previous bound that `z` is a Cauchy sequence
    have : CauchySeq fun k => (z k : α) := cauchySeq_of_edist_le_geometric_two (B n) (B_ne_top n) hz
    -- therefore, it converges
    rcases cauchySeq_tendsto_of_complete this with ⟨y, y_lim⟩
    use y
    -- the limit point `y` will be the desired point, in `t0` and close to our initial point `x`.
    -- First, we check it belongs to `t0`.
    have : y ∈ t0 :=
      mem_iInter.2 fun k =>
        mem_closure_of_tendsto y_lim
          (by
            simp only [exists_prop, Set.mem_iUnion, Filter.eventually_atTop]
            exact ⟨k, fun m hm => ⟨n + m, by lia, (z m).2⟩⟩)
    use this
    -- Then, we check that `y` is close to `x = z n`. This follows from the fact that `y`
    -- is the limit of `z k`, and the distance between `z n` and `z k` has already been estimated.
    rw [← hz₀]
    exact edist_le_of_edist_le_geometric_two_of_tendsto₀ (B n) hz y_lim
  have I2 : ∀ n, ∀ x ∈ t0, ∃ y ∈ s n, edist x y ≤ 2 * B n := by
    /- For the (much easier) reverse inequality, we start from a point `x ∈ t0` and we want
            to find a point `y ∈ s n` which is close to `x`.
            `x` belongs to `t0`, the intersection of the closures. In particular, it is well
            approximated by a point `z` in `⋃m≥n, s m`, say in `s m`. Since `s m` and
            `s n` are close, this point is itself well approximated by a point `y` in `s n`,
            as required. -/
    intro n x xt0
    have : x ∈ closure (⋃ m ≥ n, s m : Set α) := by apply mem_iInter.1 xt0 n
    obtain ⟨z : α, hz, Dxz : edist x z < B n⟩ := EMetric.mem_closure_iff.1 this (B n) (B_pos n)
    simp only [exists_prop, Set.mem_iUnion] at hz
    obtain ⟨m : ℕ, m_ge_n : m ≥ n, hm : z ∈ (s m : Set α)⟩ := hz
    have : hausdorffEDist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    obtain ⟨y : α, hy : y ∈ (s n : Set α), Dzy : edist z y < B n⟩ :=
      exists_edist_lt_of_hausdorffEDist_lt hm this
    exact
      ⟨y, hy,
        calc
          edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
          _ ≤ B n + B n := by gcongr
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : ∀ n : ℕ, edist (s n) t ≤ 2 * B n := fun n =>
    hausdorffEDist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine EMetric.tendsto_atTop.2 fun ε εpos => ?_
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one <|
      by simp) (Or.inr <| by simp)
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩

theorem isometry_singleton : Isometry ({·} : α → Closeds α) :=
  fun _ _ => hausdorffEDist_singleton

theorem lipschitz_sup : LipschitzWith 1 fun p : Closeds α × Closeds α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

end Closeds

namespace Compacts

/-- In an emetric space, the type of compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance instEMetricSpace : EMetricSpace (Compacts α) where
  /- Since the topology on `Compacts` is not defeq to the one induced by
  `UniformSpace.hausdorff`, we replace the uniformity by `Compacts.uniformSpace`, which has
  the right topology. -/
  __ := (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity <| by rfl
  eq_of_edist_eq_zero {s t} h := Compacts.ext <| by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

theorem edist_eq {s t : Compacts α} : edist s t = hausdorffEDist (s : Set α) t :=
  rfl

theorem isometry_toCloseds : Isometry (Compacts.toCloseds (α := α)) :=
  fun _ _ => rfl

theorem isometry_singleton : Isometry ({·} : α → Compacts α) :=
  fun _ _ => hausdorffEDist_singleton

theorem lipschitz_sup :
    LipschitzWith 1 fun p : Compacts α × Compacts α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

theorem lipschitz_prod :
    LipschitzWith 1 fun p : Compacts α × Compacts β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end Compacts

namespace NonemptyCompacts

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance instEMetricSpace : EMetricSpace (NonemptyCompacts α) where
  /- Since the topology on `NonemptyCompacts` is not defeq to the one induced by
  `UniformSpace.hausdorff`, we replace the uniformity by `NonemptyCompacts.uniformSpace`, which has
  the right topology. -/
  __ := (PseudoEMetricSpace.hausdorff.induced SetLike.coe).replaceUniformity <| by rfl
  eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext <| by
    have : closure (s : Set α) = closure t := hausdorffEDist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

/-- `NonemptyCompacts.toCloseds` is an isometry -/
theorem isometry_toCloseds : Isometry (@NonemptyCompacts.toCloseds α _ _) :=
  fun _ _ => rfl

theorem isometry_toCompacts : Isometry (NonemptyCompacts.toCompacts (α := α)) :=
  fun _ _ => rfl

/-- The range of `NonemptyCompacts.toCloseds` is closed in a complete space -/
theorem isClosed_in_closeds [CompleteSpace α] :
    IsClosed (range <| @NonemptyCompacts.toCloseds α _ _) := by
  have :
    range NonemptyCompacts.toCloseds =
      { s : Closeds α | (s : Set α).Nonempty ∧ IsCompact (s : Set α) } := by
    ext s
    refine ⟨?_, fun h => ⟨⟨⟨s, h.2⟩, h.1⟩, Closeds.ext rfl⟩⟩
    rintro ⟨s, hs, rfl⟩
    exact ⟨s.nonempty, s.isCompact⟩
  rw [this]
  refine isClosed_of_closure_subset fun s hs => ⟨?_, ?_⟩
  · -- take a set t which is nonempty and at a finite distance of s
    rcases EMetric.mem_closure_iff.1 hs ⊤ ENNReal.coe_lt_top with ⟨t, ht, Dst⟩
    rw [edist_comm] at Dst
    -- since `t` is nonempty, so is `s`
    exact nonempty_of_hausdorffEDist_ne_top ht.1 (ne_of_lt Dst)
  · refine isCompact_iff_totallyBounded_isComplete.2 ⟨?_, s.isClosed.isComplete⟩
    refine EMetric.totallyBounded_iff.2 fun ε (εpos : 0 < ε) => ?_
    -- we have to show that s is covered by finitely many eballs of radius ε
    -- pick a nonempty compact set t at distance at most ε/2 of s
    rcases EMetric.mem_closure_iff.1 hs (ε / 2) (ENNReal.half_pos εpos.ne') with ⟨t, ht, Dst⟩
    -- cover this space with finitely many balls of radius ε/2
    rcases EMetric.totallyBounded_iff.1 (isCompact_iff_totallyBounded_isComplete.1 ht.2).1 (ε / 2)
        (ENNReal.half_pos εpos.ne') with ⟨u, fu, ut⟩
    refine ⟨u, ⟨fu, fun x hx => ?_⟩⟩
    -- u : set α, fu : u.finite, ut : t ⊆ ⋃ (y : α) (H : y ∈ u), eball y (ε / 2)
    -- then s is covered by the union of the balls centered at u of radius ε
    rcases exists_edist_lt_of_hausdorffEDist_lt hx Dst with ⟨z, hz, Dxz⟩
    rcases mem_iUnion₂.1 (ut hz) with ⟨y, hy, Dzy⟩
    have : edist x y < ε :=
      calc
        edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add Dxz Dzy
        _ = ε := ENNReal.add_halves _
    exact mem_biUnion hy this

/-- In a complete space, the type of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
instance instCompleteSpace [CompleteSpace α] : CompleteSpace (NonemptyCompacts α) :=
  (completeSpace_iff_isComplete_range
        isometry_toCloseds.isUniformInducing).2 <|
    isClosed_in_closeds.isComplete

/-- In a second countable space, the type of nonempty compact subsets is second countable -/
instance instSecondCountableTopology [SecondCountableTopology α] :
    SecondCountableTopology (NonemptyCompacts α) :=
  haveI : SeparableSpace (NonemptyCompacts α) := by
    /- To obtain a countable dense subset of `NonemptyCompacts α`, start from
        a countable dense subset `s` of α, and then consider all its finite nonempty subsets.
        This set is countable and made of nonempty compact sets. It turns out to be dense:
        by total boundedness, any compact set `t` can be covered by finitely many small balls, and
        approximations in `s` of the centers of these balls give the required finite approximation
        of `t`. -/
    rcases exists_countable_dense α with ⟨s, cs, s_dense⟩
    let v0 := { t : Set α | t.Finite ∧ t ⊆ s }
    let v : Set (NonemptyCompacts α) := { t : NonemptyCompacts α | (t : Set α) ∈ v0 }
    refine ⟨⟨v, ?_, ?_⟩⟩
    · have : v0.Countable := countable_setOf_finite_subset cs
      exact this.preimage SetLike.coe_injective
    · refine fun t => EMetric.mem_closure_iff.2 fun ε εpos => ?_
      -- t is a compact nonempty set, that we have to approximate uniformly by a a set in `v`.
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      have δpos' : 0 < δ / 2 := ENNReal.half_pos δpos.ne'
      -- construct a map F associating to a point in α an approximating point in s, up to δ/2.
      have Exy : ∀ x, ∃ y, y ∈ s ∧ edist x y < δ / 2 := by
        intro x
        rcases EMetric.mem_closure_iff.1 (s_dense x) (δ / 2) δpos' with ⟨y, ys, hy⟩
        exact ⟨y, ⟨ys, hy⟩⟩
      let F x := (Exy x).choose
      have Fspec : ∀ x, F x ∈ s ∧ edist x (F x) < δ / 2 := fun x => (Exy x).choose_spec
      -- cover `t` with finitely many balls. Their centers form a set `a`
      have : TotallyBounded (t : Set α) := t.isCompact.totallyBounded
      obtain ⟨a : Set α, af : Set.Finite a, ta : (t : Set α) ⊆ ⋃ y ∈ a, Metric.eball y (δ / 2)⟩ :=
        EMetric.totallyBounded_iff.1 this (δ / 2) δpos'
      -- replace each center by a nearby approximation in `s`, giving a new set `b`
      let b := F '' a
      have : b.Finite := af.image _
      have tb : ∀ x ∈ t, ∃ y ∈ b, edist x y < δ := by
        intro x hx
        rcases mem_iUnion₂.1 (ta hx) with ⟨z, za, Dxz⟩
        exists F z, mem_image_of_mem _ za
        calc
          edist x (F z) ≤ edist x z + edist z (F z) := edist_triangle _ _ _
          _ < δ / 2 + δ / 2 := ENNReal.add_lt_add Dxz (Fspec z).2
          _ = δ := ENNReal.add_halves _
      -- keep only the points in `b` that are close to point in `t`, yielding a new set `c`
      let c := { y ∈ b | ∃ x ∈ t, edist x y < δ }
      have : c.Finite := ‹b.Finite›.subset fun x hx => hx.1
      -- points in `t` are well approximated by points in `c`
      have tc : ∀ x ∈ t, ∃ y ∈ c, edist x y ≤ δ := by
        intro x hx
        rcases tb x hx with ⟨y, yv, Dxy⟩
        have : y ∈ c := by simpa [c, -mem_image] using ⟨yv, ⟨x, hx, Dxy⟩⟩
        exact ⟨y, this, le_of_lt Dxy⟩
      -- points in `c` are well approximated by points in `t`
      have ct : ∀ y ∈ c, ∃ x ∈ t, edist y x ≤ δ := by
        rintro y ⟨_, x, xt, Dyx⟩
        have : edist y x ≤ δ :=
          calc
            edist y x = edist x y := edist_comm _ _
            _ ≤ δ := le_of_lt Dyx
        exact ⟨x, xt, this⟩
      -- it follows that their Hausdorff distance is small
      have : hausdorffEDist (t : Set α) c ≤ δ := hausdorffEDist_le_of_mem_edist tc ct
      have Dtc : hausdorffEDist (t : Set α) c < ε := this.trans_lt δlt
      -- the set `c` is not empty, as it is well approximated by a nonempty set
      have hc : c.Nonempty := nonempty_of_hausdorffEDist_ne_top t.nonempty (ne_top_of_lt Dtc)
      -- let `d` be the version of `c` in the type `NonemptyCompacts α`
      let d : NonemptyCompacts α := ⟨⟨c, ‹c.Finite›.isCompact⟩, hc⟩
      have : c ⊆ s := by
        intro x hx
        rcases (mem_image _ _ _).1 hx.1 with ⟨y, ⟨_, yx⟩⟩
        rw [← yx]
        exact (Fspec y).1
      have : d ∈ v := ⟨‹c.Finite›, this⟩
      -- we have proved that `d` is a good approximation of `t` as requested
      exact ⟨d, ‹d ∈ v›, Dtc⟩
  UniformSpace.secondCountable_of_separable (NonemptyCompacts α)

theorem isometry_singleton : Isometry ({·} : α → NonemptyCompacts α) :=
  fun _ _ => hausdorffEDist_singleton

theorem lipschitz_sup :
    LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyCompacts α => p.1 ⊔ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_union_le

theorem lipschitz_prod :
    LipschitzWith 1 fun p : NonemptyCompacts α × NonemptyCompacts β => p.1 ×ˢ p.2 :=
  .of_edist_le fun _ _ => hausdorffEDist_prod_le

end NonemptyCompacts

end TopologicalSpace

namespace EMetric

open Metric

@[deprecated (since := "2025-11-19")]
alias NonemptyCompacts.continuous_toCloseds :=
  TopologicalSpace.NonemptyCompacts.continuous_toCloseds

@[deprecated (since := "2025-08-20")]
alias isClosed_subsets_of_isClosed := TopologicalSpace.Closeds.isClosed_subsets_of_isClosed

@[deprecated (since := "2025-11-19")]
alias NonemptyCompacts.isClosed_subsets_of_isClosed :=
  TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed

@[deprecated (since := "2025-11-19")]
alias Closeds.isClosed_subsets_of_isClosed :=
  TopologicalSpace.Closeds.isClosed_subsets_of_isClosed

@[deprecated (since := "2026-01-08")]
alias mem_hausdorffEntourage_of_hausdorffEdist_lt :=
  mem_hausdorffEntourage_of_hausdorffEDist_lt

@[deprecated (since := "2026-01-08")]
alias hausdorffEdist_le_of_mem_hausdorffEntourage := hausdorffEDist_le_of_mem_hausdorffEntourage

@[deprecated (since := "2026-01-08")]
alias continuous_infEdist_hausdorffEdist :=
  TopologicalSpace.Closeds.continuous_infEDist

@[deprecated (since := "2026-01-08")]
alias Closeds.edist_eq := TopologicalSpace.Closeds.edist_eq

@[deprecated (since := "2026-01-08")]
alias Closeds.isometry_singleton := TopologicalSpace.Closeds.isometry_singleton

@[deprecated (since := "2026-01-08")]
alias Closeds.lipschitz_sup := TopologicalSpace.Closeds.lipschitz_sup

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isometry_toCloseds :=
  TopologicalSpace.NonemptyCompacts.isometry_toCloseds

@[deprecated (since := "2025-08-20")]
alias NonemptyCompacts.ToCloseds.isUniformEmbedding :=
  TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCloseds

@[deprecated (since := "2025-11-19")]
alias NonemptyCompacts.isUniformEmbedding_toCloseds :=
  TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCloseds

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isClosed_in_closeds :=
  TopologicalSpace.NonemptyCompacts.isClosed_in_closeds

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.isometry_singleton :=
  TopologicalSpace.NonemptyCompacts.isometry_singleton

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.lipschitz_sup :=
  TopologicalSpace.NonemptyCompacts.lipschitz_sup

@[deprecated (since := "2026-01-08")]
alias NonemptyCompacts.lipschitz_prod :=
  TopologicalSpace.NonemptyCompacts.lipschitz_prod

end EMetric --namespace

namespace Metric

section

variable {α : Type*} [MetricSpace α]

/-- `NonemptyCompacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
instance NonemptyCompacts.instMetricSpace : MetricSpace (NonemptyCompacts α) :=
  EMetricSpace.toMetricSpace fun x y =>
    hausdorffEDist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
      y.isCompact.isBounded

/-- The distance on `NonemptyCompacts α` is the Hausdorff distance, by construction -/
theorem NonemptyCompacts.dist_eq {x y : NonemptyCompacts α} :
    dist x y = hausdorffDist (x : Set α) y :=
  rfl

theorem lipschitz_infDist_set (x : α) : LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s :=
  LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    exact infDist_le_infDist_add_hausdorffDist (edist_ne_top t s)

theorem lipschitz_infDist : LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2 := by
  rw [← one_add_one_eq_two]
  exact LipschitzWith.uncurry
    (fun s : NonemptyCompacts α => lipschitz_infDist_pt (s : Set α)) lipschitz_infDist_set

theorem uniformContinuous_infDist_Hausdorff_dist :
    UniformContinuous fun p : α × NonemptyCompacts α => infDist p.1 p.2 :=
  lipschitz_infDist.uniformContinuous

end --section

end Metric --namespace
