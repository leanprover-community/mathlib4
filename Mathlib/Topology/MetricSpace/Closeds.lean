/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.UniformSpace.Closeds

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

noncomputable section

universe u

open Set Function TopologicalSpace Filter Topology ENNReal

namespace EMetric

section

variable {α : Type u} [PseudoEMetricSpace α] {S : Type*} [SetLike S α]

theorem mem_hausdorffEntourage_of_hausdorffEdist_lt {s t : S} {δ : ℝ≥0∞}
    (h : hausdorffEdist (s : Set α) t < δ) :
    (s, t) ∈ hausdorffEntourage {p | edist p.1 p.2 < δ} := by
  rw [hausdorffEdist, max_lt_iff] at h
  have {s t : Set α} (h : ⨆ x ∈ s, infEdist x t < δ) :
      s ⊆ UniformSpace.thickening {p | edist p.1 p.2 < δ} t := by
    intro x hx
    have := (le_iSup₂ x hx).trans_lt h
    simp_rw [infEdist, iInf_lt_iff] at this
    obtain ⟨y, hy, hxy⟩ := this
    rw [edist_comm] at hxy
    exact UniformSpace.ball_subset_thickening hy _ hxy
  exact ⟨this h.1, this h.2⟩

theorem hausdorffEdist_le_of_mem_hausdorffEntourage {s t : S} {δ : ℝ≥0∞}
    (h : (s, t) ∈ hausdorffEntourage {p | edist p.1 p.2 ≤ δ}) :
    hausdorffEdist (s : Set α) t ≤ δ := by
  rw [hausdorffEdist, max_le_iff]
  have {s t : Set α} (h : s ⊆ UniformSpace.thickening {p | edist p.1 p.2 ≤ δ} t) :
      ⨆ x ∈ s, infEdist x t ≤ δ := by
    rw [iSup₂_le_iff]
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp <| h hx
    refine iInf₂_le_of_le y hy ?_
    rwa [edist_comm]
  exact ⟨this h.1, this h.2⟩

/-- The Hausdorff pseudo extended metric on a family of subsets of a pseudo extended metric space.
See note [reducible non-instances]. -/
protected abbrev _root_.PseudoEMetricSpace.hausdorff : PseudoEMetricSpace S where
  edist s t := hausdorffEdist (s : Set α) t
  edist_self _ := hausdorffEdist_self
  edist_comm _ _ := hausdorffEdist_comm
  edist_triangle _ _ _ := hausdorffEdist_triangle
  toUniformSpace := .hausdorff
  uniformity_edist := by
    refine le_antisymm
      (le_iInf₂ fun ε hε => Filter.le_principal_iff.mpr ?_)
      (uniformity_basis_edist.lift' monotone_hausdorffEntourage |>.ge_iff.mpr fun ε hε =>
        Filter.mem_iInf_of_mem ε <| Filter.mem_iInf_of_mem hε fun _ =>
        mem_hausdorffEntourage_of_hausdorffEdist_lt)
    obtain ⟨δ, hδ, hδε⟩ := exists_between hε
    filter_upwards [Filter.mem_lift' (uniformity_basis_edist_le.mem_of_mem hδ)]
      with _ h using hδε.trans_le' <| hausdorffEdist_le_of_mem_hausdorffEntourage h

end

section

variable {α : Type u} [EMetricSpace α] {s : Set α}

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
instance Closeds.emetricSpace : EMetricSpace (Closeds α) where
  __ := PseudoEMetricSpace.hausdorff
  eq_of_edist_eq_zero {s t} h :=
    Closeds.ext <| (hausdorffEdist_zero_iff_eq_of_closed s.isClosed t.isClosed).1 h

/-- The edistance to a closed set depends continuously on the point and the set -/
theorem continuous_infEdist_hausdorffEdist :
    Continuous fun p : α × Closeds α => infEdist p.1 p.2 := by
  refine continuous_of_le_add_edist 2 (by simp) ?_
  rintro ⟨x, s⟩ ⟨y, t⟩
  calc
    infEdist x s ≤ infEdist x t + hausdorffEdist (t : Set α) s :=
      infEdist_le_infEdist_add_hausdorffEdist
    _ ≤ infEdist y t + edist x y + hausdorffEdist (t : Set α) s := by
      gcongr; apply infEdist_le_infEdist_add_edist
    _ = infEdist y t + (edist x y + hausdorffEdist (s : Set α) t) := by
      rw [add_assoc, hausdorffEdist_comm]
    _ ≤ infEdist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) := by
      gcongr <;> apply_rules [le_max_left, le_max_right]
    _ = infEdist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]

/-- Subsets of a given closed subset form a closed set -/
@[deprecated (since := "2025-10-22")]
alias Closeds.isClosed_subsets_of_isClosed := TopologicalSpace.Closeds.isClosed_subsets_of_isClosed

@[deprecated (since := "2025-08-20")]
alias isClosed_subsets_of_isClosed := TopologicalSpace.Closeds.isClosed_subsets_of_isClosed

/-- By definition, the edistance on `Closeds α` is given by the Hausdorff edistance -/
theorem Closeds.edist_eq {s t : Closeds α} : edist s t = hausdorffEdist (s : Set α) t :=
  rfl

/-- In a complete space, the type of closed subsets is complete for the
Hausdorff edistance. -/
instance Closeds.completeSpace [CompleteSpace α] : CompleteSpace (Closeds α) := by
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
  refine complete_of_convergent_controlled_sequences B B_pos fun s hs => ?_
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
          refine exists_edist_lt_of_hausdorffEdist_lt (s := s (n + l)) z.2 ?_
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
            exact ⟨k, fun m hm => ⟨n + m, by cutsat, (z m).2⟩⟩)
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
    obtain ⟨z : α, hz, Dxz : edist x z < B n⟩ := mem_closure_iff.1 this (B n) (B_pos n)
    simp only [exists_prop, Set.mem_iUnion] at hz
    obtain ⟨m : ℕ, m_ge_n : m ≥ n, hm : z ∈ (s m : Set α)⟩ := hz
    have : hausdorffEdist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    obtain ⟨y : α, hy : y ∈ (s n : Set α), Dzy : edist z y < B n⟩ :=
      exists_edist_lt_of_hausdorffEdist_lt hm this
    exact
      ⟨y, hy,
        calc
          edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
          _ ≤ B n + B n := by gcongr
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : ∀ n : ℕ, edist (s n) t ≤ 2 * B n := fun n =>
    hausdorffEdist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine tendsto_atTop.2 fun ε εpos => ?_
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one <|
      by simp) (Or.inr <| by simp)
  rw [mul_zero] at this
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩

/-- In a compact space, the type of closed subsets is compact. -/
instance Closeds.compactSpace [CompactSpace α] : CompactSpace (Closeds α) :=
  ⟨by
    /- by completeness, it suffices to show that it is totally bounded,
        i.e., for all ε>0, there is a finite set which is ε-dense.
        start from a set `s` which is ε-dense in α. Then the subsets of `s`
        are finitely many, and ε-dense for the Hausdorff distance. -/
    refine
      (EMetric.totallyBounded_iff.2 fun ε εpos => ?_).isCompact_of_isClosed isClosed_univ
    rcases exists_between εpos with ⟨δ, δpos, δlt⟩
    obtain ⟨s : Set α, fs : s.Finite, hs : univ ⊆ ⋃ y ∈ s, ball y δ⟩ :=
      EMetric.totallyBounded_iff.1
        (isCompact_iff_totallyBounded_isComplete.1 (@isCompact_univ α _ _)).1 δ δpos
    -- we first show that any set is well approximated by a subset of `s`.
    have main : ∀ u : Set α, ∃ v ⊆ s, hausdorffEdist u v ≤ δ := by
      intro u
      let v := { x : α | x ∈ s ∧ ∃ y ∈ u, edist x y < δ }
      exists v, (fun x hx => hx.1 : v ⊆ s)
      refine hausdorffEdist_le_of_mem_edist ?_ ?_
      · intro x hx
        have : x ∈ ⋃ y ∈ s, ball y δ := hs (by simp)
        rcases mem_iUnion₂.1 this with ⟨y, ys, dy⟩
        have : edist y x < δ := by simpa [edist_comm]
        exact ⟨y, ⟨ys, ⟨x, hx, this⟩⟩, le_of_lt dy⟩
      · rintro x ⟨_, ⟨y, yu, hy⟩⟩
        exact ⟨y, yu, le_of_lt hy⟩
    -- introduce the set F of all subsets of `s` (seen as members of `Closeds α`).
    let F := { f : Closeds α | (f : Set α) ⊆ s }
    refine ⟨F, ?_, fun u _ => ?_⟩
    -- `F` is finite
    · apply @Finite.of_finite_image _ _ F _
      · apply fs.finite_subsets.subset fun b => _
        · exact fun s => (s : Set α)
        simp only [F, and_imp, Set.mem_image, Set.mem_setOf_eq, exists_imp]
        intro _ x hx hx'
        rwa [hx'] at hx
      · exact SetLike.coe_injective.injOn
    -- `F` is ε-dense
    · obtain ⟨t0, t0s, Dut0⟩ := main u
      have : IsClosed t0 := (fs.subset t0s).isCompact.isClosed
      let t : Closeds α := ⟨t0, this⟩
      have : t ∈ F := t0s
      have : edist u t < ε := lt_of_le_of_lt Dut0 δlt
      apply mem_iUnion₂.2
      exact ⟨t, ‹t ∈ F›, this⟩⟩

namespace NonemptyCompacts

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance emetricSpace : EMetricSpace (NonemptyCompacts α) where
  __ := PseudoEMetricSpace.hausdorff
  eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext <| by
    have : closure (s : Set α) = closure t := hausdorffEdist_zero_iff_closure_eq_closure.1 h
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this

/-- `NonemptyCompacts.toCloseds` is an isometry -/
theorem isometry_toCloseds : Isometry (@NonemptyCompacts.toCloseds α _ _) :=
  fun _ _ => rfl

/-- `NonemptyCompacts.toCloseds` is a uniform embedding (as it is an isometry) -/
@[deprecated (since := "2025-10-22")]
alias isUniformEmbedding_toCloseds := TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCloseds

@[deprecated (since := "2025-08-20")]
alias ToCloseds.isUniformEmbedding := TopologicalSpace.NonemptyCompacts.isUniformEmbedding_toCloseds

/-- `NonemptyCompacts.toCloseds` is continuous (as it is an isometry) -/
@[deprecated (since := "2025-10-22")]
alias continuous_toCloseds := TopologicalSpace.NonemptyCompacts.continuous_toCloseds

@[deprecated (since := "2025-10-22")]
alias isClosed_subsets_of_isClosed := TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed

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
    rcases mem_closure_iff.1 hs ⊤ ENNReal.coe_lt_top with ⟨t, ht, Dst⟩
    rw [edist_comm] at Dst
    -- since `t` is nonempty, so is `s`
    exact nonempty_of_hausdorffEdist_ne_top ht.1 (ne_of_lt Dst)
  · refine isCompact_iff_totallyBounded_isComplete.2 ⟨?_, s.isClosed.isComplete⟩
    refine totallyBounded_iff.2 fun ε (εpos : 0 < ε) => ?_
    -- we have to show that s is covered by finitely many eballs of radius ε
    -- pick a nonempty compact set t at distance at most ε/2 of s
    rcases mem_closure_iff.1 hs (ε / 2) (ENNReal.half_pos εpos.ne') with ⟨t, ht, Dst⟩
    -- cover this space with finitely many balls of radius ε/2
    rcases totallyBounded_iff.1 (isCompact_iff_totallyBounded_isComplete.1 ht.2).1 (ε / 2)
        (ENNReal.half_pos εpos.ne') with
      ⟨u, fu, ut⟩
    refine ⟨u, ⟨fu, fun x hx => ?_⟩⟩
    -- u : set α, fu : u.finite, ut : t ⊆ ⋃ (y : α) (H : y ∈ u), eball y (ε / 2)
    -- then s is covered by the union of the balls centered at u of radius ε
    rcases exists_edist_lt_of_hausdorffEdist_lt hx Dst with ⟨z, hz, Dxz⟩
    rcases mem_iUnion₂.1 (ut hz) with ⟨y, hy, Dzy⟩
    have : edist x y < ε :=
      calc
        edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := ENNReal.add_lt_add Dxz Dzy
        _ = ε := ENNReal.add_halves _
    exact mem_biUnion hy this

/-- In a complete space, the type of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
instance completeSpace [CompleteSpace α] : CompleteSpace (NonemptyCompacts α) :=
  (completeSpace_iff_isComplete_range
        isometry_toCloseds.isUniformInducing).2 <|
    isClosed_in_closeds.isComplete

/-- In a compact space, the type of nonempty compact subsets is compact. This follows from
the same statement for closed subsets -/
instance compactSpace [CompactSpace α] : CompactSpace (NonemptyCompacts α) :=
  ⟨by
    rw [isometry_toCloseds.isEmbedding.isCompact_iff, image_univ]
    exact isClosed_in_closeds.isCompact⟩

/-- In a second countable space, the type of nonempty compact subsets is second countable -/
instance secondCountableTopology [SecondCountableTopology α] :
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
    · refine fun t => mem_closure_iff.2 fun ε εpos => ?_
      -- t is a compact nonempty set, that we have to approximate uniformly by a a set in `v`.
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      have δpos' : 0 < δ / 2 := ENNReal.half_pos δpos.ne'
      -- construct a map F associating to a point in α an approximating point in s, up to δ/2.
      have Exy : ∀ x, ∃ y, y ∈ s ∧ edist x y < δ / 2 := by
        intro x
        rcases mem_closure_iff.1 (s_dense x) (δ / 2) δpos' with ⟨y, ys, hy⟩
        exact ⟨y, ⟨ys, hy⟩⟩
      let F x := (Exy x).choose
      have Fspec : ∀ x, F x ∈ s ∧ edist x (F x) < δ / 2 := fun x => (Exy x).choose_spec
      -- cover `t` with finitely many balls. Their centers form a set `a`
      have : TotallyBounded (t : Set α) := t.isCompact.totallyBounded
      obtain ⟨a : Set α, af : Set.Finite a, ta : (t : Set α) ⊆ ⋃ y ∈ a, ball y (δ / 2)⟩ :=
        totallyBounded_iff.1 this (δ / 2) δpos'
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
      have : hausdorffEdist (t : Set α) c ≤ δ := hausdorffEdist_le_of_mem_edist tc ct
      have Dtc : hausdorffEdist (t : Set α) c < ε := this.trans_lt δlt
      -- the set `c` is not empty, as it is well approximated by a nonempty set
      have hc : c.Nonempty := nonempty_of_hausdorffEdist_ne_top t.nonempty (ne_top_of_lt Dtc)
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

end NonemptyCompacts

end

--section
end EMetric

--namespace
namespace Metric

section

variable {α : Type u} [MetricSpace α]

/-- `NonemptyCompacts α` inherits a metric space structure, as the Hausdorff
edistance between two such sets is finite. -/
instance NonemptyCompacts.metricSpace : MetricSpace (NonemptyCompacts α) :=
  EMetricSpace.toMetricSpace fun x y =>
    hausdorffEdist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.isBounded
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
