/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sets.Compacts

#align_import topology.metric_space.closeds from "leanprover-community/mathlib"@"f2ce6086713c78a7f880485f7917ea547a215982"

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

open Classical Topology ENNReal

universe u

open Classical Set Function TopologicalSpace Filter

namespace EMetric

section

variable {α : Type u} [EMetricSpace α] {s : Set α}

/-- In emetric spaces, the Hausdorff edistance defines an emetric space structure
on the type of closed subsets -/
instance Closeds.emetricSpace : EMetricSpace (Closeds α) where
  edist s t := hausdorffEdist (s : Set α) t
  edist_self s := hausdorffEdist_self
  edist_comm s t := hausdorffEdist_comm
  edist_triangle s t u := hausdorffEdist_triangle
  eq_of_edist_eq_zero {s t} h :=
    Closeds.ext <| (hausdorffEdist_zero_iff_eq_of_closed s.closed t.closed).1 h
#align emetric.closeds.emetric_space EMetric.Closeds.emetricSpace

/-- The edistance to a closed set depends continuously on the point and the set -/
theorem continuous_infEdist_hausdorffEdist :
    Continuous fun p : α × Closeds α => infEdist p.1 p.2 := by
  refine' continuous_of_le_add_edist 2 (by simp) _
  -- ⊢ ∀ (x y : α × Closeds α), infEdist x.fst ↑x.snd ≤ infEdist y.fst ↑y.snd + 2 * …
  rintro ⟨x, s⟩ ⟨y, t⟩
  -- ⊢ infEdist (x, s).fst ↑(x, s).snd ≤ infEdist (y, t).fst ↑(y, t).snd + 2 * edis …
  calc
    infEdist x s ≤ infEdist x t + hausdorffEdist (t : Set α) s :=
      infEdist_le_infEdist_add_hausdorffEdist
    _ ≤ infEdist y t + edist x y + hausdorffEdist (t : Set α) s :=
      (add_le_add_right infEdist_le_infEdist_add_edist _)
    _ = infEdist y t + (edist x y + hausdorffEdist (s : Set α) t) := by
      rw [add_assoc, hausdorffEdist_comm]
    _ ≤ infEdist y t + (edist (x, s) (y, t) + edist (x, s) (y, t)) :=
      (add_le_add_left (add_le_add (le_max_left _ _) (le_max_right _ _)) _)
    _ = infEdist y t + 2 * edist (x, s) (y, t) := by rw [← mul_two, mul_comm]
set_option linter.uppercaseLean3 false in
#align emetric.continuous_infEdist_hausdorffEdist EMetric.continuous_infEdist_hausdorffEdist

/-- Subsets of a given closed subset form a closed set -/
theorem isClosed_subsets_of_isClosed (hs : IsClosed s) :
    IsClosed { t : Closeds α | (t : Set α) ⊆ s } := by
  refine' isClosed_of_closure_subset fun t ht x hx => _
  -- ⊢ x ∈ s
  -- t : Closeds α, ht : t ∈ closure {t : Closeds α | t ⊆ s},
  -- x : α, hx : x ∈ t
  -- goal : x ∈ s
  have : x ∈ closure s := by
    refine' mem_closure_iff.2 fun ε εpos => _
    rcases mem_closure_iff.1 ht ε εpos with ⟨u, hu, Dtu⟩
    -- u : Closeds α, hu : u ∈ {t : Closeds α | t ⊆ s}, hu' : edist t u < ε
    rcases exists_edist_lt_of_hausdorffEdist_lt hx Dtu with ⟨y, hy, Dxy⟩
    -- y : α, hy : y ∈ u, Dxy : edist x y < ε
    exact ⟨y, hu hy, Dxy⟩
  rwa [hs.closure_eq] at this
  -- 🎉 no goals
#align emetric.is_closed_subsets_of_is_closed EMetric.isClosed_subsets_of_isClosed

/-- By definition, the edistance on `Closeds α` is given by the Hausdorff edistance -/
theorem Closeds.edist_eq {s t : Closeds α} : edist s t = hausdorffEdist (s : Set α) t :=
  rfl
#align emetric.closeds.edist_eq EMetric.Closeds.edist_eq

/-- In a complete space, the type of closed subsets is complete for the
Hausdorff edistance. -/
instance Closeds.completeSpace [CompleteSpace α] : CompleteSpace (Closeds α) := by
  /- We will show that, if a sequence of sets `s n` satisfies
    `edist (s n) (s (n+1)) < 2^{-n}`, then it converges. This is enough to guarantee
    completeness, by a standard completeness criterion.
    We use the shorthand `B n = 2^{-n}` in ennreal. -/
  let B : ℕ → ℝ≥0∞ := fun n => 2⁻¹ ^ n
  -- ⊢ CompleteSpace (Closeds α)
  have B_pos : ∀ n, (0 : ℝ≥0∞) < B n := by simp [ENNReal.pow_pos]
  -- ⊢ CompleteSpace (Closeds α)
  have B_ne_top : ∀ n, B n ≠ ⊤ := by simp [ENNReal.pow_ne_top]
  -- ⊢ CompleteSpace (Closeds α)
  /- Consider a sequence of closed sets `s n` with `edist (s n) (s (n+1)) < B n`.
    We will show that it converges. The limit set is `t0 = ⋂n, closure (⋃m≥n, s m)`.
    We will have to show that a point in `s n` is close to a point in `t0`, and a point
    in `t0` is close to a point in `s n`. The completeness then follows from a
    standard criterion. -/
  refine' complete_of_convergent_controlled_sequences B B_pos fun s hs => _
  -- ⊢ ∃ x, Tendsto s atTop (𝓝 x)
  let t0 := ⋂ n, closure (⋃ m ≥ n, s m : Set α)
  -- ⊢ ∃ x, Tendsto s atTop (𝓝 x)
  let t : Closeds α := ⟨t0, isClosed_iInter fun _ => isClosed_closure⟩
  -- ⊢ ∃ x, Tendsto s atTop (𝓝 x)
  use t
  -- ⊢ Tendsto s atTop (𝓝 t)
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
          refine' exists_edist_lt_of_hausdorffEdist_lt _ _
          · exact (s (n + l) : Set α)
          · exact z.2
          simp only [ENNReal.inv_pow, div_eq_mul_inv]
          rw [← pow_add]
          apply hs <;> simp
        exact ⟨⟨z', z'_mem⟩, le_of_lt hz'⟩
      use fun k => Nat.recOn k ⟨x, hx⟩ fun l z => choose (this l z)
      simp only [Nat.add_zero, Nat.zero_eq, Nat.rec_zero, Nat.rec_add_one, true_and]
      exact fun k => choose_spec (this k _)
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
            simp only [exists_prop, Set.mem_iUnion, Filter.eventually_atTop, Set.mem_preimage,
              Set.preimage_iUnion]
            exact ⟨k, fun m hm => ⟨n + m, zero_add k ▸ add_le_add (zero_le n) hm, (z m).2⟩⟩)
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
    rcases mem_closure_iff.1 this (B n) (B_pos n) with ⟨z, hz, Dxz⟩
    -- z : α, Dxz : edist x z < B n,
    simp only [exists_prop, Set.mem_iUnion] at hz
    rcases hz with ⟨m, ⟨m_ge_n, hm⟩⟩
    -- m : ℕ, m_ge_n : m ≥ n, hm : z ∈ s m
    have : hausdorffEdist (s m : Set α) (s n) < B n := hs n m n m_ge_n (le_refl n)
    rcases exists_edist_lt_of_hausdorffEdist_lt hm this with ⟨y, hy, Dzy⟩
    -- y : α, hy : y ∈ s n, Dzy : edist z y < B n
    exact
      ⟨y, hy,
        calc
          edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
          _ ≤ B n + B n := (add_le_add (le_of_lt Dxz) (le_of_lt Dzy))
          _ = 2 * B n := (two_mul _).symm
          ⟩
  -- Deduce from the above inequalities that the distance between `s n` and `t0` is at most `2 B n`.
  have main : ∀ n : ℕ, edist (s n) t ≤ 2 * B n := fun n =>
    hausdorffEdist_le_of_mem_edist (I1 n) (I2 n)
  -- from this, the convergence of `s n` to `t0` follows.
  refine' tendsto_atTop.2 fun ε εpos => _
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → edist (s n) t < ε
  have : Tendsto (fun n => 2 * B n) atTop (𝓝 (2 * 0)) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.tendsto_pow_atTop_nhds_0_of_lt_1 <| by simp [ENNReal.one_lt_two]) (Or.inr <| by simp)
  rw [mul_zero] at this
  -- ⊢ ∃ N, ∀ (n : ℕ), n ≥ N → edist (s n) t < ε
  obtain ⟨N, hN⟩ : ∃ N, ∀ b ≥ N, ε > 2 * B b :=
    ((tendsto_order.1 this).2 ε εpos).exists_forall_of_atTop
  exact ⟨N, fun n hn => lt_of_le_of_lt (main n) (hN n hn)⟩
  -- 🎉 no goals
#align emetric.closeds.complete_space EMetric.Closeds.completeSpace

/-- In a compact space, the type of closed subsets is compact. -/
instance Closeds.compactSpace [CompactSpace α] : CompactSpace (Closeds α) :=
  ⟨by
    /- by completeness, it suffices to show that it is totally bounded,
        i.e., for all ε>0, there is a finite set which is ε-dense.
        start from a set `s` which is ε-dense in α. Then the subsets of `s`
        are finitely many, and ε-dense for the Hausdorff distance. -/
    refine'
      isCompact_of_totallyBounded_isClosed (EMetric.totallyBounded_iff.2 fun ε εpos => _)
        isClosed_univ
    rcases exists_between εpos with ⟨δ, δpos, δlt⟩
    -- ⊢ ∃ t, Set.Finite t ∧ univ ⊆ ⋃ (y : Closeds α) (_ : y ∈ t), ball y ε
    rcases EMetric.totallyBounded_iff.1
        (isCompact_iff_totallyBounded_isComplete.1 (@isCompact_univ α _ _)).1 δ δpos with
      ⟨s, fs, hs⟩
    -- s : Set α, fs : s.Finite, hs : univ ⊆ ⋃ (y : α) (H : y ∈ s), eball y δ
    -- we first show that any set is well approximated by a subset of `s`.
    have main : ∀ u : Set α, ∃ (v : _) (_ : v ⊆ s), hausdorffEdist u v ≤ δ := by
      intro u
      let v := { x : α | x ∈ s ∧ ∃ y ∈ u, edist x y < δ }
      exists v, (fun x hx => hx.1 : v ⊆ s)
      refine' hausdorffEdist_le_of_mem_edist _ _
      · intro x hx
        have : x ∈ ⋃ y ∈ s, ball y δ := hs (by simp)
        rcases mem_iUnion₂.1 this with ⟨y, ys, dy⟩
        have : edist y x < δ := by simp at dy; rwa [edist_comm] at dy
        exact ⟨y, ⟨ys, ⟨x, hx, this⟩⟩, le_of_lt dy⟩
      · rintro x ⟨_, ⟨y, yu, hy⟩⟩
        exact ⟨y, yu, le_of_lt hy⟩
    -- introduce the set F of all subsets of `s` (seen as members of `Closeds α`).
    let F := { f : Closeds α | (f : Set α) ⊆ s }
    -- ⊢ ∃ t, Set.Finite t ∧ univ ⊆ ⋃ (y : Closeds α) (_ : y ∈ t), ball y ε
    refine' ⟨F, _, fun u _ => _⟩
    -- ⊢ Set.Finite F
    -- `F` is finite
    · apply @Finite.of_finite_image _ _ F _
      · apply fs.finite_subsets.subset fun b => _
        -- ⊢ Closeds α → Set α
        exact fun s => (s : Set α)
        -- ⊢ ∀ (b : Set α), b ∈ (fun s => ↑s) '' F → b ∈ {b | b ⊆ s}
        simp only [and_imp, Set.mem_image, Set.mem_setOf_eq, exists_imp]
        -- ⊢ ∀ (b : Set α) (x : Closeds α), ↑x ⊆ s → ↑x = b → b ⊆ s
        intro _ x hx hx'
        -- ⊢ b✝ ⊆ s
        rwa [hx'] at hx
        -- 🎉 no goals
      · exact SetLike.coe_injective.injOn F
        -- 🎉 no goals
    -- `F` is ε-dense
    · obtain ⟨t0, t0s, Dut0⟩ := main u
      -- ⊢ u ∈ ⋃ (y : Closeds α) (_ : y ∈ F), ball y ε
      have : IsClosed t0 := (fs.subset t0s).isCompact.isClosed
      -- ⊢ u ∈ ⋃ (y : Closeds α) (_ : y ∈ F), ball y ε
      let t : Closeds α := ⟨t0, this⟩
      -- ⊢ u ∈ ⋃ (y : Closeds α) (_ : y ∈ F), ball y ε
      have : t ∈ F := t0s
      -- ⊢ u ∈ ⋃ (y : Closeds α) (_ : y ∈ F), ball y ε
      have : edist u t < ε := lt_of_le_of_lt Dut0 δlt
      -- ⊢ u ∈ ⋃ (y : Closeds α) (_ : y ∈ F), ball y ε
      apply mem_iUnion₂.2
      -- ⊢ ∃ i j, u ∈ ball i ε
      exact ⟨t, ‹t ∈ F›, this⟩⟩
      -- 🎉 no goals
#align emetric.closeds.compact_space EMetric.Closeds.compactSpace

/-- In an emetric space, the type of non-empty compact subsets is an emetric space,
where the edistance is the Hausdorff edistance -/
instance NonemptyCompacts.emetricSpace : EMetricSpace (NonemptyCompacts α) where
  edist s t := hausdorffEdist (s : Set α) t
  edist_self s := hausdorffEdist_self
  edist_comm s t := hausdorffEdist_comm
  edist_triangle s t u := hausdorffEdist_triangle
  eq_of_edist_eq_zero {s t} h := NonemptyCompacts.ext <| by
    have : closure (s : Set α) = closure t := hausdorffEdist_zero_iff_closure_eq_closure.1 h
    -- ⊢ ↑s = ↑t
    rwa [s.isCompact.isClosed.closure_eq, t.isCompact.isClosed.closure_eq] at this
    -- 🎉 no goals
#align emetric.nonempty_compacts.emetric_space EMetric.NonemptyCompacts.emetricSpace

/-- `NonemptyCompacts.toCloseds` is a uniform embedding (as it is an isometry) -/
theorem NonemptyCompacts.ToCloseds.uniformEmbedding :
    UniformEmbedding (@NonemptyCompacts.toCloseds α _ _) :=
  Isometry.uniformEmbedding fun _ _ => rfl
#align emetric.nonempty_compacts.to_closeds.uniform_embedding EMetric.NonemptyCompacts.ToCloseds.uniformEmbedding

/-- The range of `NonemptyCompacts.toCloseds` is closed in a complete space -/
theorem NonemptyCompacts.isClosed_in_closeds [CompleteSpace α] :
    IsClosed (range <| @NonemptyCompacts.toCloseds α _ _) := by
  have :
    range NonemptyCompacts.toCloseds =
      { s : Closeds α | (s : Set α).Nonempty ∧ IsCompact (s : Set α) } := by
    ext s
    refine' ⟨_, fun h => ⟨⟨⟨s, h.2⟩, h.1⟩, Closeds.ext rfl⟩⟩
    rintro ⟨s, hs, rfl⟩
    exact ⟨s.nonempty, s.isCompact⟩
  rw [this]
  -- ⊢ IsClosed {s | Set.Nonempty ↑s ∧ IsCompact ↑s}
  refine' isClosed_of_closure_subset fun s hs => ⟨_, _⟩
  -- ⊢ Set.Nonempty ↑s
  · -- take a set t which is nonempty and at a finite distance of s
    rcases mem_closure_iff.1 hs ⊤ ENNReal.coe_lt_top with ⟨t, ht, Dst⟩
    -- ⊢ Set.Nonempty ↑s
    rw [edist_comm] at Dst
    -- ⊢ Set.Nonempty ↑s
    -- since `t` is nonempty, so is `s`
    exact nonempty_of_hausdorffEdist_ne_top ht.1 (ne_of_lt Dst)
    -- 🎉 no goals
  · refine' isCompact_iff_totallyBounded_isComplete.2 ⟨_, s.closed.isComplete⟩
    -- ⊢ TotallyBounded ↑s
    refine' totallyBounded_iff.2 fun ε (εpos : 0 < ε) => _
    -- ⊢ ∃ t, Set.Finite t ∧ ↑s ⊆ ⋃ (y : α) (_ : y ∈ t), ball y ε
    -- we have to show that s is covered by finitely many eballs of radius ε
    -- pick a nonempty compact set t at distance at most ε/2 of s
    rcases mem_closure_iff.1 hs (ε / 2) (ENNReal.half_pos εpos.ne') with ⟨t, ht, Dst⟩
    -- ⊢ ∃ t, Set.Finite t ∧ ↑s ⊆ ⋃ (y : α) (_ : y ∈ t), ball y ε
    -- cover this space with finitely many balls of radius ε/2
    rcases totallyBounded_iff.1 (isCompact_iff_totallyBounded_isComplete.1 ht.2).1 (ε / 2)
        (ENNReal.half_pos εpos.ne') with
      ⟨u, fu, ut⟩
    refine' ⟨u, ⟨fu, fun x hx => _⟩⟩
    -- ⊢ x ∈ ⋃ (y : α) (_ : y ∈ u), ball y ε
    -- u : set α, fu : u.finite, ut : t ⊆ ⋃ (y : α) (H : y ∈ u), eball y (ε / 2)
    -- then s is covered by the union of the balls centered at u of radius ε
    rcases exists_edist_lt_of_hausdorffEdist_lt hx Dst with ⟨z, hz, Dxz⟩
    -- ⊢ x ∈ ⋃ (y : α) (_ : y ∈ u), ball y ε
    rcases mem_iUnion₂.1 (ut hz) with ⟨y, hy, Dzy⟩
    -- ⊢ x ∈ ⋃ (y : α) (_ : y ∈ u), ball y ε
    have : edist x y < ε :=
      calc
        edist x y ≤ edist x z + edist z y := edist_triangle _ _ _
        _ < ε / 2 + ε / 2 := (ENNReal.add_lt_add Dxz Dzy)
        _ = ε := ENNReal.add_halves _
    exact mem_biUnion hy this
    -- 🎉 no goals
#align emetric.nonempty_compacts.is_closed_in_closeds EMetric.NonemptyCompacts.isClosed_in_closeds

/-- In a complete space, the type of nonempty compact subsets is complete. This follows
from the same statement for closed subsets -/
instance NonemptyCompacts.completeSpace [CompleteSpace α] : CompleteSpace (NonemptyCompacts α) :=
  (completeSpace_iff_isComplete_range
        NonemptyCompacts.ToCloseds.uniformEmbedding.toUniformInducing).2 <|
    NonemptyCompacts.isClosed_in_closeds.isComplete
#align emetric.nonempty_compacts.complete_space EMetric.NonemptyCompacts.completeSpace

/-- In a compact space, the type of nonempty compact subsets is compact. This follows from
the same statement for closed subsets -/
instance NonemptyCompacts.compactSpace [CompactSpace α] : CompactSpace (NonemptyCompacts α) :=
  ⟨by
    rw [NonemptyCompacts.ToCloseds.uniformEmbedding.embedding.isCompact_iff_isCompact_image]
    -- ⊢ IsCompact (NonemptyCompacts.toCloseds '' univ)
    rw [image_univ]
    -- ⊢ IsCompact (range NonemptyCompacts.toCloseds)
    exact NonemptyCompacts.isClosed_in_closeds.isCompact⟩
    -- 🎉 no goals
#align emetric.nonempty_compacts.compact_space EMetric.NonemptyCompacts.compactSpace

/-- In a second countable space, the type of nonempty compact subsets is second countable -/
instance NonemptyCompacts.secondCountableTopology [SecondCountableTopology α] :
    SecondCountableTopology (NonemptyCompacts α) :=
  haveI : SeparableSpace (NonemptyCompacts α) := by
    /- To obtain a countable dense subset of `NonemptyCompacts α`, start from
        a countable dense subset `s` of α, and then consider all its finite nonempty subsets.
        This set is countable and made of nonempty compact sets. It turns out to be dense:
        by total boundedness, any compact set `t` can be covered by finitely many small balls, and
        approximations in `s` of the centers of these balls give the required finite approximation
        of `t`. -/
    rcases exists_countable_dense α with ⟨s, cs, s_dense⟩
    -- ⊢ SeparableSpace (NonemptyCompacts α)
    let v0 := { t : Set α | t.Finite ∧ t ⊆ s }
    -- ⊢ SeparableSpace (NonemptyCompacts α)
    let v : Set (NonemptyCompacts α) := { t : NonemptyCompacts α | (t : Set α) ∈ v0 }
    -- ⊢ SeparableSpace (NonemptyCompacts α)
    refine' ⟨⟨v, _, _⟩⟩
    -- ⊢ Set.Countable v
    · have : v0.Countable := countable_setOf_finite_subset cs
      -- ⊢ Set.Countable v
      exact this.preimage SetLike.coe_injective
      -- 🎉 no goals
    · refine' fun t => mem_closure_iff.2 fun ε εpos => _
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- t is a compact nonempty set, that we have to approximate uniformly by a a set in `v`.
      rcases exists_between εpos with ⟨δ, δpos, δlt⟩
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      have δpos' : 0 < δ / 2 := ENNReal.half_pos δpos.ne'
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- construct a map F associating to a point in α an approximating point in s, up to δ/2.
      have Exy : ∀ x, ∃ y, y ∈ s ∧ edist x y < δ / 2 := by
        intro x
        rcases mem_closure_iff.1 (s_dense x) (δ / 2) δpos' with ⟨y, ys, hy⟩
        exact ⟨y, ⟨ys, hy⟩⟩
      let F x := choose (Exy x)
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      have Fspec : ∀ x, F x ∈ s ∧ edist x (F x) < δ / 2 := fun x => choose_spec (Exy x)
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- cover `t` with finitely many balls. Their centers form a set `a`
      have : TotallyBounded (t : Set α) := t.isCompact.totallyBounded
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      rcases totallyBounded_iff.1 this (δ / 2) δpos' with ⟨a, af, ta⟩
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- a : set α, af : a.finite, ta : t ⊆ ⋃ (y : α) (H : y ∈ a), eball y (δ / 2)
      -- replace each center by a nearby approximation in `s`, giving a new set `b`
      let b := F '' a
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      have : b.Finite := af.image _
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      have tb : ∀ x ∈ t, ∃ y ∈ b, edist x y < δ := by
        intro x hx
        rcases mem_iUnion₂.1 (ta hx) with ⟨z, za, Dxz⟩
        exists F z, mem_image_of_mem _ za
        calc
          edist x (F z) ≤ edist x z + edist z (F z) := edist_triangle _ _ _
          _ < δ / 2 + δ / 2 := (ENNReal.add_lt_add Dxz (Fspec z).2)
          _ = δ := ENNReal.add_halves _
      -- keep only the points in `b` that are close to point in `t`, yielding a new set `c`
      let c := { y ∈ b | ∃ x ∈ t, edist x y < δ }
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      have : c.Finite := ‹b.Finite›.subset fun x hx => hx.1
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- points in `t` are well approximated by points in `c`
      have tc : ∀ x ∈ t, ∃ y ∈ c, edist x y ≤ δ := by
        intro x hx
        rcases tb x hx with ⟨y, yv, Dxy⟩
        have : y ∈ c := by simp [-mem_image]; exact ⟨yv, ⟨x, hx, Dxy⟩⟩
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
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      have Dtc : hausdorffEdist (t : Set α) c < ε := this.trans_lt δlt
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- the set `c` is not empty, as it is well approximated by a nonempty set
      have hc : c.Nonempty := nonempty_of_hausdorffEdist_ne_top t.nonempty (ne_top_of_lt Dtc)
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- let `d` be the version of `c` in the type `NonemptyCompacts α`
      let d : NonemptyCompacts α := ⟨⟨c, ‹c.Finite›.isCompact⟩, hc⟩
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      have : c ⊆ s := by
        intro x hx
        rcases(mem_image _ _ _).1 hx.1 with ⟨y, ⟨_, yx⟩⟩
        rw [← yx]
        exact (Fspec y).1
      have : d ∈ v := ⟨‹c.Finite›, this⟩
      -- ⊢ ∃ y, y ∈ v ∧ edist t y < ε
      -- we have proved that `d` is a good approximation of `t` as requested
      exact ⟨d, ‹d ∈ v›, Dtc⟩
      -- 🎉 no goals
  UniformSpace.secondCountable_of_separable (NonemptyCompacts α)
#align emetric.nonempty_compacts.second_countable_topology EMetric.NonemptyCompacts.secondCountableTopology

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
    hausdorffEdist_ne_top_of_nonempty_of_bounded x.nonempty y.nonempty x.isCompact.bounded
      y.isCompact.bounded
#align metric.nonempty_compacts.metric_space Metric.NonemptyCompacts.metricSpace

/-- The distance on `NonemptyCompacts α` is the Hausdorff distance, by construction -/
theorem NonemptyCompacts.dist_eq {x y : NonemptyCompacts α} :
    dist x y = hausdorffDist (x : Set α) y :=
  rfl
#align metric.nonempty_compacts.dist_eq Metric.NonemptyCompacts.dist_eq

theorem lipschitz_infDist_set (x : α) : LipschitzWith 1 fun s : NonemptyCompacts α => infDist x s :=
  LipschitzWith.of_le_add fun s t => by
    rw [dist_comm]
    -- ⊢ infDist x ↑s ≤ infDist x ↑t + dist t s
    exact infDist_le_infDist_add_hausdorffDist (edist_ne_top t s)
    -- 🎉 no goals
#align metric.lipschitz_inf_dist_set Metric.lipschitz_infDist_set

theorem lipschitz_infDist : LipschitzWith 2 fun p : α × NonemptyCompacts α => infDist p.1 p.2 := by
  -- Porting note: Changed tactic from `exact` to `convert`, because Lean had trouble with 2 = 1 + 1
  convert @LipschitzWith.uncurry α (NonemptyCompacts α) ℝ _ _ _
    (fun (x : α) (s : NonemptyCompacts α) => infDist x s) 1 1
    (fun s => lipschitz_infDist_pt ↑s) lipschitz_infDist_set
  norm_num
  -- 🎉 no goals
#align metric.lipschitz_inf_dist Metric.lipschitz_infDist

theorem uniformContinuous_infDist_Hausdorff_dist :
    UniformContinuous fun p : α × NonemptyCompacts α => infDist p.1 p.2 :=
  lipschitz_infDist.uniformContinuous
#align metric.uniform_continuous_inf_dist_Hausdorff_dist Metric.uniformContinuous_infDist_Hausdorff_dist

end --section

end Metric --namespace
