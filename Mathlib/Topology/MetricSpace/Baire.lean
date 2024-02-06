/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.GDelta
import Mathlib.Topology.Sets.Compacts

#align_import topology.metric_space.baire from "leanprover-community/mathlib"@"b9e46fe101fc897fb2e7edaf0bf1f09ea49eb81a"

/-!
# Baire theorem

In a complete metric space, a countable intersection of dense open subsets is dense.

The good concept underlying the theorem is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We prove Baire theorem, giving several different
formulations that can be handy. We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

We also prove that in Baire spaces, the `residual` sets are exactly those containing a dense Gδ set.
-/


noncomputable section

open scoped Classical Topology Filter ENNReal

open Filter Set TopologicalSpace

variable {X α : Type*} {ι : Sort*}

section BaireTheorem

open EMetric ENNReal

/-- The property `BaireSpace α` means that the topological space `α` has the Baire property:
any countable intersection of open dense subsets is dense.
Formulated here when the source space is ℕ (and subsumed below by `dense_iInter_of_isOpen` working
with any encodable source space). -/
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : ∀ f : ℕ → Set X, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
#align baire_space BaireSpace

/-- Baire theorems asserts that various topological spaces have the Baire property.
Two versions of these theorems are given.
The first states that complete `PseudoEMetricSpace`s are Baire. -/
instance (priority := 100) BaireSpace.of_pseudoEMetricSpace_completeSpace [PseudoEMetricSpace X]
    [CompleteSpace X] : BaireSpace X := by
  refine' ⟨fun f ho hd => _⟩
  let B : ℕ → ℝ≥0∞ := fun n => 1 / 2 ^ n
  have Bpos : ∀ n, 0 < B n := fun n ↦
    ENNReal.div_pos one_ne_zero <| ENNReal.pow_ne_top ENNReal.coe_ne_top
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀ n x δ, δ ≠ 0 → ∃ y r, 0 < r ∧ r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n := by
    intro n x δ δpos
    have : x ∈ closure (f n) := hd n x
    rcases EMetric.mem_closure_iff.1 this (δ / 2) (ENNReal.half_pos δpos) with ⟨y, ys, xy⟩
    rw [edist_comm] at xy
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closedBall y r ⊆ f n :=
      nhds_basis_closed_eball.mem_iff.1 (isOpen_iff_mem_nhds.1 (ho n) y ys)
    refine' ⟨y, min (min (δ / 2) r) (B (n + 1)), _, _, fun z hz => ⟨_, _⟩⟩
    show 0 < min (min (δ / 2) r) (B (n + 1))
    exact lt_min (lt_min (ENNReal.half_pos δpos) rpos) (Bpos (n + 1))
    show min (min (δ / 2) r) (B (n + 1)) ≤ B (n + 1)
    exact min_le_right _ _
    show z ∈ closedBall x δ
    exact
      calc
        edist z x ≤ edist z y + edist y x := edist_triangle _ _ _
        _ ≤ min (min (δ / 2) r) (B (n + 1)) + δ / 2 := (add_le_add hz (le_of_lt xy))
        _ ≤ δ / 2 + δ / 2 := (add_le_add (le_trans (min_le_left _ _) (min_le_left _ _)) le_rfl)
        _ = δ := ENNReal.add_halves δ
    show z ∈ f n
    exact hr (calc
      edist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
      _ ≤ r := le_trans (min_le_left _ _) (min_le_right _ _))
  choose! center radius Hpos HB Hball using this
  refine' fun x => (mem_closure_iff_nhds_basis nhds_basis_closed_eball).2 fun ε εpos => _
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
    `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed
    ball `closedBall (c n) (r n)` is included in the previous ball and in `f n`, and such that
    `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
    limit which belongs to all the `f n`. -/
  let F : ℕ → X × ℝ≥0∞ := fun n =>
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p => Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n => (F n).1
  let r : ℕ → ℝ≥0∞ := fun n => (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n hn
    exact lt_min εpos (Bpos 0)
    exact Hpos n (c n) (r n) hn.ne'
  have r0 : ∀ n, r n ≠ 0 := fun n => (rpos n).ne'
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n _
    exact min_le_right _ _
    exact HB n (c n) (r n) (r0 n)
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n :=
    fun n => Hball n (c n) (r n) (r0 n)
  have cdist : ∀ n, edist (c n) (c (n + 1)) ≤ B n := by
    intro n
    rw [edist_comm]
    have A : c (n + 1) ∈ closedBall (c (n + 1)) (r (n + 1)) := mem_closedBall_self
    have I :=
      calc
        closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) :=
          Subset.trans (incl n) (inter_subset_left _ _)
        _ ⊆ closedBall (c n) (B n) := closedBall_subset_closedBall (rB n)
    exact I A
  have : CauchySeq c := cauchySeq_of_edist_le_geometric_two _ one_ne_top cdist
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y
  simp only [exists_prop, Set.mem_iInter]
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n
    refine' Nat.le_induction _ fun m _ h => _
    · exact Subset.refl _
    · exact Subset.trans (incl m) (Subset.trans (inter_subset_left _ _) h)
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    intro n
    refine' isClosed_ball.mem_of_tendsto ylim _
    refine' (Filter.eventually_ge_atTop n).mono fun m hm => _
    exact I n m hm mem_closedBall_self
  constructor
  show ∀ n, y ∈ f n
  · intro n
    have : closedBall (c (n + 1)) (r (n + 1)) ⊆ f n :=
      Subset.trans (incl n) (inter_subset_right _ _)
    exact this (yball (n + 1))
  show edist y x ≤ ε
  exact le_trans (yball 0) (min_le_left _ _)
#align baire_category_theorem_emetric_complete BaireSpace.of_pseudoEMetricSpace_completeSpace

/-- The second theorem states that locally compact R₁ spaces are Baire. -/
instance (priority := 100) BaireSpace.of_t2Space_locallyCompactSpace
    [TopologicalSpace X] [R1Space X] [LocallyCompactSpace X] : BaireSpace X := by
  constructor
  intro f ho hd
  /- To prove that an intersection of open dense subsets is dense, prove that its intersection
    with any open neighbourhood `U` is dense. Define recursively a decreasing sequence `K` of
    compact neighbourhoods: start with some compact neighbourhood inside `U`, then at each step,
    take its interior, intersect with `f n`, then choose a compact neighbourhood inside the
    intersection. -/
  rw [dense_iff_inter_open]
  intro U U_open U_nonempty
  -- Choose an antitone sequence of positive compacts such that `closure (K 0) ⊆ U`
  -- and `closure (K (n + 1)) ⊆ f n` for all `n`
  obtain ⟨K, hK_anti, hKf, hKU⟩ : ∃ K : ℕ → PositiveCompacts X,
      (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, closure ↑(K (n + 1)) ⊆ f n) ∧ closure ↑(K 0) ⊆ U := by
    rcases U_open.exists_positiveCompacts_closure_subset U_nonempty with ⟨K₀, hK₀⟩
    have : ∀ (n) (K : PositiveCompacts X),
        ∃ K' : PositiveCompacts X, closure ↑K' ⊆ f n ∩ interior K := by
      refine fun n K ↦ ((ho n).inter isOpen_interior).exists_positiveCompacts_closure_subset ?_
      rw [inter_comm]
      exact (hd n).inter_open_nonempty _ isOpen_interior K.interior_nonempty
    choose K_next hK_next using this
    refine ⟨Nat.rec K₀ K_next, fun n ↦ ?_, fun n ↦ (hK_next n _).trans (inter_subset_left _ _), hK₀⟩
    exact subset_closure.trans <| (hK_next _ _).trans <|
      (inter_subset_right _ _).trans interior_subset
  -- Prove that ̀`⋂ n : ℕ, closure (K n)` is inside `U ∩ ⋂ n : ℕ, f n`.
  have hK_subset : (⋂ n, closure (K n) : Set X) ⊆ U ∩ ⋂ n, f n := fun x hx ↦ by
    simp only [mem_iInter, mem_inter_iff] at hx ⊢
    exact ⟨hKU <| hx 0, fun n ↦ hKf n <| hx (n + 1)⟩
  /- Prove that `⋂ n : ℕ, closure (K n)` is not empty, as an intersection of a decreasing sequence
    of nonempty compact closed subsets. -/
  have hK_nonempty : (⋂ n, closure (K n) : Set X).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_compact_closed _
      (fun n => closure_mono <| hK_anti n) (fun n => (K n).nonempty.closure)
      (K 0).isCompact.closure fun n => isClosed_closure
  exact hK_nonempty.mono hK_subset
#align baire_category_theorem_locally_compact BaireSpace.of_t2Space_locallyCompactSpace

variable [TopologicalSpace X] [BaireSpace X]

/-- Definition of a Baire space. -/
theorem dense_iInter_of_isOpen_nat {f : ℕ → Set X} (ho : ∀ n, IsOpen (f n))
    (hd : ∀ n, Dense (f n)) : Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd
#align dense_Inter_of_open_nat dense_iInter_of_isOpen_nat

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_isOpen {S : Set (Set X)} (ho : ∀ s ∈ S, IsOpen s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) := by
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, rfl⟩
    exact dense_iInter_of_isOpen_nat (forall_range_iff.1 ho) (forall_range_iff.1 hd)
#align dense_sInter_of_open dense_sInter_of_isOpen

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_biInter_of_isOpen {S : Set α} {f : α → Set X} (ho : ∀ s ∈ S, IsOpen (f s))
    (hS : S.Countable) (hd : ∀ s ∈ S, Dense (f s)) : Dense (⋂ s ∈ S, f s) := by
  rw [← sInter_image]
  refine dense_sInter_of_isOpen ?_ (hS.image _) ?_ <;> rwa [ball_image_iff]
#align dense_bInter_of_open dense_biInter_of_isOpen

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable type. -/
theorem dense_iInter_of_isOpen [Countable ι] {f : ι → Set X} (ho : ∀ i, IsOpen (f i))
    (hd : ∀ i, Dense (f i)) : Dense (⋂ s, f s) :=
  dense_sInter_of_isOpen (forall_range_iff.2 ho) (countable_range _) (forall_range_iff.2 hd)
#align dense_Inter_of_open dense_iInter_of_isOpen

/-- A set is residual (comeagre) if and only if it includes a dense `Gδ` set. -/
theorem mem_residual {s : Set X} : s ∈ residual X ↔ ∃ t ⊆ s, IsGδ t ∧ Dense t := by
  constructor
  · rw [mem_residual_iff]
    rintro ⟨S, hSo, hSd, Sct, Ss⟩
    refine' ⟨_, Ss, ⟨_, fun t ht => hSo _ ht, Sct, rfl⟩, _⟩
    exact dense_sInter_of_isOpen hSo Sct hSd
  rintro ⟨t, ts, ho, hd⟩
  exact mem_of_superset (residual_of_dense_Gδ ho hd) ts
#align mem_residual mem_residual

/-- A property holds on a residual (comeagre) set if and only if it holds on some dense `Gδ` set. -/
theorem eventually_residual {p : X → Prop} :
    (∀ᶠ x in residual X, p x) ↔ ∃ t : Set X, IsGδ t ∧ Dense t ∧ ∀ x ∈ t, p x := by
  simp only [Filter.Eventually, mem_residual, subset_def, mem_setOf_eq]
  tauto
#align eventually_residual eventually_residual

theorem dense_of_mem_residual {s : Set X} (hs : s ∈ residual X) : Dense s :=
  let ⟨_, hts, _, hd⟩ := mem_residual.1 hs
  hd.mono hts
#align dense_of_mem_residual dense_of_mem_residual

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
theorem dense_sInter_of_Gδ {S : Set (Set X)} (ho : ∀ s ∈ S, IsGδ s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) :=
  dense_of_mem_residual ((countable_sInter_mem hS).mpr
    (fun _ hs => residual_of_dense_Gδ (ho _ hs) (hd _ hs)))
set_option linter.uppercaseLean3 false in
#align dense_sInter_of_Gδ dense_sInter_of_Gδ

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable type. -/
theorem dense_iInter_of_Gδ [Countable ι] {f : ι → Set X} (ho : ∀ s, IsGδ (f s))
    (hd : ∀ s, Dense (f s)) : Dense (⋂ s, f s) :=
  dense_sInter_of_Gδ (forall_range_iff.2 ‹_›) (countable_range _) (forall_range_iff.2 ‹_›)
set_option linter.uppercaseLean3 false in
#align dense_Inter_of_Gδ dense_iInter_of_Gδ

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_biInter_of_Gδ {S : Set α} {f : ∀ x ∈ S, Set X} (ho : ∀ s (H : s ∈ S), IsGδ (f s H))
    (hS : S.Countable) (hd : ∀ s (H : s ∈ S), Dense (f s H)) : Dense (⋂ s ∈ S, f s ‹_›) := by
  rw [biInter_eq_iInter]
  haveI := hS.to_subtype
  exact dense_iInter_of_Gδ (fun s => ho s s.2) fun s => hd s s.2
set_option linter.uppercaseLean3 false in
#align dense_bInter_of_Gδ dense_biInter_of_Gδ

/-- Baire theorem: the intersection of two dense Gδ sets is dense. -/
theorem Dense.inter_of_Gδ {s t : Set X} (hs : IsGδ s) (ht : IsGδ t) (hsc : Dense s)
    (htc : Dense t) : Dense (s ∩ t) := by
  rw [inter_eq_iInter]
  apply dense_iInter_of_Gδ <;> simp [Bool.forall_bool, *]
set_option linter.uppercaseLean3 false in
#align dense.inter_of_Gδ Dense.inter_of_Gδ

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃`. -/
theorem IsGδ.dense_iUnion_interior_of_closed [Countable ι] {s : Set X} (hs : IsGδ s) (hd : Dense s)
    {f : ι → Set X} (hc : ∀ i, IsClosed (f i)) (hU : s ⊆ ⋃ i, f i) :
    Dense (⋃ i, interior (f i)) := by
  let g i := (frontier (f i))ᶜ
  have hgo : ∀ i, IsOpen (g i) := fun i => isClosed_frontier.isOpen_compl
  have hgd : Dense (⋂ i, g i) := by
    refine' dense_iInter_of_isOpen hgo fun i x => _
    rw [closure_compl, interior_frontier (hc _)]
    exact id
  refine' (hd.inter_of_Gδ hs (isGδ_iInter_of_isOpen fun i => (hgo i)) hgd).mono _
  rintro x ⟨hxs, hxg⟩
  rw [mem_iInter] at hxg
  rcases mem_iUnion.1 (hU hxs) with ⟨i, hi⟩
  exact mem_iUnion.2 ⟨i, self_diff_frontier (f i) ▸ ⟨hi, hxg _⟩⟩
set_option linter.uppercaseLean3 false in
#align is_Gδ.dense_Union_interior_of_closed IsGδ.dense_iUnion_interior_of_closed

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with a union over a countable set in any type. -/
theorem IsGδ.dense_biUnion_interior_of_closed {t : Set α} {s : Set X} (hs : IsGδ s) (hd : Dense s)
    (ht : t.Countable) {f : α → Set X} (hc : ∀ i ∈ t, IsClosed (f i)) (hU : s ⊆ ⋃ i ∈ t, f i) :
    Dense (⋃ i ∈ t, interior (f i)) := by
  haveI := ht.to_subtype
  simp only [biUnion_eq_iUnion, SetCoe.forall'] at *
  exact hs.dense_iUnion_interior_of_closed hd hc hU
set_option linter.uppercaseLean3 false in
#align is_Gδ.dense_bUnion_interior_of_closed IsGδ.dense_biUnion_interior_of_closed

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃₀`. -/
theorem IsGδ.dense_sUnion_interior_of_closed {T : Set (Set X)} {s : Set X} (hs : IsGδ s)
    (hd : Dense s) (hc : T.Countable) (hc' : ∀ t ∈ T, IsClosed t) (hU : s ⊆ ⋃₀ T) :
    Dense (⋃ t ∈ T, interior t) :=
  hs.dense_biUnion_interior_of_closed hd hc hc' <| by rwa [← sUnion_eq_biUnion]
set_option linter.uppercaseLean3 false in
#align is_Gδ.dense_sUnion_interior_of_closed IsGδ.dense_sUnion_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable set in any type. -/
theorem dense_biUnion_interior_of_closed {S : Set α} {f : α → Set X} (hc : ∀ s ∈ S, IsClosed (f s))
    (hS : S.Countable) (hU : ⋃ s ∈ S, f s = univ) : Dense (⋃ s ∈ S, interior (f s)) :=
  isGδ_univ.dense_biUnion_interior_of_closed dense_univ hS hc hU.ge
#align dense_bUnion_interior_of_closed dense_biUnion_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with `⋃₀`. -/
theorem dense_sUnion_interior_of_closed {S : Set (Set X)} (hc : ∀ s ∈ S, IsClosed s)
    (hS : S.Countable) (hU : ⋃₀ S = univ) : Dense (⋃ s ∈ S, interior s) :=
  isGδ_univ.dense_sUnion_interior_of_closed dense_univ hS hc hU.ge
#align dense_sUnion_interior_of_closed dense_sUnion_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable type. -/
theorem dense_iUnion_interior_of_closed [Countable ι] {f : ι → Set X} (hc : ∀ i, IsClosed (f i))
    (hU : ⋃ i, f i = univ) : Dense (⋃ i, interior (f i)) :=
  isGδ_univ.dense_iUnion_interior_of_closed dense_univ hc hU.ge
#align dense_Union_interior_of_closed dense_iUnion_interior_of_closed

/-- One of the most useful consequences of Baire theorem: if a countable union of closed sets
covers the space, then one of the sets has nonempty interior. -/
theorem nonempty_interior_of_iUnion_of_closed [Nonempty X] [Countable ι] {f : ι → Set X}
    (hc : ∀ i, IsClosed (f i)) (hU : ⋃ i, f i = univ) : ∃ i, (interior <| f i).Nonempty := by
  simpa using (dense_iUnion_interior_of_closed hc hU).nonempty
#align nonempty_interior_of_Union_of_closed nonempty_interior_of_iUnion_of_closed

end BaireTheorem
