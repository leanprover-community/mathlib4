/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module topology.metric_space.baire
! leanprover-community/mathlib commit f2ce6086713c78a7f880485f7917ea547a215982
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.CountableInter
import Mathlib.Topology.GDelta
import Mathlib.Topology.Sets.Compacts

/-!
# Baire theorem

In a complete metric space, a countable intersection of dense open subsets is dense.

The good concept underlying the theorem is that of a Gδ set, i.e., a countable intersection
of open sets. Then Baire theorem can also be formulated as the fact that a countable
intersection of dense Gδ sets is a dense Gδ set. We prove Baire theorem, giving several different
formulations that can be handy. We also prove the important consequence that, if the space is
covered by a countable union of closed sets, then the union of their interiors is dense.

We also define the filter `residual α` generated by dense `Gδ` sets and prove that this filter
has the countable intersection property.
-/


noncomputable section

open Classical Topology Filter ENNReal

open Filter Encodable Set TopologicalSpace

variable {α : Type _} {β : Type _} {γ : Type _} {ι : Type _}

section BaireTheorem

open EMetric ENNReal

/-- The property `baire_space α` means that the topological space `α` has the Baire property:
any countable intersection of open dense subsets is dense.
Formulated here when the source space is ℕ (and subsumed below by `dense_Inter_of_open` working
with any encodable source space).-/
class BaireSpace (α : Type _) [TopologicalSpace α] : Prop where
  baire_property : ∀ f : ℕ → Set α, (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Dense (⋂ n, f n)
#align baire_space BaireSpace

/-- Baire theorems asserts that various topological spaces have the Baire property.
Two versions of these theorems are given.
The first states that complete pseudo_emetric spaces are Baire. -/
instance (priority := 100) baire_category_theorem_emetric_complete [PseudoEMetricSpace α]
    [CompleteSpace α] : BaireSpace α := by
  refine' ⟨fun f ho hd => _⟩
  let B : ℕ → ℝ≥0∞ := fun n => 1 / 2 ^ n
  have Bpos : ∀ n, 0 < B n := by
    intro n
    simp only [one_div, one_mul, ENNReal.inv_pos]
    exact pow_ne_top two_ne_top
  /- Translate the density assumption into two functions `center` and `radius` associating
    to any n, x, δ, δpos a center and a positive radius such that
    `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
    We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀ n x δ, δ ≠ 0 → ∃ y r, 0 < r ∧ r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by
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
    exact
      hr
        (calc
          edist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
          _ ≤ r := le_trans (min_le_left _ _) (min_le_right _ _)
          )
  choose! center radius Hpos HB Hball using this
  refine' fun x => (mem_closure_iff_nhds_basis nhds_basis_closed_eball).2 fun ε εpos => _
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
    `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
    `closed_ball (c n) (r n)` is included in the previous ball and in `f n`, and such that
    `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
    limit which belongs to all the `f n`. -/
  let F : ℕ → α × ℝ≥0∞ := fun n =>
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p => Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → α := fun n => (F n).1
  let r : ℕ → ℝ≥0∞ := fun n => (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n hn
    exact lt_min εpos (Bpos 0)
    exact Hpos n (c n) (r n) hn.ne'
  have r0 : ∀ n, r n ≠ 0 := fun n => (rpos n).ne'
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n hn
    exact min_le_right _ _
    exact HB n (c n) (r n) (r0 n)
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := fun n =>
    Hball n (c n) (r n) (r0 n)
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
  simp only [exists_prop, Set.mem_interᵢ]
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n
    refine' Nat.le_induction _ fun m hnm h => _
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
#align baire_category_theorem_emetric_complete baire_category_theorem_emetric_complete

/-- The second theorem states that locally compact spaces are Baire. -/
instance (priority := 100) baire_category_theorem_locally_compact [TopologicalSpace α] [T2Space α]
    [LocallyCompactSpace α] : BaireSpace α := by
  constructor
  intro f ho hd
  /- To prove that an intersection of open dense subsets is dense, prove that its intersection
    with any open neighbourhood `U` is dense. Define recursively a decreasing sequence `K` of
    compact neighbourhoods: start with some compact neighbourhood inside `U`, then at each step,
    take its interior, intersect with `f n`, then choose a compact neighbourhood inside the
    intersection.-/
  apply dense_iff_inter_open.2
  intro U U_open U_nonempty
  rcases exists_positiveCompacts_subset U_open U_nonempty with ⟨K₀, hK₀⟩
  have : ∀ (n) (K : positive_compacts α), ∃ K' : positive_compacts α, ↑K' ⊆ f n ∩ interior K := by
    refine' fun n K => exists_positiveCompacts_subset ((ho n).inter isOpen_interior) _
    rw [inter_comm]
    exact (hd n).inter_open_nonempty _ isOpen_interior K.interior_nonempty
  choose K_next hK_next
  let K : ℕ → positive_compacts α := fun n => Nat.recOn n K₀ K_next
  -- This is a decreasing sequence of positive compacts contained in suitable open sets `f n`.
  have hK_decreasing : ∀ n : ℕ, ↑(K (n + 1)) ⊆ f n ∩ K n := fun n =>
    (hK_next n (K n)).trans <| inter_subset_inter_right _ interior_subset
  -- Prove that ̀`⋂ n : ℕ, K n` is inside `U ∩ ⋂ n : ℕ, (f n)`.
  have hK_subset : (⋂ n, K n : Set α) ⊆ U ∩ ⋂ n, f n := by
    intro x hx
    simp only [mem_inter_iff, mem_Inter] at hx⊢
    exact ⟨hK₀ <| hx 0, fun n => (hK_decreasing n (hx (n + 1))).1⟩
  /- Prove that `⋂ n : ℕ, K n` is not empty, as an intersection of a decreasing sequence
    of nonempty compact subsets.-/
  have hK_nonempty : (⋂ n, K n : Set α).Nonempty :=
    IsCompact.nonempty_interᵢ_of_sequence_nonempty_compact_closed _
      (fun n => (hK_decreasing n).trans (inter_subset_right _ _)) (fun n => (K n).Nonempty)
      (K 0).IsCompact fun n => (K n).IsCompact.IsClosed
  exact hK_nonempty.mono hK_subset
#align baire_category_theorem_locally_compact baire_category_theorem_locally_compact

variable [TopologicalSpace α] [BaireSpace α]

/-- Definition of a Baire space. -/
theorem dense_interᵢ_of_open_nat {f : ℕ → Set α} (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) :=
  BaireSpace.baire_property f ho hd
#align dense_Inter_of_open_nat dense_interᵢ_of_open_nat

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with ⋂₀. -/
theorem dense_interₛ_of_open {S : Set (Set α)} (ho : ∀ s ∈ S, IsOpen s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) := by
  cases' S.eq_empty_or_nonempty with h h
  · simp [h]
  · rcases hS.exists_eq_range h with ⟨f, hf⟩
    have F : ∀ n, f n ∈ S := fun n => by rw [hf] <;> exact mem_range_self _
    rw [hf, sInter_range]
    exact dense_interᵢ_of_open_nat (fun n => ho _ (F n)) fun n => hd _ (F n)
#align dense_sInter_of_open dense_interₛ_of_open

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_open {S : Set β} {f : β → Set α} (ho : ∀ s ∈ S, IsOpen (f s))
    (hS : S.Countable) (hd : ∀ s ∈ S, Dense (f s)) : Dense (⋂ s ∈ S, f s) := by
  rw [← sInter_image]
  apply dense_interₛ_of_open
  · rwa [ball_image_iff]
  · exact hS.image _
  · rwa [ball_image_iff]
#align dense_bInter_of_open dense_bInter_of_open

/-- Baire theorem: a countable intersection of dense open sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_interᵢ_of_open [Encodable β] {f : β → Set α} (ho : ∀ s, IsOpen (f s))
    (hd : ∀ s, Dense (f s)) : Dense (⋂ s, f s) := by
  rw [← sInter_range]
  apply dense_interₛ_of_open
  · rwa [forall_range_iff]
  · exact countable_range _
  · rwa [forall_range_iff]
#align dense_Inter_of_open dense_interᵢ_of_open

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with ⋂₀. -/
theorem dense_interₛ_of_Gδ {S : Set (Set α)} (ho : ∀ s ∈ S, IsGδ s) (hS : S.Countable)
    (hd : ∀ s ∈ S, Dense s) : Dense (⋂₀ S) := by
  -- the result follows from the result for a countable intersection of dense open sets,
  -- by rewriting each set as a countable intersection of open sets, which are of course dense.
  choose T hTo hTc hsT using ho
  have : ⋂₀ S = ⋂₀ ⋃ s ∈ S, T s ‹_› :=
    by-- := (sInter_bUnion (λs hs, (hT s hs).2.2)).symm,
    simp only [sInter_Union, (hsT _ _).symm, ← sInter_eq_bInter]
  rw [this]
  refine' dense_interₛ_of_open _ (hS.bUnion hTc) _ <;> simp only [mem_Union] <;>
    rintro t ⟨s, hs, tTs⟩
  show IsOpen t
  exact hTo s hs t tTs
  show Dense t
  · intro x
    have := hd s hs x
    rw [hsT s hs] at this
    exact closure_mono (sInter_subset_of_mem tTs) this
#align dense_sInter_of_Gδ dense_interₛ_of_Gδ

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is an encodable type. -/
theorem dense_interᵢ_of_Gδ [Encodable β] {f : β → Set α} (ho : ∀ s, IsGδ (f s))
    (hd : ∀ s, Dense (f s)) : Dense (⋂ s, f s) := by
  rw [← sInter_range]
  exact dense_interₛ_of_Gδ (forall_range_iff.2 ‹_›) (countable_range _) (forall_range_iff.2 ‹_›)
#align dense_Inter_of_Gδ dense_interᵢ_of_Gδ

/-- Baire theorem: a countable intersection of dense Gδ sets is dense. Formulated here with
an index set which is a countable set in any type. -/
theorem dense_bInter_of_Gδ {S : Set β} {f : ∀ x ∈ S, Set α} (ho : ∀ s ∈ S, IsGδ (f s ‹_›))
    (hS : S.Countable) (hd : ∀ s ∈ S, Dense (f s ‹_›)) : Dense (⋂ s ∈ S, f s ‹_›) := by
  rw [bInter_eq_Inter]
  haveI := hS.to_encodable
  exact dense_interᵢ_of_Gδ (fun s => ho s s.2) fun s => hd s s.2
#align dense_bInter_of_Gδ dense_bInter_of_Gδ

/-- Baire theorem: the intersection of two dense Gδ sets is dense. -/
theorem Dense.inter_of_Gδ {s t : Set α} (hs : IsGδ s) (ht : IsGδ t) (hsc : Dense s)
    (htc : Dense t) : Dense (s ∩ t) := by
  rw [inter_eq_Inter]
  apply dense_interᵢ_of_Gδ <;> simp [Bool.forall_bool, *]
#align dense.inter_of_Gδ Dense.inter_of_Gδ

/-- A property holds on a residual (comeagre) set if and only if it holds on some dense `Gδ` set. -/
theorem eventually_residual {p : α → Prop} :
    (∀ᶠ x in residual α, p x) ↔ ∃ t : Set α, IsGδ t ∧ Dense t ∧ ∀ x ∈ t, p x :=
  calc
    (∀ᶠ x in residual α, p x) ↔ ∀ᶠ x in ⨅ (t : Set α) (ht : IsGδ t ∧ Dense t), 𝓟 t, p x := by
      simp only [residual, infᵢ_and]
    _ ↔ ∃ (t : Set α)(ht : IsGδ t ∧ Dense t), ∀ᶠ x in 𝓟 t, p x :=
      (mem_binfᵢ_of_directed
        (fun t₁ h₁ t₂ h₂ =>
          ⟨t₁ ∩ t₂, ⟨h₁.1.inter h₂.1, Dense.inter_of_Gδ h₁.1 h₂.1 h₁.2 h₂.2⟩, by simp⟩)
        ⟨univ, isGδ_univ, dense_univ⟩)
    _ ↔ _ := by simp [and_assoc']

#align eventually_residual eventually_residual

/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (t «expr ⊆ » s) -/
/-- A set is residual (comeagre) if and only if it includes a dense `Gδ` set. -/
theorem mem_residual {s : Set α} : s ∈ residual α ↔ ∃ (t : _)(_ : t ⊆ s), IsGδ t ∧ Dense t :=
  (@eventually_residual α _ _ fun x => x ∈ s).trans <|
    exists_congr fun t => by rw [exists_prop, and_comm' (t ⊆ s), subset_def, and_assoc']
#align mem_residual mem_residual

theorem dense_of_mem_residual {s : Set α} (hs : s ∈ residual α) : Dense s :=
  let ⟨t, hts, _, hd⟩ := mem_residual.1 hs
  hd.mono hts
#align dense_of_mem_residual dense_of_mem_residual

instance : CountableInterFilter (residual α) :=
  ⟨by
    intro S hSc hS
    simp only [mem_residual] at *
    choose T hTs hT using hS
    refine' ⟨⋂ s ∈ S, T s ‹_›, _, _, _⟩
    · rw [sInter_eq_bInter]
      exact Inter₂_mono hTs
    · exact isGδ_binterᵢ hSc fun s hs => (hT s hs).1
    · exact dense_bInter_of_Gδ (fun s hs => (hT s hs).1) hSc fun s hs => (hT s hs).2⟩

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃`. -/
theorem IsGδ.dense_unionᵢ_interior_of_closed [Encodable ι] {s : Set α} (hs : IsGδ s) (hd : Dense s)
    {f : ι → Set α} (hc : ∀ i, IsClosed (f i)) (hU : s ⊆ ⋃ i, f i) : Dense (⋃ i, interior (f i)) :=
  by
  let g i := frontier (f i)ᶜ
  have hgo : ∀ i, IsOpen (g i) := fun i => is_closed_frontier.is_open_compl
  have hgd : Dense (⋂ i, g i) := by
    refine' dense_interᵢ_of_open hgo fun i x => _
    rw [closure_compl, interior_frontier (hc _)]
    exact id
  refine' (hd.inter_of_Gδ hs (isGδ_interᵢ fun i => (hgo i).IsGδ) hgd).mono _
  rintro x ⟨hxs, hxg⟩
  rw [mem_Inter] at hxg
  rcases mem_Union.1 (hU hxs) with ⟨i, hi⟩
  exact mem_Union.2 ⟨i, self_diff_frontier (f i) ▸ ⟨hi, hxg _⟩⟩
#align is_Gδ.dense_Union_interior_of_closed IsGδ.dense_unionᵢ_interior_of_closed

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with a union over a countable set in any type. -/
theorem IsGδ.dense_bUnion_interior_of_closed {t : Set ι} {s : Set α} (hs : IsGδ s) (hd : Dense s)
    (ht : t.Countable) {f : ι → Set α} (hc : ∀ i ∈ t, IsClosed (f i)) (hU : s ⊆ ⋃ i ∈ t, f i) :
    Dense (⋃ i ∈ t, interior (f i)) := by
  haveI := ht.to_encodable
  simp only [bUnion_eq_Union, SetCoe.forall'] at *
  exact hs.dense_Union_interior_of_closed hd hc hU
#align is_Gδ.dense_bUnion_interior_of_closed IsGδ.dense_bUnion_interior_of_closed

/-- If a countable family of closed sets cover a dense `Gδ` set, then the union of their interiors
is dense. Formulated here with `⋃₀`. -/
theorem IsGδ.dense_unionₛ_interior_of_closed {T : Set (Set α)} {s : Set α} (hs : IsGδ s)
    (hd : Dense s) (hc : T.Countable) (hc' : ∀ t ∈ T, IsClosed t) (hU : s ⊆ ⋃₀ T) :
    Dense (⋃ t ∈ T, interior t) :=
  hs.dense_bUnion_interior_of_closed hd hc hc' <| by rwa [← sUnion_eq_bUnion]
#align is_Gδ.dense_sUnion_interior_of_closed IsGδ.dense_unionₛ_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is a countable set in any type. -/
theorem dense_bUnion_interior_of_closed {S : Set β} {f : β → Set α} (hc : ∀ s ∈ S, IsClosed (f s))
    (hS : S.Countable) (hU : (⋃ s ∈ S, f s) = univ) : Dense (⋃ s ∈ S, interior (f s)) :=
  isGδ_univ.dense_bUnion_interior_of_closed dense_univ hS hc hU.ge
#align dense_bUnion_interior_of_closed dense_bUnion_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with `⋃₀`. -/
theorem dense_unionₛ_interior_of_closed {S : Set (Set α)} (hc : ∀ s ∈ S, IsClosed s)
    (hS : S.Countable) (hU : ⋃₀ S = univ) : Dense (⋃ s ∈ S, interior s) :=
  isGδ_univ.dense_unionₛ_interior_of_closed dense_univ hS hc hU.ge
#align dense_sUnion_interior_of_closed dense_unionₛ_interior_of_closed

/-- Baire theorem: if countably many closed sets cover the whole space, then their interiors
are dense. Formulated here with an index set which is an encodable type. -/
theorem dense_unionᵢ_interior_of_closed [Encodable β] {f : β → Set α} (hc : ∀ s, IsClosed (f s))
    (hU : (⋃ s, f s) = univ) : Dense (⋃ s, interior (f s)) :=
  isGδ_univ.dense_unionᵢ_interior_of_closed dense_univ hc hU.ge
#align dense_Union_interior_of_closed dense_unionᵢ_interior_of_closed

/-- One of the most useful consequences of Baire theorem: if a countable union of closed sets
covers the space, then one of the sets has nonempty interior. -/
theorem nonempty_interior_of_unionᵢ_of_closed [Nonempty α] [Encodable β] {f : β → Set α}
    (hc : ∀ s, IsClosed (f s)) (hU : (⋃ s, f s) = univ) : ∃ s, (interior <| f s).Nonempty := by
  simpa using (dense_unionᵢ_interior_of_closed hc hU).Nonempty
#align nonempty_interior_of_Union_of_closed nonempty_interior_of_unionᵢ_of_closed

end BaireTheorem
